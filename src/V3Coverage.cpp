// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Netlist (top level) functions
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2025 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************
// COVERAGE TRANSFORMATIONS:
//      At each IF/(IF else)/CASEITEM,
//         If there's no coverage off on the block below it,
//         or a $stop
//              Insert a COVERDECL node in the module.
//              (V3Emit reencodes into per-module numbers for emitting.)
//              Insert a COVERINC node at the end of the statement list
//              for that if/else/case.
//
//*************************************************************************

#include "V3PchAstNoMT.h"  // VL_MT_DISABLED_CODE_UNIT

#include "V3Coverage.h"

#include "V3EmitV.h"

#include <list>
#include <unordered_map>

VL_DEFINE_DEBUG_FUNCTIONS;

class ExprCoverageEligibleVisitor final : public VNVisitor {
    // STATE
    bool m_eligible = true;

    void visit(AstNodeVarRef* nodep) override {
        AstNodeDType* dtypep = nodep->varp()->dtypep();
        // Class objecs and references not supported for expression coverage
        // because the object may not persist until the point at which
        // coverage data is gathered
        // This could be resolved in the future by protecting against dereferrencing
        // null pointers when cloning the expression for expression coverage
        if (VN_CAST(dtypep, ClassRefDType)) {
            m_eligible = false;
        } else {
            iterateChildren(nodep);
        }
    }

    void visit(AstNode* nodep) override {
        if (!nodep->isExprCoverageEligible()) {
            m_eligible = false;
        } else {
            iterateChildren(nodep);
        }
    }

public:
    // CONSTRUCTORS
    explicit ExprCoverageEligibleVisitor(AstNode* nodep) { iterateChildren(nodep); }
    ~ExprCoverageEligibleVisitor() override = default;

    bool eligible() { return m_eligible; }
};

//######################################################################
// Coverage state, as a visitor of each AstNode

class CoverageVisitor final : public VNVisitor {
    // TYPES
    using LinenoSet = std::set<int>;

    struct CoverTerm final {
        AstNodeExpr* m_exprp;  // Expression branch term
        bool m_objective;  // Term objective
        std::string m_emitV;  // V3EmitV string for cover point comment
        CoverTerm(AstNodeExpr* exprp, bool objective, const string& emitV)
            : m_exprp{exprp}
            , m_objective{objective}
            , m_emitV(emitV) {}
    };
    using CoverExpr = std::deque<CoverTerm>;
    using CoverExprs = std::list<CoverExpr>;

    struct ToggleEnt final {
        const string m_comment;  // Comment for coverage dump
        AstNodeExpr* m_varRefp;  // How to get to this element
        AstNodeExpr* m_chgRefp;  // How to get to this element
        AstNodeExpr* m_initRefp;  // Evaluates to true if variable is initialized
        ToggleEnt(const string& comment, AstNodeExpr* vp, AstNodeExpr* cp, AstNodeExpr* initp)
            : m_comment{comment}
            , m_varRefp{vp}
            , m_chgRefp{cp}
            , m_initRefp{initp} {}
        ~ToggleEnt() = default;
        void cleanup() {
            VL_DO_CLEAR(m_varRefp->deleteTree(), m_varRefp = nullptr);
            VL_DO_CLEAR(m_chgRefp->deleteTree(), m_chgRefp = nullptr);
            if (m_initRefp) { VL_DO_CLEAR(m_initRefp->deleteTree(), m_initRefp = nullptr); }
        }
    };

    struct CheckState final {  // State save-restored on each new coverage scope/block
        bool m_on = false;  // Should this block get covered?
        bool m_inModOff = false;  // In module with no coverage
        int m_handle = 0;  // Opaque handle for index into line tracking
        const AstNode* m_nodep = nullptr;  // Node establishing this state
        CheckState() = default;
        bool lineCoverageOn(const AstNode* nodep) const {
            return m_on && !m_inModOff && nodep->fileline()->coverageOn()
                   && v3Global.opt.coverageLine();
        }
        bool exprCoverageOn(const AstNode* nodep) const {
            return m_on && !m_inModOff && nodep->fileline()->coverageOn()
                   && v3Global.opt.coverageExpr();
        }
    };

    enum Objective : uint8_t { NONE, SEEKING, ABORTED };

    // NODE STATE
    // Entire netlist:
    //  AstIf::user1()                  -> bool.  True indicates ifelse processed
    //  AstVar::user1p()                -> AstVar*. Variable indicating if AstVar is initialized
    //  AstIf::user2()                  -> bool.  True indicates coverage-generated
    const VNUser1InUse m_inuser1;
    const VNUser2InUse m_inuser2;

    // STATE - across all visitors
    int m_nextHandle = 0;

    // STATE - for current visit position (use VL_RESTORER)
    CheckState m_state;  // State save-restored on each new coverage scope/block
    AstNodeModule* m_modp = nullptr;  // Current module to add statement to
    AstNode* m_exprStmtsp = nullptr;  // Node to add expr coverage to
    bool m_then = false;  // Whether we're iterating the then or else branch
                          // when m_exprStmtps is an AstIf
    CoverExprs m_exprs;  // List of expressions that can reach objective
    Objective m_seeking = NONE;  // Seeking objective for expression coverage
    bool m_objective = false;  // Expression objective
    bool m_ifCond = false;  // Visiting if condition
    bool m_inToggleOff = false;  // In function/task etc
    bool m_inLoopNotBody = false;  // Inside a loop, but not in its body
    string m_beginHier;  // AstBegin hier name for user coverage points

    // STATE - cleared each module
    std::unordered_map<std::string, uint32_t> m_varnames;  // Uniquify inserted variable names
    std::unordered_map<int, LinenoSet> m_handleLines;  // Line numbers for given m_stateHandle

    // METHODS

    const char* varIgnoreToggle(AstVar* nodep) {
        // Return true if this shouldn't be traced
        // See also similar rule in V3TraceDecl::varIgnoreTrace
        if (!nodep->isToggleCoverable()) return "Not relevant signal type";
        if (!v3Global.opt.coverageUnderscore()) {
            const string prettyName = nodep->prettyName();
            if (prettyName[0] == '_') return "Leading underscore";
            if (prettyName.find("._") != string::npos) return "Inlined leading underscore";
        }
        if ((nodep->width() * nodep->dtypep()->arrayUnpackedElements())
            > static_cast<uint32_t>(v3Global.opt.coverageMaxWidth())) {
            return "Wide bus/array > --coverage-max-width setting's bits";
        }
        // We allow this, though tracing doesn't
        // if (nodep->arrayp(1)) return "Unsupported: Multi-dimensional array";
        return nullptr;
    }

    AstCoverInc* newCoverInc(FileLine* fl, const string& hier, const string& page_prefix,
                             const string& comment, const string& linescov, int offset,
                             const string& trace_var_name) {
        // We could use the basename of the filename to the page, but seems
        // better for code from an include file to be listed under the
        // module using it rather than the include file.
        // Note the module name could have parameters appended, we'll consider this
        // a feature as it allows for each parameterized block to be counted separately.
        // Someday the user might be allowed to specify a different page suffix
        const string page = page_prefix + "/" + m_modp->prettyName();

        AstCoverDecl* const declp = new AstCoverDecl{fl, page, comment, linescov, offset};
        declp->hier(hier);
        m_modp->addStmtsp(declp);
        UINFO(9, "new " << declp);

        AstCoverInc* const incp = new AstCoverInc{fl, declp};
        if (!trace_var_name.empty()
            && v3Global.opt.traceCoverage()
            // No module handle to trace inside classes
            && !VN_IS(m_modp, Class)) {
            FileLine* const fl_nowarn = new FileLine{incp->fileline()};
            fl_nowarn->modifyWarnOff(V3ErrorCode::UNUSEDSIGNAL, true);
            AstVar* const varp = new AstVar{fl_nowarn, VVarType::MODULETEMP, trace_var_name,
                                            incp->findUInt32DType()};
            varp->setIgnoreSchedWrite();  // Ignore the increment output, so no UNOPTFLAT
            varp->trace(true);
            m_modp->addStmtsp(varp);
            UINFO(5, "New coverage trace: " << varp);
            AstAssign* const assp = new AstAssign{
                incp->fileline(), new AstVarRef{incp->fileline(), varp, VAccess::WRITE},
                new AstAdd{incp->fileline(), new AstVarRef{incp->fileline(), varp, VAccess::READ},
                           new AstConst{incp->fileline(), AstConst::WidthedValue{}, 32, 1}}};
            AstNode::addNext<AstNode, AstNode>(incp, assp);
        }
        return incp;
    }
    string traceNameForLine(AstNode* nodep, const string& type) {
        string name = "vlCoverageLineTrace_" + nodep->fileline()->filebasenameNoExt() + "__"
                      + cvtToStr(nodep->fileline()->lineno()) + "_" + type;
        if (const uint32_t suffix = m_varnames[name]++) name += "_" + cvtToStr(suffix);
        return name;
    }

    // Line tracking
    void createHandle(const AstNode* nodep) {
        // Start tracking lines for the given handling node
        // If and if's else have separate handles for same nodep,
        // so nodep cannot have a pointer to a unique handle
        m_state.m_on = true;
        m_state.m_handle = ++m_nextHandle;
        // Ensure line numbers we track are in the same file as this block
        // so track via nodep
        m_state.m_nodep = nodep;
        UINFO(9, "line create h" << m_state.m_handle << " " << nodep);
    }
    void lineTrack(const AstNode* nodep) {
        if (m_state.lineCoverageOn(nodep) && !m_ifCond
            && m_state.m_nodep->fileline()->filenameno() == nodep->fileline()->filenameno()) {
            for (int lineno = nodep->fileline()->firstLineno();
                 lineno <= nodep->fileline()->lastLineno(); ++lineno) {
                UINFO(9, "line track " << lineno << " for h" << m_state.m_handle << " "
                                       << m_state.m_nodep);
                m_handleLines[m_state.m_handle].insert(lineno);
            }
        }
    }
    static string linesFirstLast(const int first, const int last) {
        if (first && first == last) {
            return cvtToStr(first);
        } else if (first && last) {
            return cvtToStr(first) + "-" + cvtToStr(last);
        } else {
            return "";
        }
    }
    string linesCov(const CheckState& state, const AstNode* nodep) {
        // Return comma separated list of ranged numbers
        string out;
        const LinenoSet& lines = m_handleLines[state.m_handle];
        int first = 0;
        int last = 0;
        for (int linen : lines) {
            if (!first) {
                first = last = linen;
            } else if (linen == last + 1) {
                ++last;
            } else {
                if (!out.empty()) out += ",";
                out += linesFirstLast(first, last);
                first = last = linen;
            }
        }
        if (first) {
            if (!out.empty()) out += ",";
            out += linesFirstLast(first, last);
        }
        UINFO(9, "lines out " << out << " for h" << state.m_handle << " " << nodep);
        return out;
    }

    // VISITORS - BOTH
    void visit(AstNodeModule* nodep) override {
        const AstNodeModule* const origModp = m_modp;
        VL_RESTORER(m_modp);
        VL_RESTORER(m_state);
        createHandle(nodep);
        m_modp = nodep;
        m_state.m_inModOff
            = nodep->isTop();  // Ignore coverage on top module; it's a shell we created
        if (!origModp) {
            // No blocks cross (non-nested) modules, so save some memory
            m_varnames.clear();
            m_handleLines.clear();
        }
        iterateChildren(nodep);
    }

    void visit(AstNodeProcedure* nodep) override { iterateProcedure(nodep); }
    // we can cover expressions in while loops, but the counting goes outside
    // the while, see: "minimally-intelligent decision about ... clock domain"
    // in the Toggle Coverage docs
    void visit(AstWhile* nodep) override {
        VL_RESTORER(m_state);
        VL_RESTORER(m_inToggleOff);
        m_inToggleOff = true;
        createHandle(nodep);
        {
            VL_RESTORER(m_inLoopNotBody);
            m_inLoopNotBody = true;
            iterateAndNextNull(nodep->precondsp());
            iterateNull(nodep->condp());
            iterateAndNextNull(nodep->incsp());
        }
        iterateAndNextNull(nodep->stmtsp());
        if (m_state.lineCoverageOn(nodep)) {
            lineTrack(nodep);
            AstNode* const newp
                = newCoverInc(nodep->fileline(), "", "v_line", "block", linesCov(m_state, nodep),
                              0, traceNameForLine(nodep, "block"));
            insertProcStatement(nodep, newp);
        }
    }

    void visit(AstNodeFTask* nodep) override {
        if (!nodep->dpiImport()) iterateProcedure(nodep);
    }

    void insertProcStatement(AstNode* nodep, AstNode* stmtp) {
        if (AstNodeProcedure* const itemp = VN_CAST(nodep, NodeProcedure)) {
            itemp->addStmtsp(stmtp);
        } else if (AstNodeFTask* const itemp = VN_CAST(nodep, NodeFTask)) {
            itemp->addStmtsp(stmtp);
        } else if (AstWhile* const itemp = VN_CAST(nodep, While)) {
            itemp->addStmtsp(stmtp);
        } else if (AstIf* const itemp = VN_CAST(nodep, If)) {
            if (m_then) {
                itemp->addThensp(stmtp);
            } else {
                itemp->addElsesp(stmtp);
            }
        } else {
            nodep->v3fatalSrc("Bad node type");
        }
    }
    void iterateProcedure(AstNode* nodep) {
        VL_RESTORER(m_state);
        VL_RESTORER(m_exprStmtsp);
        VL_RESTORER(m_inToggleOff);
        m_exprStmtsp = nodep;
        m_inToggleOff = true;
        createHandle(nodep);
        iterateChildren(nodep);
        if (m_state.lineCoverageOn(nodep)) {
            lineTrack(nodep);
            AstNode* const newp
                = newCoverInc(nodep->fileline(), "", "v_line", "block", linesCov(m_state, nodep),
                              0, traceNameForLine(nodep, "block"));
            insertProcStatement(nodep, newp);
        }
    }

    // VISITORS - TOGGLE COVERAGE
    void visit(AstVar* nodep) override {
        iterateChildren(nodep);
        if (m_modp && !m_inToggleOff && !m_state.m_inModOff && nodep->fileline()->coverageOn()
            && v3Global.opt.coverageToggle()) {
            const char* const disablep = varIgnoreToggle(nodep);
            if (disablep) {
                UINFO(4, "    Disable Toggle: " << disablep << " " << nodep);
            } else {
                UINFO(4, "    Toggle: " << nodep);
                // There's several overall ways to approach this
                //    Treat like tracing, where a end-of-timestamp action sees all changes
                //      Works ok, but would be quite slow as need to reform
                //      vectors before the calls
                //    Convert to "always @ (posedge signal[#]) coverinc"
                //      Would mark many signals as clocks, precluding many later optimizations
                //    Convert to "if (x & !lastx) CoverInc"
                //      OK, but we couldn't later detect them to schedule where the IFs get called
                //    Convert to "AstCoverInc(CoverInc...)"
                //      We'll do this, and make the if(...) coverinc later.

                // Add signal to hold the old value
                const string newvarname = "__Vtogcov__"s + m_beginHier + nodep->shortName();
                FileLine* const fl_nowarn = new FileLine{nodep->fileline()};
                fl_nowarn->modifyWarnOff(V3ErrorCode::UNUSEDSIGNAL, true);
                AstVar* const chgVarp
                    = new AstVar{fl_nowarn, VVarType::MODULETEMP, newvarname, nodep};
                m_modp->addStmtsp(chgVarp);

                AstVar* initVarp = nullptr;
                AstVarRef* initVarRefp = nullptr;
                const AstBasicDType* const basicDTypep
                    = VN_CAST(nodep->dtypep()->skipRefp(), BasicDType);
                if (basicDTypep && basicDTypep->isFourstate() && basicDTypep->isBitLogic()
                    && basicDTypep->widthTotalBytes() == 1) {
                    const string initVarName
                        = "__Vtogcovinit__"s + m_beginHier + nodep->shortName();
                    AstBasicDType* const initDtypep
                        = new AstBasicDType{fl_nowarn, VBasicDTypeKwd::INT, VSigning::NOSIGN};
                    v3Global.rootp()->typeTablep()->addTypesp(initDtypep);
                    initVarp
                        = new AstVar{fl_nowarn, VVarType::MODULETEMP, initVarName, initDtypep};
                    m_modp->addStmtsp(initVarp);
                    nodep->user1p(initVarp);
                    initVarRefp = new AstVarRef{fl_nowarn, initVarp, VAccess::WRITE};
                    AstAssign* const initAssignp
                        = new AstAssign{fl_nowarn, initVarRefp->cloneTree(false),
                                        new AstConst{fl_nowarn, AstConst::All0{}}};
                    m_modp->addStmtsp(new AstInitialStatic{fl_nowarn, initAssignp});
                }

                // Create bucket for each dimension * bit.
                // This is necessarily an O(n^2) expansion, which is why
                // we limit coverage to signals with < 256 bits.

                ToggleEnt newvec{""s, new AstVarRef{fl_nowarn, nodep, VAccess::READ},
                                 new AstVarRef{fl_nowarn, chgVarp, VAccess::WRITE}, initVarRefp};
                toggleVarRecurse(nodep->dtypeSkipRefp(), 0, newvec, nodep);
                newvec.cleanup();
            }
        }
    }

    void toggleVarBottom(const ToggleEnt& above, const AstVar* varp) {
        const std::string hierPrefix
            = (m_beginHier != "") ? AstNode::prettyName(m_beginHier) + "." : "";
        AstCoverToggle* const newp = new AstCoverToggle{
            varp->fileline(),
            newCoverInc(varp->fileline(), "", "v_toggle",
                        hierPrefix + varp->name() + above.m_comment, "", 0, ""),
            above.m_varRefp->cloneTree(false), above.m_chgRefp->cloneTree(false),
            above.m_initRefp ? above.m_initRefp->cloneTree(false) : nullptr};
        m_modp->addStmtsp(newp);
    }

    void toggleVarRecurse(const AstNodeDType* const dtypep, const int depth,  // per-iteration
                          const ToggleEnt& above, const AstVar* const varp) {  // Constant
        if (const AstBasicDType* const bdtypep = VN_CAST(dtypep, BasicDType)) {
            if (bdtypep->isRanged()) {
                for (int index_docs = bdtypep->lo(); index_docs < bdtypep->hi() + 1;
                     ++index_docs) {
                    const int index_code = index_docs - bdtypep->lo();
                    ToggleEnt newent{above.m_comment + "["s + cvtToStr(index_docs) + "]",
                                     new AstSel{varp->fileline(),
                                                above.m_varRefp->cloneTree(false), index_code, 1},
                                     new AstSel{varp->fileline(),
                                                above.m_chgRefp->cloneTree(false), index_code, 1},
                                     above.m_initRefp
                                         ? new AstSel{varp->fileline(),
                                                      above.m_initRefp->cloneTree(false),
                                                      index_code, 1}
                                         : nullptr};
                    toggleVarBottom(newent, varp);
                    newent.cleanup();
                }
            } else {
                toggleVarBottom(above, varp);
            }
        } else if (const AstUnpackArrayDType* const adtypep = VN_CAST(dtypep, UnpackArrayDType)) {
            for (int index_docs = adtypep->lo(); index_docs <= adtypep->hi(); ++index_docs) {
                const int index_code = index_docs - adtypep->lo();
                ToggleEnt newent{above.m_comment + "["s + cvtToStr(index_docs) + "]",
                                 new AstArraySel{varp->fileline(),
                                                 above.m_varRefp->cloneTree(false), index_code},
                                 new AstArraySel{varp->fileline(),
                                                 above.m_chgRefp->cloneTree(false), index_code},
                                 above.m_initRefp
                                     ? new AstArraySel{varp->fileline(),
                                                       above.m_initRefp->cloneTree(false),
                                                       index_code}
                                     : nullptr};
                toggleVarRecurse(adtypep->subDTypep()->skipRefp(), depth + 1, newent, varp);
                newent.cleanup();
            }
        } else if (const AstPackArrayDType* const adtypep = VN_CAST(dtypep, PackArrayDType)) {
            for (int index_docs = adtypep->lo(); index_docs <= adtypep->hi(); ++index_docs) {
                const AstNodeDType* const subtypep = adtypep->subDTypep()->skipRefp();
                const int index_code = index_docs - adtypep->lo();
                ToggleEnt newent{
                    above.m_comment + "["s + cvtToStr(index_docs) + "]",
                    new AstSel{varp->fileline(), above.m_varRefp->cloneTree(false),
                               index_code * subtypep->width(), subtypep->width()},
                    new AstSel{varp->fileline(), above.m_chgRefp->cloneTree(false),
                               index_code * subtypep->width(), subtypep->width()},
                    above.m_initRefp
                        ? new AstSel{varp->fileline(), above.m_initRefp->cloneTree(false),
                                     index_code * subtypep->width(), subtypep->width()}
                        : nullptr};
                toggleVarRecurse(adtypep->subDTypep()->skipRefp(), depth + 1, newent, varp);
                newent.cleanup();
            }
        } else if (const AstStructDType* const adtypep = VN_CAST(dtypep, StructDType)) {
            if (adtypep->packed()) {
                for (AstMemberDType* itemp = adtypep->membersp(); itemp;
                     itemp = VN_AS(itemp->nextp(), MemberDType)) {
                    AstNodeDType* const subtypep = itemp->subDTypep()->skipRefp();
                    const int index_code = itemp->lsb();
                    ToggleEnt newent{
                        above.m_comment + "."s + itemp->name(),
                        new AstSel{varp->fileline(), above.m_varRefp->cloneTree(false), index_code,
                                   subtypep->width()},
                        new AstSel{varp->fileline(), above.m_chgRefp->cloneTree(false), index_code,
                                   subtypep->width()},
                        above.m_initRefp
                            ? new AstSel{varp->fileline(), above.m_initRefp->cloneTree(false),
                                         index_code, subtypep->width()}
                            : nullptr};
                    toggleVarRecurse(subtypep, depth + 1, newent, varp);
                    newent.cleanup();
                }
            } else {
                for (AstMemberDType* itemp = adtypep->membersp(); itemp;
                     itemp = VN_AS(itemp->nextp(), MemberDType)) {
                    AstNodeDType* const subtypep = itemp->subDTypep()->skipRefp();
                    AstNodeExpr* const varRefp = new AstStructSel{
                        varp->fileline(), above.m_varRefp->cloneTree(false), itemp->name()};
                    AstNodeExpr* const chgRefp = new AstStructSel{
                        varp->fileline(), above.m_chgRefp->cloneTree(false), itemp->name()};
                    AstNodeExpr* const initRefp
                        = above.m_initRefp
                              ? new AstStructSel{varp->fileline(),
                                                 above.m_initRefp->cloneTree(false), itemp->name()}
                              : nullptr;
                    varRefp->dtypep(subtypep);
                    chgRefp->dtypep(subtypep);
                    initRefp->dtypep(subtypep);
                    ToggleEnt newent{above.m_comment + "."s + itemp->name(), varRefp, chgRefp,
                                     initRefp};
                    toggleVarRecurse(subtypep, depth + 1, newent, varp);
                    newent.cleanup();
                }
            }
        } else if (const AstUnionDType* const adtypep = VN_CAST(dtypep, UnionDType)) {
            // Arbitrarily handle only the first member of the union
            if (const AstMemberDType* const itemp = adtypep->membersp()) {
                AstNodeDType* const subtypep = itemp->subDTypep()->skipRefp();
                if (adtypep->packed()) {
                    ToggleEnt newent{
                        above.m_comment + "."s + itemp->name(), above.m_varRefp->cloneTree(false),
                        above.m_chgRefp->cloneTree(false),
                        above.m_initRefp ? above.m_initRefp->cloneTree(false) : nullptr};
                    toggleVarRecurse(subtypep, depth + 1, newent, varp);
                    newent.cleanup();
                } else {
                    AstNodeExpr* const varRefp = new AstStructSel{
                        varp->fileline(), above.m_varRefp->cloneTree(false), itemp->name()};
                    AstNodeExpr* const chgRefp = new AstStructSel{
                        varp->fileline(), above.m_chgRefp->cloneTree(false), itemp->name()};
                    AstNodeExpr* const initRefp
                        = above.m_initRefp
                              ? new AstStructSel{varp->fileline(),
                                                 above.m_initRefp->cloneTree(false), itemp->name()}
                              : nullptr;
                    varRefp->dtypep(subtypep);
                    chgRefp->dtypep(subtypep);
                    initRefp->dtypep(subtypep);
                    ToggleEnt newent{above.m_comment + "."s + itemp->name(), varRefp, chgRefp,
                                     initRefp};
                    toggleVarRecurse(subtypep, depth + 1, newent, varp);
                    newent.cleanup();
                }
            }
        } else if (VN_IS(dtypep, QueueDType)) {
            // Not covered
        } else {
            dtypep->v3fatalSrc("Unexpected node data type in toggle coverage generation: "
                               << dtypep->prettyTypeName());
        }
    }
    bool includeCondToBranchRecursive(const AstNode* const nodep) {
        const AstNode* const backp = nodep->backp();
        if (VN_IS(backp, Cond) && VN_AS(backp, Cond)->condp() != nodep) {
            return includeCondToBranchRecursive(backp);
        } else if (VN_IS(backp, Sel) && VN_AS(backp, Sel)->fromp() == nodep) {
            return includeCondToBranchRecursive(backp);
        } else if (VN_IS(backp, NodeAssign) && VN_AS(backp, NodeAssign)->rhsp() == nodep
                   && !m_inLoopNotBody) {
            return true;
        }
        return false;
    }

    // VISITORS - LINE COVERAGE
    void visit(AstCond* nodep) override {
        UINFO(4, " COND: " << nodep);

        if (m_seeking == NONE) coverExprs(nodep->condp());

        if (m_state.lineCoverageOn(nodep) && VN_IS(m_modp, Module)
            && includeCondToBranchRecursive(nodep)) {
            VL_RESTORER(m_seeking);
            // Disable expression coverage in sub-expressions, since they were already visited
            m_seeking = ABORTED;

            const CheckState lastState = m_state;
            createHandle(nodep);
            iterate(nodep->thenp());
            lineTrack(nodep);
            AstNodeExpr* const thenp = nodep->thenp()->unlinkFrBack();
            nodep->thenp(new AstExprStmt{thenp->fileline(),
                                         newCoverInc(nodep->fileline(), "", "v_branch",
                                                     "cond_then", linesCov(m_state, nodep), 0,
                                                     traceNameForLine(nodep, "cond_then")),
                                         thenp});
            m_state = lastState;
            createHandle(nodep);
            iterate(nodep->elsep());
            AstNodeExpr* const elsep = nodep->elsep()->unlinkFrBack();
            nodep->elsep(new AstExprStmt{elsep->fileline(),
                                         newCoverInc(nodep->fileline(), "", "v_branch",
                                                     "cond_else", linesCov(m_state, nodep), 1,
                                                     traceNameForLine(nodep, "cond_else")),
                                         elsep});

            m_state = lastState;
        } else {
            lineTrack(nodep);
        }
    }
    // Note not AstNodeIf; other types don't get covered
    void visit(AstIf* nodep) override {
        if (nodep->user2()) return;

        UINFO(4, " IF: " << nodep);
        if (m_state.m_on) {
            // An else-if.  When we iterate the if, use "elsif" marking
            const bool elsif
                = nodep->thensp() && VN_IS(nodep->elsesp(), If) && !nodep->elsesp()->nextp();
            if (elsif) VN_AS(nodep->elsesp(), If)->user1(true);
            const bool first_elsif = !nodep->user1() && elsif;
            const bool cont_elsif = nodep->user1() && elsif;
            const bool final_elsif = nodep->user1() && !elsif && nodep->elsesp();
            //
            // Considered: If conditional is on a different line from if/else then we
            // can show it as part of line coverage of the statement
            // above. Otherwise show it based on what is inside.
            // But: Seemed too complicated, and fragile.
            const CheckState lastState = m_state;
            CheckState ifState;
            CheckState elseState;
            {
                VL_RESTORER(m_exprStmtsp);
                VL_RESTORER(m_then);
                m_exprStmtsp = nodep;
                m_then = true;
                createHandle(nodep);
                iterateAndNextNull(nodep->thensp());
                lineTrack(nodep);
                ifState = m_state;
            }
            m_state = lastState;
            {
                VL_RESTORER(m_exprStmtsp);
                VL_RESTORER(m_then);
                m_exprStmtsp = nodep;
                m_then = false;
                createHandle(nodep);
                iterateAndNextNull(nodep->elsesp());
                elseState = m_state;
            }
            m_state = lastState;
            //
            // If both if and else are "on", and we're not in an if/else, then
            // we do branch coverage
            if (!(first_elsif || cont_elsif || final_elsif) && ifState.lineCoverageOn(nodep)
                && elseState.lineCoverageOn(nodep)) {
                // Normal if. Linecov shows what's inside the if (not condition that is
                // always executed)
                UINFO(4, "   COVER-branch: " << nodep);
                nodep->addThensp(newCoverInc(nodep->fileline(), "", "v_branch", "if",
                                             linesCov(ifState, nodep), 0,
                                             traceNameForLine(nodep, "if")));
                // The else has a column offset of 1 to uniquify it relative to the if
                // As "if" and "else" are more than one character wide, this won't overlap
                // another token
                nodep->addElsesp(newCoverInc(nodep->fileline(), "", "v_branch", "else",
                                             linesCov(elseState, nodep), 1,
                                             traceNameForLine(nodep, "else")));
            }
            // If/else attributes to each block as non-branch coverage
            else if (first_elsif || cont_elsif) {
                UINFO(4, "   COVER-elsif: " << nodep);
                if (ifState.lineCoverageOn(nodep)) {
                    nodep->addThensp(newCoverInc(nodep->fileline(), "", "v_line", "elsif",
                                                 linesCov(ifState, nodep), 0,
                                                 traceNameForLine(nodep, "elsif")));
                }
                // and we don't insert the else as the child if-else will do so
            } else {
                // Cover as separate blocks (not a branch as is not two-legged)
                if (ifState.lineCoverageOn(nodep)) {
                    UINFO(4, "   COVER-half-if: " << nodep);
                    nodep->addThensp(newCoverInc(nodep->fileline(), "", "v_line", "if",
                                                 linesCov(ifState, nodep), 0,
                                                 traceNameForLine(nodep, "if")));
                }
                if (elseState.lineCoverageOn(nodep)) {
                    UINFO(4, "   COVER-half-el: " << nodep);
                    nodep->addElsesp(newCoverInc(nodep->fileline(), "", "v_line", "else",
                                                 linesCov(elseState, nodep), 1,
                                                 traceNameForLine(nodep, "else")));
                }
            }
            m_state = lastState;
        }
        VL_RESTORER(m_ifCond);
        m_ifCond = true;
        iterateAndNextNull(nodep->condp());
        UINFO(9, " done HANDLE " << m_state.m_handle << " for " << nodep);
    }
    void visit(AstCaseItem* nodep) override {
        // We don't add an explicit "default" coverage if not provided,
        // as we already have a warning when there is no default.
        UINFO(4, " CASEI: " << nodep);
        if (m_state.lineCoverageOn(nodep)) {
            VL_RESTORER(m_state);
            createHandle(nodep);
            iterateAndNextNull(nodep->stmtsp());
            if (m_state.lineCoverageOn(nodep)) {  // if the case body didn't disable it
                lineTrack(nodep);
                UINFO(4, "   COVER: " << nodep);
                nodep->addStmtsp(newCoverInc(nodep->fileline(), "", "v_line", "case",
                                             linesCov(m_state, nodep), 0,
                                             traceNameForLine(nodep, "case")));
            }
        }
    }
    void visit(AstCover* nodep) override {
        UINFO(4, " COVER: " << nodep);
        VL_RESTORER(m_state);
        m_state.m_on = true;  // Always do cover blocks, even if there's a $stop
        createHandle(nodep);
        iterateChildren(nodep);
        if (!nodep->coverincsp() && v3Global.opt.coverageUser()) {
            // Note the name may be overridden by V3Assert processing
            lineTrack(nodep);
            nodep->addCoverincsp(newCoverInc(nodep->fileline(), m_beginHier, "v_user", "cover",
                                             linesCov(m_state, nodep), 0,
                                             m_beginHier + "_vlCoverageUserTrace"));
        }
    }
    void visit(AstStop* nodep) override {
        UINFO(4, "  STOP: " << nodep);
        m_state.m_on = false;
    }
    void visit(AstPragma* nodep) override {
        if (nodep->pragType() == VPragmaType::COVERAGE_BLOCK_OFF) {
            // Skip all NEXT nodes under this block, and skip this if/case branch
            UINFO(4, "  OFF: h" << m_state.m_handle << " " << nodep);
            m_state.m_on = false;
            VL_DO_DANGLING(nodep->unlinkFrBack()->deleteTree(), nodep);
        } else {
            if (m_state.m_on) iterateChildren(nodep);
            lineTrack(nodep);
        }
    }
    void visit(AstBegin* nodep) override {
        // Record the hierarchy of any named begins, so we can apply to user
        // coverage points.  This is because there may be cov points inside
        // generate blocks; each point should get separate consideration.
        // (Currently ignored for line coverage, since any generate iteration
        // covers the code in that line.)
        VL_RESTORER(m_beginHier);
        VL_RESTORER(m_inToggleOff);
        if (!nodep->generate()) m_inToggleOff = true;
        if (nodep->name() != "") {
            m_beginHier = m_beginHier + (m_beginHier != "" ? "__DOT__" : "") + nodep->name();
        }
        iterateChildren(nodep);
        lineTrack(nodep);
    }

    void abortExprCoverage() {
        // is possible to hit max while in NONE, see: exprReduce()
        // if that happens we don't want to set ABORTED if it isn't already
        // since that will bleed into other expressions
        if (m_seeking != NONE) m_seeking = ABORTED;
        m_exprs.clear();
    }

    bool checkMaxExprs(size_t additional = 0) {
        if (m_seeking != ABORTED
            && static_cast<int>(m_exprs.size() + additional) <= v3Global.opt.coverageExprMax())
            return false;
        abortExprCoverage();
        return true;
    }

    void addExprCoverInc(AstNodeExpr* nodep, int start = 0) {
        FileLine* const fl = nodep->fileline();
        int count = start;
        for (CoverExpr& expr : m_exprs) {
            const string name = "expr_" + std::to_string(count);
            string comment = "(";
            bool first = true;
            AstNodeExpr* condp = nullptr;
            for (CoverTerm& term : expr) {
                comment += (first ? "" : " && ") + term.m_emitV
                           + "==" + (term.m_objective ? "1" : "0");
                AstNodeExpr* const clonep = term.m_exprp->cloneTree(false);
                AstNodeExpr* const termp = term.m_objective ? clonep : new AstLogNot{fl, clonep};
                if (condp) {
                    condp = new AstLogAnd{fl, condp, termp};
                } else {
                    condp = termp;
                }
                first = false;
            }
            comment += ") => ";
            comment += (m_objective ? '1' : '0');
            AstNode* const newp
                = newCoverInc(fl, "", "v_expr", comment, "", 0, traceNameForLine(nodep, name));
            UASSERT_OBJ(condp, nodep, "No terms in expression coverage branch");
            AstIf* const ifp = new AstIf{fl, condp, newp, nullptr};
            ifp->user2(true);
            insertProcStatement(m_exprStmtsp, ifp);
            ++count;
        }
    }

    void coverExprs(AstNodeExpr* nodep) {
        if (!m_state.exprCoverageOn(nodep) || nodep->dtypep()->width() != 1 || !m_exprStmtsp) {
            return;
        }

        UASSERT_OBJ(m_seeking == NONE, nodep, "recursively covering expressions is not expected");
        UASSERT_OBJ(m_exprs.empty(), nodep, "unexpected expression coverage garbage");
        VL_RESTORER(m_seeking);
        VL_RESTORER(m_objective);
        VL_RESTORER(m_exprs);

        m_seeking = SEEKING;
        m_objective = false;
        iterate(nodep);
        CoverExprs falseExprs;
        m_exprs.swap(falseExprs);

        m_objective = true;
        iterate(nodep);
        if (checkMaxExprs(falseExprs.size())) return;
        if (m_seeking == ABORTED) return;

        addExprCoverInc(nodep);
        const int start = m_exprs.size();
        m_objective = false;
        m_exprs.swap(falseExprs);
        addExprCoverInc(nodep, start);
    }

    void exprEither(AstNodeBiop* nodep, bool overrideObjective = false, bool lObjective = false,
                    bool rObjective = false) {
        VL_RESTORER(m_objective);
        AstNodeExpr* const lhsp = nodep->lhsp();
        AstNodeExpr* const rhsp = nodep->rhsp();

        if (overrideObjective) m_objective = lObjective;
        iterate(lhsp);
        if (checkMaxExprs()) return;
        CoverExprs lhsExprs;
        m_exprs.swap(lhsExprs);
        if (overrideObjective) m_objective = rObjective;
        iterate(rhsp);
        m_exprs.splice(m_exprs.end(), lhsExprs);
        checkMaxExprs();
    }

    void exprBoth(AstNodeBiop* nodep, bool overrideObjective = false, bool lObjective = false,
                  bool rObjective = false) {
        VL_RESTORER(m_objective);
        AstNodeExpr* const lhsp = nodep->lhsp();
        AstNodeExpr* const rhsp = nodep->rhsp();

        if (overrideObjective) m_objective = lObjective;
        iterate(lhsp);
        if (checkMaxExprs()) return;
        CoverExprs lhsExprs;
        m_exprs.swap(lhsExprs);
        if (overrideObjective) m_objective = rObjective;
        iterate(rhsp);
        if (checkMaxExprs()) return;
        CoverExprs rhsExprs;
        m_exprs.swap(rhsExprs);

        for (CoverExpr& l : lhsExprs) {
            for (CoverExpr& r : rhsExprs) {
                // array size 2 -> (false, true)
                std::array<std::set<AstVar*>, 2> varps;
                std::array<std::set<std::string>, 2> strs;

                UASSERT_OBJ(!l.empty() && !r.empty(), nodep, "Empty coverage expression branch");
                CoverExpr expr;

                // Compare Vars for simple VarRefs otherwise compare stringified terms
                // remove redundant terms and remove entire expression branches when
                // terms conflict
                // Equivalent terms which don't match on either of these criteria will
                // not be flagged as redundant or impossible, however the results will
                // still be valid, albeit messier
                for (CoverTerm& term : l) {
                    if (AstVarRef* const refp = VN_CAST(term.m_exprp, VarRef)) {
                        varps[term.m_objective].insert(refp->varp());
                    } else {
                        strs[term.m_objective].insert(term.m_emitV);
                    }
                    expr.push_back(term);
                }
                bool impossible = false;
                for (CoverTerm& term : r) {
                    bool redundant = false;
                    if (AstNodeVarRef* const refp = VN_CAST(term.m_exprp, NodeVarRef)) {
                        if (varps[term.m_objective].find(refp->varp())
                            != varps[term.m_objective].end())
                            redundant = true;
                        if (varps[!term.m_objective].find(refp->varp())
                            != varps[!term.m_objective].end())
                            impossible = true;
                    } else {
                        if (strs[term.m_objective].find(term.m_emitV)
                            != strs[term.m_objective].end())
                            redundant = true;
                        if (strs[!term.m_objective].find(term.m_emitV)
                            != strs[!term.m_objective].end())
                            impossible = true;
                    }

                    if (!redundant) expr.push_back(term);
                }
                if (!impossible) m_exprs.push_back(std::move(expr));
                if (checkMaxExprs()) return;
            }
        }
    }

    void orExpr(AstNodeBiop* nodep) {
        if (m_seeking == NONE) {
            coverExprs(nodep);
        } else if (m_objective) {
            exprEither(nodep);
        } else {
            exprBoth(nodep);
        }
        lineTrack(nodep);
    }
    void visit(AstLogOr* nodep) override { orExpr(nodep); }
    void visit(AstOr* nodep) override { orExpr(nodep); }

    void andExpr(AstNodeBiop* nodep) {
        if (m_seeking == NONE) {
            coverExprs(nodep);
        } else if (m_objective) {
            exprBoth(nodep);
        } else {
            exprEither(nodep);
        }
        lineTrack(nodep);
    }
    void visit(AstLogAnd* nodep) override { andExpr(nodep); }
    void visit(AstAnd* nodep) override { andExpr(nodep); }

    void xorExpr(AstNodeBiop* nodep) {
        if (m_seeking == NONE) {
            coverExprs(nodep);
        } else {
            for (const bool lObjective : {false, true}) {
                CoverExprs prevExprs;
                m_exprs.swap(prevExprs);
                const bool rObjective = lObjective ^ m_objective;
                exprBoth(nodep, true, lObjective, rObjective);
                m_exprs.splice(m_exprs.end(), prevExprs);
                if (checkMaxExprs()) break;
            }
        }
        lineTrack(nodep);
    }
    void visit(AstXor* nodep) override { xorExpr(nodep); }

    void exprNot(AstNodeExpr* nodep) {
        VL_RESTORER(m_objective);
        if (m_seeking == NONE) {
            coverExprs(nodep);
        } else {
            m_objective = !m_objective;
            iterateChildren(nodep);
            lineTrack(nodep);
        }
    }
    void visit(AstNot* nodep) override { exprNot(nodep); }
    void visit(AstLogNot* nodep) override { exprNot(nodep); }

    template <typename T_Oper>
    void exprReduce(AstNodeUniop* nodep) {
        if (m_seeking != ABORTED) {
            FileLine* const fl = nodep->fileline();
            AstNodeExpr* const lhsp = nodep->lhsp();
            const int width = lhsp->dtypep()->width();
            const size_t expected = std::is_same<T_Oper, AstXor>::value ? 0x1 << width : width + 1;
            if (checkMaxExprs(expected)) return;
            AstNodeExpr* unrolledp = new AstSel{fl, lhsp->cloneTree(false),
                                                new AstConst{fl, static_cast<uint32_t>(width - 1)},
                                                new AstConst{fl, 1}};
            for (int bit = width - 2; bit >= 0; bit--) {
                AstSel* const selp = new AstSel{fl, lhsp->cloneTree(false),
                                                new AstConst{fl, static_cast<uint32_t>(bit)},
                                                new AstConst{fl, 1}};
                unrolledp = new T_Oper{fl, selp, unrolledp};
            }
            iterate(unrolledp);
            pushDeletep(unrolledp);
        } else {
            iterateChildren(nodep);
            lineTrack(nodep);
        }
    }
    void visit(AstRedOr* nodep) override { exprReduce<AstOr>(nodep); }
    void visit(AstRedAnd* nodep) override { exprReduce<AstAnd>(nodep); }
    void visit(AstRedXor* nodep) override { exprReduce<AstXor>(nodep); }

    void visit(AstLogIf* nodep) override {
        if (m_seeking == NONE) {
            coverExprs(nodep);
        } else if (m_objective) {
            exprEither(nodep, true, false, true);
        } else {
            exprBoth(nodep, true, true, false);
        }
        lineTrack(nodep);
    }

    void visit(AstLogEq* nodep) override {
        VL_RESTORER(m_objective);
        if (m_seeking == NONE) {
            coverExprs(nodep);
        } else {
            m_objective = !m_objective;
            xorExpr(nodep);
            lineTrack(nodep);
        }
    }

    void visit(AstFuncRef* nodep) override {
        if (nodep->taskp()->lifetime().isAutomatic()) {
            visit(static_cast<AstNodeExpr*>(nodep));
        } else {
            exprUnsupported(nodep, "non-automatic function");
        }
    }

    void visit(AstNodeExpr* nodep) override {
        if (m_seeking != SEEKING) {
            iterateChildren(nodep);
        } else {
            ExprCoverageEligibleVisitor elgibleVisitor(nodep);
            if (elgibleVisitor.eligible()) {
                std::stringstream emitV;
                V3EmitV::verilogForTree(nodep, emitV);
                // Add new expression with a single term
                CoverExpr expr;
                expr.emplace_back(nodep, m_objective, emitV.str());
                m_exprs.push_back(std::move(expr));
                checkMaxExprs();
            } else {
                exprUnsupported(nodep, "not coverage eligible");
            }
        }
        lineTrack(nodep);
    }

    // VISITORS - BOTH
    void visit(AstNodeAssign* nodep) override {
        if (AstNodeVarRef* const varRefp = VN_CAST(nodep->lhsp(), NodeVarRef)) {
            if (varRefp->varp()->user1p()) {
                AstVarRef* const initLhsp = new AstVarRef{
                    varRefp->fileline(), VN_AS(varRefp->varp()->user1p(), Var), VAccess::WRITE};
                AstNodeAssign* const initAssignp = nodep->cloneType(
                    initLhsp, new AstConst{nodep->fileline(), AstConst::All1{}});
                AstVarRef* const initRhsp = new AstVarRef{
                    varRefp->fileline(), VN_AS(varRefp->varp()->user1p(), Var), VAccess::READ};
                AstIf* const initIfp = new AstIf{
                    nodep->fileline(),
                    new AstEq{nodep->fileline(), initRhsp, new AstConst{nodep->fileline(), 0}},
                    initAssignp};
                nodep->addNextHere(initIfp);
            }
        }
        iterateChildren(nodep);
        lineTrack(nodep);
    }

    void visit(AstNode* nodep) override {
        iterateChildren(nodep);
        lineTrack(nodep);
    }

    void exprUnsupported(AstNode* nodep, const string& why) {
        UINFO(9, "unsupported: " << why << " " << nodep);
        bool wasSeeking = m_seeking == SEEKING;
        Objective oldSeeking = m_seeking;
        if (wasSeeking) abortExprCoverage();
        m_seeking = ABORTED;
        iterateChildren(nodep);
        lineTrack(nodep);
        if (!wasSeeking) m_seeking = oldSeeking;
    }

public:
    // CONSTRUCTORS
    explicit CoverageVisitor(AstNetlist* rootp) { iterateChildren(rootp); }
    ~CoverageVisitor() override = default;
};

//######################################################################
// Coverage class functions

void V3Coverage::coverage(AstNetlist* rootp) {
    UINFO(2, __FUNCTION__ << ":");
    { CoverageVisitor{rootp}; }  // Destruct before checking
    V3Global::dumpCheckGlobalTree("coverage", 0, dumpTreeEitherLevel() >= 3);
}
