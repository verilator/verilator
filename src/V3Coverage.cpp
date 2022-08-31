// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Netlist (top level) functions
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2022 by Wilson Snyder. This program is free software; you
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

#include "config_build.h"
#include "verilatedos.h"

#include "V3Coverage.h"

#include "V3Ast.h"
#include "V3Global.h"

#include <map>
#include <unordered_map>

//######################################################################
// Coverage state, as a visitor of each AstNode

class CoverageVisitor final : public VNVisitor {
private:
    // TYPES
    using LinenoSet = std::set<int>;

    struct ToggleEnt {
        const string m_comment;  // Comment for coverage dump
        AstNode* m_varRefp;  // How to get to this element
        AstNode* m_chgRefp;  // How to get to this element
        ToggleEnt(const string& comment, AstNode* vp, AstNode* cp)
            : m_comment{comment}
            , m_varRefp{vp}
            , m_chgRefp{cp} {}
        ~ToggleEnt() = default;
        void cleanup() {
            VL_DO_CLEAR(m_varRefp->deleteTree(), m_varRefp = nullptr);
            VL_DO_CLEAR(m_chgRefp->deleteTree(), m_chgRefp = nullptr);
        }
    };

    struct CheckState {  // State save-restored on each new coverage scope/block
        bool m_on = false;  // Should this block get covered?
        bool m_inModOff = false;  // In module with no coverage
        int m_handle = 0;  // Opaque handle for index into line tracking
        const AstNode* m_nodep = nullptr;  // Node establishing this state
        CheckState() = default;
        bool lineCoverageOn(const AstNode* nodep) const {
            return m_on && !m_inModOff && nodep->fileline()->coverageOn()
                   && v3Global.opt.coverageLine();
        }
    };
    int m_nextHandle = 0;

    // NODE STATE
    // Entire netlist:
    //  AstIf::user1()                  -> bool.  True indicates ifelse processed
    const VNUser1InUse m_inuser1;

    // STATE
    CheckState m_state;  // State save-restored on each new coverage scope/block
    AstNodeModule* m_modp = nullptr;  // Current module to add statement to
    bool m_inToggleOff = false;  // In function/task etc
    std::unordered_map<std::string, int> m_varnames;  // Uniquification of inserted variable names
    string m_beginHier;  // AstBegin hier name for user coverage points
    std::unordered_map<int, LinenoSet>
        m_handleLines;  // All line numbers for a given m_stateHandle

    // METHODS
    VL_DEBUG_FUNC;  // Declare debug()

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

        AstCoverDecl* const declp = new AstCoverDecl(fl, page, comment, linescov, offset);
        declp->hier(hier);
        m_modp->addStmtp(declp);
        UINFO(9, "new " << declp << endl);

        AstCoverInc* const incp = new AstCoverInc(fl, declp);
        if (!trace_var_name.empty() && v3Global.opt.traceCoverage()) {
            AstVar* const varp = new AstVar(incp->fileline(), VVarType::MODULETEMP, trace_var_name,
                                            incp->findUInt32DType());
            varp->trace(true);
            varp->fileline()->modifyWarnOff(V3ErrorCode::UNUSED, true);
            m_modp->addStmtp(varp);
            UINFO(5, "New coverage trace: " << varp << endl);
            AstAssign* const assp = new AstAssign(
                incp->fileline(), new AstVarRef(incp->fileline(), varp, VAccess::WRITE),
                new AstAdd(incp->fileline(), new AstVarRef(incp->fileline(), varp, VAccess::READ),
                           new AstConst(incp->fileline(), AstConst::WidthedValue(), 32, 1)));
            incp->addNext(assp);
        }
        return incp;
    }
    string traceNameForLine(AstNode* nodep, const string& type) {
        string name = "vlCoverageLineTrace_" + nodep->fileline()->filebasenameNoExt() + "__"
                      + cvtToStr(nodep->fileline()->lineno()) + "_" + type;
        const auto it = m_varnames.find(name);
        if (it == m_varnames.end()) {
            m_varnames.emplace(name, 1);
        } else {
            const int suffix = (it->second)++;
            name += "_" + cvtToStr(suffix);
        }
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
        UINFO(9, "line create h" << m_state.m_handle << " " << nodep << endl);
    }
    void lineTrack(const AstNode* nodep) {
        if (m_state.lineCoverageOn(nodep)
            && m_state.m_nodep->fileline()->filenameno() == nodep->fileline()->filenameno()) {
            for (int lineno = nodep->fileline()->firstLineno();
                 lineno <= nodep->fileline()->lastLineno(); ++lineno) {
                UINFO(9, "line track " << lineno << " for h" << m_state.m_handle << " "
                                       << m_state.m_nodep << endl);
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
        UINFO(9, "lines out " << out << " for h" << state.m_handle << " " << nodep << endl);
        return out;
    }

    // VISITORS - BOTH
    virtual void visit(AstNodeModule* nodep) override {
        const AstNodeModule* const origModp = m_modp;
        VL_RESTORER(m_modp);
        VL_RESTORER(m_state);
        {
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
    }

    virtual void visit(AstNodeProcedure* nodep) override { iterateProcedure(nodep); }
    virtual void visit(AstWhile* nodep) override { iterateProcedure(nodep); }
    virtual void visit(AstNodeFTask* nodep) override {
        if (!nodep->dpiImport()) iterateProcedure(nodep);
    }
    void iterateProcedure(AstNode* nodep) {
        VL_RESTORER(m_state);
        VL_RESTORER(m_inToggleOff);
        {
            m_inToggleOff = true;
            createHandle(nodep);
            iterateChildren(nodep);
            if (m_state.lineCoverageOn(nodep)) {
                lineTrack(nodep);
                AstNode* const newp
                    = newCoverInc(nodep->fileline(), "", "v_line", "block",
                                  linesCov(m_state, nodep), 0, traceNameForLine(nodep, "block"));
                if (AstNodeProcedure* const itemp = VN_CAST(nodep, NodeProcedure)) {
                    itemp->addStmtp(newp);
                } else if (AstNodeFTask* const itemp = VN_CAST(nodep, NodeFTask)) {
                    itemp->addStmtsp(newp);
                } else if (AstWhile* const itemp = VN_CAST(nodep, While)) {
                    itemp->addBodysp(newp);
                } else {
                    nodep->v3fatalSrc("Bad node type");
                }
            }
        }
    }

    // VISITORS - TOGGLE COVERAGE
    virtual void visit(AstVar* nodep) override {
        iterateChildren(nodep);
        if (m_modp && !m_inToggleOff && !m_state.m_inModOff && nodep->fileline()->coverageOn()
            && v3Global.opt.coverageToggle()) {
            const char* const disablep = varIgnoreToggle(nodep);
            if (disablep) {
                UINFO(4, "    Disable Toggle: " << disablep << " " << nodep << endl);
            } else {
                UINFO(4, "    Toggle: " << nodep << endl);
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
                const string newvarname = std::string{"__Vtogcov__"} + nodep->shortName();
                AstVar* const chgVarp
                    = new AstVar(nodep->fileline(), VVarType::MODULETEMP, newvarname, nodep);
                chgVarp->fileline()->modifyWarnOff(V3ErrorCode::UNUSED, true);
                m_modp->addStmtp(chgVarp);

                // Create bucket for each dimension * bit.
                // This is necessarily an O(n^2) expansion, which is why
                // we limit coverage to signals with < 256 bits.

                ToggleEnt newvec{std::string{""},
                                 new AstVarRef{nodep->fileline(), nodep, VAccess::READ},
                                 new AstVarRef{nodep->fileline(), chgVarp, VAccess::WRITE}};
                toggleVarRecurse(nodep->dtypeSkipRefp(), 0, newvec, nodep, chgVarp);
                newvec.cleanup();
            }
        }
    }

    void toggleVarBottom(const ToggleEnt& above, const AstVar* varp) {
        AstCoverToggle* const newp = new AstCoverToggle(
            varp->fileline(),
            newCoverInc(varp->fileline(), "", "v_toggle", varp->name() + above.m_comment, "", 0,
                        ""),
            above.m_varRefp->cloneTree(true), above.m_chgRefp->cloneTree(true));
        m_modp->addStmtp(newp);
    }

    void toggleVarRecurse(AstNodeDType* dtypep, int depth,  // per-iteration
                          const ToggleEnt& above, AstVar* varp, AstVar* chgVarp) {  // Constant
        if (const AstBasicDType* const bdtypep = VN_CAST(dtypep, BasicDType)) {
            if (bdtypep->isRanged()) {
                for (int index_docs = bdtypep->lo(); index_docs < bdtypep->hi() + 1;
                     ++index_docs) {
                    const int index_code = index_docs - bdtypep->lo();
                    ToggleEnt newent{above.m_comment + std::string{"["} + cvtToStr(index_docs)
                                         + "]",
                                     new AstSel{varp->fileline(), above.m_varRefp->cloneTree(true),
                                                index_code, 1},
                                     new AstSel{varp->fileline(), above.m_chgRefp->cloneTree(true),
                                                index_code, 1}};
                    toggleVarBottom(newent, varp);
                    newent.cleanup();
                }
            } else {
                toggleVarBottom(above, varp);
            }
        } else if (const AstUnpackArrayDType* const adtypep = VN_CAST(dtypep, UnpackArrayDType)) {
            for (int index_docs = adtypep->lo(); index_docs <= adtypep->hi(); ++index_docs) {
                const int index_code = index_docs - adtypep->lo();
                ToggleEnt newent{above.m_comment + std::string{"["} + cvtToStr(index_docs) + "]",
                                 new AstArraySel{varp->fileline(),
                                                 above.m_varRefp->cloneTree(true), index_code},
                                 new AstArraySel{varp->fileline(),
                                                 above.m_chgRefp->cloneTree(true), index_code}};
                toggleVarRecurse(adtypep->subDTypep()->skipRefp(), depth + 1, newent, varp,
                                 chgVarp);
                newent.cleanup();
            }
        } else if (const AstPackArrayDType* const adtypep = VN_CAST(dtypep, PackArrayDType)) {
            for (int index_docs = adtypep->lo(); index_docs <= adtypep->hi(); ++index_docs) {
                const AstNodeDType* const subtypep = adtypep->subDTypep()->skipRefp();
                const int index_code = index_docs - adtypep->lo();
                ToggleEnt newent{above.m_comment + std::string{"["} + cvtToStr(index_docs) + "]",
                                 new AstSel{varp->fileline(), above.m_varRefp->cloneTree(true),
                                            index_code * subtypep->width(), subtypep->width()},
                                 new AstSel{varp->fileline(), above.m_chgRefp->cloneTree(true),
                                            index_code * subtypep->width(), subtypep->width()}};
                toggleVarRecurse(adtypep->subDTypep()->skipRefp(), depth + 1, newent, varp,
                                 chgVarp);
                newent.cleanup();
            }
        } else if (const AstStructDType* const adtypep = VN_CAST(dtypep, StructDType)) {
            // For now it's packed, so similar to array
            for (AstMemberDType* itemp = adtypep->membersp(); itemp;
                 itemp = VN_AS(itemp->nextp(), MemberDType)) {
                AstNodeDType* const subtypep = itemp->subDTypep()->skipRefp();
                const int index_code = itemp->lsb();
                ToggleEnt newent{above.m_comment + std::string{"."} + itemp->name(),
                                 new AstSel{varp->fileline(), above.m_varRefp->cloneTree(true),
                                            index_code, subtypep->width()},
                                 new AstSel{varp->fileline(), above.m_chgRefp->cloneTree(true),
                                            index_code, subtypep->width()}};
                toggleVarRecurse(subtypep, depth + 1, newent, varp, chgVarp);
                newent.cleanup();
            }
        } else if (const AstUnionDType* const adtypep = VN_CAST(dtypep, UnionDType)) {
            // Arbitrarily handle only the first member of the union
            if (const AstMemberDType* const itemp = adtypep->membersp()) {
                AstNodeDType* const subtypep = itemp->subDTypep()->skipRefp();
                ToggleEnt newent{above.m_comment + std::string{"."} + itemp->name(),
                                 above.m_varRefp->cloneTree(true),
                                 above.m_chgRefp->cloneTree(true)};
                toggleVarRecurse(subtypep, depth + 1, newent, varp, chgVarp);
                newent.cleanup();
            }
        } else {
            dtypep->v3fatalSrc("Unexpected node data type in toggle coverage generation: "
                               << dtypep->prettyTypeName());
        }
    }

    // VISITORS - LINE COVERAGE
    // Note not AstNodeIf; other types don't get covered
    virtual void visit(AstIf* nodep) override {
        UINFO(4, " IF: " << nodep << endl);
        if (m_state.m_on) {
            // An else-if.  When we iterate the if, use "elsif" marking
            const bool elsif
                = nodep->ifsp() && VN_IS(nodep->elsesp(), If) && !nodep->elsesp()->nextp();
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
                createHandle(nodep);
                iterateAndNextNull(nodep->ifsp());
                lineTrack(nodep);
                ifState = m_state;
            }
            m_state = lastState;
            {
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
                UINFO(4, "   COVER-branch: " << nodep << endl);
                nodep->addIfsp(newCoverInc(nodep->fileline(), "", "v_branch", "if",
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
                UINFO(4, "   COVER-elsif: " << nodep << endl);
                if (ifState.lineCoverageOn(nodep)) {
                    nodep->addIfsp(newCoverInc(nodep->fileline(), "", "v_line", "elsif",
                                               linesCov(ifState, nodep), 0,
                                               traceNameForLine(nodep, "elsif")));
                }
                // and we don't insert the else as the child if-else will do so
            } else {
                // Cover as separate blocks (not a branch as is not two-legged)
                if (ifState.lineCoverageOn(nodep)) {
                    UINFO(4, "   COVER-half-if: " << nodep << endl);
                    nodep->addIfsp(newCoverInc(nodep->fileline(), "", "v_line", "if",
                                               linesCov(ifState, nodep), 0,
                                               traceNameForLine(nodep, "if")));
                }
                if (elseState.lineCoverageOn(nodep)) {
                    UINFO(4, "   COVER-half-el: " << nodep << endl);
                    nodep->addElsesp(newCoverInc(nodep->fileline(), "", "v_line", "else",
                                                 linesCov(elseState, nodep), 1,
                                                 traceNameForLine(nodep, "else")));
                }
            }
            m_state = lastState;
        }
        UINFO(9, " done HANDLE " << m_state.m_handle << " for " << nodep << endl);
    }
    virtual void visit(AstCaseItem* nodep) override {
        // We don't add an explicit "default" coverage if not provided,
        // as we already have a warning when there is no default.
        UINFO(4, " CASEI: " << nodep << endl);
        if (m_state.lineCoverageOn(nodep)) {
            VL_RESTORER(m_state);
            {
                createHandle(nodep);
                iterateAndNextNull(nodep->bodysp());
                if (m_state.lineCoverageOn(nodep)) {  // if the case body didn't disable it
                    lineTrack(nodep);
                    UINFO(4, "   COVER: " << nodep << endl);
                    nodep->addBodysp(newCoverInc(nodep->fileline(), "", "v_line", "case",
                                                 linesCov(m_state, nodep), 0,
                                                 traceNameForLine(nodep, "case")));
                }
            }
        }
    }
    virtual void visit(AstCover* nodep) override {
        UINFO(4, " COVER: " << nodep << endl);
        VL_RESTORER(m_state);
        {
            m_state.m_on = true;  // Always do cover blocks, even if there's a $stop
            createHandle(nodep);
            iterateChildren(nodep);
            if (!nodep->coverincp() && v3Global.opt.coverageUser()) {
                // Note the name may be overridden by V3Assert processing
                lineTrack(nodep);
                nodep->coverincp(newCoverInc(nodep->fileline(), m_beginHier, "v_user", "cover",
                                             linesCov(m_state, nodep), 0,
                                             m_beginHier + "_vlCoverageUserTrace"));
            }
        }
    }
    virtual void visit(AstStop* nodep) override {
        UINFO(4, "  STOP: " << nodep << endl);
        m_state.m_on = false;
    }
    virtual void visit(AstPragma* nodep) override {
        if (nodep->pragType() == VPragmaType::COVERAGE_BLOCK_OFF) {
            // Skip all NEXT nodes under this block, and skip this if/case branch
            UINFO(4, "  OFF: h" << m_state.m_handle << " " << nodep << endl);
            m_state.m_on = false;
            VL_DO_DANGLING(nodep->unlinkFrBack()->deleteTree(), nodep);
        } else {
            if (m_state.m_on) iterateChildren(nodep);
            lineTrack(nodep);
        }
    }
    virtual void visit(AstBegin* nodep) override {
        // Record the hierarchy of any named begins, so we can apply to user
        // coverage points.  This is because there may be cov points inside
        // generate blocks; each point should get separate consideration.
        // (Currently ignored for line coverage, since any generate iteration
        // covers the code in that line.)
        VL_RESTORER(m_beginHier);
        VL_RESTORER(m_inToggleOff);
        {
            m_inToggleOff = true;
            if (nodep->name() != "") {
                m_beginHier = m_beginHier + (m_beginHier != "" ? "." : "") + nodep->name();
            }
            iterateChildren(nodep);
            lineTrack(nodep);
        }
    }

    // VISITORS - BOTH
    virtual void visit(AstNode* nodep) override {
        iterateChildren(nodep);
        lineTrack(nodep);
    }

public:
    // CONSTRUCTORS
    explicit CoverageVisitor(AstNetlist* rootp) { iterateChildren(rootp); }
    virtual ~CoverageVisitor() override = default;
};

//######################################################################
// Coverage class functions

void V3Coverage::coverage(AstNetlist* rootp) {
    UINFO(2, __FUNCTION__ << ": " << endl);
    { CoverageVisitor{rootp}; }  // Destruct before checking
    V3Global::dumpCheckGlobalTree("coverage", 0, v3Global.opt.dumpTreeLevel(__FILE__) >= 3);
}
