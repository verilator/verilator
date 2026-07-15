// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Netlist (top level) functions
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2003-2026 Wilson Snyder
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
#include "V3Finish.h"
#include "V3UniqueNames.h"

#include <list>
#include <unordered_map>

VL_DEFINE_DEBUG_FUNCTIONS;

class CoverageFinishBoundaryVisitor final : public VNVisitorConst {
    const V3FinishEffects& m_effects;
    std::unordered_set<const AstNode*> m_boundaries;
    bool m_containsBoundary = false;
    bool m_timingBoundaries = false;

    void analyze(AstNode* nodep, bool selfBoundary) {
        bool containsBoundary = selfBoundary;
        {
            VL_RESTORER(m_containsBoundary);
            m_containsBoundary = false;
            iterateChildrenConst(nodep);
            containsBoundary |= m_containsBoundary;
        }
        if (containsBoundary) m_boundaries.emplace(nodep);
        m_containsBoundary |= containsBoundary;
    }

    void analyzeSourceUnit(AstNode* nodep) {
        VL_RESTORER(m_timingBoundaries);
        m_timingBoundaries = m_effects.mayFinish(nodep);
        analyze(nodep, false);
    }

    void visit(AstNodeFTask* nodep) override { analyzeSourceUnit(nodep); }
    void visit(AstNodeProcedure* nodep) override { analyzeSourceUnit(nodep); }
    void visit(AstInitialAutomatic* nodep) override { analyzeSourceUnit(nodep); }
    void visit(AstBegin* nodep) override {
        if (m_effects.isSourceUnit(nodep)) {
            analyzeSourceUnit(nodep);
        } else {
            analyze(nodep, false);
        }
    }
    void visit(AstNodeFTaskRef* nodep) override { analyze(nodep, m_effects.mayFinish(nodep)); }
    void visit(AstFinish* nodep) override { analyze(nodep, true); }
    void visit(AstFinishFork* nodep) override { analyze(nodep, true); }
    void visit(AstNode* nodep) override {
        analyze(nodep, m_timingBoundaries && nodep->isTimingControl());
    }

public:
    CoverageFinishBoundaryVisitor(AstNetlist* rootp, const V3FinishEffects& effects)
        : m_effects{effects} {
        iterateChildrenConst(rootp);
    }
    ~CoverageFinishBoundaryVisitor() override = default;

    bool contains(const AstNode* nodep) const { return m_boundaries.count(nodep); }
};

class ExprCoverageEligibleVisitor final : public VNVisitorConst {
    // STATE
    const V3FinishEffects& m_finishEffects;
    bool m_eligible = true;

    static bool elemDTypeEligible(const AstNodeDType* dtypep) {
        dtypep = dtypep->skipRefp();
        if (const AstNodeDType* const dtp = dtypep->virtRefDTypep()) {
            if (!elemDTypeEligible(dtp)) return false;
        }
        if (const AstNodeDType* const dtp = dtypep->virtRefDType2p()) {
            if (!elemDTypeEligible(dtp)) return false;
        }
        return !VN_IS(dtypep, ClassRefDType);
    }

    void visit(AstNodeVarRef* nodep) override {
        const AstNodeDType* const dtypep = nodep->varp()->dtypep();
        // Class objects and references not supported for expression coverage
        // because the object may not persist until the point at which
        // coverage data is gathered
        // This could be resolved in the future by protecting against dereferrencing
        // null pointers when cloning the expression for expression coverage
        if (dtypep && elemDTypeEligible(dtypep)) {
            iterateChildrenConst(nodep);
        } else {
            m_eligible = false;
        }
    }

    void visit(AstNodeFTaskRef* nodep) override {
        if (m_finishEffects.mayFinish(nodep)) {
            m_eligible = false;
        } else {
            iterateChildrenConst(nodep);
        }
    }

    void visit(AstNode* nodep) override {
        if (!nodep->isExprCoverageEligible()) {
            m_eligible = false;
        } else {
            iterateChildrenConst(nodep);
        }
    }

public:
    // CONSTRUCTORS
    ExprCoverageEligibleVisitor(AstNode* nodep, const V3FinishEffects& finishEffects)
        : m_finishEffects{finishEffects} {
        iterateConst(nodep);
    }
    ~ExprCoverageEligibleVisitor() override = default;

    bool eligible() const { return m_eligible; }
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
            , m_emitV{emitV} {}
    };
    using CoverExpr = std::deque<CoverTerm>;
    using CoverExprs = std::list<CoverExpr>;

    struct ToggleEnt final {
        const string m_comment;  // Comment for coverage dump
        AstNodeExpr* m_varRefp;  // How to get to this element
        AstNodeExpr* m_chgRefp;  // How to get to this element
        ToggleEnt(const string& comment, AstNodeExpr* vp, AstNodeExpr* cp)
            : m_comment{comment}
            , m_varRefp{vp}
            , m_chgRefp{cp} {}
        ~ToggleEnt() = default;
        void cleanup() {
            VL_DO_CLEAR(m_varRefp->deleteTree(), m_varRefp = nullptr);
            VL_DO_CLEAR(m_chgRefp->deleteTree(), m_chgRefp = nullptr);
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

    struct LineSegment final {
        const CheckState m_state;
        AstNode* const m_beforep;  // Insert before this boundary, or append if nullptr
        const AstNode* const m_anchorp;  // Source location for non-primary segments
        LineSegment(const CheckState& state, AstNode* beforep, const AstNode* anchorp)
            : m_state{state}
            , m_beforep{beforep}
            , m_anchorp{anchorp} {}
    };
    using LineSegments = std::vector<LineSegment>;

    struct ExprCoveragePlacement final {
        AstNode* m_beforep = nullptr;  // Insert before a later finish boundary
        bool m_transactional = false;  // Cover at the original expression evaluation
    };

    enum Objective : uint8_t { NONE, SEEKING, ABORTED };

    // NODE STATE
    // Entire netlist:
    //  AstIf::user1()                  -> bool.  True indicates ifelse processed
    //  AstIf/AstLoopTest::user2()      -> bool.  True indicates coverage-generated
    const VNUser1InUse m_inuser1;
    const VNUser2InUse m_inuser2;
    const V3FinishEffects& m_finishEffects;
    CoverageFinishBoundaryVisitor m_finishBoundaries;
    V3UniqueNames m_exprTempNames;  // For generating unique temporary variable names used by
                                    // expression coverage
    std::unordered_map<AstNodeExpr*, AstVar*> m_funcTemps;
    std::unordered_set<AstNodeExpr*> m_transactionCoveredExprs;
    std::vector<AstStmtPragma*> m_deferredDeletePragmas;

    // STATE - across all visitors
    int m_nextHandle = 0;

    // STATE - for current visit position (use VL_RESTORER)
    CheckState m_state;  // State save-restored on each new coverage scope/block
    AstNodeModule* m_modp = nullptr;  // Current module to add statement to
    AstNodeFTask* m_ftaskp = nullptr;  // Current function/task
    AstNode* m_exprStmtsp = nullptr;  // Node to add expr coverage to
    bool m_then = false;  // Whether we're iterating the then or else branch
                          // when m_exprStmtps is an AstIf
    CoverExprs m_exprs;  // List of expressions that can reach objective
    Objective m_seeking = NONE;  // Seeking objective for expression coverage
    bool m_objective = false;  // Expression objective
    bool m_ifCond = false;  // Visiting if condition
    bool m_inToggleOff = false;  // In function/task etc
    string m_beginHier;  // AstBegin hier name for user coverage points
    LineSegments* m_lineSegmentsp = nullptr;  // Segments in the current coverage region
    AstNode* m_lineOwnerp = nullptr;  // Procedure/branch/loop/case owning current segments
    const AstNode* m_lineSegmentStartp = nullptr;  // First source node in current segment
    bool m_lineTrackOwner = false;  // Attribute the owner line to the first segment

    // STATE - cleared each module
    std::unordered_map<std::string, uint32_t> m_varnames;  // Uniquify inserted variable names
    std::unordered_map<int, LinenoSet> m_handleLines;  // Line numbers for given m_stateHandle

    // METHODS

    // Return non-nullptr reason if this variable shouldn't have toggle coverage
    const char* varIgnoreToggle(const AstVar* nodep) {
        const bool cover = nodep->isIO() || (nodep->isSignal() && nodep->isBitLogic());
        if (!cover) return "Not relevant signal";
        if (nodep->isConst()) return "Signal is constant";
        if (nodep->isDouble()) return "Signal is double";
        if (nodep->isString()) return "Signal is string";
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

    AstCoverInc* newCoverInc(FileLine* fl, AstNodeCoverDecl* const declp,
                             const string& trace_var_name) {
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
    string traceNameForLine(const AstNode* nodep, const string& type) {
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
    void createContinuationHandle(const AstNode* nodep) {
        const bool on = m_state.m_on;
        const bool inModOff = m_state.m_inModOff;
        createHandle(nodep);
        m_state.m_on = on;
        m_state.m_inModOff = inModOff;
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
    bool lineTracked(const CheckState& state) const {
        const auto it = m_handleLines.find(state.m_handle);
        return it != m_handleLines.end() && !it->second.empty();
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
        for (const int linen : lines) {
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
    void recordLineBoundary(AstNode* beforep, AstNode* nextp, const AstNode* contextp) {
        UASSERT_OBJ(m_lineSegmentsp && m_lineOwnerp, contextp,
                    "Coverage boundary is outside a line region");
        if (m_lineSegmentsp->empty() && m_lineTrackOwner) lineTrack(m_lineOwnerp);
        m_lineSegmentsp->emplace_back(m_state, beforep, m_lineSegmentStartp);
        const AstNode* const startp = nextp ? nextp : m_lineOwnerp;
        createContinuationHandle(startp);
        m_lineSegmentStartp = startp;
    }
    void recordLineBoundary(AstNode* boundaryp, AstNode* nextp) {
        recordLineBoundary(boundaryp, nextp, boundaryp);
    }
    bool lineRegionIsFinishSegmented() const {
        return m_lineSegmentsp && m_finishBoundaries.contains(m_lineOwnerp);
    }
    void iterateStatementList(AstNode* stmtsp) {
        for (AstNode *stmtp = stmtsp, *nextp; stmtp; stmtp = nextp) {
            nextp = stmtp->nextp();
            if (m_lineSegmentsp && !m_lineSegmentsp->empty()
                && m_lineSegmentStartp == m_lineOwnerp) {
                m_lineSegmentStartp = stmtp;
            }
            const size_t priorSegments = m_lineSegmentsp ? m_lineSegmentsp->size() : 0;
            iterate(stmtp);
            if (m_lineSegmentsp && m_finishBoundaries.contains(stmtp)
                && priorSegments == m_lineSegmentsp->size()) {
                recordLineBoundary(stmtp, nextp);
            }
        }
    }
    void iterateLineRegion(AstNode* ownerp, AstNode* stmtsp, bool trackOwner,
                           LineSegments& segments) {
        VL_RESTORER(m_lineSegmentsp);
        VL_RESTORER(m_lineOwnerp);
        VL_RESTORER(m_lineSegmentStartp);
        VL_RESTORER(m_lineTrackOwner);
        m_lineSegmentsp = &segments;
        m_lineOwnerp = ownerp;
        m_lineSegmentStartp = ownerp;
        m_lineTrackOwner = trackOwner;
        iterateStatementList(stmtsp);
        if (segments.empty() && trackOwner) lineTrack(ownerp);
        segments.emplace_back(m_state, nullptr, m_lineSegmentStartp);
    }
    void iterateChildrenWithoutList(AstNode* ownerp, AstNode* stmtsp) {
        if (!stmtsp) {
            iterateChildren(ownerp);
            return;
        }
        VNRelinker relinker;
        stmtsp->unlinkFrBackWithNext(&relinker);
        iterateChildren(ownerp);
        relinker.relink(stmtsp);
    }
    template <typename T_Node>
    void iterateTimingControl(T_Node* nodep) {
        AstNode* const stmtsp = nodep->stmtsp();
        if (!stmtsp || !lineRegionIsFinishSegmented() || !m_finishBoundaries.contains(nodep)) {
            iterateChildren(nodep);
            lineTrack(nodep);
            return;
        }
        iterateChildrenWithoutList(nodep, stmtsp);
        lineTrack(nodep);
        recordLineBoundary(nodep, stmtsp);
        iterateStatementList(stmtsp);
    }
    void emitLineSegments(AstNode* ownerp, const LineSegments& segments, const string& page,
                          const string& comment, int offset, bool allowEmptyPrimary) {
        bool primary = true;
        int point = 0;
        for (const LineSegment& segment : segments) {
            if (!segment.m_state.lineCoverageOn(ownerp)) continue;
            if (!lineTracked(segment.m_state) && !(primary && allowEmptyPrimary)) continue;
            const AstNode* const anchorp = primary ? ownerp : segment.m_anchorp;
            const string segmentPage = primary ? page : "v_line/" + m_modp->prettyName();
            const string segmentComment = primary ? comment : "block";
            AstCoverOtherDecl* const declp
                = new AstCoverOtherDecl{anchorp->fileline(), segmentPage, segmentComment,
                                        linesCov(segment.m_state, ownerp), offset + point};
            m_modp->addStmtsp(declp);
            AstNode* const newp = newCoverInc(anchorp->fileline(), declp,
                                              traceNameForLine(anchorp, segmentComment));
            if (segment.m_beforep) {
                segment.m_beforep->addHereThisAsNext(newp);
            } else {
                insertProcStatement(ownerp, newp);
            }
            primary = false;
            ++point;
        }
    }
    static bool lineCoverageOn(const AstNode* ownerp, const LineSegments& segments) {
        return std::any_of(segments.begin(), segments.end(), [ownerp](const LineSegment& segment) {
            return segment.m_state.lineCoverageOn(ownerp);
        });
    }

    // VISITORS - BOTH
    void visit(AstNodeModule* nodep) override {
        const AstNodeModule* const origModp = m_modp;
        VL_RESTORER(m_modp);
        VL_RESTORER(m_state);
        VL_RESTORER_COPY(m_exprTempNames);
        VL_RESTORER_COPY(m_funcTemps);
        createHandle(nodep);
        m_modp = nodep;
        m_state.m_inModOff = false;  // Haven't made top shell, so tops are real tops
        if (!origModp) {
            // No blocks cross (non-nested) modules, so save some memory
            m_varnames.clear();
            m_handleLines.clear();
        }
        iterateChildren(nodep);
    }
    void visit(AstClass* nodep) override {
        VL_RESTORER(m_modp);
        VL_RESTORER(m_state);
        VL_RESTORER_COPY(m_exprTempNames);
        VL_RESTORER_COPY(m_funcTemps);
        createHandle(nodep);
        m_modp = nodep;
        // Covergroup declarations are not executable statements; suppress line/expr/toggle
        // coverage so declarative elements (covergroup, coverpoint, cross) are not annotated
        m_state.m_inModOff = nodep->isCovergroup();
        iterateChildren(nodep);
    }
    void visit(AstAlways* nodep) override {
        if (nodep->keyword() == VAlwaysKwd::CONT_ASSIGN) {
            // Handle continuous assigns for expression coverage (but not line coverage)
            VL_RESTORER(m_state);
            VL_RESTORER(m_exprStmtsp);
            VL_RESTORER(m_inToggleOff);
            m_exprStmtsp = nodep;
            m_inToggleOff = true;
            createHandle(nodep);
            iterateChildren(nodep);
            // Note: No line coverage for continuous assigns
            return;
        }
        iterateProcedure(nodep);
    }
    void visit(AstNodeProcedure* nodep) override { iterateProcedure(nodep); }
    void visit(AstLoop* nodep) override {
        UASSERT_OBJ(!nodep->contsp(), nodep, "'contsp' only used before LinkJump");
        VL_RESTORER(m_state);
        VL_RESTORER(m_exprStmtsp);
        VL_RESTORER(m_inToggleOff);
        m_exprStmtsp = nodep;
        m_inToggleOff = true;
        createHandle(nodep);
        LineSegments segments;
        iterateLineRegion(nodep, nodep->stmtsp(), false, segments);
        if (lineCoverageOn(nodep, segments)) {
            emitLineSegments(nodep, segments, "v_line/" + m_modp->prettyName(), "block", 0, false);
        }
    }
    void visit(AstLoopTest* nodep) override {
        if (nodep->user2SetOnce()) return;
        lineTrack(nodep);
        if (m_state.lineCoverageOn(nodep) && nodep->backp()->nextp() == nodep) {
            AstCoverOtherDecl* const declp
                = new AstCoverOtherDecl{nodep->fileline(), "v_line/" + m_modp->prettyName(),
                                        "block", linesCov(m_state, nodep), 0};
            m_modp->addStmtsp(declp);
            AstNode* const newp
                = newCoverInc(nodep->fileline(), declp, traceNameForLine(nodep, "block"));
            nodep->addHereThisAsNext(newp);
            createHandle(nodep);
        }
        iterateChildren(nodep);
    }

    void visit(AstNodeFTask* nodep) override {
        VL_RESTORER(m_ftaskp);
        VL_RESTORER_COPY(m_exprTempNames);
        VL_RESTORER_COPY(m_funcTemps);
        m_ftaskp = nodep;
        if (!nodep->dpiImport()) iterateProcedure(nodep);
    }

    void insertProcStatement(AstNode* nodep, AstNode* stmtp) {
        if (AstNodeProcedure* const itemp = VN_CAST(nodep, NodeProcedure)) {
            itemp->addStmtsp(stmtp);
        } else if (AstNodeFTask* const itemp = VN_CAST(nodep, NodeFTask)) {
            itemp->addStmtsp(stmtp);
        } else if (AstLoop* const itemp = VN_CAST(nodep, Loop)) {
            itemp->addStmtsp(stmtp);
        } else if (AstIf* const itemp = VN_CAST(nodep, If)) {
            if (m_then) {
                itemp->addThensp(stmtp);
            } else {
                itemp->addElsesp(stmtp);
            }
        } else if (AstBegin* const itemp = VN_CAST(nodep, Begin)) {
            itemp->addStmtsp(stmtp);
        } else if (AstCaseItem* const itemp = VN_CAST(nodep, CaseItem)) {
            itemp->addStmtsp(stmtp);
        } else {
            nodep->v3fatalSrc("Bad node type");
        }
    }
    AstNode* procStatementsp(AstNode* nodep) const {
        if (AstNodeProcedure* const itemp = VN_CAST(nodep, NodeProcedure)) {
            return itemp->stmtsp();
        } else if (AstNodeFTask* const itemp = VN_CAST(nodep, NodeFTask)) {
            return itemp->stmtsp();
        } else if (AstLoop* const itemp = VN_CAST(nodep, Loop)) {
            return itemp->stmtsp();
        } else if (AstIf* const itemp = VN_CAST(nodep, If)) {
            return m_then ? itemp->thensp() : itemp->elsesp();
        } else if (AstBegin* const itemp = VN_CAST(nodep, Begin)) {
            return itemp->stmtsp();
        } else if (AstCaseItem* const itemp = VN_CAST(nodep, CaseItem)) {
            return itemp->stmtsp();
        }
        return nullptr;
    }
    ExprCoveragePlacement exprCoveragePlacement(AstNodeExpr* nodep) const {
        if (m_finishBoundaries.contains(nodep)) return {nullptr, true};
        if (!m_exprStmtsp || !m_finishBoundaries.contains(m_exprStmtsp)) return {};

        AstNode* const stmtsp = procStatementsp(m_exprStmtsp);
        AstNode* containingp = nullptr;
        for (AstNode* ancestorp = nodep; ancestorp && ancestorp != m_exprStmtsp;
             ancestorp = ancestorp->backp()) {
            for (AstNode* stmtp = stmtsp; stmtp; stmtp = stmtp->nextp()) {
                if (ancestorp == stmtp) {
                    containingp = stmtp;
                    break;
                }
            }
            if (containingp) break;
        }

        bool afterExpression = !containingp;
        for (AstNode* stmtp = stmtsp; stmtp; stmtp = stmtp->nextp()) {
            if (stmtp == containingp) {
                if (m_finishBoundaries.contains(stmtp)) return {nullptr, true};
                afterExpression = true;
            } else if (afterExpression && m_finishBoundaries.contains(stmtp)) {
                return {stmtp, false};
            }
        }
        return {};
    }
    void iterateProcedure(AstNode* nodep) {
        VL_RESTORER(m_state);
        VL_RESTORER(m_exprStmtsp);
        VL_RESTORER(m_inToggleOff);
        m_exprStmtsp = nodep;
        m_inToggleOff = true;
        createHandle(nodep);
        AstNode* const stmtsp = VN_IS(nodep, NodeProcedure) ? VN_AS(nodep, NodeProcedure)->stmtsp()
                                                            : VN_AS(nodep, NodeFTask)->stmtsp();
        iterateChildrenWithoutList(nodep, stmtsp);
        LineSegments segments;
        iterateLineRegion(nodep, stmtsp, true, segments);
        if (lineCoverageOn(nodep, segments)) {
            emitLineSegments(nodep, segments, "v_line/" + m_modp->prettyName(), "block", 0, false);
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

                // Create bucket for each dimension * bit.
                // This is necessarily an O(n^2) expansion, which is why
                // we limit coverage to signals with < 256 bits.

                ToggleEnt newvec{""s, new AstVarRef{fl_nowarn, nodep, VAccess::READ},
                                 new AstVarRef{fl_nowarn, chgVarp, VAccess::WRITE}};
                toggleVarRecurse(nodep->dtypeSkipRefp(), 0, newvec, nodep);
                newvec.cleanup();
            }
        }
    }

    void toggleVarBottom(const ToggleEnt& above, const AstVar* varp, const VNumRange& range) {
        const std::string hierPrefix
            = (m_beginHier != "") ? AstNode::prettyName(m_beginHier) + "." : "";
        AstCoverToggleDecl* const declp
            = new AstCoverToggleDecl{varp->fileline(), "v_toggle/" + m_modp->prettyName(),
                                     hierPrefix + varp->name() + above.m_comment, range};
        m_modp->addStmtsp(declp);
        AstCoverToggle* const newp = new AstCoverToggle{
            varp->fileline(), newCoverInc(varp->fileline(), declp, ""),
            above.m_varRefp->cloneTree(false), above.m_chgRefp->cloneTree(false)};
        m_modp->addStmtsp(newp);
    }

    void toggleVarRecurse(const AstNodeDType* const dtypep, const int depth,  // per-iteration
                          const ToggleEnt& above, const AstVar* const varp) {  // Constant
        if (const AstBasicDType* const basicp = VN_CAST(dtypep, BasicDType)) {
            toggleVarBottom(above, varp, basicp->nrange());
        } else if (const AstUnpackArrayDType* const adtypep = VN_CAST(dtypep, UnpackArrayDType)) {
            for (int index_docs = adtypep->lo(); index_docs <= adtypep->hi(); ++index_docs) {
                const int index_code = index_docs - adtypep->lo();
                ToggleEnt newent{above.m_comment + "["s + cvtToStr(index_docs) + "]",
                                 new AstArraySel{varp->fileline(),
                                                 above.m_varRefp->cloneTree(false), index_code},
                                 new AstArraySel{varp->fileline(),
                                                 above.m_chgRefp->cloneTree(false), index_code}};
                toggleVarRecurse(adtypep->subDTypep()->skipRefp(), depth + 1, newent, varp);
                newent.cleanup();
            }
        } else if (const AstPackArrayDType* const adtypep = VN_CAST(dtypep, PackArrayDType)) {
            for (int index_docs = adtypep->lo(); index_docs <= adtypep->hi(); ++index_docs) {
                const AstNodeDType* const subtypep = adtypep->subDTypep()->skipRefp();
                const int index_code = index_docs - adtypep->lo();
                ToggleEnt newent{above.m_comment + "["s + cvtToStr(index_docs) + "]",
                                 new AstSel{varp->fileline(), above.m_varRefp->cloneTree(false),
                                            index_code * subtypep->width(), subtypep->width()},
                                 new AstSel{varp->fileline(), above.m_chgRefp->cloneTree(false),
                                            index_code * subtypep->width(), subtypep->width()}};
                toggleVarRecurse(adtypep->subDTypep()->skipRefp(), depth + 1, newent, varp);
                newent.cleanup();
            }
        } else if (const AstStructDType* const adtypep = VN_CAST(dtypep, StructDType)) {
            if (adtypep->packed()) {
                for (AstMemberDType* itemp = adtypep->membersp(); itemp;
                     itemp = VN_AS(itemp->nextp(), MemberDType)) {
                    const AstNodeDType* const subtypep = itemp->subDTypep()->skipRefp();
                    const int index_code = itemp->lsb();
                    ToggleEnt newent{
                        above.m_comment + "."s + itemp->name(),
                        new AstSel{varp->fileline(), above.m_varRefp->cloneTree(false), index_code,
                                   subtypep->width()},
                        new AstSel{varp->fileline(), above.m_chgRefp->cloneTree(false), index_code,
                                   subtypep->width()}};
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
                    varRefp->dtypep(subtypep);
                    chgRefp->dtypep(subtypep);
                    ToggleEnt newent{above.m_comment + "."s + itemp->name(), varRefp, chgRefp};
                    toggleVarRecurse(subtypep, depth + 1, newent, varp);
                    newent.cleanup();
                }
            }
        } else if (const AstUnionDType* const adtypep = VN_CAST(dtypep, UnionDType)) {
            // Arbitrarily handle only the first member of the union
            if (const AstMemberDType* const itemp = adtypep->membersp()) {
                AstNodeDType* const subtypep = itemp->subDTypep()->skipRefp();
                if (adtypep->packed()) {
                    ToggleEnt newent{above.m_comment + "."s + itemp->name(),
                                     above.m_varRefp->cloneTree(false),
                                     above.m_chgRefp->cloneTree(false)};
                    toggleVarRecurse(subtypep, depth + 1, newent, varp);
                    newent.cleanup();
                } else {
                    AstNodeExpr* const varRefp = new AstStructSel{
                        varp->fileline(), above.m_varRefp->cloneTree(false), itemp->name()};
                    AstNodeExpr* const chgRefp = new AstStructSel{
                        varp->fileline(), above.m_chgRefp->cloneTree(false), itemp->name()};
                    varRefp->dtypep(subtypep);
                    chgRefp->dtypep(subtypep);
                    ToggleEnt newent{above.m_comment + "."s + itemp->name(), varRefp, chgRefp};
                    toggleVarRecurse(subtypep, depth + 1, newent, varp);
                    newent.cleanup();
                }
            }
        } else if (VN_IS(dtypep, QueueDType) || VN_IS(dtypep, AssocArrayDType)
                   || VN_IS(dtypep, WildcardArrayDType)) {
            // Not covered
            varp->v3warn(COVERIGN, "Coverage ignored for type " << dtypep->prettyTypeName());
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
        } else if (VN_IS(backp, NodeAssign) && VN_AS(backp, NodeAssign)->rhsp() == nodep) {
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
            AstCoverOtherDecl* const thenDeclp
                = new AstCoverOtherDecl{thenp->fileline(), "v_branch/" + m_modp->prettyName(),
                                        "cond_then", linesCov(m_state, nodep), 0};
            m_modp->addStmtsp(thenDeclp);
            nodep->thenp(new AstExprStmt{
                thenp->fileline(),
                newCoverInc(nodep->fileline(), thenDeclp, traceNameForLine(nodep, "cond_then")),
                thenp});
            m_state = lastState;
            createHandle(nodep);
            iterate(nodep->elsep());
            AstNodeExpr* const elsep = nodep->elsep()->unlinkFrBack();
            AstCoverOtherDecl* const elseDeclp
                = new AstCoverOtherDecl{thenp->fileline(), "v_branch/" + m_modp->prettyName(),
                                        "cond_else", linesCov(m_state, nodep), 1};
            m_modp->addStmtsp(elseDeclp);
            nodep->elsep(new AstExprStmt{
                elsep->fileline(),
                newCoverInc(nodep->fileline(), elseDeclp, traceNameForLine(nodep, "cond_else")),
                elsep});

            m_state = lastState;
        } else {
            lineTrack(nodep);
        }
    }
    // Note not AstNodeIf; other types don't get covered
    void visit(AstIf* nodep) override {
        if (nodep->user2()) return;
        VL_RESTORER(m_then);

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
            LineSegments ifSegments;
            LineSegments elseSegments;
            {
                VL_RESTORER(m_exprStmtsp);
                VL_RESTORER(m_then);
                m_exprStmtsp = nodep;
                m_then = true;
                createHandle(nodep);
                iterateLineRegion(nodep, nodep->thensp(), true, ifSegments);
            }
            m_state = lastState;
            {
                VL_RESTORER(m_exprStmtsp);
                VL_RESTORER(m_then);
                m_exprStmtsp = nodep;
                m_then = false;
                createHandle(nodep);
                iterateLineRegion(nodep, nodep->elsesp(), false, elseSegments);
            }
            m_state = lastState;
            //
            // If both if and else are "on", and we're not in an if/else, then
            // we do branch coverage
            if (!(first_elsif || cont_elsif || final_elsif) && lineCoverageOn(nodep, ifSegments)
                && lineCoverageOn(nodep, elseSegments)) {
                // Normal if. Linecov shows what's inside the if (not condition that is
                // always executed)
                UINFO(4, "   COVER-branch: " << nodep);
                m_then = true;
                emitLineSegments(nodep, ifSegments, "v_branch/" + m_modp->prettyName(), "if", 0,
                                 true);
                // The else has a column offset of 1 to uniquify it relative to the if
                // As "if" and "else" are more than one character wide, this won't overlap
                // another token
                m_then = false;
                emitLineSegments(nodep, elseSegments, "v_branch/" + m_modp->prettyName(), "else",
                                 1, true);
            }
            // If/else attributes to each block as non-branch coverage
            else if (first_elsif || cont_elsif) {
                UINFO(4, "   COVER-elsif: " << nodep);
                if (lineCoverageOn(nodep, ifSegments)) {
                    m_then = true;
                    emitLineSegments(nodep, ifSegments, "v_line/" + m_modp->prettyName(), "elsif",
                                     0, true);
                }
                // and we don't insert the else as the child if-else will do so
            } else {
                // Cover as separate blocks (not a branch as is not two-legged)
                if (lineCoverageOn(nodep, ifSegments)) {
                    UINFO(4, "   COVER-half-if: " << nodep);
                    m_then = true;
                    emitLineSegments(nodep, ifSegments, "v_line/" + m_modp->prettyName(), "if", 0,
                                     true);
                }
                if (lineCoverageOn(nodep, elseSegments)) {
                    UINFO(4, "   COVER-half-el: " << nodep);
                    m_then = false;
                    emitLineSegments(nodep, elseSegments, "v_line/" + m_modp->prettyName(), "else",
                                     1, true);
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
            LineSegments segments;
            iterateLineRegion(nodep, nodep->stmtsp(), true, segments);
            if (lineCoverageOn(nodep, segments)) {
                UINFO(4, "   COVER: " << nodep);
                emitLineSegments(nodep, segments, "v_line/" + m_modp->prettyName(), "case", 0,
                                 false);
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
            AstCoverOtherDecl* const declp
                = new AstCoverOtherDecl{nodep->fileline(), "v_user/" + m_modp->prettyName(),
                                        "cover", linesCov(m_state, nodep), 0};
            declp->hier(m_beginHier);
            m_modp->addStmtsp(declp);
            nodep->addCoverincsp(
                newCoverInc(nodep->fileline(), declp, m_beginHier + "_vlCoverageUserTrace"));
        }
    }
    void visit(AstPropSpec* nodep) override {
        VL_RESTORER(m_exprStmtsp);
        m_exprStmtsp = nullptr;
        iterateChildren(nodep);
    }
    void visit(AstStop* nodep) override {
        UINFO(4, "  STOP: " << nodep);
        if (lineRegionIsFinishSegmented()) recordLineBoundary(nodep, nodep->nextp());
        m_state.m_on = false;
    }
    void visit(AstStmtPragma* nodep) override {
        if (nodep->pragp()->pragType() == VPragmaType::COVERAGE_BLOCK_OFF) {
            // Skip all NEXT nodes under this block, and skip this if/case branch
            UINFO(4, "  OFF: h" << m_state.m_handle << " " << nodep);
            if (lineRegionIsFinishSegmented()) {
                recordLineBoundary(nodep, nodep->nextp());
                m_deferredDeletePragmas.push_back(nodep);
            } else {
                VL_DO_DANGLING(nodep->unlinkFrBack()->deleteTree(), nodep);
            }
            m_state.m_on = false;
        } else {
            if (m_state.m_on) iterateChildren(nodep);
            lineTrack(nodep);
        }
    }
    void visit(AstGenBlock* nodep) override {
        // Similar to AstBegin
        VL_RESTORER_COPY(m_beginHier);
        if (nodep->name() != "") {
            m_beginHier = m_beginHier + (m_beginHier != "" ? "__DOT__" : "") + nodep->name();
        }
        iterateChildren(nodep);
        lineTrack(nodep);
    }

    void visit(AstDelay* nodep) override { iterateTimingControl(nodep); }
    void visit(AstEventControl* nodep) override { iterateTimingControl(nodep); }
    void visit(AstWait* nodep) override { iterateTimingControl(nodep); }

    void visit(AstBegin* nodep) override {
        // Record the hierarchy of any named begins, so we can apply to user
        // coverage points.  This is because there may be cov points inside
        // generate blocks; each point should get separate consideration.
        // (Currently ignored for line coverage, since any generate iteration
        // covers the code in that line.)
        VL_RESTORER_COPY(m_beginHier);
        VL_RESTORER(m_inToggleOff);
        VL_RESTORER(m_exprStmtsp);
        m_exprStmtsp = nodep;
        m_inToggleOff = true;
        if (nodep->name() != "") {
            m_beginHier = m_beginHier + (m_beginHier != "" ? "__DOT__" : "") + nodep->name();
        }
        AstNode* const stmtsp = nodep->stmtsp();
        iterateChildrenWithoutList(nodep, stmtsp);
        const bool segmented = m_lineSegmentsp && m_finishBoundaries.contains(nodep);
        if (segmented) lineTrack(nodep);
        iterateStatementList(stmtsp);
        if (!segmented) lineTrack(nodep);
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

    AstVar* newExprResultTemp(AstNodeExpr* nodep) {
        AstVar* const varp = new AstVar{nodep->fileline(), VVarType::MODULETEMP,
                                        m_exprTempNames.get(nodep), nodep->dtypep()->skipRefp()};
        varp->isInternal(true);
        varp->noReset(true);
        varp->lifetime(m_ftaskp || !VN_IS(m_modp, Class) ? VLifetime::AUTOMATIC_EXPLICIT
                                                         : VLifetime::STATIC_EXPLICIT);
        if (m_ftaskp) {
            varp->funcLocal(true);
            if (m_ftaskp->stmtsp()) {
                m_ftaskp->stmtsp()->addHereThisAsNext(varp);
            } else {
                m_ftaskp->addStmtsp(varp);
            }
        } else if (m_modp->stmtsp()) {
            m_modp->stmtsp()->addHereThisAsNext(varp);
        } else {
            m_modp->addStmtsp(varp);
        }
        return varp;
    }
    void wrapExprCoverage(AstNodeExpr* nodep, AstNode* coverageStmtsp) {
        FileLine* const flp = nodep->fileline();
        AstVar* const resultVarp = newExprResultTemp(nodep);
        VNRelinker relinker;
        nodep->unlinkFrBack(&relinker);
        AstAssign* const assignp
            = new AstAssign{flp, new AstVarRef{flp, resultVarp, VAccess::WRITE}, nodep};
        AstNode::addNext<AstNode, AstNode>(assignp, coverageStmtsp);
        relinker.relink(
            new AstExprStmt{flp, assignp, new AstVarRef{flp, resultVarp, VAccess::READ}});
    }
    void addExprCoverInc(AstNodeExpr* nodep, AstNode*& transactionStmtsp,
                         const ExprCoveragePlacement& placement, int start = 0) {
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
                AstNodeExpr* covExprp = nullptr;
                if (VN_IS(term.m_exprp, FuncRef) || term.m_exprp->isSystemFunc()) {
                    AstNodeExpr* const frefp = term.m_exprp;
                    AstNodeDType* const dtypep = frefp->dtypep();
                    const auto pair = m_funcTemps.emplace(frefp, nullptr);
                    AstVar* varp = pair.first->second;
                    if (pair.second) {
                        varp = new AstVar{fl, VVarType::MODULETEMP, m_exprTempNames.get(frefp),
                                          dtypep};
                        varp->lifetime(VLifetime::AUTOMATIC_EXPLICIT);
                        pair.first->second = varp;
                        if (m_ftaskp) {
                            varp->funcLocal(true);
                            m_ftaskp->stmtsp()->addHereThisAsNext(varp);
                        } else {
                            m_modp->stmtsp()->addHereThisAsNext(varp);
                        }
                        VNRelinker relinkHandle;
                        frefp->unlinkFrBack(&relinkHandle);
                        relinkHandle.relink(new AstExprStmt{
                            fl, new AstAssign{fl, new AstVarRef{fl, varp, VAccess::WRITE}, frefp},
                            new AstVarRef{fl, varp, VAccess::READ}});
                    }
                    covExprp = new AstVarRef{fl, varp, VAccess::READ};
                } else {
                    covExprp = term.m_exprp->cloneTree(false);
                }
                AstNodeExpr* const termp
                    = term.m_objective ? covExprp : new AstLogNot{fl, covExprp};
                if (condp) {
                    condp = new AstLogAnd{fl, condp, termp};
                } else {
                    condp = termp;
                }
                first = false;
            }
            comment += ") => ";
            comment += (m_objective ? '1' : '0');
            AstCoverOtherDecl* const declp = new AstCoverOtherDecl{
                nodep->fileline(), "v_expr/" + m_modp->prettyName(), comment, "", 0};
            m_modp->addStmtsp(declp);
            AstNode* const newp = newCoverInc(fl, declp, traceNameForLine(nodep, name));
            UASSERT_OBJ(condp, nodep, "No terms in expression coverage branch");
            AstIf* const ifp = new AstIf{fl, condp, newp, nullptr};
            ifp->user2(true);
            if (placement.m_transactional) {
                transactionStmtsp = AstNode::addNext(transactionStmtsp, ifp);
            } else if (placement.m_beforep) {
                placement.m_beforep->addHereThisAsNext(ifp);
            } else {
                insertProcStatement(m_exprStmtsp, ifp);
            }
            ++count;
        }
    }

    void coverExprs(AstNodeExpr* nodep) {
        if (m_transactionCoveredExprs.count(nodep)) return;
        if (!m_state.exprCoverageOn(nodep) || nodep->dtypep()->width() != 1 || !m_exprStmtsp) {
            return;
        }

        UASSERT_OBJ(m_seeking == NONE, nodep, "recursively covering expressions is not expected");
        UASSERT_OBJ(m_exprs.empty(), nodep, "unexpected expression coverage garbage");
        VL_RESTORER(m_seeking);
        VL_RESTORER(m_objective);
        VL_RESTORER_CLEAR(m_exprs);  // Already asserted above it's empty.

        m_seeking = SEEKING;
        AstNode* transactionStmtsp = nullptr;
        const ExprCoveragePlacement placement = exprCoveragePlacement(nodep);
        m_objective = false;
        iterate(nodep);
        CoverExprs falseExprs;
        m_exprs.swap(falseExprs);

        m_objective = true;
        iterate(nodep);
        if (checkMaxExprs(falseExprs.size())) return;
        if (m_seeking == ABORTED) return;

        addExprCoverInc(nodep, transactionStmtsp, placement);
        const int start = m_exprs.size();
        m_objective = false;
        m_exprs.swap(falseExprs);
        addExprCoverInc(nodep, transactionStmtsp, placement, start);
        if (transactionStmtsp) {
            m_transactionCoveredExprs.emplace(nodep);
            wrapExprCoverage(nodep, transactionStmtsp);
        }
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

        for (const CoverExpr& l : lhsExprs) {
            for (const CoverExpr& r : rhsExprs) {
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
                for (const CoverTerm& term : l) {
                    if (const AstVarRef* const refp = VN_CAST(term.m_exprp, VarRef)) {
                        varps[term.m_objective].insert(refp->varp());
                    } else {
                        strs[term.m_objective].insert(term.m_emitV);
                    }
                    expr.push_back(term);
                }
                bool impossible = false;
                for (const CoverTerm& term : r) {
                    bool redundant = false;
                    if (const AstNodeVarRef* const refp = VN_CAST(term.m_exprp, NodeVarRef)) {
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
        if (m_finishBoundaries.contains(nodep) && m_seeking == NONE) {
            coverExprs(nodep);
            lineTrack(nodep);
            return;
        }
        if (m_seeking != ABORTED) {
            FileLine* const fl = nodep->fileline();
            AstNodeExpr* const lhsp = nodep->lhsp();
            const int width = lhsp->dtypep()->width();
            const size_t expected = std::is_same<T_Oper, AstXor>::value ? 0x1 << width : width + 1;
            if (checkMaxExprs(expected)) return;
            AstNodeExpr* unrolledp = new AstSel{
                fl, lhsp->cloneTree(false), new AstConst{fl, static_cast<uint32_t>(width - 1)}, 1};
            for (int bit = width - 2; bit >= 0; bit--) {
                AstSel* const selp = new AstSel{fl, lhsp->cloneTree(false),
                                                new AstConst{fl, static_cast<uint32_t>(bit)}, 1};
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
            ExprCoverageEligibleVisitor elgibleVisitor(nodep, m_finishEffects);
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
    void visit(AstNode* nodep) override {
        iterateChildren(nodep);
        lineTrack(nodep);
    }

    void exprUnsupported(AstNode* nodep, const string& why) {
        UINFO(9, "unsupported: " << why << " " << nodep);
        const bool wasSeeking = m_seeking == SEEKING;
        const Objective oldSeeking = m_seeking;
        if (wasSeeking) abortExprCoverage();
        m_seeking = ABORTED;
        iterateChildren(nodep);
        lineTrack(nodep);
        if (!wasSeeking) m_seeking = oldSeeking;
    }

public:
    // CONSTRUCTORS
    CoverageVisitor(AstNetlist* rootp, const V3FinishEffects& finishEffects)
        : m_finishEffects{finishEffects}
        , m_finishBoundaries{rootp, finishEffects}
        , m_exprTempNames{"__VExpr"} {
        iterateChildren(rootp);
        for (AstStmtPragma* nodep : m_deferredDeletePragmas) {
            VL_DO_DANGLING(nodep->unlinkFrBack()->deleteTree(), nodep);
        }
    }
    ~CoverageVisitor() override = default;
};

//######################################################################
// Coverage class functions

void V3Coverage::coverage(AstNetlist* rootp, const V3FinishEffects& finishEffects) {
    UINFO(2, __FUNCTION__ << ":");
    { CoverageVisitor{rootp, finishEffects}; }  // Destruct before checking
    V3Global::dumpCheckGlobalTree("coverage", 0, dumpTreeEitherLevel() >= 3);
}
