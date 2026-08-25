// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: NFA-based multi-cycle SVA assertion evaluation
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2005-2026 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************
// V3AssertNfa's Transformations:
//
//  - Convert multi-cycle SVA sequences/properties into NFA graphs.
//  - Commit state in Observed; materialize outcome counts for Reactive
//    actions, exact per-attempt for supported bounded-depth shapes.
//  - Replace converted assertions with the materialized verdict so
//    V3AssertPre sees no multi-cycle SExpr (unsupported ones fall through).
//
//  Members marked OWNED hold an AST tree this pass allocated and must delete;
//  they are not linked into the netlist.
//
//*************************************************************************

#include "V3PchAstNoMT.h"  // VL_MT_DISABLED_CODE_UNIT

#include "V3AssertNfa.h"

#include "V3Assert.h"
#include "V3Const.h"
#include "V3Graph.h"
#include "V3Stats.h"
#include "V3Task.h"
#include "V3UniqueNames.h"

#include <algorithm>
#include <map>
#include <unordered_set>
#include <vector>

VL_DEFINE_DEBUG_FUNCTIONS;

//######################################################################
// NFA Graph Data Structures (V3Graph-derived per upstream convention)

namespace {

class SvaStateVertex;

// Per-vertex algorithm data, stored via V3GraphVertex::userp() during lowering
struct SvaVertexData final {
    AstVar* stateVarp = nullptr;  // Live state register for this vertex
    AstVar* evalStateVarp = nullptr;  // Old state used for the current verdict
    AstVar* delayRingVarp = nullptr;  // Live bitset ring buffer
    AstVar* evalDelayRingVarp = nullptr;  // Old ring used for the current verdict
    AstVar* delayRingIdxVarp = nullptr;  // Next live slot written in the ring
    AstVar* evalDelayRingIdxVarp = nullptr;  // Old ring index used for the verdict
    AstVar* doneLVarp = nullptr;  // SAnd LHS done-latch
    AstVar* doneRVarp = nullptr;  // SAnd RHS done-latch
    AstNodeExpr* stateSigp = nullptr;  // Combinational state signal; OWNED during lowering
    bool needsReg = false;  // True if vertex has incoming clocked edge
};

// NFA state vertex -- one per NFA position in the sequence evaluation
class SvaStateVertex final : public V3GraphVertex {
    VL_RTTI_IMPL(SvaStateVertex, V3GraphVertex)
public:
    // True if this is the sequence-match terminal vertex
    bool m_isMatch = false;
    // OWNED throughout-guard condition clones; IEEE 1800-2023 16.9.9
    std::vector<AstNodeExpr*> m_throughoutConds;
    // Nonzero for a bitset ring-buffer vertex for ## delays.
    bool m_isFixedDelayRing = false;
    unsigned m_delayRingSize = 0;  // Fixed delay cycles. Range: max-min+1.
    AstNodeExpr* m_delayRingClearCondp = nullptr;  // local RHS for pure-boolean range
    // OWNED; enclosing-abort fire condition clearing in-flight ring bits
    AstNodeExpr* m_abortClearp = nullptr;
    // Liveness terminal (IEEE weak semantics): reject must not fire from this source
    bool m_isUnbounded = false;
    // Same-end sequence intersect combiner; IEEE 1800-2023 16.9.6
    bool m_isAndCombiner = false;
    // Temporal 'and' permits different end cycles and therefore needs done latches.
    bool m_andNeedsDoneLatches = false;
    SvaStateVertex* m_andLhsTermp = nullptr;  // LHS sub-NFA terminal vertex
    SvaStateVertex* m_andRhsTermp = nullptr;  // RHS sub-NFA terminal vertex
    AstNodeExpr* m_andLhsCondp = nullptr;  // OWNED; LHS final condition (may be nullptr)
    AstNodeExpr* m_andRhsCondp = nullptr;  // OWNED; RHS final condition (may be nullptr)
    // Reject sink for SAnd rejectOnFail wiring; not a state-signal source
    bool m_isRejectSink = false;
    // In-window vertex of a strong s_always[m:n]: if its state is still set at
    // end-of-simulation the universal-quantifier window never completed, which is
    // a liveness failure (IEEE 1800-2023 16.12.11 strong semantics).
    bool m_strongPending = false;
    int m_strongPendingGroup = -1;  // One group per lexical s_always operator

    // CONSTRUCTORS
    explicit SvaStateVertex(V3Graph* graphp)
        : V3GraphVertex{graphp} {}
    ~SvaStateVertex() override {
        for (AstNodeExpr* cp : m_throughoutConds) VL_DO_DANGLING(cp->deleteTree(), cp);
        if (m_delayRingClearCondp)
            VL_DO_DANGLING(m_delayRingClearCondp->deleteTree(), m_delayRingClearCondp);
        if (m_abortClearp) VL_DO_DANGLING(m_abortClearp->deleteTree(), m_abortClearp);
        if (m_andLhsCondp) VL_DO_DANGLING(m_andLhsCondp->deleteTree(), m_andLhsCondp);
        if (m_andRhsCondp) VL_DO_DANGLING(m_andRhsCondp->deleteTree(), m_andRhsCondp);
    }
    // METHODS
    // LCOV_EXCL_START -- Graphviz dump only
    string name() const override {
        string name = "s" + cvtToStr(color());
        if (m_delayRingSize) {
            name += "\\n";
            name += m_isFixedDelayRing ? "fixed chain " : "range chain ";
            name += cvtToStr(m_delayRingSize) + " bits";
        }
        return name;
    }
    string dotColor() const override {
        if (m_isMatch) return "red";
        if (m_delayRingSize) return "blue";
        if (m_isAndCombiner) return "purple";
        return "black";
    }
    // LCOV_EXCL_STOP
    // Access per-vertex algorithm data (valid only during lowering phase)
    SvaVertexData* datap() const { return static_cast<SvaVertexData*>(userp()); }
};

// NFA transition edge -- clocked (##1) or combinational link (##0)
class SvaTransEdge final : public V3GraphEdge {
    VL_RTTI_IMPL(SvaTransEdge, V3GraphEdge)
public:
    AstNodeExpr* m_condp;  // Transition condition; nullptr = unconditional; OWNED
    bool m_consumesCycle;  // true = clocked edge (##1), false = link (##0/boolean)
    // Reject when source is active and condp is false; set only on
    // outermost required-step Link
    bool m_rejectOnFail = false;
    // Optional dynamic condition vertex for m_rejectOnFail. Used when the
    // success condition is another NFA state rather than a static expression.
    SvaStateVertex* m_condVtxp = nullptr;

    // CONSTRUCTORS
    SvaTransEdge(V3Graph* graphp, V3GraphVertex* fromp, V3GraphVertex* top, AstNodeExpr* condp,
                 bool consumesCycle)
        : V3GraphEdge{graphp, fromp, top, /*weight=*/1}
        , m_condp{condp}
        , m_consumesCycle{consumesCycle} {}
    ~SvaTransEdge() override {
        if (m_condp) VL_DO_DANGLING(m_condp->deleteTree(), m_condp);
    }
    // METHODS
    // LCOV_EXCL_START -- Graphviz dump only
    string dotLabel() const override { return m_consumesCycle ? "##1" : "link"; }
    string dotStyle() const override { return m_consumesCycle ? "" : "dashed"; }
    // LCOV_EXCL_STOP
    // Typed accessors for NFA vertices
    SvaStateVertex* fromVtxp() const { return static_cast<SvaStateVertex*>(fromp()); }
    SvaStateVertex* toVtxp() const { return static_cast<SvaStateVertex*>(top()); }
};

// NFA graph container
class SvaGraph final {
public:
    V3Graph m_graph;  // Owns all vertices and edges
    SvaStateVertex* m_startVertexp = nullptr;  // Trigger/start vertex
    SvaStateVertex* m_matchVertexp = nullptr;  // Sequence-match terminal vertex
    bool m_hasOrMerge = false;  // At least one temporal/property OR was lowered
    bool m_hasAndCombiner = false;  // At least one same-end intersect combiner was lowered

    // Create a new state vertex
    SvaStateVertex* createStateVertex() { return new SvaStateVertex{&m_graph}; }
    // Create the match terminal vertex
    SvaStateVertex* createMatchVertex() {
        SvaStateVertex* const vtxp = createStateVertex();
        vtxp->m_isMatch = true;
        m_matchVertexp = vtxp;
        return vtxp;
    }
    // Add a clocked transition edge (##1)
    SvaTransEdge* addClockedEdge(SvaStateVertex* fromp, SvaStateVertex* top,
                                 AstNodeExpr* condp = nullptr) {
        return new SvaTransEdge{&m_graph, fromp, top, condp, /*consumesCycle=*/true};
    }
    // Add a combinational link (##0 / boolean condition)
    SvaTransEdge* addLink(SvaStateVertex* fromp, SvaStateVertex* top,
                          AstNodeExpr* condp = nullptr) {
        return new SvaTransEdge{&m_graph, fromp, top, condp, /*consumesCycle=*/false};
    }
    // Collect all edges into a flat vector for iteration.
    // Used by the lowering phase which needs global edge scans.
    std::vector<const SvaTransEdge*> allEdges() const {
        std::vector<const SvaTransEdge*> result;
        for (const V3GraphVertex& vtxr : m_graph.vertices()) {
            for (const V3GraphEdge& edger : vtxr.outEdges()) {
                result.push_back(static_cast<const SvaTransEdge*>(&edger));
            }
        }
        return result;
    }
};

//######################################################################
// Builder result: terminal vertex + optional final condition (match Link condition).
struct BuildResult final {
    SvaStateVertex* termVertexp;  // Primary terminal; contributes to both match and reject
    AstNodeExpr* finalCondp;  // nullptr = unconditional
    // Mid-window sources for range delays (pure boolean RHS): match-only (isUnbounded)
    std::vector<SvaStateVertex*> midSources;
    bool errorEmitted = false;  // Builder already emitted specific error; skip generic
    // For cover_sequence: when true, midSources already enumerate every
    // end-of-match, so wireMatchAndMidSources must NOT add the main
    // termVtxp -> matchVertex Link (would double-count via the merge vertex).
    bool termIsMidMerge = false;
    bool valid() const { return termVertexp != nullptr; }
    static BuildResult fail(bool errored = false) { return {nullptr, nullptr, {}, errored}; }
    static BuildResult failWithError() { return {nullptr, nullptr, {}, true}; }
};

// Parser-marked SAnd of overlapped implications: a property if/else/case.
static bool isPropertyControlConjunction(const AstNodeExpr* nodep) {
    if (const AstSAnd* const andp = VN_CAST(nodep, SAnd)) {
        if (!andp->propertyControl()) return false;
        return isPropertyControlConjunction(andp->lhsp())
               && isPropertyControlConjunction(andp->rhsp());
    }
    const AstImplication* const implicationp = VN_CAST(nodep, Implication);
    return implicationp && implicationp->isOverlapped() && !implicationp->isFollowedBy();
}

static bool hasPropertyControlConjunction(const AstNodeExpr* nodep) {
    return nodep->exists([](const AstSAnd* andp) { return isPropertyControlConjunction(andp); });
}

// A peeled top-level abort expression remains owned by its source AstAbortOn.
struct AbortSpec final {
    VAbortKind kind;  // Accept/reject and sync/async flavor
    AstNodeExpr* condp;  // Abort condition (owned by nodep)
    AstAbortOn* nodep;  // Source node, deleted after lowering
};

static AstNodeExpr* sampled(AstNodeExpr* exprp) {
    return new AstSampled{exprp->fileline(), exprp, exprp->dtypep(), true};
}

static bool containsMultiCycleSva(const AstNodeExpr* nodep) {
    return nodep->exists([](const AstNodeExpr* ep) { return ep->isMultiCycleSva(); });
}

static string assertCtlGetCall(const char* query, VAssertType type,
                               VAssertDirectiveType directiveType) {
    return "vlSymsp->_vm_contextp__->assertCtlGet(VerilatedAssertCtlQuery::"s + query + ", "s
           + std::to_string(type) + ", "s + std::to_string(directiveType) + ")"s;
}

static const char* assertPassOnQuery(bool vacuous) {
    static constexpr const char* queries[2]
        = {"ASSERT_CTL_PASS_ON_NONVACUOUS", "ASSERT_CTL_PASS_ON_VACUOUS"};
    return queries[vacuous];
}

// Observed captures impure assertion-control queries once; action gates read them live.
static AstNodeExpr* assertOnCond(FileLine* flp, VAssertType type,
                                 VAssertDirectiveType directiveType) {
    if (!v3Global.opt.assertOn()) { return new AstConst{flp, AstConst::BitFalse{}}; }
    return new AstCExpr{flp, assertCtlGetCall("ASSERT_CTL_ON", type, directiveType), 1};
}

static AstNodeExpr* assertKillGet(FileLine* flp, VAssertType type,
                                  VAssertDirectiveType directiveType) {
    return new AstCExpr{flp, assertCtlGetCall("ASSERT_CTL_KILL", type, directiveType), 32};
}

static string assertActionControlPrefix(VAssertDirectiveType directiveType) {
    const int controlled = !!(static_cast<int>(directiveType)
                              & (static_cast<int>(VAssertDirectiveType::ASSERT)
                                 | static_cast<int>(VAssertDirectiveType::COVER)
                                 | static_cast<int>(VAssertDirectiveType::ASSUME)));
    const int checkRuntime = controlled & static_cast<int>(v3Global.opt.assertOn());
    return "("s + std::to_string(controlled ^ 1) + " || ("s + std::to_string(checkRuntime)
           + " && "s;
}

static AstNodeExpr* assertPassOnCond(FileLine* flp, VAssertType type,
                                     VAssertDirectiveType directiveType, bool vacuous) {
    return new AstCExpr{flp,
                        assertActionControlPrefix(directiveType)
                            + assertCtlGetCall(assertPassOnQuery(vacuous), type, directiveType)
                            + "))"s,
                        1};
}

static AstNodeExpr* assertFailOnCond(FileLine* flp, VAssertType type,
                                     VAssertDirectiveType directiveType) {
    return new AstCExpr{flp,
                        assertActionControlPrefix(directiveType)
                            + assertCtlGetCall("ASSERT_CTL_FAIL_ON", type, directiveType) + "))"s,
                        1};
}

static AstIf* newPassOnIf(FileLine* flp, AstNodeExpr* firep, AstNode* bodyp, VAssertType type,
                          VAssertDirectiveType directiveType, bool vacuous) {
    AstNodeExpr* const condp
        = new AstLogAnd{flp, firep, assertPassOnCond(flp, type, directiveType, vacuous)};
    AstIf* const ifp = new AstIf{flp, condp, bodyp};
    ifp->isBoundsCheck(true);
    ifp->user1(true);
    return ifp;
}

//######################################################################
// NFA Builder

class SvaNfaBuilder final {
    SvaGraph& m_graph;  // NFA graph being built
    AstNodeModule* const m_modp;  // Module to receive hoisted sampled-prop temps
    V3UniqueNames& m_propTempNames;  // Module-shared temp-var name source
    std::vector<AstNodeExpr*> m_temporalGuardStack;  // Guards active across nested temporal states
    // Outer abort conditions, AND-ed as !cond into inner abort edges
    // (IEEE 1800-2023 16.12.14 outer-wraps-inner).
    std::vector<AstNodeExpr*> m_outerAbortStack;
    bool m_inUnboundedScope = false;  // Sticky: nodes created after inherit liveness
    bool m_markStrongPending = false;  // Mark new vertices as strong s_always in-window
    int m_strongPendingGroup = -1;  // Group currently being built, or -1
    int m_nextStrongPendingGroup = 0;  // Unique group for each strong s_always
    // IEEE 1800-2023 16.14.3 cover sequence: each end-of-match fires the action,
    // not just the first. Builder builds parallel-branch (no first-match-wins)
    // topology when true. Default false preserves cover_property semantics.
    bool m_isCoverSeq = false;
    // Assertions and negated covers need exact per-attempt reject outcomes.
    bool m_needsRejectVerdict = true;

    bool mayEmitLocalReject(bool isTopLevelStep) const {
        return isTopLevelStep && m_needsRejectVerdict && !m_inUnboundedScope;
    }

    static void cleanupProbeResult(const BuildResult& result) {
        if (result.finalCondp && !result.finalCondp->backp()) {
            VL_DO_DANGLING(result.finalCondp->deleteTree(), result.finalCondp);
        }
    }
    // Unsupported endpoint topology must reject, not ignore, or the wait hangs
    bool m_isSeqEvent = false;

    struct RangeDelayRejectInfo final {
        SvaStateVertex* startp = nullptr;
        unsigned range = 0;
        int rhsLen = 0;
    };

    void warnEndpointUnsupported(FileLine* flp, const string& what) const {
        if (m_isSeqEvent) {
            flp->v3warn(E_UNSUPPORTED,
                        "Unsupported: sequence used as an event control with " << what);
        } else {
            flp->v3warn(COVERIGN, "Ignoring unsupported: cover sequence with " << what);
        }
    }

    AstNodeExpr* throughoutCond(AstNodeExpr* baseCondp, FileLine* flp) {
        if (m_temporalGuardStack.empty()) return baseCondp;
        // AND all active temporal guards (supports nesting)
        // Each must use $sampled values.
        AstNodeExpr* guardp = nullptr;
        for (AstNodeExpr* const condp : m_temporalGuardStack) {
            AstNodeExpr* const clonep = sampled(condp->cloneTreePure(false));
            if (!guardp) {
                guardp = clonep;
            } else {
                guardp = new AstLogAnd{flp, guardp, clonep};
            }
        }
        if (baseCondp) { guardp = new AstLogAnd{flp, baseCondp, guardp}; }
        return guardp;
    }

    static unsigned getConstUInt(AstNodeExpr* exprp) {
        AstNodeExpr* const constp = V3Const::constifyEdit(exprp->cloneTreePure(false));
        const AstConst* const cp = VN_CAST(constp, Const);
        const unsigned val = cp ? cp->toUInt() : 0;
        VL_DO_DANGLING(constp->deleteTree(), constp);
        return val;
    }

    // Return a fixed clock-tick length, or -1 for variable/unbounded operands.
    static int fixedLength(AstNodeExpr* nodep) {
        if (AstSExpr* const sexprp = VN_CAST(nodep, SExpr)) {
            AstDelay* const delayp = VN_CAST(sexprp->delayp(), Delay);
            if (!delayp || !delayp->isCycleDelay()) return -1;
            unsigned delayCycles;
            if (delayp->isRangeDelay()) {
                if (delayp->isUnbounded()) return -1;  // LCOV_EXCL_LINE
                const unsigned minD = getConstUInt(delayp->lhsp());
                const unsigned maxD = getConstUInt(delayp->rhsp());
                if (minD != maxD) return -1;
                delayCycles = minD;
            } else {
                delayCycles = getConstUInt(delayp->lhsp());
            }
            int preLen = 0;
            if (AstNodeExpr* const prep = sexprp->preExprp()) {
                preLen = fixedLength(prep);
                if (preLen < 0) return -1;  // LCOV_EXCL_LINE
            }
            const int bodyLen = fixedLength(sexprp->exprp());
            if (bodyLen < 0) return -1;  // LCOV_EXCL_LINE
            return preLen + delayCycles + bodyLen;
        }
        if (AstSThroughout* const throughp = VN_CAST(nodep, SThroughout)) {
            return fixedLength(throughp->rhsp());
        }
        if (AstPropAlways* const alwaysp = VN_CAST(nodep, PropAlways)) {
            if (VN_IS(alwaysp->hiBoundp(), Unbounded) || alwaysp->propp()->isMultiCycleSva()) {
                return -1;
            }
            return static_cast<int>(getConstUInt(alwaysp->hiBoundp()));
        }
        if (AstAbortOn* const abortp = VN_CAST(nodep, AbortOn)) return fixedLength(abortp->propp());
        if (AstSConsRep* const repp = VN_CAST(nodep, SConsRep)) {
            if (repp->unbounded() || repp->exprp()->isMultiCycleSva()) return -1;
            const unsigned minN = getConstUInt(repp->countp());
            if (repp->maxCountp() && getConstUInt(repp->maxCountp()) != minN) return -1;
            return minN ? static_cast<int>(minN - 1) : 0;
        }
        if (AstSAnd* const andp = VN_CAST(nodep, SAnd)) {
            const int lhsLen = fixedLength(andp->lhsp());
            const int rhsLen = fixedLength(andp->rhsp());
            if (lhsLen < 0 || rhsLen < 0) return -1;
            return std::max(lhsLen, rhsLen);
        }
        if (AstSOr* const orp = VN_CAST(nodep, SOr)) {
            // Alternatives must share one end cycle; buildSWithin relies on
            // this to pair the OR with an SIntersect.
            const int lhsLen = fixedLength(orp->lhsp());
            const int rhsLen = fixedLength(orp->rhsp());
            if (lhsLen < 0 || rhsLen < 0 || lhsLen != rhsLen) return -1;
            return lhsLen;
        }
        if (AstSWithin* const withinp = VN_CAST(nodep, SWithin)) {
            // `seq1 within seq2` ends at seq2's end cycle (IEEE 16.9.10).
            const int lhsLen = fixedLength(withinp->lhsp());
            const int rhsLen = fixedLength(withinp->rhsp());
            if (lhsLen < 0 || rhsLen < 0 || lhsLen > rhsLen) return -1;
            return rhsLen;
        }
        // LCOV_EXCL_START -- defensive: V3AssertPre rejects composite SVA ops
        // nested in an intersect arm before fixedLength runs (clock-context
        // resolution fails). Kept as a guard in case future parser relaxations
        // permit it.
        if (nodep->exists([](const AstNodeExpr* ep) { return ep->isMultiCycleSva(); })) return -1;
        // LCOV_EXCL_STOP
        // Plain boolean expression (no SVA constructs) -- 0 cycles.
        return 0;
    }

    // Operators that can reject before their fixed endpoint (a later deadline double-rejects).
    static bool mayRejectBeforeEnd(AstNodeExpr* nodep) {
        return nodep->exists([](const AstSThroughout*) { return true; })
               || nodep->exists([](const AstAbortOn*) { return true; })
               || nodep->exists([](const AstUntil*) { return true; })
               || nodep->exists([](const AstPropAlways* const alwaysp) {
                      const AstConst* const constp = VN_CAST(alwaysp->propp(), Const);
                      return !constp || constp->num().isFourState() || constp->num().isEqZero();
                  });
    }

    static bool containsImpureExpr(AstNode* nodep) {
        return nodep->exists([](AstNode* const np) {
            // $random reports pure but advances RNG state; must not be duplicated.
            return VN_IS(np, Rand) || VN_IS(np, RandRNG) || !np->isPure();
        });
    }

    // Return [lo,hi] for one ranged delay, or {-1,-1} otherwise (IEEE 16.9.6).
    static std::pair<int, int> lengthRange(AstNodeExpr* nodep) {
        if (AstSExpr* const sexprp = VN_CAST(nodep, SExpr)) {
            AstDelay* const delayp = VN_CAST(sexprp->delayp(), Delay);
            if (!delayp || !delayp->isCycleDelay()) return {-1, -1};
            std::pair<int, int> delayRange;
            if (delayp->isRangeDelay()) {
                if (delayp->isUnbounded()) return {-1, -1};
                const unsigned minD = getConstUInt(delayp->lhsp());
                const unsigned maxD = getConstUInt(delayp->rhsp());
                delayRange = {minD, maxD};
            } else {
                const unsigned d = getConstUInt(delayp->lhsp());
                delayRange = {d, d};
            }
            std::pair<int, int> preRange{0, 0};
            if (AstNodeExpr* const prep = sexprp->preExprp()) {
                preRange = lengthRange(prep);
                if (preRange.first < 0) return {-1, -1};
            }
            const std::pair<int, int> bodyRange = lengthRange(sexprp->exprp());
            if (bodyRange.first < 0) return {-1, -1};
            const int variableParts = (preRange.first != preRange.second)
                                      + (delayRange.first != delayRange.second)
                                      + (bodyRange.first != bodyRange.second);
            if (variableParts > 1) return {-1, -1};
            return {preRange.first + delayRange.first + bodyRange.first,
                    preRange.second + delayRange.second + bodyRange.second};
        }
        if (AstSThroughout* const throughp = VN_CAST(nodep, SThroughout)) {
            return lengthRange(throughp->rhsp());
        }
        if (nodep->isMultiCycleSva()) return {-1, -1};
        return {0, 0};  // plain boolean -- 0 cycles
    }

    // Clone `operand` with its sole variable ranged cycle delay pinned so the
    // total match length is exactly `len`. `lo` is the operand's minimum length
    // (lengthRange().first). A fixed operand has no such delay and is returned
    // as a plain clone (callers only request its single achievable length).
    static AstNodeExpr* realizeAtLength(AstNodeExpr* operand, int len, int lo) {
        AstNodeExpr* const clonep = operand->cloneTreePure(false);
        AstDelay* rangeDelayp = nullptr;
        clonep->foreach([&](AstDelay* dp) {
            if (!rangeDelayp && dp->isRangeDelay() && !dp->isUnbounded()
                && getConstUInt(dp->lhsp()) != getConstUInt(dp->rhsp())) {
                rangeDelayp = dp;
            }
        });
        if (rangeDelayp) {
            FileLine* const flp = rangeDelayp->fileline();
            const unsigned pinned = getConstUInt(rangeDelayp->lhsp()) + (len - lo);
            AstNodeExpr* const oldMinp = rangeDelayp->lhsp();
            oldMinp->replaceWith(new AstConst{flp, pinned});
            VL_DO_DANGLING(oldMinp->deleteTree(), oldMinp);
            // Drop the max bound so it lowers as a fixed `##d`, not `##[d:d]`.
            AstNode* const oldMaxp = rangeDelayp->rhsp()->unlinkFrBack();
            VL_DO_DANGLING(oldMaxp->deleteTree(), oldMaxp);
        }
        return clonep;
    }

    // Cuts AST size from O(N * sizeof(exprp)) to O(N) + O(sizeof(exprp)) by
    // sharing a single `VarRef` across N check edges. Hoist also matches the
    // IEEE 1800-2023 16.9.9 "single preponed-region snapshot" semantic for
    // any exprp -- even an impure one would now evaluate exactly once per
    // clock instead of N times. Orphan temps from failed builds are unused
    // MODULETEMPs and are removed by V3Dead.
    AstVar* tryHoistSampled(AstNodeExpr* exprp, FileLine* flp, unsigned cloneCount) {
        constexpr unsigned kHoistThreshold = 2;
        if (cloneCount < kHoistThreshold) return nullptr;
        AstVar* const tempVarp
            = new AstVar{flp, VVarType::MODULETEMP, m_propTempNames.get(exprp), exprp->dtypep()};
        m_modp->addStmtsp(tempVarp);
        AstAssign* const assignp = new AstAssign{flp, new AstVarRef{flp, tempVarp, VAccess::WRITE},
                                                 sampled(exprp->cloneTreePure(false))};
        m_modp->addStmtsp(new AstAlways{flp, VAlwaysKwd::ALWAYS_COMB, nullptr, assignp});
        return tempVarp;
    }

    static AstNodeExpr* sampledRefOrClone(AstVar* hoistVarp, AstNodeExpr* exprp, FileLine* flp) {
        if (hoistVarp) return new AstVarRef{flp, hoistVarp, VAccess::READ};
        return sampled(exprp->cloneTreePure(false));
    }

    // Reject concurrent assertions whose unrolled vertex count would exceed
    // --assert-unroll-limit, so a pathological count cannot blow up compile time.
    static bool exceedsAssertUnrollLimit(AstNode* nodep, unsigned requested) {
        const int limit = v3Global.opt.assertUnrollLimit();
        if (limit >= 0 && requested <= static_cast<unsigned>(limit)) return false;
        nodep->v3error("Concurrent assertion repetition count "
                       << requested << " exceeds --assert-unroll-limit (" << limit
                       << "); raise '--assert-unroll-limit' to compile");
        return true;
    }

    // Create vertex and inherit temporal guards from the current scope.
    SvaStateVertex* scopedCreateVertex() {
        SvaStateVertex* const vtxp = m_graph.createStateVertex();
        for (AstNodeExpr* const cp : m_temporalGuardStack) {
            vtxp->m_throughoutConds.push_back(cp->cloneTreePure(false));
        }
        if (m_inUnboundedScope) vtxp->m_isUnbounded = true;
        if (m_markStrongPending) {
            vtxp->m_strongPending = true;
            vtxp->m_strongPendingGroup = m_strongPendingGroup;
        }
        return vtxp;
    }

    // AND current temporal guards into every edge/link.
    SvaTransEdge* guardedLink(SvaStateVertex* fromp, SvaStateVertex* top, AstNodeExpr* condp,
                              FileLine* flp) {
        return m_graph.addLink(fromp, top, throughoutCond(condp, flp));
    }
    SvaTransEdge* guardedLink(SvaStateVertex* fromp, SvaStateVertex* top, FileLine* flp) {
        return m_graph.addLink(fromp, top, throughoutCond(nullptr, flp));
    }
    SvaTransEdge* guardedEdge(SvaStateVertex* fromp, SvaStateVertex* top, AstNodeExpr* condp,
                              FileLine* flp) {
        return m_graph.addClockedEdge(fromp, top, throughoutCond(condp, flp));
    }
    SvaTransEdge* guardedEdge(SvaStateVertex* fromp, SvaStateVertex* top, FileLine* flp) {
        return m_graph.addClockedEdge(fromp, top, throughoutCond(nullptr, flp));
    }

    SvaStateVertex* addDelayChain(SvaStateVertex* startp, unsigned size, FileLine* flp,
                                  bool isFixed = true, AstNodeExpr* clearCondp = nullptr) {
        if (isFixed && size == 0) return startp;
        UASSERT_OBJ(size > 0, startp, "Delay chain needs at least one slot");
        if (isFixed && size == 1) {
            SvaStateVertex* const nextp = scopedCreateVertex();
            guardedEdge(startp, nextp, flp);
            return nextp;
        }
        SvaStateVertex* const ringVtxp = scopedCreateVertex();
        ringVtxp->m_isFixedDelayRing = isFixed;
        ringVtxp->m_delayRingSize = size;
        if (clearCondp) {
            UASSERT_OBJ(!isFixed, startp, "Fixed delay cannot have a clear condition");
            ringVtxp->m_delayRingClearCondp = clearCondp->cloneTreePure(false);
        }
        if (isFixed) {
            guardedEdge(startp, ringVtxp, flp);
        } else {
            guardedLink(startp, ringVtxp, flp);
        }
        return ringVtxp;
    }

    // Build NFA for an SExpr. finalCond = RHS (not yet added as a vertex).
    // isTopLevelStep: marks outermost required boolean check as rejectOnFail.
    // Apply a range delay `##[M:N]` to currentp. Returns true on success. On
    // failure, sets outErrorEmitted per semantic-error policy and returns false.
    bool applyRangeDelay(AstDelay* delayp, AstNodeExpr* rhsExprp, SvaStateVertex*& currentp,
                         std::vector<SvaStateVertex*>& midSources, FileLine* flp,
                         bool& outErrorEmitted, RangeDelayRejectInfo* rangeRejectInfop = nullptr) {
        const unsigned minDelay = getConstUInt(delayp->lhsp());
        if (delayp->isUnbounded()) {
            // `##[M:$]`: wait M cycles, then self-loop waiting for the match
            // condition. Unbounded = liveness, so no reject.
            currentp = addDelayChain(currentp, minDelay, flp);
            guardedEdge(currentp, currentp, flp);
            currentp->m_isUnbounded = true;
            m_inUnboundedScope = true;
            return true;
        }
        const unsigned maxDelay = getConstUInt(delayp->rhsp());
        if (minDelay == maxDelay) {
            currentp = addDelayChain(currentp, minDelay, flp);
            return true;
        }
        const unsigned range = maxDelay - minDelay;
        currentp = addDelayChain(currentp, minDelay, flp);
        // kChainLimit bounds per-attempt unrolled vertices. Above this, a
        // ring buffer (constant-size state) is used instead, so the vertex
        // count is O(1) in range regardless of user input; no adversarial N
        // blowup is possible.
        constexpr unsigned kChainLimit = 256;
        // IEEE 1800-2023 16.14.3: only a small bounded range before a plain
        // boolean enumerates every end-of-match below. The counter FSM drops
        // overlapping ends and the nested-sequence merge collapses them, so
        // reject those for a cover sequence rather than under-count.
        if (m_isCoverSeq && (range > kChainLimit || VN_IS(rhsExprp, SExpr))) {
            warnEndpointUnsupported(flp, "this ranged cycle delay");
            outErrorEmitted = true;
            return false;
        }
        if (range > kChainLimit) {
            currentp = addDelayChain(currentp, range + 1U, flp, false,
                                     rhsExprp->isMultiCycleSva() ? nullptr : rhsExprp);
        } else if (VN_IS(rhsExprp, SExpr)) {
            // Nested-SExpr RHS: merge all [M,N] positions. Candidate-local misses
            // are not assertion rejects while a later position can still match.
            if (rangeRejectInfop) {
                const int rhsLen = fixedLength(rhsExprp);
                if (rhsLen >= 0) *rangeRejectInfop = {currentp, range, rhsLen};
            }
            SvaStateVertex* const mergeVtxp = scopedCreateVertex();
            mergeVtxp->m_isUnbounded = true;
            guardedLink(currentp, mergeVtxp, flp);
            for (unsigned i = 0; i < range; ++i) {
                SvaStateVertex* const nextVtxp = scopedCreateVertex();
                guardedEdge(currentp, nextVtxp, flp);
                guardedLink(nextVtxp, mergeVtxp, flp);
                currentp = nextVtxp;
            }
            currentp = mergeVtxp;
            m_inUnboundedScope = true;
        } else {
            // Pure boolean RHS: register chain. Each mid-position links to
            // match (match-only); last position is the reject source.
            // For cover_sequence (IEEE 1800-2023 16.14.3) the advance edge is
            // unconditional so every (start, end) pair fires independently --
            // dropping NOT(b) turns "first-match-wins" into "every end fires".
            AstVar* const hoistVarp
                = m_isCoverSeq ? nullptr : tryHoistSampled(rhsExprp, flp, range);
            midSources.push_back(currentp);
            for (unsigned i = 0; i < range; ++i) {
                SvaStateVertex* const nextVtxp = scopedCreateVertex();
                if (m_isCoverSeq) {
                    guardedEdge(currentp, nextVtxp, flp);
                } else {
                    AstNodeExpr* const notExprp
                        = new AstLogNot{flp, sampledRefOrClone(hoistVarp, rhsExprp, flp)};
                    guardedEdge(currentp, nextVtxp, notExprp, flp);
                }
                if (i < range - 1) midSources.push_back(nextVtxp);
                currentp = nextVtxp;
            }
        }
        return true;
    }

    void addFiniteRangeReject(const RangeDelayRejectInfo& info, const BuildResult& result,
                              FileLine* flp) {
        if (!info.startp) return;

        SvaStateVertex* const expiryVtxp
            = addDelayChain(info.startp, info.range + info.rhsLen, flp);
        SvaStateVertex* const expiryMatchp = scopedCreateVertex();
        std::vector<SvaStateVertex*> sources = result.midSources;
        sources.push_back(result.termVertexp);
        for (SvaStateVertex* const srcp : sources) {
            AstNodeExpr* const condp
                = result.finalCondp ? sampled(result.finalCondp->cloneTreePure(false)) : nullptr;
            SvaStateVertex* const successNowp = scopedCreateVertex();
            guardedLink(srcp, successNowp, condp, flp);
            SvaStateVertex* stagep = successNowp;
            guardedLink(stagep, expiryMatchp, flp);
            for (unsigned i = 0; i < info.range; ++i) {
                SvaStateVertex* const nextp = scopedCreateVertex();
                guardedEdge(stagep, nextp, flp);
                stagep = nextp;
                guardedLink(stagep, expiryMatchp, flp);
            }
        }

        SvaStateVertex* const sinkVtxp = m_graph.createStateVertex();
        sinkVtxp->m_isRejectSink = true;
        SvaTransEdge* const rejectp = m_graph.addLink(expiryVtxp, sinkVtxp);
        rejectp->m_rejectOnFail = true;
        rejectp->m_condVtxp = expiryMatchp;
    }

    BuildResult buildSExpr(AstSExpr* sexprp, SvaStateVertex* entryVtxp,
                           bool isTopLevelStep = false) {
        AstDelay* const delayp = VN_CAST(sexprp->delayp(), Delay);
        if (!delayp || !delayp->isCycleDelay()) return BuildResult::fail();

        FileLine* const flp = sexprp->fileline();
        AstNodeExpr* const exprp = sexprp->exprp();

        // Handle LHS (preExpr)
        SvaStateVertex* currentp = entryVtxp;
        if (AstNodeExpr* const preExprp = sexprp->preExprp()) {
            const BuildResult pre = buildExpr(preExprp, currentp, isTopLevelStep);
            if (!pre.valid()) return BuildResult::fail(pre.errorEmitted);  // LCOV_EXCL_LINE
            if (pre.finalCondp) {
                SvaStateVertex* const condVtxp = scopedCreateVertex();
                SvaTransEdge* const edgep = guardedLink(
                    pre.termVertexp, condVtxp, sampled(pre.finalCondp->cloneTreePure(false)), flp);
                if (mayEmitLocalReject(isTopLevelStep) && !pre.termVertexp->m_isUnbounded) {
                    // Do not mark liveness sources: first boolean check is deferred.
                    edgep->m_rejectOnFail = true;
                }
                cleanupProbeResult(pre);
                currentp = condVtxp;
            } else {
                currentp = pre.termVertexp;
            }
        }

        // Handle delay
        std::vector<SvaStateVertex*> rangeMidSources;
        RangeDelayRejectInfo rangeRejectInfo;
        const bool addRangeReject = mayEmitLocalReject(isTopLevelStep);
        if (delayp->isRangeDelay()) {
            bool errorEmitted = false;
            if (!applyRangeDelay(delayp, sexprp->exprp(), currentp, rangeMidSources, flp,
                                 errorEmitted, addRangeReject ? &rangeRejectInfo : nullptr)) {
                return BuildResult::fail(errorEmitted);
            }
        } else {
            const unsigned delayCycles = getConstUInt(delayp->lhsp());
            currentp = addDelayChain(currentp, delayCycles, flp);
        }

        // Multi-cycle RHS: recurse (only plain boolean is returned as finalCondp).
        if (exprp->isMultiCycleSva()) {
            const BuildResult result = buildExpr(exprp, currentp, isTopLevelStep);
            if (result.valid()) addFiniteRangeReject(rangeRejectInfo, result, flp);
            return result;
        }
        return {currentp, exprp, std::move(rangeMidSources)};
    }

    BuildResult buildConsRep(AstSConsRep* repp, SvaStateVertex* entryVtxp,
                             bool isTopLevelStep = false) {
        FileLine* const flp = repp->fileline();
        AstNodeExpr* const exprp = repp->exprp();
        // Multi-cycle expr in ConsRep not yet supported; bail to avoid invalid AST.
        if (exprp->isMultiCycleSva()) {
            repp->v3warn(E_UNSUPPORTED, "Unsupported: multi-cycle sequence expression inside"
                                        " consecutive repetition (IEEE 1800-2023 16.9.2)");
            return BuildResult::failWithError();
        }
        const unsigned minN = getConstUInt(repp->countp());

        // Sum sites across prefix + unbounded/range tail so one hoist covers
        // every check edge of this repetition.
        unsigned totalSites = minN;
        if (repp->unbounded()) {
            totalSites += 1;
        } else if (repp->maxCountp()) {
            totalSites += getConstUInt(repp->maxCountp()) - minN;
        }
        if (exceedsAssertUnrollLimit(repp, totalSites)) return BuildResult::failWithError();
        AstVar* const hoistVarp = tryHoistSampled(exprp, flp, totalSites);

        // Cover-sequence (IEEE 1800-2023 16.14.3): collect each end-of-match
        // position so they all fire the action, not just the merged terminal.
        std::vector<SvaStateVertex*> consMidSources;

        SvaStateVertex* currentp = entryVtxp;
        for (unsigned i = 0; i < minN; ++i) {
            if (i > 0) {
                SvaStateVertex* const nextp = scopedCreateVertex();
                guardedEdge(currentp, nextp, flp);
                currentp = nextp;
            }
            // Every repetition in the minimum prefix is required.
            SvaStateVertex* const condVtxp = scopedCreateVertex();
            SvaTransEdge* const linkp
                = guardedLink(currentp, condVtxp, sampledRefOrClone(hoistVarp, exprp, flp), flp);
            if (mayEmitLocalReject(isTopLevelStep)) linkp->m_rejectOnFail = true;
            currentp = condVtxp;
        }
        // After minN: currentp is the first valid end-of-match position for [*m:n].
        if (m_isCoverSeq && (repp->unbounded() || repp->maxCountp())) {
            consMidSources.push_back(currentp);
        }

        if (repp->unbounded()) {
            if (minN == 0) {
                SvaStateVertex* const waitVtxp = scopedCreateVertex();
                guardedEdge(currentp, waitVtxp, flp);
                SvaStateVertex* const checkVtxp = scopedCreateVertex();
                guardedLink(waitVtxp, checkVtxp, sampledRefOrClone(hoistVarp, exprp, flp), flp);
                guardedEdge(checkVtxp, waitVtxp, flp);
                guardedLink(currentp, checkVtxp, flp);
                currentp = checkVtxp;
            } else {
                SvaStateVertex* const loopBackVtxp = scopedCreateVertex();
                guardedEdge(currentp, loopBackVtxp, flp);
                SvaStateVertex* const reCheckVtxp = scopedCreateVertex();
                guardedLink(loopBackVtxp, reCheckVtxp, sampledRefOrClone(hoistVarp, exprp, flp),
                            flp);
                guardedEdge(reCheckVtxp, loopBackVtxp, flp);
                guardedLink(reCheckVtxp, currentp, flp);
            }
            currentp->m_isUnbounded = true;
            m_inUnboundedScope = true;
        } else if (repp->maxCountp()) {
            const unsigned maxN = getConstUInt(repp->maxCountp());
            SvaStateVertex* const mergeVtxp = scopedCreateVertex();
            guardedLink(currentp, mergeVtxp, flp);
            for (unsigned i = minN; i < maxN; ++i) {
                SvaStateVertex* const nextVtxp = scopedCreateVertex();
                guardedEdge(currentp, nextVtxp, flp);
                SvaStateVertex* const checkVtxp = scopedCreateVertex();
                guardedLink(nextVtxp, checkVtxp, sampledRefOrClone(hoistVarp, exprp, flp), flp);
                guardedLink(checkVtxp, mergeVtxp, flp);
                currentp = checkVtxp;
                if (m_isCoverSeq) consMidSources.push_back(checkVtxp);
            }
            currentp = mergeVtxp;
        }
        // finalCond = nullptr (already checked via Links)
        BuildResult res;
        res.termVertexp = currentp;
        res.finalCondp = nullptr;
        res.midSources = std::move(consMidSources);
        // mergeVtxp is the OR of all the end-positions we already pushed to
        // midSources, so the main termVtxp -> matchVertex Link would duplicate.
        res.termIsMidMerge = m_isCoverSeq && !res.midSources.empty();
        return res;
    }

    // always[lo:hi] / s_always[lo:hi] (IEEE 1800-2023 16.12.11).
    BuildResult buildPropAlways(AstPropAlways* nodep, SvaStateVertex* entryVtxp,
                                bool isTopLevelStep = false) {
        FileLine* const flp = nodep->fileline();
        AstNodeExpr* const propp = nodep->propp();
        const unsigned lo = getConstUInt(nodep->loBoundp());
        if (VN_IS(nodep->hiBoundp(), Unbounded)) {
            // Weak always [lo:$]: unbounded upper bound (IEEE 1800-2023 16.12.11).
            // p must hold at every clock tick at least lo cycles after the attempt
            // start; those ticks are not required to exist, so there is no
            // end-of-trace obligation (weak). The self-loop keeps the attempt live
            // every cycle; each observed cycle is a safety obligation, so a false p
            // rejects immediately.
            UASSERT_OBJ(!nodep->isStrong(), nodep, "Unbounded always must be weak (V3Width)");
            SvaStateVertex* const livep = addDelayChain(entryVtxp, lo, flp);
            livep->m_isUnbounded = true;
            guardedEdge(livep, livep, flp);  // stay active every subsequent cycle
            SvaStateVertex* const sinkp = m_graph.createStateVertex();
            sinkp->m_isRejectSink = true;
            SvaTransEdge* const rejEdgep
                = guardedLink(livep, sinkp, sampled(propp->cloneTreePure(false)), flp);
            if (mayEmitLocalReject(isTopLevelStep)) rejEdgep->m_rejectOnFail = true;
            return {livep, nullptr, {}};
        }
        const unsigned hi = getConstUInt(nodep->hiBoundp());
        // Strong s_always[m:n]: mark every in-window registered vertex so an
        // attempt still mid-window at end-of-simulation is reported as a liveness
        // failure (IEEE strong: the n+1 ticks must exist). An attempt that has
        // completed earlier in the trace has already cleared its state, so it is
        // not flagged; an attempt whose final tick coincides with $finish is still
        // flagged, matching the strong reference. Weak always[m:n] is not marked.
        VL_RESTORER(m_markStrongPending);
        VL_RESTORER(m_strongPendingGroup);
        m_markStrongPending = nodep->isStrong();
        m_strongPendingGroup = nodep->isStrong() ? m_nextStrongPendingGroup++ : -1;
        // Check the first in-window tick, then reuse a guarded fixed-delay ring
        // for the remaining ticks instead of creating one state per cycle.
        SvaStateVertex* currentp = addDelayChain(entryVtxp, lo, flp);
        SvaStateVertex* const checkp = scopedCreateVertex();
        SvaTransEdge* const linkp
            = guardedLink(currentp, checkp, sampled(propp->cloneTreePure(false)), flp);
        if (mayEmitLocalReject(isTopLevelStep)) linkp->m_rejectOnFail = true;
        currentp = checkp;
        m_temporalGuardStack.push_back(propp);
        currentp = addDelayChain(currentp, hi - lo, flp);
        m_temporalGuardStack.pop_back();
        return {currentp, propp, {}};
    }

    BuildResult buildGotoRep(AstSGotoRep* repp, SvaStateVertex* entryVtxp) {
        FileLine* const flp = repp->fileline();
        AstNodeExpr* const exprp = repp->exprp();
        const unsigned minN = getConstUInt(repp->countp());
        if (minN == 0) return BuildResult::fail();
        const bool hasMax = repp->maxCountp() != nullptr;
        const unsigned maxN = hasMax ? getConstUInt(repp->maxCountp()) : minN;
        if (exceedsAssertUnrollLimit(repp, maxN)) return BuildResult::failWithError();

        if (m_isCoverSeq) {
            // Several matches may wait across false cycles, but the NFA stores only one bit for
            // them, so a cover sequence action block could run too few times.
            warnEndpointUnsupported(flp, "a goto repetition");
            return BuildResult::failWithError();
        }

        // Wait + match per iter -> 2 sites per iteration; range form needs
        // sites for every iteration in [0..maxN). NOT($sampled(x)) matches
        // $sampled(NOT(x)) at the value level (IEEE 1800-2023 16.9.9);
        // purity is enforced uniformly via cloneTreePure inside sampledRefOrClone.
        AstVar* const hoistVarp = tryHoistSampled(exprp, flp, 2U * maxN);
        SvaStateVertex* currentp = entryVtxp;
        // Build minN match-wait chains to reach the first accept point.
        for (unsigned i = 0; i < minN; ++i) {
            SvaStateVertex* const waitVtxp = scopedCreateVertex();
            // Edge (not Link) for all iterations: IEEE expansion ##1 before each
            // match. A Link at i==0 was wrong -- it allowed same-cycle matching
            // and was discarded by Phase 2 (waitNode has a self-loop Edge).
            guardedEdge(currentp, waitVtxp, flp);
            AstNodeExpr* const waitCondp
                = new AstLogNot{flp, sampledRefOrClone(hoistVarp, exprp, flp)};
            guardedEdge(waitVtxp, waitVtxp, waitCondp, flp);
            SvaStateVertex* const matchVtxp = scopedCreateVertex();
            guardedLink(waitVtxp, matchVtxp, sampledRefOrClone(hoistVarp, exprp, flp), flp);
            currentp = matchVtxp;
        }
        if (!hasMax) {
            currentp->m_isUnbounded = true;  // [->N] waits unboundedly
            m_inUnboundedScope = true;
            return {currentp, nullptr, {}};
        }
        // [->M:N]: every match in [M..N] feeds a shared merge vertex so the
        // property can accept at any count in that range. Mirrors
        // buildConsRep's range fan-out.
        SvaStateVertex* const mergeVtxp = scopedCreateVertex();
        guardedLink(currentp, mergeVtxp, flp);  // accept at match_M
        for (unsigned i = minN; i < maxN; ++i) {
            SvaStateVertex* const waitVtxp = scopedCreateVertex();
            guardedEdge(currentp, waitVtxp, flp);
            AstNodeExpr* const waitCondp
                = new AstLogNot{flp, sampledRefOrClone(hoistVarp, exprp, flp)};
            guardedEdge(waitVtxp, waitVtxp, waitCondp, flp);
            SvaStateVertex* const matchVtxp = scopedCreateVertex();
            guardedLink(waitVtxp, matchVtxp, sampledRefOrClone(hoistVarp, exprp, flp), flp);
            guardedLink(matchVtxp, mergeVtxp, flp);  // accept at match_(i+1)
            currentp = matchVtxp;
        }
        mergeVtxp->m_isUnbounded = true;  // [->M:N] still has unbounded waits between matches
        m_inUnboundedScope = true;
        return {mergeVtxp, nullptr, {}};
    }

    void linkOrBranch(const BuildResult& branch, SvaStateVertex* mergeVtxp, FileLine* flp) {
        if (branch.finalCondp) {
            guardedLink(branch.termVertexp, mergeVtxp,
                        sampled(branch.finalCondp->cloneTreePure(false)), flp);
        } else {
            guardedLink(branch.termVertexp, mergeVtxp, flp);
        }
    }

    // Build merge vertex for SOr / LogOr: both branches feed into one vertex.
    BuildResult buildOrMerge(AstNodeExpr* lhsp, AstNodeExpr* rhsp, SvaStateVertex* entryVtxp,
                             FileLine* flp, bool isTopLevelStep) {
        // Constant truth of an operand: 1 true, 0 false, -1 not a two-state constant
        const auto constTruth = [](AstNodeExpr* exprp) -> int {
            bool strong = false;
            if (const AstPropAlways* const alwaysp = VN_CAST(exprp, PropAlways)) {
                strong = alwaysp->isStrong();
                exprp = alwaysp->propp();
            }
            const AstConst* const constp = VN_CAST(exprp, Const);
            if (!constp || constp->num().isFourState()) return -1;
            if (constp->num().isEqZero()) return 0;
            return strong ? -1 : 1;
        };
        const int lhsConst = constTruth(lhsp);
        const int rhsConst = constTruth(rhsp);
        if (m_isSeqEvent && (containsMultiCycleSva(lhsp) || containsMultiCycleSva(rhsp))) {
            warnEndpointUnsupported(flp, "a sequence operand of 'or'");
            return BuildResult::failWithError();
        }
        // Cover sequence must count a temporal sibling's later ends; do not fold to true.
        if (m_isCoverSeq
            && ((lhsConst == 1 && containsMultiCycleSva(rhsp))
                || (rhsConst == 1 && containsMultiCycleSva(lhsp)))) {
            flp->v3warn(COVERIGN,
                        "Ignoring unsupported: cover sequence with a sequence operand of 'or'");
            return BuildResult::failWithError();
        }
        if (lhsConst == 1) return buildExpr(lhsp, entryVtxp, isTopLevelStep);
        if (rhsConst == 1) return buildExpr(rhsp, entryVtxp, isTopLevelStep);
        if (lhsConst == 0) return buildExpr(rhsp, entryVtxp, isTopLevelStep);
        if (rhsConst == 0) return buildExpr(lhsp, entryVtxp, isTopLevelStep);

        const int lhsLen = fixedLength(lhsp);
        const int rhsLen = fixedLength(rhsp);
        const bool sameFixedEnd = lhsLen >= 0 && lhsLen == rhsLen;
        if (!sameFixedEnd) {
            // Diagnose an unsupported child before rejecting the OR (better source location).
            const BuildResult lhs = buildExpr(lhsp, entryVtxp);
            if (!lhs.valid() && lhs.errorEmitted) return BuildResult::failWithError();
            const BuildResult rhs = buildExpr(rhsp, entryVtxp);
            if (!rhs.valid() && rhs.errorEmitted) {
                cleanupProbeResult(lhs);
                return BuildResult::failWithError();
            }
            cleanupProbeResult(lhs);
            cleanupProbeResult(rhs);
            flp->v3warn(E_UNSUPPORTED,
                        "Unsupported: unequal/variable-end temporal 'or' cannot preserve "
                        "overlapping assertion attempt identity");
            return BuildResult::failWithError();
        }
        // A side-effecting operand would be evaluated twice (state + count channel); reject it.
        if (containsImpureExpr(lhsp) || containsImpureExpr(rhsp)) {
            flp->v3warn(E_UNSUPPORTED,
                        "Unsupported: impure expression in a temporal 'or' composite");
            return BuildResult::failWithError();
        }
        if (sameFixedEnd && mayEmitLocalReject(isTopLevelStep)
            && (mayRejectBeforeEnd(lhsp) || mayRejectBeforeEnd(rhsp))) {
            flp->v3warn(E_UNSUPPORTED,
                        "Unsupported: temporal 'or' endpoint deadline after an operand that can "
                        "reject earlier");
            return BuildResult::failWithError();
        }
        m_graph.m_hasOrMerge = true;
        const BuildResult lhs = buildExpr(lhsp, entryVtxp);
        const BuildResult rhs = buildExpr(rhsp, entryVtxp);
        if (!lhs.valid() || !rhs.valid()) {
            cleanupProbeResult(lhs);
            cleanupProbeResult(rhs);
            return BuildResult::fail(lhs.errorEmitted || rhs.errorEmitted);
        }
        // Reject cover-seq 'or' operands whose earlier endpoints bypass this merge.
        if (m_isCoverSeq && (lhs.termVertexp != entryVtxp || rhs.termVertexp != entryVtxp)) {
            cleanupProbeResult(lhs);
            cleanupProbeResult(rhs);
            warnEndpointUnsupported(flp, "a sequence operand of 'or'");
            return BuildResult::failWithError();
        }
        SvaStateVertex* const mergeVtxp = scopedCreateVertex();
        linkOrBranch(lhs, mergeVtxp, flp);
        linkOrBranch(rhs, mergeVtxp, flp);
        cleanupProbeResult(lhs);
        cleanupProbeResult(rhs);

        // One endpoint verdict: reject once only if neither branch reached the merge.
        if (sameFixedEnd && mayEmitLocalReject(isTopLevelStep)) {
            SvaStateVertex* const deadlineVtxp = addDelayChain(entryVtxp, lhsLen, flp);
            SvaStateVertex* const sinkVtxp = m_graph.createStateVertex();
            sinkVtxp->m_isRejectSink = true;
            SvaTransEdge* const rejectp = m_graph.addLink(deadlineVtxp, sinkVtxp);
            rejectp->m_rejectOnFail = true;
            rejectp->m_condVtxp = mergeVtxp;
        }

        return {mergeVtxp, nullptr, {}};
    }

    // A done latch retains the first temporal-AND endpoint until its sibling arrives.
    BuildResult buildAndCombiner(AstNodeExpr* lhsExprp, AstNodeExpr* rhsExprp,
                                 SvaStateVertex* entryVtxp, FileLine* flp) {
        const bool savedScope = m_inUnboundedScope;
        const BuildResult lhs = buildExpr(lhsExprp, entryVtxp);
        const bool lhsScope = m_inUnboundedScope;
        m_inUnboundedScope = savedScope;
        const BuildResult rhs = buildExpr(rhsExprp, entryVtxp);
        const bool rhsScope = m_inUnboundedScope;
        m_inUnboundedScope = savedScope || lhsScope || rhsScope;
        if (!lhs.valid() || !rhs.valid()) {
            cleanupProbeResult(lhs);
            cleanupProbeResult(rhs);
            return BuildResult::fail(lhs.errorEmitted || rhs.errorEmitted);
        }

        // Single-cycle operands: use boolean AND (done-latch would fire across cycles).
        // If both operands stayed at entry, they must be boolean leaves which
        // buildExpr returns with finalCondp=nodep (non-null).
        if (lhs.termVertexp == entryVtxp && rhs.termVertexp == entryVtxp) {
            UASSERT_OBJ(lhs.finalCondp && rhs.finalCondp, lhsExprp,
                        "Single-cycle SAnd operands must have finalCondp");
            AstNodeExpr* const condp = new AstLogAnd{flp, lhs.finalCondp->cloneTreePure(false),
                                                     rhs.finalCondp->cloneTreePure(false)};
            cleanupProbeResult(lhs);
            cleanupProbeResult(rhs);
            return {entryVtxp, condp, {}};
        }
        // Range-delay mid-window sources in either sub-branch would need
        // to be folded into the latch's match-now signal, which the
        // current combiner does not support.
        if (!lhs.midSources.empty() || !rhs.midSources.empty()) {
            cleanupProbeResult(lhs);
            cleanupProbeResult(rhs);
            UASSERT_OBJ(!m_isSeqEvent, flp, "Seq events reject variable 'and' operands first");
            flp->v3warn(E_UNSUPPORTED,
                        "Unsupported: ranged cycle delay in an operand of property 'and'");
            return BuildResult::failWithError();
        }
        SvaStateVertex* const combVtxp = scopedCreateVertex();
        combVtxp->m_isAndCombiner = true;
        combVtxp->m_andNeedsDoneLatches = true;
        combVtxp->m_andLhsTermp = lhs.termVertexp;
        combVtxp->m_andRhsTermp = rhs.termVertexp;
        if (lhs.finalCondp) combVtxp->m_andLhsCondp = lhs.finalCondp->cloneTreePure(false);
        if (rhs.finalCondp) combVtxp->m_andRhsCondp = rhs.finalCondp->cloneTreePure(false);
        if (lhs.termVertexp->m_isUnbounded || rhs.termVertexp->m_isUnbounded) {
            combVtxp->m_isUnbounded = true;
        }
        if (!combVtxp->m_isUnbounded) {
            const bool lhsMultiCycle = lhs.termVertexp != entryVtxp;
            const bool rhsMultiCycle = rhs.termVertexp != entryVtxp;
            const bool needSink
                = (lhs.finalCondp && lhsMultiCycle) || (rhs.finalCondp && rhsMultiCycle);
            if (needSink) {
                SvaStateVertex* const sinkVtxp = m_graph.createStateVertex();
                sinkVtxp->m_isRejectSink = true;
                if (lhs.finalCondp && lhsMultiCycle && !lhs.termVertexp->m_isUnbounded) {
                    SvaTransEdge* const ep = m_graph.addLink(
                        lhs.termVertexp, sinkVtxp, sampled(lhs.finalCondp->cloneTreePure(false)));
                    ep->m_rejectOnFail = true;
                }
                if (rhs.finalCondp && rhsMultiCycle && !rhs.termVertexp->m_isUnbounded) {
                    SvaTransEdge* const ep = m_graph.addLink(
                        rhs.termVertexp, sinkVtxp, sampled(rhs.finalCondp->cloneTreePure(false)));
                    ep->m_rejectOnFail = true;
                }
            }
        }
        cleanupProbeResult(lhs);
        cleanupProbeResult(rhs);
        return {combVtxp, nullptr, {}};
    }

    // Equal-length intersect operands combine terminal matches without persistent state.
    BuildResult buildSameEndIntersectCombiner(AstNodeExpr* lhsExprp, AstNodeExpr* rhsExprp,
                                              SvaStateVertex* entryVtxp, FileLine* flp,
                                              int sameEndLength, bool isTopLevelStep = false) {
        UASSERT_OBJ(sameEndLength >= 0, lhsExprp,
                    "Same-end intersect combiner needs a fixed endpoint");
        if (mayEmitLocalReject(isTopLevelStep)
            && (mayRejectBeforeEnd(lhsExprp) || mayRejectBeforeEnd(rhsExprp))) {
            flp->v3warn(
                E_UNSUPPORTED,
                "Unsupported: intersect/within endpoint deadline after an operand that can "
                "reject earlier");
            return BuildResult::failWithError();
        }
        m_graph.m_hasAndCombiner = true;
        // Snapshot-restore scope so LHS liveness does not leak into RHS.
        const bool savedScope = m_inUnboundedScope;
        const BuildResult lhs = buildExpr(lhsExprp, entryVtxp);
        const bool lhsScope = m_inUnboundedScope;
        m_inUnboundedScope = savedScope;
        const BuildResult rhs = buildExpr(rhsExprp, entryVtxp);
        const bool rhsScope = m_inUnboundedScope;
        m_inUnboundedScope = savedScope || lhsScope || rhsScope;
        if (!lhs.valid() || !rhs.valid()) {
            cleanupProbeResult(lhs);
            cleanupProbeResult(rhs);
            return BuildResult::fail(lhs.errorEmitted || rhs.errorEmitted);
        }
        // Both-boolean operands have fixed length 0 and never route here (conjoined instead).
        UASSERT_OBJ(lhs.termVertexp != entryVtxp || rhs.termVertexp != entryVtxp, lhsExprp,
                    "Intersect combiner requires a non-fixed operand");
        // Fixed-length operands (or-merge, bounded always, throughout of those) have no
        // mid-window endpoints.
        UASSERT_OBJ(lhs.midSources.empty() && rhs.midSources.empty(), lhsExprp,
                    "Same-end intersect operands cannot have mid-window sources");
        SvaStateVertex* const combVtxp = scopedCreateVertex();
        combVtxp->m_isAndCombiner = true;
        combVtxp->m_andLhsTermp = lhs.termVertexp;
        combVtxp->m_andRhsTermp = rhs.termVertexp;
        if (lhs.finalCondp) combVtxp->m_andLhsCondp = lhs.finalCondp->cloneTreePure(false);
        if (rhs.finalCondp) combVtxp->m_andRhsCondp = rhs.finalCondp->cloneTreePure(false);
        cleanupProbeResult(lhs);
        cleanupProbeResult(rhs);
        // One endpoint verdict: reject once if the same-end combiner did not match.
        if (mayEmitLocalReject(isTopLevelStep)) {
            SvaStateVertex* const deadlineVtxp = addDelayChain(entryVtxp, sameEndLength, flp);
            SvaStateVertex* const sinkVtxp = m_graph.createStateVertex();
            sinkVtxp->m_isRejectSink = true;
            SvaTransEdge* const rejectp = m_graph.addLink(deadlineVtxp, sinkVtxp);
            rejectp->m_rejectOnFail = true;
            rejectp->m_condVtxp = combVtxp;
        }
        return {combVtxp, nullptr, {}};
    }

    // Lower fixed-length `seq1 within seq2` by aligning each legal seq1 placement.
    BuildResult buildSWithin(AstSWithin* nodep, SvaStateVertex* entryVtxp,
                             bool isTopLevelStep = false) {
        const int innerLen = fixedLength(nodep->lhsp());
        const int outerLen = fixedLength(nodep->rhsp());
        if (innerLen < 0 || outerLen < 0) {
            nodep->v3warn(E_UNSUPPORTED, "Unsupported: within with ranged cycle-delay operand");
            return BuildResult::failWithError();
        }
        if (innerLen > outerLen) {
            return buildNeverMatchIntersect(
                nodep, entryVtxp, isTopLevelStep,
                "the inner sequence is longer than the outer sequence");
        }
        FileLine* const flp = nodep->fileline();
        const int slack = outerLen - innerLen;
        AstNodeExpr* innerOrp = nullptr;
        for (int i = 0; i <= slack; ++i) {
            const int postPad = slack - i;
            AstNodeExpr* branchp = nodep->lhsp()->cloneTreePure(false);
            if (i > 0) {
                AstConst* const prePadp = new AstConst{flp, AstConst::BitTrue{}};
                AstDelay* const delayp
                    = new AstDelay{flp, new AstConst{flp, static_cast<uint32_t>(i)}, true};
                AstSExpr* const wrapped = new AstSExpr{flp, prePadp, delayp, branchp};
                wrapped->dtypeSetBit();
                branchp = wrapped;
            }
            if (postPad > 0) {
                AstConst* const postTruep = new AstConst{flp, AstConst::BitTrue{}};
                AstDelay* const delayp
                    = new AstDelay{flp, new AstConst{flp, static_cast<uint32_t>(postPad)}, true};
                AstSExpr* const wrapped = new AstSExpr{flp, branchp, delayp, postTruep};
                wrapped->dtypeSetBit();
                branchp = wrapped;
            }
            innerOrp = innerOrp ? static_cast<AstNodeExpr*>(new AstSOr{flp, innerOrp, branchp})
                                : branchp;
        }
        AstNodeExpr* const outerClonep = nodep->rhsp()->cloneTreePure(false);
        AstNodeExpr* const combinedp = new AstSIntersect{flp, innerOrp, outerClonep};
        BuildResult result = buildExpr(combinedp, entryVtxp, isTopLevelStep);
        VL_DO_DANGLING(combinedp->deleteTree(), combinedp);
        // A conjoined boolean intersect returns a freshly-allocated finalCondp with no
        // parent; callers clone-and-discard finalCondp, so anchor it in the graph via an edge.
        if (result.valid() && result.finalCondp && !result.finalCondp->backp()) {
            SvaStateVertex* const wrapVtxp = scopedCreateVertex();
            guardedLink(result.termVertexp, wrapVtxp, sampled(result.finalCondp), flp);
            result = {wrapVtxp, nullptr, result.midSources};
        }
        return result;
    }

    static bool reserveFixedTraceSites(AstNode* nodep, uint64_t& sites, uint64_t increment) {
        const uint64_t limit = static_cast<uint64_t>(v3Global.opt.assertUnrollLimit());
        if (sites <= limit && increment <= limit - sites) {
            sites += increment;
            return true;
        }
        nodep->v3error("Concurrent assertion fixed-trace expansion exceeds "
                       "--assert-unroll-limit ("
                       << limit << "); raise '--assert-unroll-limit' to compile");
        return false;
    }

    // Bound fixed-sequence expansion and reject leaves whose effects would be duplicated.
    static bool validateFixedTrace(AstNodeExpr* nodep, uint64_t& sites) {
        if (AstSExpr* const sexprp = VN_CAST(nodep, SExpr)) {
            if (AstNodeExpr* const prep = sexprp->preExprp()) {
                if (!validateFixedTrace(prep, sites)) return false;
            }
            return validateFixedTrace(sexprp->exprp(), sites);
        }
        if (AstSConsRep* const repp = VN_CAST(nodep, SConsRep)) {
            const unsigned minN = getConstUInt(repp->countp());
            if (containsImpureExpr(repp->exprp())) {
                repp->v3warn(
                    E_UNSUPPORTED,
                    "Unsupported: impure expression in a flattened consecutive repetition");
                return false;
            }
            return reserveFixedTraceSites(repp, sites, static_cast<uint64_t>(minN));
        }
        if (AstSAnd* const andp = VN_CAST(nodep, SAnd)) {
            return validateFixedTrace(andp->lhsp(), sites)
                   && validateFixedTrace(andp->rhsp(), sites);
        }
        if (AstSThroughout* const throughoutp = VN_CAST(nodep, SThroughout)) {
            const int rhsLen = fixedLength(throughoutp->rhsp());
            if (rhsLen < 0) return true;
            if (containsImpureExpr(throughoutp->lhsp())) {
                throughoutp->v3warn(
                    E_UNSUPPORTED,
                    "Unsupported: impure guard in a flattened throughout composite");
                return false;
            }
            if (!reserveFixedTraceSites(throughoutp, sites, static_cast<uint64_t>(rhsLen) + 1)) {
                return false;
            }
            return validateFixedTrace(throughoutp->rhsp(), sites);
        }
        if (nodep->exists([](const AstNodeExpr* ep) { return ep->isMultiCycleSva(); }))
            return true;
        if (containsImpureExpr(nodep)) {
            nodep->v3warn(E_UNSUPPORTED,
                          "Unsupported: impure expression in a flattened temporal composite");
            return false;
        }
        return reserveFixedTraceSites(nodep, sites, 1);
    }

    // Collect boolean leaf checks of a fixed-length match, keyed by clock offset.
    static bool flattenFixedSeq(AstNodeExpr* nodep, int baseOffset,
                                std::map<int, std::vector<AstNodeExpr*>>& out) {
        if (AstSExpr* const sexprp = VN_CAST(nodep, SExpr)) {
            AstDelay* const delayp = VN_CAST(sexprp->delayp(), Delay);
            if (!delayp || !delayp->isCycleDelay() || delayp->isUnbounded()) return false;
            const unsigned delayCycles = getConstUInt(delayp->lhsp());
            if (delayp->isRangeDelay() && getConstUInt(delayp->rhsp()) != delayCycles)
                return false;
            int preLen = 0;
            if (AstNodeExpr* const prep = sexprp->preExprp()) {
                if (!flattenFixedSeq(prep, baseOffset, out)) return false;
                preLen = fixedLength(prep);
                if (preLen < 0) return false;
            }
            return flattenFixedSeq(sexprp->exprp(), baseOffset + preLen + delayCycles, out);
        }
        if (AstSConsRep* const repp = VN_CAST(nodep, SConsRep)) {
            if (repp->unbounded() || repp->exprp()->isMultiCycleSva()) return false;
            const unsigned minN = getConstUInt(repp->countp());
            if (repp->maxCountp() && getConstUInt(repp->maxCountp()) != minN) return false;
            for (unsigned i = 0; i < minN; ++i) {
                if (!flattenFixedSeq(repp->exprp(), baseOffset + static_cast<int>(i), out)) {
                    return false;
                }
            }
            return true;
        }
        if (AstSAnd* const andp = VN_CAST(nodep, SAnd)) {
            return flattenFixedSeq(andp->lhsp(), baseOffset, out)
                   && flattenFixedSeq(andp->rhsp(), baseOffset, out);
        }
        if (AstSThroughout* const throughoutp = VN_CAST(nodep, SThroughout)) {
            const int rhsLen = fixedLength(throughoutp->rhsp());
            if (rhsLen < 0 || !flattenFixedSeq(throughoutp->rhsp(), baseOffset, out)) return false;
            // IEEE 16.9.9 covers the start tick, the end tick, and every gap tick between.
            for (int offset = 0; offset <= rhsLen; ++offset) {
                out[baseOffset + offset].push_back(throughoutp->lhsp());
            }
            return true;
        }
        if (nodep->exists([](const AstNodeExpr* ep) { return ep->isMultiCycleSva(); }))
            return false;
        out[baseOffset].push_back(nodep);
        return true;
    }

    // Conjoin two fixed sequences into one, AND-ing leaf checks at each offset.
    static AstNodeExpr* conjoinFixedSeqs(AstNodeExpr* lhsp, AstNodeExpr* rhsp, FileLine* flp) {
        std::map<int, std::vector<AstNodeExpr*>> checks;
        if (!flattenFixedSeq(lhsp, 0, checks) || !flattenFixedSeq(rhsp, 0, checks)) return nullptr;
        if (checks.empty()) return nullptr;
        AstNodeExpr* resultp = nullptr;
        int prevOffset = 0;
        for (const auto& offsetChecks : checks) {
            const int offset = offsetChecks.first;
            AstNodeExpr* condp = nullptr;
            for (AstNodeExpr* const leafp : offsetChecks.second) {
                AstNodeExpr* const clonep = leafp->cloneTreePure(false);
                if (!condp) {
                    condp = clonep;
                } else {
                    condp = new AstLogAnd{flp, condp, clonep};
                    condp->dtypeSetBit();
                }
            }
            if (!resultp) {
                if (offset > 0) {
                    AstDelay* const delayp = new AstDelay{
                        flp, new AstConst{flp, static_cast<uint32_t>(offset)}, /*isCycle=*/true};
                    resultp
                        = new AstSExpr{flp, new AstConst{flp, AstConst::BitTrue{}}, delayp, condp};
                    resultp->dtypeSetBit();
                } else {
                    resultp = condp;
                }
            } else {
                AstDelay* const delayp = new AstDelay{
                    flp, new AstConst{flp, static_cast<uint32_t>(offset - prevOffset)},
                    /*isCycle=*/true};
                resultp = new AstSExpr{flp, resultp, delayp, condp};
                resultp->dtypeSetBit();
            }
            prevOffset = offset;
        }
        return resultp;
    }

    static void collectPropertyControlBranches(AstNodeExpr* nodep,
                                               std::vector<AstImplication*>& branches) {
        if (AstSAnd* const andp = VN_CAST(nodep, SAnd)) {
            UASSERT_OBJ(andp->propertyControl(), andp,
                        "Property-control branch tree lost parser provenance");
            collectPropertyControlBranches(andp->lhsp(), branches);
            collectPropertyControlBranches(andp->rhsp(), branches);
            return;
        }
        branches.push_back(VN_AS(nodep, Implication));
    }

    // Property-control branches retain independent state, rejects, and failure depths.
    BuildResult buildPropertyControlAnd(AstSAnd* nodep, SvaStateVertex* entryVtxp,
                                        bool isTopLevelStep) {
        if (m_inUnboundedScope) {
            nodep->v3warn(E_UNSUPPORTED,
                          "Unsupported: property if/case inside a variable-end temporal window");
            return BuildResult::failWithError();
        }

        std::vector<AstImplication*> branches;
        collectPropertyControlBranches(nodep, branches);
        const auto impureIt
            = std::find_if(branches.begin(), branches.end(),
                           [](AstImplication* bp) { return containsImpureExpr(bp->lhsp()); });
        if (impureIt != branches.end()) {
            (*impureIt)->lhsp()->v3warn(
                E_UNSUPPORTED,
                "Unsupported: impure property if/case selector cannot be sampled once");
            return BuildResult::failWithError();
        }

        SvaStateVertex* const mergeVtxp = scopedCreateVertex();
        m_graph.m_hasOrMerge = true;
        for (AstImplication* const branchp : branches) {
            const bool savedScope = m_inUnboundedScope;
            m_inUnboundedScope = false;
            BuildResult branch = buildImplicationEdges(
                branchp->lhsp(), branchp->rhsp(), entryVtxp, /*isOverlapped=*/true,
                /*isFollowedBy=*/false, branchp->lhsp(), branchp->fileline());
            m_inUnboundedScope = savedScope;
            if (!branch.valid()) return BuildResult::fail(branch.errorEmitted);

            const auto addSuccess = [&](SvaStateVertex* sourcep, bool rejectOnMiss) {
                AstNodeExpr* condp = branch.finalCondp
                                         ? sampled(branch.finalCondp->cloneTreePure(false))
                                         : nullptr;
                SvaTransEdge* const edgep
                    = guardedLink(sourcep, mergeVtxp, condp, branchp->fileline());
                if (rejectOnMiss && condp && mayEmitLocalReject(isTopLevelStep)) {
                    edgep->m_rejectOnFail = true;
                }
            };
            for (SvaStateVertex* const sourcep : branch.midSources) {
                addSuccess(sourcep, /*rejectOnMiss=*/false);
            }
            addSuccess(branch.termVertexp,
                       /*rejectOnMiss=*/!branch.termVertexp->m_isUnbounded);
            if (branch.finalCondp && !branch.finalCondp->backp()) branch.finalCondp->deleteTree();
            branch.finalCondp = nullptr;
        }
        return {mergeVtxp, nullptr, {}};
    }

    BuildResult buildSAnd(AstSAnd* nodep, SvaStateVertex* entryVtxp, bool isTopLevelStep) {
        if (isPropertyControlConjunction(nodep)) {
            return buildPropertyControlAnd(nodep, entryVtxp, isTopLevelStep);
        }
        const int lhsLen = fixedLength(nodep->lhsp());
        const int rhsLen = fixedLength(nodep->rhsp());
        const bool hasAbort = nodep->exists([](const AstAbortOn*) { return true; });
        if (lhsLen >= 0 && rhsLen >= 0 && !hasAbort) {
            uint64_t traceSites = 0;
            if (!validateFixedTrace(nodep->lhsp(), traceSites)
                || !validateFixedTrace(nodep->rhsp(), traceSites)) {
                return BuildResult::failWithError();
            }
            if (AstNodeExpr* const conjp
                = conjoinFixedSeqs(nodep->lhsp(), nodep->rhsp(), nodep->fileline())) {
                return buildFromLoweringTree(conjp, entryVtxp, isTopLevelStep);
            }
            nodep->v3warn(E_UNSUPPORTED,
                          "Unsupported: bounded temporal 'and' operand cannot be represented as a "
                          "single fixed match trace");
            return BuildResult::failWithError();
        }
        if (!m_needsRejectVerdict) {
            if (m_isSeqEvent) {
                warnEndpointUnsupported(nodep->fileline(), "a variable/unbounded temporal 'and'");
            } else {
                nodep->v3warn(E_UNSUPPORTED,
                              "Unsupported: variable/unbounded temporal 'and' cannot preserve "
                              "overlapping assertion attempt identity");
            }
            return BuildResult::failWithError();
        }
        return buildAndCombiner(nodep->lhsp(), nodep->rhsp(), entryVtxp, nodep->fileline());
    }

    // A simple ranged sequence `start ##[m:n] end` (start optional).
    struct SimpleRanged final {
        bool ok = false;
        AstNodeExpr* startp = nullptr;  // may be null (absent start)
        AstNodeExpr* endp = nullptr;
    };
    static SimpleRanged asSimpleRanged(AstNodeExpr* nodep) {
        AstSExpr* const sexprp = VN_CAST(nodep, SExpr);
        if (!sexprp) return {};
        AstDelay* const delayp = VN_CAST(sexprp->delayp(), Delay);
        if (!delayp || !delayp->isCycleDelay() || !delayp->isRangeDelay() || delayp->isUnbounded())
            return {};
        if (getConstUInt(delayp->lhsp()) == getConstUInt(delayp->rhsp())) return {};
        AstNodeExpr* const prep = sexprp->preExprp();
        if (prep && fixedLength(prep) != 0) return {};
        if (fixedLength(sexprp->exprp()) != 0) return {};
        return {true, prep, sexprp->exprp()};
    }

    // Build the NFA for a synthesized lowering tree, cloning finalCondp before freeing it.
    BuildResult buildFromLoweringTree(AstNodeExpr* treep, SvaStateVertex* entryVtxp,
                                      bool isTopLevelStep) {
        BuildResult result = buildExpr(treep, entryVtxp, isTopLevelStep);
        if (result.valid() && result.finalCondp) {
            result.finalCondp = result.finalCondp->cloneTreePure(false);
        }
        VL_DO_DANGLING(treep->deleteTree(), treep);
        return result;
    }

    // No common length: the intersect never matches (legal, 16.9.6) -> constant false.
    BuildResult buildNeverMatchIntersect(AstNodeExpr* nodep, SvaStateVertex* entryVtxp,
                                         bool isTopLevelStep, const char* reason) {
        nodep->v3warn(NEVERMATCH, "Sequence can never match because " << reason << ".");
        AstNodeExpr* const falsep = new AstConst{nodep->fileline(), AstConst::BitFalse{}};
        return buildFromLoweringTree(falsep, entryVtxp, isTopLevelStep);
    }

    // Lower supported variable-length intersect forms under IEEE 1800-2023 16.9.6.
    BuildResult buildVarLenIntersect(AstSIntersect* nodep, SvaStateVertex* entryVtxp,
                                     bool isTopLevelStep) {
        const std::pair<int, int> lhsRange = lengthRange(nodep->lhsp());
        const std::pair<int, int> rhsRange = lengthRange(nodep->rhsp());
        if (lhsRange.first < 0 || rhsRange.first < 0) {
            nodep->v3warn(E_UNSUPPORTED,
                          "Unsupported: intersect with this variable-length operand");
            return BuildResult::failWithError();
        }
        const int lo = std::max(lhsRange.first, rhsRange.first);
        const int hi = std::min(lhsRange.second, rhsRange.second);
        if (lo > hi) {
            // Disjoint length ranges share no common length -> never matches.
            return buildNeverMatchIntersect(nodep, entryVtxp, isTopLevelStep,
                                            "intersect operands have no common length");
        }
        FileLine* const flp = nodep->fileline();
        if (lo == hi) {
            // Pinning a ranged operand to one length supports only plain boolean traces.
            if (nodep->exists([](const AstSThroughout*) { return true; })) {
                nodep->v3warn(E_UNSUPPORTED,
                              "Unsupported: intersect operand is not a plain boolean sequence");
                return BuildResult::failWithError();
            }
            AstNodeExpr* const lp = realizeAtLength(nodep->lhsp(), lo, lhsRange.first);
            AstNodeExpr* const rp = realizeAtLength(nodep->rhsp(), lo, rhsRange.first);
            AstNodeExpr* const conjp = conjoinFixedSeqs(lp, rp, flp);
            VL_DO_DANGLING(lp->deleteTree(), lp);
            VL_DO_DANGLING(rp->deleteTree(), rp);
            if (!conjp) {
                nodep->v3warn(E_UNSUPPORTED,
                              "Unsupported: intersect operand is not a plain boolean sequence");
                return BuildResult::failWithError();
            }
            return buildFromLoweringTree(conjp, entryVtxp, isTopLevelStep);
        }
        const SimpleRanged sl = asSimpleRanged(nodep->lhsp());
        const SimpleRanged sr = asSimpleRanged(nodep->rhsp());
        if (!sl.ok || !sr.ok) {
            nodep->v3warn(E_UNSUPPORTED,
                          "Unsupported: intersect of two sequences that each vary in length over a"
                          " range with internal structure");
            return BuildResult::failWithError();
        }
        const auto andBool = [&](AstNodeExpr* ap, AstNodeExpr* bp) -> AstNodeExpr* {
            AstNodeExpr* const aClonep
                = ap ? ap->cloneTreePure(false) : new AstConst{flp, AstConst::BitTrue{}};
            AstNodeExpr* const bClonep
                = bp ? bp->cloneTreePure(false) : new AstConst{flp, AstConst::BitTrue{}};
            AstLogAnd* const andp = new AstLogAnd{flp, aClonep, bClonep};
            andp->dtypeSetBit();
            return andp;
        };
        AstDelay* const delayp = new AstDelay{flp, new AstConst{flp, static_cast<uint32_t>(lo)},
                                              /*isCycle=*/true};
        delayp->rhsp(new AstConst{flp, static_cast<uint32_t>(hi)});
        AstSExpr* const reducedp
            = new AstSExpr{flp, andBool(sl.startp, sr.startp), delayp, andBool(sl.endp, sr.endp)};
        reducedp->dtypeSetBit();
        return buildFromLoweringTree(reducedp, entryVtxp, isTopLevelStep);
    }

    BuildResult buildThroughout(AstSThroughout* nodep, SvaStateVertex* entryVtxp,
                                bool isTopLevelStep = false) {
        // Mark entryVtxp so "cond false at tick 0" is detected as throughout-drop.
        entryVtxp->m_throughoutConds.push_back(nodep->lhsp()->cloneTreePure(false));
        m_temporalGuardStack.push_back(nodep->lhsp());
        BuildResult result = buildExpr(nodep->rhsp(), entryVtxp, isTopLevelStep);
        if (result.valid()) {
            // Fold active throughout guards into the boolean terminal tick too.
            AstNodeExpr* finalp = result.finalCondp;
            if (finalp && finalp->backp()) finalp = finalp->cloneTreePure(false);
            result.finalCondp = throughoutCond(finalp, nodep->fileline());
        }
        m_temporalGuardStack.pop_back();
        return result;
    }

    // until / until_with (weak forms only) per IEEE 1800-2023 16.12.12.
    // Topology: combinational wait vertex with self-feeding state register.
    //   entry  --link[T]--> waitC
    //   waitR  --link[T]--> waitC                          (back-loop)
    //   waitC  --edge[##1, sampled(p) && !sampled(q)]--> waitR  (continue)
    //   waitC  --link[REQUIRE, rejectOnFail]--> sink            (per-cycle fail)
    //   waitC  --link[T]--> match  (added by wireMatchAndMidSources;
    //                               accept condition rides via finalCondp)
    // waitC is m_isUnbounded so the terminal-match link contributes only to
    // terminalActive, not to rejectBase (which would otherwise spuriously fire
    // every cycle q is false). Per-cycle reject comes from the explicit
    // rejectOnFail link to the sink vertex.
    //
    // Weak non-overlapping (p until q):
    //   REQUIRE = sampled(p) || sampled(q)   accept = sampled(q)
    // Weak overlapping (p until_with q):
    //   REQUIRE = sampled(p)                 accept = sampled(p) && sampled(q)
    BuildResult buildUntil(AstUntil* nodep, SvaStateVertex* entryVtxp, bool isTopLevelStep) {
        FileLine* const flp = nodep->fileline();
        if (!isTopLevelStep) {
            nodep->v3warn(E_UNSUPPORTED, "Unsupported: '" << nodep->verilogKwd()
                                                          << "' in complex property expression");
            return BuildResult::failWithError();
        }
        if (nodep->isStrong()) {
            nodep->v3warn(E_UNSUPPORTED, "Unsupported: s_until"
                                             << (nodep->isOverlapping() ? "_with" : "")
                                             << " (in property expression)");
            return BuildResult::failWithError();
        }
        AstNodeExpr* const lhsBitp = nodep->lhsp();
        AstNodeExpr* const rhsBitp = nodep->rhsp();
        if (containsMultiCycleSva(lhsBitp) || containsMultiCycleSva(rhsBitp)) {
            nodep->v3warn(E_UNSUPPORTED, "Unsupported: '" << nodep->verilogKwd()
                                                          << "' in complex property expression");
            return BuildResult::failWithError();
        }
        if (m_inUnboundedScope) {
            nodep->v3warn(E_UNSUPPORTED, "Unsupported: '"
                                             << nodep->verilogKwd()
                                             << "' inside a variable-length property window");
            return BuildResult::failWithError();
        }

        const bool ov = nodep->isOverlapping();
        // p hoist count: continue, require (ov: 1 use; nov: 1 use). At least 2 uses.
        AstVar* const pHoistp = tryHoistSampled(lhsBitp, flp, 2);
        // q hoist count: continue (1) + require nov (1) = 2; ov: continue only (1).
        AstVar* const qHoistp = ov ? nullptr : tryHoistSampled(rhsBitp, flp, 2);

        SvaStateVertex* const waitCp = scopedCreateVertex();
        SvaStateVertex* const waitRp = scopedCreateVertex();
        waitCp->m_isUnbounded = true;

        // Entry and back-loop Links carry no condition; throughout-folding still applies.
        guardedLink(entryVtxp, waitCp, flp);
        guardedLink(waitRp, waitCp, flp);

        // Continue clocked edge: p && !q advances to next-cycle wait.
        AstNodeExpr* const contCondp
            = new AstLogAnd{flp, sampledRefOrClone(pHoistp, lhsBitp, flp),
                            new AstLogNot{flp, sampledRefOrClone(qHoistp, rhsBitp, flp)}};
        guardedEdge(waitCp, waitRp, contCondp, flp);

        // Reject sink: fires when require-condition is false.
        SvaStateVertex* const sinkVtxp = m_graph.createStateVertex();
        sinkVtxp->m_isRejectSink = true;
        AstNodeExpr* requireCondp;
        if (ov) {
            requireCondp = sampledRefOrClone(pHoistp, lhsBitp, flp);
        } else {
            requireCondp = new AstLogOr{flp, sampledRefOrClone(pHoistp, lhsBitp, flp),
                                        sampledRefOrClone(qHoistp, rhsBitp, flp)};
        }
        SvaTransEdge* const rejEdgep = m_graph.addLink(waitCp, sinkVtxp, requireCondp);
        if (mayEmitLocalReject(isTopLevelStep)) rejEdgep->m_rejectOnFail = true;

        // Accept condition rides via finalCondp; assembleResult $sampled-wraps it.
        AstNodeExpr* acceptCondp;
        if (ov) {
            acceptCondp
                = new AstLogAnd{flp, lhsBitp->cloneTreePure(false), rhsBitp->cloneTreePure(false)};
        } else {
            acceptCondp = rhsBitp->cloneTreePure(false);
        }
        return {waitCp, acceptCondp, {}};
    }

    // IEEE 1800-2023 16.12.14 property abort operators. Sync and async share
    // the same NFA encoding: AstSampled already gives matured values at every
    // maturing clocking event, and async firing "between clocks" is not
    // observable in a cycle-based model. VAbortKind selects accept vs reject
    // verdict (sync vs async only changes the user-visible spelling).

    // Build `condp && !outer_1 && !outer_2 ...` (unsampled).
    AstNodeExpr* abortFireExpr(AstNodeExpr* condp, FileLine* flp) {
        AstNodeExpr* resultp = condp->cloneTreePure(false);
        for (AstNodeExpr* const op : m_outerAbortStack)
            resultp = new AstLogAnd{flp, resultp, new AstLogNot{flp, op->cloneTreePure(false)}};
        return resultp;
    }

    // True when a same-tick Link chain already accounts the attempt: a
    // required-step Link covers both outcomes; followed-by pairs both edges.
    static bool chainAccountsSource(const SvaStateVertex* srcp,
                                    const std::unordered_set<const V3GraphEdge*>& preEdges) {
        bool plainNonSink = false;
        bool markedSink = false;
        for (const V3GraphEdge& edger : srcp->outEdges()) {
            if (preEdges.count(&edger)) continue;
            const SvaTransEdge& tedger = static_cast<const SvaTransEdge&>(edger);
            if (tedger.m_consumesCycle) continue;
            const bool sink = static_cast<const SvaStateVertex*>(tedger.toVtxp())->m_isRejectSink;
            if (tedger.m_rejectOnFail) {
                if (!sink) return true;
                markedSink = true;
            } else if (!sink) {
                plainNonSink = true;
            }
        }
        return plainNonSink && markedSink;
    }

    // Reject edge: fires when the source is live and the abort samples true.
    void addAbortRejectEdge(SvaStateVertex* srcp, SvaStateVertex* sinkp, AstNodeExpr* condp,
                            FileLine* flp) {
        AstNodeExpr* const notFirep = new AstLogNot{flp, sampled(abortFireExpr(condp, flp))};
        m_graph.addLink(srcp, sinkp, notFirep)->m_rejectOnFail = true;
        return;
    }

    // On the fire tick: kill body threads; accept kinds also forgive step misses.
    void gateBodyEdgesOnAbort(const std::unordered_set<const V3GraphEdge*>& preEdges,
                              AstNodeExpr* condp, VAbortKind kind, FileLine* flp) {
        for (V3GraphVertex& vtxr : m_graph.m_graph.vertices()) {
            for (V3GraphEdge& edger : vtxr.outEdges()) {
                if (preEdges.count(&edger)) continue;
                SvaTransEdge* const tedgep = static_cast<SvaTransEdge*>(&edger);
                if (tedgep->m_rejectOnFail) {
                    if (!kind.isAccept()) continue;
                    AstNodeExpr* const firep = sampled(abortFireExpr(condp, flp));
                    tedgep->m_condp
                        = tedgep->m_condp ? new AstLogOr{flp, tedgep->m_condp, firep} : firep;
                } else if (tedgep->m_consumesCycle) {
                    AstNodeExpr* const notFirep
                        = new AstLogNot{flp, sampled(abortFireExpr(condp, flp))};
                    tedgep->m_condp = tedgep->m_condp
                                          ? new AstLogAnd{flp, tedgep->m_condp, notFirep}
                                          : notFirep;
                }
            }
        }
    }

    BuildResult buildAbortOn(AstNodeExpr* condp, AstNodeExpr* bodyp, SvaStateVertex* entryVtxp,
                             VAbortKind kind, FileLine* flp, bool isTopLevelStep) {
        // Snapshot pre-body vertices/edges so post-build diff yields the body's sub-NFA.
        std::unordered_set<const V3GraphVertex*> preExisting;
        std::unordered_set<const V3GraphEdge*> preEdges;
        for (V3GraphVertex& vtxr : m_graph.m_graph.vertices()) {
            preExisting.insert(&vtxr);
            for (V3GraphEdge& edger : vtxr.outEdges()) preEdges.insert(&edger);
        }

        m_outerAbortStack.push_back(condp);
        const BuildResult bodyResult = buildExpr(bodyp, entryVtxp, isTopLevelStep);
        m_outerAbortStack.pop_back();
        if (!bodyResult.valid()) return bodyResult;

        gateBodyEdgesOnAbort(preEdges, condp, kind, flp);

        // Live-thread sources for the abort edge: entry + new body vertices,
        // minus reject sinks (they carry reject fuel, not live-thread fuel).
        std::vector<SvaStateVertex*> abortSources;
        abortSources.push_back(entryVtxp);
        for (V3GraphVertex& vtxr : m_graph.m_graph.vertices()) {
            if (preExisting.count(&vtxr)) continue;
            auto* const sp = static_cast<SvaStateVertex*>(&vtxr);
            if (sp->m_delayRingSize) {
                AstNodeExpr* const firep = abortFireExpr(condp, flp);
                sp->m_abortClearp
                    = sp->m_abortClearp ? new AstLogOr{flp, sp->m_abortClearp, firep} : firep;
            }
            if (sp->m_isRejectSink) continue;
            abortSources.push_back(sp);
        }

        auto sampledAbortFire = [&]() -> AstNodeExpr* {
            AstNodeExpr* const expr = abortFireExpr(condp, flp);
            return sampled(expr);
        };

        if (kind.isAccept()) {
            // Match-only sink fed by $sampled(abort-fire) from every live source;
            // registered as midSource so it never contributes a reject.
            SvaStateVertex* const acceptSinkp = scopedCreateVertex();
            for (SvaStateVertex* const srcp : abortSources)
                guardedLink(srcp, acceptSinkp, sampledAbortFire(), flp);
            std::vector<SvaStateVertex*> midSources = bodyResult.midSources;
            midSources.push_back(acceptSinkp);
            AstNodeExpr* finalCondp = bodyResult.finalCondp;
            if (finalCondp) {
                if (finalCondp->backp()) finalCondp = finalCondp->cloneTreePure(false);
                finalCondp = new AstLogOr{flp, finalCondp, abortFireExpr(condp, flp)};
            }
            return {bodyResult.termVertexp, finalCondp, std::move(midSources)};
        }

        // rejectOnFail treats m_condp as the success condition and fires on
        // !condp, so the edge carries !sampledAbortFire().
        SvaStateVertex* const rejectSinkp = m_graph.createStateVertex();
        rejectSinkp->m_isRejectSink = true;
        for (SvaStateVertex* const srcp : abortSources)
            if (!chainAccountsSource(srcp, preEdges))
                addAbortRejectEdge(srcp, rejectSinkp, condp, flp);
        AstNodeExpr* finalCondp = bodyResult.finalCondp;
        if (finalCondp) {
            if (finalCondp->backp()) finalCondp = finalCondp->cloneTreePure(false);
            finalCondp
                = new AstLogAnd{flp, finalCondp, new AstLogNot{flp, abortFireExpr(condp, flp)}};
        }
        return {bodyResult.termVertexp, finalCondp, bodyResult.midSources};
    }

public:
    SvaNfaBuilder(SvaGraph& graph, AstNodeModule* modp, V3UniqueNames& propTempNames,
                  bool isCoverSeq = false, bool needsRejectVerdict = true, bool isSeqEvent = false)
        : m_graph{graph}
        , m_modp{modp}
        , m_propTempNames{propTempNames}
        , m_isCoverSeq{isCoverSeq}
        , m_needsRejectVerdict{needsRejectVerdict}
        , m_isSeqEvent{isSeqEvent} {}

    // Reset scope between antecedent and consequent: liveness must not leak.
    // m_outerAbortStack survives: an abort wrapping the implication covers the
    // consequent too (IEEE 1800-2023 16.12.14).
    void resetScope() {
        m_inUnboundedScope = false;
        m_temporalGuardStack.clear();
    }

    BuildResult buildExpr(AstNodeExpr* nodep, SvaStateVertex* entryVtxp,
                          bool isTopLevelStep = false) {
        if (AstSExpr* const sexprp = VN_CAST(nodep, SExpr)) {
            return buildSExpr(sexprp, entryVtxp, isTopLevelStep);
        }
        if (AstSConsRep* const repp = VN_CAST(nodep, SConsRep)) {
            return buildConsRep(repp, entryVtxp, isTopLevelStep);
        }
        if (AstPropAlways* const alwaysp = VN_CAST(nodep, PropAlways)) {
            return buildPropAlways(alwaysp, entryVtxp, isTopLevelStep);
        }
        if (AstSGotoRep* const repp = VN_CAST(nodep, SGotoRep)) {
            return buildGotoRep(repp, entryVtxp);
        }
        if (AstSThroughout* const throughoutp = VN_CAST(nodep, SThroughout)) {
            return buildThroughout(throughoutp, entryVtxp, isTopLevelStep);
        }
        if (AstSOr* const orp = VN_CAST(nodep, SOr)) {
            return buildOrMerge(orp->lhsp(), orp->rhsp(), entryVtxp, orp->fileline(),
                                isTopLevelStep);
        }
        if (AstLogOr* const orp = VN_CAST(nodep, LogOr)) {
            // A plain logical OR is one sampled boolean, not a temporal merge.
            UASSERT_OBJ(!orp->exists([](const AstNodeExpr* ep) { return ep->isMultiCycleSva(); }),
                        orp, "Grammar forbids temporal '||' operands");
            return {entryVtxp, orp, {}};
        }
        if (AstSAnd* const andp = VN_CAST(nodep, SAnd)) {
            return buildSAnd(andp, entryVtxp, isTopLevelStep);
        }
        if (AstSIntersect* const intp = VN_CAST(nodep, SIntersect)) {
            // Conjoin equal-length intersect checks, retaining a non-flattened fallback.
            const int lhsLen = fixedLength(intp->lhsp());
            const int rhsLen = fixedLength(intp->rhsp());
            if (lhsLen >= 0 && rhsLen >= 0) {
                if (lhsLen != rhsLen) {
                    // Unequal fixed lengths share no common length -> never matches.
                    return buildNeverMatchIntersect(intp, entryVtxp, isTopLevelStep,
                                                    "intersect operands have no common length");
                }
                if (AstNodeExpr* const conjp
                    = conjoinFixedSeqs(intp->lhsp(), intp->rhsp(), intp->fileline())) {
                    return buildFromLoweringTree(conjp, entryVtxp, isTopLevelStep);
                }
                return buildSameEndIntersectCombiner(intp->lhsp(), intp->rhsp(), entryVtxp,
                                                     intp->fileline(), lhsLen, isTopLevelStep);
            }
            return buildVarLenIntersect(intp, entryVtxp, isTopLevelStep);
        }
        if (AstSWithin* const withinp = VN_CAST(nodep, SWithin)) {
            return buildSWithin(withinp, entryVtxp, isTopLevelStep);
        }
        if (AstAbortOn* const ap = VN_CAST(nodep, AbortOn)) {
            return buildAbortOn(ap->condp(), ap->propp(), entryVtxp, ap->kind(), ap->fileline(),
                                isTopLevelStep);
        }
        if (VN_IS(nodep, SNonConsRep)) return BuildResult::fail();
        if (AstImplication* const implp = VN_CAST(nodep, Implication)) {
            return buildImplicationEdges(implp->lhsp(), implp->rhsp(), entryVtxp,
                                         implp->isOverlapped(), implp->isFollowedBy(),
                                         implp->lhsp(), implp->fileline());
        }
        if (AstUntil* const untilp = VN_CAST(nodep, Until)) {
            return buildUntil(untilp, entryVtxp, isTopLevelStep);
        }
        // Leave unsupported temporal operators to V3AssertPre to avoid duplicate diagnostics.
        if (nodep->exists([](const AstNodeExpr* ep) { return ep->isMultiCycleSva(); })) {
            return BuildResult::fail();
        }
        // Boolean leaf (including LogAnd): return as finalCond
        return {entryVtxp, nodep, {}};
    }

    // Wire antecedent, match/reject links, delay, and body for implication/followed-by.
    BuildResult buildImplicationEdges(AstNodeExpr* antExprp, AstNodeExpr* bodyExprp,
                                      SvaStateVertex* entryVtxp, bool isOverlapped,
                                      bool isFollowedBy, AstNode* errorNodep, FileLine* flp) {
        const BuildResult antResult = buildExpr(antExprp, entryVtxp);
        if (!antResult.valid()) return antResult;
        // Followed-by requires pure-boolean antecedent for non-vacuous-fail at
        // the attempt-start cycle. IEEE 1800-2023 16.12.9 permits a multi-cycle
        // sequence LHS, so this is an implementation gap rather than illegal SV.
        if (isFollowedBy && antResult.termVertexp != entryVtxp) {
            errorNodep->v3warn(E_UNSUPPORTED,
                               "Unsupported: sequence expression as antecedent of followed-by"
                               " (#-# / #=#) (IEEE 1800-2023 16.12.9)");
            cleanupProbeResult(antResult);
            return BuildResult::failWithError();
        }
        UASSERT_OBJ(!isFollowedBy || antResult.finalCondp, errorNodep,
                    "followed-by antecedent terminal at entry must carry finalCondp");

        // Use raw createStateVertex() so trigVtxp starts without liveness --
        // reaching the antecedent terminal is a definitive event.
        SvaStateVertex* const trigVtxp = m_graph.createStateVertex();
        if (antResult.finalCondp) {
            m_graph.addLink(antResult.termVertexp, trigVtxp,
                            sampled(antResult.finalCondp->cloneTreePure(false)));
            // Followed-by non-vacuous fail: rejectOnFail fires when the attempt
            // is live (termVtx reachable) and sampled(antecedent) is false.
            if (isFollowedBy) {
                SvaStateVertex* const sinkVtxp = m_graph.createStateVertex();
                sinkVtxp->m_isRejectSink = true;
                SvaTransEdge* const ep
                    = m_graph.addLink(antResult.termVertexp, sinkVtxp,
                                      sampled(antResult.finalCondp->cloneTreePure(false)));
                ep->m_rejectOnFail = true;
            }
            // finalCondp is cloned into the Sampled nodes; if the original is
            // not parented anywhere in the AST anymore it must be freed here
            // or ASan flags it as a leak (e.g. t_sequence_bool_ops).
            if (!antResult.finalCondp->backp()) {
                VL_DO_DANGLING(antResult.finalCondp->deleteTree(), antResult.finalCondp);
            }
        } else {
            m_graph.addLink(antResult.termVertexp, trigVtxp);
        }
        resetScope();

        SvaStateVertex* bodyEntryp = trigVtxp;
        if (!isOverlapped) {
            SvaStateVertex* const delayVtxp = m_graph.createStateVertex();
            m_graph.addClockedEdge(trigVtxp, delayVtxp);
            bodyEntryp = delayVtxp;
        }
        return buildExpr(bodyExprp, bodyEntryp, /*isTopLevelStep=*/true);
    }

    BuildResult build(AstNodeExpr* exprp) {
        m_graph.m_startVertexp = scopedCreateVertex();
        return buildExpr(exprp, m_graph.m_startVertexp, /*isTopLevelStep=*/true);
    }
};

//######################################################################
// NFA Lowering (Observed evaluation/state update, Reactive action dispatch)

class SvaNfaLowering final {
public:
    // Inputs for lower(). disableExprp ownership transfers to the lowering.
    struct LowerRequest final {
        AstNodeExpr* triggerExprp = nullptr;  // Runtime assertion-on gate
        AstSenTree* senTreep = nullptr;  // Clock sensitivity tree
        AstNodeExpr* matchCondp = nullptr;  // Final boolean match condition
        AstNodeExpr* disableExprp = nullptr;  // Normalized disable iff (consumed)
        const std::vector<AbortSpec>* abortSpecsp = nullptr;  // Peeled abort prefix
        AstVar* disableCntVarp = nullptr;  // Disable posedge epoch counter
        AstVar* snapshotVarp = nullptr;  // Disable epoch snapshot
        bool isCover = false;  // Cover directive: count matches, no rejects
        bool negated = false;  // Property under not(): swap match/reject roles
        VAssertType assertType = VAssertType::INTERNAL;  // For assertion-control gating
        VAssertDirectiveType directiveType = VAssertDirectiveType::INTERNAL;  // Likewise
        // Requested optional outputs; unset ones stay empty in LowerResult
        bool wantPerSrcFail = false;  // Per-depth failure sources
        // The synthesized default handler only needs a count for true multiplicity.
        bool pruneSingleFailSource = false;
        bool wantPerSrcMatch = false;  // Per-depth match sources
        bool wantAbortPassCount = false;  // Forced-accept attempt count
        bool wantAbortFailCount = false;  // Forced-reject attempt count
        bool wantStrongPending = false;  // End-of-sim pending count
        bool wantPerMid = false;  // Per-end cover sequence signals
    };
    // Outputs of lower(); all expressions are freshly built (caller owns)
    struct LowerResult final {
        AstNodeExpr* outputExprp = nullptr;  // Materialized !reject / match verdict
        AstNodeExpr* abortAnyp = nullptr;  // Any abort fired this evaluation
        AstNodeExpr* disableRefp = nullptr;  // Observed disable variable reference
        AstNodeExpr* failCountp = nullptr;  // Extra dynamically counted failures
        AstNodeExpr* matchCountp = nullptr;  // Extra range-ring match multiplicity
        AstNodeExpr* abortPassCountp = nullptr;  // Forced-accept attempt count
        AstNodeExpr* abortFailCountp = nullptr;  // Forced-reject attempt count
        AstNodeExpr* strongPendingCountp = nullptr;  // End-of-sim pending attempts
        std::vector<AstNodeExpr*> failAttemptSrcs;  // Per-depth failure outcomes
        std::vector<AstNodeExpr*> matchAttemptSrcs;  // Per-depth match outcomes
        std::vector<AstNodeExpr*> perMidSrcs;  // Per-end cover sequence signals
    };

private:
    AstNodeModule* const m_modp;  // Module to add state vars and always blocks to
    AstNodeDType* const m_u32DTypep;  // Shared unsigned counter dtype
    V3UniqueNames m_names{"__Vnfa"};  // Generated state variable names
    size_t m_statDelayRingEdgeVisits = 0;  // Delay-ring incoming edges visited

    // Per-lowering shared context (passed to phase sub-functions)
    // Per-vertex lowering state is stored in SvaVertexData and accessed via
    // V3GraphVertex::userp() (see vtx[i]->datap()).
    struct LowerCtx final {
        FileLine* const flp;  // Source location for generated AST
        SvaGraph& graph;  // NFA graph
        int N = 0;  // Number of vertices
        std::vector<SvaStateVertex*> vtx;  // Color-indexed vertex lookup
        std::vector<const SvaTransEdge*> edges;  // All edges (flat)
        int startIdx = 0;  // Start vertex color index
        int matchIdx = -1;  // Match vertex color index (-1 if none)
        AstSenTree* senTreep = nullptr;  // Clock sensitivity tree
        AstNodeExpr* disableExprp = nullptr;  // disable iff expression (may be nullptr)
        AstNodeExpr* matchCondp = nullptr;  // Final boolean match condition (may be nullptr)
        AstVar* disableCntVarp = nullptr;  // disable counter var (may be nullptr)
        AstVar* snapshotVarp = nullptr;  // disable snapshot var (may be nullptr)
        VAssertType assertType = VAssertType::INTERNAL;  // Assertion type for control tasks
        VAssertDirectiveType directiveType
            = VAssertDirectiveType::INTERNAL;  // Directive type for control tasks
        AstVar* killVarp = nullptr;  // Last observed kill generation
        AstVar* evalKillVarp = nullptr;  // Pre-update kill generation used for the verdict
        AstVar* ctlKillVarp = nullptr;  // Kill query captured once at transaction entry
        AstVar* abortAnyVarp = nullptr;  // Any outer-priority abort condition fired
        AstVar* abortAcceptVarp = nullptr;  // Winning abort is accept_on
        AstVar* abortRejectVarp = nullptr;  // Winning abort is reject_on
        AstNode* snapshotBodyp = nullptr;  // Observed old-state snapshot statements
        AstNode* updateBodyp = nullptr;  // Observed live-state update statements
        LowerCtx(FileLine* fl, SvaGraph& g)
            : flp{fl}
            , graph{g} {}
    };

    static void appendStmt(AstNode*& bodypr, AstNode* stmtp) {
        if (bodypr) {
            bodypr->addNext(stmtp);
        } else {
            bodypr = stmtp;
        }
    }

    // Build a match-now expression: stateSig[i] && $sampled(condp)
    static AstNodeExpr* buildMatchNow(FileLine* flp, AstNodeExpr* stateExprp, AstNodeExpr* condp) {
        AstNodeExpr* const statep = stateExprp->cloneTreePure(false);
        if (!condp) return statep;
        return new AstLogAnd{flp, statep, sampled(condp->cloneTreePure(false))};
    }
    static AstNodeExpr* andCond(FileLine* flp, AstNodeExpr* exprp, AstNodeExpr* condp) {
        if (!condp) return exprp;
        return new AstLogAnd{flp, exprp, condp->cloneTreePure(false)};
    }
    // bp is always non-null; only ap can be null (serving as accumulator).
    static AstNodeExpr* orExprs(FileLine* flp, AstNodeExpr* ap, AstNodeExpr* bp) {
        if (!ap) return bp;
        return new AstLogOr{flp, ap, bp};
    }
    static AstNodeExpr* killActive(LowerCtx& c) {
        return new AstNeq{c.flp, new AstVarRef{c.flp, c.evalKillVarp, VAccess::READ},
                          new AstVarRef{c.flp, c.ctlKillVarp, VAccess::READ}};
    }
    static AstNodeExpr* notKillActive(LowerCtx& c) { return new AstLogNot{c.flp, killActive(c)}; }
    static AstNodeExpr* gateNotKill(LowerCtx& c, AstNodeExpr* exprp) {
        if (!exprp) return nullptr;
        return new AstLogAnd{c.flp, exprp, notKillActive(c)};
    }
    static AstNodeExpr* abortActive(LowerCtx& c) {
        return c.abortAnyVarp
                   ? static_cast<AstNodeExpr*>(new AstVarRef{c.flp, c.abortAnyVarp, VAccess::READ})
                   : static_cast<AstNodeExpr*>(new AstConst{c.flp, AstConst::BitFalse{}});
    }
    static AstNodeExpr* gateNotAbort(LowerCtx& c, AstNodeExpr* exprp) {
        if (!exprp || !c.abortAnyVarp) return exprp;
        return new AstLogAnd{c.flp, exprp, new AstLogNot{c.flp, abortActive(c)}};
    }
    static AstNodeExpr* nextRingIndex(FileLine* flp, AstVar* idxp, uint32_t size) {
        const auto u32Const = [flp](uint32_t value) {
            return new AstConst{flp, AstConst::WidthedValue{}, 32, value};
        };
        UASSERT(size > 1, "Delay ring index needs at least two slots");
        // idx == size - 1 ? 0 : idx + 1
        AstAdd* const addp = new AstAdd{flp, new AstVarRef{flp, idxp, VAccess::READ}, u32Const(1)};
        addp->dtypeFrom(idxp);
        AstCond* const condp = new AstCond{
            flp, new AstEq{flp, new AstVarRef{flp, idxp, VAccess::READ}, u32Const(size - 1)},
            u32Const(0), addp};
        condp->dtypeFrom(idxp);
        return condp;
    }
    static AstNodeExpr* delayRingBit(FileLine* flp, AstVar* ringp, AstNodeExpr* idxExprp,
                                     VAccess access = VAccess::READ) {
        // ring[idx]
        return new AstSel{flp, new AstVarRef{flp, ringp, access}, idxExprp, 1};
    }
    static AstNodeExpr* ringIndexOffset(FileLine* flp, AstVar* idxp, uint32_t size,
                                        uint32_t offset) {
        if (!offset) return new AstVarRef{flp, idxp, VAccess::READ};
        AstAdd* const addp = new AstAdd{flp, new AstVarRef{flp, idxp, VAccess::READ},
                                        new AstConst{flp, AstConst::WidthedValue{}, 32, offset}};
        addp->dtypeFrom(idxp);
        AstModDiv* const modp
            = new AstModDiv{flp, addp, new AstConst{flp, AstConst::WidthedValue{}, 32, size}};
        modp->dtypeFrom(idxp);
        return modp;
    }
    static AstNodeExpr* currentEntryAlive(LowerCtx& c) {
        if (!c.disableExprp) return nullptr;
        return new AstLogNot{c.flp, c.disableExprp->cloneTreePure(false)};
    }
    static AstNodeExpr* oldAttemptAlive(LowerCtx& c) {
        AstNodeExpr* gatep = currentEntryAlive(c);
        if (!gatep && !c.snapshotVarp) return nullptr;
        if (c.snapshotVarp) {
            AstNodeExpr* const epochOkp
                = new AstEq{c.flp, new AstVarRef{c.flp, c.snapshotVarp, VAccess::READ},
                            new AstVarRef{c.flp, c.disableCntVarp, VAccess::READ}};
            gatep = gatep ? static_cast<AstNodeExpr*>(new AstLogAnd{c.flp, gatep, epochOkp})
                          : epochOkp;
        }
        return gatep;
    }
    static AstNodeExpr* gateOldAttempt(LowerCtx& c, AstNodeExpr* exprp) {
        AstNodeExpr* const gatep = oldAttemptAlive(c);
        if (!gatep) return exprp;
        return new AstLogAnd{c.flp, exprp, gatep};
    }

    static void clearStateSignals(LowerCtx& c) {
        for (int i = 0; i < c.N; ++i) {
            AstNodeExpr*& sigp = c.vtx[i]->datap()->stateSigp;
            if (sigp) VL_DO_DANGLING(sigp->deleteTree(), sigp);
        }
    }

    void emitAbortCapture(LowerCtx& c, const std::string& baseName,
                          const std::vector<AbortSpec>* abortSpecsp) {
        if (!abortSpecsp || abortSpecsp->empty()) return;

        std::vector<AstVar*> condVars;
        condVars.reserve(abortSpecsp->size());
        for (size_t i = 0; i < abortSpecsp->size(); ++i) {
            const AbortSpec& spec = abortSpecsp->at(i);
            AstVar* const varp
                = new AstVar{c.flp, VVarType::MODULETEMP,
                             baseName + "__abortCond" + std::to_string(i), m_modp->findBitDType()};
            varp->lifetime(VLifetime::STATIC_EXPLICIT);
            m_modp->addStmtsp(varp);
            condVars.push_back(varp);
            // Sample abort once per clock; supported async forms have no live inter-clock window.
            AstNodeExpr* valuep = sampled(spec.condp->cloneTreePure(false));
            appendStmt(c.snapshotBodyp,
                       new AstAssign{c.flp, new AstVarRef{c.flp, varp, VAccess::WRITE}, valuep});
        }

        const auto newAbortVar = [&](const std::string& suffix) {
            AstVar* const varp = new AstVar{c.flp, VVarType::MODULETEMP, baseName + suffix,
                                            m_modp->findBitDType()};
            varp->lifetime(VLifetime::STATIC_EXPLICIT);
            m_modp->addStmtsp(varp);
            return varp;
        };
        c.abortAnyVarp = newAbortVar("__abortAny");
        c.abortAcceptVarp = newAbortVar("__abortAccept");
        c.abortRejectVarp = newAbortVar("__abortReject");

        AstNodeExpr* anyp = nullptr;
        AstNodeExpr* acceptp = nullptr;
        AstNodeExpr* rejectp = nullptr;
        AstNodeExpr* remainingp = new AstConst{c.flp, AstConst::BitTrue{}};
        for (size_t i = 0; i < abortSpecsp->size(); ++i) {
            AstNodeExpr* const condp = new AstVarRef{c.flp, condVars[i], VAccess::READ};
            anyp = orExprs(c.flp, anyp, condp->cloneTreePure(false));
            AstNodeExpr* const effectivep = new AstLogAnd{c.flp, condp->cloneTreePure(false),
                                                          remainingp->cloneTreePure(false)};
            if (abortSpecsp->at(i).kind.isAccept()) {
                acceptp = orExprs(c.flp, acceptp, effectivep);
            } else {
                rejectp = orExprs(c.flp, rejectp, effectivep);
            }
            remainingp = new AstLogAnd{c.flp, remainingp, new AstLogNot{c.flp, condp}};
        }
        VL_DO_DANGLING(remainingp->deleteTree(), remainingp);
        if (!acceptp) acceptp = new AstConst{c.flp, AstConst::BitFalse{}};
        if (!rejectp) rejectp = new AstConst{c.flp, AstConst::BitFalse{}};
        appendStmt(
            c.snapshotBodyp,
            new AstAssign{c.flp, new AstVarRef{c.flp, c.abortAnyVarp, VAccess::WRITE}, anyp});
        appendStmt(c.snapshotBodyp,
                   new AstAssign{c.flp, new AstVarRef{c.flp, c.abortAcceptVarp, VAccess::WRITE},
                                 acceptp});
        appendStmt(c.snapshotBodyp,
                   new AstAssign{c.flp, new AstVarRef{c.flp, c.abortRejectVarp, VAccess::WRITE},
                                 rejectp});
    }

    void emitEvaluationSnapshots(LowerCtx& c) {
        AstNode* bodyp = c.snapshotBodyp;
        const auto addSnapshot = [&](AstVar* const evalp, AstVar* const livep) {
            if (!evalp) return;
            UASSERT_OBJ(livep, evalp, "Evaluation snapshot missing live state");
            AstAssign* const assignp
                = new AstAssign{c.flp, new AstVarRef{c.flp, evalp, VAccess::WRITE},
                                new AstVarRef{c.flp, livep, VAccess::READ}};
            appendStmt(bodyp, assignp);
        };
        addSnapshot(c.evalKillVarp, c.killVarp);
        for (int i = 0; i < c.N; ++i) {
            SvaVertexData* const datap = c.vtx[i]->datap();
            addSnapshot(datap->evalStateVarp, datap->stateVarp);
            addSnapshot(datap->evalDelayRingVarp, datap->delayRingVarp);
            addSnapshot(datap->evalDelayRingIdxVarp, datap->delayRingIdxVarp);
        }
        c.snapshotBodyp = bodyp;
    }

    // Phase 3 output signals
    struct SignalSet final {
        AstNodeExpr* terminalActivep = nullptr;  // OR of all successful terminal matches
        AstNodeExpr* matchCountp = nullptr;  // Additional range-ring match multiplicity
        AstNodeExpr* failCountp = nullptr;  // Additional dynamically counted failures
        AstNodeExpr* rejectBasep = nullptr;  // Reject when a terminal match fails
        AstNodeExpr* requiredStepRejectp = nullptr;  // Per-source reject from rejectOnFail Links
        AstNodeExpr* throughoutRejectp = nullptr;  // Reject when a throughout guard drops
    };

    static constexpr int kDepthUnreachable = -1;
    static constexpr int kDepthAmbiguous = -2;
    using OutcomeBuckets = std::map<int, AstNodeExpr*>;

    static AstNodeExpr* boolToCount(LowerCtx& c, AstNodeExpr* condp) {
        AstCond* const resultp
            = new AstCond{c.flp, condp, new AstConst{c.flp, AstConst::WidthedValue{}, 32, 1},
                          new AstConst{c.flp, AstConst::WidthedValue{}, 32, 0}};
        resultp->dtypeFrom(c.killVarp);
        return resultp;
    }

    static AstNodeExpr* addCounts(LowerCtx& c, AstNodeExpr* lhsp, AstNodeExpr* rhsp) {
        if (!lhsp) return rhsp;
        AstAdd* const resultp = new AstAdd{c.flp, lhsp, rhsp};
        resultp->dtypeFrom(c.killVarp);
        return resultp;
    }

    static AstNodeExpr* gateCount(LowerCtx& c, AstNodeExpr* gatep, AstNodeExpr* countp) {
        if (!gatep) return countp;
        AstCond* const resultp = new AstCond{c.flp, gatep, countp,
                                             new AstConst{c.flp, AstConst::WidthedValue{}, 32, 0}};
        resultp->dtypeFrom(c.killVarp);
        return resultp;
    }

    static std::vector<int> computeAttemptDepths(const LowerCtx& c) {
        std::vector<int> depths(c.N, kDepthUnreachable);
        depths[c.startIdx] = 0;
        bool converged = false;
        for (int pass = 0; pass < 2 * c.N + 2; ++pass) {
            bool changed = false;
            for (const SvaTransEdge* const tep : c.edges) {
                const int fi = tep->fromVtxp()->color();
                const int ti = tep->toVtxp()->color();
                if (depths[fi] == kDepthUnreachable || ti == c.startIdx) continue;
                int edgeDepth = tep->m_consumesCycle ? 1 : 0;
                if (tep->toVtxp()->m_isFixedDelayRing) {
                    edgeDepth = tep->toVtxp()->m_delayRingSize;
                }
                const int candidate
                    = depths[fi] == kDepthAmbiguous ? kDepthAmbiguous : depths[fi] + edgeDepth;
                if (depths[ti] == kDepthUnreachable) {
                    depths[ti] = candidate;
                    changed = true;
                } else if (depths[ti] != candidate && depths[ti] != kDepthAmbiguous) {
                    depths[ti] = kDepthAmbiguous;
                    changed = true;
                }
            }
            if (!changed) {
                converged = true;
                break;
            }
        }
        UASSERT_OBJ(converged, c.graph.m_startVertexp,
                    "Attempt depth propagation did not converge");
        return depths;
    }

    AstNodeExpr* strongPendingFastCount(LowerCtx& c) {
        AstNodeExpr* countp = nullptr;
        for (int i = 0; i < c.N; ++i) {
            if (!c.vtx[i]->m_strongPending) continue;
            AstNodeExpr* itemCountp = nullptr;
            if (c.vtx[i]->datap()->stateVarp) {
                itemCountp = boolToCount(
                    c, new AstVarRef{c.flp, c.vtx[i]->datap()->stateVarp, VAccess::READ});
            } else if (c.vtx[i]->datap()->delayRingVarp) {
                AstCountOnes* const ringCountp = new AstCountOnes{
                    c.flp, new AstVarRef{c.flp, c.vtx[i]->datap()->delayRingVarp, VAccess::READ}};
                ringCountp->dtypeFrom(c.killVarp);
                itemCountp = ringCountp;
            }
            if (itemCountp) countp = addCounts(c, countp, itemCountp);
        }
        return countp;
    }

    OutcomeBuckets bucketStrongByDepth(LowerCtx& c, const std::vector<int>& depths) {
        OutcomeBuckets depthBuckets;
        for (int i = 0; i < c.N; ++i) {
            if (!c.vtx[i]->m_strongPending) continue;
            if (AstVar* const statep = c.vtx[i]->datap()->stateVarp) {
                AstNodeExpr*& bucketpr = depthBuckets[depths[i]];
                bucketpr = orExprs(c.flp, bucketpr, new AstVarRef{c.flp, statep, VAccess::READ});
                continue;
            }
            AstVar* const ringp = c.vtx[i]->datap()->delayRingVarp;
            if (!ringp) continue;
            UASSERT_OBJ(c.vtx[i]->m_isFixedDelayRing, c.vtx[i],
                        "Strong pending range ring is unsupported");
            AstVar* const idxp = c.vtx[i]->datap()->delayRingIdxVarp;
            const uint32_t size = static_cast<uint32_t>(c.vtx[i]->m_delayRingSize);
            for (uint32_t offset = 0; offset < size; ++offset) {
                AstNodeExpr* const bitp
                    = delayRingBit(c.flp, ringp, ringIndexOffset(c.flp, idxp, size, offset));
                AstNodeExpr*& bucketpr = depthBuckets[depths[i] - offset];
                bucketpr = orExprs(c.flp, bucketpr, bitp);
            }
        }
        return depthBuckets;
    }

    AstNodeExpr* buildStrongPendingCount(LowerCtx& c, bool trackResolved,
                                         bool ambiguousResolvedDepth) {
        std::unordered_set<int> groups;
        uint64_t ringSlots = 0;
        for (int i = 0; i < c.N; ++i) {
            if (!c.vtx[i]->m_strongPending) continue;
            UASSERT_OBJ(c.vtx[i]->m_strongPendingGroup >= 0, c.vtx[i],
                        "Strong pending vertex has no group");
            groups.insert(c.vtx[i]->m_strongPendingGroup);
            if (c.vtx[i]->datap()->delayRingVarp) {
                ringSlots += static_cast<uint64_t>(c.vtx[i]->m_delayRingSize);
            }
        }

        if (groups.empty()) return nullptr;

        if (c.graph.m_hasAndCombiner) {
            c.flp->v3warn(E_UNSUPPORTED,
                          "Unsupported: strong s_always in a temporal AND/intersect "
                          "composite cannot preserve resolved attempt identity");
            return strongPendingFastCount(c);
        }

        // Linear strong properties use an exact O(1) ring count; OR needs depth buckets.
        if (!trackResolved && groups.size() <= 1) return strongPendingFastCount(c);

        const std::vector<int> depths = computeAttemptDepths(c);
        for (int i = 0; i < c.N; ++i) {
            if (!c.vtx[i]->m_strongPending) continue;
            if (depths[i] < 0) {
                c.flp->v3warn(E_UNSUPPORTED,
                              "Unsupported: end-of-simulation attempt counting for multiple "
                              "strong operators with an ambiguous temporal depth");
                return strongPendingFastCount(c);
            }
        }
        if (ringSlots > static_cast<uint64_t>(v3Global.opt.assertUnrollLimit())) {
            c.flp->v3error("End-of-simulation attempt counting for multiple strong operators "
                           "requires expanding "
                           << ringSlots << " ring slots, exceeding --assert-unroll-limit ("
                           << v3Global.opt.assertUnrollLimit() << ")");
            return strongPendingFastCount(c);
        }

        if (trackResolved && ambiguousResolvedDepth) {
            c.flp->v3warn(E_UNSUPPORTED,
                          "Unsupported: end-of-simulation attempt counting for multiple "
                          "strong operators with an ambiguous temporal depth");
            return strongPendingFastCount(c);
        }

        OutcomeBuckets depthBuckets = bucketStrongByDepth(c, depths);
        if (depthBuckets.empty()) {
            c.flp->v3warn(E_UNSUPPORTED, "Unsupported: strong s_always pending state has a "
                                         "non-positive temporal depth");
            return strongPendingFastCount(c);
        }
        AstNodeExpr* countp = nullptr;
        for (auto& pair : depthBuckets) {
            countp = addCounts(c, countp, boolToCount(c, pair.second));
        }
        return countp;
    }

    static AstNodeExpr* computeActiveAttemptCount(LowerCtx& c) {
        const std::vector<int> depths = computeAttemptDepths(c);
        // Abort priority starts the current attempt before implication filters it.
        UASSERT_OBJ(c.vtx[c.startIdx]->datap()->stateSigp, c.vtx[c.startIdx],
                    "Abort attempt root signal was not resolved");
        AstNodeExpr* currentp = c.vtx[c.startIdx]->datap()->stateSigp->cloneTreePure(false);
        currentp = gateNotKill(c, currentp);
        AstNodeExpr* countp = boolToCount(c, currentp);

        OutcomeBuckets scalarRoots;
        for (int i = 0; i < c.N; ++i) {
            SvaVertexData* const datap = c.vtx[i]->datap();
            if (datap->evalStateVarp) {
                UASSERT_OBJ(depths[i] >= 0, c.vtx[i],
                            "Linear abort body implies a unique registered-vertex depth");
                AstNodeExpr* rootp = new AstVarRef{c.flp, datap->evalStateVarp, VAccess::READ};
                rootp = gateOldAttempt(c, rootp);
                rootp = gateNotKill(c, rootp);
                AstNodeExpr*& bucketpr = scalarRoots[depths[i]];
                bucketpr = orExprs(c.flp, bucketpr, rootp);
            }
            if (datap->evalDelayRingVarp) {
                AstCountOnes* const ringCountp = new AstCountOnes{
                    c.flp, new AstVarRef{c.flp, datap->evalDelayRingVarp, VAccess::READ}};
                ringCountp->dtypeFrom(c.killVarp);
                AstNodeExpr* gatep = oldAttemptAlive(c);
                gatep = gatep ? static_cast<AstNodeExpr*>(
                                    new AstLogAnd{c.flp, gatep, notKillActive(c)})
                              : notKillActive(c);
                countp = addCounts(c, countp, gateCount(c, gatep, ringCountp));
            }
        }
        for (auto& pair : scalarRoots) {
            countp = addCounts(c, countp, boolToCount(c, pair.second));
        }
        return countp;
    }

    // Guard drops are counted by the throughout path
    static AstNodeExpr* gateThroughoutGuards(LowerCtx& c, const SvaStateVertex* vtxp,
                                             AstNodeExpr* exprp) {
        for (AstNodeExpr* const condp : vtxp->m_throughoutConds) {
            exprp = new AstLogAnd{c.flp, exprp, sampled(condp->cloneTreePure(false))};
        }
        return exprp;
    }

    static AstNodeExpr* gateAttemptOutcome(LowerCtx& c, AstNodeExpr* exprp) {
        exprp = gateNotKill(c, exprp);
        exprp = gateNotAbort(c, exprp);
        if (c.disableExprp) {
            exprp = new AstLogAnd{c.flp, exprp,
                                  new AstLogNot{c.flp, c.disableExprp->cloneTreePure(false)}};
        }
        return exprp;
    }

    static void addAttemptOutcome(LowerCtx& c, OutcomeBuckets* bucketsp,
                                  const std::vector<int>& depths, int vertexIdx,
                                  AstNodeExpr* exprp, int extraDepth = 0) {
        if (!bucketsp) {
            VL_DO_DANGLING(exprp->deleteTree(), exprp);
            return;
        }
        int depth = depths[vertexIdx];
        if (depth >= 0) depth += extraDepth;
        AstNodeExpr*& bucketpr = (*bucketsp)[depth];
        bucketpr = orExprs(c.flp, bucketpr, gateAttemptOutcome(c, exprp));
    }

    static void finishAttemptOutcomes(LowerCtx& c, OutcomeBuckets& buckets,
                                      std::vector<AstNodeExpr*>* outAttemptSrcsp) {
        if (!outAttemptSrcsp) {
            for (auto& pair : buckets) VL_DO_DANGLING(pair.second->deleteTree(), pair.second);
            return;
        }
        AstNodeExpr* fallbackp = nullptr;
        for (auto& pair : buckets) {
            if (pair.first < 0) {
                fallbackp = orExprs(c.flp, fallbackp, pair.second);
            } else {
                outAttemptSrcsp->push_back(pair.second);
            }
        }
        if (fallbackp) outAttemptSrcsp->push_back(fallbackp);
    }

    // Phase 2 updates live registered state after snapshotting incoming contributions.
    void emitStateUpdate(LowerCtx& c) {
        AstNode* bodyp = nullptr;
        for (int i = 0; i < c.N; ++i) {
            if (!c.vtx[i]->datap()->stateVarp) continue;

            AstNodeExpr* nextStatep = nullptr;
            for (const V3GraphEdge& edger : c.vtx[i]->inEdges()) {
                const SvaTransEdge& tedger = static_cast<const SvaTransEdge&>(edger);
                if (!tedger.m_consumesCycle) continue;
                const int fromIdx = tedger.fromVtxp()->color();
                UASSERT_OBJ(c.vtx[fromIdx]->datap()->stateSigp, tedger.fromVtxp(),
                            "Clocked-edge source missing stateSig");

                AstNodeExpr* srcSigp = c.vtx[fromIdx]->datap()->stateSigp->cloneTreePure(false);
                srcSigp = andCond(c.flp, srcSigp, tedger.m_condp);
                nextStatep = orExprs(c.flp, nextStatep, srcSigp);
            }

            UASSERT_OBJ(nextStatep, c.vtx[i],
                        "Registered vertex has no clocked incoming contribution");
            nextStatep = gateNotKill(c, nextStatep);
            nextStatep = gateNotAbort(c, nextStatep);

            AstAssign* const assignp = new AstAssign{
                c.flp, new AstVarRef{c.flp, c.vtx[i]->datap()->stateVarp, VAccess::WRITE},
                nextStatep};
            appendStmt(bodyp, assignp);
        }

        if (bodyp) appendStmt(c.updateBodyp, bodyp);
    }

    // Phase 2b: Bitset ring-buffer delay update.
    void emitDelayRingUpdate(LowerCtx& c) {
        for (int ri = 0; ri < c.N; ++ri) {
            SvaStateVertex* const vtxp = c.vtx[ri];
            AstVar* const ringp = vtxp->datap()->delayRingVarp;
            if (!ringp) continue;
            AstVar* const idxp = vtxp->datap()->delayRingIdxVarp;
            AstVar* const evalRingp = vtxp->datap()->evalDelayRingVarp;
            AstVar* const evalIdxp = vtxp->datap()->evalDelayRingIdxVarp;
            const uint32_t size = static_cast<uint32_t>(vtxp->m_delayRingSize);

            AstNodeExpr* incomingp = nullptr;
            for (const V3GraphEdge& edger : vtxp->inEdges()) {
                ++m_statDelayRingEdgeVisits;
                const SvaTransEdge& tedger = static_cast<const SvaTransEdge&>(edger);
                UASSERT_OBJ(tedger.m_consumesCycle == vtxp->m_isFixedDelayRing, vtxp,
                            "Delay-ring incoming edge kind mismatch");
                const int fi = tedger.fromVtxp()->color();
                UASSERT_OBJ(c.vtx[fi]->datap()->stateSigp, c.vtx[fi],
                            "Delay-ring incoming source missing stateSig");
                AstNodeExpr* contribp = c.vtx[fi]->datap()->stateSigp->cloneTreePure(false);
                contribp = andCond(c.flp, contribp, tedger.m_condp);
                incomingp = orExprs(c.flp, incomingp, contribp);
            }
            UASSERT_OBJ(incomingp, vtxp, "Delay ring has no incoming edge");
            incomingp = gateNotKill(c, incomingp);

            AstNode* updatep = nullptr;
            if (vtxp->m_isFixedDelayRing) {
                updatep = new AstAssign{c.flp,
                                        delayRingBit(c.flp, ringp,
                                                     new AstVarRef{c.flp, evalIdxp, VAccess::READ},
                                                     VAccess::WRITE),
                                        incomingp};
            } else {
                AstAssign* const clearExpirep = new AstAssign{
                    c.flp,
                    delayRingBit(c.flp, ringp, nextRingIndex(c.flp, evalIdxp, size),
                                 VAccess::WRITE),
                    new AstConst{c.flp, AstConst::BitFalse{}}};
                clearExpirep->addNext(new AstAssign{
                    c.flp,
                    delayRingBit(c.flp, ringp, new AstVarRef{c.flp, evalIdxp, VAccess::READ},
                                 VAccess::WRITE),
                    incomingp});
                updatep = clearExpirep;
            }

            AstNodeExpr* clearp = killActive(c);
            if (c.abortAnyVarp) clearp = orExprs(c.flp, clearp, abortActive(c));
            if (vtxp->m_delayRingClearCondp) {
                clearp = orExprs(c.flp, clearp,
                                 sampled(vtxp->m_delayRingClearCondp->cloneTreePure(false)));
            }
            if (vtxp->m_abortClearp) {
                clearp = orExprs(c.flp, clearp,
                                 sampled(vtxp->m_abortClearp->cloneTreePure(false)));
            }
            if (AstNodeExpr* const alivep = oldAttemptAlive(c)) {
                clearp = orExprs(c.flp, clearp, new AstLogNot{c.flp, alivep});
            }
            AstNodeExpr* guardp = nullptr;
            for (AstNodeExpr* const cp : vtxp->m_throughoutConds) {
                AstNodeExpr* const sampledp = sampled(cp->cloneTreePure(false));
                guardp = guardp ? static_cast<AstNodeExpr*>(new AstLogAnd{c.flp, guardp, sampledp})
                                : sampledp;
            }
            if (guardp) clearp = orExprs(c.flp, clearp, new AstLogNot{c.flp, guardp});
            if (clearp) {
                AstConst* const zerop = new AstConst{c.flp, AstConst::DTyped{}, ringp->dtypep()};
                zerop->num().setAllBits0();
                updatep = new AstIf{
                    c.flp, clearp,
                    new AstAssign{c.flp, new AstVarRef{c.flp, ringp, VAccess::WRITE}, zerop},
                    updatep};
            }
            appendStmt(c.updateBodyp, updatep);
            appendStmt(c.updateBodyp,
                       new AstAssign{c.flp, new AstVarRef{c.flp, idxp, VAccess::WRITE},
                                     nextRingIndex(c.flp, evalIdxp, size)});

            UASSERT_OBJ(evalRingp, vtxp, "Delay ring missing evaluation snapshot");
        }
    }

    // Done latches retain early AND endpoints after outcome expressions are captured.
    void emitAndCombinerDoneUpdate(LowerCtx& c) {
        for (int ai = 0; ai < c.N; ++ai) {
            SvaStateVertex* const vtxp = c.vtx[ai];
            if (!vtxp->datap()->doneLVarp) continue;
            UASSERT_OBJ(vtxp->m_andLhsTermp && vtxp->m_andRhsTermp, vtxp,
                        "And-combiner vertex missing LHS/RHS terminal");
            const int l = vtxp->m_andLhsTermp->color();
            const int r = vtxp->m_andRhsTermp->color();
            UASSERT_OBJ(c.vtx[l]->datap()->stateSigp && c.vtx[r]->datap()->stateSigp
                            && vtxp->datap()->stateSigp,
                        vtxp, "And-combiner signals unresolved");

            AstNodeExpr* matchLp
                = buildMatchNow(c.flp, c.vtx[l]->datap()->stateSigp, vtxp->m_andLhsCondp);
            AstNodeExpr* matchRp
                = buildMatchNow(c.flp, c.vtx[r]->datap()->stateSigp, vtxp->m_andRhsCondp);
            matchLp = gateNotKill(c, matchLp);
            matchRp = gateNotKill(c, matchRp);
            matchLp = gateNotAbort(c, matchLp);
            matchRp = gateNotAbort(c, matchRp);

            AstAssign* const clearLp = new AstAssign{
                c.flp, new AstVarRef{c.flp, vtxp->datap()->doneLVarp, VAccess::WRITE},
                new AstConst{c.flp, AstConst::BitFalse{}}};
            clearLp->addNext(new AstAssign{
                c.flp, new AstVarRef{c.flp, vtxp->datap()->doneRVarp, VAccess::WRITE},
                new AstConst{c.flp, AstConst::BitFalse{}}});

            AstAssign* const setLp = new AstAssign{
                c.flp, new AstVarRef{c.flp, vtxp->datap()->doneLVarp, VAccess::WRITE},
                new AstConst{c.flp, AstConst::BitTrue{}}};
            AstIf* const setLIfp = new AstIf{c.flp, matchLp, setLp};
            setLIfp->addNext(new AstIf{
                c.flp, matchRp,
                new AstAssign{c.flp,
                              new AstVarRef{c.flp, vtxp->datap()->doneRVarp, VAccess::WRITE},
                              new AstConst{c.flp, AstConst::BitTrue{}}}});

            AstNodeExpr* clearp
                = orExprs(c.flp, killActive(c), vtxp->datap()->stateSigp->cloneTreePure(false));
            if (c.abortAnyVarp) clearp = orExprs(c.flp, clearp, abortActive(c));
            if (AstNodeExpr* const alivep = oldAttemptAlive(c)) {
                clearp = orExprs(c.flp, clearp, new AstLogNot{c.flp, alivep});
            }
            appendStmt(c.updateBodyp, new AstIf{c.flp, clearp, clearLp, setLIfp});
        }
    }

    static void emitKillAckUpdate(LowerCtx& c) {
        AstAssign* const ackp
            = new AstAssign{c.flp, new AstVarRef{c.flp, c.killVarp, VAccess::WRITE},
                            new AstVarRef{c.flp, c.ctlKillVarp, VAccess::READ}};
        appendStmt(c.updateBodyp, new AstIf{c.flp, killActive(c), ackp, nullptr});
    }

    static void emitDisableEpochUpdate(LowerCtx& c) {
        if (!c.snapshotVarp) return;
        UASSERT_OBJ(c.disableCntVarp, c.senTreep, "snapshotVarp set without disableCntVarp");
        appendStmt(c.updateBodyp,
                   new AstAssign{c.flp, new AstVarRef{c.flp, c.snapshotVarp, VAccess::WRITE},
                                 new AstVarRef{c.flp, c.disableCntVarp, VAccess::READ}});
    }

    // Per-attempt match multiplicity contributed by a ranged-delay ring terminal.
    void emitRangeRingMatchCount(LowerCtx& c, const SvaTransEdge* tep, int fi, SignalSet& sigs) {
        AstCountOnes* const oldCountp = new AstCountOnes{
            c.flp, new AstVarRef{c.flp, c.vtx[fi]->datap()->evalDelayRingVarp, VAccess::READ}};
        oldCountp->dtypeFrom(c.killVarp);
        AstNodeExpr* oldMatchCountp = oldCountp;
        if (AstNodeExpr* const alivep = oldAttemptAlive(c)) {
            oldMatchCountp = gateCount(c, alivep, oldMatchCountp);
        }

        AstNodeExpr* incomingp = nullptr;
        for (const V3GraphEdge& er : tep->fromVtxp()->inEdges()) {
            const SvaTransEdge& inp = static_cast<const SvaTransEdge&>(er);
            if (inp.m_consumesCycle) continue;
            const int incomingFrom = inp.fromVtxp()->color();
            UASSERT_OBJ(c.vtx[incomingFrom]->datap()->stateSigp, inp.fromVtxp(),
                        "Range-ring incoming source missing stateSig");
            AstNodeExpr* contributionp
                = c.vtx[incomingFrom]->datap()->stateSigp->cloneTreePure(false);
            contributionp = andCond(c.flp, contributionp, inp.m_condp);
            incomingp = orExprs(c.flp, incomingp, contributionp);
        }
        UASSERT_OBJ(incomingp, tep->fromVtxp(), "Range ring has no incoming link");
        AstNodeExpr* countp = addCounts(c, oldMatchCountp, boolToCount(c, incomingp));

        AstNodeExpr* gatep = notKillActive(c);
        UASSERT_OBJ(!tep->m_condp, tep->fromVtxp(), "Range terminal condition rides matchCondp");
        if (c.matchCondp) {
            gatep = new AstLogAnd{c.flp, gatep, sampled(c.matchCondp->cloneTreePure(false))};
        }
        if (c.disableExprp) {
            gatep = new AstLogAnd{c.flp, gatep,
                                  new AstLogNot{c.flp, c.disableExprp->cloneTreePure(false)}};
        }
        gatep = gateNotAbort(c, gatep);
        countp = gateCount(c, gatep, countp);
        sigs.matchCountp = addCounts(c, sigs.matchCountp, countp);
    }

    // Phase 3/3a/3b: Compute terminal match/reject signals, required-step reject,
    // throughout-drop reject; clean up intermediate state signals.
    // Phase 3: terminalActive and rejectBase from Links to matchVertex.
    // Builder only adds Links (non-clocked) to matchVertex via addLink in
    // wireMatchAndMidSources. When outPerMidSrcsp is non-null, also collect
    // the per-edge match signal (IEEE 1800-2023 16.14.3 cover sequence: each
    // end-of-match fires the action independently, no OR-fold).
    void computeTerminalMatchAndReject(LowerCtx& c, SignalSet& sigs, OutcomeBuckets* failBucketsp,
                                       OutcomeBuckets* matchBucketsp,
                                       const std::vector<int>& depths,
                                       std::vector<AstNodeExpr*>* outPerMidSrcsp = nullptr) {
        for (const SvaTransEdge* const tedgep : c.edges) {
            if (tedgep->toVtxp() != c.graph.m_matchVertexp) continue;
            const int fi = tedgep->fromVtxp()->color();
            UASSERT_OBJ(c.vtx[fi]->datap()->stateSigp, tedgep->fromVtxp(),
                        "Terminal-link source missing stateSig");

            const bool isRangeRing
                = tedgep->fromVtxp()->m_delayRingSize && !tedgep->fromVtxp()->m_isFixedDelayRing;
            AstNodeExpr* srcSigp = c.vtx[fi]->datap()->stateSigp->cloneTreePure(false);
            srcSigp = andCond(c.flp, srcSigp, tedgep->m_condp);
            if (matchBucketsp && !isRangeRing) {
                AstNodeExpr* matchp = srcSigp->cloneTreePure(false);
                if (c.matchCondp) {
                    matchp = new AstLogAnd{c.flp, matchp,
                                           sampled(c.matchCondp->cloneTreePure(false))};
                }
                // Count simultaneous sibling matches once in their shared depth bucket.
                addAttemptOutcome(c, matchBucketsp, depths, tedgep->fromVtxp()->color(), matchp);
            }
            if (matchBucketsp && isRangeRing) emitRangeRingMatchCount(c, tedgep, fi, sigs);
            if (outPerMidSrcsp) {
                // Gate per-mid matches with matchCondp like the collapsed terminal signal.
                AstNodeExpr* perMidp = srcSigp->cloneTreePure(false);
                if (c.matchCondp) {
                    perMidp = new AstLogAnd{c.flp, perMidp,
                                            sampled(c.matchCondp->cloneTreePure(false))};
                }
                perMidp = gateNotKill(c, perMidp);
                outPerMidSrcsp->push_back(perMidp);
            }

            if (isRangeRing) {
                sigs.terminalActivep
                    = orExprs(c.flp, sigs.terminalActivep, srcSigp->cloneTreePure(false));
                AstVar* const ringp = c.vtx[fi]->datap()->evalDelayRingVarp;
                AstVar* const idxp = c.vtx[fi]->datap()->evalDelayRingIdxVarp;
                const uint32_t size = static_cast<uint32_t>(c.vtx[fi]->m_delayRingSize);
                AstNodeExpr* expirep = gateOldAttempt(
                    c, delayRingBit(c.flp, ringp, nextRingIndex(c.flp, idxp, size)));
                expirep = andCond(c.flp, expirep, tedgep->m_condp);
                if (c.matchCondp) {
                    AstNodeExpr* const failp = new AstLogAnd{
                        c.flp, expirep->cloneTreePure(false),
                        new AstLogNot{c.flp, sampled(c.matchCondp->cloneTreePure(false))}};
                    addAttemptOutcome(c, failBucketsp, depths, fi, failp,
                                      tedgep->fromVtxp()->m_delayRingSize - 1);
                }
                sigs.rejectBasep = orExprs(c.flp, sigs.rejectBasep, expirep);
                VL_DO_DANGLING(srcSigp->deleteTree(), srcSigp);
            } else if (tedgep->fromVtxp()->m_isUnbounded || tedgep->fromVtxp()->m_isAndCombiner) {
                sigs.terminalActivep = orExprs(c.flp, sigs.terminalActivep, srcSigp);
            } else {
                sigs.terminalActivep
                    = orExprs(c.flp, sigs.terminalActivep, srcSigp->cloneTreePure(false));
                if (c.matchCondp) {
                    AstNodeExpr* failp = new AstLogAnd{
                        c.flp, srcSigp->cloneTreePure(false),
                        new AstLogNot{c.flp, sampled(c.matchCondp->cloneTreePure(false))}};
                    failp = gateThroughoutGuards(c, tedgep->fromVtxp(), failp);
                    addAttemptOutcome(c, failBucketsp, depths, fi, failp);
                }
                sigs.rejectBasep = orExprs(c.flp, sigs.rejectBasep, srcSigp);
            }
        }
        // wireMatchAndMidSources always adds a Link from result.termVertexp
        // to m_matchVertexp, so the loop above always sets terminalActivep.
        UASSERT_OBJ(sigs.terminalActivep, c.graph.m_matchVertexp,
                    "No terminal edge to match vertex");
    }

    // Phase 3b: Throughout-drop rejection (IEEE 16.9.9).
    void computeThroughoutReject(LowerCtx& c, SignalSet& sigs, OutcomeBuckets* failBucketsp,
                                 const std::vector<int>& depths) {
        for (int i = 0; i < c.N; ++i) {
            const auto& conds = c.vtx[i]->m_throughoutConds;
            if (conds.empty()) continue;
            if (c.vtx[i]->m_isAndCombiner) continue;
            UASSERT_OBJ(c.vtx[i]->datap()->stateSigp, c.vtx[i],
                        "Throughout-conds vertex missing state representation");
            AstVar* const evalRingp = c.vtx[i]->datap()->evalDelayRingVarp;
            AstNodeExpr* stateExprp = nullptr;
            if (evalRingp && c.vtx[i]->m_isFixedDelayRing) {
                stateExprp = gateOldAttempt(
                    c, new AstRedOr{c.flp, new AstVarRef{c.flp, evalRingp, VAccess::READ}});
            } else {
                stateExprp = c.vtx[i]->datap()->stateSigp->cloneTreePure(false);
            }
            AstNodeExpr* guardp = nullptr;
            for (AstNodeExpr* const cp : conds) {
                AstNodeExpr* const sp = sampled(cp->cloneTreePure(false));
                guardp = guardp ? static_cast<AstNodeExpr*>(new AstLogAnd{c.flp, guardp, sp}) : sp;
            }
            AstNodeExpr* const notGuardp = new AstLogNot{c.flp, guardp};
            AstNodeExpr* const failp = new AstLogAnd{c.flp, stateExprp, notGuardp};
            if (evalRingp && failBucketsp) {
                // Preserve one count per live ring attempt for actions and negated outcomes.
                AstCountOnes* const ringCountp
                    = new AstCountOnes{c.flp, new AstVarRef{c.flp, evalRingp, VAccess::READ}};
                ringCountp->dtypeFrom(c.killVarp);
                AstNodeExpr* countGatep
                    = gateOldAttempt(c, new AstLogNot{c.flp, guardp->cloneTreePure(false)});
                countGatep = gateAttemptOutcome(c, countGatep);
                sigs.failCountp
                    = addCounts(c, sigs.failCountp, gateCount(c, countGatep, ringCountp));
            } else {
                addAttemptOutcome(c, failBucketsp, depths, i, failp->cloneTreePure(false));
            }
            sigs.throughoutRejectp = orExprs(c.flp, sigs.throughoutRejectp, failp);
        }
    }

    SignalSet computeSignals(LowerCtx& c, std::vector<AstNodeExpr*>* outFailAttemptSrcsp,
                             std::vector<AstNodeExpr*>* outMatchAttemptSrcsp, bool needMatchCount,
                             bool* outAmbiguousResolvedDepthp = nullptr,
                             std::vector<AstNodeExpr*>* outPerMidSrcsp = nullptr) {
        SignalSet sigs;
        const std::vector<int> depths = computeAttemptDepths(c);
        OutcomeBuckets failBuckets;
        OutcomeBuckets matchBuckets;
        OutcomeBuckets* const failBucketsp = outFailAttemptSrcsp ? &failBuckets : nullptr;
        OutcomeBuckets* const matchBucketsp
            = (outMatchAttemptSrcsp || needMatchCount || outAmbiguousResolvedDepthp)
                  ? &matchBuckets
                  : nullptr;

        computeTerminalMatchAndReject(c, sigs, failBucketsp, matchBucketsp, depths,
                                      outPerMidSrcsp);

        // Phase 3a: required-step rejection.
        // Builder only sets m_rejectOnFail on non-clocked Links with m_condp
        // or m_condVtxp, and the source always has a resolved stateSig.
        for (const SvaTransEdge* const tedgep : c.edges) {
            if (!tedgep->m_rejectOnFail) continue;
            const int fi = tedgep->fromVtxp()->color();
            UASSERT_OBJ(c.vtx[fi]->datap()->stateSigp && (tedgep->m_condp || tedgep->m_condVtxp),
                        tedgep->fromVtxp(),
                        "rejectOnFail Link must have condp/condVtxp and source stateSig");
            AstNodeExpr* const srcSigp = c.vtx[fi]->datap()->stateSigp->cloneTreePure(false);
            AstNodeExpr* condp = nullptr;
            if (tedgep->m_condVtxp) {
                const int ci = tedgep->m_condVtxp->color();
                UASSERT_OBJ(c.vtx[ci]->datap()->stateSigp, tedgep->m_condVtxp,
                            "rejectOnFail condVtxp missing stateSig");
                condp = c.vtx[ci]->datap()->stateSigp->cloneTreePure(false);
                if (tedgep->m_condp) {
                    condp = new AstLogOr{c.flp, condp, tedgep->m_condp->cloneTreePure(false)};
                }
            } else {
                condp = tedgep->m_condp->cloneTreePure(false);
            }
            AstNodeExpr* const notCondp = new AstLogNot{c.flp, condp};
            AstNodeExpr* const rawFailp = new AstLogAnd{c.flp, srcSigp, notCondp};
            addAttemptOutcome(c, failBucketsp, depths, fi, rawFailp->cloneTreePure(false));
            AstNodeExpr* const failp = gateAttemptOutcome(c, rawFailp);
            sigs.requiredStepRejectp = orExprs(c.flp, sigs.requiredStepRejectp, failp);
        }

        computeThroughoutReject(c, sigs, failBucketsp, depths);
        sigs.terminalActivep = gateNotKill(c, sigs.terminalActivep);
        sigs.rejectBasep = gateNotKill(c, sigs.rejectBasep);
        sigs.throughoutRejectp = gateNotKill(c, sigs.throughoutRejectp);
        sigs.terminalActivep = gateNotAbort(c, sigs.terminalActivep);
        sigs.rejectBasep = gateNotAbort(c, sigs.rejectBasep);
        sigs.throughoutRejectp = gateNotAbort(c, sigs.throughoutRejectp);

        // Free the orphan intermediate state signals (lifetime ends this scope).
        clearStateSignals(c);
        // Fire-edge disable uses the current value; earlier window hops are gated above.
        if (c.disableExprp) {
            // terminalActivep is always set, so gate it unconditionally.
            AstNodeExpr* const notTermp
                = new AstLogNot{c.flp, c.disableExprp->cloneTreePure(false)};
            sigs.terminalActivep = new AstLogAnd{c.flp, sigs.terminalActivep, notTermp};
            if (sigs.rejectBasep) {
                AstNodeExpr* const notDisp
                    = new AstLogNot{c.flp, c.disableExprp->cloneTreePure(false)};
                sigs.rejectBasep = new AstLogAnd{c.flp, sigs.rejectBasep, notDisp};
            }
            if (sigs.throughoutRejectp) {
                AstNodeExpr* const notDisp
                    = new AstLogNot{c.flp, c.disableExprp->cloneTreePure(false)};
                sigs.throughoutRejectp = new AstLogAnd{c.flp, sigs.throughoutRejectp, notDisp};
            }
        }

        if (c.disableExprp) {
            VL_DO_DANGLING(c.disableExprp->deleteTree(), c.disableExprp);
            c.disableExprp = nullptr;
        }

        if (outAmbiguousResolvedDepthp) {
            for (const auto& pair : matchBuckets) {
                if (pair.first < 0) *outAmbiguousResolvedDepthp = true;
            }
        }

        finishAttemptOutcomes(c, failBuckets, outFailAttemptSrcsp);
        finishAttemptOutcomes(c, matchBuckets, outMatchAttemptSrcsp);

        return sigs;
    }

    // Phase 1 seeds: start trigger, registered state reads, delay-ring reads.
    void seedLinkBaseSignals(LowerCtx& c, AstVar* triggerVarp) {
        // datap() was freshly allocated in lower() -- all stateSigp start null.
        AstNodeExpr* startp = new AstVarRef{c.flp, triggerVarp, VAccess::READ};
        if (AstNodeExpr* const alivep = currentEntryAlive(c)) {
            startp = new AstLogAnd{c.flp, startp, alivep};
        }
        c.vtx[c.startIdx]->datap()->stateSigp = startp;
        for (int i = 0; i < c.N; ++i) {
            if (c.vtx[i]->datap()->stateVarp) {
                AstVar* const statep = c.vtx[i]->datap()->evalStateVarp;
                c.vtx[i]->datap()->stateSigp
                    = gateOldAttempt(c, new AstVarRef{c.flp, statep, VAccess::READ});
            } else if (c.vtx[i]->datap()->delayRingVarp) {
                AstVar* const ringp = c.vtx[i]->datap()->evalDelayRingVarp;
                AstVar* const idxp = c.vtx[i]->datap()->evalDelayRingIdxVarp;
                AstNodeExpr* ringStatep = nullptr;
                if (c.vtx[i]->m_isFixedDelayRing) {
                    ringStatep
                        = delayRingBit(c.flp, ringp, new AstVarRef{c.flp, idxp, VAccess::READ});
                } else {
                    ringStatep = new AstRedOr{c.flp, new AstVarRef{c.flp, ringp, VAccess::READ}};
                }
                c.vtx[i]->datap()->stateSigp = gateOldAttempt(c, ringStatep);
            }
        }
    }

    // OR every in-Link contribution (and combiner terminal match) onto the seed.
    void finalizeLinkTarget(LowerCtx& c, int ti) {
        SvaStateVertex* const vtxp = c.vtx[ti];
        AstNodeExpr* sigp = vtxp->datap()->stateSigp;
        if (vtxp->m_isAndCombiner) {
            const int l = vtxp->m_andLhsTermp->color();
            const int r = vtxp->m_andRhsTermp->color();
            if (c.vtx[l]->datap()->stateSigp && c.vtx[r]->datap()->stateSigp) {
                AstNodeExpr* const matchLp
                    = buildMatchNow(c.flp, c.vtx[l]->datap()->stateSigp, vtxp->m_andLhsCondp);
                AstNodeExpr* const matchRp
                    = buildMatchNow(c.flp, c.vtx[r]->datap()->stateSigp, vtxp->m_andRhsCondp);
                AstNodeExpr* matchp = nullptr;
                if (vtxp->m_andNeedsDoneLatches) {
                    UASSERT_OBJ(vtxp->datap()->doneLVarp && vtxp->datap()->doneRVarp, vtxp,
                                "Temporal-and combiner missing done latches");
                    AstNodeExpr* const doneLOrp = new AstLogOr{
                        c.flp, new AstVarRef{c.flp, vtxp->datap()->doneLVarp, VAccess::READ},
                        matchLp};
                    AstNodeExpr* const doneROrp = new AstLogOr{
                        c.flp, new AstVarRef{c.flp, vtxp->datap()->doneRVarp, VAccess::READ},
                        matchRp};
                    AstNodeExpr* const bothp = new AstLogAnd{c.flp, doneLOrp, doneROrp};
                    AstNodeExpr* const oneNowp = new AstLogOr{c.flp, matchLp->cloneTreePure(false),
                                                              matchRp->cloneTreePure(false)};
                    matchp = new AstLogAnd{c.flp, bothp, oneNowp};
                } else {
                    matchp = new AstLogAnd{c.flp, matchLp, matchRp};
                }
                sigp = orExprs(c.flp, sigp, matchp);
            }
        }
        for (const V3GraphEdge& er : vtxp->inEdges()) {
            const SvaTransEdge& te = static_cast<const SvaTransEdge&>(er);
            if (te.m_consumesCycle) continue;
            AstNodeExpr* const srcSigp = te.fromVtxp()->datap()->stateSigp;
            if (!srcSigp) continue;
            sigp = orExprs(c.flp, sigp, andCond(c.flp, srcSigp->cloneTreePure(false), te.m_condp));
        }
        vtxp->datap()->stateSigp = sigp;
    }

    // Phase 1 finalizes each combinational Link after all dependency sources.
    void resolveLinks(LowerCtx& c, AstVar* triggerVarp) {
        seedLinkBaseSignals(c, triggerVarp);
        std::vector<int> pendingDeps(c.N, 0);
        std::vector<std::vector<int>> dependents(c.N);
        for (const SvaTransEdge* const tep : c.edges) {
            if (tep->m_consumesCycle) continue;
            const SvaStateVertex* const top = tep->toVtxp();
            if (top->m_isMatch || top->m_isRejectSink || top->datap()->needsReg) continue;
            pendingDeps[top->color()]++;
            dependents[tep->fromVtxp()->color()].push_back(top->color());
        }
        for (int i = 0; i < c.N; ++i) {
            if (!c.vtx[i]->m_isAndCombiner) continue;
            // Same-end combiner vertices always have both terminal pointers set.
            UASSERT_OBJ(c.vtx[i]->m_andLhsTermp && c.vtx[i]->m_andRhsTermp, c.vtx[i],
                        "Same-end combiner vertex missing LHS/RHS terminal");
            pendingDeps[i] += 2;
            dependents[c.vtx[i]->m_andLhsTermp->color()].push_back(i);
            dependents[c.vtx[i]->m_andRhsTermp->color()].push_back(i);
        }
        std::vector<int> worklist;
        std::vector<bool> finalized(c.N, false);
        for (int i = 0; i < c.N; ++i) {
            if (!pendingDeps[i]) {
                finalized[i] = true;
                worklist.push_back(i);
            }
        }
        while (!worklist.empty()) {
            const int u = worklist.back();
            worklist.pop_back();
            for (const int d : dependents[u]) {
                if (--pendingDeps[d]) continue;
                finalizeLinkTarget(c, d);
                finalized[d] = true;
                worklist.push_back(d);
            }
        }
        for (int i = 0; i < c.N; ++i) {
            UASSERT_OBJ(finalized[i], c.vtx[i], "Combinational Link dependency cycle");
        }
    }

    // Combine terminal/reject signals into final output expression.
    AstNodeExpr* assembleResult(FileLine* flp, bool isCover, bool negated, AstNodeExpr* matchCondp,
                                AstNodeExpr* terminalActivep, AstNodeExpr* rejectBasep,
                                AstNodeExpr* throughoutRejectp, AstNodeExpr* requiredStepRejectp) {
        // Property negation (IEEE 1800-2023 16.12.1 `not`): invert match/reject.
        if (negated) {
            if (isCover) {
                if (terminalActivep)
                    VL_DO_DANGLING(terminalActivep->deleteTree(), terminalActivep);
                AstNodeExpr* negRejectp = nullptr;
                if (matchCondp && rejectBasep) {
                    AstNodeExpr* const sampledCondp = sampled(matchCondp->cloneTreePure(false));
                    AstNodeExpr* const notCondp = new AstLogNot{flp, sampledCondp};
                    negRejectp = new AstLogAnd{flp, rejectBasep, notCondp};
                } else if (rejectBasep) {
                    VL_DO_DANGLING(rejectBasep->deleteTree(), rejectBasep);
                }
                if (throughoutRejectp) negRejectp = orExprs(flp, negRejectp, throughoutRejectp);
                if (requiredStepRejectp)
                    negRejectp = orExprs(flp, negRejectp, requiredStepRejectp);
                return negRejectp ? negRejectp : new AstConst{flp, AstConst::BitFalse{}};
            }
            // Negated assert/assume: output = !match.
            AstNodeExpr* matchp = terminalActivep;
            if (matchCondp) {
                AstNodeExpr* const sampledCondp = sampled(matchCondp->cloneTreePure(false));
                matchp = new AstLogAnd{flp, matchp, sampledCondp};
            }
            if (throughoutRejectp)
                VL_DO_DANGLING(throughoutRejectp->deleteTree(), throughoutRejectp);
            if (rejectBasep) VL_DO_DANGLING(rejectBasep->deleteTree(), rejectBasep);
            if (requiredStepRejectp)
                VL_DO_DANGLING(requiredStepRejectp->deleteTree(), requiredStepRejectp);
            AstNodeExpr* const resultExprp = new AstLogNot{flp, matchp};
            return resultExprp;
        }
        if (isCover) {
            if (throughoutRejectp)
                VL_DO_DANGLING(throughoutRejectp->deleteTree(), throughoutRejectp);
            if (rejectBasep) VL_DO_DANGLING(rejectBasep->deleteTree(), rejectBasep);
            if (requiredStepRejectp)
                VL_DO_DANGLING(requiredStepRejectp->deleteTree(), requiredStepRejectp);
            if (matchCondp) {
                AstNodeExpr* const sampledCondp = sampled(matchCondp->cloneTreePure(false));
                return new AstLogAnd{flp, terminalActivep, sampledCondp};
            }
            return terminalActivep;
        }
        // Assert/assume: output = !reject
        AstNodeExpr* rejectp = nullptr;
        if (matchCondp && rejectBasep) {
            AstNodeExpr* const sampledCondp = sampled(matchCondp->cloneTreePure(false));
            rejectp = new AstLogAnd{flp, rejectBasep, new AstLogNot{flp, sampledCondp}};
        } else if (rejectBasep) {
            VL_DO_DANGLING(rejectBasep->deleteTree(), rejectBasep);
        }
        if (terminalActivep) VL_DO_DANGLING(terminalActivep->deleteTree(), terminalActivep);
        if (throughoutRejectp) rejectp = orExprs(flp, rejectp, throughoutRejectp);
        if (requiredStepRejectp) rejectp = orExprs(flp, rejectp, requiredStepRejectp);
        if (!rejectp) return new AstConst{flp, AstConst::BitTrue{}};
        AstNodeExpr* const resultExprp = new AstLogNot{flp, rejectp};
        return resultExprp;
    }

    // Capture an impure control query once at transaction entry; readers use the var.
    AstVar* emitCtlCapture(LowerCtx& c, const std::string& name, AstNodeExpr* valuep,
                           AstNodeDType* dtypep) {
        AstVar* const varp = new AstVar{c.flp, VVarType::MODULETEMP, name,
                                        dtypep ? dtypep : m_modp->findBitDType()};
        varp->lifetime(VLifetime::STATIC_EXPLICIT);
        m_modp->addStmtsp(varp);
        appendStmt(c.snapshotBodyp,
                   new AstAssign{c.flp, new AstVarRef{c.flp, varp, VAccess::WRITE}, valuep});
        return varp;
    }

    AstNodeExpr* materializeObserved(LowerCtx& c, const std::string& name, AstNodeExpr* exprp,
                                     AstNode*& bodypr, AstNodeDType* dtypep = nullptr) {
        if (!exprp) return nullptr;
        AstVar* const varp = new AstVar{c.flp, VVarType::MODULETEMP, name,
                                        dtypep ? dtypep : m_modp->findBitDType()};
        varp->lifetime(VLifetime::STATIC_EXPLICIT);
        m_modp->addStmtsp(varp);
        appendStmt(bodypr,
                   new AstAssign{c.flp, new AstVarRef{c.flp, varp, VAccess::WRITE}, exprp});
        return new AstVarRef{c.flp, varp, VAccess::READ};
    }

    // Requested-output pointers into a LowerResult; null = not requested
    struct LowerOutputs final {
        AstNodeExpr** abortAnypp = nullptr;  // Any abort fired
        AstNodeExpr** disablepp = nullptr;  // Observed disable reference
        std::vector<AstNodeExpr*>* failAttemptSrcsp = nullptr;  // Per-depth failures
        std::vector<AstNodeExpr*>* matchAttemptSrcsp = nullptr;  // Per-depth matches
        AstNodeExpr** failCountpp = nullptr;  // Extra counted failures
        AstNodeExpr** matchCountpp = nullptr;  // Extra counted matches
        AstNodeExpr** abortPassCountpp = nullptr;  // Forced-accept count
        AstNodeExpr** abortFailCountpp = nullptr;  // Forced-reject count
        AstNodeExpr** strongPendingCountpp = nullptr;  // End-of-sim pending count
        std::vector<AstNodeExpr*>* perMidSrcsp = nullptr;  // Per-end cover signals
    };
    static LowerOutputs bindLowerOutputs(const LowerRequest& req, LowerResult& res) {
        LowerOutputs o;
        o.abortAnypp = req.abortSpecsp && !req.abortSpecsp->empty() ? &res.abortAnyp : nullptr;
        o.disablepp = req.disableExprp ? &res.disableRefp : nullptr;
        o.failAttemptSrcsp = req.wantPerSrcFail ? &res.failAttemptSrcs : nullptr;
        o.matchAttemptSrcsp = req.wantPerSrcMatch ? &res.matchAttemptSrcs : nullptr;
        o.failCountpp = req.wantPerSrcFail ? &res.failCountp : nullptr;
        o.matchCountpp = req.wantPerSrcMatch ? &res.matchCountp : nullptr;
        o.abortPassCountpp = req.wantAbortPassCount ? &res.abortPassCountp : nullptr;
        o.abortFailCountpp = req.wantAbortFailCount ? &res.abortFailCountp : nullptr;
        o.strongPendingCountpp = req.wantStrongPending ? &res.strongPendingCountp : nullptr;
        o.perMidSrcsp = req.wantPerMid ? &res.perMidSrcs : nullptr;
        return o;
    }
    static bool anyStrongPending(const std::vector<SvaStateVertex*>& vtx) {
        for (const SvaStateVertex* const vtxp : vtx) {
            if (vtxp->m_strongPending) return true;
        }
        return false;
    }

    static void pruneSingleFailSource(const LowerRequest& req, const LowerOutputs& o,
                                      const SignalSet& sigs, LowerResult& res) {
        if (!req.pruneSingleFailSource || !o.failAttemptSrcsp) return;
        if (res.failAttemptSrcs.size() > 1 || sigs.failCountp) return;
        for (AstNodeExpr* const srcp : res.failAttemptSrcs) {
            VL_DO_DANGLING(srcp->deleteTree(), srcp);
        }
        res.failAttemptSrcs.clear();
    }

    void materializeLoweringOutputs(LowerCtx& c, const std::string& baseName, SignalSet& sigs,
                                    const LowerOutputs& o, AstNodeExpr* abortPassCountp,
                                    AstNodeExpr* abortFailCountp,
                                    AstNode*& captureBodyp) {
        if (o.abortAnypp) {
            *o.abortAnypp = c.abortAnyVarp ? materializeObserved(c, baseName + "__abortAnyOutcome",
                                                                 abortActive(c), captureBodyp)
                                           : nullptr;
        }
        if (o.failAttemptSrcsp) {
            for (size_t i = 0; i < o.failAttemptSrcsp->size(); ++i) {
                AstNodeExpr*& exprpr = o.failAttemptSrcsp->at(i);
                exprpr = materializeObserved(c, baseName + "__fail" + std::to_string(i), exprpr,
                                             captureBodyp);
            }
        }
        if (o.matchAttemptSrcsp) {
            for (size_t i = 0; i < o.matchAttemptSrcsp->size(); ++i) {
                AstNodeExpr*& exprpr = o.matchAttemptSrcsp->at(i);
                exprpr = materializeObserved(c, baseName + "__matchAttempt" + std::to_string(i),
                                             exprpr, captureBodyp);
            }
        }
        if (o.matchCountpp) {
            *o.matchCountpp = materializeObserved(c, baseName + "__matchCount", sigs.matchCountp,
                                                  captureBodyp, m_u32DTypep);
        } else {
            UASSERT_OBJ(!sigs.matchCountp, c.flp, "Match count built without a requested output");
        }
        if (o.failCountpp) {
            *o.failCountpp = materializeObserved(c, baseName + "__failCount", sigs.failCountp,
                                                 captureBodyp, m_u32DTypep);
        } else {
            UASSERT_OBJ(!sigs.failCountp, c.flp, "Fail count built without a requested output");
        }
        if (o.abortPassCountpp) {
            *o.abortPassCountpp = materializeObserved(c, baseName + "__abortPassCount",
                                                      abortPassCountp, captureBodyp, m_u32DTypep);
        } else if (abortPassCountp) {
            VL_DO_DANGLING(abortPassCountp->deleteTree(), abortPassCountp);
        }
        if (o.abortFailCountpp) {
            *o.abortFailCountpp = materializeObserved(c, baseName + "__abortFailCount",
                                                      abortFailCountp, captureBodyp, m_u32DTypep);
        } else if (abortFailCountp) {
            VL_DO_DANGLING(abortFailCountp->deleteTree(), abortFailCountp);
        }
        if (o.perMidSrcsp) {
            for (size_t i = 0; i < o.perMidSrcsp->size(); ++i) {
                AstNodeExpr*& exprpr = o.perMidSrcsp->at(i);
                exprpr = materializeObserved(c, baseName + "__mid" + std::to_string(i), exprpr,
                                             captureBodyp);
            }
        }
    }

    struct LowerVars final {
        int N = 0;  // Number of vertices
        std::vector<SvaStateVertex*> vtx;  // Color-indexed vertex lookup
        std::vector<std::unique_ptr<SvaVertexData>> vertexData;  // Per-vertex lowering data
        int startIdx = 0;  // Start vertex color index
        int matchIdx = -1;  // Match vertex color index (-1 if none)
        std::vector<const SvaTransEdge*> edges;  // All edges (flat)
        AstVar* killVarp = nullptr;  // Last observed kill generation
        AstVar* evalKillVarp = nullptr;  // Pre-update kill generation used for the verdict
        AstNode* disableCapturep = nullptr;  // Observed disable capture statement
    };
    void allocateVertexStateVars(FileLine* flp, const std::string& baseName, LowerVars& lv) {
        std::vector<SvaStateVertex*>& vtx = lv.vtx;
        for (int i = 0; i < lv.N; ++i) {
            if (vtx[i]->m_andNeedsDoneLatches) {
                const std::string base = baseName + "__a" + std::to_string(i);
                AstVar* const lp = new AstVar{flp, VVarType::MODULETEMP, base + "_doneL",
                                              m_modp->findBitDType()};
                lp->lifetime(VLifetime::STATIC_EXPLICIT);
                m_modp->addStmtsp(lp);
                vtx[i]->datap()->doneLVarp = lp;
                AstVar* const rp = new AstVar{flp, VVarType::MODULETEMP, base + "_doneR",
                                              m_modp->findBitDType()};
                rp->lifetime(VLifetime::STATIC_EXPLICIT);
                m_modp->addStmtsp(rp);
                vtx[i]->datap()->doneRVarp = rp;
                continue;
            }
            if (vtx[i]->m_delayRingSize) {
                const std::string base = baseName + "__d" + std::to_string(i);
                AstNodeDType* const ringDTypep = m_modp->findLogicDType(
                    vtx[i]->m_delayRingSize, vtx[i]->m_delayRingSize, VSigning::UNSIGNED);
                AstVar* const ringp
                    = new AstVar{flp, VVarType::MODULETEMP, base + "_ring", ringDTypep};
                ringp->lifetime(VLifetime::STATIC_EXPLICIT);
                m_modp->addStmtsp(ringp);
                vtx[i]->datap()->delayRingVarp = ringp;
                AstVar* const evalRingp
                    = new AstVar{flp, VVarType::MODULETEMP, base + "_ringEval", ringDTypep};
                evalRingp->lifetime(VLifetime::STATIC_EXPLICIT);
                m_modp->addStmtsp(evalRingp);
                vtx[i]->datap()->evalDelayRingVarp = evalRingp;
                AstVar* const idxp
                    = new AstVar{flp, VVarType::MODULETEMP, base + "_idx", m_u32DTypep};
                idxp->lifetime(VLifetime::STATIC_EXPLICIT);
                m_modp->addStmtsp(idxp);
                vtx[i]->datap()->delayRingIdxVarp = idxp;
                AstVar* const evalIdxp
                    = new AstVar{flp, VVarType::MODULETEMP, base + "_idxEval", m_u32DTypep};
                evalIdxp->lifetime(VLifetime::STATIC_EXPLICIT);
                m_modp->addStmtsp(evalIdxp);
                vtx[i]->datap()->evalDelayRingIdxVarp = evalIdxp;
                continue;
            }
            if (!vtx[i]->datap()->needsReg) continue;
            if (i == lv.startIdx || vtx[i]->m_isMatch) continue;
            const std::string varName = baseName + "__s" + std::to_string(i);
            AstVar* const varp
                = new AstVar{flp, VVarType::MODULETEMP, varName, m_modp->findBitDType()};
            varp->lifetime(VLifetime::STATIC_EXPLICIT);
            m_modp->addStmtsp(varp);
            vtx[i]->datap()->stateVarp = varp;
            AstVar* const evalVarp
                = new AstVar{flp, VVarType::MODULETEMP, varName + "Eval", m_modp->findBitDType()};
            evalVarp->lifetime(VLifetime::STATIC_EXPLICIT);
            m_modp->addStmtsp(evalVarp);
            vtx[i]->datap()->evalStateVarp = evalVarp;
        }
    }
    LowerVars allocateLoweringVars(FileLine* flp, SvaGraph& graph, const std::string& baseName,
                                   AstNodeExpr*& disableExprp,
                                   AstNodeExpr** outDisablepp) {
        LowerVars lv;
        int& N = lv.N;
        for (V3GraphVertex& vtxr : graph.m_graph.vertices()) { vtxr.color(N++); }
        std::vector<SvaStateVertex*>& vtx = lv.vtx;
        vtx.assign(N, nullptr);
        for (V3GraphVertex& vtxr : graph.m_graph.vertices()) {
            vtx[vtxr.color()] = static_cast<SvaStateVertex*>(&vtxr);
        }
        lv.startIdx = graph.m_startVertexp->color();
        lv.matchIdx = graph.m_matchVertexp ? graph.m_matchVertexp->color() : -1;
        lv.edges = graph.allEdges();

        lv.vertexData.resize(N);
        for (int i = 0; i < N; ++i) {
            lv.vertexData[i] = std::make_unique<SvaVertexData>();
            vtx[i]->userp(lv.vertexData[i].get());
        }

        for (int i = 0; i < N; ++i) {
            for (const V3GraphEdge& er : vtx[i]->outEdges()) {
                const SvaTransEdge& te = static_cast<const SvaTransEdge&>(er);
                const int toIdx = te.toVtxp()->color();
                if (te.m_consumesCycle && toIdx != lv.matchIdx && !te.toVtxp()->m_isRejectSink) {
                    vtx[toIdx]->datap()->needsReg = true;
                }
            }
        }

        lv.killVarp = new AstVar{flp, VVarType::MODULETEMP, baseName + "__kill", m_u32DTypep};
        lv.killVarp->lifetime(VLifetime::STATIC_EXPLICIT);
        m_modp->addStmtsp(lv.killVarp);
        lv.evalKillVarp
            = new AstVar{flp, VVarType::MODULETEMP, baseName + "__killEval", m_u32DTypep};
        lv.evalKillVarp->lifetime(VLifetime::STATIC_EXPLICIT);
        m_modp->addStmtsp(lv.evalKillVarp);
        allocateVertexStateVars(flp, baseName, lv);

        if (disableExprp) {
            AstVar* const disableObservedp = new AstVar{
                flp, VVarType::MODULETEMP, baseName + "__disable", m_modp->findBitDType()};
            disableObservedp->lifetime(VLifetime::STATIC_EXPLICIT);
            m_modp->addStmtsp(disableObservedp);
            lv.disableCapturep = new AstAssign{
                flp, new AstVarRef{flp, disableObservedp, VAccess::WRITE}, disableExprp};
            disableExprp = new AstVarRef{flp, disableObservedp, VAccess::READ};
            if (outDisablepp) {
                *outDisablepp = new AstVarRef{flp, disableObservedp, VAccess::READ};
            }
        }
        return lv;
    }

    void finalizeStrongPending(LowerCtx& c, bool trackStrongResolved, bool ambiguousResolvedDepth,
                               AstNodeExpr** outStrongPendingCountpp) {
        FileLine* const flp = c.flp;
        AstNodeExpr* pendingCountp
            = buildStrongPendingCount(c, trackStrongResolved, ambiguousResolvedDepth);
        if (pendingCountp) {
            AstNodeExpr* gatep = oldAttemptAlive(c);
            AstNodeExpr* const notKilledp
                = new AstEq{flp, new AstVarRef{flp, c.killVarp, VAccess::READ},
                            assertKillGet(flp, c.assertType, c.directiveType)};
            gatep = gatep ? static_cast<AstNodeExpr*>(new AstLogAnd{flp, gatep, notKilledp})
                          : notKilledp;
            pendingCountp = gateCount(c, gatep, pendingCountp);
        }
        if (outStrongPendingCountpp) {
            *outStrongPendingCountpp = pendingCountp;
        } else if (pendingCountp) {
            VL_DO_DANGLING(pendingCountp->deleteTree(), pendingCountp);
        }
    }

    AstNodeExpr* applyAbortToResult(LowerCtx& c, AstNodeExpr* activeAttemptCountp, bool isCover,
                                    bool negated, AstNodeExpr* matchCondp, SignalSet& sigs,
                                    AstNodeExpr*& abortPassCountp, AstNodeExpr*& abortFailCountp) {
        FileLine* const flp = c.flp;
        AstNodeExpr* abortPassp = nullptr;
        AstNodeExpr* abortFailp = nullptr;
        abortPassCountp = nullptr;
        abortFailCountp = nullptr;
        if (activeAttemptCountp) {
            abortPassCountp = gateCount(c, new AstVarRef{flp, c.abortAcceptVarp, VAccess::READ},
                                        activeAttemptCountp->cloneTreePure(false));
            abortFailCountp = gateCount(c, new AstVarRef{flp, c.abortRejectVarp, VAccess::READ},
                                        activeAttemptCountp->cloneTreePure(false));
            abortPassp = new AstNeq{flp, abortPassCountp->cloneTreePure(false),
                                    new AstConst{flp, AstConst::WidthedValue{}, 32, 0}};
            abortFailp = new AstNeq{flp, abortFailCountp->cloneTreePure(false),
                                    new AstConst{flp, AstConst::WidthedValue{}, 32, 0}};
            VL_DO_DANGLING(activeAttemptCountp->deleteTree(), activeAttemptCountp);
        }

        AstNodeExpr* resultp
            = assembleResult(flp, isCover, negated, matchCondp, sigs.terminalActivep,
                             sigs.rejectBasep, sigs.throughoutRejectp, sigs.requiredStepRejectp);
        if (abortPassp) {
            UASSERT_OBJ(abortFailp, c.graph.m_startVertexp,
                        "Abort pass verdict without fail verdict");
            if (isCover) {
                resultp = new AstLogOr{flp, abortPassp->cloneTreePure(false), resultp};
            } else {
                resultp = new AstLogOr{
                    flp, abortPassp->cloneTreePure(false),
                    new AstLogAnd{flp, new AstLogNot{flp, abortFailp->cloneTreePure(false)},
                                  resultp}};
            }
            VL_DO_DANGLING(abortPassp->deleteTree(), abortPassp);
            VL_DO_DANGLING(abortFailp->deleteTree(), abortFailp);
        }
        return resultp;
    }

public:
    explicit SvaNfaLowering(AstNodeModule* modp)
        : m_modp{modp}
        , m_u32DTypep{modp->findBasicDType(VBasicDTypeKwd::UINT32)} {}
    ~SvaNfaLowering() {
        V3Stats::addStatSum("Assertions, NFA delay ring edge visits", m_statDelayRingEdgeVisits);
    }

    // Lower snapshot, verdict, and commit into Observed; actions execute in Reactive.
    LowerResult lower(FileLine* flp, SvaGraph& graph, const LowerRequest& req) {
        LowerResult res;
        const LowerOutputs o = bindLowerOutputs(req, res);
        AstNodeExpr* disableExprp = req.disableExprp;

        const std::string baseName = m_names.get("");
        LowerVars lv
            = allocateLoweringVars(flp, graph, baseName, disableExprp, o.disablepp);
        const int N = lv.N;
        std::vector<SvaStateVertex*>& vtx = lv.vtx;

        // Build lowering context for phase sub-functions.
        LowerCtx c{flp, graph};
        c.N = N;
        c.vtx = vtx;
        c.edges = lv.edges;
        c.startIdx = lv.startIdx;
        c.matchIdx = lv.matchIdx;
        c.senTreep = req.senTreep;
        c.disableExprp = disableExprp;
        c.matchCondp = req.matchCondp;
        c.disableCntVarp = req.disableCntVarp;
        c.snapshotVarp = req.snapshotVarp;
        c.assertType = req.assertType;
        c.directiveType = req.directiveType;
        c.killVarp = lv.killVarp;
        c.evalKillVarp = lv.evalKillVarp;
        c.snapshotBodyp = lv.disableCapturep;

        c.ctlKillVarp
            = emitCtlCapture(c, baseName + "__ctlKill",
                             assertKillGet(flp, req.assertType, req.directiveType), m_u32DTypep);
        AstVar* const ctlOnVarp
            = emitCtlCapture(c, baseName + "__ctlOn", req.triggerExprp->cloneTree(false), nullptr);
        emitAbortCapture(c, baseName, req.abortSpecsp);
        emitEvaluationSnapshots(c);

        // Phase 1: Resolve combinational Links via fixed-point propagation.
        resolveLinks(c, ctlOnVarp);

        AstNodeExpr* const activeAttemptCountp
            = o.abortAnypp ? computeActiveAttemptCount(c) : nullptr;

        // Phase 2: update registered state, delay rings, endpoint latches, and epochs.
        emitAndCombinerDoneUpdate(c);
        emitStateUpdate(c);
        emitDelayRingUpdate(c);
        emitKillAckUpdate(c);
        emitDisableEpochUpdate(c);

        const bool trackStrongResolved
            = o.strongPendingCountpp && anyStrongPending(vtx) && graph.m_hasOrMerge;
        if (trackStrongResolved && o.matchAttemptSrcsp) {
            flp->v3warn(E_UNSUPPORTED,
                        "Unsupported: pass-action multiplicity for strong s_always in a "
                        "temporal OR composite cannot preserve resolved attempts");
        }
        bool ambiguousResolvedDepth = false;

        // Phase 3/3a/3b: Compute terminal match/reject signals (cleans up stateSig).
        SignalSet sigs = computeSignals(
            c, o.failAttemptSrcsp, o.matchAttemptSrcsp, o.matchCountpp != nullptr,
            trackStrongResolved ? &ambiguousResolvedDepth : nullptr, o.perMidSrcsp);

        pruneSingleFailSource(req, o, sigs, res);

        AstNodeExpr* abortPassCountp = nullptr;
        AstNodeExpr* abortFailCountp = nullptr;
        AstNodeExpr* resultp
            = applyAbortToResult(c, activeAttemptCountp, req.isCover, req.negated, req.matchCondp,
                                 sigs, abortPassCountp, abortFailCountp);

        AstNode* captureBodyp = nullptr;
        resultp = materializeObserved(c, baseName + "__result", resultp, captureBodyp);
        materializeLoweringOutputs(c, baseName, sigs, o, abortPassCountp, abortFailCountp,
                                   captureBodyp);

        // Strong EOS pending count; ambiguous resolved-match depths fall back gracefully.
        finalizeStrongPending(c, trackStrongResolved, ambiguousResolvedDepth,
                              o.strongPendingCountpp);

        AstNode* observedBodyp = c.snapshotBodyp;
        appendStmt(observedBodyp, captureBodyp);
        appendStmt(observedBodyp, c.updateBodyp);
        AstNodeExpr* const notFinishp
            = new AstLogNot{flp, new AstCExpr{flp,
                                              "(vlSymsp->_vm_contextp__->finishPending()"
                                              " || vlSymsp->_vm_contextp__->gotFinish())",
                                              1}};
        m_modp->addStmtsp(new AstAlwaysObserved{flp, req.senTreep->cloneTree(false),
                                                new AstIf{flp, notFinishp, observedBodyp}});

        // Clear userp on every vertex before vertexData unique_ptrs are destroyed.
        for (int i = 0; i < N; ++i) vtx[i]->userp(nullptr);
        res.outputExprp = resultp;
        return res;
    }
};

}  // namespace

//######################################################################
// Top-level visitor

class AssertNfaVisitor final : public VNVisitor {
    // STATE
    AstNodeModule* m_modp = nullptr;  // Current module being processed
    AstClocking* m_defaultClockingp = nullptr;  // Default clocking
    AstDefaultDisable* m_defaultDisablep = nullptr;  // Default disable iff
    SvaNfaLowering* m_loweringp = nullptr;  // NFA-to-hardware lowering engine
    AstSenTree* m_sampledValueClockp = nullptr;  // Inherited clock during scoped attachment
    V3UniqueNames m_propVarNames{"__Vpropvar"};  // Property-local variable names
    V3UniqueNames m_disableCntNames{"__VnfaDis"};  // Disable-iff counter names
    V3UniqueNames m_disableSampleNames{"__VnfaDisSample"};
    V3UniqueNames m_propTempNames{"__VnfaSampled"};  // Hoisted $sampled(propp) temps
    V3UniqueNames m_actionCountNames{"__VnfaActionCount"};
    std::unordered_set<const AstProperty*> m_inliningProps;  // Recursion guard

    template <typename T_Node>
    void visitSampledValue(T_Node* const nodep) {
        if (m_sampledValueClockp && !nodep->sentreep()) {
            nodep->sentreep(m_sampledValueClockp->cloneTree(true));
        }
        iterateChildren(nodep);
    }

    // Wire match vertex and mid-window sources for a successful NFA build.
    static void wireMatchAndMidSources(SvaGraph& graph, const BuildResult& result, FileLine* flp) {
        graph.createMatchVertex();
        // Skip the main term Link when midSources already cover every
        // end-of-match (cover_sequence path); otherwise the per-mid extraction
        // double-counts via the merge vertex.
        if (!result.termIsMidMerge) { graph.addLink(result.termVertexp, graph.m_matchVertexp); }
        for (SvaStateVertex* srcVtxp : result.midSources) {
            AstNodeExpr* condp = nullptr;
            for (AstNodeExpr* const tc : srcVtxp->m_throughoutConds) {
                AstNodeExpr* const tcClone = tc->cloneTreePure(false);
                condp = condp ? new AstLogAnd{flp, condp, tcClone} : tcClone;
            }
            graph.addLink(srcVtxp, graph.m_matchVertexp, condp);
            srcVtxp->m_isUnbounded = true;
        }
    }

    static AstNodeExpr* getSequenceBodyExprp(const AstSequence* seqp) {
        AstNode* bodyp = seqp->stmtsp();
        while (bodyp && VN_IS(bodyp, Var)) bodyp = bodyp->nextp();
        return VN_CAST(bodyp, NodeExpr);
    }

    static AstPropSpec* getPropertySpecp(const AstProperty* propp) {
        AstNode* stmtp = propp->stmtsp();
        // V3LinkParse emits InitialStaticStmt for property-local variable
        // initialisers; the InitialAutomaticStmt variant only appears for
        // task/function-scope automatic lifetime, not properties.
        while (stmtp
               && (VN_IS(stmtp, Var) || VN_IS(stmtp, InitialStaticStmt)
                   || VN_IS(stmtp, InitialAutomaticStmt))) {  // LCOV_EXCL_LINE
            stmtp = stmtp->nextp();
        }
        return VN_CAST(stmtp, PropSpec);
    }

    void inlineNamedProperty(AstPropSpec* outerSpecp, AstFuncRef* funcrefp,
                             const AstProperty* propyp) {
        // Recursion guard: IEEE 1800-2023 16.12.1 forbids recursive properties.
        // V3Width emits "Recursive property call" for direct recursion before this
        // pass runs; this catches any nested-inlining cycle that slips past.
        if (m_inliningProps.count(propyp)) {
            funcrefp->v3error("Illegal recursive property reference");  // LCOV_EXCL_LINE
            return;  // LCOV_EXCL_LINE
        }
        m_inliningProps.insert(propyp);
        struct Guard final {
            std::unordered_set<const AstProperty*>& setr;
            const AstProperty* keyp;
            ~Guard() { setr.erase(keyp); }
        } guard{m_inliningProps, propyp};
        AstPropSpec* propSpecp = getPropertySpecp(propyp);
        UASSERT_OBJ(propSpecp, funcrefp, "Property has no body PropSpec");
        propSpecp = propSpecp->cloneTree(false);

        const V3TaskConnects tconnects = V3Task::taskConnects(funcrefp, propyp->stmtsp());
        std::unordered_map<const AstVar*, AstNodeExpr*> portMap;
        for (const auto& tconnect : tconnects) {
            portMap[tconnect.first] = tconnect.second->exprp();
        }

        // Promote property-local variables to module-level temps (IEEE 16.10).
        std::unordered_map<const AstVar*, AstVar*> localVarMap;
        for (AstNode* stmtp = propyp->stmtsp(); stmtp; stmtp = stmtp->nextp()) {
            if (AstVar* const varp = VN_CAST(stmtp, Var)) {
                if (!varp->isIO()) {
                    const string newName = m_propVarNames.get(varp);
                    AstVar* const newVarp = new AstVar{varp->fileline(), VVarType::MODULETEMP,
                                                       newName, varp->dtypep()};
                    newVarp->lifetime(VLifetime::STATIC_EXPLICIT);
                    m_modp->addStmtsp(newVarp);
                    localVarMap[varp] = newVarp;
                }
            }
        }

        propSpecp->foreach([&](AstVarRef* refp) {
            const auto portIt = portMap.find(refp->varp());
            if (portIt != portMap.end()) {
                refp->replaceWith(portIt->second->cloneTree(false));
                VL_DO_DANGLING(pushDeletep(refp), refp);
                return;
            }
            const auto localIt = localVarMap.find(refp->varp());
            if (localIt != localVarMap.end()) refp->varp(localIt->second);
        });  // LCOV_EXCL_LINE -- gcov attributes lambda's implicit return to `})`

        for (const auto& tconnect : tconnects) {
            pushDeletep(tconnect.second->exprp()->unlinkFrBack());
        }

        // Merge disable iff (IEEE 1800-2023 16.12.1)
        if (outerSpecp->disablep() && propSpecp->disablep()) {
            outerSpecp->v3error("disable iff expression before property call "
                                "and in its body is not legal");
            pushDeletep(propSpecp->disablep()->unlinkFrBack());
        }
        if (outerSpecp->disablep()) {
            propSpecp->disablep(outerSpecp->disablep()->unlinkFrBack());
        }

        if (outerSpecp->sensesp() && propSpecp->sensesp()) {
            outerSpecp->v3warn(E_UNSUPPORTED,
                               "Unsupported: Clock event before property call and in its body");
            pushDeletep(propSpecp->sensesp()->unlinkFrBack());
        }
        if (outerSpecp->sensesp()) {
            AstSenItem* const sensesp = outerSpecp->sensesp();
            sensesp->unlinkFrBack();
            propSpecp->sensesp(sensesp);
        }

        outerSpecp->replaceWith(propSpecp);
        VL_DO_DANGLING(pushDeletep(outerSpecp), outerSpecp);
    }

    void inlineSequenceRef(AstFuncRef* funcrefp, AstSequence* seqp) {
        AstNodeExpr* const bodyExprp = getSequenceBodyExprp(seqp);
        UASSERT_OBJ(bodyExprp, funcrefp, "Sequence has no body expression");
        AstNodeExpr* const clonedp = bodyExprp->cloneTree(false);

        const V3TaskConnects tconnects = V3Task::taskConnects(funcrefp, seqp->stmtsp());
        std::unordered_map<const AstVar*, AstNodeExpr*> portMap;
        for (const auto& tconnect : tconnects) {
            portMap[tconnect.first] = tconnect.second->exprp();
        }
        clonedp->foreach([&](AstVarRef* refp) {
            const auto it = portMap.find(refp->varp());
            if (it != portMap.end()) {
                refp->replaceWith(it->second->cloneTree(false));
                VL_DO_DANGLING(pushDeletep(refp), refp);
            }
        });
        for (const auto& tconnect : tconnects) {
            pushDeletep(tconnect.second->exprp()->unlinkFrBack());
        }
        funcrefp->replaceWith(clonedp);
        VL_DO_DANGLING(pushDeletep(funcrefp), funcrefp);
        // Clear referenced flag so V3AssertPre cleanup does not emit
        // spurious UNSUPPORTED for sequences that were already inlined here.
        seqp->isReferenced(false);
    }

    // Must run before hasMultiCycleExpr() so NFA sees sequence bodies.
    void inlineAllSequenceRefs(AstNode* rootp) {
        bool changed = true;
        while (changed) {
            changed = false;
            rootp->foreach([&](AstFuncRef* funcrefp) {
                if (changed) return;
                if (AstSequence* const seqp = VN_CAST(funcrefp->taskp(), Sequence)) {
                    inlineSequenceRef(funcrefp, seqp);
                    changed = true;
                }
            });
        }
    }

    static bool hasMultiCycleExpr(const AstNode* nodep) {
        return nodep->exists([](const AstNode* np) {
            if (const auto* const ep = VN_CAST(np, NodeExpr)) return ep->isMultiCycleSva();
            return false;
        });
    }

    static VPropStrength effectiveAssertPropStrength(const AstPropSpec* const propSpecp) {
        if (propSpecp->propStrength() != VPropStrength::DEFAULT) return propSpecp->propStrength();
        return propSpecp->fileline()->language() <= V3LangCode::L1800_2005 ? VPropStrength::STRONG
                                                                           : VPropStrength::WEAK;
    }

    // Bare `assert property (p until q)` with boolean operands stays on
    // V3AssertPre's AstLoop lowering, which preserves per-attempt action-block
    // firings that this NFA's single-bit aggregated state cannot. Strong bare
    // forms are also lowered there. NFA still owns sequence operands and any
    // embedding inside a multi-cycle context (implication consequent, or/and
    // operands, etc.).
    static bool isBareTopLevelUntil(AstNode* propp) {
        AstNode* p = propp;
        if (AstPropSpec* const specp = VN_CAST(p, PropSpec)) p = specp->propp();
        while (AstLogNot* const notp = VN_CAST(p, LogNot)) p = notp->lhsp();
        AstUntil* const untilp = VN_CAST(p, Until);
        if (!untilp) return false;
        return !containsMultiCycleSva(untilp->lhsp()) && !containsMultiCycleSva(untilp->rhsp());
    }

    struct PropertyParts final {
        AstNodeExpr* triggerExprp = nullptr;
        AstNodeExpr* seqExprp = nullptr;
        bool isOverlapped = true;
        bool hasImplication = false;
        bool isFollowedBy = false;  // True for #-# / #=# (non-vacuous-fail on antecedent miss)
    };

    static PropertyParts decomposeProperty(AstNode* propp) {
        PropertyParts parts;
        if (AstPropSpec* const specp = VN_CAST(propp, PropSpec)) { propp = specp->propp(); }
        if (AstImplication* const implp = VN_CAST(propp, Implication)) {
            parts.hasImplication = true;
            parts.isOverlapped = implp->isOverlapped();
            parts.isFollowedBy = implp->isFollowedBy();
            parts.triggerExprp = implp->lhsp();
            parts.seqExprp = implp->rhsp();
        } else if (AstNodeExpr* const exprp = VN_CAST(propp, NodeExpr)) {
            parts.triggerExprp = nullptr;
            parts.seqExprp = exprp;
        }
        return parts;
    }

    static std::vector<AbortSpec> peelAbortPrefix(AstNodeExpr*& exprpr) {
        std::vector<AbortSpec> result;
        while (AstAbortOn* const abortp = VN_CAST(exprpr, AbortOn)) {
            result.push_back({abortp->kind(), abortp->condp(), abortp});
            exprpr = abortp->propp();
        }
        return result;
    }

    static bool isLinearAbortBody(AstNodeExpr* nodep) {
        if (AstImplication* const implp = VN_CAST(nodep, Implication)) {
            return !hasMultiCycleExpr(implp->lhsp()) && isLinearAbortBody(implp->rhsp());
        }
        if (AstSExpr* const sexprp = VN_CAST(nodep, SExpr)) {
            AstDelay* const delayp = VN_CAST(sexprp->delayp(), Delay);
            if (!delayp || !delayp->isCycleDelay() || delayp->isUnbounded()) return false;
            if (delayp->isRangeDelay() && sexprp->exprp()->isMultiCycleSva()) return false;
            return (!sexprp->preExprp() || isLinearAbortBody(sexprp->preExprp()))
                   && isLinearAbortBody(sexprp->exprp());
        }
        if (AstPropAlways* const alwaysp = VN_CAST(nodep, PropAlways)) {
            return !VN_IS(alwaysp->hiBoundp(), Unbounded) && !hasMultiCycleExpr(alwaysp->propp());
        }
        if (AstLogNot* const notp = VN_CAST(nodep, LogNot)) {
            return isLinearAbortBody(notp->lhsp());
        }
        if (VN_IS(nodep, AbortOn)) return false;
        return !nodep->isMultiCycleSva();
    }

    static bool canSplitImplicationPassActions(const PropertyParts& parts) {
        UASSERT(parts.hasImplication,
                "Implication pass action split requested without implication");
        UASSERT(parts.triggerExprp, "Implication pass action split requested without trigger");
        // Direct vacuous/nonvacuous classification uses the antecedent value in the current
        // assertion attempt. Leave delayed antecedents on the existing NFA pass path.
        return !hasMultiCycleExpr(parts.triggerExprp);
    }

    void splitImplicationPassActions(AstAssert* assertp, AstPropSpec* propSpecp,
                                     const PropertyParts& parts, AstNodeExpr* nonvacuousCountp,
                                     bool includeVacuous, AstNodeExpr* abortAnyp = nullptr) {
        FileLine* const flp = assertp->fileline();

        AstNode* const passsp = assertp->passsp()->unlinkFrBackWithNext();
        AstNode* splitsp = nullptr;

        if (!parts.isFollowedBy && includeVacuous) {
            AstNodeExpr* vacuousp
                = new AstLogNot{flp, sampled(parts.triggerExprp->cloneTreePure(false))};
            // IEEE 1800-2023 16.12.14 gives abort priority over same-step completion.
            if (abortAnyp) {
                vacuousp = new AstLogAnd{flp, vacuousp,
                                         new AstLogNot{flp, abortAnyp->cloneTreePure(false)}};
            }
            AstNode* const vacuousBodyp = passsp->cloneTree(true);
            splitsp = newPassOnIf(flp, vacuousp, vacuousBodyp, assertp->userType(),
                                  assertp->directive(), /*vacuous=*/true);
        }

        AstNodeExpr* const nonvacuousCondp
            = new AstNeq{flp, nonvacuousCountp->cloneTreePure(false),
                         new AstConst{flp, AstConst::WidthedValue{}, 32, 0}};
        AstIf* const nonvacuousIfp
            = newPassOnIf(flp, nonvacuousCondp, repeatAction(flp, nonvacuousCountp, passsp),
                          assertp->userType(), assertp->directive(), /*vacuous=*/false);
        splitsp = splitsp ? AstNode::addNext<AstNode, AstNode>(splitsp, nonvacuousIfp)
                          : static_cast<AstNode*>(nonvacuousIfp);
        if (!assertp->failsp()) assertp->addFailsp(new AstComment{flp, ""});
        AstAssert* const handlerp = new AstAssert{
            flp,
            clonePropSpecWithBody(propSpecp, new AstConst{flp, AstConst::BitTrue{}}),
            splitsp,
            nullptr,
            assertp->userType(),
            assertp->directive(),
            assertp->name()};
        if (assertp->sentreep()) handlerp->sentreep(assertp->sentreep()->cloneTree(false));
        handlerp->senFromAlways(assertp->senFromAlways());
        handlerp->nfaLowered(true);
        assertp->addNextHere(handlerp);
    }

    // Allocate disable-iff counter + snapshot vars. Returns {cntp, snapp} or
    // {nullptr, nullptr} if no counter is needed.
    struct DisableVars final {
        AstVar* cntp = nullptr;
        AstVar* snapp = nullptr;
    };

    AstNodeExpr* normalizeDisableExpr(AstNodeExpr* disableExprp, AstSenTree* senTreep) {
        FileLine* const flp = disableExprp->fileline();
        AstNodeExpr* const normalizedp
            = new AstLogNot{flp, new AstLogNot{flp, disableExprp->cloneTreePure(false)}};
        std::vector<AstSampled*> sampleps;
        normalizedp->foreach([&sampleps](AstSampled* const nodep) { sampleps.push_back(nodep); });
        std::unordered_set<const AstSampled*> nestedps;
        for (AstSampled* const samplep : sampleps) {
            samplep->exprp()->foreach(
                [&nestedps](AstSampled* const nodep) { nestedps.insert(nodep); });
        }
        AstNode* sampleBodyp = nullptr;
        for (AstSampled* const samplep : sampleps) {
            // Nested $sampled moves with the outer clone; extract outermost only
            if (nestedps.count(samplep)) continue;
            FileLine* const sampleFlp = samplep->fileline();
            AstVar* const varp = new AstVar{sampleFlp, VVarType::MODULETEMP,
                                            m_disableSampleNames.get(""), samplep->dtypep()};
            varp->lifetime(VLifetime::STATIC_EXPLICIT);
            m_modp->addStmtsp(varp);
            AstNodeExpr* const sampledValuep = samplep->cloneTreePure(false);
            samplep->replaceWith(new AstVarRef{sampleFlp, varp, VAccess::READ});
            VL_DO_DANGLING(samplep->deleteTree(), samplep);
            AstAssign* const assignp = new AstAssign{
                sampleFlp, new AstVarRef{sampleFlp, varp, VAccess::WRITE}, sampledValuep};
            sampleBodyp = AstNode::addNext(sampleBodyp, assignp);
        }
        if (sampleBodyp) {
            m_modp->addStmtsp(
                new AstAlways{flp, VAlwaysKwd::ALWAYS, senTreep->cloneTree(false), sampleBodyp});
        }
        return normalizedp;
    }

    DisableVars createDisableCounterMechanism(FileLine* flp, AstNodeExpr* disableExprp) {
        if (!disableExprp || VN_IS(disableExprp, Const)) return {};

        AstNodeDType* const u32DTypep = m_modp->findBasicDType(VBasicDTypeKwd::UINT32);
        const std::string cntName = m_disableCntNames.get("");
        AstVar* const cntp = new AstVar{flp, VVarType::MODULETEMP, cntName, u32DTypep};
        cntp->lifetime(VLifetime::STATIC_EXPLICIT);
        m_modp->addStmtsp(cntp);

        AstNodeExpr* const incrExprp
            = new AstAdd{flp, new AstVarRef{flp, cntp, VAccess::READ},
                         new AstConst{flp, AstConst::WidthedValue{}, 32, 1u}};
        incrExprp->dtypeFrom(cntp);
        m_modp->addStmtsp(new AstAlways{
            flp, VAlwaysKwd::ALWAYS,
            new AstSenTree{flp, new AstSenItem{flp, VEdgeType::ET_POSEDGE,
                                               disableExprp->cloneTreePure(false)}},
            new AstAssign{flp, new AstVarRef{flp, cntp, VAccess::WRITE}, incrExprp}});

        AstVar* const snapp = new AstVar{flp, VVarType::MODULETEMP, cntName + "__snap", u32DTypep};
        snapp->lifetime(VLifetime::STATIC_EXPLICIT);
        m_modp->addStmtsp(snapp);

        return {cntp, snapp};
    }

    // On a PropSpec-wrapped assertion whose NFA build failed with a semantic
    // error (errorEmitted), replace the body with a BitFalse const so later
    // passes see a well-formed AST. Returns true if replaced.
    void replaceBodyOnBuildError(FileLine* flp, AstPropSpec* propSpecp, bool errorEmitted) {
        if (!errorEmitted) return;
        AstNode* const innerPropp = propSpecp->propp();
        innerPropp->replaceWith(new AstConst{flp, AstConst::BitFalse{}});
        VL_DO_DANGLING(pushDeletep(innerPropp), innerPropp);
    }

    // Hoist a leading clocking event (IEEE 1800-2023 16.7):
    bool hoistClockedSeq(AstPropSpec* specp) {
        while (AstSClocked* const clockedp = VN_CAST(specp->propp(), SClocked)) {
            if (specp->sensesp()) {
                clockedp->v3warn(E_UNSUPPORTED, "Unsupported: multiclocked sequence or property");
                replaceBodyOnBuildError(specp->fileline(), specp, true);
                return true;
            }
            for (const AstSenItem* sp = clockedp->sensesp(); sp;
                 sp = VN_CAST(sp->nextp(), SenItem)) {
                if (!sp->edgeType().anEdge()) {
                    clockedp->v3warn(E_UNSUPPORTED,
                                     "Unsupported: non-edge clocking event on a sequence; "
                                     "use an edge such as @(posedge clk)");
                    replaceBodyOnBuildError(specp->fileline(), specp, true);
                    return true;
                }
            }
            specp->sensesp(clockedp->sensesp()->unlinkFrBackWithNext());
            AstNodeExpr* const bodyp = clockedp->exprp()->unlinkFrBack();
            clockedp->replaceWith(bodyp);
            VL_DO_DANGLING(pushDeletep(clockedp), clockedp);
        }
        // A clocking event anywhere else in the sequence is not supported.
        const AstSClocked* nestedp = nullptr;
        specp->propp()->foreach([&](const AstSClocked* p) {
            if (!nestedp) nestedp = p;
        });
        if (nestedp) {
            nestedp->v3warn(E_UNSUPPORTED,
                            "Unsupported: clocking event inside sequence expression");
            replaceBodyOnBuildError(specp->fileline(), specp, true);
            return true;
        }
        return false;
    }

    // Build the NFA graph for a property body, handling both the antecedent
    // |-> consequent and simple sequence cases. Returns the consequent/body
    // BuildResult (invalid on parse/build failure).
    BuildResult buildAssertionGraph(SvaNfaBuilder& builder, SvaGraph& graph, AstNodeExpr* seqBodyp,
                                    const PropertyParts& parts, FileLine* flp) {
        if (!parts.hasImplication) return builder.build(seqBodyp);

        graph.m_startVertexp = graph.createStateVertex();
        return builder.buildImplicationEdges(parts.triggerExprp, seqBodyp, graph.m_startVertexp,
                                             parts.isOverlapped, parts.isFollowedBy,
                                             parts.triggerExprp, flp);
    }

    AstPropSpec* clonePropSpecWithBody(AstPropSpec* propSpecp, AstNodeExpr* bodyp) {
        // Build a fresh PropSpec; a temporal body is not cloneTreePure-able.
        AstPropSpec* const clonep = new AstPropSpec{
            propSpecp->fileline(),
            propSpecp->sensesp() ? propSpecp->sensesp()->cloneTree(true) : nullptr,
            propSpecp->disablep() ? propSpecp->disablep()->cloneTreePure(false) : nullptr, bodyp};
        clonep->dtypeFrom(propSpecp);
        return clonep;
    }

    AstNodeExpr* outcomeCount(std::vector<AstNodeExpr*>& srcs,
                              AstNodeExpr* additionalCountp = nullptr) {
        AstNodeDType* const u32p = m_modp->findBasicDType(VBasicDTypeKwd::UINT32);
        AstNodeExpr* countp = additionalCountp;
        for (AstNodeExpr* const srcp : srcs) {
            AstCond* const oneIfp
                = new AstCond{srcp->fileline(), srcp,
                              new AstConst{srcp->fileline(), AstConst::WidthedValue{}, 32, 1},
                              new AstConst{srcp->fileline(), AstConst::WidthedValue{}, 32, 0}};
            oneIfp->dtypeFrom(u32p);
            if (countp) {
                AstAdd* const addp = new AstAdd{srcp->fileline(), countp, oneIfp};
                addp->dtypeFrom(u32p);
                countp = addp;
            } else {
                countp = oneIfp;
            }
        }
        srcs.clear();
        return countp;
    }

    AstNode* newDefaultFailAction(FileLine* flp) {
        AstDisplay* const dispp
            = new AstDisplay{flp, VDisplayType::DT_ERROR, "'assert' failed.", nullptr, nullptr};
        dispp->fmtp()->timeunit(m_modp->timeunit());
        AstNode* resultp = dispp;
        if (v3Global.opt.stopFail()) resultp->addNext(new AstStop{flp, false});
        return resultp;
    }

    // Module-level counter keeps the action out of a named block, for %m
    AstNode* repeatAction(FileLine* flp, AstNodeExpr* countp, AstNode* actionp) {
        AstNodeDType* const u32p = m_modp->findBasicDType(VBasicDTypeKwd::UINT32);
        AstVar* const counterp
            = new AstVar{flp, VVarType::MODULETEMP, m_actionCountNames.get(""), u32p};
        counterp->lifetime(VLifetime::STATIC_EXPLICIT);
        m_modp->addStmtsp(counterp);
        return V3AssertCommon::repeatLoop(flp, counterp, countp, actionp);
    }

    void addStrongPendingHandler(AstAssert* assertp, AstNodeExpr* countp, AstSenTree* senTreep,
                                 bool defaultSynthesized) {
        if (!countp) return;
        FileLine* const flp = assertp->fileline();
        AstNode* actionp = nullptr;
        if (assertp->failsp() && !defaultSynthesized) {
            actionp = assertp->failsp()->cloneTree(true);
            actionp->foreachAndNext([senTreep](AstPast* const pastp) {
                if (!pastp->sentreep()) pastp->sentreep(senTreep->cloneTree(false));
            });
        } else if (!assertp->passsp()) {
            AstDisplay* const dispp
                = new AstDisplay{flp, VDisplayType::DT_ERROR, "", nullptr, nullptr};
            dispp->fmtp()->timeunit(m_modp->timeunit());
            actionp = dispp;
            if (v3Global.opt.stopFail()) actionp->addNext(new AstStop{flp, false});
        }
        if (!actionp) {
            VL_DO_DANGLING(pushDeletep(countp), countp);
            return;
        }

        AstIf* const failOnp
            = new AstIf{flp, assertFailOnCond(flp, assertp->userType(), assertp->directive()),
                        repeatAction(flp, countp, actionp)};
        failOnp->isBoundsCheck(true);
        failOnp->user1(true);
        failOnp->user2(true);
        AstIf* const assertOnp = new AstIf{
            flp, assertOnCond(flp, assertp->userType(), assertp->directive()), failOnp};
        assertOnp->isBoundsCheck(true);
        assertOnp->user2(true);
        m_modp->addStmtsp(new AstFinal{flp, assertOnp});
    }

    void addCountPassHandler(AstAssert* assertp, AstPropSpec* propSpecp, AstNodeExpr* countp) {
        UASSERT_OBJ(assertp->passsp() && countp, assertp, "Missing counted pass action");
        FileLine* const flp = assertp->fileline();
        AstNode* const actionp = assertp->passsp()->unlinkFrBackWithNext();
        if (!assertp->failsp()) assertp->addFailsp(new AstComment{flp, ""});
        AstAssert* const handlerp = new AstAssert{
            flp,
            clonePropSpecWithBody(propSpecp,
                                  new AstNeq{flp, countp->cloneTreePure(false),
                                             new AstConst{flp, AstConst::WidthedValue{}, 32, 0}}),
            repeatAction(flp, countp->cloneTreePure(false), actionp),
            nullptr,
            assertp->userType(),
            assertp->directive(),
            assertp->name()};
        if (assertp->sentreep()) handlerp->sentreep(assertp->sentreep()->cloneTree(false));
        handlerp->senFromAlways(assertp->senFromAlways());
        handlerp->nfaLowered(true);
        assertp->addNextHere(handlerp);
        VL_DO_DANGLING(pushDeletep(countp), countp);
    }

    void addCountVacuousPassHandler(AstAssert* assertp, AstPropSpec* propSpecp,
                                    AstNodeExpr* countp) {
        UASSERT_OBJ(assertp->passsp() && countp, assertp, "Missing counted vacuous pass action");
        FileLine* const flp = assertp->fileline();
        AstNode* const actionp = assertp->passsp()->cloneTree(true);
        AstNodeExpr* const firep = new AstNeq{flp, countp->cloneTreePure(false),
                                              new AstConst{flp, AstConst::WidthedValue{}, 32, 0}};
        AstIf* const passp
            = newPassOnIf(flp, firep, repeatAction(flp, countp, actionp), assertp->userType(),
                          assertp->directive(), /*vacuous=*/true);
        AstAssert* const handlerp = new AstAssert{
            flp,
            clonePropSpecWithBody(propSpecp, new AstConst{flp, AstConst::BitTrue{}}),
            passp,
            nullptr,
            assertp->userType(),
            assertp->directive(),
            assertp->name()};
        if (assertp->sentreep()) handlerp->sentreep(assertp->sentreep()->cloneTree(false));
        handlerp->senFromAlways(assertp->senFromAlways());
        handlerp->nfaLowered(true);
        assertp->addNextHere(handlerp);
    }

    void addCountFailHandler(AstAssert* assertp, AstPropSpec* propSpecp, AstNodeExpr* countp) {
        UASSERT_OBJ(assertp->failsp() && countp, assertp, "Missing counted failure action");
        FileLine* const flp = assertp->fileline();
        AstNode* const actionp = assertp->failsp()->unlinkFrBackWithNext();
        assertp->addFailsp(new AstComment{flp, ""});
        AstAssert* const handlerp = new AstAssert{
            flp,
            clonePropSpecWithBody(propSpecp,
                                  new AstEq{flp, countp->cloneTreePure(false),
                                            new AstConst{flp, AstConst::WidthedValue{}, 32, 0}}),
            nullptr,
            repeatAction(flp, countp->cloneTreePure(false), actionp),
            assertp->userType(),
            assertp->directive(),
            assertp->name()};
        if (assertp->sentreep()) handlerp->sentreep(assertp->sentreep()->cloneTree(false));
        handlerp->senFromAlways(assertp->senFromAlways());
        handlerp->nfaLowered(true);
        assertp->addNextHere(handlerp);
        VL_DO_DANGLING(pushDeletep(countp), countp);
    }

    void setCoverCount(AstCover* coverp, AstPropSpec* propSpecp, AstNodeExpr* outputExprp,
                       AstNodeExpr* countp) {
        UASSERT_OBJ(countp, coverp, "Missing cover match count");
        FileLine* const flp = coverp->fileline();
        AstNode* const innerp = propSpecp->propp();
        innerp->replaceWith(new AstNeq{flp, countp->cloneTreePure(false),
                                       new AstConst{flp, AstConst::WidthedValue{}, 32, 0}});
        VL_DO_DANGLING(pushDeletep(innerp), innerp);
        if (AstCoverInc* const incp = VN_CAST(coverp->coverincsp(), CoverInc)) {
            incp->multiplicityp(countp->cloneTreePure(false));
        }
        VL_DO_DANGLING(outputExprp->deleteTree(), outputExprp);
        VL_DO_DANGLING(pushDeletep(countp), countp);
    }

    void splitCoverOutcomes(AstCover* coverp, AstNodeExpr* outputExprp,
                            std::vector<AstNodeExpr*>& outcomeSrcs) {
        UASSERT_OBJ(!outcomeSrcs.empty(), coverp, "Cover split without outcome source");
        std::vector<AstCover*> coverList;
        coverList.push_back(coverp);
        for (size_t i = 1; i < outcomeSrcs.size(); ++i) {
            AstCover* const clonep = coverp->cloneTree(false);
            coverp->addNextHere(clonep);
            coverList.push_back(clonep);
        }
        for (size_t i = 0; i < outcomeSrcs.size(); ++i) {
            AstPropSpec* const clonePropSpecp = VN_CAST(coverList[i]->propp(), PropSpec);
            AstNode* const innerp = clonePropSpecp->propp();
            innerp->replaceWith(outcomeSrcs[i]);
            VL_DO_DANGLING(pushDeletep(innerp), innerp);
        }
        outcomeSrcs.clear();
        VL_DO_DANGLING(outputExprp->deleteTree(), outputExprp);
    }

    // Replace one VarRef to a captured local var with $past(rhs, K)
    // (or rhs inline when K == 0). No-op if refp is not in matchMap.
    void substituteMatchItemRef(AstVarRef* refp, unsigned K,
                                const std::unordered_map<const AstVar*, AstNodeExpr*>& matchMap) {
        const auto it = matchMap.find(refp->varp());
        if (it == matchMap.end()) return;
        AstNodeExpr* newp = it->second->cloneTreePure(false);
        if (K > 0) {
            AstConst* const ticksp = new AstConst{refp->fileline(), AstConst::WidthedValue{}, 32,
                                                  static_cast<uint32_t>(K)};
            AstPast* const pastp = new AstPast{refp->fileline(), newp, ticksp};
            pastp->dtypeFrom(newp);
            newp = pastp;
        }
        refp->replaceWith(newp);
        VL_DO_DANGLING(pushDeletep(refp), refp);
        return;
    }

    // Recursively walk a consequent. Returns cycle length consumed and
    // substitutes each VarRef to a captured local var with $past(rhs, K)
    // (or rhs inline when K == 0). Reports E_UNSUPPORTED on non-constant
    // delays or composite sequence operators.
    int walkSubstituteMatchItems(AstNodeExpr* nodep, unsigned K,
                                 const std::unordered_map<const AstVar*, AstNodeExpr*>& matchItems,
                                 bool& errorEmitted) {
        if (AstSExpr* const sexprp = VN_CAST(nodep, SExpr)) {
            // IEEE 1800-2023 16.9.2: cycle_delay's lhsp is a constant_expression
            // and the delay form in a sequence is always `##N`, folded by
            // V3Const + V3Param before V3AssertNfa. Range form `##[m:n]` is the
            // only user-visible reject here.
            AstDelay* const delayp = VN_AS(sexprp->delayp(), Delay);
            UASSERT_OBJ(delayp->isCycleDelay() && VN_IS(delayp->lhsp(), Const), sexprp,
                        "SVA cycle delay must have a constant lhsp");
            if (delayp->isRangeDelay()) {
                sexprp->v3warn(E_UNSUPPORTED, "Unsupported: property local variable used across "
                                              "non-constant cycle delay in consequent"
                                              " (IEEE 1800-2023 16.10)");
                errorEmitted = true;
                return -1;
            }
            const unsigned delayCycles = VN_AS(delayp->lhsp(), Const)->toUInt();
            int preLen = 0;
            if (AstNodeExpr* const prep = sexprp->preExprp()) {
                preLen = walkSubstituteMatchItems(prep, K, matchItems, errorEmitted);
                if (errorEmitted) return -1;
            }
            const int bodyLen = walkSubstituteMatchItems(sexprp->exprp(), K + preLen + delayCycles,
                                                         matchItems, errorEmitted);
            if (errorEmitted) return -1;
            return preLen + delayCycles + bodyLen;
        }
        if (nodep->isMultiCycleSva()) {
            nodep->v3warn(E_UNSUPPORTED, "Unsupported: property local variable used across "
                                         "composite sequence operator in consequent"
                                         " (IEEE 1800-2023 16.10)");
            errorEmitted = true;
            return -1;
        }
        std::vector<AstVarRef*> refs;
        nodep->foreach([&refs](AstVarRef* p) { refs.push_back(p); });
        for (AstVarRef* const refp : refs) substituteMatchItemRef(refp, K, matchItems);
        return 0;
    }

    // Lower property-local match-item assignments before NFA construction.
    // Without this, the antecedent's AstExprStmt(<x = rhs_expr>, antBool)
    // survives into every NFA edge as a continuous-alias side-effect, so the
    // local-var temp tracks the current cycle's rhs_expr rather than the
    // antecedent-match cycle's value -- wrong for `|-> ##N` and `|=> ##N`
    // with N > 0 (issue #7587). Each consequent reference to the local var
    // is replaced with `$past(rhs_expr, K)` where K = (overlapped ? 0 : 1)
    // plus any accumulated `##N` delay. Returns true if E_UNSUPPORTED was
    // emitted; caller must replace the body with BitFalse and bail.
    bool liftMatchItemSubstitutions(PropertyParts& parts, AstNodeExpr* seqBodyp) {
        if (!parts.hasImplication) return false;
        AstExprStmt* const exprStmtp = VN_CAST(parts.triggerExprp, ExprStmt);
        if (!exprStmtp) return false;
        // IEEE 1800-2023 16.10 BNF requires `(expr, match_item {, match_item})`
        // with at least one match item; V3LinkParse only emits ExprStmt for
        // this form and only emits AstAssign with VarRef LHS for each item.
        std::unordered_map<const AstVar*, AstNodeExpr*> matchItems;
        for (AstNode* stmtp = exprStmtp->stmtsp(); stmtp; stmtp = stmtp->nextp()) {
            AstAssign* const assignp = VN_AS(stmtp, Assign);
            AstVarRef* const lhsRefp = VN_AS(assignp->lhsp(), VarRef);
            matchItems[lhsRefp->varp()] = assignp->rhsp();
        }
        const unsigned startK = parts.isOverlapped ? 0 : 1;
        bool errorEmitted = false;
        walkSubstituteMatchItems(seqBodyp, startK, matchItems, errorEmitted);
        // Match-item substitution / strip mutates ancestor purity. Release
        // builds don't auto-clear caches on edits, so refresh here.
        VIsCached::clearCacheTree();
        if (errorEmitted) return true;
        AstNodeExpr* const antBoolp = exprStmtp->resultp()->unlinkFrBack();
        exprStmtp->replaceWith(antBoolp);
        VL_DO_DANGLING(pushDeletep(exprStmtp), exprStmtp);
        parts.triggerExprp = antBoolp;
        return false;
    }

    struct ProcState final {
        AstNodeCoverOrAssert* assertp = nullptr;  // Assertion being lowered
        AstPropSpec* propSpecp = nullptr;  // Its property spec
        FileLine* flp = nullptr;  // Assertion file line
        bool isCover = false;  // cover directive
        bool isCoverSeq = false;  // cover sequence directive
        bool isSeqEvent = false;  // Sequence used as an event control
        AstCover* coverp = nullptr;  // Cover directive, else nullptr
        PropertyParts parts;  // Antecedent/consequent split
        AstNodeExpr* seqBodyp = nullptr;  // Body under any leading not
        bool negated = false;  // Odd number of leading not
        const char* propertyControlp = nullptr;  // Unsupported if/case context, else nullptr
        std::vector<AbortSpec> abortSpecs;  // Peeled top-level aborts
        AstSenTree* senTreep = nullptr;  // Owned clock sensitivity tree
        AstNodeExpr* disableExprp = nullptr;  // disable iff expression
        AstNodeExpr* outputExprp = nullptr;  // Materialized verdict
        bool countNegatedOutcomes = false;  // Swap pass/fail counts under not
        bool countNegatedPasssp = false;  // Negated assert with a pass action
        bool countNegatedFailsp = false;  // Negated assert with a fail action
        bool countNegatedCover = false;  // Negated cover property
        bool splitImplicationPasssp = false;  // Vacuous/nonvacuous pass split
        bool perAttemptPasssp = false;  // Pass action counted per attempt
        bool defaultFailSynthesized = false;  // Default fail action added here
        bool needPerSrcFail = false;  // Per-depth failure sources requested
        bool needPerSrcMatch = false;  // Per-depth match sources requested
        bool needAbortPassCount = false;  // Forced-accept count requested
        bool needAbortFailCount = false;  // Forced-reject count requested
        std::vector<AstNodeExpr*> failAttemptSrcs;  // Per-depth failure outcomes
        std::vector<AstNodeExpr*> matchAttemptSrcs;  // Per-depth match outcomes
        std::vector<AstNodeExpr*> perMidSrcs;  // Per-end cover sequence signals
        AstNodeExpr* additionalFailCountp = nullptr;  // Extra dynamically counted failures
        AstNodeExpr* matchCountp = nullptr;  // Extra range-ring match multiplicity
        AstNodeExpr* abortPassCountp = nullptr;  // Forced-accept attempt count
        AstNodeExpr* abortFailCountp = nullptr;  // Forced-reject attempt count
        AstNodeExpr* abortAnyp = nullptr;  // Any abort fired this evaluation
        AstNodeExpr* strongPendingCountp = nullptr;  // End-of-sim pending attempts
        AstNodeExpr* passCountp = nullptr;  // Final pass action multiplicity
        AstNodeExpr* failCountp = nullptr;  // Final fail action multiplicity
    };

    // Aborts peeled here are counted exactly; other shapes stay in the builder.
    static bool canPeelAborts(const AstNodeCoverOrAssert* assertp, const AstNodeExpr* bodyp,
                              const std::vector<AbortSpec>& abortSpecs) {
        if (abortSpecs.empty()) return true;
        const bool liveWindow = hasMultiCycleExpr(bodyp);
        for (const AbortSpec& spec : abortSpecs) {
            if (liveWindow && spec.kind.isAsync()) return false;
        }
        if (liveWindow && bodyp->exists([](const AstAbortOn*) { return true; })) return false;
        if (liveWindow && VN_IS(assertp, Cover)) return false;
        return isLinearAbortBody(const_cast<AstNodeExpr*>(bodyp));
    }

    // Outcome counts for a property if/case are wrong in an outcome-multiplying
    // context. Returns that context, or nullptr when the shape is supported.
    static const char* unsupportedPropertyControl(const AstNodeCoverOrAssert* assertp,
                                                  const AstNodeExpr* seqBodyp, bool negated,
                                                  bool hasAbort) {
        if (!hasPropertyControlConjunction(seqBodyp)) return nullptr;
        if (negated) return "negation";
        if (VN_IS(assertp, Cover)) return "cover";
        if (VN_AS(assertp, Assert)->passsp()) return "a pass action";
        if (hasAbort || seqBodyp->exists([](const AstAbortOn*) { return true; })) {
            return "an abort operator";
        }
        if (seqBodyp->exists([](const AstPropAlways* alwaysp) { return alwaysp->isStrong(); })) {
            return "a strong end-of-trace obligation";
        }
        return nullptr;
    }

    bool prepareConcurrentAssertion(ProcState& s) {
        AstNodeCoverOrAssert* const assertp = s.assertp;
        s.coverp = VN_CAST(assertp, Cover);
        s.isCover = s.coverp != nullptr;
        s.isCoverSeq = s.coverp && s.coverp->isCoverSeq();
        s.isSeqEvent = s.coverp && s.coverp->isSeqEvent();
        AstNode* const propp = assertp->propp();
        AstPropSpec* const propSpecp = s.propSpecp = VN_CAST(assertp->propp(), PropSpec);
        UASSERT_OBJ(propSpecp, assertp, "Concurrent assertion must have PropSpec");
        AstNodeExpr* decompositionRootp = VN_AS(propSpecp->propp(), NodeExpr);
        s.abortSpecs = peelAbortPrefix(decompositionRootp);
        if (!canPeelAborts(assertp, decompositionRootp, s.abortSpecs)) {
            s.abortSpecs.clear();
            decompositionRootp = VN_AS(propSpecp->propp(), NodeExpr);
        }
        const std::vector<AbortSpec>& abortSpecs = s.abortSpecs;

        s.parts = decomposeProperty(decompositionRootp);
        PropertyParts& parts = s.parts;
        UASSERT_OBJ(parts.seqExprp, propp, "Property body must be an expression");

        AstNodeExpr*& seqBodyp = s.seqBodyp;
        seqBodyp = parts.seqExprp;
        bool& negated = s.negated;
        negated = false;
        while (AstLogNot* const notp = VN_CAST(seqBodyp, LogNot)) {
            if (!hasMultiCycleExpr(notp->lhsp())) break;
            negated = !negated;
            seqBodyp = notp->lhsp();
        }
        if (negated && parts.hasImplication && !canSplitImplicationPassActions(parts)) {
            const AstAssert* const actionAssertp = VN_CAST(s.assertp, Assert);
            if (s.isCover || (actionAssertp && actionAssertp->passsp())) {
                seqBodyp->v3warn(
                    E_UNSUPPORTED,
                    "Unsupported: temporal implication antecedent with a negated consequent "
                    "and a pass or cover action cannot preserve attempt identity");
                replaceBodyOnBuildError(s.assertp->fileline(), propSpecp,
                                        /*errorEmitted=*/true);
                return false;
            }
        }
        s.propertyControlp
            = unsupportedPropertyControl(assertp, seqBodyp, negated, !abortSpecs.empty());
        if (liftMatchItemSubstitutions(parts, seqBodyp)) {
            replaceBodyOnBuildError(assertp->fileline(), propSpecp, /*errorEmitted=*/true);
            return false;
        }

        if (!propSpecp->sensesp() && m_defaultClockingp) {
            propSpecp->sensesp(m_defaultClockingp->sensesp()->cloneTree(true));
        }
        if (!propSpecp->disablep() && m_defaultDisablep && !s.isSeqEvent) {
            propSpecp->disablep(m_defaultDisablep->condp()->cloneTreePure(true));
        }
        if (!propSpecp->sensesp()) return false;
        AstSenTree*& senTreep = s.senTreep;
        senTreep = new AstSenTree{propSpecp->fileline(), propSpecp->sensesp()->cloneTree(true)};
        s.disableExprp = propSpecp->disablep();

        // NFA lowering clones repeated operands and may hoist them into an
        // always_comb block. Resolve implicit sampled-value clocks first, while
        // the enclosing assertion clock is still available.
        {
            VL_RESTORER(m_sampledValueClockp);
            m_sampledValueClockp = senTreep;
            iterate(propSpecp->propp());
        }

        s.flp = assertp->fileline();
        return true;
    }

    void planOutcomeChannels(ProcState& s) {
        AstNodeCoverOrAssert* const assertp = s.assertp;
        const PropertyParts& parts = s.parts;
        const bool negated = s.negated;
        const bool isCover = s.isCover;
        const bool isCoverSeq = s.isCoverSeq;
        const std::vector<AbortSpec>& abortSpecs = s.abortSpecs;
        AstAssert* const assertAssertp = VN_CAST(assertp, Assert);
        // Negated-consequent failure multiplicity is independent of vacuous-pass splitting.
        s.countNegatedOutcomes = negated;
        s.countNegatedPasssp = s.countNegatedOutcomes && assertAssertp && assertAssertp->passsp();
        s.countNegatedFailsp = s.countNegatedOutcomes && assertAssertp && assertAssertp->failsp();
        s.countNegatedCover = s.countNegatedOutcomes && isCover && !isCoverSeq;
        s.splitImplicationPasssp = assertAssertp && assertAssertp->passsp() && parts.hasImplication
                                   && !negated && canSplitImplicationPassActions(parts);
        s.perAttemptPasssp
            = assertAssertp && assertAssertp->passsp() && !parts.hasImplication && !negated;
        s.needPerSrcFail = (!isCover && !negated && assertAssertp && assertAssertp->failsp())
                           || s.countNegatedPasssp || s.countNegatedCover;
        s.needPerSrcMatch = s.perAttemptPasssp || s.splitImplicationPasssp
                            || (isCover && !isCoverSeq && !negated) || s.countNegatedFailsp;
        s.needAbortPassCount
            = !abortSpecs.empty() && ((assertAssertp && assertAssertp->passsp()) || isCover);
        s.needAbortFailCount = !abortSpecs.empty() && assertAssertp && assertAssertp->failsp();
    }

    void replaceObservedDisable(AstPropSpec* propSpecp, AstNodeExpr* disableObservedp) {
        if (!disableObservedp) return;
        AstNodeExpr* const oldDisablep = propSpecp->disablep();
        UASSERT_OBJ(oldDisablep, propSpecp, "Observed disable without PropSpec disable");
        oldDisablep->replaceWith(disableObservedp);
        VL_DO_DANGLING(pushDeletep(oldDisablep), oldDisablep);
    }

    bool lowerConcurrentAssertion(ProcState& s) {
        AstNodeCoverOrAssert* const assertp = s.assertp;
        AstPropSpec* const propSpecp = s.propSpecp;
        FileLine* const flp = s.flp;
        const bool isCover = s.isCover;
        const bool isCoverSeq = s.isCoverSeq;
        const bool isSeqEvent = s.isSeqEvent;
        const bool negated = s.negated;
        AstNodeExpr* const seqBodyp = s.seqBodyp;
        PropertyParts& parts = s.parts;
        AstSenTree*& senTreep = s.senTreep;
        AstNodeExpr*& disableExprp = s.disableExprp;
        const std::vector<AbortSpec>& abortSpecs = s.abortSpecs;

        SvaGraph graph;
        SvaNfaBuilder builder{graph,     m_modp, m_propTempNames, isCoverSeq, !isCover || negated,
                              isSeqEvent};

        const BuildResult result = buildAssertionGraph(builder, graph, seqBodyp, parts, flp);
        if (result.valid()) wireMatchAndMidSources(graph, result, flp);
        if (!result.valid()) {
            replaceBodyOnBuildError(flp, propSpecp, result.errorEmitted);
            VL_DO_DANGLING(pushDeletep(senTreep), senTreep);
            return false;
        }
        // After the build, so a construct the builder rejects reports itself.
        if (s.propertyControlp) {
            seqBodyp->v3warn(E_UNSUPPORTED,
                             "Unsupported: temporal property if/case with " << s.propertyControlp);
            replaceBodyOnBuildError(flp, propSpecp, /*errorEmitted=*/true);
            VL_DO_DANGLING(pushDeletep(senTreep), senTreep);
            return false;
        }

        AstNodeExpr* const normalizedDisablep
            = disableExprp ? normalizeDisableExpr(disableExprp, senTreep) : nullptr;
        const DisableVars disableVars = createDisableCounterMechanism(flp, normalizedDisablep);
        AstVar* const disableCntVarp = disableVars.cntp;
        AstVar* const snapshotVarp = disableVars.snapp;

        AstAssert* const assertWithFailp = VN_CAST(assertp, Assert);
        // Synthesize the default fail action before planning counts, like an explicit else.
        if (assertWithFailp && !assertWithFailp->passsp() && !assertWithFailp->failsp()) {
            assertWithFailp->addFailsp(newDefaultFailAction(flp));
            s.defaultFailSynthesized = true;
        }
        planOutcomeChannels(s);

        AstNodeExpr* const alwaysTriggerp
            = isSeqEvent ? new AstConst{flp, AstConst::BitTrue{}}
                         : assertOnCond(flp, assertp->userType(), assertp->directive());
        SvaNfaLowering::LowerRequest req;
        req.triggerExprp = alwaysTriggerp;
        req.senTreep = senTreep;
        req.matchCondp = result.finalCondp;
        req.disableExprp = normalizedDisablep ? normalizedDisablep->cloneTreePure(false) : nullptr;
        req.abortSpecsp = abortSpecs.empty() ? nullptr : &abortSpecs;
        req.disableCntVarp = disableCntVarp;
        req.snapshotVarp = snapshotVarp;
        req.isCover = isCover;
        req.negated = negated;
        req.assertType = isSeqEvent ? VAssertType{VAssertType::INTERNAL} : assertp->userType();
        req.directiveType = isSeqEvent ? VAssertDirectiveType{VAssertDirectiveType::INTERNAL}
                                       : assertp->directive();
        req.wantPerSrcFail = s.needPerSrcFail;
        req.pruneSingleFailSource = s.defaultFailSynthesized && !negated && abortSpecs.empty();
        req.wantPerSrcMatch = s.needPerSrcMatch;
        req.wantAbortPassCount = s.needAbortPassCount;
        req.wantAbortFailCount = s.needAbortFailCount;
        req.wantStrongPending = assertWithFailp != nullptr;
        req.wantPerMid = isCoverSeq;
        SvaNfaLowering::LowerResult res = m_loweringp->lower(flp, graph, req);
        s.outputExprp = res.outputExprp;
        s.abortAnyp = res.abortAnyp;
        s.additionalFailCountp = res.failCountp;
        s.matchCountp = res.matchCountp;
        s.abortPassCountp = res.abortPassCountp;
        s.abortFailCountp = res.abortFailCountp;
        s.strongPendingCountp = res.strongPendingCountp;
        s.failAttemptSrcs = std::move(res.failAttemptSrcs);
        s.matchAttemptSrcs = std::move(res.matchAttemptSrcs);
        s.perMidSrcs = std::move(res.perMidSrcs);
        AstNodeExpr* const disableObservedp = res.disableRefp;

        if (assertWithFailp) {
            addStrongPendingHandler(assertWithFailp, s.strongPendingCountp, senTreep,
                                    s.defaultFailSynthesized);
        }

        VL_DO_DANGLING(pushDeletep(alwaysTriggerp), alwaysTriggerp);
        if (normalizedDisablep) {
            VL_DO_DANGLING(normalizedDisablep->deleteTree(), normalizedDisablep);
        }
        VL_DO_DANGLING(pushDeletep(senTreep), senTreep);
        replaceObservedDisable(propSpecp, disableObservedp);
        if (result.finalCondp && !result.finalCondp->backp()) pushDeletep(result.finalCondp);
        if (dumpGraphLevel() >= 6) graph.m_graph.dumpDotFilePrefixed("assert-nfa");
        assertp->nfaLowered(true);
        return true;
    }

    void finalizeOutcomeCounts(ProcState& s) {
        FileLine* const flp = s.flp;
        const bool needPerSrcMatch = s.needPerSrcMatch;
        const bool needPerSrcFail = s.needPerSrcFail;
        const bool countNegatedOutcomes = s.countNegatedOutcomes;
        const bool countNegatedPasssp = s.countNegatedPasssp;
        const bool countNegatedFailsp = s.countNegatedFailsp;
        const bool countNegatedCover = s.countNegatedCover;
        std::vector<AstNodeExpr*>& matchAttemptSrcs = s.matchAttemptSrcs;
        std::vector<AstNodeExpr*>& failAttemptSrcs = s.failAttemptSrcs;
        AstNodeExpr*& matchCountp = s.matchCountp;
        AstNodeExpr*& additionalFailCountp = s.additionalFailCountp;
        AstNodeExpr*& abortPassCountp = s.abortPassCountp;
        AstNodeExpr*& abortFailCountp = s.abortFailCountp;
        AstNodeExpr*& passCountp = s.passCountp;
        AstNodeExpr*& failCountp = s.failCountp;

        if (needPerSrcMatch) {
            passCountp = outcomeCount(matchAttemptSrcs, matchCountp);
            matchCountp = nullptr;
        }
        if (needPerSrcFail) failCountp = outcomeCount(failAttemptSrcs, additionalFailCountp);
        additionalFailCountp = nullptr;

        if (countNegatedOutcomes) std::swap(passCountp, failCountp);

        const auto addOutcomeCounts = [&](AstNodeExpr* lhsp, AstNodeExpr* rhsp) {
            if (!lhsp) return rhsp;
            if (!rhsp) return lhsp;
            AstAdd* const addp = new AstAdd{flp, lhsp, rhsp};
            addp->dtypeFrom(m_modp->findBasicDType(VBasicDTypeKwd::UINT32));
            return static_cast<AstNodeExpr*>(addp);
        };
        failCountp = addOutcomeCounts(failCountp, abortFailCountp);
        abortFailCountp = nullptr;
        if (s.isCover) {
            passCountp = addOutcomeCounts(passCountp, abortPassCountp);
            abortPassCountp = nullptr;
        }

        if (countNegatedOutcomes) {
            const auto zeroCount = [&]() {
                return static_cast<AstNodeExpr*>(
                    new AstConst{flp, AstConst::WidthedValue{}, 32, 0});
            };
            if ((countNegatedPasssp || countNegatedCover) && !passCountp) {
                passCountp = zeroCount();
            }
            if (countNegatedFailsp && !failCountp) failCountp = zeroCount();
        }
    }

    void installActionHandlers(ProcState& s) {
        AstNodeCoverOrAssert* const assertp = s.assertp;
        AstPropSpec* const propSpecp = s.propSpecp;
        PropertyParts& parts = s.parts;
        const bool countNegatedOutcomes = s.countNegatedOutcomes;
        const bool countNegatedPasssp = s.countNegatedPasssp;
        const bool countNegatedFailsp = s.countNegatedFailsp;
        const bool perAttemptPasssp = s.perAttemptPasssp;
        const bool splitImplicationPasssp = s.splitImplicationPasssp;
        std::vector<AstNodeExpr*>& failAttemptSrcs = s.failAttemptSrcs;
        std::vector<AstNodeExpr*>& matchAttemptSrcs = s.matchAttemptSrcs;
        AstNodeExpr*& passCountp = s.passCountp;
        AstNodeExpr*& failCountp = s.failCountp;
        AstNodeExpr*& abortAnyp = s.abortAnyp;
        AstAssert* const assertAssertp = VN_CAST(assertp, Assert);
        AstAssert* const assertWithFailp = VN_CAST(assertp, Assert);

        if (countNegatedOutcomes && assertAssertp) {
            if (countNegatedPasssp) {
                UASSERT_OBJ(passCountp, assertAssertp,
                            "Negated pass action requested without a reject count");
                if (parts.hasImplication) {
                    splitImplicationPassActions(assertAssertp, propSpecp, parts, passCountp,
                                                /*includeVacuous=*/true, abortAnyp);
                } else {
                    addCountPassHandler(assertAssertp, propSpecp, passCountp);
                }
                passCountp = nullptr;
            }
            if (countNegatedFailsp) {
                UASSERT_OBJ(failCountp, assertWithFailp,
                            "Negated failure action requested without a match count");
                addCountFailHandler(assertWithFailp, propSpecp, failCountp);
                failCountp = nullptr;
            }
            for (AstNodeExpr* const srcp : failAttemptSrcs) pushDeletep(srcp);
            for (AstNodeExpr* const srcp : matchAttemptSrcs) pushDeletep(srcp);
        } else if (perAttemptPasssp) {
            UASSERT_OBJ(passCountp, assertAssertp, "Pass action requested without a match count");
            addCountPassHandler(assertAssertp, propSpecp, passCountp);
            passCountp = nullptr;
            if (failCountp) {
                addCountFailHandler(assertWithFailp, propSpecp, failCountp);
                failCountp = nullptr;
            }
        } else if (splitImplicationPasssp) {
            UASSERT_OBJ(passCountp, assertAssertp,
                        "Implication pass action requested without a match count");
            splitImplicationPassActions(assertAssertp, propSpecp, parts, passCountp,
                                        /*includeVacuous=*/true, abortAnyp);
            passCountp = nullptr;
            if (failCountp) {
                addCountFailHandler(assertWithFailp, propSpecp, failCountp);
                failCountp = nullptr;
            }
        } else if (failCountp) {
            addCountFailHandler(assertWithFailp, propSpecp, failCountp);
            failCountp = nullptr;
        }
    }

    void installOutcomeHandlers(ProcState& s) {
        AstNodeCoverOrAssert* const assertp = s.assertp;
        AstPropSpec* const propSpecp = s.propSpecp;
        const bool isCover = s.isCover;
        const bool isCoverSeq = s.isCoverSeq;
        AstCover* const coverp = s.coverp;
        AstNodeExpr* const outputExprp = s.outputExprp;
        const bool needPerSrcMatch = s.needPerSrcMatch;
        const bool countNegatedCover = s.countNegatedCover;
        std::vector<AstNodeExpr*>& perMidSrcs = s.perMidSrcs;
        AstNodeExpr*& passCountp = s.passCountp;
        AstNodeExpr*& failCountp = s.failCountp;
        AstNodeExpr*& matchCountp = s.matchCountp;
        AstNodeExpr*& additionalFailCountp = s.additionalFailCountp;
        AstNodeExpr*& abortPassCountp = s.abortPassCountp;
        AstNodeExpr*& abortFailCountp = s.abortFailCountp;
        AstNodeExpr*& abortAnyp = s.abortAnyp;
        AstAssert* const assertAssertp = VN_CAST(assertp, Assert);

        if (isCoverSeq && !perMidSrcs.empty()) {
            splitCoverOutcomes(coverp, outputExprp, perMidSrcs);
        } else if (isCover && (needPerSrcMatch || countNegatedCover)) {
            UASSERT_OBJ(passCountp, coverp, "Cover requested without a match count");
            setCoverCount(coverp, propSpecp, outputExprp, passCountp);
            passCountp = nullptr;
        } else {
            AstNode* const innerPropp = propSpecp->propp();
            innerPropp->replaceWith(outputExprp);
            VL_DO_DANGLING(pushDeletep(innerPropp), innerPropp);
            for (AstNodeExpr* const sp : perMidSrcs) pushDeletep(sp);
        }

        if (abortPassCountp && assertAssertp && assertAssertp->passsp()) {
            addCountVacuousPassHandler(assertAssertp, propSpecp, abortPassCountp);
            abortPassCountp = nullptr;
        }

        installActionHandlers(s);

        if (passCountp) VL_DO_DANGLING(pushDeletep(passCountp), passCountp);
        if (failCountp) VL_DO_DANGLING(pushDeletep(failCountp), failCountp);
        if (matchCountp) VL_DO_DANGLING(pushDeletep(matchCountp), matchCountp);
        UASSERT_OBJ(!additionalFailCountp, assertp, "Fail count not consumed by outcome counts");
        if (abortPassCountp) VL_DO_DANGLING(pushDeletep(abortPassCountp), abortPassCountp);
        if (abortFailCountp) VL_DO_DANGLING(pushDeletep(abortFailCountp), abortFailCountp);
        if (abortAnyp) VL_DO_DANGLING(pushDeletep(abortAnyp), abortAnyp);
    }

    // Inline property/sequence refs and reject unsupported shapes.
    // Returns the PropSpec to lower, or nullptr when fully handled here.
    AstPropSpec* prepareAssertionProp(AstNodeCoverOrAssert* assertp) {
        if (AstPropSpec* const specp = VN_CAST(assertp->propp(), PropSpec)) {
            if (AstFuncRef* const funcrefp = VN_CAST(specp->propp(), FuncRef)) {
                if (const AstProperty* const propyp = VN_CAST(funcrefp->taskp(), Property)) {
                    inlineNamedProperty(specp, funcrefp, propyp);
                }
            }
        }

        inlineAllSequenceRefs(assertp->propp());

        if (AstPropSpec* const specp = VN_CAST(assertp->propp(), PropSpec)) {
            if (hoistClockedSeq(specp)) return nullptr;
        }

        AstPropSpec* const propp = VN_AS(assertp->propp(), PropSpec);
        if (!VN_IS(assertp, Cover)
            && effectiveAssertPropStrength(propp) == VPropStrength::STRONG) {
            propp->v3warn(E_UNSUPPORTED,
                          "Unsupported: strong property in " + assertp->verilogKwd() + ".");
            replaceBodyOnBuildError(assertp->fileline(), propp, /*errorEmitted=*/true);
            return nullptr;
        }

        if (!hasMultiCycleExpr(propp)) return nullptr;
        // A nested property instance keeps its body behind the call; lowering would drop it.
        if (propp->exists([](const AstFuncRef* refp) { return VN_IS(refp->taskp(), Property); })) {
            assertp->v3warn(E_UNSUPPORTED,
                            "Unsupported: property instance inside a multi-cycle property "
                            "expression");
            VL_DO_DANGLING(pushDeletep(assertp->unlinkFrBack()), assertp);
            return nullptr;
        }
        if (isBareTopLevelUntil(propp)) return nullptr;
        return propp;
    }

    void processAssertion(AstNodeCoverOrAssert* assertp) {
        if (assertp->immediate()) return;
        if (!prepareAssertionProp(assertp)) return;

        ProcState s;
        s.assertp = assertp;
        if (!prepareConcurrentAssertion(s)) return;
        if (!lowerConcurrentAssertion(s)) return;
        finalizeOutcomeCounts(s);
        installOutcomeHandlers(s);
        UINFO(4, "NFA converted assertion at " << s.flp << endl);
    }

    // VISITORS
    void visit(AstNodeModule* nodep) override {
        VL_RESTORER(m_modp);
        VL_RESTORER(m_loweringp);
        VL_RESTORER(m_defaultClockingp);
        VL_RESTORER(m_defaultDisablep);
        m_modp = nodep;
        m_defaultClockingp = nullptr;
        m_defaultDisablep = nodep->defaultDisablep();
        SvaNfaLowering lowering{nodep};
        m_loweringp = &lowering;
        iterateChildren(nodep);
    }
    void visit(AstClocking* nodep) override {
        if (nodep->isDefault() && !m_defaultClockingp) m_defaultClockingp = nodep;
        iterateChildren(nodep);
    }
    void visit(AstGenBlock* nodep) override {
        VL_RESTORER(m_defaultDisablep);
        m_defaultDisablep = nodep->defaultDisablep();
        iterateChildren(nodep);
    }
    void visit(AstDefaultDisable* nodep) override {}
    void visit(AstFell* nodep) override { visitSampledValue(nodep); }
    void visit(AstPast* nodep) override { visitSampledValue(nodep); }
    void visit(AstRose* nodep) override { visitSampledValue(nodep); }
    void visit(AstStable* nodep) override { visitSampledValue(nodep); }
    void visit(AstAssert* nodep) override { processAssertion(nodep); }
    void visit(AstCover* nodep) override { processAssertion(nodep); }
    void visit(AstRestrict* nodep) override {
        // Restrict property is ignored by simulators (IEEE 1800-2023 16.12.2).
        // Remove here so temporal SExpr don't leak to V3AssertPre.
        VL_DO_DANGLING(pushDeletep(nodep->unlinkFrBack()), nodep);
    }
    void visit(AstAssertIntrinsic* nodep) override {}
    void visit(AstNode* nodep) override { iterateChildren(nodep); }

public:
    explicit AssertNfaVisitor(AstNetlist* nodep) { iterate(nodep); }
};

//######################################################################
// Top entry point

void V3AssertNfa::assertNfaAll(AstNetlist* nodep) {
    UINFO(2, __FUNCTION__ << ":" << endl);
    { AssertNfaVisitor{nodep}; }
    V3Global::dumpCheckGlobalTree("assertnfa", 0, dumpTreeEitherLevel() >= 3);
}
