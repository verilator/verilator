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
//  - Emit module-level state registers driven by AstAlways blocks.
//  - Replace converted assertions with combinational match/reject checks
//    so V3AssertPre sees no multi-cycle SExpr (unsupported ones fall through).
//
//*************************************************************************

#include "V3PchAstNoMT.h"  // VL_MT_DISABLED_CODE_UNIT

#include "V3AssertNfa.h"

#include "V3Const.h"
#include "V3Graph.h"
#include "V3Task.h"
#include "V3UniqueNames.h"

#include <set>
#include <vector>

VL_DEFINE_DEBUG_FUNCTIONS;

//######################################################################
// NFA Graph Data Structures (V3Graph-derived per upstream convention)

namespace {

class SvaStateVertex;

// Per-vertex algorithm data, stored via V3GraphVertex::userp() during lowering
struct SvaVertexData final {
    AstVar* stateVarp = nullptr;  // NBA state register for this vertex
    AstVar* counterActiveVarp = nullptr;  // Counter FSM active flag
    AstVar* counterCountVarp = nullptr;  // Counter FSM count register
    AstVar* doneLVarp = nullptr;  // SAnd LHS done-latch
    AstVar* doneRVarp = nullptr;  // SAnd RHS done-latch
    AstNodeExpr* stateSigp = nullptr;  // Combinational state signal (owned during lowering)
    bool needsReg = false;  // True if vertex has incoming clocked edge
};

// NFA state vertex -- one per NFA position in the sequence evaluation
class SvaStateVertex final : public V3GraphVertex {
    VL_RTTI_IMPL(SvaStateVertex, V3GraphVertex)
public:
    // True if this is the sequence-match terminal vertex
    bool m_isMatch = false;
    // Owned throughout-guard condition clones; IEEE 1800-2023 16.9.9
    std::vector<AstNodeExpr*> m_throughoutConds;
    // Counter FSM vertex for ##[M:N] when N-M > kChainLimit
    bool m_isCounter = false;
    int m_counterMax
        = 0;  // Counter window maximum (min is always 0; pre-chain handles the M offset)
    // Liveness terminal (IEEE weak semantics): reject must not fire from this source
    bool m_isUnbounded = false;
    // Temporal sequence AND combiner; IEEE 1800-2023 16.9.5
    bool m_isAndCombiner = false;
    SvaStateVertex* m_andLhsTermp = nullptr;  // LHS sub-NFA terminal vertex
    SvaStateVertex* m_andRhsTermp = nullptr;  // RHS sub-NFA terminal vertex
    AstNodeExpr* m_andLhsCondp = nullptr;  // OWNED; LHS final condition (may be nullptr)
    AstNodeExpr* m_andRhsCondp = nullptr;  // OWNED; RHS final condition (may be nullptr)
    // Reject sink for SAnd rejectOnFail wiring; not a state-signal source
    bool m_isRejectSink = false;

    // CONSTRUCTORS
    explicit SvaStateVertex(V3Graph* graphp)
        : V3GraphVertex{graphp} {}
    ~SvaStateVertex() override {
        for (AstNodeExpr* cp : m_throughoutConds) VL_DO_DANGLING(cp->deleteTree(), cp);
        if (m_andLhsCondp) VL_DO_DANGLING(m_andLhsCondp->deleteTree(), m_andLhsCondp);
        if (m_andRhsCondp) VL_DO_DANGLING(m_andRhsCondp->deleteTree(), m_andRhsCondp);
    }
    // METHODS
    string name() const override { return "s" + cvtToStr(color()); }  // LCOV_EXCL_LINE
    // LCOV_EXCL_START -- Graphviz dump only
    string dotColor() const override {
        if (m_isMatch) return "red";
        if (m_isCounter) return "blue";
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
            for (const V3GraphEdge& er : vtxr.outEdges()) {
                result.push_back(static_cast<const SvaTransEdge*>(&er));
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
    bool valid() const { return termVertexp != nullptr; }
    static BuildResult fail(bool errored = false) { return {nullptr, nullptr, {}, errored}; }
    static BuildResult failWithError() { return {nullptr, nullptr, {}, true}; }
};

//######################################################################
// NFA Builder

class SvaNfaBuilder final {
    SvaGraph& m_graph;  // NFA graph being built
    AstNodeModule* const m_modp;  // Module to receive hoisted sampled-prop temps
    V3UniqueNames& m_propTempNames;  // Module-shared temp-var name source
    std::vector<AstNodeExpr*> m_throughoutStack;  // Active throughout guards (IEEE 16.9.9)
    bool m_inUnboundedScope = false;  // Sticky: nodes created after inherit liveness

    AstNodeExpr* throughoutCond(AstNodeExpr* baseCondp, FileLine* flp) {
        if (m_throughoutStack.empty()) return baseCondp;
        // AND all throughout conditions (supports nesting)
        // Each must use $sampled values per IEEE 16.9.9
        AstNodeExpr* guardp = nullptr;
        for (AstNodeExpr* const condp : m_throughoutStack) {
            AstNodeExpr* const clonep = sampled(condp->cloneTreePure(false));
            if (!guardp) {
                guardp = clonep;
            } else {
                guardp = new AstAnd{flp, guardp, clonep};
            }
        }
        if (baseCondp) { guardp = new AstAnd{flp, baseCondp, guardp}; }
        return guardp;
    }

    static int getConstInt(AstNodeExpr* exprp) {
        AstNodeExpr* const constp = V3Const::constifyEdit(exprp->cloneTreePure(false));
        const AstConst* const cp = VN_CAST(constp, Const);
        const int val = cp ? cp->toSInt() : -1;
        VL_DO_DANGLING(constp->deleteTree(), constp);
        return val;
    }

    // Static fixed-length analysis: clock ticks from entry to terminal, or -1.
    // Used by SIntersect to verify IEEE 1800-2023 16.9.6 equal-length precondition.
    //
    // Supported:
    //  - Boolean leaf (default)              -> 0
    //  - AstSExpr with fixed cycle delay     -> pre + N + body
    //  - AstSExpr with range delay M==N      -> pre + N + body
    //  - AstSThroughout                      -> length of rhsp (the seq)
    // Unsupported (returns -1):
    //  - Range delays with M != N            -> variable
    //  - Unbounded waits ##[M:$]             -> infinite/variable
    //  - ConsRep / SGotoRep / SAnd / SOr     -> defer (rare in intersect)
    //  - SIntersect nested in SIntersect     -> defer
    static int fixedLength(AstNodeExpr* nodep) {
        if (AstSExpr* const sexprp = VN_CAST(nodep, SExpr)) {
            AstDelay* const delayp = VN_CAST(sexprp->delayp(), Delay);
            if (!delayp || !delayp->isCycleDelay()) return -1;
            int delayCycles = -1;
            if (delayp->isRangeDelay()) {
                if (delayp->isUnbounded()) return -1;  // LCOV_EXCL_LINE
                const int minD = getConstInt(delayp->lhsp());
                const int maxD = getConstInt(delayp->rhsp());
                if (minD < 0 || maxD < 0 || minD != maxD) return -1;
                delayCycles = minD;
            } else {
                delayCycles = getConstInt(delayp->lhsp());
                if (delayCycles < 0) return -1;  // LCOV_EXCL_LINE
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
        if (nodep->isMultiCycleSva()) return -1;
        // LCOV_EXCL_STOP
        // Plain boolean expression (no SVA constructs) -- 0 cycles.
        return 0;
    }

    static AstNodeExpr* sampled(AstNodeExpr* exprp) {
        AstSampled* const sp = new AstSampled{exprp->fileline(), exprp};
        sp->dtypeFrom(exprp);
        return sp;
    }

    // Cuts AST size from O(N * sizeof(exprp)) to O(N) + O(sizeof(exprp)) by
    // sharing a single `VarRef` across N check edges. Hoist also matches the
    // IEEE 1800-2023 16.9.9 "single preponed-region snapshot" semantic for
    // any exprp -- even an impure one would now evaluate exactly once per
    // clock instead of N times. Orphan temps from failed builds are unused
    // MODULETEMPs and are removed by V3Dead.
    AstVar* tryHoistSampled(AstNodeExpr* exprp, FileLine* flp, int cloneCount) {
        constexpr int kHoistThreshold = 2;
        if (cloneCount < kHoistThreshold) return nullptr;
        AstVar* const tempVarp = new AstVar{flp, VVarType::MODULETEMP, m_propTempNames.get(exprp),
                                            m_modp->findBitDType()};
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

    // Create vertex and inherit throughout guards from current scope (IEEE 16.9.9).
    SvaStateVertex* scopedCreateVertex() {
        SvaStateVertex* const vtxp = m_graph.createStateVertex();
        for (AstNodeExpr* const cp : m_throughoutStack) {
            vtxp->m_throughoutConds.push_back(cp->cloneTreePure(false));
        }
        if (m_inUnboundedScope) vtxp->m_isUnbounded = true;
        return vtxp;
    }

    // AND current throughout stack into every edge/link (IEEE 16.9.9 invariant).
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

    SvaStateVertex* addDelayChain(SvaStateVertex* startp, int n, FileLine* flp) {
        SvaStateVertex* currentp = startp;
        for (int i = 0; i < n; ++i) {
            SvaStateVertex* const nextp = scopedCreateVertex();
            guardedEdge(currentp, nextp, flp);
            currentp = nextp;
        }
        return currentp;
    }

    // Build NFA for an SExpr. finalCond = RHS (not yet added as a vertex).
    // isTopLevelStep: marks outermost required boolean check as rejectOnFail.
    // Apply a range delay `##[M:N]` to currentp. Returns true on success. On
    // failure, sets outErrorEmitted per semantic-error policy and returns false.
    bool applyRangeDelay(AstDelay* delayp, AstNodeExpr* rhsExprp, SvaStateVertex*& currentp,
                         std::vector<SvaStateVertex*>& midSources, FileLine* flp,
                         bool& outErrorEmitted) {
        const int minDelay = getConstInt(delayp->lhsp());
        if (minDelay < 0) {
            delayp->v3error("Range delay minimum is not a non-negative elaboration-time constant"
                            " (IEEE 1800-2023 16.7)");
            outErrorEmitted = true;
            return false;
        }
        if (delayp->isUnbounded()) {
            // `##[M:$]`: wait M cycles, then self-loop waiting for the match
            // condition. Unbounded = liveness, so no reject.
            currentp = addDelayChain(currentp, minDelay, flp);
            guardedEdge(currentp, currentp, flp);
            currentp->m_isUnbounded = true;
            m_inUnboundedScope = true;
            return true;
        }
        const int maxDelay = getConstInt(delayp->rhsp());
        if (maxDelay < 0) {
            delayp->v3error("Range delay maximum is not a non-negative elaboration-time constant"
                            " (IEEE 1800-2023 16.7)");
            outErrorEmitted = true;
            return false;
        }
        if (maxDelay < minDelay) {
            delayp->v3error("Range delay maximum must be >= minimum (IEEE 1800-2023 16.7)");
            outErrorEmitted = true;
            return false;
        }
        if (minDelay == maxDelay) {
            currentp = addDelayChain(currentp, minDelay, flp);
            return true;
        }
        const int range = maxDelay - minDelay;
        currentp = addDelayChain(currentp, minDelay, flp);
        // kChainLimit bounds per-attempt unrolled vertices. Above this, a
        // counter FSM (constant-size state) is used instead, so the vertex
        // count is O(1) in range regardless of user input; no adversarial N
        // blowup is possible.
        constexpr int kChainLimit = 256;
        if (range > kChainLimit) {
            // Large range: counter FSM. Overlapping triggers during an active
            // count are dropped (non-overlapping semantics only).
            SvaStateVertex* const counterVtxp = scopedCreateVertex();
            counterVtxp->m_isCounter = true;
            counterVtxp->m_counterMax = range;
            guardedEdge(currentp, counterVtxp, flp);
            currentp = counterVtxp;
        } else if (VN_IS(rhsExprp, SExpr)) {
            // Nested-SExpr RHS: merge all [M,N] positions; continuation is per-attempt.
            SvaStateVertex* const mergeVtxp = scopedCreateVertex();
            guardedLink(currentp, mergeVtxp, flp);
            for (int i = 0; i < range; ++i) {
                SvaStateVertex* const nextVtxp = scopedCreateVertex();
                guardedEdge(currentp, nextVtxp, flp);
                guardedLink(nextVtxp, mergeVtxp, flp);
                currentp = nextVtxp;
            }
            currentp = mergeVtxp;
        } else {
            // Pure boolean RHS: register chain. Each mid-position links to
            // match (match-only); last position is the reject source.
            AstVar* const hoistVarp = tryHoistSampled(rhsExprp, flp, range);
            midSources.push_back(currentp);
            for (int i = 0; i < range; ++i) {
                SvaStateVertex* const nextVtxp = scopedCreateVertex();
                AstNodeExpr* const notExprp
                    = new AstNot{flp, sampledRefOrClone(hoistVarp, rhsExprp, flp)};
                guardedEdge(currentp, nextVtxp, notExprp, flp);
                if (i < range - 1) midSources.push_back(nextVtxp);
                currentp = nextVtxp;
            }
        }
        return true;
    }

    BuildResult buildSExpr(AstSExpr* sexprp, SvaStateVertex* entryVtxp,
                           bool isTopLevelStep = false) {
        AstDelay* const delayp = VN_CAST(sexprp->delayp(), Delay);
        if (!delayp || !delayp->isCycleDelay()) return BuildResult::fail();

        FileLine* const flp = sexprp->fileline();

        // Handle LHS (preExpr)
        SvaStateVertex* currentp = entryVtxp;
        if (AstNodeExpr* const preExprp = sexprp->preExprp()) {
            const BuildResult pre = buildExpr(preExprp, currentp, isTopLevelStep);
            if (!pre.valid()) return BuildResult::fail(pre.errorEmitted);  // LCOV_EXCL_LINE
            if (pre.finalCondp) {
                SvaStateVertex* const condVtxp = scopedCreateVertex();
                SvaTransEdge* const edgep = guardedLink(
                    pre.termVertexp, condVtxp, sampled(pre.finalCondp->cloneTreePure(false)), flp);
                if (isTopLevelStep && !pre.termVertexp->m_isUnbounded && !m_inUnboundedScope) {
                    // Do not mark liveness sources: first boolean check is deferred.
                    edgep->m_rejectOnFail = true;
                }
                currentp = condVtxp;
            } else {
                currentp = pre.termVertexp;
            }
        }

        // Handle delay
        std::vector<SvaStateVertex*> rangeMidSources;
        if (delayp->isRangeDelay()) {
            bool errorEmitted = false;
            if (!applyRangeDelay(delayp, sexprp->exprp(), currentp, rangeMidSources, flp,
                                 errorEmitted)) {
                return BuildResult::fail(errorEmitted);
            }
        } else {
            const int delayCycles = getConstInt(delayp->lhsp());
            if (delayCycles < 0) {
                delayp->v3error("Delay value is not a non-negative"
                                " elaboration-time constant"
                                " (IEEE 1800-2023 16.7)");
                return BuildResult::failWithError();
            }
            currentp = addDelayChain(currentp, delayCycles, flp);
        }

        // Multi-cycle RHS: recurse (only plain boolean is returned as finalCondp).
        AstNodeExpr* const exprp = sexprp->exprp();
        if (exprp->isMultiCycleSva()) return buildExpr(exprp, currentp, isTopLevelStep);
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
        const int minN = getConstInt(repp->countp());
        UASSERT_OBJ(minN >= 0, repp, "ConsRep count must be non-negative (V3Width invariant)");
        // Exact-repetition ConsRep is currently unrolled into minN vertices, so
        // we cap minN to keep compile size bounded. An unbounded or ranged rep
        // has already been rewritten to a counter-FSM path elsewhere.
        constexpr int kConsRepLimit = 256;
        // LCOV_EXCL_START -- compile-size guard; exercised only with >256-rep inputs
        if (minN > kConsRepLimit && !repp->unbounded() && !repp->maxCountp()) {
            return BuildResult::fail();
        }
        // LCOV_EXCL_STOP

        // Sum sites across prefix + unbounded/range tail so one hoist covers
        // every check edge of this repetition.
        int totalSites = minN;
        if (repp->unbounded()) {
            totalSites += 1;
        } else if (repp->maxCountp()) {
            totalSites += getConstInt(repp->maxCountp()) - minN;
        }
        AstVar* const hoistVarp = tryHoistSampled(exprp, flp, totalSites);

        SvaStateVertex* currentp = entryVtxp;
        for (int i = 0; i < minN; ++i) {
            if (i > 0) {
                SvaStateVertex* const nextp = scopedCreateVertex();
                guardedEdge(currentp, nextp, flp);
                currentp = nextp;
            }
            // Mark first and last boolean Links as rejectOnFail for correct
            // reject on standalone ConsRep.
            SvaStateVertex* const condVtxp = scopedCreateVertex();
            SvaTransEdge* const linkp
                = guardedLink(currentp, condVtxp, sampledRefOrClone(hoistVarp, exprp, flp), flp);
            if (isTopLevelStep && (i == 0 || i == minN - 1)) { linkp->m_rejectOnFail = true; }
            currentp = condVtxp;
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
            const int maxN = getConstInt(repp->maxCountp());
            UASSERT_OBJ(maxN >= minN, repp, "ConsRep range max < min (V3Width invariant)");
            SvaStateVertex* const mergeVtxp = scopedCreateVertex();
            guardedLink(currentp, mergeVtxp, flp);
            for (int i = minN; i < maxN; ++i) {
                SvaStateVertex* const nextVtxp = scopedCreateVertex();
                guardedEdge(currentp, nextVtxp, flp);
                SvaStateVertex* const checkVtxp = scopedCreateVertex();
                guardedLink(nextVtxp, checkVtxp, sampledRefOrClone(hoistVarp, exprp, flp), flp);
                guardedLink(checkVtxp, mergeVtxp, flp);
                currentp = checkVtxp;
            }
            currentp = mergeVtxp;
        }
        // finalCond = nullptr (already checked via Links)
        return {currentp, nullptr, {}};
    }

    // always[lo:hi] / s_always[lo:hi] (IEEE 1800-2023 16.12.11).
    BuildResult buildPropAlways(AstPropAlways* nodep, SvaStateVertex* entryVtxp,
                                bool isTopLevelStep = false) {
        FileLine* const flp = nodep->fileline();
        AstNodeExpr* const propp = nodep->propp();
        const int lo = getConstInt(nodep->loBoundp());
        const int hi = getConstInt(nodep->hiBoundp());
        UASSERT_OBJ(lo >= 0 && hi >= lo, nodep, "PropAlways bounds invariant (V3Width)");
        AstVar* const hoistVarp = tryHoistSampled(propp, flp, hi - lo + 1);
        SvaStateVertex* currentp = addDelayChain(entryVtxp, lo, flp);
        for (int k = 0; k <= hi - lo; ++k) {
            if (k > 0) {
                SvaStateVertex* const nextp = scopedCreateVertex();
                guardedEdge(currentp, nextp, flp);
                currentp = nextp;
            }
            SvaStateVertex* const checkp = scopedCreateVertex();
            SvaTransEdge* const linkp
                = guardedLink(currentp, checkp, sampledRefOrClone(hoistVarp, propp, flp), flp);
            if (isTopLevelStep && !m_inUnboundedScope) linkp->m_rejectOnFail = true;
            currentp = checkp;
        }
        return {currentp, nullptr, {}};
    }

    BuildResult buildGotoRep(AstSGotoRep* repp, SvaStateVertex* entryVtxp) {
        FileLine* const flp = repp->fileline();
        AstNodeExpr* const exprp = repp->exprp();
        const int n = getConstInt(repp->countp());
        if (n <= 0) return BuildResult::fail();

        // Wait + match per iter -> 2n sites. NOT($sampled(x)) matches
        // $sampled(NOT(x)) at the value level (IEEE 1800-2023 16.9.9);
        // purity is enforced uniformly via cloneTreePure inside sampledRefOrClone.
        AstVar* const hoistVarp = tryHoistSampled(exprp, flp, 2 * n);
        SvaStateVertex* currentp = entryVtxp;
        for (int i = 0; i < n; ++i) {
            SvaStateVertex* const waitVtxp = scopedCreateVertex();
            // Edge (not Link) for all iterations: IEEE expansion ##1 before each
            // match. A Link at i==0 was wrong -- it allowed same-cycle matching
            // and was discarded by Phase 2 (waitNode has a self-loop Edge).
            guardedEdge(currentp, waitVtxp, flp);
            AstNodeExpr* const waitCondp
                = new AstNot{flp, sampledRefOrClone(hoistVarp, exprp, flp)};
            guardedEdge(waitVtxp, waitVtxp, waitCondp, flp);
            SvaStateVertex* const matchVtxp = scopedCreateVertex();
            guardedLink(waitVtxp, matchVtxp, sampledRefOrClone(hoistVarp, exprp, flp), flp);
            currentp = matchVtxp;
        }
        currentp->m_isUnbounded = true;  // [->N] waits unboundedly
        m_inUnboundedScope = true;
        return {currentp, nullptr, {}};
    }

    // Build merge vertex for SOr / LogOr: both branches feed into one vertex.
    BuildResult buildOrMerge(AstNodeExpr* lhsp, AstNodeExpr* rhsp, SvaStateVertex* entryVtxp,
                             FileLine* flp) {
        const BuildResult lhs = buildExpr(lhsp, entryVtxp);
        const BuildResult rhs = buildExpr(rhsp, entryVtxp);
        if (!lhs.valid() || !rhs.valid()) {  // LCOV_EXCL_START -- sub-build fail bail
            return BuildResult::fail(lhs.errorEmitted || rhs.errorEmitted);
        }  // LCOV_EXCL_STOP
        SvaStateVertex* const mergeVtxp = scopedCreateVertex();
        if (lhs.finalCondp) {
            guardedLink(lhs.termVertexp, mergeVtxp, sampled(lhs.finalCondp->cloneTreePure(false)),
                        flp);
        } else {
            guardedLink(lhs.termVertexp, mergeVtxp, flp);
        }
        if (rhs.finalCondp) {
            guardedLink(rhs.termVertexp, mergeVtxp, sampled(rhs.finalCondp->cloneTreePure(false)),
                        flp);
        } else {
            guardedLink(rhs.termVertexp, mergeVtxp, flp);
        }
        return {mergeVtxp, nullptr, {}};
    }

    // Build done-latch combiner for SAnd/SIntersect (IEEE 1800-2023 16.9.5).
    BuildResult buildAndCombiner(AstNodeExpr* lhsExprp, AstNodeExpr* rhsExprp,
                                 SvaStateVertex* entryVtxp, FileLine* flp) {
        // Snapshot-restore scope so LHS liveness does not leak into RHS.
        const bool savedScope = m_inUnboundedScope;
        const BuildResult lhs = buildExpr(lhsExprp, entryVtxp);
        const bool lhsScope = m_inUnboundedScope;
        m_inUnboundedScope = savedScope;
        const BuildResult rhs = buildExpr(rhsExprp, entryVtxp);
        const bool rhsScope = m_inUnboundedScope;
        m_inUnboundedScope = savedScope || lhsScope || rhsScope;
        if (!lhs.valid() || !rhs.valid()) {  // LCOV_EXCL_START -- sub-build fail bail
            return BuildResult::fail(lhs.errorEmitted || rhs.errorEmitted);
        }  // LCOV_EXCL_STOP

        // Single-cycle operands: use boolean AND (done-latch would fire across cycles).
        // If both operands stayed at entry, they must be boolean leaves which
        // buildExpr returns with finalCondp=nodep (non-null).
        if (lhs.termVertexp == entryVtxp && rhs.termVertexp == entryVtxp) {
            UASSERT_OBJ(lhs.finalCondp && rhs.finalCondp, lhsExprp,
                        "Single-cycle SAnd operands must have finalCondp");
            AstNodeExpr* const condp = new AstAnd{flp, lhs.finalCondp->cloneTreePure(false),
                                                  rhs.finalCondp->cloneTreePure(false)};
            return {entryVtxp, condp, {}};
        }
        // Range-delay mid-window sources in either sub-branch would need
        // to be folded into the latch's match-now signal, which the
        // current combiner does not support. Defer (UNSUPPORTED).
        if (!lhs.midSources.empty() || !rhs.midSources.empty()) return BuildResult::fail();
        SvaStateVertex* const combVtxp = scopedCreateVertex();
        combVtxp->m_isAndCombiner = true;
        combVtxp->m_andLhsTermp = lhs.termVertexp;
        combVtxp->m_andRhsTermp = rhs.termVertexp;
        if (lhs.finalCondp) combVtxp->m_andLhsCondp = lhs.finalCondp->cloneTreePure(false);
        if (rhs.finalCondp) combVtxp->m_andRhsCondp = rhs.finalCondp->cloneTreePure(false);
        if (lhs.termVertexp->m_isUnbounded || rhs.termVertexp->m_isUnbounded) {
            combVtxp->m_isUnbounded = true;
        }
        // Wire terminal-boolean rejects to a dedicated sink so each side can fail
        // the AND independently. Skip for liveness or single-cycle operands
        // (single-cycle termVertexp == entryVtxp would fire every cycle).
        if (!combVtxp->m_isUnbounded) {
            bool needSink = false;
            const bool lhsMultiCycle = (lhs.termVertexp != entryVtxp);
            const bool rhsMultiCycle = (rhs.termVertexp != entryVtxp);
            if (lhs.finalCondp && lhsMultiCycle && !lhs.termVertexp->m_isUnbounded) {
                needSink = true;
            }
            if (rhs.finalCondp && rhsMultiCycle && !rhs.termVertexp->m_isUnbounded) {
                needSink = true;
            }
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
        return {combVtxp, nullptr, {}};
    }

    // Lower `seq1 within seq2` (IEEE 1800-2023 16.9.10) as:
    //   (OR_{i in 0..slack} 1 ##i seq1 ##(slack-i) 1) intersect seq2
    // Both operands must have fixed length (no ranged cycle delays).
    // The OR lives inside a single SIntersect so one AndCombiner done-latch
    // serves all offsets; lifting it out would double-count matches where
    // multiple offsets accept on the same seq2 end cycle.
    BuildResult buildSWithin(AstSWithin* nodep, SvaStateVertex* entryVtxp,
                             bool isTopLevelStep = false) {
        const int innerLen = fixedLength(nodep->lhsp());
        const int outerLen = fixedLength(nodep->rhsp());
        if (innerLen < 0 || outerLen < 0) {
            nodep->v3warn(E_UNSUPPORTED, "Unsupported: within with ranged cycle-delay operand");
            return BuildResult::failWithError();
        }
        if (innerLen > outerLen) {
            nodep->v3error("'within' inner sequence " + std::to_string(innerLen)
                           + " cycles exceeds outer sequence " + std::to_string(outerLen)
                           + " cycles (IEEE 1800-2023 16.9.10)");
            return BuildResult::failWithError();
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
        // When both operands are plain booleans, buildAndCombiner returns a
        // freshly-allocated AstAnd as finalCondp with no parent. Callers up
        // the chain clone-and-discard finalCondp, so leave it parent-less and
        // it leaks; anchor it in the graph now via an edge.
        if (result.valid() && result.finalCondp && !result.finalCondp->backp()) {
            SvaStateVertex* const wrapVtxp = scopedCreateVertex();
            guardedLink(result.termVertexp, wrapVtxp, sampled(result.finalCondp), flp);
            result = {wrapVtxp, nullptr, result.midSources};
        }
        return result;
    }

    BuildResult buildThroughout(AstSThroughout* nodep, SvaStateVertex* entryVtxp,
                                bool isTopLevelStep = false) {
        // Mark entryVtxp so "cond false at tick 0" is detected as throughout-drop.
        entryVtxp->m_throughoutConds.push_back(nodep->lhsp()->cloneTreePure(false));
        m_throughoutStack.push_back(nodep->lhsp());
        const BuildResult result = buildExpr(nodep->rhsp(), entryVtxp, isTopLevelStep);
        m_throughoutStack.pop_back();
        return result;
    }

public:
    SvaNfaBuilder(SvaGraph& graph, AstNodeModule* modp, V3UniqueNames& propTempNames)
        : m_graph{graph}
        , m_modp{modp}
        , m_propTempNames{propTempNames} {}

    // Reset scope between antecedent and consequent: liveness must not leak.
    void resetScope() {
        m_inUnboundedScope = false;
        m_throughoutStack.clear();
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
            return buildOrMerge(orp->lhsp(), orp->rhsp(), entryVtxp, orp->fileline());
        }
        if (AstLogOr* const orp = VN_CAST(nodep, LogOr)) {
            return buildOrMerge(orp->lhsp(), orp->rhsp(), entryVtxp, orp->fileline());
        }
        if (AstSAnd* const andp = VN_CAST(nodep, SAnd)) {
            return buildAndCombiner(andp->lhsp(), andp->rhsp(), entryVtxp, andp->fileline());
        }
        if (AstSIntersect* const intp = VN_CAST(nodep, SIntersect)) {
            // IEEE 1800-2023 16.9.6: SAnd with equal-length constraint.
            // Variable-length intersect deferred to follow-up.
            const int lhsLen = fixedLength(intp->lhsp());
            const int rhsLen = fixedLength(intp->rhsp());
            if (lhsLen < 0 || rhsLen < 0) return BuildResult::fail();
            if (lhsLen != rhsLen) {
                intp->v3error("Intersect sequence length mismatch: left " + std::to_string(lhsLen)
                              + " cycles, right " + std::to_string(rhsLen)
                              + " cycles (IEEE 1800-2023 16.9.6)");
                return BuildResult::failWithError();
            }
            return buildAndCombiner(intp->lhsp(), intp->rhsp(), entryVtxp, intp->fileline());
        }
        if (AstSWithin* const withinp = VN_CAST(nodep, SWithin)) {
            return buildSWithin(withinp, entryVtxp, isTopLevelStep);
        }
        if (VN_IS(nodep, SNonConsRep)) return BuildResult::fail();
        if (AstImplication* const implp = VN_CAST(nodep, Implication)) {
            return buildImplicationEdges(implp->lhsp(), implp->rhsp(), entryVtxp,
                                         implp->isOverlapped(), implp->isFollowedBy(),
                                         implp->lhsp(), implp->fileline());
        }
        // Boolean leaf (including LogAnd): return as finalCond
        return {entryVtxp, nodep, {}};
    }

    // Wire an implication / followed-by from `entryVtxp`: builds the antecedent,
    // emits the match-link (and for followed-by the reject-sink edge), inserts a
    // delay vertex for non-overlapped forms, and builds the body. Used both for
    // nested AstImplication in pexpr position and for the top-level assertion
    // antecedent -- `errorNodep` anchors the "unsupported sequence antecedent"
    // error, which differs between the two call sites.
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
// NFA Lowering (converts NFA graph to synthesizable AstAlways blocks)

class SvaNfaLowering final {
    AstNodeModule* const m_modp;  // Module to add state vars and always blocks to
    V3UniqueNames m_names{"__Vnfa"};

    // Per-lowering shared context (passed to phase sub-functions)
    // Per-vertex lowering state is stored in SvaVertexData and accessed via
    // V3GraphVertex::userp() (see vtx[i]->datap()).
    struct LowerCtx final {
        FileLine* flp;  // Source location for generated AST
        int N;  // Number of vertices
        std::vector<SvaStateVertex*> vtx;  // Color-indexed vertex lookup
        std::vector<const SvaTransEdge*> edges;  // All edges (flat)
        int startIdx;  // Start vertex color index
        int matchIdx;  // Match vertex color index (-1 if none)
        AstSenTree* senTreep;  // Clock sensitivity tree
        AstNodeExpr* disableExprp;  // disable iff expression (may be nullptr)
        AstNodeExpr* matchCondp;  // Final boolean match condition (may be nullptr)
        AstVar* disableCntVarp;  // disable counter var (may be nullptr)
        AstVar* snapshotVarp;  // disable snapshot var (may be nullptr)
        SvaGraph& graph;  // NFA graph
    };

    // Build a match-now expression: stateSig[i] && $sampled(condp)
    static AstNodeExpr* buildMatchNow(FileLine* flp, AstNodeExpr* stateExprp, AstNodeExpr* condp) {
        AstNodeExpr* const statep = stateExprp->cloneTreePure(false);
        if (!condp) return statep;
        AstSampled* const sampp = new AstSampled{flp, condp->cloneTreePure(false)};
        sampp->dtypeFrom(condp);
        return new AstAnd{flp, statep, sampp};
    }
    static AstNodeExpr* andCond(FileLine* flp, AstNodeExpr* exprp, AstNodeExpr* condp) {
        if (!condp) return exprp;
        return new AstAnd{flp, exprp, condp->cloneTreePure(false)};
    }
    // bp is always non-null; only ap can be null (serving as accumulator).
    static AstNodeExpr* orExprs(FileLine* flp, AstNodeExpr* ap, AstNodeExpr* bp) {
        if (!ap) return bp;
        return new AstOr{flp, ap, bp};
    }

    // Phase 3 output signals
    struct SignalSet final {
        AstNodeExpr* terminalActivep = nullptr;  // OR of all successful terminal matches
        AstNodeExpr* rejectBasep = nullptr;  // Reject when a terminal match fails
        AstNodeExpr* requiredStepRejectp = nullptr;  // Per-source reject from rejectOnFail Links
        AstNodeExpr* throughoutRejectp = nullptr;  // Reject when a throughout guard drops
    };

    // Phase 2/2b/2c: Emit NBA state-update always blocks for registered vertices,
    // counter FSMs, and SAnd combiner done-latches.
    // Phase 2: State register NBA always block. Each clocked-edge target
    // latches the OR of its incoming contributions.
    void emitStateRegisterNba(LowerCtx& c) {
        AstNode* bodyp = nullptr;
        for (int i = 0; i < c.N; ++i) {
            if (!c.vtx[i]->datap()->stateVarp) continue;

            AstNodeExpr* nextStatep = nullptr;
            for (const V3GraphEdge& er : c.vtx[i]->inEdges()) {
                const SvaTransEdge& te = static_cast<const SvaTransEdge&>(er);
                if (!te.m_consumesCycle) continue;
                const int fromIdx = te.fromVtxp()->color();
                UASSERT_OBJ(c.vtx[fromIdx]->datap()->stateSigp, te.fromVtxp(),
                            "Clocked-edge source missing stateSig");

                AstNodeExpr* srcSigp = c.vtx[fromIdx]->datap()->stateSigp->cloneTreePure(false);
                srcSigp = andCond(c.flp, srcSigp, te.m_condp);

                if (c.disableExprp && !c.snapshotVarp) {
                    AstNodeExpr* const notDisp
                        = new AstNot{c.flp, c.disableExprp->cloneTreePure(false)};
                    srcSigp = new AstAnd{c.flp, srcSigp, notDisp};
                }
                nextStatep = orExprs(c.flp, nextStatep, srcSigp);
            }

            UASSERT_OBJ(nextStatep, c.vtx[i],
                        "Registered vertex has no clocked incoming contribution");

            AstAssignDly* const assignp = new AstAssignDly{
                c.flp, new AstVarRef{c.flp, c.vtx[i]->datap()->stateVarp, VAccess::WRITE},
                nextStatep};
            if (!bodyp) {
                bodyp = assignp;
            } else {
                bodyp->addNext(assignp);
            }
        }

        if (!bodyp) return;
        // Capture disableCnt in Phase-2 NBA before any reactive re-evaluation.
        // snapshotVarp and disableCntVarp are allocated together.
        if (c.snapshotVarp) {
            UASSERT_OBJ(c.disableCntVarp, c.senTreep, "snapshotVarp set without disableCntVarp");
            bodyp->addNext(
                new AstAssignDly{c.flp, new AstVarRef{c.flp, c.snapshotVarp, VAccess::WRITE},
                                 new AstVarRef{c.flp, c.disableCntVarp, VAccess::READ}});
        }
        m_modp->addStmtsp(
            new AstAlways{c.flp, VAlwaysKwd::ALWAYS, c.senTreep->cloneTree(false), bodyp});
    }

    // Phase 2b: Counter FSM always block.
    // if (active) { if (done) active<=0; else counter<=counter+1; }
    // else if (incoming) { active<=1; counter<=0; }
    void emitCounterFsmNba(LowerCtx& c) {
        for (int ci = 0; ci < c.N; ++ci) {
            if (!c.vtx[ci]->datap()->counterActiveVarp) continue;
            AstVar* const activep = c.vtx[ci]->datap()->counterActiveVarp;
            AstVar* const cntp = c.vtx[ci]->datap()->counterCountVarp;
            const uint32_t counterMax = static_cast<uint32_t>(c.vtx[ci]->m_counterMax);

            // Builder only adds clocked edges to counter vertices (guardedEdge
            // in buildSExpr), so m_consumesCycle is always true here.
            AstNodeExpr* incomingp = nullptr;
            for (const SvaTransEdge* const tep : c.edges) {
                const int toIdx = tep->toVtxp()->color();
                if (toIdx != ci) continue;
                const int fi = tep->fromVtxp()->color();
                UASSERT_OBJ(c.vtx[fi]->datap()->stateSigp, c.vtx[fi],
                            "Clocked edge source missing stateSig");
                AstNodeExpr* contribp = c.vtx[fi]->datap()->stateSigp->cloneTreePure(false);
                contribp = andCond(c.flp, contribp, tep->m_condp);
                if (c.disableExprp) {
                    AstNodeExpr* const notDisp
                        = new AstNot{c.flp, c.disableExprp->cloneTreePure(false)};
                    contribp = new AstAnd{c.flp, contribp, notDisp};
                }
                incomingp = orExprs(c.flp, incomingp, contribp);
            }
            UASSERT_OBJ(incomingp, c.vtx[ci], "Counter vertex has no incoming contribution");

            // Counter window is always [0, m_counterMax]; M offset is handled by
            // the pre-chain in buildSExpr, so every tick inside an active count
            // is in-window.
            AstNodeExpr* inWindowp = new AstConst{c.flp, AstConst::BitTrue{}};
            AstNodeExpr* matchedNowp = nullptr;
            if (c.matchCondp) {
                AstSampled* const sampp
                    = new AstSampled{c.flp, c.matchCondp->cloneTreePure(false)};
                sampp->dtypeFrom(c.matchCondp);
                matchedNowp = new AstAnd{c.flp, inWindowp, sampp};
            } else {  // LCOV_EXCL_LINE -- no counter-FSM caller leaves matchCondp null
                matchedNowp = inWindowp;  // LCOV_EXCL_LINE
            }

            AstNodeExpr* const counterAtEndp
                = new AstEq{c.flp, new AstVarRef{c.flp, cntp, VAccess::READ},
                            new AstConst{c.flp, AstConst::WidthedValue{}, 32, counterMax}};

            AstNodeExpr* const donep = new AstOr{c.flp, matchedNowp, counterAtEndp};

            AstAssignDly* const clearActivep
                = new AstAssignDly{c.flp, new AstVarRef{c.flp, activep, VAccess::WRITE},
                                   new AstConst{c.flp, AstConst::BitFalse{}}};
            AstAdd* const addExprp
                = new AstAdd{c.flp, new AstVarRef{c.flp, cntp, VAccess::READ},
                             new AstConst{c.flp, AstConst::WidthedValue{}, 32, 1u}};
            addExprp->dtypeFrom(cntp);
            AstAssignDly* const incCountp
                = new AstAssignDly{c.flp, new AstVarRef{c.flp, cntp, VAccess::WRITE}, addExprp};
            AstIf* const doneIfp = new AstIf{c.flp, donep, clearActivep, incCountp};

            AstAssignDly* const setActivep
                = new AstAssignDly{c.flp, new AstVarRef{c.flp, activep, VAccess::WRITE},
                                   new AstConst{c.flp, AstConst::BitTrue{}}};
            AstAssignDly* const resetCountp
                = new AstAssignDly{c.flp, new AstVarRef{c.flp, cntp, VAccess::WRITE},
                                   new AstConst{c.flp, AstConst::WidthedValue{}, 32, 0u}};
            setActivep->addNext(resetCountp);
            AstIf* const startIfp = new AstIf{c.flp, incomingp, setActivep, nullptr};
            AstIf* const topIfp = new AstIf{c.flp, new AstVarRef{c.flp, activep, VAccess::READ},
                                            doneIfp, startIfp};

            m_modp->addStmtsp(
                new AstAlways{c.flp, VAlwaysKwd::ALWAYS, c.senTreep->cloneTree(false), topIfp});
        }
    }

    // Phase 2c: SAnd combiner done-latch always block.
    // NBA semantics ensure doneL/doneR read pre-update values (IEEE 16.9.5).
    void emitAndCombinerDoneLatchNba(LowerCtx& c) {
        for (int ai = 0; ai < c.N; ++ai) {
            if (!c.vtx[ai]->datap()->doneLVarp) continue;
            // doneLVars is non-null only for AndCombiner vertices, which always
            // have both m_andLhsTermp and m_andRhsTermp set at build time.
            const SvaStateVertex* const avp = c.vtx[ai];
            UASSERT_OBJ(avp->m_andLhsTermp && avp->m_andRhsTermp, avp,
                        "AndCombiner vertex missing LHS/RHS terminal");
            const int l = avp->m_andLhsTermp->color();
            const int r = avp->m_andRhsTermp->color();
            // resolveLinks' 2*N+2 fixed-point pass is guaranteed to populate
            // stateSigp on every AndCombiner and its LHS/RHS terminals.
            UASSERT_OBJ(c.vtx[l]->datap()->stateSigp && c.vtx[r]->datap()->stateSigp
                            && c.vtx[ai]->datap()->stateSigp,
                        avp, "AndCombiner stateSigp chain unresolved after resolveLinks");

            AstAssignDly* const clearLp = new AstAssignDly{
                c.flp, new AstVarRef{c.flp, c.vtx[ai]->datap()->doneLVarp, VAccess::WRITE},
                new AstConst{c.flp, AstConst::BitFalse{}}};
            AstAssignDly* const clearRp = new AstAssignDly{
                c.flp, new AstVarRef{c.flp, c.vtx[ai]->datap()->doneRVarp, VAccess::WRITE},
                new AstConst{c.flp, AstConst::BitFalse{}}};
            clearLp->addNext(clearRp);

            AstNodeExpr* const matchLNowp
                = buildMatchNow(c.flp, c.vtx[l]->datap()->stateSigp, avp->m_andLhsCondp);
            AstNodeExpr* const matchRNowp
                = buildMatchNow(c.flp, c.vtx[r]->datap()->stateSigp, avp->m_andRhsCondp);
            AstNodeExpr* gateLp = matchLNowp;
            AstNodeExpr* gateRp = matchRNowp;
            if (c.disableExprp) {
                AstNodeExpr* const notDisLp
                    = new AstNot{c.flp, c.disableExprp->cloneTreePure(false)};
                gateLp = new AstAnd{c.flp, gateLp, notDisLp};
                AstNodeExpr* const notDisRp
                    = new AstNot{c.flp, c.disableExprp->cloneTreePure(false)};
                gateRp = new AstAnd{c.flp, gateRp, notDisRp};
            }
            AstAssignDly* const setLp = new AstAssignDly{
                c.flp, new AstVarRef{c.flp, c.vtx[ai]->datap()->doneLVarp, VAccess::WRITE},
                new AstConst{c.flp, AstConst::BitTrue{}}};
            AstIf* const setLIfp = new AstIf{c.flp, gateLp, setLp, nullptr};
            AstAssignDly* const setRp = new AstAssignDly{
                c.flp, new AstVarRef{c.flp, c.vtx[ai]->datap()->doneRVarp, VAccess::WRITE},
                new AstConst{c.flp, AstConst::BitTrue{}}};
            AstIf* const setRIfp = new AstIf{c.flp, gateRp, setRp, nullptr};
            setLIfp->addNext(setRIfp);

            AstIf* const topp = new AstIf{
                c.flp, c.vtx[ai]->datap()->stateSigp->cloneTreePure(false), clearLp, setLIfp};
            m_modp->addStmtsp(
                new AstAlways{c.flp, VAlwaysKwd::ALWAYS, c.senTreep->cloneTree(false), topp});
        }
    }

    // Phase 3/3a/3b: Compute terminal match/reject signals, required-step reject,
    // throughout-drop reject; clean up intermediate state signals.
    // Phase 3: terminalActive and rejectBase from Links to matchVertex.
    // Builder only adds Links (non-clocked) to matchVertex via addLink in
    // wireMatchAndMidSources.
    void computeTerminalMatchAndReject(LowerCtx& c, AstNodeExpr* snapshotOkp, SignalSet& sigs) {
        for (const SvaTransEdge* const tep : c.edges) {
            if (tep->toVtxp() != c.graph.m_matchVertexp) continue;
            const int fi = tep->fromVtxp()->color();
            UASSERT_OBJ(c.vtx[fi]->datap()->stateSigp, tep->fromVtxp(),
                        "Terminal-link source missing stateSig");

            AstNodeExpr* srcSigp = c.vtx[fi]->datap()->stateSigp->cloneTreePure(false);
            srcSigp = andCond(c.flp, srcSigp, tep->m_condp);
            if (snapshotOkp) {
                srcSigp = new AstAnd{c.flp, srcSigp, snapshotOkp->cloneTreePure(false)};
            }

            if (tep->fromVtxp()->m_isCounter) {
                sigs.terminalActivep
                    = orExprs(c.flp, sigs.terminalActivep, srcSigp->cloneTreePure(false));
                AstNodeExpr* const atEndp = new AstEq{
                    c.flp,
                    new AstVarRef{c.flp, c.vtx[fi]->datap()->counterCountVarp, VAccess::READ},
                    new AstConst{c.flp, AstConst::WidthedValue{}, 32,
                                 static_cast<uint32_t>(tep->fromVtxp()->m_counterMax)}};
                AstNodeExpr* const expireContribp = new AstAnd{c.flp, srcSigp, atEndp};
                sigs.rejectBasep = orExprs(c.flp, sigs.rejectBasep, expireContribp);
            } else if (tep->fromVtxp()->m_isUnbounded || tep->fromVtxp()->m_isAndCombiner) {
                sigs.terminalActivep = orExprs(c.flp, sigs.terminalActivep, srcSigp);
            } else {
                sigs.terminalActivep
                    = orExprs(c.flp, sigs.terminalActivep, srcSigp->cloneTreePure(false));
                sigs.rejectBasep = orExprs(c.flp, sigs.rejectBasep, srcSigp);
            }
        }
        // wireMatchAndMidSources always adds a Link from result.termVertexp
        // to m_matchVertexp, so the loop above always sets terminalActivep.
        UASSERT_OBJ(sigs.terminalActivep, c.graph.m_matchVertexp,
                    "No terminal edge to match vertex");
    }

    // Phase 3b: Throughout-drop rejection (IEEE 16.9.9).
    void computeThroughoutReject(LowerCtx& c, SignalSet& sigs) {
        for (int i = 0; i < c.N; ++i) {
            const auto& conds = c.vtx[i]->m_throughoutConds;
            if (conds.empty()) continue;
            if (c.vtx[i]->m_isAndCombiner) continue;
            AstNodeExpr* stateExprp = nullptr;
            if (c.vtx[i]->datap()->stateVarp) {
                stateExprp = new AstVarRef{c.flp, c.vtx[i]->datap()->stateVarp, VAccess::READ};
            } else {
                UASSERT_OBJ(c.vtx[i]->datap()->stateSigp, c.vtx[i],
                            "Throughout-conds vertex missing state representation");
                stateExprp = c.vtx[i]->datap()->stateSigp->cloneTreePure(false);
            }
            AstNodeExpr* guardp = nullptr;
            for (AstNodeExpr* const cp : conds) {
                AstSampled* const sp = new AstSampled{c.flp, cp->cloneTreePure(false)};
                sp->dtypeFrom(cp);
                guardp = guardp ? static_cast<AstNodeExpr*>(new AstAnd{c.flp, guardp, sp}) : sp;
            }
            AstNodeExpr* const notGuardp = new AstNot{c.flp, guardp};
            sigs.throughoutRejectp
                = orExprs(c.flp, sigs.throughoutRejectp, new AstAnd{c.flp, stateExprp, notGuardp});
        }
    }

    SignalSet computeSignals(LowerCtx& c, std::vector<AstNodeExpr*>* outRequiredStepSrcsp) {
        SignalSet sigs;

        // Snapshot comparison expression for disable-iff counter.
        // snapshotVarp and disableCntVarp are allocated together.
        AstNodeExpr* snapshotOkp = nullptr;
        if (c.snapshotVarp) {
            UASSERT_OBJ(c.disableCntVarp, c.senTreep, "snapshotVarp set without disableCntVarp");
            snapshotOkp = new AstEq{c.flp, new AstVarRef{c.flp, c.snapshotVarp, VAccess::READ},
                                    new AstVarRef{c.flp, c.disableCntVarp, VAccess::READ}};
        }

        computeTerminalMatchAndReject(c, snapshotOkp, sigs);

        // Phase 3a: required-step rejection.
        // Builder only sets m_rejectOnFail on non-clocked Links with m_condp,
        // and the source always has a resolved stateSig.
        for (const SvaTransEdge* const tep : c.edges) {
            if (!tep->m_rejectOnFail) continue;
            const int fi = tep->fromVtxp()->color();
            UASSERT_OBJ(c.vtx[fi]->datap()->stateSigp && tep->m_condp, tep->fromVtxp(),
                        "rejectOnFail Link must have condp and source stateSig");
            AstNodeExpr* const srcSigp = c.vtx[fi]->datap()->stateSigp->cloneTreePure(false);
            AstNodeExpr* const notCondp = new AstNot{c.flp, tep->m_condp->cloneTreePure(false)};
            AstNodeExpr* const failp = new AstAnd{c.flp, srcSigp, notCondp};
            if (outRequiredStepSrcsp) {
                outRequiredStepSrcsp->push_back(failp->cloneTreePure(false));
            }
            sigs.requiredStepRejectp = orExprs(c.flp, sigs.requiredStepRejectp, failp);
        }

        computeThroughoutReject(c, sigs);

        // Clean up intermediate state signals. These are orphan subtrees
        // (never linked into the enclosing AST); deleteTree() is immediate
        // which is what we want since stateSigp lifetime ends with this scope.
        for (int i = 0; i < c.N; ++i) {
            AstNodeExpr*& sigp = c.vtx[i]->datap()->stateSigp;
            if (sigp) VL_DO_DANGLING(sigp->deleteTree(), sigp);
        }
        // Disable iff gating on throughout/required-step rejects (IEEE 16.12).
        if (c.disableExprp) {
            if (sigs.throughoutRejectp) {
                AstNodeExpr* const notDisp
                    = new AstNot{c.flp, c.disableExprp->cloneTreePure(false)};
                sigs.throughoutRejectp = new AstAnd{c.flp, sigs.throughoutRejectp, notDisp};
            }
            if (sigs.requiredStepRejectp) {
                AstNodeExpr* const notDisp
                    = new AstNot{c.flp, c.disableExprp->cloneTreePure(false)};
                sigs.requiredStepRejectp = new AstAnd{c.flp, sigs.requiredStepRejectp, notDisp};
            }
        }

        if (snapshotOkp) {
            VL_DO_DANGLING(snapshotOkp->deleteTree(), snapshotOkp);
            snapshotOkp = nullptr;
        }
        if (c.disableExprp) {
            VL_DO_DANGLING(c.disableExprp->deleteTree(), c.disableExprp);
            c.disableExprp = nullptr;
        }

        return sigs;
    }

    // Phase 1: Resolve combinational Links via fixed-point propagation.
    void resolveLinks(LowerCtx& c, AstNodeExpr* triggerExprp) {
        // datap() was freshly allocated in lower() -- all stateSigp start null.
        c.vtx[c.startIdx]->datap()->stateSigp = triggerExprp->cloneTreePure(false);
        for (int i = 0; i < c.N; ++i) {
            if (c.vtx[i]->datap()->stateVarp) {
                c.vtx[i]->datap()->stateSigp
                    = new AstVarRef{c.flp, c.vtx[i]->datap()->stateVarp, VAccess::READ};
            } else if (c.vtx[i]->datap()->counterActiveVarp) {
                // Counter window is always [0, m_counterMax]; see buildSExpr.
                c.vtx[i]->datap()->stateSigp
                    = new AstVarRef{c.flp, c.vtx[i]->datap()->counterActiveVarp, VAccess::READ};
            }
        }
        // Fixed-point propagation along zero-delay (Link) edges.
        // Worst case: longest chain is N hops; SAnd seeding adds one extra round;
        // factor-of-2 covers reverse-order dependencies.
        for (int pass = 0; pass < 2 * c.N + 2; ++pass) {
            bool changed = false;
            // Seed SAnd combiners (sub-NFA termVertices may only be available
            // after a propagation pass).
            for (int i = 0; i < c.N; ++i) {
                if (!c.vtx[i]->m_isAndCombiner) continue;
                if (c.vtx[i]->datap()->stateSigp) continue;
                // AndCombiner vertices always have both terminal pointers set.
                UASSERT_OBJ(c.vtx[i]->m_andLhsTermp && c.vtx[i]->m_andRhsTermp, c.vtx[i],
                            "AndCombiner vertex missing LHS/RHS terminal");
                const int l = c.vtx[i]->m_andLhsTermp->color();
                const int r = c.vtx[i]->m_andRhsTermp->color();
                if (!c.vtx[l]->datap()->stateSigp || !c.vtx[r]->datap()->stateSigp) continue;
                AstNodeExpr* const matchLp
                    = buildMatchNow(c.flp, c.vtx[l]->datap()->stateSigp, c.vtx[i]->m_andLhsCondp);
                AstNodeExpr* const matchRp
                    = buildMatchNow(c.flp, c.vtx[r]->datap()->stateSigp, c.vtx[i]->m_andRhsCondp);
                AstNodeExpr* const doneLOrp = new AstOr{
                    c.flp, new AstVarRef{c.flp, c.vtx[i]->datap()->doneLVarp, VAccess::READ},
                    matchLp};
                AstNodeExpr* const doneROrp = new AstOr{
                    c.flp, new AstVarRef{c.flp, c.vtx[i]->datap()->doneRVarp, VAccess::READ},
                    matchRp};
                AstNodeExpr* const bothp = new AstAnd{c.flp, doneLOrp, doneROrp};
                AstNodeExpr* const oneNowp = new AstOr{c.flp, matchLp->cloneTreePure(false),
                                                       matchRp->cloneTreePure(false)};
                c.vtx[i]->datap()->stateSigp = new AstAnd{c.flp, bothp, oneNowp};
                changed = true;
            }
            // Propagate Link edges
            for (int fi = 0; fi < c.N; ++fi) {
                if (!c.vtx[fi]->datap()->stateSigp) continue;
                for (const V3GraphEdge& er : c.vtx[fi]->outEdges()) {
                    const SvaTransEdge& te = static_cast<const SvaTransEdge&>(er);
                    if (te.m_consumesCycle) continue;
                    const int ti = te.toVtxp()->color();
                    if (te.toVtxp()->m_isMatch || te.toVtxp()->m_isRejectSink) continue;
                    AstNodeExpr* const contributionp = andCond(
                        c.flp, c.vtx[fi]->datap()->stateSigp->cloneTreePure(false), te.m_condp);
                    if (!c.vtx[ti]->datap()->stateSigp) {
                        c.vtx[ti]->datap()->stateSigp = contributionp;
                        changed = true;
                    } else if (!c.vtx[ti]->datap()->needsReg) {
                        c.vtx[ti]->datap()->stateSigp
                            = orExprs(c.flp, c.vtx[ti]->datap()->stateSigp, contributionp);
                        changed = true;
                    } else {
                        VL_DO_DANGLING(contributionp->deleteTree(), contributionp);
                    }
                }
            }
            if (!changed) break;
        }
    }

    // Combine terminal/reject signals into final output expression.
    AstNodeExpr* assembleResult(FileLine* flp, bool isCover, bool negated, AstNodeExpr* matchCondp,
                                AstNodeExpr* terminalActivep, AstNodeExpr* rejectBasep,
                                AstNodeExpr* throughoutRejectp, AstNodeExpr* requiredStepRejectp,
                                AstNodeExpr** outMatchpp) {
        // Property negation (IEEE 1800-2023 16.12.1 `not`): invert match/reject.
        if (negated) {
            if (isCover) {
                if (terminalActivep)
                    VL_DO_DANGLING(terminalActivep->deleteTree(), terminalActivep);
                AstNodeExpr* negRejectp = nullptr;
                if (matchCondp && rejectBasep) {
                    AstNodeExpr* const sampledCondp
                        = new AstSampled{flp, matchCondp->cloneTreePure(false)};
                    sampledCondp->dtypeFrom(matchCondp);
                    AstNodeExpr* const notCondp = new AstNot{flp, sampledCondp};
                    negRejectp = new AstAnd{flp, rejectBasep, notCondp};
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
                AstNodeExpr* const sampledCondp
                    = new AstSampled{flp, matchCondp->cloneTreePure(false)};
                sampledCondp->dtypeFrom(matchCondp);
                matchp = new AstAnd{flp, matchp, sampledCondp};
            }
            if (outMatchpp) {
                AstNodeExpr* notPMatchp = nullptr;
                if (matchCondp && rejectBasep) {
                    AstNodeExpr* const sampledCondp
                        = new AstSampled{flp, matchCondp->cloneTreePure(false)};
                    sampledCondp->dtypeFrom(matchCondp);
                    notPMatchp = new AstAnd{flp, rejectBasep->cloneTreePure(false),
                                            new AstNot{flp, sampledCondp}};
                } else if (rejectBasep) {
                    notPMatchp = rejectBasep->cloneTreePure(false);
                }
                if (throughoutRejectp)
                    notPMatchp = orExprs(flp, notPMatchp, throughoutRejectp->cloneTreePure(false));
                if (requiredStepRejectp)
                    notPMatchp
                        = orExprs(flp, notPMatchp, requiredStepRejectp->cloneTreePure(false));
                *outMatchpp = notPMatchp;
            }
            if (throughoutRejectp)
                VL_DO_DANGLING(throughoutRejectp->deleteTree(), throughoutRejectp);
            if (rejectBasep) VL_DO_DANGLING(rejectBasep->deleteTree(), rejectBasep);
            if (requiredStepRejectp)
                VL_DO_DANGLING(requiredStepRejectp->deleteTree(), requiredStepRejectp);
            AstNodeExpr* const resultExprp = new AstNot{flp, matchp};
            return resultExprp;
        }
        if (isCover) {
            if (throughoutRejectp)
                VL_DO_DANGLING(throughoutRejectp->deleteTree(), throughoutRejectp);
            if (rejectBasep) VL_DO_DANGLING(rejectBasep->deleteTree(), rejectBasep);
            if (requiredStepRejectp)
                VL_DO_DANGLING(requiredStepRejectp->deleteTree(), requiredStepRejectp);
            if (matchCondp) {
                AstNodeExpr* const sampledCondp
                    = new AstSampled{flp, matchCondp->cloneTreePure(false)};
                sampledCondp->dtypeFrom(matchCondp);
                return new AstAnd{flp, terminalActivep, sampledCondp};
            }
            return terminalActivep;
        }
        // Assert/assume: output = !reject
        AstNodeExpr* rejectp = nullptr;
        if (matchCondp && rejectBasep) {
            AstNodeExpr* const sampledCondp
                = new AstSampled{flp, matchCondp->cloneTreePure(false)};
            sampledCondp->dtypeFrom(matchCondp);
            rejectp = new AstAnd{flp, rejectBasep, new AstNot{flp, sampledCondp}};
        } else if (rejectBasep) {
            VL_DO_DANGLING(rejectBasep->deleteTree(), rejectBasep);
        }
        if (outMatchpp) {
            AstNodeExpr* matchExprp = terminalActivep->cloneTreePure(false);
            if (matchCondp) {
                AstSampled* const sp = new AstSampled{flp, matchCondp->cloneTreePure(false)};
                sp->dtypeFrom(matchCondp);
                matchExprp = new AstAnd{flp, matchExprp, sp};
            }
            *outMatchpp = matchExprp;
        }
        if (terminalActivep) VL_DO_DANGLING(terminalActivep->deleteTree(), terminalActivep);
        if (throughoutRejectp) rejectp = orExprs(flp, rejectp, throughoutRejectp);
        if (requiredStepRejectp) rejectp = orExprs(flp, rejectp, requiredStepRejectp);
        if (!rejectp) return new AstConst{flp, AstConst::BitTrue{}};
        AstNodeExpr* const resultExprp = new AstNot{flp, rejectp};
        return resultExprp;
    }

public:
    explicit SvaNfaLowering(AstNodeModule* modp)
        : m_modp{modp} {}

    // Lower NFA graph to synthesizable AstAlways blocks with state registers.
    // Links are combinational; Edges are registered (NBA).
    // Returns !reject for assert/assume, or match for cover.
    AstNodeExpr* lower(FileLine* flp, SvaGraph& graph, AstNodeExpr* triggerExprp,
                       AstSenTree* senTreep, AstNodeExpr* matchCondp, bool isCover,
                       AstNodeExpr* disableExprp = nullptr, bool negated = false,
                       AstNodeExpr** outMatchpp = nullptr, AstVar* disableCntVarp = nullptr,
                       AstVar* snapshotVarp = nullptr,
                       std::vector<AstNodeExpr*>* outRequiredStepSrcsp = nullptr) {
        const std::string baseName = m_names.get("");

        // Number vertices with sequential colors for array indexing.
        int N = 0;
        for (V3GraphVertex& vtxr : graph.m_graph.vertices()) { vtxr.color(N++); }
        std::vector<SvaStateVertex*> vtx(N, nullptr);
        for (V3GraphVertex& vtxr : graph.m_graph.vertices()) {
            vtx[vtxr.color()] = static_cast<SvaStateVertex*>(&vtxr);
        }
        const int startIdx = graph.m_startVertexp->color();
        const int matchIdx = graph.m_matchVertexp ? graph.m_matchVertexp->color() : -1;
        const std::vector<const SvaTransEdge*> edges = graph.allEdges();

        // Allocate per-vertex lowering data (stored via V3GraphVertex::userp()).
        std::vector<std::unique_ptr<SvaVertexData>> vertexData(N);
        for (int i = 0; i < N; ++i) {
            vertexData[i] = std::make_unique<SvaVertexData>();
            vtx[i]->userp(vertexData[i].get());
        }

        // Identify registered vertices (targets of clocked edges).
        for (int i = 0; i < N; ++i) {
            for (const V3GraphEdge& er : vtx[i]->outEdges()) {
                const SvaTransEdge& te = static_cast<const SvaTransEdge&>(er);
                const int toIdx = te.toVtxp()->color();
                if (te.m_consumesCycle && toIdx != matchIdx && !te.toVtxp()->m_isRejectSink) {
                    vtx[toIdx]->datap()->needsReg = true;
                }
            }
        }

        AstNodeDType* const u32DTypep = m_modp->findBasicDType(VBasicDTypeKwd::UINT32);
        for (int i = 0; i < N; ++i) {
            if (vtx[i]->m_isAndCombiner) {
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
            if (vtx[i]->m_isCounter) {
                const std::string base = baseName + "__c" + std::to_string(i);
                AstVar* const activep = new AstVar{flp, VVarType::MODULETEMP, base + "_active",
                                                   m_modp->findBitDType()};
                activep->lifetime(VLifetime::STATIC_EXPLICIT);
                m_modp->addStmtsp(activep);
                vtx[i]->datap()->counterActiveVarp = activep;
                AstVar* const cntp
                    = new AstVar{flp, VVarType::MODULETEMP, base + "_cnt", u32DTypep};
                cntp->lifetime(VLifetime::STATIC_EXPLICIT);
                m_modp->addStmtsp(cntp);
                vtx[i]->datap()->counterCountVarp = cntp;
                continue;
            }
            if (!vtx[i]->datap()->needsReg) continue;
            if (i == startIdx || vtx[i]->m_isMatch) continue;
            const std::string varName = baseName + "__s" + std::to_string(i);
            AstVar* const varp
                = new AstVar{flp, VVarType::MODULETEMP, varName, m_modp->findBitDType()};
            varp->lifetime(VLifetime::STATIC_EXPLICIT);
            m_modp->addStmtsp(varp);
            vtx[i]->datap()->stateVarp = varp;
        }

        // Build lowering context for phase sub-functions.
        LowerCtx c{flp,          N,        vtx,          edges,      startIdx,
                   matchIdx,     senTreep, disableExprp, matchCondp, disableCntVarp,
                   snapshotVarp, graph};

        // Phase 1: Resolve combinational Links via fixed-point propagation.
        resolveLinks(c, triggerExprp);

        // Phase 2/2b/2c: Emit NBA state-update, counter FSM, and SAnd done-latch logic.
        emitStateRegisterNba(c);
        emitCounterFsmNba(c);
        emitAndCombinerDoneLatchNba(c);

        // Phase 3/3a/3b: Compute terminal match/reject signals (cleans up stateSig).
        const SignalSet sigs = computeSignals(c, outRequiredStepSrcsp);

        AstNodeExpr* const resultp = assembleResult(
            flp, isCover, negated, matchCondp, sigs.terminalActivep, sigs.rejectBasep,
            sigs.throughoutRejectp, sigs.requiredStepRejectp, outMatchpp);

        // Clear userp on every vertex before vertexData unique_ptrs are destroyed.
        for (int i = 0; i < N; ++i) vtx[i]->userp(nullptr);
        return resultp;
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
    V3UniqueNames m_propVarNames{"__Vpropvar"};  // Property-local variable names
    V3UniqueNames m_disableCntNames{"__VnfaDis"};  // Disable-iff counter names
    V3UniqueNames m_propTempNames{"__VnfaSampled"};  // Hoisted $sampled(propp) temps
    std::set<const AstProperty*> m_inliningProps;  // Recursion guard for inlineNamedProperty

    // Wire match vertex and mid-window sources for a successful NFA build.
    static void wireMatchAndMidSources(SvaGraph& graph, const BuildResult& result, FileLine* flp) {
        graph.createMatchVertex();
        graph.addLink(result.termVertexp, graph.m_matchVertexp);
        for (SvaStateVertex* srcVtxp : result.midSources) {
            AstNodeExpr* condp = nullptr;
            for (AstNodeExpr* const tc : srcVtxp->m_throughoutConds) {
                AstNodeExpr* const tcClone = tc->cloneTreePure(false);
                condp = condp ? new AstAnd{flp, condp, tcClone} : tcClone;
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
            std::set<const AstProperty*>& setr;
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

    // Allocate disable-iff counter + snapshot vars and unlink the original
    // disable expression from the PropSpec. Returns {cntp, snapp} or
    // {nullptr, nullptr} if no counter is needed.
    struct DisableVars final {
        AstVar* cntp = nullptr;
        AstVar* snapp = nullptr;
    };
    DisableVars createDisableCounterMechanism(FileLine* flp, AstNodeExpr* disableExprp,
                                              bool hasImplication, AstPropSpec* propSpecp) {
        if (!disableExprp || hasImplication || VN_IS(disableExprp, Const)) return {};
        if (disableExprp->exists([](const AstSampled*) { return true; })) return {};

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

        if (propSpecp && propSpecp->disablep()) propSpecp->disablep()->unlinkFrBack();
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

    // Install the pass-action handler and per-thread fail-handlers generated by
    // lower() on a negated assert.
    void attachMatchHandlers(FileLine* flp, AstAssert* assertAssertp, AstAssert* assertWithFailp,
                             AstNodeExpr* matchExprp, AstSenTree* perSrcSenTreep,
                             const std::vector<AstNodeExpr*>& requiredStepSrcs) {
        // Gate pass handler on match to prevent vacuous-pass firings.
        if (matchExprp) {
            // needMatch implies passsp() was non-null when evaluated above;
            // lowering does not mutate the assert's pass-action between the
            // two reads, so passsp() is still non-null here.
            AstNode* passsp = assertAssertp->passsp();
            UASSERT_OBJ(passsp, assertAssertp, "needMatch set but passsp is null");
            passsp->unlinkFrBackWithNext();
            assertAssertp->addPasssp(new AstIf{flp, matchExprp->cloneTreePure(false),
                                               passsp->cloneTree(false), nullptr});
            // Fail-handler prefix for overlapping instances (IEEE 16.12):
            // fires when reject=1 && match=1 in the same cycle.
            if (AstNode* const failsp = assertAssertp->failsp()) {
                failsp->addHereThisAsNext(
                    new AstIf{flp, matchExprp, passsp->cloneTree(false), nullptr});
            } else {
                VL_DO_DANGLING(pushDeletep(matchExprp), matchExprp);
            }
            VL_DO_DANGLING(pushDeletep(passsp), passsp);
        }

        // Extra fail-handler fires for simultaneous required-step failures
        // (IEEE 1800-2023: fail handler fires once per failing thread).
        // perSrcSenTreep is set only when requiredStepSrcs.size() >= 2, and
        // requiredStepSrcs is populated only when assertWithFailp->failsp() is non-null.
        if (perSrcSenTreep) {
            AstNode* const failsp = assertWithFailp->failsp();
            AstNodeExpr* cumulativeOrp = requiredStepSrcs[0]->cloneTreePure(false);
            for (size_t i = 1; i < requiredStepSrcs.size(); ++i) {
                AstNodeExpr* const srcp = requiredStepSrcs[i];
                AstNodeExpr* const condp = new AstAnd{flp, srcp->cloneTreePure(false),
                                                      cumulativeOrp->cloneTreePure(false)};
                m_modp->addStmtsp(
                    new AstAlways{flp, VAlwaysKwd::ALWAYS, perSrcSenTreep->cloneTree(false),
                                  new AstIf{flp, condp, failsp->cloneTree(true), nullptr}});
                cumulativeOrp = new AstOr{flp, cumulativeOrp, srcp->cloneTreePure(false)};
            }
            VL_DO_DANGLING(pushDeletep(cumulativeOrp), cumulativeOrp);
            VL_DO_DANGLING(pushDeletep(perSrcSenTreep), perSrcSenTreep);
        }
        for (AstNodeExpr* const srcp : requiredStepSrcs) pushDeletep(srcp);
    }

    void processAssertion(AstNodeCoverOrAssert* assertp) {
        if (assertp->immediate()) return;

        if (AstPropSpec* const specp = VN_CAST(assertp->propp(), PropSpec)) {
            if (AstFuncRef* const funcrefp = VN_CAST(specp->propp(), FuncRef)) {
                if (const AstProperty* const propyp = VN_CAST(funcrefp->taskp(), Property)) {
                    inlineNamedProperty(specp, funcrefp, propyp);
                }
            }
        }

        inlineAllSequenceRefs(assertp->propp());

        AstNode* const propp = assertp->propp();
        if (!hasMultiCycleExpr(propp)) return;

        const PropertyParts parts = decomposeProperty(propp);
        UASSERT_OBJ(parts.seqExprp, propp, "Property body must be an expression");

        // Unwrap `not` (IEEE 1800-2023 16.12.1); odd count -> negated semantics.
        AstNodeExpr* seqBodyp = parts.seqExprp;
        bool negated = false;
        while (AstLogNot* const notp = VN_CAST(seqBodyp, LogNot)) {
            negated = !negated;
            seqBodyp = notp->lhsp();
        }

        AstSenTree* senTreep = assertp->sentreep();
        bool senTreeOwned = false;  // True if we created senTreep locally
        AstPropSpec* const propSpecp = VN_CAST(assertp->propp(), PropSpec);
        UASSERT_OBJ(propSpecp, assertp, "Concurrent assertion must have PropSpec");
        // Inherit module defaults (IEEE 14.12, 16.15) when assertion has none.
        if (!propSpecp->sensesp() && m_defaultClockingp) {
            propSpecp->sensesp(m_defaultClockingp->sensesp()->cloneTree(true));
        }
        if (!propSpecp->disablep() && m_defaultDisablep) {
            propSpecp->disablep(m_defaultDisablep->condp()->cloneTreePure(true));
        }
        if (!senTreep && propSpecp->sensesp()) {
            senTreep
                = new AstSenTree{propSpecp->fileline(), propSpecp->sensesp()->cloneTree(true)};
            senTreeOwned = true;
        }
        AstNodeExpr* disableExprp = propSpecp->disablep();
        if (!senTreep) return;

        FileLine* const flp = assertp->fileline();
        const bool isCover = VN_IS(assertp, Cover);

        SvaGraph graph;
        SvaNfaBuilder builder{graph, m_modp, m_propTempNames};

        const BuildResult result = buildAssertionGraph(builder, graph, seqBodyp, parts, flp);
        if (result.valid()) wireMatchAndMidSources(graph, result, flp);
        if (!result.valid()) {
            // Fall through to V3AssertPre for unsupported constructs; only
            // replace the body on real semantic errors. Any hoisted temps
            // from this attempt become orphan MODULETEMPs; V3Dead removes
            // them along with the dead always_comb driver.
            replaceBodyOnBuildError(flp, propSpecp, result.errorEmitted);
            if (senTreeOwned) VL_DO_DANGLING(pushDeletep(senTreep), senTreep);
            return;
        }

        // Build succeeded. Now create snapshot mechanism for disable iff if needed.
        // Done here (not before build) so failed builds don't pollute the AST.
        const DisableVars disableVars
            = createDisableCounterMechanism(flp, disableExprp, parts.hasImplication, propSpecp);
        AstVar* const disableCntVarp = disableVars.cntp;
        AstVar* const snapshotVarp = disableVars.snapp;
        const bool disableExprUnlinked = disableCntVarp && disableExprp;

        AstAssert* const assertAssertp = VN_CAST(assertp, Assert);
        const bool needMatch
            = !isCover && !parts.hasImplication && assertAssertp && assertAssertp->passsp();
        AstNodeExpr* matchExprp = nullptr;

        AstAssert* const assertWithFailp = VN_CAST(assertp, Assert);
        const bool needPerSrcFail
            = !isCover && !parts.hasImplication && assertWithFailp && assertWithFailp->failsp();
        std::vector<AstNodeExpr*> requiredStepSrcs;

        AstNodeExpr* const alwaysTriggerp = new AstConst{flp, AstConst::BitTrue{}};
        AstNodeExpr* const outputExprp
            = m_loweringp->lower(flp, graph, alwaysTriggerp, senTreep, result.finalCondp, isCover,
                                 disableExprp ? disableExprp->cloneTreePure(false) : nullptr,
                                 negated, needMatch ? &matchExprp : nullptr, disableCntVarp,
                                 snapshotVarp, needPerSrcFail ? &requiredStepSrcs : nullptr);

        AstSenTree* const perSrcSenTreep
            = (requiredStepSrcs.size() >= 2) ? senTreep->cloneTree(false) : nullptr;

        VL_DO_DANGLING(pushDeletep(alwaysTriggerp), alwaysTriggerp);
        if (senTreeOwned) VL_DO_DANGLING(pushDeletep(senTreep), senTreep);
        if (disableExprUnlinked) VL_DO_DANGLING(pushDeletep(disableExprp), disableExprp);
        if (result.finalCondp && !result.finalCondp->backp()) pushDeletep(result.finalCondp);

        attachMatchHandlers(flp, assertAssertp, assertWithFailp, needMatch ? matchExprp : nullptr,
                            perSrcSenTreep, requiredStepSrcs);

        AstNode* const innerPropp = propSpecp->propp();
        innerPropp->replaceWith(outputExprp);
        VL_DO_DANGLING(pushDeletep(innerPropp), innerPropp);

        UINFO(4, "NFA converted assertion at " << flp << endl);
    }

    // VISITORS
    void visit(AstNodeModule* nodep) override {
        VL_RESTORER(m_modp);
        VL_RESTORER(m_loweringp);
        VL_RESTORER(m_defaultClockingp);
        VL_RESTORER(m_defaultDisablep);
        m_modp = nodep;
        m_defaultClockingp = nullptr;
        m_defaultDisablep = nullptr;
        SvaNfaLowering lowering{nodep};
        m_loweringp = &lowering;
        iterateChildren(nodep);
    }
    void visit(AstClocking* nodep) override {
        if (nodep->isDefault() && !m_defaultClockingp) m_defaultClockingp = nodep;
        iterateChildren(nodep);
    }
    void visit(AstDefaultDisable* nodep) override {
        if (!m_defaultDisablep) m_defaultDisablep = nodep;
    }
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
