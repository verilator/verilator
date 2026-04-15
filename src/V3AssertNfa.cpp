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
//  - Replace converted assertions with combinational accept/reject checks
//    so V3AssertPre sees no multi-cycle SExpr (unsupported ones fall through).
//
//*************************************************************************

#include "V3PchAstNoMT.h"  // VL_MT_DISABLED_CODE_UNIT

#include "V3AssertNfa.h"

#include "V3Const.h"
#include "V3Task.h"
#include "V3UniqueNames.h"

#include <set>
#include <vector>

VL_DEFINE_DEBUG_FUNCTIONS;

//######################################################################
// NFA Graph Data Structures

namespace {

struct SvaNfaNode final {
    int id;
    bool isAccept = false;
    // Owned throughout-guard clones; if any drop while node is active, reject fires
    // per IEEE 1800-2023 16.9.9.
    std::vector<AstNodeExpr*> throughoutConds;
    // Counter FSM node for ##[M:N] when N-M > kChainLimit
    bool isCounter = false;
    int counterMin = 0;
    int counterMax = 0;
    // Liveness terminal (IEEE weak semantics): reject must not fire from this source.
    bool isUnbounded = false;
    // Temporal sequence AND combiner per IEEE 1800-2023 16.9.5
    bool isAndCombiner = false;
    int andLhsTermId = -1;
    int andRhsTermId = -1;
    AstNodeExpr* andLhsCondp = nullptr;  // OWNED; may be null
    AstNodeExpr* andRhsCondp = nullptr;  // OWNED; may be null
    // Reject sink for SAnd rejectOnFail wiring; not a stateSig source
    bool isRejectSink = false;
};

struct SvaNfaEdge final {
    int fromId;
    int toId;
    AstNodeExpr* condp = nullptr;  // nullptr = unconditional; OWNED by NFA
    bool consumesCycle;  // true = Edge (##1), false = Link (##0/boolean)
    // Reject when source is active and condp is false. Set only on the
    // outermost required-step Link; nested / optional Links must not set this.
    bool rejectOnFail = false;
};

struct SvaNfa final {
    int startNode = -1;
    int acceptNode = -1;
    std::vector<SvaNfaNode> nodes;
    std::vector<SvaNfaEdge> edges;

    ~SvaNfa() {
        for (auto& edge : edges) {
            if (edge.condp) {
                edge.condp->deleteTree();
                edge.condp = nullptr;
            }
        }
        for (auto& node : nodes) {
            for (auto* cp : node.throughoutConds) cp->deleteTree();
            node.throughoutConds.clear();
            if (node.andLhsCondp) {
                node.andLhsCondp->deleteTree();
                node.andLhsCondp = nullptr;
            }
            if (node.andRhsCondp) {
                node.andRhsCondp->deleteTree();
                node.andRhsCondp = nullptr;
            }
        }
    }

    int createNode() {
        const int id = static_cast<int>(nodes.size());
        SvaNfaNode node;
        node.id = id;
        nodes.push_back(std::move(node));
        return id;
    }
    int createAcceptNode() {
        const int id = createNode();
        nodes[id].isAccept = true;
        acceptNode = id;
        return id;
    }
    void addClockEdge(int from, int to, AstNodeExpr* condp = nullptr) {
        edges.push_back(SvaNfaEdge{from, to, condp, true});
    }
    void addLink(int from, int to, AstNodeExpr* condp = nullptr) {
        edges.push_back(SvaNfaEdge{from, to, condp, false});
    }
};

//######################################################################
// Builder result: terminal node + optional final condition (accept Link condition).
struct BuildResult final {
    int termNode;  // Primary terminal; contributes to both accept and reject (Phase 3).
    AstNodeExpr* finalCondp;  // nullptr = unconditional
    // Mid-window sources for range delays (pure boolean RHS): accept-only (isUnbounded).
    std::vector<int> midSources;
    bool errorEmitted = false;  // Builder already emitted specific error; skip generic.
    bool valid() const { return termNode >= 0; }
    static BuildResult fail(bool errored = false) { return {-1, nullptr, {}, errored}; }
    static BuildResult failWithError() { return {-1, nullptr, {}, true}; }
};

//######################################################################
// NFA Builder

class SvaNfaBuilder final {
    SvaNfa& m_nfa;
    std::vector<AstNodeExpr*> m_throughoutStack;
    // Sticky once an unbounded wait is built; nodes created after inherit liveness.
    bool m_inUnboundedScope = false;

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
                guardp->dtypeSetBit();
            }
        }
        if (baseCondp) {
            guardp = new AstAnd{flp, baseCondp, guardp};
            guardp->dtypeSetBit();
        }
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
        if (!nodep) return 0;
        if (AstSExpr* const sexprp = VN_CAST(nodep, SExpr)) {
            AstDelay* const delayp = VN_CAST(sexprp->delayp(), Delay);
            if (!delayp || !delayp->isCycleDelay()) return -1;
            int delayCycles = -1;
            if (delayp->isRangeDelay()) {
                if (delayp->isUnbounded()) return -1;
                const int minD = getConstInt(delayp->lhsp());
                const int maxD = getConstInt(delayp->rhsp());
                if (minD < 0 || maxD < 0 || minD != maxD) return -1;
                delayCycles = minD;
            } else {
                delayCycles = getConstInt(delayp->lhsp());
                if (delayCycles < 0) return -1;
            }
            int preLen = 0;
            if (AstNodeExpr* const prep = sexprp->preExprp()) {
                preLen = fixedLength(prep);
                if (preLen < 0) return -1;
            }
            const int bodyLen = fixedLength(sexprp->exprp());
            if (bodyLen < 0) return -1;
            return preLen + delayCycles + bodyLen;
        }
        if (AstSThroughout* const throughp = VN_CAST(nodep, SThroughout)) {
            return fixedLength(throughp->rhsp());
        }
        if (VN_IS(nodep, SConsRep) || VN_IS(nodep, SGotoRep) || VN_IS(nodep, SAnd)
            || VN_IS(nodep, SOr) || VN_IS(nodep, SIntersect)) {
            // Conservatively variable -- can be tightened in a follow-up.
            return -1;
        }
        // Plain boolean expression (no SVA constructs) -- 0 cycles.
        return 0;
    }

    static AstNodeExpr* sampled(AstNodeExpr* exprp) {
        AstSampled* const sp = new AstSampled{exprp->fileline(), exprp};
        sp->dtypeFrom(exprp);
        return sp;
    }

    // Create node and inherit throughout guards from current scope (IEEE 16.9.9).
    int scopedCreateNode() {
        const int id = m_nfa.createNode();
        auto& node = m_nfa.nodes[id];
        for (AstNodeExpr* const cp : m_throughoutStack) {
            node.throughoutConds.push_back(cp->cloneTreePure(false));
        }
        if (m_inUnboundedScope) node.isUnbounded = true;
        return id;
    }

    // AND current throughout stack into every edge/link (IEEE 16.9.9 invariant).
    void guardedLink(int from, int to, AstNodeExpr* condp, FileLine* flp) {
        m_nfa.addLink(from, to, throughoutCond(condp, flp));
    }
    void guardedLink(int from, int to, FileLine* flp) {
        m_nfa.addLink(from, to, throughoutCond(nullptr, flp));
    }
    void guardedEdge(int from, int to, AstNodeExpr* condp, FileLine* flp) {
        m_nfa.addClockEdge(from, to, throughoutCond(condp, flp));
    }
    void guardedEdge(int from, int to, FileLine* flp) {
        m_nfa.addClockEdge(from, to, throughoutCond(nullptr, flp));
    }

    int addDelayChain(int startNode, int n, FileLine* flp) {
        int current = startNode;
        for (int i = 0; i < n; ++i) {
            const int next = scopedCreateNode();
            guardedEdge(current, next, flp);
            current = next;
        }
        return current;
    }

    // Build NFA for an SExpr. finalCond = RHS (not yet added as a node).
    // isTopLevelStep: marks outermost required boolean check as rejectOnFail.
    BuildResult buildSExpr(AstSExpr* sexprp, int entryNode, bool isTopLevelStep = false) {
        AstDelay* const delayp = VN_CAST(sexprp->delayp(), Delay);
        if (!delayp || !delayp->isCycleDelay()) return BuildResult::fail();

        FileLine* const flp = sexprp->fileline();

        // Handle LHS (preExpr)
        int currentNode = entryNode;
        if (AstNodeExpr* const preExprp = sexprp->preExprp()) {
            const BuildResult pre = buildExpr(preExprp, currentNode, isTopLevelStep);
            if (!pre.valid()) return BuildResult::fail(pre.errorEmitted);
            if (pre.finalCondp) {
                const int condNode = scopedCreateNode();
                guardedLink(pre.termNode, condNode, sampled(pre.finalCondp->cloneTreePure(false)),
                            flp);
                if (isTopLevelStep && !m_nfa.nodes[pre.termNode].isUnbounded
                    && !m_inUnboundedScope) {
                    // Do not mark liveness sources: first boolean check is deferred.
                    m_nfa.edges.back().rejectOnFail = true;
                }
                currentNode = condNode;
            } else {
                currentNode = pre.termNode;
            }
        }

        // Handle delay
        std::vector<int> rangeMidSources;
        if (delayp->isRangeDelay()) {
            const int minDelay = getConstInt(delayp->lhsp());
            if (minDelay < 0) {
                delayp->v3error("Range delay minimum is not a non-negative"
                                " elaboration-time constant"
                                " (IEEE 1800-2023 16.7)");
                return BuildResult::failWithError();
            }

            if (delayp->isUnbounded()) {
                // `##[M:$]`: wait M cycles, then self-loop waiting for the
                // match condition. Unbounded = liveness, so no reject.
                currentNode = addDelayChain(currentNode, minDelay, flp);
                guardedEdge(currentNode, currentNode, flp);
                m_nfa.nodes[currentNode].isUnbounded = true;
                m_inUnboundedScope = true;
            } else {
                const int maxDelay = getConstInt(delayp->rhsp());
                if (maxDelay < 0) {
                    delayp->v3error("Range delay maximum is not a non-negative"
                                    " elaboration-time constant"
                                    " (IEEE 1800-2023 16.7)");
                    return BuildResult::failWithError();
                }
                if (maxDelay < minDelay) {
                    delayp->v3error("Range delay maximum must be >= minimum"
                                    " (IEEE 1800-2023 16.7)");
                    return BuildResult::failWithError();
                }
                if (minDelay == maxDelay) {
                    currentNode = addDelayChain(currentNode, minDelay, flp);
                } else {
                    const int range = maxDelay - minDelay;
                    currentNode = addDelayChain(currentNode, minDelay, flp);
                    constexpr int kChainLimit = 256;
                    AstNodeExpr* const exprp = sexprp->exprp();
                    const bool nestedRhs = VN_IS(exprp, SExpr);
                    if (range > kChainLimit) {
                        // Large range: counter FSM. Overlapping triggers during an
                        // active count are dropped (non-overlapping semantics only).
                        const int counterNodeId = scopedCreateNode();
                        m_nfa.nodes[counterNodeId].isCounter = true;
                        m_nfa.nodes[counterNodeId].counterMin = 0;
                        m_nfa.nodes[counterNodeId].counterMax = range;
                        guardedEdge(currentNode, counterNodeId, flp);
                        currentNode = counterNodeId;
                    } else if (nestedRhs) {
                        // Merge all [M,N] positions; continuation is per-attempt.
                        const int mergeNode = scopedCreateNode();
                        guardedLink(currentNode, mergeNode, flp);
                        for (int i = 0; i < range; ++i) {
                            const int nextNode = scopedCreateNode();
                            guardedEdge(currentNode, nextNode, flp);
                            guardedLink(nextNode, mergeNode, flp);
                            currentNode = nextNode;
                        }
                        currentNode = mergeNode;
                    } else {
                        // Pure boolean RHS: register chain. Each mid-position links to accept
                        // (accept-only); last position is the reject source. Edge gating
                        // (!sampled(exprp)) prevents already-matched attempts from propagating
                        // further, avoiding spurious reject at later positions.
                        rangeMidSources.push_back(currentNode);
                        for (int i = 0; i < range; ++i) {
                            const int nextNode = scopedCreateNode();
                            AstNodeExpr* const notExprp
                                = new AstNot{flp, sampled(exprp->cloneTreePure(false))};
                            notExprp->dtypeSetBit();
                            guardedEdge(currentNode, nextNode, notExprp, flp);
                            if (i < range - 1) { rangeMidSources.push_back(nextNode); }
                            currentNode = nextNode;
                        }
                    }
                }
            }
        } else {
            const int delayCycles = getConstInt(delayp->lhsp());
            if (delayCycles < 0) {
                delayp->v3error("Delay value is not a non-negative"
                                " elaboration-time constant"
                                " (IEEE 1800-2023 16.7)");
                return BuildResult::failWithError();
            }
            currentNode = addDelayChain(currentNode, delayCycles, flp);
        }

        // Multi-cycle RHS: recurse (only plain boolean is returned as finalCondp).
        AstNodeExpr* const exprp = sexprp->exprp();
        if (VN_IS(exprp, SExpr) || VN_IS(exprp, SAnd) || VN_IS(exprp, SOr)
            || VN_IS(exprp, SConsRep) || VN_IS(exprp, SGotoRep) || VN_IS(exprp, SThroughout)
            || VN_IS(exprp, SIntersect) || VN_IS(exprp, SNonConsRep)) {
            return buildExpr(exprp, currentNode, isTopLevelStep);
        }
        return {currentNode, exprp, std::move(rangeMidSources)};
    }

    BuildResult buildConsRep(AstSConsRep* repp, int entryNode, bool isTopLevelStep = false) {
        FileLine* const flp = repp->fileline();
        AstNodeExpr* const exprp = repp->exprp();
        // Multi-cycle expr in ConsRep not yet supported; bail to avoid invalid AST.
        if (VN_IS(exprp, SExpr) || VN_IS(exprp, SThroughout) || VN_IS(exprp, SAnd)
            || VN_IS(exprp, SOr) || VN_IS(exprp, SConsRep) || VN_IS(exprp, SGotoRep)
            || VN_IS(exprp, SIntersect) || VN_IS(exprp, SNonConsRep)) {
            repp->v3warn(E_UNSUPPORTED, "Unsupported: multi-cycle sequence expression inside"
                                        " consecutive repetition (IEEE 1800-2023 16.9.2)");
            return BuildResult::failWithError();
        }
        const int minN = getConstInt(repp->countp());
        if (minN < 0) return BuildResult::fail();
        // Bail on large exact repetitions (no counter FSM for ConsRep yet).
        constexpr int kConsRepLimit = 256;
        if (minN > kConsRepLimit && !repp->unbounded() && !repp->maxCountp()) {
            return BuildResult::fail();
        }

        int currentNode = entryNode;
        for (int i = 0; i < minN; ++i) {
            if (i > 0) {
                const int nextNode = scopedCreateNode();
                guardedEdge(currentNode, nextNode, flp);
                currentNode = nextNode;
            }
            // Mark first and last boolean Links as rejectOnFail for correct
            // reject on standalone ConsRep.
            const int condNode = scopedCreateNode();
            guardedLink(currentNode, condNode, sampled(exprp->cloneTreePure(false)), flp);
            if (isTopLevelStep && (i == 0 || i == minN - 1)) {
                m_nfa.edges.back().rejectOnFail = true;
            }
            currentNode = condNode;
        }

        if (repp->unbounded()) {
            if (minN == 0) {
                const int waitNode = scopedCreateNode();
                guardedEdge(currentNode, waitNode, flp);
                const int checkNode = scopedCreateNode();
                guardedLink(waitNode, checkNode, sampled(exprp->cloneTreePure(false)), flp);
                guardedEdge(checkNode, waitNode, flp);
                guardedLink(currentNode, checkNode, flp);
                currentNode = checkNode;
            } else {
                const int loopBackNode = scopedCreateNode();
                guardedEdge(currentNode, loopBackNode, flp);
                const int reCheckNode = scopedCreateNode();
                guardedLink(loopBackNode, reCheckNode, sampled(exprp->cloneTreePure(false)), flp);
                guardedEdge(reCheckNode, loopBackNode, flp);
                guardedLink(reCheckNode, currentNode, flp);
            }
            m_nfa.nodes[currentNode].isUnbounded = true;
            m_inUnboundedScope = true;
        } else if (repp->maxCountp()) {
            const int maxN = getConstInt(repp->maxCountp());
            if (maxN < minN) return BuildResult::fail();
            const int mergeNode = scopedCreateNode();
            guardedLink(currentNode, mergeNode, flp);
            for (int i = minN; i < maxN; ++i) {
                const int nextNode = scopedCreateNode();
                guardedEdge(currentNode, nextNode, flp);
                const int checkNode = scopedCreateNode();
                guardedLink(nextNode, checkNode, sampled(exprp->cloneTreePure(false)), flp);
                guardedLink(checkNode, mergeNode, flp);
                currentNode = checkNode;
            }
            currentNode = mergeNode;
        }
        // finalCond = nullptr (already checked via Links)
        return {currentNode, nullptr, {}};
    }

    BuildResult buildGotoRep(AstSGotoRep* repp, int entryNode) {
        FileLine* const flp = repp->fileline();
        AstNodeExpr* const exprp = repp->exprp();
        const int n = getConstInt(repp->countp());
        if (n <= 0) return BuildResult::fail();

        int currentNode = entryNode;
        for (int i = 0; i < n; ++i) {
            const int waitNode = scopedCreateNode();
            // Edge (not Link) for all iterations: IEEE expansion ##1 before each
            // match. A Link at i==0 was wrong -- it allowed same-cycle matching
            // and was discarded by Phase 2 (waitNode has a self-loop Edge).
            guardedEdge(currentNode, waitNode, flp);
            AstNodeExpr* const notExprp = new AstNot{flp, exprp->cloneTreePure(false)};
            notExprp->dtypeSetBit();
            guardedEdge(waitNode, waitNode, sampled(notExprp), flp);
            const int matchNode = scopedCreateNode();
            guardedLink(waitNode, matchNode, sampled(exprp->cloneTreePure(false)), flp);
            currentNode = matchNode;
        }
        m_nfa.nodes[currentNode].isUnbounded = true;  // [->N] waits unboundedly
        m_inUnboundedScope = true;
        return {currentNode, nullptr, {}};
    }

    // Build merge node for SOr / LogOr: both branches feed into one node.
    BuildResult buildOrMerge(AstNodeExpr* lhsp, AstNodeExpr* rhsp, int entryNode, FileLine* flp) {
        const BuildResult lhs = buildExpr(lhsp, entryNode);
        const BuildResult rhs = buildExpr(rhsp, entryNode);
        if (!lhs.valid() || !rhs.valid()) {
            return BuildResult::fail(lhs.errorEmitted || rhs.errorEmitted);
        }
        const int mergeNode = scopedCreateNode();
        if (lhs.finalCondp) {
            guardedLink(lhs.termNode, mergeNode, sampled(lhs.finalCondp->cloneTreePure(false)),
                        flp);
        } else {
            guardedLink(lhs.termNode, mergeNode, flp);
        }
        if (rhs.finalCondp) {
            guardedLink(rhs.termNode, mergeNode, sampled(rhs.finalCondp->cloneTreePure(false)),
                        flp);
        } else {
            guardedLink(rhs.termNode, mergeNode, flp);
        }
        return {mergeNode, nullptr, {}};
    }

    // Build done-latch combiner for SAnd/SIntersect (IEEE 1800-2023 16.9.5).
    BuildResult buildAndCombiner(AstNodeExpr* lhsExprp, AstNodeExpr* rhsExprp, int entryNode,
                                 FileLine* flp) {
        // Snapshot-restore scope so LHS liveness does not leak into RHS.
        const bool savedScope = m_inUnboundedScope;
        const BuildResult lhs = buildExpr(lhsExprp, entryNode);
        const bool lhsScope = m_inUnboundedScope;
        m_inUnboundedScope = savedScope;
        const BuildResult rhs = buildExpr(rhsExprp, entryNode);
        const bool rhsScope = m_inUnboundedScope;
        m_inUnboundedScope = savedScope || lhsScope || rhsScope;
        if (!lhs.valid() || !rhs.valid()) {
            return BuildResult::fail(lhs.errorEmitted || rhs.errorEmitted);
        }

        // Single-cycle operands: use boolean AND (done-latch would fire across cycles).
        if (lhs.termNode == entryNode && rhs.termNode == entryNode) {
            AstNodeExpr* condp = nullptr;
            if (lhs.finalCondp && rhs.finalCondp) {
                condp = new AstAnd{flp, lhs.finalCondp->cloneTreePure(false),
                                   rhs.finalCondp->cloneTreePure(false)};
                condp->dtypeSetBit();
            } else if (lhs.finalCondp) {
                condp = lhs.finalCondp;
            } else {
                condp = rhs.finalCondp;
            }
            return {entryNode, condp, {}};
        }
        // Range-delay mid-window sources in either sub-branch would need
        // to be folded into the latch's "accept-now" signal, which the
        // current combiner does not support. Defer (UNSUPPORTED).
        if (!lhs.midSources.empty() || !rhs.midSources.empty()) { return BuildResult::fail(); }
        const int combNode = scopedCreateNode();
        SvaNfaNode& cn = m_nfa.nodes[combNode];
        cn.isAndCombiner = true;
        cn.andLhsTermId = lhs.termNode;
        cn.andRhsTermId = rhs.termNode;
        if (lhs.finalCondp) { cn.andLhsCondp = lhs.finalCondp->cloneTreePure(false); }
        if (rhs.finalCondp) { cn.andRhsCondp = rhs.finalCondp->cloneTreePure(false); }
        if (m_nfa.nodes[lhs.termNode].isUnbounded || m_nfa.nodes[rhs.termNode].isUnbounded) {
            cn.isUnbounded = true;
        }
        // Wire terminal-boolean rejects to a dedicated sink so each side can fail
        // the AND independently. Skip for liveness or single-cycle operands
        // (single-cycle termNode == entryNode would fire every cycle).
        if (!cn.isUnbounded) {
            bool needSink = false;
            const bool lhsMultiCycle = (lhs.termNode != entryNode);
            const bool rhsMultiCycle = (rhs.termNode != entryNode);
            if (lhs.finalCondp && lhsMultiCycle && !m_nfa.nodes[lhs.termNode].isUnbounded) {
                needSink = true;
            }
            if (rhs.finalCondp && rhsMultiCycle && !m_nfa.nodes[rhs.termNode].isUnbounded) {
                needSink = true;
            }
            if (needSink) {
                const int sinkNode = m_nfa.createNode();
                m_nfa.nodes[sinkNode].isRejectSink = true;
                if (lhs.finalCondp && lhsMultiCycle && !m_nfa.nodes[lhs.termNode].isUnbounded) {
                    m_nfa.addLink(lhs.termNode, sinkNode,
                                  sampled(lhs.finalCondp->cloneTreePure(false)));
                    m_nfa.edges.back().rejectOnFail = true;
                }
                if (rhs.finalCondp && rhsMultiCycle && !m_nfa.nodes[rhs.termNode].isUnbounded) {
                    m_nfa.addLink(rhs.termNode, sinkNode,
                                  sampled(rhs.finalCondp->cloneTreePure(false)));
                    m_nfa.edges.back().rejectOnFail = true;
                }
            }
        }
        return {combNode, nullptr, {}};
    }

    BuildResult buildThroughout(AstSThroughout* nodep, int entryNode,
                                bool isTopLevelStep = false) {
        // Mark entryNode so "cond false at tick 0" is detected as throughout-drop.
        m_nfa.nodes[entryNode].throughoutConds.push_back(nodep->lhsp()->cloneTreePure(false));
        m_throughoutStack.push_back(nodep->lhsp());
        const BuildResult result = buildExpr(nodep->rhsp(), entryNode, isTopLevelStep);
        m_throughoutStack.pop_back();
        return result;
    }

public:
    explicit SvaNfaBuilder(SvaNfa& nfa)
        : m_nfa{nfa} {}

    // Reset scope between antecedent and consequent: liveness must not leak.
    void resetScope() {
        m_inUnboundedScope = false;
        m_throughoutStack.clear();
    }

    BuildResult buildExpr(AstNodeExpr* nodep, int entryNode, bool isTopLevelStep = false) {
        if (AstSExpr* const sexprp = VN_CAST(nodep, SExpr)) {
            return buildSExpr(sexprp, entryNode, isTopLevelStep);
        }
        if (AstSConsRep* const repp = VN_CAST(nodep, SConsRep)) {
            return buildConsRep(repp, entryNode, isTopLevelStep);
        }
        if (AstSGotoRep* const repp = VN_CAST(nodep, SGotoRep)) {
            return buildGotoRep(repp, entryNode);
        }
        if (AstSThroughout* const throughoutp = VN_CAST(nodep, SThroughout)) {
            return buildThroughout(throughoutp, entryNode, isTopLevelStep);
        }
        if (AstSOr* const orp = VN_CAST(nodep, SOr)) {
            return buildOrMerge(orp->lhsp(), orp->rhsp(), entryNode, orp->fileline());
        }
        if (AstLogOr* const orp = VN_CAST(nodep, LogOr)) {
            return buildOrMerge(orp->lhsp(), orp->rhsp(), entryNode, orp->fileline());
        }
        if (AstSAnd* const andp = VN_CAST(nodep, SAnd)) {
            return buildAndCombiner(andp->lhsp(), andp->rhsp(), entryNode, andp->fileline());
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
            return buildAndCombiner(intp->lhsp(), intp->rhsp(), entryNode, intp->fileline());
        }
        if (VN_IS(nodep, SNonConsRep)) { return BuildResult::fail(); }
        // Boolean leaf (including LogAnd): return as finalCond
        return {entryNode, nodep, {}};
    }

    BuildResult build(AstNodeExpr* exprp) {
        m_nfa.startNode = scopedCreateNode();
        return buildExpr(exprp, m_nfa.startNode, /*isTopLevelStep=*/true);
    }
};

//######################################################################
// NFA Emitter

class SvaNfaEmitter final {
    AstNodeModule* const m_modp;
    V3UniqueNames m_names{"__Vnfa"};

    static AstNodeExpr* andCond(FileLine* flp, AstNodeExpr* exprp, AstNodeExpr* condp) {
        if (!condp) return exprp;
        AstNodeExpr* const resultp = new AstAnd{flp, exprp, condp->cloneTreePure(false)};
        resultp->dtypeSetBit();
        return resultp;
    }
    static AstNodeExpr* orExprs(FileLine* flp, AstNodeExpr* ap, AstNodeExpr* bp) {
        if (!ap) return bp;
        if (!bp) return ap;
        AstNodeExpr* const resultp = new AstOr{flp, ap, bp};
        resultp->dtypeSetBit();
        return resultp;
    }

public:
    explicit SvaNfaEmitter(AstNodeModule* modp)
        : m_modp{modp} {}

    // Emit NFA hardware. Links are combinational; Edges are registered.
    // Returns !reject for assert/assume, or accept for cover.
    AstNodeExpr* emit(FileLine* flp, const SvaNfa& nfa, AstNodeExpr* triggerExprp,
                      AstSenTree* senTreep, AstNodeExpr* acceptCondp, bool isCover,
                      AstNodeExpr* disableExprp = nullptr, bool negated = false,
                      AstNodeExpr** outAcceptpp = nullptr, AstVar* disableCntVarp = nullptr,
                      AstVar* snapshotVarp = nullptr,
                      std::vector<AstNodeExpr*>* outRequiredStepSrcsp = nullptr) {
        const std::string baseName = m_names.get("");
        const int N = static_cast<int>(nfa.nodes.size());

        // Identify registered nodes (targets of Edges)
        std::vector<bool> needsReg(N, false);
        for (const auto& edge : nfa.edges) {
            if (edge.consumesCycle && edge.toId != nfa.acceptNode
                && !nfa.nodes[edge.toId].isRejectSink) {
                needsReg[edge.toId] = true;
            }
        }

        std::vector<AstVar*> stateVars(N, nullptr);
        std::vector<AstVar*> counterActiveVars(N, nullptr);
        std::vector<AstVar*> counterCountVars(N, nullptr);
        std::vector<AstVar*> doneLVars(N, nullptr);
        std::vector<AstVar*> doneRVars(N, nullptr);
        AstNodeDType* const u32DTypep = m_modp->findBasicDType(VBasicDTypeKwd::UINT32);
        for (int i = 0; i < N; ++i) {
            if (nfa.nodes[i].isAndCombiner) {
                const std::string base = baseName + "__a" + std::to_string(i);
                AstVar* const lp = new AstVar{flp, VVarType::MODULETEMP, base + "_doneL",
                                              m_modp->findBitDType()};
                lp->lifetime(VLifetime::STATIC_EXPLICIT);
                m_modp->addStmtsp(lp);
                doneLVars[i] = lp;
                AstVar* const rp = new AstVar{flp, VVarType::MODULETEMP, base + "_doneR",
                                              m_modp->findBitDType()};
                rp->lifetime(VLifetime::STATIC_EXPLICIT);
                m_modp->addStmtsp(rp);
                doneRVars[i] = rp;
                continue;
            }
            if (nfa.nodes[i].isCounter) {
                const std::string base = baseName + "__c" + std::to_string(i);
                AstVar* const activep = new AstVar{flp, VVarType::MODULETEMP, base + "_active",
                                                   m_modp->findBitDType()};
                activep->lifetime(VLifetime::STATIC_EXPLICIT);
                m_modp->addStmtsp(activep);
                counterActiveVars[i] = activep;
                AstVar* const cntp
                    = new AstVar{flp, VVarType::MODULETEMP, base + "_cnt", u32DTypep};
                cntp->lifetime(VLifetime::STATIC_EXPLICIT);
                m_modp->addStmtsp(cntp);
                counterCountVars[i] = cntp;
                continue;
            }
            if (!needsReg[i]) continue;
            if (i == nfa.startNode || nfa.nodes[i].isAccept) continue;
            const std::string varName = baseName + "__s" + std::to_string(i);
            AstVar* const varp
                = new AstVar{flp, VVarType::MODULETEMP, varName, m_modp->findBitDType()};
            varp->lifetime(VLifetime::STATIC_EXPLICIT);
            m_modp->addStmtsp(varp);
            stateVars[i] = varp;
        }

        // Phase 1: Resolve Links (combinational state_sig)
        std::vector<AstNodeExpr*> stateSig(N, nullptr);
        stateSig[nfa.startNode] = triggerExprp->cloneTreePure(false);
        for (int i = 0; i < N; ++i) {
            if (stateVars[i]) {
                stateSig[i] = new AstVarRef{flp, stateVars[i], VAccess::READ};
            } else if (counterActiveVars[i]) {
                AstVarRef* const activeRefp
                    = new AstVarRef{flp, counterActiveVars[i], VAccess::READ};
                if (nfa.nodes[i].counterMin == 0) {
                    stateSig[i] = activeRefp;
                } else {
                    AstGte* const gtep
                        = new AstGte{flp, new AstVarRef{flp, counterCountVars[i], VAccess::READ},
                                     new AstConst{flp, AstConst::WidthedValue{}, 32,
                                                  static_cast<uint32_t>(nfa.nodes[i].counterMin)}};
                    gtep->dtypeSetBit();
                    AstNodeExpr* const andp = new AstAnd{flp, activeRefp, gtep};
                    andp->dtypeSetBit();
                    stateSig[i] = andp;
                }
            }
        }

        auto buildAcceptNow = [flp](AstNodeExpr* stateExprp, AstNodeExpr* condp) -> AstNodeExpr* {
            AstNodeExpr* const statep = stateExprp->cloneTreePure(false);
            if (!condp) return statep;
            AstSampled* const sampp = new AstSampled{flp, condp->cloneTreePure(false)};
            sampp->dtypeSetBit();
            AstNodeExpr* const andp = new AstAnd{flp, statep, sampp};
            andp->dtypeSetBit();
            return andp;
        };

        for (int pass = 0; pass < 2 * N + 2; ++pass) {
            bool changed = false;
            // Seed SAnd combiners inside the fixed-point (sub-NFA termNodes
            // may be Link-propagated and only available after a pass).
            for (int i = 0; i < N; ++i) {
                const auto& node = nfa.nodes[i];
                if (!node.isAndCombiner) continue;
                if (stateSig[i]) continue;
                const int l = node.andLhsTermId;
                const int r = node.andRhsTermId;
                if (l < 0 || r < 0) continue;
                if (!stateSig[l] || !stateSig[r]) continue;

                AstNodeExpr* const acceptLNowp = buildAcceptNow(stateSig[l], node.andLhsCondp);
                AstNodeExpr* const acceptRNowp = buildAcceptNow(stateSig[r], node.andRhsCondp);

                AstNodeExpr* const doneLRefp = new AstVarRef{flp, doneLVars[i], VAccess::READ};
                AstNodeExpr* const doneLOrp = new AstOr{flp, doneLRefp, acceptLNowp};
                doneLOrp->dtypeSetBit();
                AstNodeExpr* const doneRRefp = new AstVarRef{flp, doneRVars[i], VAccess::READ};
                AstNodeExpr* const doneROrp = new AstOr{flp, doneRRefp, acceptRNowp};
                doneROrp->dtypeSetBit();
                AstNodeExpr* const bothDonep = new AstAnd{flp, doneLOrp, doneROrp};
                bothDonep->dtypeSetBit();
                AstNodeExpr* const oneNowp = new AstOr{flp, acceptLNowp->cloneTreePure(false),
                                                       acceptRNowp->cloneTreePure(false)};
                oneNowp->dtypeSetBit();
                AstNodeExpr* const acceptp = new AstAnd{flp, bothDonep, oneNowp};
                acceptp->dtypeSetBit();
                stateSig[i] = acceptp;
                changed = true;
            }

            for (const auto& edge : nfa.edges) {
                if (edge.consumesCycle) continue;
                if (!stateSig[edge.fromId]) continue;
                if (nfa.nodes[edge.toId].isAccept) continue;
                if (nfa.nodes[edge.toId].isRejectSink) continue;

                AstNodeExpr* const srcSigp = stateSig[edge.fromId]->cloneTreePure(false);
                AstNodeExpr* const contributionp = andCond(flp, srcSigp, edge.condp);

                if (!stateSig[edge.toId]) {
                    stateSig[edge.toId] = contributionp;
                    changed = true;
                } else if (!needsReg[edge.toId]) {
                    stateSig[edge.toId] = orExprs(flp, stateSig[edge.toId], contributionp);
                    changed = true;
                } else {
                    contributionp->deleteTree();
                }
            }
            if (!changed) break;
        }

        // Phase 2: Compute Edge activations -> NBA
        AstNode* bodyp = nullptr;
        for (int i = 0; i < N; ++i) {
            if (!stateVars[i]) continue;

            AstNodeExpr* nextStatep = nullptr;
            for (const auto& edge : nfa.edges) {
                if (edge.toId != i) continue;
                if (!edge.consumesCycle) continue;
                if (!stateSig[edge.fromId]) continue;

                AstNodeExpr* srcSigp = stateSig[edge.fromId]->cloneTreePure(false);
                srcSigp = andCond(flp, srcSigp, edge.condp);

                if (disableExprp && !snapshotVarp) {
                    AstNodeExpr* const notDisp
                        = new AstNot{flp, disableExprp->cloneTreePure(false)};
                    notDisp->dtypeSetBit();
                    srcSigp = new AstAnd{flp, srcSigp, notDisp};
                    srcSigp->dtypeSetBit();
                }
                nextStatep = orExprs(flp, nextStatep, srcSigp);
            }

            if (!nextStatep) nextStatep = new AstConst{flp, AstConst::BitFalse{}};

            AstAssignDly* const assignp = new AstAssignDly{
                flp, new AstVarRef{flp, stateVars[i], VAccess::WRITE}, nextStatep};
            if (!bodyp) {
                bodyp = assignp;
            } else {
                bodyp->addNext(assignp);
            }
        }

        if (bodyp) {
            // Capture disableCnt in Phase-2 NBA before any reactive re-evaluation.
            if (snapshotVarp && disableCntVarp) {
                AstAssignDly* const snapAssignp
                    = new AstAssignDly{flp, new AstVarRef{flp, snapshotVarp, VAccess::WRITE},
                                       new AstVarRef{flp, disableCntVarp, VAccess::READ}};
                bodyp->addNext(snapAssignp);
            }
            AstAlways* const alwaysp
                = new AstAlways{flp, VAlwaysKwd::ALWAYS, senTreep->cloneTree(false), bodyp};
            m_modp->addStmtsp(alwaysp);
        }

        // Phase 2b: Counter FSM always block.
        // if (active) { if (done) active<=0; else counter<=counter+1; }
        // else if (incoming) { active<=1; counter<=0; }
        for (int ci = 0; ci < N; ++ci) {
            if (!counterActiveVars[ci]) continue;
            AstVar* const activep = counterActiveVars[ci];
            AstVar* const cntp = counterCountVars[ci];
            const uint32_t counterMax = static_cast<uint32_t>(nfa.nodes[ci].counterMax);

            AstNodeExpr* incomingp = nullptr;
            for (const auto& edge : nfa.edges) {
                if (edge.toId != ci) continue;
                if (!edge.consumesCycle) continue;
                if (!stateSig[edge.fromId]) continue;
                AstNodeExpr* contribp = stateSig[edge.fromId]->cloneTreePure(false);
                contribp = andCond(flp, contribp, edge.condp);
                if (disableExprp) {
                    AstNodeExpr* const notDisp
                        = new AstNot{flp, disableExprp->cloneTreePure(false)};
                    notDisp->dtypeSetBit();
                    contribp = new AstAnd{flp, contribp, notDisp};
                    contribp->dtypeSetBit();
                }
                incomingp = orExprs(flp, incomingp, contribp);
            }
            if (!incomingp) incomingp = new AstConst{flp, AstConst::BitFalse{}};

            AstNodeExpr* inWindowp = nullptr;
            if (nfa.nodes[ci].counterMin == 0) {
                inWindowp = new AstConst{flp, AstConst::BitTrue{}};
            } else {
                inWindowp
                    = new AstGte{flp, new AstVarRef{flp, cntp, VAccess::READ},
                                 new AstConst{flp, AstConst::WidthedValue{}, 32,
                                              static_cast<uint32_t>(nfa.nodes[ci].counterMin)}};
                inWindowp->dtypeSetBit();
            }
            AstNodeExpr* acceptedNowp = nullptr;
            if (acceptCondp) {
                AstSampled* const sampp = new AstSampled{flp, acceptCondp->cloneTreePure(false)};
                sampp->dtypeSetBit();
                acceptedNowp = new AstAnd{flp, inWindowp, sampp};
                acceptedNowp->dtypeSetBit();
            } else {
                acceptedNowp = inWindowp;
            }

            AstNodeExpr* const counterAtEndp
                = new AstEq{flp, new AstVarRef{flp, cntp, VAccess::READ},
                            new AstConst{flp, AstConst::WidthedValue{}, 32, counterMax}};
            counterAtEndp->dtypeSetBit();

            AstNodeExpr* const donep = new AstOr{flp, acceptedNowp, counterAtEndp};
            donep->dtypeSetBit();

            AstAssignDly* const clearActivep
                = new AstAssignDly{flp, new AstVarRef{flp, activep, VAccess::WRITE},
                                   new AstConst{flp, AstConst::BitFalse{}}};
            AstAdd* const addExprp
                = new AstAdd{flp, new AstVarRef{flp, cntp, VAccess::READ},
                             new AstConst{flp, AstConst::WidthedValue{}, 32, 1u}};
            addExprp->dtypeFrom(cntp);
            AstAssignDly* const incCountp
                = new AstAssignDly{flp, new AstVarRef{flp, cntp, VAccess::WRITE}, addExprp};
            AstIf* const doneIfp = new AstIf{flp, donep, clearActivep, incCountp};

            AstAssignDly* const setActivep
                = new AstAssignDly{flp, new AstVarRef{flp, activep, VAccess::WRITE},
                                   new AstConst{flp, AstConst::BitTrue{}}};
            AstAssignDly* const resetCountp
                = new AstAssignDly{flp, new AstVarRef{flp, cntp, VAccess::WRITE},
                                   new AstConst{flp, AstConst::WidthedValue{}, 32, 0u}};
            setActivep->addNext(resetCountp);
            AstIf* const startIfp = new AstIf{flp, incomingp, setActivep, nullptr};
            AstIf* const topIfp
                = new AstIf{flp, new AstVarRef{flp, activep, VAccess::READ}, doneIfp, startIfp};

            AstAlways* const counterAlwaysp
                = new AstAlways{flp, VAlwaysKwd::ALWAYS, senTreep->cloneTree(false), topIfp};
            m_modp->addStmtsp(counterAlwaysp);
        }

        // Phase 2c: SAnd combiner done-latch always block.
        // NBA semantics ensure doneL/doneR read pre-update values (IEEE 16.9.5).
        for (int ai = 0; ai < N; ++ai) {
            if (!doneLVars[ai]) continue;
            const auto& node = nfa.nodes[ai];
            const int l = node.andLhsTermId;
            const int r = node.andRhsTermId;
            if (!stateSig[l] || !stateSig[r] || !stateSig[ai]) continue;

            AstAssignDly* const clearLp
                = new AstAssignDly{flp, new AstVarRef{flp, doneLVars[ai], VAccess::WRITE},
                                   new AstConst{flp, AstConst::BitFalse{}}};
            AstAssignDly* const clearRp
                = new AstAssignDly{flp, new AstVarRef{flp, doneRVars[ai], VAccess::WRITE},
                                   new AstConst{flp, AstConst::BitFalse{}}};
            clearLp->addNext(clearRp);

            AstNodeExpr* const acceptLNowp = buildAcceptNow(stateSig[l], node.andLhsCondp);
            AstNodeExpr* const acceptRNowp = buildAcceptNow(stateSig[r], node.andRhsCondp);
            AstNodeExpr* gateLp = acceptLNowp;
            AstNodeExpr* gateRp = acceptRNowp;
            if (disableExprp) {
                AstNodeExpr* const notDisLp = new AstNot{flp, disableExprp->cloneTreePure(false)};
                notDisLp->dtypeSetBit();
                gateLp = new AstAnd{flp, gateLp, notDisLp};
                gateLp->dtypeSetBit();
                AstNodeExpr* const notDisRp = new AstNot{flp, disableExprp->cloneTreePure(false)};
                notDisRp->dtypeSetBit();
                gateRp = new AstAnd{flp, gateRp, notDisRp};
                gateRp->dtypeSetBit();
            }
            AstAssignDly* const setLp
                = new AstAssignDly{flp, new AstVarRef{flp, doneLVars[ai], VAccess::WRITE},
                                   new AstConst{flp, AstConst::BitTrue{}}};
            AstIf* const setLIfp = new AstIf{flp, gateLp, setLp, nullptr};
            AstAssignDly* const setRp
                = new AstAssignDly{flp, new AstVarRef{flp, doneRVars[ai], VAccess::WRITE},
                                   new AstConst{flp, AstConst::BitTrue{}}};
            AstIf* const setRIfp = new AstIf{flp, gateRp, setRp, nullptr};
            setLIfp->addNext(setRIfp);

            AstIf* const topp
                = new AstIf{flp, stateSig[ai]->cloneTreePure(false), clearLp, setLIfp};
            AstAlways* const combAlwaysp
                = new AstAlways{flp, VAlwaysKwd::ALWAYS, senTreep->cloneTree(false), topp};
            m_modp->addStmtsp(combAlwaysp);
        }

        // Phase 3: Compute accept/reject from terminal Links.
        // rejectBasep: counter sources only at window end; others on every terminal cycle.
        AstNodeExpr* snapshotOkp = nullptr;
        if (snapshotVarp && disableCntVarp) {
            snapshotOkp = new AstEq{flp, new AstVarRef{flp, snapshotVarp, VAccess::READ},
                                    new AstVarRef{flp, disableCntVarp, VAccess::READ}};
            snapshotOkp->dtypeSetBit();
        }

        AstNodeExpr* terminalActivep = nullptr;
        AstNodeExpr* rejectBasep = nullptr;
        for (const auto& edge : nfa.edges) {
            if (edge.toId != nfa.acceptNode) continue;
            if (edge.consumesCycle) continue;
            if (!stateSig[edge.fromId]) continue;

            AstNodeExpr* srcSigp = stateSig[edge.fromId]->cloneTreePure(false);
            srcSigp = andCond(flp, srcSigp, edge.condp);
            if (snapshotOkp) {
                srcSigp = new AstAnd{flp, srcSigp, snapshotOkp->cloneTreePure(false)};
                srcSigp->dtypeSetBit();
            }

            if (nfa.nodes[edge.fromId].isCounter) {
                const int ci = edge.fromId;
                terminalActivep = orExprs(flp, terminalActivep, srcSigp->cloneTreePure(false));
                AstNodeExpr* const atEndp
                    = new AstEq{flp, new AstVarRef{flp, counterCountVars[ci], VAccess::READ},
                                new AstConst{flp, AstConst::WidthedValue{}, 32,
                                             static_cast<uint32_t>(nfa.nodes[ci].counterMax)}};
                atEndp->dtypeSetBit();
                AstNodeExpr* const expireContribp = new AstAnd{flp, srcSigp, atEndp};
                expireContribp->dtypeSetBit();
                rejectBasep = orExprs(flp, rejectBasep, expireContribp);
            } else if (nfa.nodes[edge.fromId].isUnbounded
                       || nfa.nodes[edge.fromId].isAndCombiner) {
                // Liveness or SAnd combiner: accept only; sub-NFAs own their rejects.
                terminalActivep = orExprs(flp, terminalActivep, srcSigp);
            } else {
                terminalActivep = orExprs(flp, terminalActivep, srcSigp->cloneTreePure(false));
                rejectBasep = orExprs(flp, rejectBasep, srcSigp);
            }
        }

        // If no Links to accept, check stateSig at the last registered node
        // that connects directly (this handles standalone sequences)
        if (!terminalActivep) {
            // Find the highest-numbered registered node
            for (int i = N - 1; i >= 0; --i) {
                if (stateVars[i] && stateSig[i]) {
                    terminalActivep = stateSig[i]->cloneTreePure(false);
                    break;
                }
            }
        }
        if (!terminalActivep) { terminalActivep = new AstConst{flp, AstConst::BitFalse{}}; }

        // Phase 3a: required-step rejection.
        // Fires when source is active but link condition is false.
        // E.g. `a |-> b ##...`: antecedent fires but b is false -- the attempt never
        // leaves the start state, so no terminal-based reject can fire.
        AstNodeExpr* requiredStepRejectp = nullptr;
        for (const auto& edge : nfa.edges) {
            if (!edge.rejectOnFail) continue;
            if (edge.consumesCycle) continue;
            if (!stateSig[edge.fromId]) continue;
            if (!edge.condp) continue;
            AstNodeExpr* const srcSigp = stateSig[edge.fromId]->cloneTreePure(false);
            AstNodeExpr* const notCondp = new AstNot{flp, edge.condp->cloneTreePure(false)};
            notCondp->dtypeSetBit();
            AstNodeExpr* const failp = new AstAnd{flp, srcSigp, notCondp};
            failp->dtypeSetBit();
            if (outRequiredStepSrcsp) {
                outRequiredStepSrcsp->push_back(failp->cloneTreePure(false));
            }
            requiredStepRejectp = orExprs(flp, requiredStepRejectp, failp);
        }

        // Phase 3b: Throughout-drop rejection (IEEE 16.9.9).
        // fail_i = state_active[i] && !$sampled(AND of throughout exprs).
        AstNodeExpr* throughoutRejectp = nullptr;
        for (int i = 0; i < N; ++i) {
            const auto& conds = nfa.nodes[i].throughoutConds;
            if (conds.empty()) continue;
            // SAnd combiner stateSig fires only at completion; sub-sequences own their nodes.
            if (nfa.nodes[i].isAndCombiner) continue;
            AstNodeExpr* stateExprp = nullptr;
            if (stateVars[i]) {
                stateExprp = new AstVarRef{flp, stateVars[i], VAccess::READ};
            } else if (stateSig[i]) {
                stateExprp = stateSig[i]->cloneTreePure(false);
            } else {
                continue;
            }
            AstNodeExpr* guardp = nullptr;
            for (AstNodeExpr* const cp : conds) {
                AstSampled* const sp = new AstSampled{flp, cp->cloneTreePure(false)};
                sp->dtypeSetBit();
                if (!guardp) {
                    guardp = sp;
                } else {
                    guardp = new AstAnd{flp, guardp, sp};
                    guardp->dtypeSetBit();
                }
            }
            AstNodeExpr* const notGuardp = new AstNot{flp, guardp};
            notGuardp->dtypeSetBit();
            AstNodeExpr* const failp = new AstAnd{flp, stateExprp, notGuardp};
            failp->dtypeSetBit();
            throughoutRejectp = orExprs(flp, throughoutRejectp, failp);
        }

        for (int i = 0; i < N; ++i) {
            if (stateSig[i]) {
                stateSig[i]->deleteTree();
                stateSig[i] = nullptr;
            }
        }
        // disable iff applied to throughout-drop and required-step rejects:
        // either kind of failure during disable is abandoned per IEEE 16.12.
        if (disableExprp) {
            if (throughoutRejectp) {
                AstNodeExpr* const notDisp = new AstNot{flp, disableExprp->cloneTreePure(false)};
                notDisp->dtypeSetBit();
                throughoutRejectp = new AstAnd{flp, throughoutRejectp, notDisp};
                throughoutRejectp->dtypeSetBit();
            }
            if (requiredStepRejectp) {
                AstNodeExpr* const notDisp = new AstNot{flp, disableExprp->cloneTreePure(false)};
                notDisp->dtypeSetBit();
                requiredStepRejectp = new AstAnd{flp, requiredStepRejectp, notDisp};
                requiredStepRejectp->dtypeSetBit();
            }
        }

        if (snapshotOkp) {
            snapshotOkp->deleteTree();
            snapshotOkp = nullptr;
        }

        if (disableExprp) {
            disableExprp->deleteTree();
            disableExprp = nullptr;
        }

        // Property negation (IEEE 1800-2023 16.12.1 `not`): invert accept/reject.
        if (negated) {
            if (isCover) {
                if (terminalActivep) terminalActivep->deleteTree();
                AstNodeExpr* negRejectp = nullptr;
                if (acceptCondp && rejectBasep) {
                    AstNodeExpr* const sampledCondp
                        = new AstSampled{flp, acceptCondp->cloneTreePure(false)};
                    sampledCondp->dtypeFrom(acceptCondp);
                    AstNodeExpr* const notCondp = new AstNot{flp, sampledCondp};
                    notCondp->dtypeSetBit();
                    negRejectp = new AstAnd{flp, rejectBasep, notCondp};
                    negRejectp->dtypeSetBit();
                } else if (rejectBasep) {
                    rejectBasep->deleteTree();
                }
                if (throughoutRejectp) {
                    negRejectp = orExprs(flp, negRejectp, throughoutRejectp);
                    if (negRejectp) negRejectp->dtypeSetBit();
                }
                if (requiredStepRejectp) {
                    negRejectp = orExprs(flp, negRejectp, requiredStepRejectp);
                    if (negRejectp) negRejectp->dtypeSetBit();
                }
                return negRejectp ? negRejectp : new AstConst{flp, AstConst::BitFalse{}};
            }
            // Negated assert/assume: output = !accept.
            AstNodeExpr* acceptp = terminalActivep;
            if (acceptCondp) {
                AstNodeExpr* const sampledCondp
                    = new AstSampled{flp, acceptCondp->cloneTreePure(false)};
                sampledCondp->dtypeFrom(acceptCondp);
                acceptp = new AstAnd{flp, acceptp, sampledCondp};
                acceptp->dtypeSetBit();
            }
            if (outAcceptpp) {
                AstNodeExpr* notPAcceptp = nullptr;
                if (acceptCondp && rejectBasep) {
                    AstNodeExpr* const sampledCondp
                        = new AstSampled{flp, acceptCondp->cloneTreePure(false)};
                    sampledCondp->dtypeFrom(acceptCondp);
                    AstNodeExpr* const notCondp = new AstNot{flp, sampledCondp};
                    notCondp->dtypeSetBit();
                    notPAcceptp = new AstAnd{flp, rejectBasep->cloneTreePure(false), notCondp};
                    notPAcceptp->dtypeSetBit();
                } else if (rejectBasep) {
                    notPAcceptp = rejectBasep->cloneTreePure(false);
                }
                if (throughoutRejectp)
                    notPAcceptp
                        = orExprs(flp, notPAcceptp, throughoutRejectp->cloneTreePure(false));
                if (requiredStepRejectp)
                    notPAcceptp
                        = orExprs(flp, notPAcceptp, requiredStepRejectp->cloneTreePure(false));
                *outAcceptpp = notPAcceptp;
            }
            if (throughoutRejectp) throughoutRejectp->deleteTree();
            if (rejectBasep) rejectBasep->deleteTree();
            if (requiredStepRejectp) requiredStepRejectp->deleteTree();
            AstNodeExpr* const resultExprp = new AstNot{flp, acceptp};
            resultExprp->dtypeSetBit();
            return resultExprp;
        }

        if (isCover) {
            if (throughoutRejectp) throughoutRejectp->deleteTree();
            if (rejectBasep) rejectBasep->deleteTree();
            if (requiredStepRejectp) requiredStepRejectp->deleteTree();
            if (acceptCondp) {
                AstNodeExpr* const sampledCondp
                    = new AstSampled{flp, acceptCondp->cloneTreePure(false)};
                sampledCondp->dtypeFrom(acceptCondp);
                AstNodeExpr* const acceptp = new AstAnd{flp, terminalActivep, sampledCondp};
                acceptp->dtypeSetBit();
                return acceptp;
            }
            return terminalActivep;
        }

        // Assert/assume: output = !reject
        AstNodeExpr* rejectp = nullptr;
        if (acceptCondp && rejectBasep) {
            AstNodeExpr* const sampledCondp
                = new AstSampled{flp, acceptCondp->cloneTreePure(false)};
            sampledCondp->dtypeFrom(acceptCondp);
            AstNodeExpr* const notCondp = new AstNot{flp, sampledCondp};
            notCondp->dtypeSetBit();
            rejectp = new AstAnd{flp, rejectBasep, notCondp};
            rejectp->dtypeSetBit();
        } else if (rejectBasep) {
            rejectBasep->deleteTree();
        }
        if (outAcceptpp) {
            AstNodeExpr* acceptExprp = terminalActivep->cloneTreePure(false);
            if (acceptCondp) {
                AstNodeExpr* const sp = new AstSampled{flp, acceptCondp->cloneTreePure(false)};
                sp->dtypeSetBit();
                acceptExprp = new AstAnd{flp, acceptExprp, sp};
                acceptExprp->dtypeSetBit();
            }
            *outAcceptpp = acceptExprp;
        }
        if (terminalActivep) terminalActivep->deleteTree();

        if (throughoutRejectp) {
            rejectp = orExprs(flp, rejectp, throughoutRejectp);
            if (rejectp) rejectp->dtypeSetBit();
        }
        if (requiredStepRejectp) {
            rejectp = orExprs(flp, rejectp, requiredStepRejectp);
            if (rejectp) rejectp->dtypeSetBit();
        }
        if (!rejectp) { return new AstConst{flp, AstConst::BitTrue{}}; }
        AstNodeExpr* const resultExprp = new AstNot{flp, rejectp};
        resultExprp->dtypeSetBit();
        return resultExprp;
    }
};

}  // namespace

//######################################################################
// Top-level visitor

class AssertNfaVisitor final : public VNVisitor {
    // STATE
    AstNodeModule* m_modp = nullptr;
    SvaNfaEmitter* m_emitterp = nullptr;
    V3UniqueNames m_propVarNames{"__Vpropvar"};
    V3UniqueNames m_disableCntNames{"__VnfaDis"};
    std::set<const AstProperty*> m_inliningProps;  // Recursion guard for inlineNamedProperty

    // Wire accept node and mid-window sources for a successful NFA build.
    static void wireAcceptAndMidSources(SvaNfa& nfa, const BuildResult& result, FileLine* flp) {
        nfa.createAcceptNode();
        nfa.addLink(result.termNode, nfa.acceptNode);
        for (int src : result.midSources) {
            AstNodeExpr* condp = nullptr;
            for (AstNodeExpr* const tc : nfa.nodes[src].throughoutConds) {
                AstNodeExpr* const tcClone = tc->cloneTreePure(false);
                condp = condp ? new AstAnd{flp, condp, tcClone} : tcClone;
                if (condp->width() != 1) condp->dtypeSetBit();
            }
            nfa.addLink(src, nfa.acceptNode, condp);
            nfa.nodes[src].isUnbounded = true;
        }
    }

    static AstNodeExpr* getSequenceBodyExprp(const AstSequence* seqp) {
        AstNode* bodyp = seqp->stmtsp();
        while (bodyp && VN_IS(bodyp, Var)) bodyp = bodyp->nextp();
        return VN_CAST(bodyp, NodeExpr);
    }

    static AstPropSpec* getPropertySpecp(const AstProperty* propp) {
        AstNode* stmtp = propp->stmtsp();
        while (stmtp
               && (VN_IS(stmtp, Var) || VN_IS(stmtp, InitialStaticStmt)
                   || VN_IS(stmtp, InitialAutomaticStmt))) {
            stmtp = stmtp->nextp();
        }
        return VN_CAST(stmtp, PropSpec);
    }

    void inlineNamedProperty(AstPropSpec* outerSpecp, AstFuncRef* funcrefp,
                             const AstProperty* propyp) {
        // Recursion guard: IEEE 1800-2023 16.12.1 forbids recursive properties.
        if (m_inliningProps.count(propyp)) {
            funcrefp->v3error("Recursive property reference not allowed"
                              " (IEEE 1800-2023 16.12.1)");
            return;
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
            {
                const auto portIt = portMap.find(refp->varp());
                if (portIt != portMap.end()) {
                    refp->replaceWith(portIt->second->cloneTree(false));
                    VL_DO_DANGLING(pushDeletep(refp), refp);
                    return;
                }
            }
            {
                const auto localIt = localVarMap.find(refp->varp());
                if (localIt != localVarMap.end()) { refp->varp(localIt->second); }
            }
        });

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

    void inlineSequenceRef(AstFuncRef* funcrefp, const AstSequence* seqp) {
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
    }

    // Must run before hasMultiCycleExpr() so NFA sees sequence bodies.
    void inlineAllSequenceRefs(AstNode* rootp) {
        bool changed = true;
        while (changed) {
            changed = false;
            rootp->foreach([&](AstFuncRef* funcrefp) {
                if (changed) return;
                if (const AstSequence* const seqp = VN_CAST(funcrefp->taskp(), Sequence)) {
                    inlineSequenceRef(funcrefp, seqp);
                    changed = true;
                }
            });
        }
    }

    static bool hasMultiCycleExpr(const AstNode* nodep) {
        return !nodep->forall([](const AstNode* np) {
            return !VN_IS(np, SExpr) && !VN_IS(np, SConsRep) && !VN_IS(np, SGotoRep)
                   && !VN_IS(np, SIntersect) && !VN_IS(np, SThroughout) && !VN_IS(np, SAnd)
                   && !VN_IS(np, SOr) && !VN_IS(np, SNonConsRep);
        });
    }

    struct PropertyParts final {
        AstNodeExpr* triggerExprp = nullptr;
        AstNodeExpr* seqExprp = nullptr;
        bool isOverlapped = true;
        bool hasImplication = false;
    };

    static PropertyParts decomposeProperty(AstNode* propp) {
        PropertyParts parts;
        if (AstPropSpec* const specp = VN_CAST(propp, PropSpec)) { propp = specp->propp(); }
        if (AstImplication* const implp = VN_CAST(propp, Implication)) {
            parts.hasImplication = true;
            parts.isOverlapped = implp->isOverlapped();
            parts.triggerExprp = implp->lhsp();
            parts.seqExprp = implp->rhsp();
        } else if (AstNodeExpr* const exprp = VN_CAST(propp, NodeExpr)) {
            parts.triggerExprp = nullptr;
            parts.seqExprp = exprp;
        }
        return parts;
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
        if (!parts.seqExprp) return;

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
        AstNodeExpr* disableExprp = nullptr;
        if (propSpecp) {
            if (!senTreep && propSpecp->sensesp()) {
                senTreep
                    = new AstSenTree{propSpecp->fileline(), propSpecp->sensesp()->cloneTree(true)};
                senTreeOwned = true;
            }
            disableExprp = propSpecp->disablep();
        }
        if (!senTreep) return;

        FileLine* const flp = assertp->fileline();
        const bool isCover = VN_IS(assertp, Cover);

        SvaNfa nfa;
        SvaNfaBuilder builder{nfa};

        BuildResult result = BuildResult::fail();
        if (parts.hasImplication) {
            nfa.startNode = nfa.createNode();

            const BuildResult antResult = builder.buildExpr(parts.triggerExprp, nfa.startNode);
            if (!antResult.valid()) {
                // Fall through to V3AssertPre for unsupported constructs.
                // Only replace with BitFalse on real semantic errors.
                if (antResult.errorEmitted) {
                    if (propSpecp) {
                        AstNode* const innerPropp = propSpecp->propp();
                        innerPropp->replaceWith(new AstConst{flp, AstConst::BitFalse{}});
                        VL_DO_DANGLING(pushDeletep(innerPropp), innerPropp);
                    }
                }
                if (senTreeOwned) senTreep->deleteTree();
                return;
            }

            // Use raw createNode() (not scopedCreateNode) so trigNode starts without liveness.
            // Reaching the antecedent terminal is a definitive event; consequent must fire.
            const int trigNode = nfa.createNode();
            if (antResult.finalCondp) {
                nfa.addLink(antResult.termNode, trigNode,
                            new AstSampled{flp, antResult.finalCondp->cloneTreePure(false)});
                if (!antResult.finalCondp->backp()) antResult.finalCondp->deleteTree();
            } else {
                nfa.addLink(antResult.termNode, trigNode);
            }
            builder.resetScope();

            if (parts.isOverlapped) {
                result = builder.buildExpr(seqBodyp, trigNode,
                                           /*isTopLevelStep=*/true);
            } else {
                const int delayNode = nfa.createNode();
                nfa.addClockEdge(trigNode, delayNode);
                result = builder.buildExpr(seqBodyp, delayNode,
                                           /*isTopLevelStep=*/true);
            }

            if (result.valid()) wireAcceptAndMidSources(nfa, result, flp);
        } else {
            result = builder.build(seqBodyp);
            if (result.valid()) wireAcceptAndMidSources(nfa, result, flp);
        }

        if (!result.valid()) {
            // Fall through to V3AssertPre for unsupported constructs.
            // Only replace with BitFalse on real semantic errors.
            if (result.errorEmitted) {
                if (propSpecp) {
                    AstNode* const innerPropp = propSpecp->propp();
                    innerPropp->replaceWith(new AstConst{flp, AstConst::BitFalse{}});
                    VL_DO_DANGLING(pushDeletep(innerPropp), innerPropp);
                } else {
                    AstNode* const oldPropp = assertp->propp();
                    oldPropp->replaceWith(new AstConst{flp, AstConst::BitFalse{}});
                    VL_DO_DANGLING(pushDeletep(oldPropp), oldPropp);
                }
            }
            if (senTreeOwned) senTreep->deleteTree();
            return;
        }

        // Build succeeded. Now create snapshot mechanism for disable iff if needed.
        // Done here (not before build) so failed builds don't pollute the AST.
        AstVar* disableCntVarp = nullptr;
        AstVar* snapshotVarp = nullptr;
        const bool disableHasSampled
            = disableExprp && disableExprp->exists([](const AstSampled*) { return true; });
        if (disableExprp && !parts.hasImplication && !VN_IS(disableExprp, Const)
            && !disableHasSampled) {
            AstNodeDType* const u32DTypep = m_modp->findBasicDType(VBasicDTypeKwd::UINT32);
            const std::string cntName = m_disableCntNames.get("");
            disableCntVarp = new AstVar{flp, VVarType::MODULETEMP, cntName, u32DTypep};
            disableCntVarp->lifetime(VLifetime::STATIC_EXPLICIT);
            m_modp->addStmtsp(disableCntVarp);

            AstNodeExpr* const rdRefp = new AstVarRef{flp, disableCntVarp, VAccess::READ};
            AstNodeExpr* const wrRefp = new AstVarRef{flp, disableCntVarp, VAccess::WRITE};
            AstNodeExpr* const incrExprp
                = new AstAdd{flp, rdRefp, new AstConst{flp, AstConst::WidthedValue{}, 32, 1u}};
            incrExprp->dtypeFrom(disableCntVarp);
            AstAssign* const incrAssignp = new AstAssign{flp, wrRefp, incrExprp};
            AstSenItem* const senItemp
                = new AstSenItem{flp, VEdgeType::ET_POSEDGE, disableExprp->cloneTreePure(false)};
            AstSenTree* const disSenp = new AstSenTree{flp, senItemp};
            AstAlways* const disAlwaysp
                = new AstAlways{flp, VAlwaysKwd::ALWAYS, disSenp, incrAssignp};
            m_modp->addStmtsp(disAlwaysp);

            const std::string snapName = m_disableCntNames.get("") + "__snap";
            snapshotVarp = new AstVar{flp, VVarType::MODULETEMP, snapName, u32DTypep};
            snapshotVarp->lifetime(VLifetime::STATIC_EXPLICIT);
            m_modp->addStmtsp(snapshotVarp);

            if (propSpecp && propSpecp->disablep()) {
                AstNodeExpr* const oldDisp = propSpecp->disablep();
                oldDisp->unlinkFrBack();
            }
        }
        const bool disableExprUnlinked = disableCntVarp && disableExprp;

        AstAssert* const assertAssertp = VN_CAST(assertp, Assert);
        const bool needAccept
            = !isCover && !parts.hasImplication && assertAssertp && assertAssertp->passsp();
        AstNodeExpr* acceptExprp = nullptr;

        AstAssert* const assertWithFailp = VN_CAST(assertp, Assert);
        const bool needPerSrcFail
            = !isCover && !parts.hasImplication && assertWithFailp && assertWithFailp->failsp();
        std::vector<AstNodeExpr*> requiredStepSrcs;

        AstNodeExpr* const alwaysTriggerp = new AstConst{flp, AstConst::BitTrue{}};
        AstNodeExpr* const outputExprp
            = m_emitterp->emit(flp, nfa, alwaysTriggerp, senTreep, result.finalCondp, isCover,
                               disableExprp ? disableExprp->cloneTreePure(false) : nullptr,
                               negated, needAccept ? &acceptExprp : nullptr, disableCntVarp,
                               snapshotVarp, needPerSrcFail ? &requiredStepSrcs : nullptr);

        AstSenTree* const perSrcSenTreep
            = (requiredStepSrcs.size() >= 2) ? senTreep->cloneTree(false) : nullptr;

        alwaysTriggerp->deleteTree();
        if (senTreeOwned) senTreep->deleteTree();
        if (disableExprUnlinked) disableExprp->deleteTree();
        if (result.finalCondp && !result.finalCondp->backp()) { result.finalCondp->deleteTree(); }

        // Gate pass handler on accept to prevent vacuous-pass firings.
        if (needAccept && acceptExprp) {
            AstNode* passsp = assertAssertp->passsp();
            if (passsp) {
                passsp->unlinkFrBackWithNext();
                assertAssertp->addPasssp(new AstIf{flp, acceptExprp->cloneTreePure(false),
                                                   passsp->cloneTree(false), nullptr});
                // Fail-handler prefix for overlapping instances (IEEE 16.12):
                // fires when reject=1 && accept=1 in the same cycle.
                if (AstNode* const failsp = assertAssertp->failsp()) {
                    failsp->addHereThisAsNext(
                        new AstIf{flp, acceptExprp, passsp->cloneTree(false), nullptr});
                } else {
                    acceptExprp->deleteTree();
                }
                VL_DO_DANGLING(pushDeletep(passsp), passsp);
            } else {
                acceptExprp->deleteTree();
            }
        }

        // Extra fail-handler fires for simultaneous required-step failures
        // (IEEE 1800-2023: fail handler fires once per failing thread).
        if (requiredStepSrcs.size() >= 2 && assertWithFailp && assertWithFailp->failsp()
            && perSrcSenTreep) {
            AstNode* const failsp = assertWithFailp->failsp();
            AstNodeExpr* cumulativeOrp = requiredStepSrcs[0]->cloneTreePure(false);
            for (size_t i = 1; i < requiredStepSrcs.size(); ++i) {
                AstNodeExpr* const srcp = requiredStepSrcs[i];
                AstNodeExpr* const condp = new AstAnd{flp, srcp->cloneTreePure(false),
                                                      cumulativeOrp->cloneTreePure(false)};
                condp->dtypeSetBit();
                AstNode* const failClonep = failsp->cloneTree(true);
                AstIf* const ifp = new AstIf{flp, condp, failClonep, nullptr};
                AstAlways* const alwaysp = new AstAlways{flp, VAlwaysKwd::ALWAYS,
                                                         perSrcSenTreep->cloneTree(false), ifp};
                m_modp->addStmtsp(alwaysp);
                AstNodeExpr* const extOrp
                    = new AstOr{flp, cumulativeOrp, srcp->cloneTreePure(false)};
                extOrp->dtypeSetBit();
                cumulativeOrp = extOrp;
            }
            for (AstNodeExpr* const srcp : requiredStepSrcs) srcp->deleteTree();
            cumulativeOrp->deleteTree();
            perSrcSenTreep->deleteTree();
        } else {
            for (AstNodeExpr* const srcp : requiredStepSrcs) srcp->deleteTree();
            if (perSrcSenTreep) perSrcSenTreep->deleteTree();
        }

        if (propSpecp) {
            AstNode* const innerPropp = propSpecp->propp();
            innerPropp->replaceWith(outputExprp);
            VL_DO_DANGLING(pushDeletep(innerPropp), innerPropp);
        } else {
            AstNode* const oldPropp = assertp->propp();
            oldPropp->replaceWith(outputExprp);
            VL_DO_DANGLING(pushDeletep(oldPropp), oldPropp);
        }

        UINFO(4, "NFA converted assertion at " << flp << ", " << nfa.nodes.size() << " nodes, "
                                               << nfa.edges.size() << " edges" << endl);
    }

    // VISITORS
    void visit(AstNodeModule* nodep) override {
        VL_RESTORER(m_modp);
        VL_RESTORER(m_emitterp);
        m_modp = nodep;
        SvaNfaEmitter emitter{nodep};
        m_emitterp = &emitter;
        iterateChildren(nodep);
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
