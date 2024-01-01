// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Gate optimizations, such as wire elimination
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2024 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************
// V3Gate's Transformations:
//
// Extract a graph of the *entire* netlist with cells expanded
// Perform constant optimization across the graph
// Create VARSCOPEs for any variables we can rip out
//
//*************************************************************************

#include "V3PchAstNoMT.h"  // VL_MT_DISABLED_CODE_UNIT

#include "V3Gate.h"

#include "V3AstUserAllocator.h"
#include "V3Const.h"
#include "V3DupFinder.h"
#include "V3Graph.h"
#include "V3Stats.h"

#include <list>
#include <unordered_map>
#include <unordered_set>

VL_DEFINE_DEBUG_FUNCTIONS;

constexpr uint32_t GATE_DEDUP_MAX_DEPTH = 20;

//######################################################################
// Gate graph classes

class GateEitherVertex VL_NOT_FINAL : public V3GraphVertex {
    VL_RTTI_IMPL(GateEitherVertex, V3GraphVertex)
    bool m_reducible = true;  // True if this node should be able to be eliminated
    bool m_dedupable = true;  // True if this node should be able to be deduped
    bool m_consumed = false;  // Output goes to something meaningful
public:
    GateEitherVertex(V3Graph* graphp)
        : V3GraphVertex{graphp} {}
    ~GateEitherVertex() override = default;

    // ACCESSORS
    bool reducible() const { return m_reducible; }
    bool dedupable() const { return m_dedupable; }
    bool consumed() const { return m_consumed; }
    void setConsumed(const char* /*consumedReason*/) {
        // if (!m_consumed) UINFO(0, "\t\tSetConsumed " << consumedReason << " " << this << endl);
        m_consumed = true;
    }
    void clearReducible(const char* /*nonReducibleReason*/) {
        // UINFO(0, "     NR: " << nonReducibleReason << "  " << name() << endl);
        m_reducible = false;
    }
    void clearDedupable(const char* /*nonDedupableReason*/) {
        // UINFO(0, "     ND: " << nonDedupableReason << "  " << name() << endl);
        m_dedupable = false;
    }
    void clearReducibleAndDedupable(const char* nonReducibleReason) {
        clearReducible(nonReducibleReason);
        clearDedupable(nonReducibleReason);
    }

    // DOT debug
    std::string dotStyle() const override { return m_consumed ? "" : "dotted"; }
};

class GateVarVertex final : public GateEitherVertex {
    VL_RTTI_IMPL(GateVarVertex, GateEitherVertex)
    AstVarScope* const m_varScp;
    bool m_isTop = false;
    bool m_isClock = false;
    AstNode* m_rstSyncNodep = nullptr;  // Used as reset and not in SenItem, in clocked always
    AstNode* m_rstAsyncNodep = nullptr;  // Used as reset and in SenItem, in clocked always
public:
    GateVarVertex(V3Graph* graphp, AstVarScope* varScp)
        : GateEitherVertex{graphp}
        , m_varScp{varScp} {}
    ~GateVarVertex() override = default;

    // ACCESSORS
    AstVarScope* varScp() const VL_MT_STABLE { return m_varScp; }
    bool isTop() const { return m_isTop; }
    void setIsTop() { m_isTop = true; }
    bool isClock() const { return m_isClock; }
    void setIsClock() {
        m_isClock = true;
        setConsumed("isclk");
    }
    AstNode* rstSyncNodep() const { return m_rstSyncNodep; }
    void rstSyncNodep(AstNode* nodep) { m_rstSyncNodep = nodep; }
    AstNode* rstAsyncNodep() const { return m_rstAsyncNodep; }
    void rstAsyncNodep(AstNode* nodep) { m_rstAsyncNodep = nodep; }

    // METHODS
    void propagateAttrClocksFrom(GateVarVertex* fromp) {
        // Propagate clock and general attribute onto this node
        varScp()->varp()->propagateAttrFrom(fromp->varScp()->varp());
        if (fromp->isClock()) {
            varScp()->varp()->usedClock(true);
            setIsClock();
        }
    }

    // DOT debug
    std::string name() const override VL_MT_STABLE { return varScp()->name(); }
    std::string dotColor() const override { return "green"; }
};

class GateLogicVertex final : public GateEitherVertex {
    VL_RTTI_IMPL(GateLogicVertex, GateEitherVertex)
    AstNode* const m_nodep;
    AstActive* const m_activep;  // Under what active; nullptr is ok (under cfunc or such)
    const bool m_slow;  // In slow block
public:
    GateLogicVertex(V3Graph* graphp, AstNode* nodep, AstActive* activep, bool slow)
        : GateEitherVertex{graphp}
        , m_nodep{nodep}
        , m_activep{activep}
        , m_slow{slow} {}
    ~GateLogicVertex() override = default;

    // ACCESSORS
    FileLine* fileline() const override { return nodep()->fileline(); }
    AstNode* nodep() const { return m_nodep; }
    AstActive* activep() const { return m_activep; }
    bool slow() const { return m_slow; }

    // DOT debug
    std::string name() const override { return m_nodep->fileline()->ascii(); }
    std::string dotColor() const override { return "red"; }
};

class GateEdge final : public V3GraphEdge {
    std::string dotLabel() const override { return std::to_string(weight()); }

public:
    GateEdge(V3Graph* graphp, V3GraphVertex* fromp, V3GraphVertex* top, int weight)
        : V3GraphEdge{graphp, fromp, top, weight} {}
};

class GateGraph final : public V3Graph {
    // NODE STATE
    // AstVarScope::user1p      -> GateVarVertex* for usage var, 0=not set yet
    const VNUser1InUse m_inuser1;

public:
    GateVarVertex* makeVarVertex(AstVarScope* vscp) {
        GateVarVertex* vVtxp = reinterpret_cast<GateVarVertex*>(vscp->user1p());
        if (!vVtxp) {
            UINFO(6, "New vertex " << vscp << endl);
            vVtxp = new GateVarVertex{this, vscp};
            vscp->user1p(vVtxp);
            if (vscp->varp()->sensIfacep()) {
                // Can be used in a class method, which cannot be tracked statically
                vVtxp->clearReducibleAndDedupable("VirtIface");
                vVtxp->setConsumed("VirtIface");
            }
            if (vscp->varp()->isSigPublic()) {
                // Public signals shouldn't be changed, pli code might be messing with them
                vVtxp->clearReducibleAndDedupable("SigPublic");
                vVtxp->setConsumed("SigPublic");
            }
            if (vscp->varp()->isIO() && vscp->scopep()->isTop()) {
                // We may need to convert to/from sysc/reg sigs
                vVtxp->setIsTop();
                vVtxp->clearReducibleAndDedupable("isTop");
                vVtxp->setConsumed("isTop");
            }
            if (vscp->varp()->isUsedClock()) vVtxp->setConsumed("clock");
        }
        return vVtxp;
    }

    void addEdge(GateVarVertex* srcp, GateLogicVertex* dstp, int weight) {
        new GateEdge{this, srcp, dstp, weight};
    }

    void addEdge(GateLogicVertex* srcp, GateVarVertex* dstp, int weight) {
        new GateEdge{this, srcp, dstp, weight};
    }
};

//######################################################################
// GateGraph builder

class GateBuildVisitor final : public VNVisitorConst {
    // STATE
    GateGraph* m_graphp = new GateGraph{};  // The graph being built (var usages/dependencies)
    GateLogicVertex* m_logicVertexp = nullptr;  // Current statement being tracked, nullptr=ignored
    const AstNodeModule* m_modp = nullptr;  // Current module
    const AstScope* m_scopep = nullptr;  // Current scope being processed
    AstActive* m_activep = nullptr;  // Current active
    bool m_inClockedActive = false;  // Underneath clocked active
    bool m_inSenItem = false;  // Underneath AstSenItem; any varrefs are clocks

    // METHODS
    void checkNode(AstNode* nodep) {
        if (nodep->isOutputter()) m_logicVertexp->setConsumed("outputter");
        if (nodep->isTimingControl()) {
            m_logicVertexp->clearReducibleAndDedupable("TimingControl");
            m_logicVertexp->setConsumed("TimingControl");
        }
    }

    void iterateLogic(AstNode* nodep, bool slow = false, const char* nonReducibleReason = nullptr,
                      const char* consumeReason = nullptr) {
        UASSERT_OBJ(m_scopep, nodep, "Logic not under Scope");
        UASSERT_OBJ(!m_logicVertexp, nodep, "Logic blocks should not nest");
        VL_RESTORER(m_logicVertexp)

        // m_activep is null under AstCFunc's, that's ok.
        m_logicVertexp = new GateLogicVertex{m_graphp, nodep, m_activep, slow};
        if (nonReducibleReason) {
            m_logicVertexp->clearReducibleAndDedupable(nonReducibleReason);
        } else if (m_inClockedActive) {
            m_logicVertexp->clearReducible("Clocked logic");  // but dedupable
        }
        if (consumeReason) m_logicVertexp->setConsumed(consumeReason);
        checkNode(nodep);
        iterateChildrenConst(nodep);
    }

    // VISITORS
    void visit(AstNodeModule* nodep) override {
        UASSERT_OBJ(!m_modp, nodep, "Should not nest");
        VL_RESTORER(m_modp);
        m_modp = nodep;
        iterateChildrenConst(nodep);
    }
    void visit(AstScope* nodep) override {
        UASSERT_OBJ(!m_scopep, nodep, "Should not nest");
        VL_RESTORER(m_scopep);
        m_scopep = nodep;
        iterateChildrenConst(nodep);
    }
    void visit(AstActive* nodep) override {
        UASSERT_OBJ(!m_activep, nodep, "Should not nest");
        VL_RESTORER(m_activep);
        VL_RESTORER(m_inClockedActive);
        m_activep = nodep;
        m_inClockedActive = nodep->hasClocked();

        // AstVarScope::user2 -> bool: Signal used in SenItem in *this* active block
        const VNUser2InUse user2InUse;
        iterateChildrenConst(nodep);
    }

    void visit(AstAlwaysPublic* nodep) override { iterateLogic(nodep, true, "AlwaysPublic"); }
    void visit(AstCFunc* nodep) override {  //
        iterateLogic(nodep, nodep->slow(), "C Function", "C Function");
    }
    void visit(AstNodeProcedure* nodep) override {
        const bool slow = VN_IS(nodep, Initial) || VN_IS(nodep, Final);
        iterateLogic(nodep, slow, nodep->isJustOneBodyStmt() ? nullptr : "Multiple Stmts");
    }
    void visit(AstAssignAlias* nodep) override {  //
        iterateLogic(nodep);
    }
    void visit(AstAssignW* nodep) override {  //
        iterateLogic(nodep);
    }
    void visit(AstCoverToggle* nodep) override {
        iterateLogic(nodep, false, "CoverToggle", "CoverToggle");
    }
    void visit(AstSenItem* nodep) override {
        VL_RESTORER(m_inSenItem);
        m_inSenItem = true;
        if (m_logicVertexp) {  // Already under logic, e.g.: AstEventControl
            iterateChildrenConst(nodep);
        } else {  // Standalone item, under a SenTree or an Active
            iterateLogic(nodep, false, nullptr, "senItem");
        }
    }
    void visit(AstNodeVarRef* nodep) override {
        if (!m_logicVertexp) return;

        AstVarScope* const vscp = nodep->varScopep();
        GateVarVertex* const vVtxp = m_graphp->makeVarVertex(vscp);

        if (m_inSenItem) {
            vVtxp->setIsClock();
            vscp->user2(true);
        } else if (m_inClockedActive && nodep->access().isReadOnly()) {
            // For SYNCASYNCNET
            if (vscp->user2()) {
                if (!vVtxp->rstAsyncNodep()) vVtxp->rstAsyncNodep(nodep);
            } else {
                if (!vVtxp->rstSyncNodep()) vVtxp->rstSyncNodep(nodep);
            }
        }

        // We use weight of one; if we ref the var more than once, when we simplify,
        // the weight will increase
        if (nodep->access().isWriteOrRW()) m_graphp->addEdge(m_logicVertexp, vVtxp, 1);
        if (nodep->access().isReadOrRW()) m_graphp->addEdge(vVtxp, m_logicVertexp, 1);
    }
    void visit(AstConcat* nodep) override {
        UASSERT_OBJ(!(VN_IS(nodep->backp(), NodeAssign)
                      && VN_AS(nodep->backp(), NodeAssign)->lhsp() == nodep),
                    nodep, "Concat on LHS of assignment; V3Const should have deleted it");
        iterateChildrenConst(nodep);
    }

    //--------------------
    void visit(AstNode* nodep) override {
        if (m_logicVertexp) checkNode(nodep);
        iterateChildrenConst(nodep);
    }

    // CONSTRUCTORS
    explicit GateBuildVisitor(AstNetlist* nodep) { iterateChildrenConst(nodep); }

public:
    static std::unique_ptr<GateGraph> apply(AstNetlist* netlistp) {
        return std::unique_ptr<GateGraph>{GateBuildVisitor{netlistp}.m_graphp};
    }
};

//######################################################################
// SYCNASYNC warning

static void v3GateWarnSyncAsync(GateGraph& graph) {
    // AstVar::user2            -> bool: Warned about SYNCASYNCNET
    const VNUser2InUse user2InUse;
    for (V3GraphVertex* itp = graph.verticesBeginp(); itp; itp = itp->verticesNextp()) {
        if (const GateVarVertex* const vvertexp = itp->cast<GateVarVertex>()) {
            const AstVarScope* const vscp = vvertexp->varScp();
            const AstNode* const sp = vvertexp->rstSyncNodep();
            const AstNode* const ap = vvertexp->rstAsyncNodep();
            if (ap && sp && !vscp->varp()->user2()) {
                // This is somewhat wrong, as marking one flop as ok for sync
                // may mean a different flop now fails.  However it's a pain to
                // then report a warning in a new place - we should report them all at once.
                // Instead, we will disable if any disabled
                if (!vscp->fileline()->warnIsOff(V3ErrorCode::SYNCASYNCNET)
                    && !ap->fileline()->warnIsOff(V3ErrorCode::SYNCASYNCNET)
                    && !sp->fileline()->warnIsOff(V3ErrorCode::SYNCASYNCNET)) {
                    vscp->varp()->user2(true);  // Warn only once per signal
                    vscp->v3warn(SYNCASYNCNET,
                                 "Signal flopped as both synchronous and async: "
                                     << vscp->prettyNameQ() << '\n'
                                     << ap->warnOther() << "... Location of async usage\n"
                                     << ap->warnContextPrimary() << '\n'
                                     << sp->warnOther() << "... Location of sync usage\n"
                                     << sp->warnContextSecondary());
                }
            }
        }
    }
}

//######################################################################
// Find a var's offset in a concatenation (only used by GateClkDecomp)

class GateConcatVisitor final : public VNVisitorConst {
    // STATE
    const AstVarScope* m_vscp = nullptr;  // Varscope we're trying to find
    int m_offset = 0;  // Current offset of varscope
    int m_found_offset = 0;  // Found offset of varscope
    bool m_found = false;  // Offset found

    // VISITORS
    // TODO: This is broken, what if there is logic in between? {a, ~clk}
    void visit(AstNodeVarRef* nodep) override {
        if (nodep->varScopep() == m_vscp && !nodep->user2() && !m_found) {
            // A concatenation may use the same var multiple times
            // But the graph will initially have an edge per instance
            nodep->user2(true);
            m_found_offset = m_offset;
            m_found = true;
            UINFO(9, "CLK DECOMP Concat found var (off = " << m_offset << ") - " << nodep << endl);
        }
        m_offset += nodep->dtypep()->width();
    }
    void visit(AstConcat* nodep) override {
        iterateConst(nodep->rhsp());
        iterateConst(nodep->lhsp());
    }
    //--------------------
    void visit(AstNode* nodep) override { iterateChildrenConst(nodep); }

public:
    // PUBLIC METHODS
    bool concatOffset(AstConcat* concatp, AstVarScope* vscp, int& offsetr) {
        m_vscp = vscp;
        m_offset = 0;
        m_found = false;
        // Iterate
        iterateConst(concatp);
        offsetr = m_found_offset;
        return m_found;
    }
};

//######################################################################
// Recurse through the graph, looking for clock vectors to bypass

class GateClkDecomp final {
    // NODE STATE
    // AstVarScope::user2p      -> bool: already visited
    const VNUser2InUse m_inuser2;

    GateGraph& m_graph;  // The graph being processed
    bool m_clkVectors = false;  // A non-single-bit variable is involved in the path
    GateVarVertex* m_clkVtxp = nullptr;  // The canonical clock variable vertex
    GateConcatVisitor m_concatVisitor;

    // Statistics
    size_t m_seenClkVectors = 0;
    size_t m_decomposedClkVectors = 0;

    void visit(GateVarVertex* vVtxp, int offset) {
        AstVarScope* const vscp = vVtxp->varScp();

        // Can't propagate if this variable is forceable
        if (vscp->varp()->isForceable()) return;

        // Check that we haven't been here before
        if (vscp->user2SetOnce()) return;

        UINFO(9, "CLK DECOMP Var - " << vVtxp << " : " << vscp << endl);
        VL_RESTORER(m_clkVectors);
        if (vscp->varp()->width() > 1) {
            m_clkVectors = true;
            ++m_seenClkVectors;
        }

        for (V3GraphEdge *edgep = vVtxp->outBeginp(), *nextp; edgep; edgep = nextp) {
            // Need to find the next edge before visiting in case the edge is deleted
            nextp = edgep->outNextp();
            visit(edgep->top()->as<GateLogicVertex>(), offset, vscp);
        }

        vscp->user2(false);
    }

    void visit(GateLogicVertex* lVtxp, int offset, AstVarScope* lastVscp) {
        int clkOffset = offset;
        const AstAssignW* const assignp = VN_CAST(lVtxp->nodep(), AssignW);
        if (!assignp || assignp->timingControlp()) return;
        UASSERT_OBJ(lVtxp->outSize1(), assignp, "ASSIGNW Driving more than 1 LHS?");

        AstNodeExpr* const rhsp = assignp->rhsp();
        AstNodeExpr* const lhsp = assignp->lhsp();

        // RHS
        if (const AstSel* const rselp = VN_CAST(rhsp, Sel)) {
            if (VN_IS(rselp->lsbp(), Const) && VN_IS(rselp->widthp(), Const)) {
                if (clkOffset < rselp->lsbConst() || clkOffset > rselp->msbConst()) return;
                clkOffset -= rselp->lsbConst();
            } else {
                return;
            }
        } else if (AstConcat* const rcatp = VN_CAST(rhsp, Concat)) {
            int concat_offset;
            if (!m_concatVisitor.concatOffset(rcatp, lastVscp, concat_offset /*ref*/)) return;
            clkOffset += concat_offset;
        } else if (!VN_IS(rhsp, VarRef)) {
            return;
        }

        // LHS
        if (const AstSel* const lselp = VN_CAST(lhsp, Sel)) {
            if (VN_IS(lselp->lsbp(), Const) && VN_IS(lselp->widthp(), Const)) {
                clkOffset += lselp->lsbConst();
            } else {
                return;
            }
        } else if (const AstVarRef* const refp = VN_CAST(lhsp, VarRef)) {
            if (refp->dtypep()->width() == 1 && m_clkVectors) {
                UASSERT_OBJ(clkOffset == 0, assignp,
                            "Should only make it here with clkOffset == 0");
                rhsp->replaceWith(
                    new AstVarRef{rhsp->fileline(), m_clkVtxp->varScp(), VAccess::READ});
                while (V3GraphEdge* const edgep = lVtxp->inBeginp()) {
                    VL_DO_DANGLING(edgep->unlinkDelete(), edgep);
                }
                m_graph.addEdge(m_clkVtxp, lVtxp, 1);
                ++m_decomposedClkVectors;
            }
        } else {
            return;
        }

        visit(lVtxp->outBeginp()->top()->as<GateVarVertex>(), clkOffset);
    }

    explicit GateClkDecomp(GateGraph& graph)
        : m_graph{graph} {
        UINFO(9, "Starting clock decomposition" << endl);
        for (V3GraphVertex* itp = graph.verticesBeginp(); itp; itp = itp->verticesNextp()) {
            GateVarVertex* const vVtxp = itp->cast<GateVarVertex>();
            if (!vVtxp) continue;

            const AstVarScope* const vscp = vVtxp->varScp();
            if (vscp->varp()->attrClocker() != VVarAttrClocker::CLOCKER_YES) continue;

            if (vscp->varp()->width() == 1) {
                UINFO(9, "CLK DECOMP - " << vVtxp << " : " << vscp << endl);
                m_clkVtxp = vVtxp;
                visit(vVtxp, 0);
            }
        }
    }

    ~GateClkDecomp() {
        V3Stats::addStat("Optimizations, Clocker seen vectors", m_seenClkVectors);
        V3Stats::addStat("Optimizations, Clocker decomposed vectors", m_decomposedClkVectors);
    }

public:
    static void apply(GateGraph& graph) { GateClkDecomp{graph}; }
};

//######################################################################
// Is this a simple expression with a single input and single output?

class GateOkVisitor final : public VNVisitorConst {
    // RETURN STATE
    bool m_isSimple = true;  // Set false when we know it isn't simple
    std::vector<AstVarScope*> m_readVscps;  // Variables read by logic
    AstNodeExpr* m_substitutionp = nullptr;  // What to replace the variable with

    // STATE
    const bool m_dedupe;  // Set when we use isGateDedupable instead of isGateOptimizable

    // Set when we only allow simple buffering, no equations (for clocks)
    const bool m_buffersOnly;
    // VarRef on lhs of assignment (what we're replacing)
    const AstNodeVarRef* m_lhsVarRef = nullptr;
    int m_ops = 0;  // Operation count

    // METHODS
    void clearSimple(const char* because) {
        if (m_isSimple) UINFO(9, "Clear simple " << because << endl);
        m_isSimple = false;
    }

    static bool multiInputOptimizable(const AstVarScope* vscp) {
        return !vscp->varp()->isUsedClock();
    }

    // VISITORS
    void visit(AstNodeVarRef* nodep) override {
        if (!m_isSimple) return;

        ++m_ops;
        // Don't want to eliminate the VL_ASSIGN_S*
        if (nodep->varScopep()->varp()->isSc()) clearSimple("SystemC sig");

        if (nodep->access().isRW()) {
            clearSimple("R/W");
            return;
        }

        // We only allow a LHS ref for the var being set, and a RHS ref for
        // something else being read.
        if (nodep->access().isWriteOnly()) {
            if (m_lhsVarRef) clearSimple(">1 write refs");
            m_lhsVarRef = nodep;
        } else {
            AstVarScope* const vscp = nodep->varScopep();
            // TODO: possible bug, should it be >= 1 as add is below?
            if (m_readVscps.size() > 1) {
                const AstVarScope* const lastVscp = m_readVscps.back();
                if (m_buffersOnly) {
                    clearSimple(">1 rhs varRefs");
                } else if (!multiInputOptimizable(vscp) || !multiInputOptimizable(lastVscp)) {
                    clearSimple("!multiInputOptimizable");
                }
            }
            m_readVscps.push_back(vscp);
        }
    }
    void visit(AstNodeAssign* nodep) override {
        if (!m_isSimple) return;

        m_substitutionp = nodep->rhsp();
        if (!VN_IS(nodep->lhsp(), NodeVarRef)) {
            clearSimple("ASSIGN(non-VARREF)");
        } else if (nodep->isTimingControl()) {
            clearSimple("Timing control");
        } else {
            iterateChildrenConst(nodep);
        }
        // We don't push logic other than assignments/NOTs into SenItems
        // This avoids a mess in computing what exactly a POSEDGE is
        // V3Const cleans up any NOTs by flipping the edges for us
        if (m_buffersOnly
            && !(
                VN_IS(nodep->rhsp(), VarRef)
                // Avoid making non-clocked logic into clocked,
                // as it slows down the verilator_sim_benchmark
                || (VN_IS(nodep->rhsp(), Not) && VN_IS(VN_AS(nodep->rhsp(), Not)->lhsp(), VarRef)
                    && VN_AS(VN_AS(nodep->rhsp(), Not)->lhsp(), VarRef)->varp()->isUsedClock()))) {
            clearSimple("Not a buffer (goes to a clock)");
        }
    }
    //--------------------
    void visit(AstNode* nodep) override {
        if (!m_isSimple) return;  // Fastpath

        if (++m_ops > v3Global.opt.gateStmts()) {
            clearSimple("--gate-stmts exceeded");
            return;
        }

        if (!(m_dedupe ? nodep->isGateDedupable() : nodep->isGateOptimizable())  //
            || !nodep->isPure() || nodep->isBrancher()) {
            UINFO(5, "Non optimizable type: " << nodep << endl);
            clearSimple("Non optimizable type");
            return;
        }

        iterateChildrenConst(nodep);
    }

public:
    // CONSTRUCTORS
    GateOkVisitor(AstNode* nodep, bool buffersOnly, bool dedupe)
        : m_dedupe{dedupe}
        , m_buffersOnly{buffersOnly} {
        // Iterate
        iterateConst(nodep);
        // Check results
        if (!m_substitutionp) {
            clearSimple("No assignment found\n");
            return;
        }
        if (m_isSimple && m_lhsVarRef) {
            for (const AstVarScope* const vscp : m_readVscps) {
                if (m_lhsVarRef->varScopep() == vscp) {
                    clearSimple("Circular logic\n");
                    return;
                }
            }
        }
    }
    ~GateOkVisitor() override = default;
    // PUBLIC METHODS
    bool isSimple() const { return m_isSimple; }
    AstNodeExpr* substitutionp() const {
        UASSERT(m_isSimple, "Can't substitute non-simple");
        return m_substitutionp;
    }
    const std::vector<AstVarScope*>& readVscps() const { return m_readVscps; }
};

//######################################################################
// GateInline

class GateInline final {
    using Substitutions = std::unordered_map<AstVarScope*, AstNodeExpr*>;

    // NODE STATE
    // {logic}Node::user2       -> map of substitutions, via m_substitutions
    const VNUser2InUse m_inuser2;

    // Variable substitutions to apply to a given logic block
    AstUser2Allocator<AstNode, Substitutions> m_substitutions;

    // STATE
    GateGraph& m_graph;
    size_t m_ord = 0;  // Counter for sorting
    // Logic block with pending substitutions are stored in this map, together with their ordinal
    std::unordered_map<AstNode*, size_t> m_hasPending;
    size_t m_statInlined = 0;  // Statistic tracking - signals inlined
    size_t m_statRefs = 0;  // Statistic tracking

    // METHODS
    void recordSubstitution(AstVarScope* vscp, AstNodeExpr* substp, AstNode* logicp) {
        m_hasPending.emplace(logicp, ++m_ord);  // It's OK if already present
        m_substitutions(logicp).emplace(vscp, substp->cloneTreePure(false));
    }

    void commitSubstitutions(AstNode* logicp) {
        if (!m_hasPending.erase(logicp)) return;  // Had no pending substitutions

        Substitutions& substitutions = m_substitutions(logicp);
        UASSERT_OBJ(!substitutions.empty(), logicp, "No pending substitutions");

        // Recursion filter holding already replaced variables
        std::unordered_set<const AstVarScope*> replaced(substitutions.size() * 2);

        const std::function<void(AstNodeVarRef*)> visit = [&](AstNodeVarRef* nodep) -> void {
            // See if this variable has a substitution
            AstVarScope* const vscp = nodep->varScopep();
            const auto& it = substitutions.find(vscp);
            if (it == substitutions.end()) return;

            // Do not substitute circular logic
            if (!replaced.insert(vscp).second) return;

            // Substitute nodep with substp
            AstNodeExpr* const substp = it->second;

            UASSERT_OBJ(nodep->access().isReadOnly(), nodep, "Can't replace write references");
            UASSERT_OBJ(!VN_IS(substp, NodeVarRef) || !nodep->isSame(substp), substp,
                        "Replacing node with itself; perhaps circular logic?");
            // The replacement
            AstNodeExpr* const newp = substp->cloneTreePure(false);
            // Which fileline() to use? If replacing with logic, an error/warning is likely to want
            // to point to the logic IE what we're replacing with. However, a VARREF should point
            // to the original as it's otherwise confusing to throw warnings that point to a PIN
            // rather than where the pin us used.
            if (VN_IS(newp, VarRef)) newp->fileline(nodep->fileline());
            // Make the newp an rvalue like nodep.
            if (AstNodeVarRef* const varrefp = VN_CAST(newp, NodeVarRef)) {
                varrefp->access(VAccess::READ);
            }
            // Replace the node
            nodep->replaceWith(newp);
            VL_DO_DANGLING(nodep->deleteTree(), nodep);
            // Recursively substitute the new tree
            newp->foreach(visit);

            // Remove from recursion filter
            replaced.erase(vscp);
        };

        logicp->foreach(visit);

        AstNode* const simplifiedp = V3Const::constifyEdit(logicp);
        UASSERT_OBJ(simplifiedp == logicp, simplifiedp, "Should not remove whole logic");
        for (const auto& pair : substitutions) pair.second->deleteTree();
        substitutions.clear();
    }

    static GateVarVertex* ffToVarVtx(V3GraphVertex* vtxp) {
        while (vtxp && !vtxp->is<GateVarVertex>()) vtxp = vtxp->verticesNextp();
        return static_cast<GateVarVertex*>(vtxp);
    }

    void optimizeSignals(bool allowMultiIn) {
        // Consider "inlining" variables
        GateVarVertex* nextp = ffToVarVtx(m_graph.verticesBeginp());
        while (GateVarVertex* const vVtxp = nextp) {
            // vVtxp and it's driving logic might be deleted, so grab next up front
            nextp = ffToVarVtx(vVtxp->verticesNextp());

            // Nothing to inline if no driver, or multiple drivers ...
            if (!vVtxp->inSize1()) continue;

            // Can't inline if non-reducible, etc
            if (!vVtxp->reducible()) continue;

            // Grab the driving logic
            GateLogicVertex* const lVtxp = vVtxp->inBeginp()->fromp()->as<GateLogicVertex>();
            if (!lVtxp->reducible()) continue;
            AstNode* const logicp = lVtxp->nodep();

            // Commit pending optimizations to driving logic, as we will re-analyze
            commitSubstitutions(logicp);

            // Can we eliminate?
            const GateOkVisitor okVisitor{logicp, vVtxp->isClock(), false};

            // Was it ok?
            if (!okVisitor.isSimple()) continue;

            // Does it read multiple source variables?
            if (okVisitor.readVscps().size() > 1) {
                if (!allowMultiIn) {
                    continue;
                } else {
                    // Do it if not used, or used only once, ignoring slow code
                    int n = 0;
                    for (V3GraphEdge* ep = vVtxp->outBeginp(); ep; ep = ep->outNextp()) {
                        const GateLogicVertex* const dstVtxp = ep->top()->as<GateLogicVertex>();
                        // Ignore slow code, or if the destination is not used
                        if (!dstVtxp->slow() && dstVtxp->outBeginp()) n += ep->weight();
                        if (n > 1) break;
                    }
                    if (n > 1) continue;
                }
            }

            // Process it
            ++m_statInlined;

            AstVarScope* const vscp = vVtxp->varScp();
            AstNodeExpr* const substp = okVisitor.substitutionp();
            if (debug() >= 9) {
                vscp->dumpTree("substituting: ");
                substp->dumpTree("        with: ");
            }

            const auto& readVscpsVec = okVisitor.readVscps();
            const std::unordered_set<AstVarScope*> readVscps{readVscpsVec.begin(),
                                                             readVscpsVec.end()};

            for (V3GraphEdge *edgep = vVtxp->outBeginp(), *nextp; edgep; edgep = nextp) {
                // Edge might be deleted, so grab next
                nextp = edgep->outNextp();

                GateLogicVertex* const dstVtxp = edgep->top()->as<GateLogicVertex>();

                // If the consumer logic writes one of the variables that the substitution
                // is reading, then we would get a cycles, so we cannot do that.
                bool canInline = true;
                for (V3GraphEdge* edgep = dstVtxp->outBeginp(); edgep; edgep = edgep->outNextp()) {
                    const GateVarVertex* const consVVertexp = edgep->top()->as<GateVarVertex>();
                    if (readVscps.count(consVVertexp->varScp())) {
                        canInline = false;
                        break;
                    }
                }

                if (!canInline) continue;  // Cannot optimize this replacement

                if (debug() >= 9) dstVtxp->nodep()->dumpTree("      inside: ");

                recordSubstitution(vscp, substp, dstVtxp->nodep());

                // If the new replacement referred to a signal,
                // Correct the graph to point to this new generating variable
                for (AstVarScope* const newVscp : okVisitor.readVscps()) {
                    GateVarVertex* const varvertexp = m_graph.makeVarVertex(newVscp);
                    m_graph.addEdge(varvertexp, dstVtxp, 1);
                    // Propagate clock attribute onto generating node
                    varvertexp->propagateAttrClocksFrom(vVtxp);
                }

                // Remove the edge
                VL_DO_DANGLING(edgep->unlinkDelete(), edgep);
                ++m_statRefs;
            }

            // If removed all usage
            if (vVtxp->outEmpty()) {
                // Remove Variable vertex
                VL_DO_DANGLING(vVtxp->unlinkDelete(&m_graph), vVtxp);
                // Remove driving logic and vertex
                VL_DO_DANGLING(logicp->unlinkFrBack()->deleteTree(), logicp);
                VL_DO_DANGLING(lVtxp->unlinkDelete(&m_graph), lVtxp);
            }
        }
    }

    explicit GateInline(GateGraph& graph)
        : m_graph{graph} {
        // Find gate interconnect and optimize
        graph.userClearVertices();  // vertex->user(): bool. Indicates we've set it as consumed
        // Get rid of buffers first,
        optimizeSignals(false);
        // Then propagate more complicated equations
        optimizeSignals(true);
        // Commit substitutions in insertion order for stability
        using Pair = std::pair<AstNode*, size_t>;
        std::vector<Pair> pending{m_hasPending.begin(), m_hasPending.end()};
        std::sort(pending.begin(), pending.end(), [](const Pair& a, const Pair& b) {  //
            return a.second < b.second;
        });
        for (const auto& pair : pending) commitSubstitutions(pair.first);
    }

    ~GateInline() {
        V3Stats::addStat("Optimizations, Gate sigs deleted", m_statInlined);
        V3Stats::addStat("Optimizations, Gate inputs replaced", m_statRefs);
    }

public:
    static void apply(GateGraph& graph) { GateInline{graph}; }
};

//######################################################################
// Auxiliary hash class for GateDedupeVarVisitor

class GateDedupeHash final : public V3DupFinderUserSame {
    // NODE STATE
    // VNUser2InUse    m_inuser2;      (Allocated in GateDedupe)
    struct AuxAstNodeExpr final {
        // AstActive* of assign, for isSame() in test for duplicate. Set to nullptr if this
        // assign's tree was later replaced
        AstActive* activep = nullptr;
        // AstNodeExpr* of assign if condition, for isSame() in test for duplicate. Set to nullptr
        // if this assign's tree was later replaced
        AstNodeExpr* condp = nullptr;
        // Parent AstNodeAssign* for this rhsp
        AstNodeAssign* parentp = nullptr;
    };
    AstUser2Allocator<AstNodeExpr, AuxAstNodeExpr> m_auxNodeExpr;

    AstNodeExpr* m_currRhsp = nullptr;  // Current node we are searching for duplicates of
    AuxAstNodeExpr m_auxCurRhsp;  // Aux of current node

    V3DupFinder m_dupFinder;  // Duplicate finder for rhs of assigns

    bool same(AstNode* node1p, AstNode* node2p) {
        // Regarding the complexity of this function 'same':
        // Applying this comparison function to a a set of n trees pairwise is O(n^2) in the
        // number of comparisons (number of pairs). AstNode::sameTree itself, is O(sizeOfTree) in
        // the worst case, which happens if the operands of sameTree are indeed identical copies,
        // which means this line is O(n^2*sizeOfTree), iff you are comparing identical copies of
        // the same tree. In practice the identity comparison over the pointers, and the short
        // circuiting in sameTree means that for comparing the same tree instance to itself, or
        // trees of different types/shapes is a lot closer to O(1), so this 'same' function is
        // Omega(n^2) and O(n^2*sizeOfTree), and in practice as we are mostly comparing the same
        // instance to itself or different trees, the complexity should be closer to the lower
        // bound.
        //
        // Also if you see where this 'same' function is used within isSame, it's only ever
        // comparing AstActive nodes, which are very likely not to compare equals (and for the
        // purposes of V3Gate, we probably only care about them either being identical instances,
        // or having the same sensitivities anyway, so if this becomes a problem, it can be
        // improved which should also speed things up), and AstNodeExpr for if conditions, which
        // are hopefully small.
        return node1p == node2p || (node1p && node1p->sameTree(node2p));
    }

    // Callback from V3DupFinder::findDuplicate
    bool isSame(AstNode* node1p, AstNode* node2p) override {
        UASSERT_OBJ(node1p == m_currRhsp, m_currRhsp, "Comparing to unexpected node");
        const auto& aux2 = m_auxNodeExpr(VN_AS(node2p, NodeExpr));
        return m_auxCurRhsp.parentp->type() == aux2.parentp->type()  //
               && same(m_auxCurRhsp.activep, aux2.activep)  //
               && same(m_auxCurRhsp.condp, aux2.condp);
    }

public:
    GateDedupeHash() = default;
    ~GateDedupeHash() = default;

    const AstNodeAssign* hashAndFindDupe(AstNodeAssign* assignp, AstActive* activep,
                                         AstNodeExpr* condp) {
        // Legal for activep to be nullptr, we'll compare with other assigns with also nullptr
        m_currRhsp = assignp->rhsp();
        m_auxCurRhsp.activep = activep;
        m_auxCurRhsp.condp = condp;
        m_auxCurRhsp.parentp = assignp;

        // Check for a duplicate, if found return its assignment
        const auto it = m_dupFinder.findDuplicate(m_currRhsp, this);
        if (it != m_dupFinder.end()) return m_auxNodeExpr(VN_AS(it->second, NodeExpr)).parentp;

        // Insert new node
        m_dupFinder.insert(m_currRhsp);
        m_auxNodeExpr(m_currRhsp) = m_auxCurRhsp;
        return nullptr;
    }
};

//######################################################################
// Have we seen the rhs of this assign before?

class GateDedupeVarVisitor final : public VNVisitorConst {
    // Given a node, it is visited to try to find the AstNodeAssign under
    // it that can used for dedupe.
    // Right now, only the following node trees are supported for dedupe.
    // 1. AstNodeAssign
    // 2. AstAlways -> AstNodeAssign
    //   (Note, the assign must also be the only node under the always)
    // 3. AstAlways -> AstNodeIf -> AstNodeAssign
    //   (Note, the IF must be the only node under the always,
    //    and the assign must be the only node under the if, other than the ifcond)
    // Any other ordering or node type, except for an AstComment, makes it not dedupable
    // AstExprStmt in the subtree of a node also makes the node not dedupable.

    // STATE
    GateDedupeHash m_ghash;  // Hash used to find dupes of rhs of assign
    AstNodeAssign* m_assignp = nullptr;  // Assign found for dedupe
    AstNodeExpr* m_ifCondp = nullptr;  // IF condition that assign is under
    bool m_always = false;  // Assign is under an always
    bool m_dedupable = true;  // Determined the assign to be dedupable

    // VISITORS
    void visit(AstNodeAssign* nodep) override {
        if (!m_dedupable) return;

        // I think we could safely dedupe an always block with multiple
        // non-blocking statements, but erring on side of caution here
        if (!m_assignp) {
            m_assignp = nodep;
            m_dedupable = !nodep->exists([](AstExprStmt*) { return true; });
            return;
        }

        m_dedupable = false;
    }

    void visit(AstAlways* nodep) override {
        if (!m_dedupable) return;

        if (!m_always) {
            m_always = true;
            iterateAndNextConstNull(nodep->stmtsp());
            return;
        }

        m_dedupable = false;
    }

    // Ugly support for latches of the specific form -
    //  always @(...)
    //    if (...)
    //       foo = ...; // or foo <= ...;
    void visit(AstNodeIf* nodep) override {
        if (!m_dedupable) return;

        if (m_always && !m_ifCondp && !nodep->elsesp()) {
            // we're under an always, this is the first IF, and there's no else
            m_ifCondp = nodep->condp();
            m_dedupable = !m_ifCondp->exists([](AstExprStmt*) { return true; });
            iterateAndNextConstNull(nodep->thensp());
            return;
        }

        m_dedupable = false;
    }

    void visit(AstComment*) override {}  // NOP
    //--------------------
    void visit(AstNode*) override { m_dedupable = false; }

public:
    // CONSTRUCTORS
    GateDedupeVarVisitor() = default;
    ~GateDedupeVarVisitor() override = default;
    // PUBLIC METHODS
    AstNodeVarRef* findDupe(AstNode* logicp, AstVarScope* consumerVscp, AstActive* activep) {
        m_assignp = nullptr;
        m_ifCondp = nullptr;
        m_always = false;
        m_dedupable = true;
        iterateConst(logicp);
        if (m_dedupable && m_assignp) {
            const AstNode* const lhsp = m_assignp->lhsp();
            // Possible todo, handle more complex lhs expressions
            if (const AstNodeVarRef* const lRefp = VN_CAST(lhsp, NodeVarRef)) {
                UASSERT_OBJ(lRefp->varScopep() == consumerVscp, consumerVscp,
                            "Consumer doesn't match lhs of assign");
                if (const AstNodeAssign* const dup
                    = m_ghash.hashAndFindDupe(m_assignp, activep, m_ifCondp)) {
                    return static_cast<AstNodeVarRef*>(dup->lhsp());
                }
            }
        }
        return nullptr;
    }
};

//######################################################################
// Recurse through the graph, looking for duplicate expressions on the rhs of an assign

class GateDedupe final {
    // NODE STATE
    // AstVarScope::user2p      -> bool: already visited
    const VNUser2InUse m_inuser2;

    // STATE
    size_t m_statDedupLogic = 0;  // Statistic tracking
    GateDedupeVarVisitor m_varVisitor;  // Looks for a dupe of the logic
    uint32_t m_depth = 0;  // Iteration depth

    void visit(GateVarVertex* vVtxp) {
        // Break loops; before user2 set so hit this vertex later
        if (m_depth > GATE_DEDUP_MAX_DEPTH) return;

        // Check that we haven't been here before
        if (vVtxp->varScp()->user2SetOnce()) return;

        VL_RESTORER(m_depth);
        ++m_depth;
        if (!vVtxp->inSize1()) return;

        AstNodeVarRef* dupRefp = nullptr;
        for (V3GraphEdge* edgep = vVtxp->inBeginp(); edgep; edgep = edgep->inNextp()) {
            dupRefp = visit(edgep->fromp()->as<GateLogicVertex>(), vVtxp);
        }
        if (!dupRefp) return;

        UASSERT_OBJ(vVtxp->dedupable(), vVtxp->varScp(),
                    "GateLogicVertex* visit should have returned nullptr "
                    "if consumer var vertex is not dedupable.");

        GateLogicVertex* const lVtxp = vVtxp->inBeginp()->fromp()->as<GateLogicVertex>();
        const GateOkVisitor okVisitor{lVtxp->nodep(), false, true};
        if (!okVisitor.isSimple()) return;

        ++m_statDedupLogic;
        GateVarVertex* const dupVVtxp = dupRefp->varScopep()->user1u().to<GateVarVertex*>();
        UINFO(4, "replacing " << vVtxp << " with " << dupVVtxp << endl);

        // Replace all of this varvertex's consumers with dupRefp
        for (V3GraphEdge *edgep = vVtxp->outBeginp(), *nextp; edgep; edgep = nextp) {
            nextp = edgep->outNextp();
            const GateLogicVertex* const consumerVtxp = edgep->top()->as<GateLogicVertex>();
            AstNode* const consumerp = consumerVtxp->nodep();
            UINFO(9, "elim src vtx" << lVtxp << " node " << lVtxp->nodep() << endl);
            UINFO(9, "elim cons vtx" << consumerVtxp << " node " << consumerp << endl);
            UINFO(9, "elim var vtx " << vVtxp << " node " << vVtxp->varScp() << endl);
            UINFO(9, "replace with " << dupRefp << endl);
            if (lVtxp == consumerVtxp) {
                UINFO(9, "skipping as self-recirculates\n");
            } else {
                // Substitute consumer logic
                consumerp->foreach([&](AstNodeVarRef* refp) {
                    if (refp->varScopep() != vVtxp->varScp()) return;

                    UASSERT_OBJ(refp->access().isReadOnly(), refp, "Can't replace a write ref");

                    // The replacement
                    AstNodeVarRef* const newp = dupRefp->cloneTreePure(false);
                    // A VARREF should point to the original as it's otherwise confusing to throw
                    // warnings that point to a PIN rather than where the pin is used.
                    newp->fileline(refp->fileline());
                    newp->access(VAccess::READ);

                    // Replace the node
                    refp->replaceWith(newp);
                    VL_DO_DANGLING(refp->deleteTree(), refp);
                });
            }
            edgep->relinkFromp(dupVVtxp);
        }

        // Remove inputs links
        while (V3GraphEdge* const edgep = vVtxp->inBeginp()) {
            VL_DO_DANGLING(edgep->unlinkDelete(), edgep);
        }

        // Propagate attributes
        dupVVtxp->propagateAttrClocksFrom(vVtxp);
    }

    // Given iterated logic, starting at consumerVtxp, returns a varref that
    // has the same logic input, or nullptr if none
    AstNodeVarRef* visit(GateLogicVertex* lVtxp, const GateVarVertex* consumerVtxp) {
        for (V3GraphEdge* edgep = lVtxp->inBeginp(); edgep; edgep = edgep->inNextp()) {
            visit(edgep->fromp()->as<GateVarVertex>());
        }

        if (lVtxp->dedupable() && consumerVtxp->dedupable()) {
            // TODO: Doing a simple pointer comparison of activep won't work
            // optimally for statements under generated clocks. Statements under
            // different generated clocks will never compare as equal, even if the
            // generated clocks are deduped into one clock.
            return m_varVisitor.findDupe(lVtxp->nodep(), consumerVtxp->varScp(), lVtxp->activep());
        }
        return nullptr;
    }

    explicit GateDedupe(GateGraph& graph) {
        // Traverse starting from each of the clocks
        UINFO(9, "Gate dedupe() clocks:\n");
        for (V3GraphVertex* itp = graph.verticesBeginp(); itp; itp = itp->verticesNextp()) {
            if (GateVarVertex* const vVtxp = itp->cast<GateVarVertex>()) {
                if (vVtxp->isClock()) visit(vVtxp);
            }
        }
        // Traverse starting from each of the outputs
        UINFO(9, "Gate dedupe() outputs:\n");
        for (V3GraphVertex* itp = graph.verticesBeginp(); itp; itp = itp->verticesNextp()) {
            if (GateVarVertex* const vVtxp = itp->cast<GateVarVertex>()) {
                if (vVtxp->isTop() && vVtxp->varScp()->varp()->isWritable()) visit(vVtxp);
            }
        }
    }

    ~GateDedupe() { V3Stats::addStat("Optimizations, Gate sigs deduped", m_statDedupLogic); }

public:
    static void apply(GateGraph& graph) { GateDedupe{graph}; }
};

//######################################################################
// Recurse through the graph, try to merge assigns

class GateMergeAssignments final {
    GateGraph& m_graph;
    size_t m_statAssignMerged = 0;  // Statistic tracking

    // assemble two Sel into one if possible
    AstSel* merge(AstSel* prevSelp, AstSel* currSelp) {
        const AstVarRef* const pRefp = VN_CAST(prevSelp->fromp(), VarRef);
        AstVarRef* const cRefp = VN_CAST(currSelp->fromp(), VarRef);
        if (!pRefp || !cRefp || !cRefp->same(pRefp)) return nullptr;  // not the same var

        const AstConst* const pstart = VN_CAST(prevSelp->lsbp(), Const);
        const AstConst* const pwidth = VN_CAST(prevSelp->widthp(), Const);
        const AstConst* const cstart = VN_CAST(currSelp->lsbp(), Const);
        const AstConst* const cwidth = VN_CAST(currSelp->widthp(), Const);
        if (!pstart || !pwidth || !cstart || !cwidth) return nullptr;  // too complicated

        if (currSelp->msbConst() + 1 == prevSelp->lsbConst()) {
            return new AstSel{cRefp->fileline(), cRefp->cloneTree(false), currSelp->lsbConst(),
                              prevSelp->widthConst() + currSelp->widthConst()};
        } else {
            return nullptr;
        }
    }

    void process(GateVarVertex* vVtxp) {
        GateLogicVertex* prevLVtxp = nullptr;
        AstNodeAssign* prevAssignp = nullptr;

        for (V3GraphEdge *edgep = vVtxp->inBeginp(), *nextp; edgep; edgep = nextp) {
            nextp = edgep->inNextp();  // fThe edge could be deleted

            GateLogicVertex* const lVtxp = edgep->fromp()->as<GateLogicVertex>();
            if (!lVtxp->outSize1()) continue;

            AstNodeAssign* const assignp = VN_CAST(lVtxp->nodep(), NodeAssign);
            if (!assignp) continue;

            if (!VN_IS(assignp->lhsp(), Sel)) continue;

            // First assign with Sel-lhs, or not under the same active
            if (!prevLVtxp || prevLVtxp->activep() != lVtxp->activep()) {
                prevLVtxp = lVtxp;
                prevAssignp = assignp;
                continue;
            }

            UASSERT_OBJ(prevAssignp->type() == assignp->type(), assignp, "Mismatched types");

            AstSel* const prevSelp = VN_AS(prevAssignp->lhsp(), Sel);
            AstSel* const currSelp = VN_AS(assignp->lhsp(), Sel);

            if (AstSel* const newSelp = merge(prevSelp, currSelp)) {
                UINFO(5, "assemble to new sel: " << newSelp << endl);
                // replace preSel with newSel
                prevSelp->replaceWith(newSelp);
                VL_DO_DANGLING(prevSelp->deleteTree(), prevSelp);
                // create new rhs for pre assignment
                AstNode* const newRhsp = new AstConcat{prevAssignp->rhsp()->fileline(),
                                                       prevAssignp->rhsp()->cloneTreePure(false),
                                                       assignp->rhsp()->cloneTreePure(false)};
                AstNode* const prevRhsp = prevAssignp->rhsp();
                prevRhsp->replaceWith(newRhsp);
                VL_DO_DANGLING(prevRhsp->deleteTree(), prevRhsp);
                // Why do we care about the type of an assignment?
                prevAssignp->dtypeChgWidthSigned(prevAssignp->width() + assignp->width(),
                                                 prevAssignp->width() + assignp->width(),
                                                 VSigning::SIGNED);
                // Don't need to delete assignp, will be handled

                // Update the graph
                while (V3GraphEdge* const iedgep = lVtxp->inBeginp()) {
                    GateVarVertex* const fromVtxp = iedgep->fromp()->as<GateVarVertex>();
                    m_graph.addEdge(fromVtxp, prevLVtxp, 1);
                    VL_DO_DANGLING(iedgep->unlinkDelete(), iedgep);
                }

                // Delete the out-edges of lVtxp (there is only one, we checked earlier)
                VL_DO_DANGLING(edgep->unlinkDelete(), edgep);

                ++m_statAssignMerged;
            } else {
                prevLVtxp = lVtxp;
                prevAssignp = assignp;
            }
        }
    }

    explicit GateMergeAssignments(GateGraph& graph)
        : m_graph{graph} {
        UINFO(6, "mergeAssigns\n");
        for (V3GraphVertex* itp = graph.verticesBeginp(); itp; itp = itp->verticesNextp()) {
            if (GateVarVertex* const vVtxp = itp->cast<GateVarVertex>()) process(vVtxp);
        }
    }

    ~GateMergeAssignments() {
        V3Stats::addStat("Optimizations, Gate assign merged", m_statAssignMerged);
    }

public:
    static void apply(GateGraph& graph) { GateMergeAssignments{graph}; }
};

//######################################################################
// GateUnused

class GateUnused final {
    // STATE
    GateGraph& m_graph;

    // METHODS

    void markRecurse(GateEitherVertex* vtxp) {
        if (vtxp->user()) return;  // Already marked
        vtxp->user(true);
        vtxp->setConsumed("propagated");
        // Walk sources and mark them too
        for (V3GraphEdge* edgep = vtxp->inBeginp(); edgep; edgep = edgep->inNextp()) {
            GateEitherVertex* const fromVtxp = static_cast<GateEitherVertex*>(edgep->fromp());
            markRecurse(fromVtxp);
        }
    }

    // Mark all vertices that feed a consumed vertex
    void mark() {
        m_graph.userClearVertices();
        for (V3GraphVertex* vtxp = m_graph.verticesBeginp(); vtxp; vtxp = vtxp->verticesNextp()) {
            GateEitherVertex* const eVtxp = static_cast<GateEitherVertex*>(vtxp);
            if (eVtxp->consumed()) markRecurse(eVtxp);
        }
    }

    // Remove unused logic
    void remove() {
        for (V3GraphVertex *vtxp = m_graph.verticesBeginp(), *nextp; vtxp; vtxp = nextp) {
            nextp = vtxp->verticesNextp();
            if (GateLogicVertex* const lVtxp = vtxp->cast<GateLogicVertex>()) {
                if (!lVtxp->consumed() && lVtxp->activep()) {  // activep is nullptr under cfunc
                    AstNode* const nodep = lVtxp->nodep();
                    UINFO(8, "    Remove unconsumed " << nodep << endl);
                    nodep->unlinkFrBack();
                    VL_DO_DANGLING(nodep->deleteTree(), nodep);
                    lVtxp->unlinkDelete(&m_graph);
                }
            }
        }
    }

    GateUnused(GateGraph& graph)
        : m_graph{graph} {
        mark();  // Mark all used vertices
        remove();  // Remove unused vertices
    }

public:
    static void apply(GateGraph& graph) { GateUnused{graph}; }
};

//######################################################################
// Pass entry point

void V3Gate::gateAll(AstNetlist* netlistp) {
    UINFO(2, __FUNCTION__ << ": " << endl);

    {
        // Build the graph
        std::unique_ptr<GateGraph> graphp = GateBuildVisitor::apply(netlistp);
        if (dumpGraphLevel() >= 3) graphp->dumpDotFilePrefixed("gate_graph");

        // Warn, before loss of sync/async pointers
        v3GateWarnSyncAsync(*graphp);

        // Decompose clock vectors -- need to do this before removing redundant edges
        GateClkDecomp::apply(*graphp);
        if (dumpGraphLevel() >= 6) graphp->dumpDotFilePrefixed("gate_decomp");

        // Remove redundant edges. Edge weighs are added, so a variable read twice by
        // the same logic block will have and edge to the logic block with weight 2
        graphp->removeRedundantEdgesSum(&V3GraphEdge::followAlwaysTrue);
        if (dumpGraphLevel() >= 6) graphp->dumpDotFilePrefixed("gate_simp");

        // Inline variables
        GateInline::apply(*graphp);
        if (dumpGraphLevel() >= 6) graphp->dumpDotFilePrefixed("gate_inline");

        // Remove redundant logic
        if (v3Global.opt.fDedupe()) {
            GateDedupe::apply(*graphp);
            if (dumpGraphLevel() >= 6) graphp->dumpDotFilePrefixed("gate_dedup");
        }

        // Merge assignments
        if (v3Global.opt.fAssemble()) {
            GateMergeAssignments::apply(*graphp);
            if (dumpGraphLevel() >= 6) graphp->dumpDotFilePrefixed("gate_merge");
        }

        // Remove unused logic
        GateUnused::apply(*graphp);
        if (dumpGraphLevel() >= 3) graphp->dumpDotFilePrefixed("gate_final");
    }

    V3Global::dumpCheckGlobalTree("gate", 0, dumpTreeLevel() >= 3);
}
