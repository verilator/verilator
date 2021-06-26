// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Gate optimizations, such as wire elimination
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2021 by Wilson Snyder. This program is free software; you
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

#include "config_build.h"
#include "verilatedos.h"

#include "V3Global.h"
#include "V3Gate.h"
#include "V3Ast.h"
#include "V3Graph.h"
#include "V3Const.h"
#include "V3Stats.h"
#include "V3DupFinder.h"

#include <algorithm>
#include <list>
#include <map>
#include <unordered_set>

using GateVarRefList = std::list<AstNodeVarRef*>;

constexpr int GATE_DEDUP_MAX_DEPTH = 20;

//######################################################################

class GateBaseVisitor VL_NOT_FINAL : public AstNVisitor {
public:
    VL_DEBUG_FUNC;  // Declare debug()
};

//######################################################################

class GateLogicVertex;
class GateVarVertex;
class GateGraphBaseVisitor VL_NOT_FINAL {
public:
    V3Graph* m_graphp;  // Graph this class is visiting
    explicit GateGraphBaseVisitor(V3Graph* graphp)
        : m_graphp{graphp} {}
    virtual ~GateGraphBaseVisitor() = default;
    virtual VNUser visit(GateLogicVertex* vertexp, VNUser vu = VNUser(0)) = 0;
    virtual VNUser visit(GateVarVertex* vertexp, VNUser vu = VNUser(0)) = 0;
    VL_DEBUG_FUNC;  // Declare debug()
};

//######################################################################
// Support classes

class GateEitherVertex VL_NOT_FINAL : public V3GraphVertex {
    AstScope* m_scopep;  // Scope vertex refers to
    bool m_reducible = true;  // True if this node should be able to be eliminated
    bool m_dedupable = true;  // True if this node should be able to be deduped
    bool m_consumed = false;  // Output goes to something meaningful
public:
    GateEitherVertex(V3Graph* graphp, AstScope* scopep)
        : V3GraphVertex{graphp}
        , m_scopep{scopep} {}
    virtual ~GateEitherVertex() override = default;
    // ACCESSORS
    virtual string dotStyle() const override { return m_consumed ? "" : "dotted"; }
    AstScope* scopep() const { return m_scopep; }
    bool reducible() const { return m_reducible; }
    bool dedupable() const { return m_dedupable; }
    void setConsumed(const char* consumedReason) {
        m_consumed = true;
        // UINFO(0, "\t\tSetConsumed "<<consumedReason<<" "<<this<<endl);
    }
    bool consumed() const { return m_consumed; }
    void clearReducible(const char* nonReducibleReason) {
        m_reducible = false;
        // UINFO(0, "     NR: "<<nonReducibleReason<<"  "<<name()<<endl);
    }
    void clearDedupable(const char* nonDedupableReason) {
        m_dedupable = false;
        // UINFO(0, "     ND: "<<nonDedupableReason<<"  "<<name()<<endl);
    }
    void clearReducibleAndDedupable(const char* nonReducibleReason) {
        clearReducible(nonReducibleReason);
        clearDedupable(nonReducibleReason);
    }
    virtual VNUser accept(GateGraphBaseVisitor& v, VNUser vu = VNUser(0)) = 0;
    // Returns only the result from the LAST vertex iterated over
    VNUser iterateInEdges(GateGraphBaseVisitor& v, VNUser vu = VNUser(0)) {
        VNUser ret = VNUser(0);
        for (V3GraphEdge* edgep = inBeginp(); edgep; edgep = edgep->inNextp()) {
            ret = dynamic_cast<GateEitherVertex*>(edgep->fromp())->accept(v, vu);
        }
        return ret;
    }
    // Returns only the result from the LAST vertex iterated over
    // Note: This behaves differently than iterateInEdges() in that it will traverse
    //          all edges that exist when it is initially called, whereas
    //          iterateInEdges() will stop traversing edges if one is deleted
    VNUser iterateCurrentOutEdges(GateGraphBaseVisitor& v, VNUser vu = VNUser(0)) {
        VNUser ret = VNUser(0);
        V3GraphEdge* next_edgep = nullptr;
        for (V3GraphEdge* edgep = outBeginp(); edgep; edgep = next_edgep) {
            // Need to find the next edge before visiting in case the edge is deleted
            next_edgep = edgep->outNextp();
            ret = dynamic_cast<GateEitherVertex*>(edgep->top())->accept(v, vu);
        }
        return ret;
    }
};

class GateVarVertex final : public GateEitherVertex {
    AstVarScope* m_varScp;
    bool m_isTop = false;
    bool m_isClock = false;
    AstNode* m_rstSyncNodep = nullptr;  // Used as reset and not in SenItem, in clocked always
    AstNode* m_rstAsyncNodep = nullptr;  // Used as reset and in SenItem, in clocked always
public:
    GateVarVertex(V3Graph* graphp, AstScope* scopep, AstVarScope* varScp)
        : GateEitherVertex{graphp, scopep}
        , m_varScp{varScp} {}
    virtual ~GateVarVertex() override = default;
    // ACCESSORS
    AstVarScope* varScp() const { return m_varScp; }
    virtual string name() const override { return (cvtToHex(m_varScp) + " " + varScp()->name()); }
    virtual string dotColor() const override { return "blue"; }
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
    virtual VNUser accept(GateGraphBaseVisitor& v, VNUser vu = VNUser(0)) override {
        return v.visit(this, vu);
    }
};

class GateLogicVertex final : public GateEitherVertex {
    AstNode* m_nodep;
    AstActive* m_activep;  // Under what active; nullptr is ok (under cfunc or such)
    bool m_slow;  // In slow block
public:
    GateLogicVertex(V3Graph* graphp, AstScope* scopep, AstNode* nodep, AstActive* activep,
                    bool slow)
        : GateEitherVertex{graphp, scopep}
        , m_nodep{nodep}
        , m_activep{activep}
        , m_slow{slow} {}
    virtual ~GateLogicVertex() override = default;
    // ACCESSORS
    virtual string name() const override {
        return (cvtToHex(m_nodep) + "@" + scopep()->prettyName());
    }
    virtual string dotColor() const override { return "purple"; }
    virtual FileLine* fileline() const override { return nodep()->fileline(); }
    AstNode* nodep() const { return m_nodep; }
    AstActive* activep() const { return m_activep; }
    bool slow() const { return m_slow; }
    virtual VNUser accept(GateGraphBaseVisitor& v, VNUser vu = VNUser(0)) override {
        return v.visit(this, vu);
    }
};

//######################################################################
// Is this a simple math expression with a single input and single output?

class GateOkVisitor final : public GateBaseVisitor {
private:
    // RETURN STATE
    bool m_isSimple = true;  // Set false when we know it isn't simple
    GateVarRefList m_rhsVarRefs;  // VarRefs on rhs of assignment
    AstNode* m_substTreep = nullptr;  // What to replace the variable with
    // STATE
    bool m_buffersOnly;  // Set when we only allow simple buffering, no equations (for clocks)
    AstNodeVarRef* m_lhsVarRef = nullptr;  // VarRef on lhs of assignment (what we're replacing)
    bool m_dedupe;  // Set when we use isGateDedupable instead of isGateOptimizable
    int m_ops = 0;  // Operation count

    // METHODS
    void clearSimple(const char* because) {
        if (m_isSimple) {
            m_isSimple = false;
            UINFO(9, "Clear simple " << because << endl);
        }
    }
    // VISITORS
    virtual void visit(AstNodeVarRef* nodep) override {
        ++m_ops;
        iterateChildren(nodep);
        // We only allow a LHS ref for the var being set, and a RHS ref for
        // something else being read.
        if (nodep->varScopep()->varp()->isSc()) {
            clearSimple("SystemC sig");  // Don't want to eliminate the VL_ASSIGN_SI's
        }
        if (nodep->access().isRW()) {
            clearSimple("R/W");
        } else if (nodep->access().isWriteOrRW()) {
            if (m_lhsVarRef) clearSimple(">1 lhs varRefs");
            m_lhsVarRef = nodep;
        } else {
            if (m_rhsVarRefs.size() > 1) {
                AstNodeVarRef* lastRefp = m_rhsVarRefs.back();
                if (m_buffersOnly) clearSimple(">1 rhs varRefs");
                if (!nodep->varScopep()->varp()->gateMultiInputOptimizable()
                    // We didn't check multiInput on the first varref, so check it here
                    || !lastRefp->varScopep()->varp()->gateMultiInputOptimizable()) {
                    clearSimple("!gateMultiInputOptimizable");
                }
            }
            m_rhsVarRefs.push_back(nodep);
        }
    }
    virtual void visit(AstNodeAssign* nodep) override {
        m_substTreep = nodep->rhsp();
        if (!VN_IS(nodep->lhsp(), NodeVarRef)) {
            clearSimple("ASSIGN(non-VARREF)");
        } else {
            iterateChildren(nodep);
        }
        // We don't push logic other then assignments/NOTs into SenItems
        // This avoids a mess in computing what exactly a POSEDGE is
        // V3Const cleans up any NOTs by flipping the edges for us
        if (m_buffersOnly
            && !(VN_IS(nodep->rhsp(), VarRef)
                 // Avoid making non-clocked logic into clocked,
                 // as it slows down the verilator_sim_benchmark
                 || (VN_IS(nodep->rhsp(), Not)
                     && VN_IS(VN_CAST(nodep->rhsp(), Not)->lhsp(), VarRef)
                     && VN_CAST(VN_CAST(nodep->rhsp(), Not)->lhsp(), VarRef)
                            ->varp()
                            ->isUsedClock()))) {
            clearSimple("Not a buffer (goes to a clock)");
        }
    }
    //--------------------
    virtual void visit(AstNode* nodep) override {
        // *** Special iterator
        if (!m_isSimple) return;  // Fastpath
        if (++m_ops > v3Global.opt.gateStmts()) clearSimple("--gate-stmts exceeded");
        if (!(m_dedupe ? nodep->isGateDedupable() : nodep->isGateOptimizable())  //
            || !nodep->isPure() || nodep->isBrancher()) {
            UINFO(5, "Non optimizable type: " << nodep << endl);
            clearSimple("Non optimizable type");
        } else {
            iterateChildren(nodep);
        }
    }

public:
    // CONSTRUCTORS
    GateOkVisitor(AstNode* nodep, bool buffersOnly, bool dedupe) {
        m_buffersOnly = buffersOnly;
        m_dedupe = dedupe;
        // Iterate
        iterate(nodep);
        // Check results
        if (!m_substTreep) clearSimple("No assignment found\n");
        for (GateVarRefList::const_iterator it = m_rhsVarRefs.begin(); it != m_rhsVarRefs.end();
             ++it) {
            if (m_lhsVarRef && m_lhsVarRef->varScopep() == (*it)->varScopep()) {
                clearSimple("Circular logic\n");  // Oh my, we'll get a UNOPTFLAT much later.
            }
        }
        if (debug() >= 9 && !m_isSimple) nodep->dumpTree(cout, "    gate!Ok: ");
    }
    virtual ~GateOkVisitor() override = default;
    // PUBLIC METHODS
    bool isSimple() const { return m_isSimple; }
    AstNode* substTree() const { return m_substTreep; }
    const GateVarRefList& rhsVarRefs() const { return m_rhsVarRefs; }
};

//######################################################################
// Gate class functions

class GateVisitor final : public GateBaseVisitor {
private:
    // NODE STATE
    // Entire netlist:
    // AstVarScope::user1p      -> GateVarVertex* for usage var, 0=not set yet
    // {statement}Node::user1p  -> GateLogicVertex* for this statement
    // AstVarScope::user2       -> bool: Signal used in SenItem in *this* always statement
    // AstVar::user2            -> bool: Warned about SYNCASYNCNET
    // AstNodeVarRef::user2     -> bool: ConcatOffset visited
    AstUser1InUse m_inuser1;
    AstUser2InUse m_inuser2;

    // STATE
    V3Graph m_graph;  // Scoreboard of var usages/dependencies
    GateLogicVertex* m_logicVertexp = nullptr;  // Current statement being tracked, nullptr=ignored
    AstScope* m_scopep = nullptr;  // Current scope being processed
    AstNodeModule* m_modp = nullptr;  // Current module
    AstActive* m_activep = nullptr;  // Current active
    bool m_activeReducible = true;  // Is activation block reducible?
    bool m_inSenItem = false;  // Underneath AstSenItem; any varrefs are clocks
    bool m_inSlow = false;  // Inside a slow structure
    VDouble0 m_statSigs;  // Statistic tracking
    VDouble0 m_statRefs;  // Statistic tracking
    VDouble0 m_statDedupLogic;  // Statistic tracking
    VDouble0 m_statAssignMerged;  // Statistic tracking

    // METHODS
    void iterateNewStmt(AstNode* nodep, const char* nonReducibleReason,
                        const char* consumeReason) {
        if (m_scopep) {
            UINFO(5, "   STMT " << nodep << endl);
            // m_activep is null under AstCFunc's, that's ok.
            m_logicVertexp = new GateLogicVertex(&m_graph, m_scopep, nodep, m_activep, m_inSlow);
            if (nonReducibleReason) {
                m_logicVertexp->clearReducibleAndDedupable(nonReducibleReason);
            } else if (!m_activeReducible) {
                // Sequential logic is dedupable
                m_logicVertexp->clearReducible("Block Unreducible");
            }
            if (consumeReason) m_logicVertexp->setConsumed(consumeReason);
            if (VN_IS(nodep, SenItem)) m_logicVertexp->setConsumed("senItem");
            iterateChildren(nodep);
            m_logicVertexp = nullptr;
        }
    }

    GateVarVertex* makeVarVertex(AstVarScope* varscp) {
        GateVarVertex* vertexp = reinterpret_cast<GateVarVertex*>(varscp->user1p());
        if (!vertexp) {
            UINFO(6, "New vertex " << varscp << endl);
            vertexp = new GateVarVertex(&m_graph, m_scopep, varscp);
            varscp->user1p(vertexp);
            if (varscp->varp()->isSigPublic()) {
                // Public signals shouldn't be changed, pli code might be messing with them
                vertexp->clearReducibleAndDedupable("SigPublic");
                vertexp->setConsumed("SigPublic");
            }
            if (varscp->varp()->isIO() && varscp->scopep()->isTop()) {
                // We may need to convert to/from sysc/reg sigs
                vertexp->setIsTop();
                vertexp->clearReducibleAndDedupable("isTop");
                vertexp->setConsumed("isTop");
            }
            if (varscp->varp()->isUsedClock()) vertexp->setConsumed("clock");
        }
        return vertexp;
    }

    void optimizeSignals(bool allowMultiIn);
    bool elimLogicOkOutputs(GateLogicVertex* consumeVertexp, const GateOkVisitor& okVisitor);
    void optimizeElimVar(AstVarScope* varscp, AstNode* substp, AstNode* consumerp);
    void warnSignals();
    void consumedMark();
    void consumedMarkRecurse(GateEitherVertex* vertexp);
    void consumedMove();
    void replaceAssigns();
    void dedupe();
    void mergeAssigns();
    void decomposeClkVectors();

    // VISITORS
    virtual void visit(AstNetlist* nodep) override {
        iterateChildren(nodep);
        // if (debug() > 6) m_graph.dump();
        if (debug() > 6) m_graph.dumpDotFilePrefixed("gate_pre");
        warnSignals();  // Before loss of sync/async pointers
        // Decompose clock vectors -- need to do this before removing redundant edges
        decomposeClkVectors();
        m_graph.removeRedundantEdgesSum(&V3GraphEdge::followAlwaysTrue);
        m_graph.dumpDotFilePrefixed("gate_simp");
        // Find gate interconnect and optimize
        m_graph.userClearVertices();  // vertex->user(): bool. Indicates we've set it as consumed
        // Get rid of buffers first,
        optimizeSignals(false);
        // Then propagate more complicated equations
        optimizeSignals(true);
        // Remove redundant logic
        if (v3Global.opt.oDedupe()) {
            dedupe();
            if (debug() >= 6) m_graph.dumpDotFilePrefixed("gate_dedup");
        }
        if (v3Global.opt.oAssemble()) {
            mergeAssigns();
            if (debug() >= 6) m_graph.dumpDotFilePrefixed("gate_assm");
        }
        // Consumption warnings
        consumedMark();
        m_graph.dumpDotFilePrefixed("gate_opt");
        // Rewrite assignments
        consumedMove();
        replaceAssigns();
    }
    virtual void visit(AstNodeModule* nodep) override {
        VL_RESTORER(m_modp);
        {
            m_modp = nodep;
            m_activeReducible = true;
            iterateChildren(nodep);
        }
    }
    virtual void visit(AstScope* nodep) override {
        UINFO(4, " SCOPE " << nodep << endl);
        m_scopep = nodep;
        m_logicVertexp = nullptr;
        iterateChildren(nodep);
        m_scopep = nullptr;
    }
    virtual void visit(AstActive* nodep) override {
        // Create required blocks and add to module
        UINFO(4, "  BLOCK  " << nodep << endl);
        m_activeReducible = !(nodep->hasClocked());  // Seq logic outputs aren't reducible
        m_activep = nodep;
        AstNode::user2ClearTree();
        iterateChildren(nodep);
        AstNode::user2ClearTree();
        m_activep = nullptr;
        m_activeReducible = true;
    }
    virtual void visit(AstNodeVarRef* nodep) override {
        if (m_scopep) {
            UASSERT_OBJ(m_logicVertexp, nodep, "Var ref not under a logic block");
            AstVarScope* varscp = nodep->varScopep();
            UASSERT_OBJ(varscp, nodep, "Var didn't get varscoped in V3Scope.cpp");
            GateVarVertex* vvertexp = makeVarVertex(varscp);
            UINFO(5, " VARREF to " << varscp << endl);
            if (m_inSenItem) {
                vvertexp->setIsClock();
                // For SYNCASYNCNET
                varscp->user2(true);
            } else if (m_activep && m_activep->hasClocked() && nodep->access().isReadOnly()) {
                if (varscp->user2()) {
                    if (!vvertexp->rstAsyncNodep()) vvertexp->rstAsyncNodep(nodep);
                } else {
                    if (!vvertexp->rstSyncNodep()) vvertexp->rstSyncNodep(nodep);
                }
            }
            // We use weight of one; if we ref the var more than once, when we simplify,
            // the weight will increase
            if (nodep->access().isWriteOrRW()) {
                new V3GraphEdge(&m_graph, m_logicVertexp, vvertexp, 1);
            }
            if (nodep->access().isReadOrRW()) {
                new V3GraphEdge(&m_graph, vvertexp, m_logicVertexp, 1);
            }
        }
    }
    virtual void visit(AstAlwaysPublic* nodep) override {
        VL_RESTORER(m_inSlow);
        {
            m_inSlow = true;
            iterateNewStmt(nodep, "AlwaysPublic", nullptr);
        }
    }
    virtual void visit(AstCFunc* nodep) override {
        iterateNewStmt(nodep, "User C Function", "User C Function");
    }
    virtual void visit(AstSenItem* nodep) override {
        m_inSenItem = true;
        if (m_logicVertexp) {  // Already under logic; presumably a SenGate
            iterateChildren(nodep);
        } else {  // Standalone item, probably right under a SenTree
            iterateNewStmt(nodep, nullptr, nullptr);
        }
        m_inSenItem = false;
    }
    virtual void visit(AstNodeProcedure* nodep) override {
        VL_RESTORER(m_inSlow);
        {
            m_inSlow = VN_IS(nodep, Initial) || VN_IS(nodep, Final);
            iterateNewStmt(nodep, (nodep->isJustOneBodyStmt() ? nullptr : "Multiple Stmts"),
                           nullptr);
        }
    }
    virtual void visit(AstAssignAlias* nodep) override {  //
        iterateNewStmt(nodep, nullptr, nullptr);
    }
    virtual void visit(AstAssignW* nodep) override {  //
        iterateNewStmt(nodep, nullptr, nullptr);
    }
    virtual void visit(AstCoverToggle* nodep) override {
        iterateNewStmt(nodep, "CoverToggle", "CoverToggle");
    }
    virtual void visit(AstTraceDecl* nodep) override {
        VL_RESTORER(m_inSlow);
        {
            m_inSlow = true;
            iterateNewStmt(nodep, "Tracing", "Tracing");
        }
    }
    virtual void visit(AstConcat* nodep) override {
        UASSERT_OBJ(!(VN_IS(nodep->backp(), NodeAssign)
                      && VN_CAST(nodep->backp(), NodeAssign)->lhsp() == nodep),
                    nodep, "Concat on LHS of assignment; V3Const should have deleted it");
        iterateChildren(nodep);
    }

    //--------------------
    virtual void visit(AstNode* nodep) override {
        iterateChildren(nodep);
        if (nodep->isOutputter() && m_logicVertexp) m_logicVertexp->setConsumed("outputter");
    }

public:
    // CONSTRUCTORS
    explicit GateVisitor(AstNode* nodep) { iterate(nodep); }
    virtual ~GateVisitor() override {
        V3Stats::addStat("Optimizations, Gate sigs deleted", m_statSigs);
        V3Stats::addStat("Optimizations, Gate inputs replaced", m_statRefs);
        V3Stats::addStat("Optimizations, Gate sigs deduped", m_statDedupLogic);
        V3Stats::addStat("Optimizations, Gate assign merged", m_statAssignMerged);
    }
};

//----------------------------------------------------------------------

void GateVisitor::optimizeSignals(bool allowMultiIn) {
    for (V3GraphVertex* itp = m_graph.verticesBeginp(); itp; itp = itp->verticesNextp()) {
        if (GateVarVertex* vvertexp = dynamic_cast<GateVarVertex*>(itp)) {
            if (vvertexp->inEmpty()) {
                vvertexp->clearReducibleAndDedupable("inEmpty");  // Can't deal with no sources
                if (!vvertexp->isTop()  // Ok if top inputs are driverless
                    && !vvertexp->varScp()->varp()->valuep()
                    && !vvertexp->varScp()->varp()->isSigPublic()) {
                    UINFO(4, "No drivers " << vvertexp->varScp() << endl);
                    if (false) {
                        // If we warned here after constant propagation, what the user considered
                        // reasonable logic may have disappeared.  Issuing a warning would
                        // thus be confusing.  V3Undriven now handles this.
                        vvertexp->varScp()->varp()->v3warn(
                            UNDRIVEN, "Signal has no drivers: '"
                                          << vvertexp->scopep()->prettyName() << "."
                                          << vvertexp->varScp()->varp()->prettyName() << "'");
                    }
                }
            } else if (!vvertexp->inSize1()) {
                // Can't deal with more than one src
                vvertexp->clearReducibleAndDedupable("size!1");
            }
            // Reduce it?
            if (!vvertexp->reducible()) {
                UINFO(8, "SigNotRed " << vvertexp->name() << endl);
            } else {
                UINFO(8, "Sig " << vvertexp->name() << endl);
                GateLogicVertex* logicVertexp
                    = dynamic_cast<GateLogicVertex*>(vvertexp->inBeginp()->fromp());
                UINFO(8, "  From " << logicVertexp->name() << endl);
                AstNode* logicp = logicVertexp->nodep();
                if (logicVertexp->reducible()) {
                    // Can we eliminate?
                    GateOkVisitor okVisitor(logicp, vvertexp->isClock(), false);
                    const bool multiInputs = okVisitor.rhsVarRefs().size() > 1;
                    // Was it ok?
                    bool doit = okVisitor.isSimple();
                    if (doit && multiInputs) {
                        if (!allowMultiIn) doit = false;
                        // Doit if one input, or not used, or used only once, ignoring traces
                        int n = 0;
                        for (V3GraphEdge* edgep = vvertexp->outBeginp(); edgep;
                             edgep = edgep->outNextp()) {
                            GateLogicVertex* consumeVertexp
                                = dynamic_cast<GateLogicVertex*>(edgep->top());
                            if (!consumeVertexp->slow()) {  // Not tracing or other slow path junk
                                if (edgep->top()->outBeginp()) {  // Destination is itself used
                                    n += edgep->weight();
                                }
                            }
                            if (n > 1) {
                                doit = false;
                                break;
                            }
                        }
                    }
                    // Process it
                    if (!doit) {
                        if (allowMultiIn && (debug() >= 9)) {
                            UINFO(9, "Not ok simp" << okVisitor.isSimple() << " mi" << multiInputs
                                                   << " ob" << vvertexp->outBeginp() << " on"
                                                   << (vvertexp->outBeginp()
                                                           ? vvertexp->outBeginp()->outNextp()
                                                           : nullptr)
                                                   << " " << vvertexp->name() << endl);
                            for (V3GraphEdge* edgep = vvertexp->outBeginp(); edgep;
                                 edgep = edgep->outNextp()) {
                                GateLogicVertex* consumeVertexp
                                    = dynamic_cast<GateLogicVertex*>(edgep->top());
                                UINFO(9, "    edge " << edgep << " to: " << consumeVertexp->nodep()
                                                     << endl);
                            }
                            for (V3GraphEdge* edgep = vvertexp->inBeginp(); edgep;
                                 edgep = edgep->inNextp()) {
                                GateLogicVertex* consumeVertexp
                                    = dynamic_cast<GateLogicVertex*>(edgep->fromp());
                                UINFO(9, "    edge " << edgep << " from: "
                                                     << consumeVertexp->nodep() << endl);
                            }
                        }
                    } else {
                        AstNode* substp = okVisitor.substTree();
                        if (debug() >= 5) logicp->dumpTree(cout, "    elimVar:  ");
                        if (debug() >= 5) substp->dumpTree(cout, "      subst:  ");
                        ++m_statSigs;
                        bool removedAllUsages = true;
                        for (V3GraphEdge* edgep = vvertexp->outBeginp(); edgep;) {
                            GateLogicVertex* consumeVertexp
                                = dynamic_cast<GateLogicVertex*>(edgep->top());
                            AstNode* consumerp = consumeVertexp->nodep();
                            if (!elimLogicOkOutputs(consumeVertexp, okVisitor /*ref*/)) {
                                // Cannot optimize this replacement
                                removedAllUsages = false;
                                edgep = edgep->outNextp();
                            } else {
                                optimizeElimVar(vvertexp->varScp(), substp, consumerp);
                                // If the new replacement referred to a signal,
                                // Correct the graph to point to this new generating variable
                                const GateVarRefList& rhsVarRefs = okVisitor.rhsVarRefs();
                                for (GateVarRefList::const_iterator it = rhsVarRefs.begin();
                                     it != rhsVarRefs.end(); ++it) {
                                    AstVarScope* newvarscp = (*it)->varScopep();
                                    UINFO(9, "         Point-to-new vertex " << newvarscp << endl);
                                    GateVarVertex* varvertexp = makeVarVertex(newvarscp);
                                    new V3GraphEdge(&m_graph, varvertexp, consumeVertexp, 1);
                                    // Propagate clock attribute onto generating node
                                    varvertexp->propagateAttrClocksFrom(vvertexp);
                                }
                                // Remove the edge
                                VL_DO_DANGLING(edgep->unlinkDelete(), edgep);
                                ++m_statRefs;
                                edgep = vvertexp->outBeginp();
                            }
                        }
                        if (removedAllUsages) {
                            // Remove input links
                            while (V3GraphEdge* edgep = vvertexp->inBeginp()) {
                                VL_DO_DANGLING(edgep->unlinkDelete(), edgep);
                            }
                            // Clone tree so we remember it for tracing, and keep the pointer
                            // to the "ALWAYS" part of the tree as part of this statement
                            // That way if a later signal optimization that
                            // retained a pointer to the always can
                            // optimize it further
                            logicp->unlinkFrBack();
                            vvertexp->varScp()->valuep(logicp);
                            logicp = nullptr;
                            // Mark the vertex so we don't mark it as being
                            // unconsumed in the next step
                            vvertexp->user(true);
                            logicVertexp->user(true);
                        }
                    }
                }
            }
        }
    }
}

bool GateVisitor::elimLogicOkOutputs(GateLogicVertex* consumeVertexp,
                                     const GateOkVisitor& okVisitor) {
    // Return true if can optimize
    // Return false if the consuming logic has an output signal that the
    // replacement logic has as an input

    // Use map to find duplicates between two lists
    std::unordered_set<AstVarScope*> varscopes;
    // Replacement logic usually has shorter input list, so faster to build list based on it
    const GateVarRefList& rhsVarRefs = okVisitor.rhsVarRefs();
    for (GateVarRefList::const_iterator it = rhsVarRefs.begin(); it != rhsVarRefs.end(); ++it) {
        AstVarScope* vscp = (*it)->varScopep();
        varscopes.insert(vscp);
    }
    for (V3GraphEdge* edgep = consumeVertexp->outBeginp(); edgep; edgep = edgep->outNextp()) {
        GateVarVertex* consVVertexp = dynamic_cast<GateVarVertex*>(edgep->top());
        AstVarScope* vscp = consVVertexp->varScp();
        if (varscopes.find(vscp) != varscopes.end()) {
            UINFO(9, "    Block-unopt, insertion generates input vscp " << vscp << endl);
            return false;
        }
    }
    return true;
}

void GateVisitor::replaceAssigns() {
    for (V3GraphVertex* itp = m_graph.verticesBeginp(); itp; itp = itp->verticesNextp()) {
        if (GateVarVertex* vvertexp = dynamic_cast<GateVarVertex*>(itp)) {
            // Take the Comments/assigns that were moved to the VarScope and change them to a
            // simple value assignment
            AstVarScope* vscp = vvertexp->varScp();
            if (vscp->valuep() && !VN_IS(vscp->valuep(), NodeMath)) {
                // if (debug() > 9) vscp->dumpTree(cout, "-vscPre:  ");
                while (AstNode* delp = VN_CAST(vscp->valuep(), Comment)) {
                    VL_DO_DANGLING(delp->unlinkFrBack()->deleteTree(), delp);
                }
                if (AstInitial* delp = VN_CAST(vscp->valuep(), Initial)) {
                    AstNode* bodyp = delp->bodysp();
                    bodyp->unlinkFrBackWithNext();
                    delp->replaceWith(bodyp);
                    VL_DO_DANGLING(delp->deleteTree(), delp);
                }
                if (AstAlways* delp = VN_CAST(vscp->valuep(), Always)) {
                    AstNode* bodyp = delp->bodysp();
                    bodyp->unlinkFrBackWithNext();
                    delp->replaceWith(bodyp);
                    VL_DO_DANGLING(delp->deleteTree(), delp);
                }
                if (AstNodeAssign* delp = VN_CAST(vscp->valuep(), NodeAssign)) {
                    AstNode* rhsp = delp->rhsp();
                    rhsp->unlinkFrBack();
                    delp->replaceWith(rhsp);
                    VL_DO_DANGLING(delp->deleteTree(), delp);
                }
                // if (debug() > 9) {vscp->dumpTree(cout, "-vscDone: "); cout<<endl;}
                if (!VN_IS(vscp->valuep(), NodeMath) || vscp->valuep()->nextp()) {
                    vscp->dumpTree(std::cerr, "vscStrange: ");
                    vscp->v3fatalSrc("Value of varscope not mathematical");
                }
            }
        }
    }
}

//----------------------------------------------------------------------

void GateVisitor::consumedMark() {
    // Propagate consumed signals backwards to all producers into a consumed node
    m_graph.userClearVertices();
    for (V3GraphVertex* vertexp = m_graph.verticesBeginp(); vertexp;
         vertexp = vertexp->verticesNextp()) {
        GateEitherVertex* evertexp = static_cast<GateEitherVertex*>(vertexp);
        if (!evertexp->user() && evertexp->consumed()) consumedMarkRecurse(evertexp);
    }
}

void GateVisitor::consumedMarkRecurse(GateEitherVertex* vertexp) {
    if (vertexp->user()) return;  // Already marked
    vertexp->user(true);
    if (!vertexp->consumed()) vertexp->setConsumed("propagated");
    // Walk sources and mark them too
    for (V3GraphEdge* edgep = vertexp->inBeginp(); edgep; edgep = edgep->inNextp()) {
        GateEitherVertex* eFromVertexp = static_cast<GateEitherVertex*>(edgep->fromp());
        consumedMarkRecurse(eFromVertexp);
    }
}

void GateVisitor::consumedMove() {
    // Remove unused logic (logic that doesn't hit a combo block or a display statement)
    // We need the "usually" block logic to do a better job at this
    for (V3GraphVertex* vertexp = m_graph.verticesBeginp(); vertexp;
         vertexp = vertexp->verticesNextp()) {
        if (GateVarVertex* vvertexp = dynamic_cast<GateVarVertex*>(vertexp)) {
            if (!vvertexp->consumed() && !vvertexp->user()) {
                UINFO(8, "Unconsumed " << vvertexp->varScp() << endl);
            }
        }
        if (GateLogicVertex* lvertexp = dynamic_cast<GateLogicVertex*>(vertexp)) {
            AstNode* nodep = lvertexp->nodep();
            AstActive* oldactp = lvertexp->activep();  // nullptr under cfunc
            if (!lvertexp->consumed() && oldactp) {
                // Eventually: Move the statement to a new active block
                // with "tracing-on" sensitivity
                UINFO(8, "    Remove unconsumed " << nodep << endl);
                nodep->unlinkFrBack();
                VL_DO_DANGLING(pushDeletep(nodep), nodep);
            }
        }
    }
}

//----------------------------------------------------------------------

void GateVisitor::warnSignals() {
    AstNode::user2ClearTree();
    for (V3GraphVertex* itp = m_graph.verticesBeginp(); itp; itp = itp->verticesNextp()) {
        if (GateVarVertex* vvertexp = dynamic_cast<GateVarVertex*>(itp)) {
            AstVarScope* vscp = vvertexp->varScp();
            AstNode* sp = vvertexp->rstSyncNodep();
            AstNode* ap = vvertexp->rstAsyncNodep();
            if (ap && sp && !vscp->varp()->user2()) {
                // This is somewhat wrong, as marking one flop as ok for sync
                // may mean a different flop now fails.  However it's a pain to
                // then report a warning in a new place - we should report them all at once.
                // Instead we'll disable if any disabled
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
// Push constant into expressions and reevaluate

class GateDedupeVarVisitor;

class GateElimVisitor final : public GateBaseVisitor {
private:
    // NODE STATE
    // STATE
    AstVarScope* m_elimVarScp;  // Variable being eliminated
    AstNode* m_replaceTreep;  // What to replace the variable with
    bool m_didReplace;  // Did we do any replacements
    GateDedupeVarVisitor* m_varVisp;  // Callback to keep hash up to date

    // METHODS
    void hashReplace(AstNode* oldp, AstNode* newp);

    // VISITORS
    virtual void visit(AstNodeVarRef* nodep) override {
        if (nodep->varScopep() == m_elimVarScp) {
            // Substitute in the new tree
            // It's possible we substitute into something that will be reduced more later,
            // however, as we never delete the top Always/initial statement, all should be well.
            m_didReplace = true;
            UASSERT_OBJ(nodep->access().isReadOnly(), nodep,
                        "Can't replace lvalue assignments with const var");
            AstNode* substp = m_replaceTreep->cloneTree(false);
            UASSERT_OBJ(
                !(VN_IS(nodep, NodeVarRef) && VN_IS(substp, NodeVarRef) && nodep->same(substp)),
                // Prevent an infinite loop...
                substp, "Replacing node with itself; perhaps circular logic?");
            // Which fileline() to use?
            // If replacing with logic, an error/warning is likely to want to point to the logic
            // IE what we're replacing with.
            // However a VARREF should point to the original as it's otherwise confusing
            // to throw warnings that point to a PIN rather than where the pin us used.
            if (VN_IS(substp, VarRef)) substp->fileline(nodep->fileline());
            // Make the substp an rvalue like nodep. This facilitates the hashing in dedupe.
            if (AstNodeVarRef* varrefp = VN_CAST(substp, NodeVarRef))
                varrefp->access(VAccess::READ);
            hashReplace(nodep, substp);
            nodep->replaceWith(substp);
            VL_DO_DANGLING(nodep->deleteTree(), nodep);
        }
    }
    virtual void visit(AstNode* nodep) override { iterateChildren(nodep); }

public:
    // CONSTRUCTORS
    virtual ~GateElimVisitor() override = default;
    GateElimVisitor(AstNode* nodep, AstVarScope* varscp, AstNode* replaceTreep,
                    GateDedupeVarVisitor* varVisp) {
        UINFO(9, "     elimvisitor " << nodep << endl);
        UINFO(9, "     elim varscp " << varscp << endl);
        UINFO(9, "     elim repce  " << replaceTreep << endl);
        m_didReplace = false;
        m_elimVarScp = varscp;
        m_replaceTreep = replaceTreep;
        m_varVisp = varVisp;
        iterate(nodep);
    }
    bool didReplace() const { return m_didReplace; }
};

void GateVisitor::optimizeElimVar(AstVarScope* varscp, AstNode* substp, AstNode* consumerp) {
    if (debug() >= 5) consumerp->dumpTree(cout, "    elimUsePre: ");
    GateElimVisitor elimVisitor(consumerp, varscp, substp, nullptr);
    if (elimVisitor.didReplace()) {
        if (debug() >= 9) consumerp->dumpTree(cout, "    elimUseCns: ");
        // Caution: Can't let V3Const change our handle to consumerp, such as by
        // optimizing away this assignment, etc.
        consumerp = V3Const::constifyEdit(consumerp);
        if (debug() >= 5) consumerp->dumpTree(cout, "    elimUseDne: ");
        // Some previous input edges may have disappeared, perhaps all of them.
        // If we remove the edges we can further optimize
        // See e.g t_var_overzero.v.
    }
}

//######################################################################
// Auxiliary hash class for GateDedupeVarVisitor

class GateDedupeHash final : public V3DupFinderUserSame {
private:
    // NODE STATE
    // Ast*::user2p     -> parent AstNodeAssign* for this rhsp
    // Ast*::user3p     -> AstActive* of assign, for isSame() in test for duplicate
    //                     Set to nullptr if this assign's tree was later replaced
    // Ast*::user5p     -> AstNode* of assign if condition, for isSame() in test for duplicate
    //                     Set to nullptr if this assign's tree was later replaced
    // AstUser1InUse    m_inuser1;      (Allocated for use in GateVisitor)
    // AstUser2InUse    m_inuser2;      (Allocated for use in GateVisitor)
    AstUser3InUse m_inuser3;
    // AstUser4InUse    m_inuser4;      (Allocated for use in V3Hasher via V3DupFinder)
    AstUser5InUse m_inuser5;

    V3DupFinder m_dupFinder;  // Duplicate finder for rhs of assigns
    std::unordered_set<AstNode*> m_nodeDeleteds;  // Any node in this hash was deleted

    VL_DEBUG_FUNC;  // Declare debug()

    bool same(AstNode* node1p, AstNode* node2p) {
        // Regarding the complexity of this funcition 'same':
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
        // improved which should also speed things up), and AstNodeMath for if conditions, which
        // are hopefully small, and to be safe they should probably be only considered same when
        // identical instances (otherwise if writing the condition between 2 ifs don't really
        // merge).
        return node1p == node2p || (node1p && node1p->sameTree(node2p));
    }

public:
    GateDedupeHash() = default;
    virtual ~GateDedupeHash() override {
        if (v3Global.opt.debugCheck()) check();
    }

    // About to replace a node; any node we're tracking refers to oldp, change it to newp.
    // This might be a variable on the lhs of the duplicate tree,
    // or could be a rhs variable in a tree we're not replacing (or not yet anyways)
    void hashReplace(AstNode* oldp, AstNode* newp) {
        UINFO(9, "replacing " << (void*)oldp << " with " << (void*)newp << endl);
        // We could update the user3p and user5p but the resulting node
        // still has incorrect hash.  We really need to remove all hash on
        // the whole hash entry tree involving the replaced node and
        // rehash.  That's complicated and this is rare, so just remove it
        // from consideration.
        m_nodeDeleteds.insert(oldp);
    }
    bool isReplaced(AstNode* nodep) {
        // Assignment may have been hashReplaced, if so consider non-match (effectively removed)
        UASSERT_OBJ(!VN_IS(nodep, NodeAssign), nodep, "Dedup attempt on non-assign");
        AstNode* extra1p = nodep->user3p();
        AstNode* extra2p = nodep->user5p();
        return ((extra1p && m_nodeDeleteds.find(extra1p) != m_nodeDeleteds.end())
                || (extra2p && m_nodeDeleteds.find(extra2p) != m_nodeDeleteds.end()));
    }

    // Callback from V3DupFinder::findDuplicate
    virtual bool isSame(AstNode* node1p, AstNode* node2p) override {
        // Assignment may have been hashReplaced, if so consider non-match (effectively removed)
        if (isReplaced(node1p) || isReplaced(node2p)) {
            // UINFO(9, "isSame hit on replaced "<<(void*)node1p<<" "<<(void*)node2p<<endl);
            return false;
        }
        return same(node1p->user3p(), node2p->user3p()) && same(node1p->user5p(), node2p->user5p())
               && node1p->user2p()->type() == node2p->user2p()->type();
    }

    AstNodeAssign* hashAndFindDupe(AstNodeAssign* assignp, AstNode* extra1p, AstNode* extra2p) {
        // Legal for extra1p/2p to be nullptr, we'll compare with other assigns with extras also
        // nullptr
        AstNode* rhsp = assignp->rhsp();
        rhsp->user2p(assignp);
        rhsp->user3p(extra1p);
        rhsp->user5p(extra2p);

        const auto inserted = m_dupFinder.insert(rhsp);
        const auto dupit = m_dupFinder.findDuplicate(rhsp, this);
        // Even though rhsp was just inserted, V3DupFinder::findDuplicate doesn't
        // return anything in the hash that has the same pointer (V3DupFinder::findDuplicate)
        // So dupit is either a different, duplicate rhsp, or the end of the hash.
        if (dupit != m_dupFinder.end()) {
            m_dupFinder.erase(inserted);
            return VN_CAST(dupit->second->user2p(), NodeAssign);
        }
        // Retain new inserted information
        return nullptr;
    }

    void check() {
        for (const auto& itr : m_dupFinder) {
            AstNode* nodep = itr.second;
            AstNode* activep = nodep->user3p();
            AstNode* condVarp = nodep->user5p();
            if (!isReplaced(nodep)) {
                // This class won't break if activep isn't an active, or
                // ifVar isn't a var, but this is checking the caller's construction.
                UASSERT_OBJ(!activep || (!VN_DELETED(activep) && VN_IS(activep, Active)), nodep,
                            "V3DupFinder check failed, lost active pointer");
                UASSERT_OBJ(!condVarp || !VN_DELETED(condVarp), nodep,
                            "V3DupFinder check failed, lost if pointer");
            }
        }
    }
};

//######################################################################
// Have we seen the rhs of this assign before?

class GateDedupeVarVisitor final : public GateBaseVisitor {
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
private:
    // STATE
    GateDedupeHash m_ghash;  // Hash used to find dupes of rhs of assign
    AstNodeAssign* m_assignp = nullptr;  // Assign found for dedupe
    AstNode* m_ifCondp = nullptr;  // IF condition that assign is under
    bool m_always = false;  // Assign is under an always
    bool m_dedupable = true;  // Determined the assign to be dedupable

    // VISITORS
    virtual void visit(AstNodeAssign* assignp) override {
        if (m_dedupable) {
            // I think we could safely dedupe an always block with multiple
            // non-blocking statements, but erring on side of caution here
            if (!m_assignp) {
                m_assignp = assignp;
            } else {
                m_dedupable = false;
            }
        }
    }
    virtual void visit(AstAlways* alwaysp) override {
        if (m_dedupable) {
            if (!m_always) {
                m_always = true;
                iterateAndNextNull(alwaysp->bodysp());
            } else {
                m_dedupable = false;
            }
        }
    }
    // Ugly support for latches of the specific form -
    //  always @(...)
    //    if (...)
    //       foo = ...; // or foo <= ...;
    virtual void visit(AstNodeIf* ifp) override {
        if (m_dedupable) {
            if (m_always && !m_ifCondp && !ifp->elsesp()) {
                // we're under an always, this is the first IF, and there's no else
                m_ifCondp = ifp->condp();
                iterateAndNextNull(ifp->ifsp());
            } else {
                m_dedupable = false;
            }
        }
    }

    virtual void visit(AstComment*) override {}  // NOP
    //--------------------
    virtual void visit(AstNode*) override {  //
        m_dedupable = false;
    }

public:
    // CONSTRUCTORS
    GateDedupeVarVisitor() = default;
    virtual ~GateDedupeVarVisitor() override = default;
    // PUBLIC METHODS
    AstNodeVarRef* findDupe(AstNode* nodep, AstVarScope* consumerVarScopep, AstActive* activep) {
        m_assignp = nullptr;
        m_ifCondp = nullptr;
        m_always = false;
        m_dedupable = true;
        iterate(nodep);
        if (m_dedupable && m_assignp) {
            AstNode* lhsp = m_assignp->lhsp();
            // Possible todo, handle more complex lhs expressions
            if (AstNodeVarRef* lhsVarRefp = VN_CAST(lhsp, NodeVarRef)) {
                UASSERT_OBJ(lhsVarRefp->varScopep() == consumerVarScopep, consumerVarScopep,
                            "Consumer doesn't match lhs of assign");
                if (AstNodeAssign* dup = m_ghash.hashAndFindDupe(m_assignp, activep, m_ifCondp)) {
                    return static_cast<AstNodeVarRef*>(dup->lhsp());
                }
            }
        }
        return nullptr;
    }
    void hashReplace(AstNode* oldp, AstNode* newp) { m_ghash.hashReplace(oldp, newp); }
};

//######################################################################

void GateElimVisitor::hashReplace(AstNode* oldp, AstNode* newp) {
    UINFO(9, "hashReplace " << (void*)oldp << " -> " << (void*)newp << endl);
    if (m_varVisp) m_varVisp->hashReplace(oldp, newp);
}

//######################################################################
// Recurse through the graph, looking for duplicate expressions on the rhs of an assign

class GateDedupeGraphVisitor final : public GateGraphBaseVisitor {
private:
    // NODE STATE
    // AstVarScope::user2p      -> bool: already visited
    // AstUser2InUse            m_inuser2;      (Allocated for use in GateVisitor)
    VDouble0 m_numDeduped;  // Statistic tracking
    GateDedupeVarVisitor m_varVisitor;  // Looks for a dupe of the logic
    int m_depth = 0;  // Iteration depth

    virtual VNUser visit(GateVarVertex* vvertexp, VNUser) override {
        // Check that we haven't been here before
        if (m_depth > GATE_DEDUP_MAX_DEPTH)
            return VNUser(0);  // Break loops; before user2 set so hit this vertex later
        if (vvertexp->varScp()->user2()) return VNUser(0);
        vvertexp->varScp()->user2(true);

        m_depth++;
        if (vvertexp->inSize1()) {
            AstNodeVarRef* dupVarRefp = static_cast<AstNodeVarRef*>(
                vvertexp->iterateInEdges(*this, VNUser(vvertexp)).toNodep());
            if (dupVarRefp) {  // visit(GateLogicVertex*...) returned match
                V3GraphEdge* edgep = vvertexp->inBeginp();
                GateLogicVertex* lvertexp = static_cast<GateLogicVertex*>(edgep->fromp());
                UASSERT_OBJ(vvertexp->dedupable(), vvertexp->varScp(),
                            "GateLogicVertex* visit should have returned nullptr "
                            "if consumer var vertex is not dedupable.");
                GateOkVisitor okVisitor(lvertexp->nodep(), false, true);
                if (okVisitor.isSimple()) {
                    AstVarScope* dupVarScopep = dupVarRefp->varScopep();
                    GateVarVertex* dupVvertexp
                        = reinterpret_cast<GateVarVertex*>(dupVarScopep->user1p());
                    UINFO(4, "replacing " << vvertexp << " with " << dupVvertexp << endl);
                    ++m_numDeduped;
                    // Replace all of this varvertex's consumers with dupVarRefp
                    for (V3GraphEdge* outedgep = vvertexp->outBeginp(); outedgep;) {
                        GateLogicVertex* consumeVertexp
                            = dynamic_cast<GateLogicVertex*>(outedgep->top());
                        AstNode* consumerp = consumeVertexp->nodep();
                        // if (debug() >= 9) m_graphp->dumpDotFilePrefixed("gate_preelim");
                        UINFO(9,
                              "elim src vtx" << lvertexp << " node " << lvertexp->nodep() << endl);
                        UINFO(9,
                              "elim cons vtx" << consumeVertexp << " node " << consumerp << endl);
                        UINFO(9, "elim var vtx " << vvertexp << " node " << vvertexp->varScp()
                                                 << endl);
                        UINFO(9, "replace with " << dupVarRefp << endl);
                        if (lvertexp == consumeVertexp) {
                            UINFO(9, "skipping as self-recirculates\n");
                        } else {
                            GateElimVisitor elimVisitor(consumerp, vvertexp->varScp(), dupVarRefp,
                                                        &m_varVisitor);
                        }
                        outedgep = outedgep->relinkFromp(dupVvertexp);
                    }
                    // Propagate attributes
                    dupVvertexp->propagateAttrClocksFrom(vvertexp);
                    // Remove inputs links
                    while (V3GraphEdge* inedgep = vvertexp->inBeginp()) {
                        VL_DO_DANGLING(inedgep->unlinkDelete(), inedgep);
                    }
                    // replaceAssigns() does the deleteTree on lvertexNodep in a later step
                    AstNode* lvertexNodep = lvertexp->nodep();
                    lvertexNodep->unlinkFrBack();
                    vvertexp->varScp()->valuep(lvertexNodep);
                    lvertexNodep = nullptr;
                    vvertexp->user(true);
                    lvertexp->user(true);
                }
            }
        }
        m_depth--;
        return VNUser(0);
    }

    // Given iterated logic, starting at vu which was consumer's GateVarVertex
    // Returns a varref that has the same logic input; or nullptr if none
    virtual VNUser visit(GateLogicVertex* lvertexp, VNUser vu) override {
        lvertexp->iterateInEdges(*this);

        GateVarVertex* consumerVvertexpp = static_cast<GateVarVertex*>(vu.toGraphVertex());
        if (lvertexp->dedupable() && consumerVvertexpp->dedupable()) {
            AstNode* nodep = lvertexp->nodep();
            AstVarScope* consumerVarScopep = consumerVvertexpp->varScp();
            // TODO: Doing a simple pointer comparison of activep won't work
            // optimally for statements under generated clocks. Statements under
            // different generated clocks will never compare as equal, even if the
            // generated clocks are deduped into one clock.
            AstActive* activep = lvertexp->activep();
            return VNUser(m_varVisitor.findDupe(nodep, consumerVarScopep, activep));
        }
        return VNUser(0);
    }

public:
    explicit GateDedupeGraphVisitor(V3Graph* graphp)
        : GateGraphBaseVisitor{graphp} {}
    void dedupeTree(GateVarVertex* vvertexp) { vvertexp->accept(*this); }
    VDouble0 numDeduped() { return m_numDeduped; }
};

//----------------------------------------------------------------------

void GateVisitor::dedupe() {
    AstNode::user2ClearTree();
    GateDedupeGraphVisitor deduper(&m_graph);
    // Traverse starting from each of the clocks
    UINFO(9, "Gate dedupe() clocks:\n");
    for (V3GraphVertex* itp = m_graph.verticesBeginp(); itp; itp = itp->verticesNextp()) {
        if (GateVarVertex* vvertexp = dynamic_cast<GateVarVertex*>(itp)) {
            if (vvertexp->isClock()) deduper.dedupeTree(vvertexp);
        }
    }
    // Traverse starting from each of the outputs
    UINFO(9, "Gate dedupe() outputs:\n");
    for (V3GraphVertex* itp = m_graph.verticesBeginp(); itp; itp = itp->verticesNextp()) {
        if (GateVarVertex* vvertexp = dynamic_cast<GateVarVertex*>(itp)) {
            if (vvertexp->isTop() && vvertexp->varScp()->varp()->isWritable()) {
                deduper.dedupeTree(vvertexp);
            }
        }
    }
    m_statDedupLogic += deduper.numDeduped();
}

//######################################################################
// Recurse through the graph, try to merge assigns

class GateMergeAssignsGraphVisitor final : public GateGraphBaseVisitor {
private:
    // NODE STATE
    AstNodeAssign* m_assignp = nullptr;
    AstActive* m_activep = nullptr;
    GateLogicVertex* m_logicvp = nullptr;
    VDouble0 m_numMergedAssigns;  // Statistic tracking

    // assemble two Sel into one if possible
    AstSel* merge(AstSel* pre, AstSel* cur) {
        AstVarRef* preVarRefp = VN_CAST(pre->fromp(), VarRef);
        AstVarRef* curVarRefp = VN_CAST(cur->fromp(), VarRef);
        if (!preVarRefp || !curVarRefp || !curVarRefp->same(preVarRefp)) {
            return nullptr;  // not the same var
        }
        const AstConst* pstart = VN_CAST(pre->lsbp(), Const);
        const AstConst* pwidth = VN_CAST(pre->widthp(), Const);
        const AstConst* cstart = VN_CAST(cur->lsbp(), Const);
        const AstConst* cwidth = VN_CAST(cur->widthp(), Const);
        if (!pstart || !pwidth || !cstart || !cwidth) return nullptr;  // too complicated
        if (cur->lsbConst() + cur->widthConst() == pre->lsbConst()) {
            return new AstSel(curVarRefp->fileline(), curVarRefp->cloneTree(false),
                              cur->lsbConst(), pre->widthConst() + cur->widthConst());
        } else {
            return nullptr;
        }
    }

    virtual VNUser visit(GateVarVertex* vvertexp, VNUser) override {
        for (V3GraphEdge* edgep = vvertexp->inBeginp(); edgep;) {
            V3GraphEdge* oldedgep = edgep;
            edgep = edgep->inNextp();  // for recursive since the edge could be deleted
            if (GateLogicVertex* lvertexp = dynamic_cast<GateLogicVertex*>(oldedgep->fromp())) {
                if (AstNodeAssign* assignp = VN_CAST(lvertexp->nodep(), NodeAssign)) {
                    // if (lvertexp->outSize1() && VN_IS(assignp->lhsp(), Sel)) {
                    if (VN_IS(assignp->lhsp(), Sel) && lvertexp->outSize1()) {
                        UINFO(9, "assing to the nodep["
                                     << VN_CAST(assignp->lhsp(), Sel)->lsbConst() << "]" << endl);
                        // first assign with Sel-lhs
                        if (!m_activep) m_activep = lvertexp->activep();
                        if (!m_logicvp) m_logicvp = lvertexp;
                        if (!m_assignp) m_assignp = assignp;

                        // not under the same active
                        if (m_activep != lvertexp->activep()) {
                            m_activep = lvertexp->activep();
                            m_logicvp = lvertexp;
                            m_assignp = assignp;
                            continue;
                        }

                        AstSel* preselp = VN_CAST(m_assignp->lhsp(), Sel);
                        AstSel* curselp = VN_CAST(assignp->lhsp(), Sel);
                        if (!preselp || !curselp) continue;

                        if (AstSel* newselp = merge(preselp, curselp)) {
                            UINFO(5, "assemble to new sel: " << newselp << endl);
                            // replace preSel with newSel
                            preselp->replaceWith(newselp);
                            VL_DO_DANGLING(preselp->deleteTree(), preselp);
                            // create new rhs for pre assignment
                            AstNode* newrhsp = new AstConcat(m_assignp->rhsp()->fileline(),
                                                             m_assignp->rhsp()->cloneTree(false),
                                                             assignp->rhsp()->cloneTree(false));
                            AstNode* oldrhsp = m_assignp->rhsp();
                            oldrhsp->replaceWith(newrhsp);
                            VL_DO_DANGLING(oldrhsp->deleteTree(), oldrhsp);
                            m_assignp->dtypeChgWidthSigned(m_assignp->width() + assignp->width(),
                                                           m_assignp->width() + assignp->width(),
                                                           VSigning::SIGNED);
                            // don't need to delete, will be handled
                            // assignp->unlinkFrBack(); VL_DO_DANGLING(assignp->deleteTree(),
                            // assignp);

                            // update the graph
                            {
                                // delete all inedges to lvertexp
                                if (!lvertexp->inEmpty()) {
                                    for (V3GraphEdge* ledgep = lvertexp->inBeginp(); ledgep;) {
                                        V3GraphEdge* oedgep = ledgep;
                                        ledgep = ledgep->inNextp();
                                        GateEitherVertex* fromvp
                                            = dynamic_cast<GateEitherVertex*>(oedgep->fromp());
                                        new V3GraphEdge(m_graphp, fromvp, m_logicvp, 1);
                                        VL_DO_DANGLING(oedgep->unlinkDelete(), oedgep);
                                    }
                                }
                                // delete all outedges to lvertexp, only one
                                VL_DO_DANGLING(oldedgep->unlinkDelete(), oldedgep);
                            }
                            ++m_numMergedAssigns;
                        } else {
                            m_assignp = assignp;
                            m_logicvp = lvertexp;
                        }
                    }
                }
            }
        }
        return VNUser(0);
    }
    virtual VNUser visit(GateLogicVertex*, VNUser) override {  //
        return VNUser(0);
    }

public:
    explicit GateMergeAssignsGraphVisitor(V3Graph* graphp)
        : GateGraphBaseVisitor{graphp} {
        m_graphp = graphp;  // In base
    }
    void mergeAssignsTree(GateVarVertex* vvertexp) { vvertexp->accept(*this); }
    VDouble0 numMergedAssigns() { return m_numMergedAssigns; }
};

//----------------------------------------------------------------------

void GateVisitor::mergeAssigns() {
    UINFO(6, "mergeAssigns\n");
    GateMergeAssignsGraphVisitor merger(&m_graph);
    for (V3GraphVertex* itp = m_graph.verticesBeginp(); itp; itp = itp->verticesNextp()) {
        if (GateVarVertex* vvertexp = dynamic_cast<GateVarVertex*>(itp)) {
            merger.mergeAssignsTree(vvertexp);
        }
    }
    m_statAssignMerged += merger.numMergedAssigns();
}

//######################################################################
// Find a var's offset in a concatenation

class GateConcatVisitor final : public GateBaseVisitor {
private:
    // STATE
    AstVarScope* m_vscp = nullptr;  // Varscope we're trying to find
    int m_offset = 0;  // Current offset of varscope
    int m_found_offset = 0;  // Found offset of varscope
    bool m_found = false;  // Offset found

    // VISITORS
    virtual void visit(AstNodeVarRef* nodep) override {
        UINFO(9, "CLK DECOMP Concat search var (off = " << m_offset << ") - " << nodep << endl);
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
    virtual void visit(AstConcat* nodep) override {
        UINFO(9, "CLK DECOMP Concat search (off = " << m_offset << ") - " << nodep << endl);
        iterate(nodep->rhsp());
        iterate(nodep->lhsp());
    }
    //--------------------
    virtual void visit(AstNode* nodep) override { iterateChildren(nodep); }

public:
    // CONSTRUCTORS
    GateConcatVisitor() = default;
    virtual ~GateConcatVisitor() override = default;
    // PUBLIC METHODS
    bool concatOffset(AstConcat* concatp, AstVarScope* vscp, int& offsetr) {
        m_vscp = vscp;
        m_offset = 0;
        m_found = false;
        // Iterate
        iterate(concatp);
        UINFO(9, "CLK DECOMP Concat Offset (found = " << m_found << ") (" << m_found_offset
                                                      << ") - " << concatp << " : " << vscp
                                                      << endl);
        offsetr = m_found_offset;
        return m_found;
    }
};

//######################################################################
// Recurse through the graph, looking for clock vectors to bypass

class GateClkDecompState final {
public:
    int m_offset;
    AstVarScope* m_last_vsp;
    GateClkDecompState(int offset, AstVarScope* vsp)
        : m_offset{offset}
        , m_last_vsp{vsp} {}
    virtual ~GateClkDecompState() = default;
};

class GateClkDecompGraphVisitor final : public GateGraphBaseVisitor {
private:
    // NODE STATE
    // AstVarScope::user2p      -> bool: already visited
    int m_seen_clk_vectors = 0;
    AstVarScope* m_clk_vsp = nullptr;
    GateVarVertex* m_clk_vvertexp = nullptr;
    GateConcatVisitor m_concat_visitor;
    int m_total_seen_clk_vectors = 0;
    int m_total_decomposed_clk_vectors = 0;

    virtual VNUser visit(GateVarVertex* vvertexp, VNUser vu) override {
        // Check that we haven't been here before
        AstVarScope* vsp = vvertexp->varScp();
        if (vsp->user2SetOnce()) return VNUser(0);
        UINFO(9, "CLK DECOMP Var - " << vvertexp << " : " << vsp << endl);
        if (vsp->varp()->width() > 1) {
            m_seen_clk_vectors++;
            m_total_seen_clk_vectors++;
        }
        GateClkDecompState* currState = reinterpret_cast<GateClkDecompState*>(vu.c());
        GateClkDecompState nextState(currState->m_offset, vsp);
        vvertexp->iterateCurrentOutEdges(*this, VNUser(&nextState));
        if (vsp->varp()->width() > 1) --m_seen_clk_vectors;
        vsp->user2(false);
        return VNUser(0);  // Unused
    }

    virtual VNUser visit(GateLogicVertex* lvertexp, VNUser vu) override {
        GateClkDecompState* currState = reinterpret_cast<GateClkDecompState*>(vu.c());
        int clk_offset = currState->m_offset;
        if (const AstAssignW* assignp = VN_CAST(lvertexp->nodep(), AssignW)) {
            UINFO(9, "CLK DECOMP Logic (off = " << clk_offset << ") - " << lvertexp << " : "
                                                << m_clk_vsp << endl);
            // RHS
            if (AstSel* rselp = VN_CAST(assignp->rhsp(), Sel)) {
                if (VN_IS(rselp->lsbp(), Const) && VN_IS(rselp->widthp(), Const)) {
                    if (clk_offset < rselp->lsbConst() || clk_offset > rselp->msbConst()) {
                        UINFO(9, "CLK DECOMP Sel [ " << rselp->msbConst() << " : "
                                                     << rselp->lsbConst() << " ] dropped clock ("
                                                     << clk_offset << ")" << endl);
                        return VNUser(0);
                    }
                    clk_offset -= rselp->lsbConst();
                } else {
                    return VNUser(0);
                }
            } else if (AstConcat* catp = VN_CAST(assignp->rhsp(), Concat)) {
                UINFO(9, "CLK DECOMP Concat searching - " << assignp->lhsp() << endl);
                int concat_offset;
                if (!m_concat_visitor.concatOffset(catp, currState->m_last_vsp,
                                                   concat_offset /*ref*/)) {
                    return VNUser(0);
                }
                clk_offset += concat_offset;
            } else if (VN_IS(assignp->rhsp(), VarRef)) {
                UINFO(9, "CLK DECOMP VarRef searching - " << assignp->lhsp() << endl);
            } else {
                return VNUser(0);
            }
            // LHS
            if (const AstSel* lselp = VN_CAST(assignp->lhsp(), Sel)) {
                if (VN_IS(lselp->lsbp(), Const) && VN_IS(lselp->widthp(), Const)) {
                    clk_offset += lselp->lsbConst();
                } else {
                    return VNUser(0);
                }
            } else if (const AstVarRef* vrp = VN_CAST(assignp->lhsp(), VarRef)) {
                if (vrp->dtypep()->width() == 1 && m_seen_clk_vectors) {
                    if (clk_offset != 0) {
                        UINFO(9, "Should only make it here with clk_offset = 0" << endl);
                        return VNUser(0);
                    }
                    UINFO(9, "CLK DECOMP Connecting - " << assignp->lhsp() << endl);
                    UINFO(9, "                   to - " << m_clk_vsp << endl);
                    AstNode* rhsp = assignp->rhsp();
                    rhsp->replaceWith(new AstVarRef(rhsp->fileline(), m_clk_vsp, VAccess::READ));
                    while (V3GraphEdge* edgep = lvertexp->inBeginp()) {
                        VL_DO_DANGLING(edgep->unlinkDelete(), edgep);
                    }
                    new V3GraphEdge(m_graphp, m_clk_vvertexp, lvertexp, 1);
                    m_total_decomposed_clk_vectors++;
                }
            } else {
                return VNUser(0);
            }
            GateClkDecompState nextState(clk_offset, currState->m_last_vsp);
            return lvertexp->iterateCurrentOutEdges(*this, VNUser(&nextState));
        }
        return VNUser(0);
    }

public:
    explicit GateClkDecompGraphVisitor(V3Graph* graphp)
        : GateGraphBaseVisitor{graphp} {}
    virtual ~GateClkDecompGraphVisitor() override {
        V3Stats::addStat("Optimizations, Clocker seen vectors", m_total_seen_clk_vectors);
        V3Stats::addStat("Optimizations, Clocker decomposed vectors",
                         m_total_decomposed_clk_vectors);
    }
    void clkDecomp(GateVarVertex* vvertexp) {
        UINFO(9, "CLK DECOMP Starting Var - " << vvertexp << endl);
        m_seen_clk_vectors = 0;
        m_clk_vsp = vvertexp->varScp();
        m_clk_vvertexp = vvertexp;
        GateClkDecompState nextState(0, m_clk_vsp);
        vvertexp->accept(*this, VNUser(&nextState));
    }
};

void GateVisitor::decomposeClkVectors() {
    UINFO(9, "Starting clock decomposition" << endl);
    AstNode::user2ClearTree();
    GateClkDecompGraphVisitor decomposer(&m_graph);
    for (V3GraphVertex* itp = m_graph.verticesBeginp(); itp; itp = itp->verticesNextp()) {
        if (GateVarVertex* vertp = dynamic_cast<GateVarVertex*>(itp)) {
            AstVarScope* vsp = vertp->varScp();
            if (vsp->varp()->attrClocker() == VVarAttrClocker::CLOCKER_YES) {
                if (vsp->varp()->width() > 1) {
                    UINFO(9, "Clocker > 1 bit, not decomposing: " << vsp << endl);
                } else {
                    UINFO(9, "CLK DECOMP - " << vertp << " : " << vsp << endl);
                    decomposer.clkDecomp(vertp);
                }
            }
        }
    }
}

//######################################################################
// Convert VARSCOPE(ASSIGN(default, VARREF)) to just VARSCOPE(default)

class GateDeassignVisitor final : public GateBaseVisitor {
private:
    // VISITORS
    virtual void visit(AstVarScope* nodep) override {
        if (AstNodeAssign* assp = VN_CAST(nodep->valuep(), NodeAssign)) {
            UINFO(5, " Removeassign " << assp << endl);
            AstNode* valuep = assp->rhsp();
            valuep->unlinkFrBack();
            assp->replaceWith(valuep);
            VL_DO_DANGLING(assp->deleteTree(), assp);
        }
    }
    // Speedups
    virtual void visit(AstVar*) override {}  // Accelerate
    virtual void visit(AstActive*) override {}  // Accelerate
    virtual void visit(AstNode* nodep) override { iterateChildren(nodep); }

public:
    // CONSTRUCTORS
    explicit GateDeassignVisitor(AstNode* nodep) { iterate(nodep); }
    virtual ~GateDeassignVisitor() override = default;
};

//######################################################################
// Gate class functions

void V3Gate::gateAll(AstNetlist* nodep) {
    UINFO(2, __FUNCTION__ << ": " << endl);
    {
        GateVisitor visitor(nodep);
        GateDeassignVisitor deassign(nodep);
    }  // Destruct before checking
    V3Global::dumpCheckGlobalTree("gate", 0, v3Global.opt.dumpTreeLevel(__FILE__) >= 3);
}
