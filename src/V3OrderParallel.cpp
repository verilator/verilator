// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Block code ordering
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
//
//  Parallel code ordering
//
//*************************************************************************

#include "V3PchAstNoMT.h"  // VL_MT_DISABLED_CODE_UNIT

#include "V3Graph.h"
#include "V3GraphStream.h"
#include "V3List.h"
#include "V3OrderCFuncEmitter.h"
#include "V3OrderInternal.h"
#include "V3OrderMoveGraphBuilder.h"
#include "V3Partition.h"
#include "V3PartitionGraph.h"

#include <unordered_map>
#include <vector>

VL_DEFINE_DEBUG_FUNCTIONS;

// Sort MTaskMoveVertex vertices by domain, then by scope, based on teh order they are encountered
class OrderVerticesByDomainThenScope final {
    mutable uint64_t m_nextId = 0;  // Next id to use
    mutable std::unordered_map<const void*, uint64_t> m_id;  // Map from ptr to id

    // Map a pointer into an id, for deterministic results
    uint64_t findId(const void* ptrp) const {
        const auto pair = m_id.emplace(ptrp, m_nextId);
        if (pair.second) ++m_nextId;
        return pair.first->second;
    }

public:
    bool operator()(const V3GraphVertex* lhsp, const V3GraphVertex* rhsp) const {
        const MTaskMoveVertex* const l_vxp = lhsp->as<MTaskMoveVertex>();
        const MTaskMoveVertex* const r_vxp = rhsp->as<MTaskMoveVertex>();
        const uint64_t l_id = findId(l_vxp->domainp());
        const uint64_t r_id = findId(r_vxp->domainp());
        if (l_id != r_id) return l_id < r_id;
        return findId(l_vxp->scopep()) < findId(r_vxp->scopep());
    }
};

// Sort AbstractMTask vertices by their serial IDs.
struct MTaskVxIdLessThan final {
    bool operator()(const V3GraphVertex* lhsp, const V3GraphVertex* rhsp) const {
        return lhsp->as<AbstractLogicMTask>()->id() < rhsp->as<AbstractLogicMTask>()->id();
    }
};

AstExecGraph* V3Order::createParallel(const OrderGraph& graph, const std::string& tag,
                                      const TrigToSenMap& trigToSen, bool slow) {
    UINFO(2, "  Constructing parallel code for '" + tag + "'");

    // For nondeterminism debug:
    V3Partition::hashGraphDebug(&graph, "V3Order's m_graph");

    // We already produced a graph of every var, input, and logic
    // block and all dependencies; this is 'm_graph'.
    //
    // Now, starting from m_graph, make a slightly-coarsened graph representing
    // only logic, and discarding edges we know we can ignore.
    // This is quite similar to the 'm_pomGraph' of the serial code gen:
    const std::unique_ptr<V3Graph> logicGraphp
        = V3OrderMoveGraphBuilder<MTaskMoveVertex>::apply(graph, trigToSen);

    // Needed? We do this for m_pomGraph in serial mode, so do it here too:
    logicGraphp->removeRedundantEdgesMax(&V3GraphEdge::followAlwaysTrue);

    // Partition logicGraph into LogicMTask's. The partitioner will annotate
    // each vertex in logicGraph with a 'color' which is really an mtask ID
    // in this context.
    V3Partition partitioner{&graph, logicGraphp.get()};
    V3Graph mtasks;
    partitioner.go(&mtasks);

    // processMTask* routines schedule threaded execution
    struct MTaskState final {
        AstMTaskBody* m_mtaskBodyp = nullptr;
        std::list<const OrderLogicVertex*> m_logics;
        ExecMTask* m_execMTaskp = nullptr;
        MTaskState() = default;
    };

    std::unordered_map<unsigned /*mtask id*/, MTaskState> mtaskStates;

    // Iterate through the entire logicGraph. For each logic node,
    // attach it to a per-MTask ordered list of logic nodes.
    // This is the order we'll execute logic nodes within the MTask.
    //
    // MTasks may span scopes and domains, so sort by both here:
    GraphStream<OrderVerticesByDomainThenScope> logicStream{logicGraphp.get()};
    while (const V3GraphVertex* const vtxp = logicStream.nextp()) {
        const MTaskMoveVertex* const movep = vtxp->as<MTaskMoveVertex>();
        // Only care about logic vertices
        if (!movep->logicp()) continue;

        const unsigned mtaskId = movep->color();
        UASSERT(mtaskId > 0, "Every MTaskMoveVertex should have an mtask assignment >0");

        // Add this logic to the per-mtask order
        mtaskStates[mtaskId].m_logics.push_back(movep->logicp());

        // Since we happen to be iterating over every logic node,
        // take this opportunity to annotate each AstVar with the id's
        // of mtasks that consume it and produce it. We'll use this
        // information in V3EmitC when we lay out var's in memory.
        const OrderLogicVertex* const logicp = movep->logicp();
        for (const V3GraphEdge* edgep = logicp->inBeginp(); edgep; edgep = edgep->inNextp()) {
            const OrderVarVertex* const pre_varp = edgep->fromp()->cast<const OrderVarVertex>();
            if (!pre_varp) continue;
            AstVar* const varp = pre_varp->vscp()->varp();
            // varp depends on logicp, so logicp produces varp,
            // and vice-versa below
            varp->addProducingMTaskId(mtaskId);
        }
        for (const V3GraphEdge* edgep = logicp->outBeginp(); edgep; edgep = edgep->outNextp()) {
            const OrderVarVertex* const post_varp = edgep->top()->cast<const OrderVarVertex>();
            if (!post_varp) continue;
            AstVar* const varp = post_varp->vscp()->varp();
            varp->addConsumingMTaskId(mtaskId);
        }
        // TODO? We ignore IO vars here, so those will have empty mtask
        // signatures. But we could also give those mtask signatures.
    }

    // Create the AstExecGraph node which represents the execution
    // of the MTask graph.
    FileLine* const rootFlp = v3Global.rootp()->fileline();
    AstExecGraph* const execGraphp = new AstExecGraph{rootFlp, tag};

    // Create CFuncs and bodies for each MTask.
    V3OrderCFuncEmitter emitter{tag, slow};
    GraphStream<MTaskVxIdLessThan> mtaskStream{&mtasks};
    while (const V3GraphVertex* const vtxp = mtaskStream.nextp()) {
        const AbstractLogicMTask* const mtaskp = vtxp->as<AbstractLogicMTask>();

        // Create a body for this mtask
        AstMTaskBody* const bodyp = new AstMTaskBody{rootFlp};
        MTaskState& state = mtaskStates[mtaskp->id()];
        state.m_mtaskBodyp = bodyp;

        // Emit functions with this MTaks's logic, and call them in the body.
        for (const OrderLogicVertex* lVtxp : state.m_logics) emitter.emitLogic(lVtxp);
        for (AstActive* const activep : emitter.getAndClearActiveps()) bodyp->addStmtsp(activep);

        // Translate the LogicMTask graph into the corresponding ExecMTask
        // graph, which will outlive V3Order and persist for the remainder
        // of verilator's processing.
        // - The LogicMTask graph points to MTaskMoveVertex's
        //   and OrderLogicVertex's which are ephemeral to V3Order.
        // - The ExecMTask graph and the AstMTaskBody's produced here
        //   persist until code generation time.
        V3Graph* const depGraphp = execGraphp->depGraphp();
        state.m_execMTaskp = new ExecMTask{depGraphp, bodyp, mtaskp->id()};
        // Cross-link each ExecMTask and MTaskBody
        //  Q: Why even have two objects?
        //  A: One is an AstNode, the other is a GraphVertex,
        //     to combine them would involve multiple inheritance...
        state.m_mtaskBodyp->execMTaskp(state.m_execMTaskp);
        for (V3GraphEdge* inp = mtaskp->inBeginp(); inp; inp = inp->inNextp()) {
            const V3GraphVertex* fromVxp = inp->fromp();
            const AbstractLogicMTask* const fromp
                = static_cast<const AbstractLogicMTask*>(fromVxp);
            const MTaskState& fromState = mtaskStates[fromp->id()];
            new V3GraphEdge{depGraphp, fromState.m_execMTaskp, state.m_execMTaskp, 1};
        }
        execGraphp->addMTaskBodiesp(bodyp);
    }

    return execGraphp;
}
