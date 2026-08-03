// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: OrderMTask graph construction
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

#include "V3PchAstNoMT.h"  // VL_MT_DISABLED_CODE_UNIT

#include "V3OrderMTaskGraph.h"

#include "V3Global.h"
#include "V3InstrCount.h"

VL_DEFINE_DEBUG_FUNCTIONS;

//######################################################################
// OrderMTaskGraph

OrderMTaskGraph::OrderMTaskGraph(OrderMoveGraph& moveGraph)
    : m_moveGraph{moveGraph}
    , m_entryp{new LogicMTask{*this, nullptr}}
    , m_exitp{new LogicMTask{*this, nullptr}}
    , m_forwardPropagator{v3Global.opt.debugPartition()}
    , m_reversePropagator{v3Global.opt.debugPartition()} {}

uint64_t OrderMTaskGraph::totalCost() const {
    uint64_t cost = 0;
    for (const V3GraphVertex& vtx : vertices()) cost += static_cast<const LogicMTask&>(vtx).cost();
    return cost;
}

//######################################################################
// LogicMTask

uint32_t LogicMTask::s_nextId = 1;  // Start at 1, so that 0 indicates no mtask.

LogicMTask::LogicMTask(OrderMTaskGraph& graph, OrderMoveVertex* mVtxp)
    : V3GraphVertex{&graph} {
    UASSERT(s_nextId < 0xFFFFFFFFUL, "Too many LogicMTask instances");
    if (!mVtxp) return;
    m_mVertices.linkBack(mVtxp);
    if (const OrderLogicVertex* const olvp = mVtxp->logicp()) {
        m_cost += V3InstrCount::count(olvp->nodep(), true);
    }
}

//######################################################################
// OrderMTaskGraphBuilder

class OrderMTaskGraphBuilder final {
    // NODE STATE
    // Used by V3InstrCount::count within the LogicMTask constructor only
    const VNUser1InUse m_user1InUse;

    // MEMBERS
    OrderMTaskGraph& m_mtaskGraph;  // Output OrderMTaskGraph

    // METHODS

    // Predicate function to determine what OrderMoveVertex to bypass when constructing the MTask
    // graph. The OrderMoveGraph is a bipartite graph of:
    // - 1. OrderMoveVertex instances containing logic via OrderLogicVertex
    //      (OrderMoveVertex::logicp() != nullptr)
    // - 2. OrderMoveVertex instances containing an (OrderVarVertex, domain) pair
    // The goal is to order the logic vertices. The second type of variable/domain vertices only
    // carry dependencies and are eventually discarded. In order to reduce the working set size,
    // we 'bypass' and not create LogicMTask vertices for some variable vertices, and instead add
    // the transitive dependencies directly, but only if adding the transitive edges directly does
    // not require more dependency edges than keeping the intermediate vertex. That is, we bypass a
    // variable vertex if fanIn * fanOut <= fanIn + fanOut. This is true if fanIn or fanOut are 1,
    // or if they are both 2. This can significantly reduce the initial size of OrderMTaskGraph.
    static bool bypassOk(OrderMoveVertex* mvtxp) {
        // Need to keep all logic vertices
        if (mvtxp->logicp()) return false;
        // Count fan-in, up to 3
        unsigned fanIn = 0;
        auto& inEdges = mvtxp->inEdges();
        for (auto it = inEdges.begin(); it != inEdges.end(); ++it) {
            if (++fanIn == 3) break;
        }
        // If fanIn no more than one, bypass
        if (fanIn <= 1) return true;
        // Count fan-out, up to 3
        unsigned fanOut = 0;
        auto& outEdges = mvtxp->outEdges();
        for (auto it = outEdges.begin(); it != outEdges.end(); ++it) {
            if (++fanOut == 3) break;
        }
        // If fan-out no more than one, bypass
        if (fanOut <= 1) return true;
        // They can only be (2, 2), (2, 3), (3, 2), (3, 3) at this point, bypass if (2, 2)
        return fanIn + fanOut == 4;
    }

    // Add an edge to the graph, if there is not already an edge between the two vertices.
    void addEdge(LogicMTask& src, LogicMTask& dst) {
        UASSERT_OBJ(&src != &dst, &src, "Should not create self-edges");
        if (src.hasRelativeMTask(&dst)) return;  // Don't create redundant edges.
        new MTaskEdge{&m_mtaskGraph, &src, &dst, 1};
    }

    // CONSTRUCTORS
    explicit OrderMTaskGraphBuilder(OrderMTaskGraph& mtaskGraph)
        : m_mtaskGraph{mtaskGraph} {

        // Create the LogicMTasks for each OrderMoveVertex
        for (V3GraphVertex& vtx : mtaskGraph.moveGraph().vertices()) {
            OrderMoveVertex& mVtx = static_cast<OrderMoveVertex&>(vtx);
            if (bypassOk(&mVtx)) {
                mVtx.userp(nullptr);  // Set to nullptr to mark as bypassed
            } else {
                mVtx.userp(new LogicMTask{mtaskGraph, &mVtx});  // Create vertex and set userp
            }
        }

        LogicMTask& entry = *mtaskGraph.entryp();
        LogicMTask& exit = *mtaskGraph.exitp();

        // Create the MTask dependency edges based on the OrderMoveGraph dependencies
        for (V3GraphVertex& vtx : mtaskGraph.vertices()) {
            LogicMTask& mtask = static_cast<LogicMTask&>(vtx);

            // Entry and exit vertices handled separately
            if (VL_UNLIKELY((&mtask == &entry) || (&mtask == &exit))) continue;

            OrderMoveVertex::List& vertexList = mtask.vertexList();
            // At this point, there should only be one OrderMoveVertex per LogicMTask
            UASSERT_OBJ(vertexList.hasSingleElement(), &mtask, "Multiple OrderMoveVertex");
            OrderMoveVertex* const mVtxp = vertexList.frontp();
            UASSERT_OBJ(mVtxp->userp(), &mtask, "Bypassed OrderMoveVertex should not have MTask");

            // Iterate downstream direct dependents
            for (const V3GraphEdge& dEdge : mVtxp->outEdges()) {
                V3GraphVertex* const top = dEdge.top();

                // If the opposite end of the edge is not a bypassed vertex, add direct dependency
                if (LogicMTask* const otherp = static_cast<LogicMTask*>(top->userp())) {
                    addEdge(mtask, *otherp);
                    continue;
                }

                // The opposite end of the edge is a bypassed vertex, add transitive dependencies
                for (const V3GraphEdge& tEdge : top->outEdges()) {
                    LogicMTask* const transp = static_cast<LogicMTask*>(tEdge.top()->userp());
                    // The Move graph is bipartite (logic <-> var), and logic is never
                    // bypassed, hence 'transp' must be non-nullptr.
                    UASSERT_OBJ(transp, mVtxp, "This cannot be a bypassed vertex");
                    addEdge(mtask, *transp);
                }
            }
        }

        // Create Dependencies to/from the entry/exit vertices, so all vertices are
        // reachable from the entry point and flow to the exit point.
        for (V3GraphVertex& vtx : mtaskGraph.vertices()) {
            LogicMTask& mtask = static_cast<LogicMTask&>(vtx);
            if (VL_UNLIKELY((&mtask == &entry) || (&mtask == &exit))) continue;
            // Add the entry/exit edges if not otherwise connected
            if (mtask.inEmpty()) addEdge(entry, mtask);
            if (mtask.outEmpty()) addEdge(mtask, exit);
        }
    }
    ~OrderMTaskGraphBuilder() = default;
    VL_UNCOPYABLE(OrderMTaskGraphBuilder);
    VL_UNMOVABLE(OrderMTaskGraphBuilder);

public:
    static void apply(OrderMTaskGraph& mtaskGraph) { OrderMTaskGraphBuilder{mtaskGraph}; }
};

std::unique_ptr<OrderMTaskGraph> OrderMTaskGraph::build(OrderMoveGraph& moveGraph) {
    std::unique_ptr<OrderMTaskGraph> resp{new OrderMTaskGraph{moveGraph}};
    OrderMTaskGraphBuilder::apply(*resp);
    return resp;
}
