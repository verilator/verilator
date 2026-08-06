// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Multi-threaded code partitioning and ordering
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
//
//  Parallel code ordering
//
//*************************************************************************

#include "V3PchAstNoMT.h"  // VL_MT_DISABLED_CODE_UNIT

#include "V3Ast.h"
#include "V3Control.h"
#include "V3ExecGraph.h"
#include "V3Graph.h"
#include "V3GraphStream.h"
#include "V3OrderCFuncEmitter.h"
#include "V3OrderInternal.h"
#include "V3OrderMTaskGraph.h"

#include <memory>
#include <unordered_map>

VL_DEFINE_DEBUG_FUNCTIONS;

//######################################################################
// Partitioner implementation

// Partitioner takes the fine-grained OrderMoveGraph from V3Order and collapses
// it into a coarse-grained graph of LogicMTask's, each of which contains of set
// of the logic nodes from the fine-grained graph.

static std::unique_ptr<OrderMTaskGraph> partition(OrderMoveGraph& moveGraph) {
    // Build the initial MTask graph. Initially, each MTask just wraps one OrderMoveVertex. We will
    // merge MTasks together and eventually each MTask will wrap a large number of OrderMoveVertex
    // (and the logic nodes therein).
    std::unique_ptr<OrderMTaskGraph> mTaskGraphp = OrderMTaskGraph::build(moveGraph);
    mTaskGraphp->hashGraphDebug("initial MTask graph");

    // Merge nodes that could present data hazards
    OrderMTaskGraph::fixDataHazards(*mTaskGraphp);
    mTaskGraphp->hashGraphDebug("MTask graph after fixDataHazards()");

    // Merge MTask nodes together, repeatedly, until the critical path budget is reached. Coarsens
    // the graph, usually by several orders of magnitude. Some tests disable this for stability,
    // it should always be enabled in production.
    if (v3Global.opt.threadsCoarsen()) {
        const int nThreads = v3Global.opt.threads();
        UASSERT(nThreads >= 2, "Should not reach Partitioner when --threads <= 1");

        // Set critical path limit to roughly totalGraphCost / nThreads. Actually set it slighly
        // lower, by a hardcoded fudge factor. This results in a smaller graph, which helps reduce
        // fragmentation when scheduling them. TODO: What does this sentence mean?
        const uint64_t fudgeNum = 3;
        const uint64_t fudgeDen = 5;
        const uint64_t limit = (mTaskGraphp->totalCost() * fudgeNum) / (nThreads * fudgeDen);
        UINFO(4, "Partitioner set critical path limit = " << limit);

        OrderMTaskGraph::contract(*mTaskGraphp, limit);
        mTaskGraphp->hashGraphDebug("MTask graph after contract()");
    }

    mTaskGraphp->removeTransitiveEdges();
    mTaskGraphp->hashGraphDebug("MTask graph after removeTransitiveEdges()");

    // Remove MTasks that have no logic in it, rerouting the edges. Set user to indicate the
    // mtask on every underlying OrderMoveVertex. Clear vertex lists (used later).
    moveGraph.userClearVertices();
    for (V3GraphVertex* const vtxp : mTaskGraphp->vertices().unlinkable()) {
        LogicMTask* const mtaskp = vtxp->as<LogicMTask>();
        OrderMoveVertex::List& vertexList = mtaskp->vertexList();
        // Check if MTask is empty
        bool empty = true;
        for (const OrderMoveVertex& mVtx : vertexList) {
            if (mVtx.logicp()) {
                empty = false;
                break;
            }
        }
        // If empty remove it now
        if (empty) {
            mtaskp->rerouteEdges(mTaskGraphp.get());
            VL_DO_DANGLING(mtaskp->unlinkDelete(mTaskGraphp.get()), mtaskp);
            continue;
        }
        // Annotate the underlying OrderMoveVertex vertices and unlink them
        while (OrderMoveVertex* const mVtxp = vertexList.unlinkFront()) mVtxp->userp(mtaskp);
    }
    mTaskGraphp->removeRedundantEdgesSum(&V3GraphEdge::followAlwaysTrue);

    // Return the resulting MTask graph
    return mTaskGraphp;
}

//######################################################################
// DpiThreadsVisitor - Finds number of threads used by an ExecMTask

class DpiThreadsVisitor final : public VNVisitorConst {
    int m_threads = 1;  // Max number of threads used by this mtask

    // METHODS
    void visit(AstCFunc* nodep) override {
        m_threads = std::max(m_threads, V3Control::getHierWorkers(nodep->cname()));
        iterateChildrenConst(nodep);
    }
    void visit(AstNodeCCall* nodep) override { iterateConst(nodep->funcp()); }
    void visit(AstNode* nodep) override { iterateChildrenConst(nodep); }

    // CONSTRUCTORS
    explicit DpiThreadsVisitor(AstCFunc* nodep) { iterateConst(nodep); }
    ~DpiThreadsVisitor() override = default;
    VL_UNCOPYABLE(DpiThreadsVisitor);

public:
    // Number of threads occupied by the given MTask
    static int apply(const ExecMTask* mTaskp) {
        return DpiThreadsVisitor{mTaskp->funcp()}.m_threads;
    }
};

//######################################################################
// Entry point

AstNodeStmt* V3Order::createParallel(OrderMoveGraph& moveGraph, const std::string& tag,
                                     bool slow) {
    UINFO(2, "  Constructing parallel code for '" + tag + "'");

    // For nondeterminism debugging
    moveGraph.hashGraphDebug("V3Order::createParallel input OrderMoveGraph");
    moveGraph.orderGraph().hashGraphDebug("V3Order::createParallel input OrderGraph");

    // Partition moveGraph into LogicMTask's. The partitioner will set userp() on each logic
    // vertex in the moveGraph to the MTask it belongs to.
    const std::unique_ptr<OrderMTaskGraph> mTaskGraphp = partition(moveGraph);
    if (dumpGraphLevel() >= 9) moveGraph.dumpDotFilePrefixed(tag + "_ordermv_mtasks");

    // Some variable OrderMoveVertices are not assigned to an MTask. Reroute and delete these.
    for (V3GraphVertex* const vtxp : moveGraph.vertices().unlinkable()) {
        OrderMoveVertex* const mVtxp = vtxp->as<OrderMoveVertex>();
        if (!mVtxp->userp()) {
            UASSERT_OBJ(!mVtxp->logicp(), mVtxp, "Logic OrderMoveVertex not assigned to mtask");
            mVtxp->rerouteEdges(&moveGraph);
            VL_DO_DANGLING(mVtxp->unlinkDelete(&moveGraph), mVtxp);
        }
    }

    // Remove all edges from the move graph that cross between MTasks. Add logic to MTask lists.
    for (V3GraphVertex& vtx : moveGraph.vertices()) {
        OrderMoveVertex* const mVtxp = vtx.as<OrderMoveVertex>();
        LogicMTask* const mtaskp = static_cast<LogicMTask*>(mVtxp->userp());
        // Add to list in MTask, in MoveGraph order. This should not be necessary, but see #4993.
        mtaskp->vertexList().linkBack(mVtxp);
        // Remove edges crossing between MTasks
        for (V3GraphEdge* const edgep : mVtxp->outEdges().unlinkable()) {
            const OrderMoveVertex* const toMVtxp = edgep->top()->as<OrderMoveVertex>();
            if (mtaskp != toMVtxp->userp()) VL_DO_DANGLING(edgep->unlinkDelete(), edgep);
        }
    }
    if (dumpGraphLevel() >= 9) moveGraph.dumpDotFilePrefixed(tag + "_ordermv_pruned");

    // Create the AstExecGraph node which represents the execution of the MTask graph.
    FileLine* const flp = v3Global.rootp()->fileline();
    AstScope* const scopep = v3Global.rootp()->topScopep()->scopep();
    AstExecGraph* const execGraphp = new AstExecGraph{flp, tag};
    V3Graph* const depGraphp = execGraphp->depGraphp();

    // Translate the LogicMTask graph into the corresponding ExecMTask graph,
    // which will outlive ordering.
    std::unordered_map<const LogicMTask*, ExecMTask*> logicMTaskToExecMTask;
    OrderMoveGraphSerializer serializer{moveGraph};
    V3OrderCFuncEmitter emitter{tag, slow};
    // Sort LogicMTask vertices by their serial IDs.
    struct MTaskVxIdLessThan final {
        bool operator()(const V3GraphVertex* lhsp, const V3GraphVertex* rhsp) const {
            return lhsp->as<LogicMTask>()->id() < rhsp->as<LogicMTask>()->id();
        }
    };
    GraphStream<MTaskVxIdLessThan> mtaskStream{mTaskGraphp.get()};
    while (const V3GraphVertex* const vtxp = mtaskStream.nextp()) {
        const LogicMTask* const cMTaskp = vtxp->as<LogicMTask>();
        LogicMTask* const mTaskp = const_cast<LogicMTask*>(cMTaskp);

        // Add initially ready vertices within this MTask to the serializer as seeds,
        // and unlink them from the vertex list in the MTask as we go. (The serializer
        // uses the list links in the vertex, so must unlink it here.)
        while (OrderMoveVertex* const mVtxp = mTaskp->vertexList().unlinkFront()) {
            if (mVtxp->inEmpty()) serializer.addSeed(mVtxp);
        }

        // Emit all logic within the MTask as they become ready
        OrderMoveDomScope* prevDomScopep = nullptr;
        while (OrderMoveVertex* const mVtxp = serializer.getNext()) {
            // We only really care about logic vertices
            if (OrderLogicVertex* const logicp = mVtxp->logicp()) {
                // Force a new function if the domain or scope changed, for better combining.
                OrderMoveDomScope* const domScopep = &mVtxp->domScope();
                if (domScopep != prevDomScopep) emitter.forceNewFunction();
                prevDomScopep = domScopep;
                // Emit the logic under this vertex
                emitter.emitLogic(logicp);
            }
            // Can delete the vertex now
            VL_DO_DANGLING(mVtxp->unlinkDelete(&moveGraph), mVtxp);
        }

        // Create the ExecMTask
        ExecMTask* const execMTaskp = new ExecMTask{execGraphp, scopep, emitter.getStmts()};
        if (!v3Global.opt.hierBlocks().empty()) {
            execMTaskp->threads(DpiThreadsVisitor::apply(execMTaskp));
        }
        const bool newEntry = logicMTaskToExecMTask.emplace(mTaskp, execMTaskp).second;
        UASSERT_OBJ(newEntry, mTaskp, "LogicMTasks should be processed in dependencyorder");
        UINFO(3, "Final '" << tag << "' LogicMTask " << mTaskp->id() << " maps to ExecMTask"
                           << execMTaskp->id());

        // For code analysis purposes, we can pretend the AstExecGraph runs the
        // MTasks sequentially, in some topological order that respects edges.
        // The order they are created here happens to be just such an order.
        AstCCall* const callp = new AstCCall{flp, execMTaskp->funcp()};
        callp->dtypeSetVoid();
        execGraphp->addStmtsp(callp->makeStmt());

        // Add the dependency edges between ExecMTasks
        for (const V3GraphEdge& edge : mTaskp->inEdges()) {
            const V3GraphVertex* fromVxp = edge.fromp();
            const LogicMTask* const fromp = fromVxp->as<const LogicMTask>();
            new V3GraphEdge{depGraphp, logicMTaskToExecMTask.at(fromp), execMTaskp, 1};
        }
    }

    // Delete the remaining variable vertices
    for (V3GraphVertex* const vtxp : moveGraph.vertices().unlinkable()) {
        if (!vtxp->as<OrderMoveVertex>()->logicp()) {
            VL_DO_DANGLING(vtxp->unlinkDelete(&moveGraph), vtxp);
        }
    }

    return execGraphp;
}
