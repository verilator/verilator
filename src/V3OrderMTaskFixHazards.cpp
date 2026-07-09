// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Multi-threaded MTask graph data hazard fixing
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

#include "V3Control.h"
#include "V3Global.h"
#include "V3Graph.h"
#include "V3GraphStream.h"
#include "V3OrderGraph.h"
#include "V3OrderMTaskGraph.h"

#include <algorithm>
#include <map>
#include <set>
#include <vector>

VL_DEFINE_DEBUG_FUNCTIONS;

//######################################################################
// DpiImportCallVisitor

// Scan node, indicate whether it contains a call to a DPI imported routine.
class DpiImportCallVisitor final : public VNVisitor {
    bool m_hasDpiHazard = false;  // Found a DPI import call.
    bool m_tracingCall = false;  // Iterating into a CCall to a CFunc
    // METHODS
    void visit(AstCFunc* nodep) override {
        if (!m_tracingCall) return;
        m_tracingCall = false;
        if (nodep->dpiImportWrapper()) {
            if (nodep->dpiPure() ? !v3Global.opt.threadsDpiPure()
                                 : !v3Global.opt.threadsDpiUnpure()) {
                // If hierarchical DPI wrapper cost is not found or is of a 0 cost,
                // we have a normal DPI which induces DPI hazard by default.
                m_hasDpiHazard = V3Control::getProfileData(nodep->cname()) == 0;
                UINFO(9, "DPI wrapper '" << nodep->cname()
                                         << "' has dpi hazard = " << m_hasDpiHazard);
            }
        }
        iterateChildren(nodep);
    }
    void visit(AstNodeCCall* nodep) override {
        iterateChildren(nodep);
        // Enter the function and trace it
        m_tracingCall = true;
        iterate(nodep->funcp());
    }
    void visit(AstNode* nodep) override { iterateChildren(nodep); }

    // CONSTRUCTORS
    explicit DpiImportCallVisitor(AstNode* nodep) { iterate(nodep); }

public:
    static bool hasDpiHazard(AstNode* nodep) { return DpiImportCallVisitor{nodep}.m_hasDpiHazard; }
};

//######################################################################
// FixDataHazards

class FixDataHazards final {
    //
    // Fix data hazards in the MTask graph.
    //
    // The fine-grained graph from V3Order may contain data hazards which are
    // not a problem for serial mode, but which would be a problem in parallel
    // mode.
    //
    // There are basically two classes: unordered pairs of writes, and
    // unordered write-read pairs. We fix both here, with a combination of
    // MTask-merges and new edges to ensure no such unordered pairs remain.
    //
    // ABOUT UNORDERED WRITE-WRITE PAIRS
    //
    //   The V3Order dependency graph treats these as unordered events:
    //
    //    a)  sig[15:8] = stuff;
    //          ...
    //    b)  sig[7:0]  = other_stuff;
    //
    //   Seems OK right? They are writes to disjoint bits of the same
    //   signal. They can run in either order, in serial mode, and the result
    //   will be the same.
    //
    //   The resulting C code for each of this isn't a pure write, it's
    //   actually an R-M-W sequence:
    //
    //    a)  sig = (sig & 0xff)   | (0xff00 & (stuff << 8));
    //          ...
    //    b)  sig = (sig & 0xff00) | (0xff & other_stuff);
    //
    //   In serial mode, order doesn't matter so long as these run serially.
    //   In parallel mode, we must serialize these RMW's to avoid a race.
    //
    //   We don't actually check here if each write would involve an R-M-W, we
    //   just assume that it would. If this routine ever causes a drastic
    //   increase in critical path, it could be optimized to make a better
    //   prediction (with all the risk that word implies!) about whether a
    //   given write is likely to turn into an R-M-W.
    //
    // ABOUT UNORDERED WRITE-READ PAIRS
    //
    //   If we don't put unordered write-read pairs into some order at Verilation
    //   time, we risk a runtime race.
    //
    //   How do such unordered writer/reader pairs happen? Here's a partial list
    //   of scenarios:
    //
    //   Case 1: Circular logic
    //
    //     If the design has circular logic, V3Order has by now generated some
    //     dependency cycles, and also cut some of the edges to make it
    //     acyclic.
    //
    //     For serial mode, that was fine. We can break logic circles at an
    //     arbitrary point. At runtime, we'll repeat the _eval() until no
    //     changes are detected, which papers over the discarded dependency.
    //
    //     For parallel mode, this situation can lead to unordered reads and
    //     writes of the same variable, causing a data race. For example if the
    //     original code is this:
    //
    //       assign b = b | a << 2;
    //       assign out = b;
    //
    //     ... there's originally a dependency edge which records that 'b'
    //     depends on the first assign. V3Order may cut this edge, making the
    //     statements unordered. In serial mode that's fine, they can run in
    //     either order. In parallel mode it's a reader/writer race.
    //
    //   Case 2: Race Condition in Verilog Sources
    //
    //     If the input has races, eg. blocking assignments in always blocks
    //     that share variables, the graph at this point will contain unordered
    //     writes and reads (or unordered write-write pairs) reflecting that.

    // TYPES
    // Sort LogicMTask objects into deterministic order by calling id()
    // which is a unique and stable serial number.
    struct MTaskIdLessThan final {
        bool operator()(const LogicMTask* lhsp, const LogicMTask* rhsp) const {
            return *lhsp < *rhsp;
        }
    };
    using TasksByRank = std::map<uint32_t /*rank*/, std::set<LogicMTask*, MTaskIdLessThan>>;

    // MEMBERS
    OrderMTaskGraph& m_mTaskGraph;  // The Mtask graph

    // METHODS

    // Redirect all edges of 'donorp' onto 'recipientp'
    static void redirectEdgesFrom(LogicMTask* recipientp, LogicMTask* donorp) {
        // Process outgoing edges
        while (MTaskEdge* const edgep = static_cast<MTaskEdge*>(donorp->outEdges().frontp())) {
            LogicMTask* const top = edgep->toMTaskp();
            top->removeRelativeEdge<GraphWay::REVERSE>(edgep);

            // If an edge already exists between recipient and sink of donor, drop the duplicate.
            if (recipientp->hasRelativeMTask(top)) {
                VL_DO_DANGLING(edgep->unlinkDelete(), edgep);
                continue;
            }

            // Otherwise redirect the edge from donorp->top to recipientp->top.
            edgep->relinkFromp(recipientp);
            recipientp->addRelativeMTask(top);
            recipientp->stealRelativeEdge<GraphWay::FORWARD>(edgep);
            top->addRelativeEdge<GraphWay::REVERSE>(edgep);
        }

        // Process incoming edges
        while (MTaskEdge* const edgep = static_cast<MTaskEdge*>(donorp->inEdges().frontp())) {
            LogicMTask* const fromp = edgep->fromMTaskp();
            fromp->removeRelativeMTask(donorp);
            fromp->removeRelativeEdge<GraphWay::FORWARD>(edgep);

            // If an edge already exists between recipient and source of donor, drop the duplicate.
            if (fromp->hasRelativeMTask(recipientp)) {
                VL_DO_DANGLING(edgep->unlinkDelete(), edgep);
                continue;
            }

            // Otherwise redirect the edge from fromp->donorp to fromp->recipientp.
            edgep->relinkTop(recipientp);
            fromp->addRelativeMTask(recipientp);
            fromp->addRelativeEdge<GraphWay::FORWARD>(edgep);
            recipientp->stealRelativeEdge<GraphWay::REVERSE>(edgep);
        }
    }

    void findAdjacentTasks(const OrderVarStdVertex* varVtxp, TasksByRank& tasksByRank) {
        // Find all writer tasks for this variable, group by rank.
        for (const V3GraphEdge& edge : varVtxp->inEdges()) {
            if (const auto* const logicVtxp = edge.fromp()->cast<OrderLogicVertex>()) {
                LogicMTask* const writerMtaskp = static_cast<LogicMTask*>(logicVtxp->userp());
                tasksByRank[writerMtaskp->rank()].insert(writerMtaskp);
            }
        }
        // Note: Find all reader tasks for this variable, group by rank.
        // There was "broken" code here to find readers, but fixing it to
        // work properly harmed performance on some tests, see issue #3360.
    }

    void mergeSameRankTasks(const TasksByRank& tasksByRank) {
        LogicMTask* lastRecipientp = nullptr;
        for (const auto& pair : tasksByRank) {
            // Find the largest node at this rank, merge into it.  (If we
            // happen to find a huge node, this saves time in
            // redirectEdgesFrom() versus merging into an arbitrary node.)
            LogicMTask* recipientp = nullptr;
            for (LogicMTask* const mtaskp : pair.second) {
                if (!recipientp || (recipientp->cost() < mtaskp->cost())) recipientp = mtaskp;
            }
            UASSERT_OBJ(!lastRecipientp || (lastRecipientp->rank() < recipientp->rank()),
                        recipientp, "Merging must be on lower rank");

            for (LogicMTask* const donorp : pair.second) {
                // Merge donor into recipient.
                if (donorp == recipientp) continue;
                // Fix up the map, so donor's OLVs map to recipientp
                for (const OrderMoveVertex& vtx : donorp->vertexList()) {
                    vtx.logicp()->userp(recipientp);
                }
                // Move all vertices from donorp to recipientp
                recipientp->moveAllVerticesFrom(donorp);
                // Redirect edges from donorp to recipientp
                redirectEdgesFrom(recipientp, donorp);
                // Remove donorp from the graph
                VL_DO_DANGLING(donorp->unlinkDelete(&m_mTaskGraph), donorp);
            }

            if (lastRecipientp && !lastRecipientp->hasRelativeMTask(recipientp)) {
                new MTaskEdge{&m_mTaskGraph, lastRecipientp, recipientp, 1};
            }
            lastRecipientp = recipientp;
        }
    }

    bool hasDpiHazard(LogicMTask* mtaskp) {
        for (const OrderMoveVertex& mVtx : mtaskp->vertexList()) {
            OrderLogicVertex* const lvtxp = mVtx.logicp();
            if (!lvtxp) continue;
            // NOTE: We don't handle DPI exports. If testbench code calls a DPI-exported function
            // at any time during eval() we may have a data hazard. (Likewise in non-threaded mode
            // if an export messes with an ordered variable we're broken.)

            // Find all calls to DPI-imported functions, we can put those into a serial order at
            // least. That should solve the most likely DPI-related data hazards.
            if (DpiImportCallVisitor::hasDpiHazard(lvtxp->nodep())) return true;
        }
        return false;
    }

    // CONSTRUCTOR
    FixDataHazards(OrderMTaskGraph& mTaskGraph)
        : m_mTaskGraph{mTaskGraph} {
        // Rank the graph. DGS is faster than V3GraphAlg's recursive rank, and also allows us to
        // set up the OrderLogicVertex -> LogicMTask map at the same time.
        {
            GraphStreamUnordered serialize{&m_mTaskGraph};
            while (LogicMTask* const mtaskp
                   = const_cast<LogicMTask*>(static_cast<const LogicMTask*>(serialize.nextp()))) {
                // Compute and assign rank
                uint32_t rank = 0;
                for (V3GraphEdge& edge : mtaskp->inEdges()) {
                    rank = std::max(edge.fromp()->rank() + 1, rank);
                }
                mtaskp->rank(rank);

                // Set up the OrderLogicVertex -> LogicMTask map
                // Entry and exit MTasks have no MTaskMoveVertices under them, so move on
                if (mtaskp->vertexList().empty()) continue;
                // Otherwise there should be only one OrderMoveVertex in each MTask at this stage
                const OrderMoveVertex::List& vertexList = mtaskp->vertexList();
                UASSERT_OBJ(vertexList.hasSingleElement(), mtaskp, "Multiple OrderMoveVertex");
                const OrderMoveVertex* const mVtxp = vertexList.frontp();
                // Set up mapping back to the MTask from the OrderLogicVertex
                if (OrderLogicVertex* const lvtxp = mVtxp->logicp()) lvtxp->userp(mtaskp);
            }
        }

        // Gather all variables. SystemC vars will be handled slightly specially, so keep separate.
        const OrderGraph& orderGraph = m_mTaskGraph.moveGraph().orderGraph();
        std::vector<const OrderVarStdVertex*> regularVars;
        std::vector<const OrderVarStdVertex*> systemCVars;
        for (const V3GraphVertex& vtx : orderGraph.vertices()) {
            // Only consider OrderVarStdVertex which reflects
            // an actual lvalue assignment; the others do not.
            if (const OrderVarStdVertex* const vvtxp = vtx.cast<const OrderVarStdVertex>()) {
                if (vvtxp->vscp()->varp()->isSc()) {
                    systemCVars.push_back(vvtxp);
                } else {
                    regularVars.push_back(vvtxp);
                }
            }
        }

        // For each OrderVarVertex, look at its writer and reader MTasks.
        //
        // If there's a set of writers and readers at the same rank, we
        // know these are unordered with respect to one another, so merge
        // those MTasks all together.
        //
        // At this point, we have at most one merged mtask per rank (for a
        // given OVV.) Create edges across these remaining MTasks to ensure
        // they run in serial order (going along with the existing ranks.)
        //
        // NOTE: we don't update the CP's stored in the LogicMTasks to
        // reflect the changes we make to the graph. That's OK, as we
        // haven't yet initialized CPs when we call this routine.
        for (const OrderVarStdVertex* const varVtxp : regularVars) {
            // Build a set of MTasks, per rank, which access this var.
            // Within a rank, sort by MTaskID to avoid nondeterminism.
            TasksByRank tasksByRank;

            // Find all reader and writer tasks for this variable, add to
            // tasksByRank.
            findAdjacentTasks(varVtxp, tasksByRank);

            // Merge all writer and reader tasks from same rank together.
            //
            // NOTE: Strictly speaking, we don't need to merge all the
            // readers together. That may lead to extra serialization. The
            // least amount of ordering we could impose here would be to
            // merge all writers at a given rank together; then make edges
            // from the merged writer node to each reader node at the same
            // rank; and then from each reader node to the merged writer at
            // the next rank.
            //
            // Whereas, merging all readers and writers at the same rank
            // together is "the simplest thing that could possibly work"
            // and it seems to.  It also creates fairly few edges. We don't
            // want to create tons of edges here, doing so is not nice to
            // the main edge contraction pass.
            mergeSameRankTasks(tasksByRank);
        }

        // Handle SystemC vars just a little differently. Instead of
        // treating each var as an independent entity, and serializing
        // writes to that one var, we treat ALL systemC vars as a single
        // entity and serialize writes (and, conservatively, reads) across
        // all of them.
        //
        // Reasoning: writing a systemC var actually turns into a call to a
        // var.write() method, which under the hood is accessing some data
        // structure that's shared by many SC vars. It's not thread safe.
        //
        // Hopefully we only have a few SC vars -- top level ports, probably.
        {
            TasksByRank tasksByRank;
            for (const OrderVarStdVertex* const varVtxp : systemCVars) {
                findAdjacentTasks(varVtxp, tasksByRank);
            }
            mergeSameRankTasks(tasksByRank);
        }

        // Handle nodes containing DPI calls, we want to serialize those
        // by default unless user gave '--threads-dpi none'.
        // Same basic strategy as above to serialize access to SC vars.
        if (!v3Global.opt.threadsDpiPure() || !v3Global.opt.threadsDpiUnpure()) {
            TasksByRank tasksByRank;
            for (V3GraphVertex& vtx : m_mTaskGraph.vertices()) {
                LogicMTask& mtask = static_cast<LogicMTask&>(vtx);
                if (hasDpiHazard(&mtask)) tasksByRank[mtask.rank()].insert(&mtask);
            }
            mergeSameRankTasks(tasksByRank);
        }
    }

public:
    static void apply(OrderMTaskGraph& mTaskGraph) { FixDataHazards{mTaskGraph}; }
};

void OrderMTaskGraph::fixDataHazards(OrderMTaskGraph& mtaskGraph) {
    FixDataHazards::apply(mtaskGraph);
}
