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
#include "V3GraphStream.h"
#include "V3InstrCount.h"
#include "V3Stats.h"

#include <algorithm>
#include <map>
#include <memory>
#include <unordered_map>
#include <unordered_set>

VL_DEFINE_DEBUG_FUNCTIONS;

//######################################################################
// LogicMTask

uint32_t LogicMTask::s_nextId = 1;  // Start at 1, for historic reasons

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
// OrderMTaskGraph

OrderMTaskGraph::OrderMTaskGraph(OrderMoveGraph& moveGraph)
    : m_moveGraph{moveGraph}
    , m_entryp{new LogicMTask{*this, nullptr}}
    , m_exitp{new LogicMTask{*this, nullptr}}
    , m_slowAsserts{v3Global.opt.debugPartition()} {}

bool OrderMTaskGraph::pathExistsImpl(LogicMTask* fromp, LogicMTask* top,
                                     const MTaskEdge* excludedEdgep) {
    UDEBUGONLY(UASSERT_OBJ(fromp->m_generation != m_currentGeneration, fromp,
                           "Should not visit an MTask twice in the same search"););
    // Mark visited.
    fromp->m_generation = m_currentGeneration;

    // Base case: we found a path.
    if (fromp == top) return true;

    // Base case: fromp is too late, cannot possibly be a prereq for top.
    if (fromp->cpExclusive<GraphWay::REVERSE>() < top->cpInclusive<GraphWay::REVERSE>()) {
        return false;
    }
    if (fromp->cpInclusive<GraphWay::FORWARD>() > top->cpExclusive<GraphWay::FORWARD>()) {
        return false;
    }

    // Recursively look for a path
    for (const V3GraphEdge& follow : fromp->outEdges()) {
        if (&follow == excludedEdgep) continue;
        LogicMTask* const nextp = static_cast<LogicMTask*>(follow.top());
        // Don't visit the same MTask twice in the same search.
        if (nextp->m_generation == m_currentGeneration) continue;
        if (pathExistsImpl(nextp, top, nullptr)) return true;
    }
    return false;
}

template <GraphWay::en N_Way>
void OrderMTaskGraph::propagatePush(LogicMTask* mtaskp) {
    constexpr GraphWay way{N_Way};
    constexpr GraphWay inv{way.invert()};
    const uint64_t inclusiveCp = mtaskp->cpInclusive<way>();

    for (V3GraphEdge& graphEdge : mtaskp->edges<way>()) {
        MTaskEdge& edge = static_cast<MTaskEdge&>(graphEdge);

        LogicMTask* const relativep = edge.furtherMTaskp<N_Way>();
        EdgeHeap::Node& edgeHeapNode = edge.m_edgeHeapNode[inv];
        if (inclusiveCp > edgeHeapNode.key().m_cp) {
            relativep->m_edgeHeap[inv].increaseKey(&edgeHeapNode, inclusiveCp);
        }

        const uint64_t relativeCp = relativep->cpExclusive<way>();

        if (relativeCp >= inclusiveCp) continue;

        // relativep's critical path is out of step with its longest !wayward edge.
        // Schedule that to be resolved.
        const uint64_t increment = inclusiveCp - relativeCp;

        PropagatePendingHeap::Node*& pendingNodepRef = relativep->m_propagateHeapNodep;
        if (PropagatePendingHeap::Node* const nodep = pendingNodepRef) {
            // Already in heap. Increase the increment if needed.
            if (increment > nodep->key().m_increment) {
                m_pendingHeap.increaseKey(nodep, increment);
            }
            continue;
        }

        // Add to heap
        PropagatePendingHeap::Node* const nodep = m_pendingNodePool.alloc();
        pendingNodepRef = nodep;
        m_pendingHeap.insert(nodep, {increment, relativep->id(), relativep});
    }
}

template <GraphWay::en N_Way>
void OrderMTaskGraph::propagateResolve() {
    constexpr GraphWay way{N_Way};
    constexpr GraphWay inv{way.invert()};

    // Each pending MTask is keyed on how much its critical path will grow by. Resolving them in
    // decreasing order of that growth means each MTask needs resolving only once: the growth of a
    // wayward MTask is never larger than the growth of the MTask it was pushed from, so once an
    // MTask has been resolved, no larger growth can be pushed onto it later.
    while (!m_pendingHeap.empty()) {
        // Pop max element from heap
        PropagatePendingHeap::Node* const maxp = m_pendingHeap.max();
        m_pendingHeap.remove(maxp);
        // Pick up values
        LogicMTask* const mtaskp = maxp->key().m_mtaskp;
        const uint64_t cpGrowBy = maxp->key().m_increment;
        // Confirm that we only set each node's CP once. That's an important property of this
        // algorithm, which allows it to be far faster than a recursive one.
        UASSERT_OBJ(mtaskp->m_generation != m_currentGeneration, mtaskp, "Set CP on node twice");
        mtaskp->m_generation = m_currentGeneration;
        // Free the heap node, we are done with it
        m_pendingNodePool.free(maxp);
        mtaskp->m_propagateHeapNodep = nullptr;
        // Update the critical path of mtaskp, that was out-of-date with respect to its edges
        uint64_t& cpRef = mtaskp->m_cpExclusive[way];
        const uint64_t newCp = cpRef + cpGrowBy;
        // Check that CP matches that of the longest edge wayward of mtaskp.
        if (VL_UNLIKELY(m_slowAsserts)) {
            const uint64_t edgeCp = mtaskp->m_edgeHeap[inv].max()->key().m_cp;
            UASSERT_OBJ(edgeCp == newCp, mtaskp, "CP doesn't match longest wayward edge");
        }
        cpRef = newCp;
        propagatePush<N_Way>(mtaskp);
    }
}

uint64_t OrderMTaskGraph::totalCost() const {
    uint64_t cost = 0;
    for (const V3GraphVertex& vtx : vertices()) cost += static_cast<const LogicMTask&>(vtx).cost();
    return cost;
}

void OrderMTaskGraph::addEdge(LogicMTask* fromp, LogicMTask* top) {
    UASSERT_OBJ(fromp != top, fromp, "Should not create self-edges");
    UDEBUGONLY(UASSERT_OBJ(!fromp->hasEdgeTo(top), fromp, "Should not create redundant edges"););

    // Create the edge. This inserts it into the edge heap of both endpoints with the correct
    // critical path keys, as the critical paths of the endpoints are still unchanged here.
    new MTaskEdge{this, fromp, top};

    // The path through the new edge might be longer than the current critical path of its
    // endpoints, in which case the critical paths need updating. Note each endpoint is the seed of
    // one propagation, and is updated by the other: the inclusive critical paths of the endpoints
    // themselves did not change (a new out-edge cannot lengthen a path into 'fromp', nor a new
    // in-edge a path out of 'top'), so it is the new relative of each seed whose critical path
    // might need to grow. That is, 'top' is updated wayward of 'fromp' below, and vice versa,
    // together with the relatives of each, transitively.
    //
    // The guards below are an asymptotic optimization. The graph is consistent apart from the new
    // edge, so the new relative is the only relative of either seed that can have a stale critical
    // path, and if it does not need updating the propagation does nothing. It would however still
    // walk all edges of the seed to discover that, which is expensive for a high degree seed.
    if (fromp->cpInclusive<GraphWay::FORWARD>() > top->cpExclusive<GraphWay::FORWARD>()) {
        propagate<GraphWay::FORWARD>(fromp);
    }
    if (top->cpInclusive<GraphWay::REVERSE>() > fromp->cpExclusive<GraphWay::REVERSE>()) {
        propagate<GraphWay::REVERSE>(top);
    }
}

void OrderMTaskGraph::mergeMTasks(LogicMTask* recipientp, LogicMTask* donorp, bool deferred) {
    UASSERT_OBJ(recipientp != donorp, recipientp, "Should not merge an MTask with itself");

    // Note we redirect the edges before updating the cost and critical paths of the recipient,
    // which means the redirected edges are inserted into the edge heaps of the relatives using the
    // pre-merge values of the recipient. The critical path propagation below then brings all of
    // them up to date. This works because the keys in the edge heaps only ever need increasing:
    // the inclusive critical path of the merged MTask is at least the inclusive critical path of
    // either of the two MTasks it is made of, in both directions.

    // Process outgoing edges of donor
    while (MTaskEdge* const edgep = static_cast<MTaskEdge*>(donorp->outEdges().frontp())) {
        LogicMTask* const relativep = edgep->toMTaskp();

        if (!deferred) relativep->removeRelativeEdge<GraphWay::REVERSE>(edgep);

        if (relativep == recipientp || recipientp->hasEdgeTo(relativep)) {
            // This is either the edge connecting the two MTasks, which becomes internal to the
            // merged MTask, or is parallel with an existing edge of the recipient. Drop it.
            VL_DO_DANGLING(edgep->unlinkDelete(), edgep);
        } else {
            // No existing edge between recipient and relative of donor.
            // Redirect the edge from donor -> relative to recipient -> relative.
            edgep->relinkFromp(recipientp);
            recipientp->addDependent(relativep);
            if (!deferred) {
                recipientp->stealRelativeEdge<GraphWay::FORWARD>(edgep);
                relativep->addRelativeEdge<GraphWay::REVERSE>(edgep);
            }
        }
    }

    // Process incoming edges of donor
    while (MTaskEdge* const edgep = static_cast<MTaskEdge*>(donorp->inEdges().frontp())) {
        LogicMTask* const relativep = edgep->fromMTaskp();

        relativep->removeDependent(donorp);
        if (!deferred) relativep->removeRelativeEdge<GraphWay::FORWARD>(edgep);

        if (relativep == recipientp || relativep->hasEdgeTo(recipientp)) {
            // This is either the edge connecting the two MTasks, which becomes internal to the
            // merged MTask, or is parallel with an existing edge of the recipient. Drop it.
            VL_DO_DANGLING(edgep->unlinkDelete(), edgep);
        } else {
            // No existing edge between recipient and relative of donor.
            // Redirect the edge from relative -> donor to relative -> recipient.
            edgep->relinkTop(recipientp);
            relativep->addDependent(recipientp);
            if (!deferred) {
                relativep->addRelativeEdge<GraphWay::FORWARD>(edgep);
                recipientp->stealRelativeEdge<GraphWay::REVERSE>(edgep);
            }
        }
    }

    // Move the contents of the donor into the recipient, update its cost
    recipientp->m_mVertices.splice(recipientp->m_mVertices.end(), donorp->m_mVertices);
    recipientp->m_cost += donorp->m_cost;

    if (deferred) {
        VL_DO_DANGLING(donorp->unlinkDelete(this), donorp);
        return;
    }

    // The recipient now holds all edges of the merged MTask, and the critical paths of all its
    // relatives are still up to date, so the critical paths implied by its edges are the critical
    // paths of the merged MTask.
    const uint64_t newCpFwd = recipientp->cpExclusiveFromEdges<GraphWay::FORWARD>();
    const uint64_t newCpRev = recipientp->cpExclusiveFromEdges<GraphWay::REVERSE>();

    // Set the new critical paths, then propagate the increases to the relatives. Note this also
    // brings the keys of all edges of the merged MTask up to date in the relatives' edge heaps.
    recipientp->cpExclusive<GraphWay::FORWARD>(newCpFwd);
    propagate<GraphWay::FORWARD>(recipientp);
    recipientp->cpExclusive<GraphWay::REVERSE>(newCpRev);
    propagate<GraphWay::REVERSE>(recipientp);

    // Remove the donor from the graph
    VL_DO_DANGLING(donorp->unlinkDelete(this), donorp);
}

void OrderMTaskGraph::removeTransitiveEdges() {
    // Removing a transitive edge cannot change any critical path, so none need updating here.
    // Only the edge heaps and the dependent sets need maintaining.
    for (V3GraphVertex& vtx : vertices()) {
        for (V3GraphEdge* const graphEdgep : vtx.outEdges().unlinkable()) {
            MTaskEdge* const edgep = static_cast<MTaskEdge*>(graphEdgep);
            LogicMTask* const fromp = edgep->fromMTaskp();
            LogicMTask* const top = edgep->toMTaskp();
            // If the MTasks are also connected by some other path, then this is a transitive edge
            if (!pathExists(fromp, top, edgep)) continue;
            // Maintain the additional data structures of the OrderMTaskGraph
            fromp->removeDependent(top);
            fromp->removeRelativeEdge<GraphWay::FORWARD>(edgep);
            top->removeRelativeEdge<GraphWay::REVERSE>(edgep);
            VL_DO_DANGLING(edgep->unlinkDelete(), edgep);
        }
    }
    // Confirm the above left the maintained state consistent
    validate();
}

void OrderMTaskGraph::removeEmptyMTasks() {
    // This transform preserves the critical paths as it connects every predecessor of the
    // removed MTask to every successor, and the removed MTask itself has zero cost.
    for (V3GraphVertex* const vtxp : vertices().unlinkable()) {
        LogicMTask* const mtaskp = static_cast<LogicMTask*>(vtxp);

        // Keep the entry and exit vertices.
        if (mtaskp == m_entryp || mtaskp == m_exitp) continue;

        // Keep any MTask that holds logic
        bool empty = true;
        for (const OrderMoveVertex& mVtx : mtaskp->vertexList()) {
            if (mVtx.logicp()) {
                empty = false;
                break;
            }
        }
        if (!empty) continue;

        // The MTask holding no logic should have zero cost
        UASSERT_OBJ(!mtaskp->cost(), mtaskp, "MTask holding no logic should have 0 cost");

        // Connect each predecessor directly to each successor.
        for (V3GraphEdge& inEdge : mtaskp->inEdges()) {
            LogicMTask* const fromp = static_cast<MTaskEdge&>(inEdge).fromMTaskp();
            for (V3GraphEdge& outEdge : mtaskp->outEdges()) {
                LogicMTask* const top = static_cast<MTaskEdge&>(outEdge).toMTaskp();
                if (!fromp->hasEdgeTo(top)) addEdge(fromp, top);
            }
        }

        // Remove incoming edges of 'mtaskp'
        while (MTaskEdge* const edgep = static_cast<MTaskEdge*>(mtaskp->inEdges().frontp())) {
            LogicMTask* const relativep = edgep->fromMTaskp();
            relativep->removeDependent(mtaskp);
            relativep->removeRelativeEdge<GraphWay::FORWARD>(edgep);
            VL_DO_DANGLING(edgep->unlinkDelete(), edgep);
        }
        // Remove outgoing edges of 'mtaskp'
        while (MTaskEdge* const edgep = static_cast<MTaskEdge*>(mtaskp->outEdges().frontp())) {
            LogicMTask* const relativep = edgep->toMTaskp();
            relativep->removeRelativeEdge<GraphWay::REVERSE>(edgep);
            VL_DO_DANGLING(edgep->unlinkDelete(), edgep);
        }
        // Delete the empty MTask
        VL_DO_DANGLING(mtaskp->unlinkDelete(this), mtaskp);
    }
    // Confirm the above left the maintained state consistent
    validate();
}

// Check the critical paths in the given direction, and the critical paths cached in the edge heaps
// in the opposite direction, against those implied by the edges. Note this deliberately iterates
// the edge lists, rather than consulting the edge heaps, so the heaps are validated, not trusted.
template <GraphWay::en N_Way>
void OrderMTaskGraph::validateWay() const {
    constexpr GraphWay way{N_Way};
    constexpr GraphWay inv = way.invert();
    for (const V3GraphVertex& vtx : vertices()) {
        const LogicMTask& mtask = *vtx.as<LogicMTask>();
        uint64_t cpCost = 0;
        std::unordered_set<const V3GraphVertex*> relatives;
        for (const V3GraphEdge& graphEdge : mtask.edges<inv>()) {
            const MTaskEdge& edge = *graphEdge.as<MTaskEdge>();
            const LogicMTask& relative = *(edge.furtherp<inv>()->template as<LogicMTask>());
            // Run a few asserts on the graph, while we are iterating through...
            UASSERT_OBJ(edge.weight() != 0, &mtask, "Should be no cut edges in MTask graph");
            UASSERT_OBJ(&relative != &mtask, &mtask, "Should be no self edges in MTask graph");
            const bool first = relatives.insert(&relative).second;
            UASSERT_OBJ(first, &mtask, "Should be no redundant edges in MTask graph");
            const uint64_t inclusiveCp = relative.cpInclusive<way>();
            // The critical path cached in the edge heap must match that of the relative
            UASSERT_OBJ(edge.cachedCp(inv) == inclusiveCp, &mtask,
                        "Cached critical path does not match the relative");
            // As must the ID it is keyed on, which breaks ties between equal critical paths
            UASSERT_OBJ(edge.cachedId(inv) == relative.id(), &mtask,
                        "Cached ID does not match the relative");
            cpCost = std::max(cpCost, inclusiveCp);
        }
        const uint64_t cp = mtask.cpExclusive<way>();
        UASSERT_OBJ(cp == cpCost, &mtask, "Critical path does not match the edges");
        // The edge heap must yield the same, that is: it must return the largest of its keys
        UASSERT_OBJ(mtask.cpExclusiveFromEdges<N_Way>() == cpCost, &mtask,
                    "Edge heap maximum does not match the edges");
    }
}

void OrderMTaskGraph::validate() const {
    if (!m_slowAsserts) return;

    validateWay<GraphWay::FORWARD>();
    validateWay<GraphWay::REVERSE>();

    // Check the dependents set of each MTask agrees with its out-edges
    for (const V3GraphVertex& vtx : vertices()) {
        const LogicMTask& mtask = *vtx.as<LogicMTask>();
        size_t nDependents = 0;
        for (const V3GraphEdge& graphEdge : mtask.outEdges()) {
            LogicMTask* const top = graphEdge.as<MTaskEdge>()->toMTaskp();
            UASSERT_OBJ(mtask.hasEdgeTo(top), &mtask, "Dependent missing from the dependents set");
            ++nDependents;
        }
        UASSERT_OBJ(mtask.m_dependents.size() == nDependents, &mtask,
                    "Stale entry in the dependents set");
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
    void addEdge(LogicMTask* srcp, LogicMTask* dstp) {
        if (srcp->hasEdgeTo(dstp)) return;  // Don't create redundant edges.
        m_mtaskGraph.addEdge(srcp, dstp);
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
                    addEdge(&mtask, otherp);
                    continue;
                }

                // The opposite end of the edge is a bypassed vertex, add transitive dependencies
                for (const V3GraphEdge& tEdge : top->outEdges()) {
                    LogicMTask* const transp = static_cast<LogicMTask*>(tEdge.top()->userp());
                    // The Move graph is bipartite (logic <-> var), and logic is never
                    // bypassed, hence 'transp' must be non-nullptr.
                    UASSERT_OBJ(transp, mVtxp, "This cannot be a bypassed vertex");
                    addEdge(&mtask, transp);
                }
            }
        }

        // Create Dependencies to/from the entry/exit vertices, so all vertices are
        // reachable from the entry point and flow to the exit point.
        for (V3GraphVertex& vtx : mtaskGraph.vertices()) {
            LogicMTask& mtask = static_cast<LogicMTask&>(vtx);
            if (VL_UNLIKELY((&mtask == &entry) || (&mtask == &exit))) continue;
            // Add the entry/exit edges if not otherwise connected
            if (mtask.inEmpty()) addEdge(&entry, &mtask);
            if (mtask.outEmpty()) addEdge(&mtask, &exit);
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
    resp->validate();
    return resp;
}

//######################################################################
// threads_unit merging

void OrderMTaskGraph::mergeThreadsUnits(OrderMTaskGraph& mtaskGraph) {
    // Nothing to do unless some module is marked
    AstNodeModule* modp = v3Global.rootp()->modulesp();
    while (modp && !modp->threadsUnit()) modp = VN_AS(modp->nextp(), NodeModule);
    if (!modp) return;

    // NODE STATE
    //  AstScope::user3p()  -> AstScope*: The unit (instance of a marked module) the scope is in
    const VNUser3InUse user3InUse;
    for (modp = v3Global.rootp()->modulesp(); modp; modp = VN_AS(modp->nextp(), NodeModule)) {
        for (AstNode* nodep = modp->stmtsp(); nodep; nodep = nodep->nextp()) {
            AstScope* const scopep = VN_CAST(nodep, Scope);
            if (!scopep) continue;
            for (AstScope* sp = scopep; sp; sp = sp->aboveScopep()) {
                if (sp->modp()->threadsUnit()) {
                    scopep->user3p(sp);
                    break;
                }
            }
        }
    }

    // Find the unit and level of each MTask, in dependency order. Each still holds one
    // OrderMoveVertex. A logic MTask is in the unit its scope is in, and a variable MTask in the
    // unit of its writers, if they all agree. The level of an MTask is the largest number of unit
    // entries on any path to it, where an edge enters a unit when its head is in the unit and its
    // tail isn't. A group is the MTasks of one unit at one level. Groups can't form a cycle: along
    // any path the level never decreases, and it increases each time the path enters a unit, so
    // a path that leaves a group can only come back to its unit at a higher level. This includes
    // the edges added by fixDataHazards. Edges from the entry MTask are not unit entries:
    // counting them would raise a unit's MTasks with no other predecessors to level 1, merging
    // them with the unit's logic that depends on other units.
    using Place = std::pair<const AstScope*, uint32_t>;  // The unit and level of an MTask
    std::unordered_map<const V3GraphVertex*, Place> placeOf;
    std::map<Place, size_t> groupIndex;  // Index of each group in 'groups'
    std::vector<std::vector<LogicMTask*>> groups;  // Members of each group, in first-seen order
    GraphStreamUnordered stream{&mtaskGraph};
    while (const V3GraphVertex* const vtxp = stream.nextp()) {
        LogicMTask* const mtaskp = const_cast<LogicMTask*>(vtxp->as<LogicMTask>());
        const AstScope* unitp = nullptr;
        if (mtaskp == mtaskGraph.entryp() || mtaskp == mtaskGraph.exitp()) {
            // Not in a unit
        } else if (const OrderLogicVertex* const lVtxp = mtaskp->vertexList().frontp()->logicp()) {
            unitp = VN_AS(lVtxp->scopep()->user3p(), Scope);
        } else {
            // A variable MTask follows the logic writing it
            unitp = placeOf.at(mtaskp->inEdges().frontp()->fromp()).first;
            for (const V3GraphEdge& edge : mtaskp->inEdges()) {
                if (placeOf.at(edge.fromp()).first != unitp) unitp = nullptr;
            }
        }
        uint32_t level = 0;
        for (const V3GraphEdge& edge : mtaskp->inEdges()) {
            if (edge.fromp() == mtaskGraph.entryp()) continue;
            const Place& from = placeOf.at(edge.fromp());
            level = std::max(level, from.second + (unitp && from.first != unitp));
        }
        placeOf.emplace(mtaskp, Place{unitp, level});
        if (unitp) {
            const auto pair = groupIndex.emplace(Place{unitp, level}, groups.size());
            if (pair.second) groups.emplace_back();
            groups[pair.first->second].push_back(mtaskp);
        }
    }

    // Merge each group into its first MTask, then bring the critical paths up to date once.
    // Merging with 'mergeMTasks' instead updates the critical paths after every merge, which
    // takes minutes on large designs.
    mtaskGraph.clearEdgeHeaps();
    for (const std::vector<LogicMTask*>& members : groups) {
        for (size_t i = 1; i < members.size(); ++i) {
            mtaskGraph.mergeMTasks(members[0], members[i], true);
        }
    }
    mtaskGraph.rebuildCriticalPaths();
    mtaskGraph.validate();
    V3Stats::addStatSum("MTask graph, threads_unit groups", groups.size());
}

void OrderMTaskGraph::clearEdgeHeaps() {
    // Clear all heaps before yanking any node, as an edge's nodes are in the heaps of both its
    // endpoints, and clearing a heap checks the back link of its root
    for (V3GraphVertex& vtx : vertices()) {
        LogicMTask& mtask = static_cast<LogicMTask&>(vtx);
        mtask.m_edgeHeap[GraphWay::FORWARD].clear();
        mtask.m_edgeHeap[GraphWay::REVERSE].clear();
    }
    for (V3GraphVertex& vtx : vertices()) {
        for (V3GraphEdge& edge : vtx.outEdges()) {
            MTaskEdge& mEdge = static_cast<MTaskEdge&>(edge);
            mEdge.m_edgeHeapNode[GraphWay::FORWARD].yank();
            mEdge.m_edgeHeapNode[GraphWay::REVERSE].yank();
        }
    }
}

void OrderMTaskGraph::rebuildCriticalPaths() {
    // Critical paths, in dependency order each way
    {
        GraphStreamUnordered stream{this, GraphWay::FORWARD};
        while (const V3GraphVertex* const vtxp = stream.nextp()) {
            LogicMTask* const mtaskp = const_cast<LogicMTask*>(vtxp->as<LogicMTask>());
            uint64_t cp = 0;
            for (const V3GraphEdge& edge : vtxp->inEdges()) {
                const LogicMTask* const fromp = static_cast<const LogicMTask*>(edge.fromp());
                cp = std::max(cp, fromp->cpInclusive<GraphWay::FORWARD>());
            }
            mtaskp->cpExclusive<GraphWay::FORWARD>(cp);
        }
    }
    {
        GraphStreamUnordered stream{this, GraphWay::REVERSE};
        while (const V3GraphVertex* const vtxp = stream.nextp()) {
            LogicMTask* const mtaskp = const_cast<LogicMTask*>(vtxp->as<LogicMTask>());
            uint64_t cp = 0;
            for (const V3GraphEdge& edge : vtxp->outEdges()) {
                const LogicMTask* const top = static_cast<const LogicMTask*>(edge.top());
                cp = std::max(cp, top->cpInclusive<GraphWay::REVERSE>());
            }
            mtaskp->cpExclusive<GraphWay::REVERSE>(cp);
        }
    }
    // Edge heaps, keyed by the critical paths above
    for (V3GraphVertex& vtx : vertices()) {
        for (V3GraphEdge& edge : vtx.outEdges()) {
            MTaskEdge* const edgep = static_cast<MTaskEdge*>(&edge);
            edgep->fromMTaskp()->addRelativeEdge<GraphWay::FORWARD>(edgep);
            edgep->toMTaskp()->addRelativeEdge<GraphWay::REVERSE>(edgep);
        }
    }
}
