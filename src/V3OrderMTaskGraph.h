// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: MTask graph for multi-threaded ordering
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
//  LogicMTask and MTaskEdge are the vertex and edge of the mtask
//  graph built and coarsened by the multi-threaded partitioner (see
//  V3OrderParallel.cpp). They are independent of the partitioner's merge
//  candidate machinery: any auxiliary data the algorithms need is attached
//  externally via the vertex/edge user pointers.
//
//*************************************************************************

#ifndef VERILATOR_V3ORDERMTASKGRAPH_H_
#define VERILATOR_V3ORDERMTASKGRAPH_H_

#include "config_build.h"
#include "verilatedos.h"

#include "V3Graph.h"
#include "V3OrderMoveGraph.h"
#include "V3PairingHeap.h"

#include <array>
#include <cmath>
#include <memory>
#include <sstream>
#include <unordered_set>

class LogicMTask;
template <GraphWay::en N_Way>
class PropagateCp;

//=============================================================================
// OrderMTaskGraph

// The graph of LogicMTask vertices and MTaskEdge edges, used during multi-threaded scheduling.
class OrderMTaskGraph final : public V3Graph {
    OrderMoveGraph& m_moveGraph;  // The OrderMoveGraph this graph is built from
    LogicMTask* const m_entryp;  // The singular entry point vertex
    LogicMTask* const m_exitp;  // The singular exit point vertex

    // CONSTRUCTOR
    explicit OrderMTaskGraph(OrderMoveGraph& moveGraph);  // Used by build(), hence private
    VL_UNCOPYABLE(OrderMTaskGraph);
    VL_UNMOVABLE(OrderMTaskGraph);

public:
    // ACCESSORS
    OrderMoveGraph& moveGraph() const { return m_moveGraph; }
    LogicMTask* entryp() const { return m_entryp; }
    LogicMTask* exitp() const { return m_exitp; }

    // METHODS
    uint64_t totalCost() const;  // O(V), called once

    // STATIC METHODS
    // Build an MTask graph from 'moveGraph'
    static std::unique_ptr<OrderMTaskGraph> build(OrderMoveGraph& moveGraph) VL_MT_DISABLED;
    // Fix data hazards in the MTask graph
    static void fixDataHazards(OrderMTaskGraph& mtaskGraph) VL_MT_DISABLED;
    // Coarsen the MTask graph by merging MTasks until the given critical-path limit is reached
    static void contract(OrderMTaskGraph& mtaskGraph, uint64_t scoreLimit) VL_MT_DISABLED;
};

//=============================================================================
// We keep MTaskEdge graph edges in a PairingHeap, sorted by score and id

struct EdgeKey final {
    uint64_t m_score;  // Score part of edge key
    uint64_t m_id;  // Unique ID part of edge key
    void increase(uint64_t score) {
        UDEBUGONLY(UASSERT(score >= m_score, "Must increase"););
        m_score = score;
    }
    // Sort first by Score then by ID
    bool operator<(const EdgeKey& other) const {
        if (m_score != other.m_score) return m_score < other.m_score;
        return m_id < other.m_id;
    }
};

using EdgeHeap = PairingHeap<EdgeKey>;

//=============================================================================
// GraphEdge for the MTask graph

class MTaskEdge final : public V3GraphEdge {
    VL_RTTI_IMPL(MTaskEdge, V3GraphEdge)

    friend class LogicMTask;
    template <GraphWay::en N_Way>
    friend class PropagateCp;

    // MEMBERS
    // This edge can be in 2 EdgeHeaps, one forward and one reverse. We allocate the heap nodes
    // directly within the edge as they are always required and this makes association cheap.
    std::array<EdgeHeap::Node, GraphWay::NUM_WAYS> m_edgeHeapNode;

    // Note: The edge's contraction merge candidate (if any) is held in the inherited user pointer
    // (V3GraphEdge::userp), managed entirely by the partitioner; see edgeMC() and
    // MergeCandidateScoreboard. Kept out of MTaskEdge so it does not depend on the MergeCandidate
    // hierarchy.

public:
    // CONSTRUCTORS
    inline MTaskEdge(OrderMTaskGraph* graphp, LogicMTask* fromp, LogicMTask* top, int weight);
    VL_UNCOPYABLE(MTaskEdge);
    VL_UNMOVABLE(MTaskEdge);

    // METHODS
    template <GraphWay::en N_Way>
    inline LogicMTask* furtherMTaskp() const;
    inline LogicMTask* fromMTaskp() const;
    inline LogicMTask* toMTaskp() const;

    // Following initial assignment of critical paths, clear this MTaskEdge
    // out of the edge-map for each node and reinsert at a new location
    // with updated critical path.
    inline void resetCriticalPaths();
    uint64_t cachedCp(GraphWay way) const { return m_edgeHeapNode[way].key().m_score; }
    // Convert from the address of the m_edgeHeapNode[way] in an MTaskEdge back to the MTaskEdge
    static const MTaskEdge* toMTaskEdge(GraphWay way, const EdgeHeap::Node* nodep) {
        const size_t offset = VL_OFFSETOF(MTaskEdge, m_edgeHeapNode[way]);
        return reinterpret_cast<const MTaskEdge*>(reinterpret_cast<uintptr_t>(nodep) - offset);
    }
};

//=============================================================================
// LogicMTask

class LogicMTask final : public V3GraphVertex {
    VL_RTTI_IMPL(LogicMTask, V3GraphVertex)

    template <GraphWay::en N_Way>
    friend class PropagateCp;

    // MEMBERS

    // List of OrderMoveVertex's assigned to this mtask. LogicMTask does not own the
    // OrderMoveVertex objects, we merely keep them in a list here.
    OrderMoveVertex::List m_mVertices;

    // Cost estimate for this LogicMTask, derived from V3InstrCount, in abstract time units.
    // Cost estimates and critical path lengths are bounded by number of AstNodes * constant,
    // will run out of host memory storing the Ast way before they can overflow.
    uint64_t m_cost = 0;

    // Cost of critical paths going FORWARD from graph-start to the start
    // of this vertex, and also going REVERSE from the end of the graph to
    // the end of the vertex. Same units as m_cost.
    std::array<uint64_t, GraphWay::NUM_WAYS> m_critPathCost = {};

    static uint32_t s_nextId;  // Next ID number to use
    const uint32_t m_id = s_nextId++;  // Unique LogicMTask ID number for stable comparison

    // Count "generations" which are just operations that scan through the
    // graph. We'll mark each node with the last generation that scanned
    // it. We can use this to avoid recursing through the same node twice
    // while searching for a path.
    uint64_t m_generation = 0;

    // Store a set of forward relatives so we can quickly check if we have a given child
    std::unordered_set<LogicMTask*> m_edgeSet;
    // Store the outgoing and incoming edges in a heap sorted by the critical path length
    std::array<EdgeHeap, GraphWay::NUM_WAYS> m_edgeHeap;

    // Scratch pointer used only by PropagateCp: this MTask's node in the pending heap, or nullptr
    // if this MTask is not pending. Type erased, as the heap node type is private to PropagateCp,
    // and differs between its two instantiations (which never run concurrently).
    void* m_propagateHeapNodep = nullptr;

public:
    // CONSTRUCTORS
    LogicMTask(OrderMTaskGraph& graph, OrderMoveVertex* mVtxp) VL_MT_DISABLED;
    VL_UNCOPYABLE(LogicMTask);
    VL_UNMOVABLE(LogicMTask);

    // ACCESSORS
    OrderMoveVertex::List& vertexList() { return m_mVertices; }
    const OrderMoveVertex::List& vertexList() const { return m_mVertices; }
    uint32_t id() const { return m_id; }
    uint64_t cost() const VL_MT_SAFE { return m_cost; }
    uint64_t critPathCost(GraphWay way) const { return m_critPathCost[way]; }
    void setCritPathCost(GraphWay way, uint64_t cost) { m_critPathCost[way] = cost; }

    // METHODS
    bool operator<(const LogicMTask& rhs) const { return id() < rhs.id(); }

    void moveAllVerticesFrom(LogicMTask* otherp) {
        m_mVertices.splice(m_mVertices.end(), otherp->vertexList());
        m_cost += otherp->m_cost;
    }

    template <GraphWay::en N_Way>
    void addRelativeEdge(MTaskEdge* edgep) {
        constexpr GraphWay way{N_Way};
        constexpr GraphWay inv = way.invert();
        // Add to the edge heap
        LogicMTask* const relativep = edgep->furtherMTaskp<N_Way>();
        // Value is !way cp to this edge
        const uint64_t cp = relativep->cost() + relativep->critPathCost(inv);
        m_edgeHeap[way].insert(&edgep->m_edgeHeapNode[way], {cp, relativep->id()});
    }
    template <GraphWay::en N_Way>
    void stealRelativeEdge(MTaskEdge* edgep) {
        constexpr GraphWay way{N_Way};
        // Make heap node insertable, ruining the heap it is currently in.
        edgep->m_edgeHeapNode[way].yank();
        // Add the edge as new
        addRelativeEdge<N_Way>(edgep);
    }
    template <GraphWay::en N_Way>
    void removeRelativeEdge(MTaskEdge* edgep) {
        constexpr GraphWay way{N_Way};
        // Remove from the edge heap
        m_edgeHeap[way].remove(&edgep->m_edgeHeapNode[way]);
    }

    void addRelativeMTask(LogicMTask* relativep) {
        // Add the relative to connecting edge map
        const bool exits = !m_edgeSet.emplace(relativep).second;
        UDEBUGONLY(UASSERT(!exits, "Adding existing relative"););
    }
    void removeRelativeMTask(LogicMTask* relativep) {
        const size_t removed = m_edgeSet.erase(relativep);
        UDEBUGONLY(UASSERT(removed, "Relative should have been in set"););
    }
    bool hasRelativeMTask(LogicMTask* relativep) const { return m_edgeSet.count(relativep); }

    template <GraphWay::en N_Way>
    void checkRelativesCp() const {
        constexpr GraphWay way{N_Way};
        for (const V3GraphEdge& edge : edges<N_Way>()) {
            const LogicMTask* const relativep
                = static_cast<const LogicMTask*>(edge.furtherp<N_Way>());
            const uint64_t cachedCp = static_cast<const MTaskEdge&>(edge).cachedCp(way);
            const uint64_t cp = relativep->critPathCost(way.invert()) + relativep->cost();
            UASSERT(cachedCp == cp, "Calculation error in scoring");
        }
    }

    template <GraphWay::en N_Way>
    uint64_t critPathCostWithout(const V3GraphEdge* withoutp) const {
        const GraphWay way{N_Way};
        const GraphWay inv = way.invert();
        // Compute the critical path cost wayward to this node, without considering edge
        // 'withoutp'. We need to look at two edges at most, the critical path if that is not via
        // 'withoutp', or the second-worst path, if the critical path is via 'withoutp'.
        UDEBUGONLY(UASSERT(withoutp->furtherp<N_Way>() == this,
                           "In critPathCostWithout(), edge 'withoutp' must further to 'this'"););
        const EdgeHeap& edgeHeap = m_edgeHeap[inv];
        const EdgeHeap::Node* const maxp = edgeHeap.max();
        if (!maxp) return 0;
        if (MTaskEdge::toMTaskEdge(inv, maxp) != withoutp) return maxp->key().m_score;
        const EdgeHeap::Node* const secp = edgeHeap.secondMax();
        if (!secp) return 0;
        return secp->key().m_score;
    }

private:
    // This takes LogicMTask instead of generic V3GraphVertex. We will use the critical
    // paths known to LogicMTask to prune the recursion for speed. Also store 'generation' in
    // LogicMTask::m_generation so we can prune the search and avoid recursing through the same
    // node more than once in a single search.
    static bool pathExistsFromInternal(LogicMTask* fromp, LogicMTask* top,
                                       const MTaskEdge* excludedEdgep, uint64_t generation) {

        // If already looked at this node in the current search, since we're back again,
        // we must not have found a path on the first go.
        if (fromp->m_generation == generation) return false;

        // Mark visited
        fromp->m_generation = generation;

        // Base case: we found a path.
        if (fromp == top) return true;

        // Base case: fromp is too late, cannot possibly be a prereq for top.
        if (fromp->critPathCost(GraphWay::REVERSE)
            < (top->critPathCost(GraphWay::REVERSE) + top->cost())) {
            return false;
        }
        if ((fromp->critPathCost(GraphWay::FORWARD) + fromp->cost())
            > top->critPathCost(GraphWay::FORWARD)) {
            return false;
        }

        // Recursively look for a path
        for (const V3GraphEdge& follow : fromp->outEdges()) {
            if (&follow == excludedEdgep) continue;
            LogicMTask* const nextp = static_cast<LogicMTask*>(follow.top());
            if (pathExistsFromInternal(nextp, top, nullptr, generation)) return true;
        }
        return false;
    }

public:
    // True if there's a path from 'fromp' to 'top' excluding 'excludedEdgep', false otherwise.
    // 'excludedEdgep' may be nullptr in which case no edge is excluded. If 'excludedEdgep' is
    // non-nullptr it must connect fromp and top.
    static bool pathExistsFrom(LogicMTask* fromp, LogicMTask* top,
                               const MTaskEdge* excludedEdgep) {
        static uint64_t s_generation = 0;
        return pathExistsFromInternal(fromp, top, excludedEdgep, ++s_generation);
    }

    // For Graphviz dumps only
    std::string name() const override VL_MT_STABLE {
        std::ostringstream out;
        out << "mt" << m_id  //
            << " | fwdCP " << m_critPathCost[GraphWay::FORWARD]  //
            << " | revCP " << m_critPathCost[GraphWay::REVERSE]  //
            << " | cost " << cost();
        return out.str();
    }
};

//=============================================================================
// MTaskEdge method definitions (need the full definition of LogicMTask)

MTaskEdge::MTaskEdge(OrderMTaskGraph* graphp, LogicMTask* fromp, LogicMTask* top, int weight)
    : V3GraphEdge{graphp, fromp, top, weight} {
    fromp->addRelativeMTask(top);
    fromp->addRelativeEdge<GraphWay::FORWARD>(this);
    top->addRelativeEdge<GraphWay::REVERSE>(this);
}

template <GraphWay::en N_Way>
LogicMTask* MTaskEdge::furtherMTaskp() const {
    return static_cast<LogicMTask*>(this->furtherp<N_Way>());
}
LogicMTask* MTaskEdge::fromMTaskp() const { return static_cast<LogicMTask*>(fromp()); }
LogicMTask* MTaskEdge::toMTaskp() const { return static_cast<LogicMTask*>(top()); }

void MTaskEdge::resetCriticalPaths() {
    LogicMTask* const fromp = fromMTaskp();
    LogicMTask* const top = toMTaskp();
    fromp->removeRelativeEdge<GraphWay::FORWARD>(this);
    top->removeRelativeEdge<GraphWay::REVERSE>(this);
    fromp->addRelativeEdge<GraphWay::FORWARD>(this);
    top->addRelativeEdge<GraphWay::REVERSE>(this);
}

#endif  // Guard
