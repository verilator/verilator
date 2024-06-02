// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: DAG Path Checking
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

#define VL_MT_DISABLED_CODE_UNIT 1

#include "config_build.h"
#include "verilatedos.h"

#include "V3GraphPathChecker.h"

#include "V3Global.h"
#include "V3GraphStream.h"

//######################################################################
// GraphPCNode

struct GraphPCNode final {
    // User data for each node in GraphPathChecker.
    //
    // Like the LogicMTasks's, store before and after CPs for the nodes in
    // the GraphPathChecker graph.
    //
    // Unlike the LogicMTasks's, we have no cost info for the generic graph
    // accepted by GraphPathChecker, so assume each node has unit cost.
    std::array<uint32_t, GraphWay::NUM_WAYS> m_cp;

    // Detect if we've seen this node before in a given recursive
    // operation. We'll use this in pathExistsInternal() to avoid checking
    // the same node twice, and again in updateHalfCriticalPath() to assert
    // there are no cycles.
    uint64_t m_seenAtGeneration = 0;

    // CONSTRUCTORS
    GraphPCNode() {
        for (unsigned int& w : m_cp) w = 0;
    }
    ~GraphPCNode() = default;
};

//######################################################################
// GraphPathChecker implementation

template <GraphWay::en T_Way>
void GraphPathChecker::initHalfCriticalPaths(bool checkOnly) {
    constexpr GraphWay way{T_Way};
    constexpr GraphWay rev = way.invert();
    GraphStreamUnordered order(m_graphp, way);
    while (const V3GraphVertex* const vertexp = order.nextp()) {
        unsigned critPathCost = 0;
        for (const V3GraphEdge& edge : vertexp->edges<rev>()) {
            if (!m_edgeFuncp(&edge)) continue;

            const V3GraphVertex* wrelativep = edge.furtherp<rev>();
            const GraphPCNode* const wrelUserp = static_cast<GraphPCNode*>(wrelativep->userp());
            critPathCost = std::max(critPathCost, wrelUserp->m_cp[way] + 1);
        }

        GraphPCNode* const ourUserp = static_cast<GraphPCNode*>(vertexp->userp());
        if (checkOnly) {
            UASSERT_OBJ(ourUserp->m_cp[way] == critPathCost, vertexp,
                        "Validation of critical paths failed");
        } else {
            ourUserp->m_cp[way] = critPathCost;
        }
    }
}

template void GraphPathChecker::initHalfCriticalPaths<GraphWay::FORWARD>(bool);
template void GraphPathChecker::initHalfCriticalPaths<GraphWay::REVERSE>(bool);

GraphPathChecker::GraphPathChecker(V3Graph* graphp, V3EdgeFuncP edgeFuncp)
    : GraphAlg<V3Graph>{graphp, edgeFuncp} {
    for (V3GraphVertex& vtx : graphp->vertices()) {
        // Setup tracking structure for each node.  If delete a vertex
        // there would be a leak, but ok as accept only const V3Graph*'s.
        vtx.userp(new GraphPCNode);
    }
    // Init critical paths in userp() for each vertex
    initHalfCriticalPaths<GraphWay::FORWARD>(false);
    initHalfCriticalPaths<GraphWay::REVERSE>(false);
}

GraphPathChecker::~GraphPathChecker() {
    // Free every GraphPCNode
    for (V3GraphVertex& vtx : m_graphp->vertices()) {
        const GraphPCNode* const nodep = static_cast<GraphPCNode*>(vtx.userp());
        VL_DO_DANGLING(delete nodep, nodep);
        vtx.userp(nullptr);
    }
}

bool GraphPathChecker::pathExistsInternal(const V3GraphVertex* ap, const V3GraphVertex* bp,
                                          unsigned* costp) {
    GraphPCNode* const auserp = static_cast<GraphPCNode*>(ap->userp());
    const GraphPCNode* const buserp = static_cast<GraphPCNode*>(bp->userp());

    // If have already searched this node on the current search, don't
    // recurse through it again. Since we're still searching, we must not
    // have found a path on the first go either.
    if (auserp->m_seenAtGeneration == m_generation) {
        if (costp) *costp = 0;
        return false;
    }
    auserp->m_seenAtGeneration = m_generation;

    if (costp) *costp = 1;  // count 'a' toward the search cost

    if (ap == bp) return true;

    // Rule out an a->b path based on their CPs
    if (auserp->m_cp[GraphWay::REVERSE] < buserp->m_cp[GraphWay::REVERSE] + 1) return false;
    if (buserp->m_cp[GraphWay::FORWARD] < auserp->m_cp[GraphWay::FORWARD] + 1) return false;

    // Slow path; visit some extended family
    bool foundPath = false;
    for (const V3GraphEdge& edge : ap->outEdges()) {
        if (!m_edgeFuncp(&edge)) continue;

        unsigned childCost;
        if (pathExistsInternal(edge.top(), bp, &childCost)) foundPath = true;
        if (costp) *costp += childCost;
    }

    return foundPath;
}

bool GraphPathChecker::pathExistsFrom(const V3GraphVertex* fromp, const V3GraphVertex* top) {
    incGeneration();
    return pathExistsInternal(fromp, top);
}

bool GraphPathChecker::isTransitiveEdge(const V3GraphEdge* edgep) {
    const V3GraphVertex* fromp = edgep->fromp();
    const V3GraphVertex* top = edgep->top();
    incGeneration();
    for (const V3GraphEdge& fromOut : fromp->outEdges()) {
        if (&fromOut == edgep) continue;
        if (pathExistsInternal(fromOut.top(), top)) return true;
    }
    return false;
}
