// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Cycle finding algorithm for DfgGraph
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2026 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************
//
// Implements Pearce's algorithm to color the strongly connected components. For reference
// see "An Improved Algorithm for Finding the Strongly Connected Components of a Directed
// Graph", David J.Pearce, 2005.
//
//*************************************************************************

#include "V3Dfg.h"
#include "V3DfgPasses.h"

#include <limits>
#include <vector>

class ColorStronglyConnectedComponents final {
    static_assert(sizeof(uint32_t[2]) == sizeof(uint64_t), "Incorrect overlay size");

    // CONSTANTS
    static constexpr uint32_t UNASSIGNED = std::numeric_limits<uint32_t>::max();

    // STATE
    const DfgGraph& m_dfg;  // The input graph
    DfgUserMap<uint64_t>& m_map;  // The result map we are computing - also used for traversal
    uint32_t m_nonTrivialSCCs = 0;  // Number of non-trivial SCCs in the graph
    uint32_t m_index = 0;  // Visitation index counter
    std::vector<const DfgVertex*> m_stack;  // The stack used by the algorithm

    // METHODS
    // Use the bottom 32-bit word as the component number
    uint32_t& component(const DfgVertex& vtx) {  //
        return reinterpret_cast<uint32_t(&)[2]>(m_map[vtx])[0];
    }
    // Use the top 32-bit word as the visitation index
    uint32_t& index(const DfgVertex& vtx) {  //
        return reinterpret_cast<uint32_t(&)[2]>(m_map[vtx])[1];
    }

    void visitColorSCCs(const DfgVertex& vtx) {
        UDEBUGONLY(UASSERT_OBJ(index(vtx) == UNASSIGNED, &vtx, "Already visited vertex"););

        // Visiting vertex
        const size_t rootIndex = index(vtx) = ++m_index;

        // Visit children
        vtx.foreachSink([&](const DfgVertex& child) {
            // If the child has not yet been visited, then continue traversal
            if (index(child) == UNASSIGNED) visitColorSCCs(child);
            // If the child is not in an SCC
            if (component(child) == UNASSIGNED) {
                if (index(vtx) > index(child)) index(vtx) = index(child);
            }
            return false;
        });

        if (index(vtx) == rootIndex) {
            // This is the 'root' of an SCC

            // A trivial SCC contains only a single vertex
            const bool isTrivial = m_stack.empty() || index(*m_stack.back()) < rootIndex;
            // We also need a separate component for vertices that drive themselves (which can
            // happen for input like 'assign a = a'), as we want to extract them (they are cyclic).
            const bool drivesSelf = vtx.foreachSink([&](const DfgVertex& sink) {  //
                return &vtx == &sink;
            });

            if (!isTrivial || drivesSelf) {
                // Allocate new component
                ++m_nonTrivialSCCs;
                component(vtx) = m_nonTrivialSCCs;
                while (!m_stack.empty()) {
                    // Only higher nodes belong to the same SCC
                    if (index(*m_stack.back()) < rootIndex) break;
                    component(*m_stack.back()) = m_nonTrivialSCCs;
                    m_stack.pop_back();
                }
            } else {
                // Trivial SCC (and does not drive itself), so acyclic. Keep it in original graph.
                component(vtx) = 0;
            }
        } else {
            // Not the root of an SCC
            m_stack.push_back(&vtx);
        }
    }

    void colorSCCs() {
        // We know constant nodes have no input edges, so they cannot be part
        // of a non-trivial SCC. Mark them as such without any real traversals.
        for (const DfgConst& vtx : m_dfg.constVertices()) {
            index(vtx) = 0;
            component(vtx) = 0;
        }

        // Initialize state of variable vertices
        for (const DfgVertexVar& vtx : m_dfg.varVertices()) {
            // If it has no inputs or no outputs, it cannot be part of a non-trivial SCC.
            if ((!vtx.srcp() && !vtx.defaultp()) || !vtx.hasSinks()) {
                index(vtx) = 0;
                component(vtx) = 0;
                continue;
            }
            index(vtx) = UNASSIGNED;
            component(vtx) = UNASSIGNED;
        }

        // Initialize state of operation vertices
        for (const DfgVertex& vtx : m_dfg.opVertices()) {
            index(vtx) = UNASSIGNED;
            component(vtx) = UNASSIGNED;
        }

        // Start traversals through not yet visited variables
        for (const DfgVertexVar& vtx : m_dfg.varVertices()) {
            if (index(vtx) == UNASSIGNED) visitColorSCCs(vtx);
        }

        // Start traversals through not yet visited operations
        for (const DfgVertex& vtx : m_dfg.opVertices()) {
            if (index(vtx) == UNASSIGNED) visitColorSCCs(vtx);
        }
    }

    explicit ColorStronglyConnectedComponents(const DfgGraph& dfg, DfgUserMap<uint64_t>& map)
        : m_dfg{dfg}
        , m_map{map} {
        UASSERT(dfg.size() < UNASSIGNED, "Graph too big " << dfg.name());
        // Yet another implementation of Pearce's algorithm.
        colorSCCs();
        // Re-assign mapped values
        m_dfg.forEachVertex([&](const DfgVertex& vtx) {
            const uint64_t c = component(vtx);
            map[vtx] = c;
        });
    }

public:
    // See declaration of  V3DfgPasses::colorStronglyConnectedComponents
    static uint32_t apply(const DfgGraph& dfg, DfgUserMap<uint64_t>& map) {
        return ColorStronglyConnectedComponents{dfg, map}.m_nonTrivialSCCs;
    }
};

uint32_t V3DfgPasses::colorStronglyConnectedComponents(const DfgGraph& dfg,
                                                       DfgUserMap<uint64_t>& map) {
    return ColorStronglyConnectedComponents::apply(dfg, map);
}
