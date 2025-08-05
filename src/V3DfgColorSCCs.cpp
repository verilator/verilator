// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Cycle finding algorithm for DfgGraph
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2025 by Wilson Snyder. This program is free software; you
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

// Similar algorithm used in ExtractCyclicComponents.
// This one sets DfgVertex::user(). See the static 'apply' method below.
class ColorStronglyConnectedComponents final {
    static constexpr uint32_t UNASSIGNED = std::numeric_limits<uint32_t>::max();

    // TYPES
    struct VertexState final {
        uint32_t component = UNASSIGNED;  // Result component number (0 means not in SCC)
        uint32_t index = UNASSIGNED;  // Used by Pearce's algorithm for detecting SCCs
        VertexState() = default;
        VertexState(uint32_t i, uint32_t n)
            : component{n}
            , index{i} {}
    };

    // STATE
    DfgGraph& m_dfg;  // The input graph
    uint32_t m_nonTrivialSCCs = 0;  // Number of non-trivial SCCs in the graph
    uint32_t m_index = 0;  // Visitation index counter
    std::vector<DfgVertex*> m_stack;  // The stack used by the algorithm

    // METHODS
    void visitColorSCCs(DfgVertex& vtx, VertexState& vtxState) {
        UDEBUGONLY(UASSERT_OBJ(vtxState.index == UNASSIGNED, &vtx, "Already visited vertex"););

        // Visiting vertex
        const size_t rootIndex = vtxState.index = ++m_index;

        // Visit children
        vtx.forEachSink([&](DfgVertex& child) {
            VertexState& childSatate = child.user<VertexState>();
            // If the child has not yet been visited, then continue traversal
            if (childSatate.index == UNASSIGNED) visitColorSCCs(child, childSatate);
            // If the child is not in an SCC
            if (childSatate.component == UNASSIGNED) {
                if (vtxState.index > childSatate.index) vtxState.index = childSatate.index;
            }
        });

        if (vtxState.index == rootIndex) {
            // This is the 'root' of an SCC

            // A trivial SCC contains only a single vertex
            const bool isTrivial = m_stack.empty()  //
                                   || m_stack.back()->getUser<VertexState>().index < rootIndex;
            // We also need a separate component for vertices that drive themselves (which can
            // happen for input like 'assign a = a'), as we want to extract them (they are cyclic).
            const bool drivesSelf = vtx.findSink<DfgVertex>([&vtx](const DfgVertex& sink) {  //
                return &vtx == &sink;
            });

            if (!isTrivial || drivesSelf) {
                // Allocate new component
                ++m_nonTrivialSCCs;
                vtxState.component = m_nonTrivialSCCs;
                while (!m_stack.empty()) {
                    VertexState& topState = m_stack.back()->getUser<VertexState>();
                    // Only higher nodes belong to the same SCC
                    if (topState.index < rootIndex) break;
                    m_stack.pop_back();
                    topState.component = m_nonTrivialSCCs;
                }
            } else {
                // Trivial SCC (and does not drive itself), so acyclic. Keep it in original graph.
                vtxState.component = 0;
            }
        } else {
            // Not the root of an SCC
            m_stack.push_back(&vtx);
        }
    }

    void colorSCCs() {
        // We know constant nodes have no input edges, so they cannot be part
        // of a non-trivial SCC. Mark them as such without any real traversals.
        for (DfgConst& vtx : m_dfg.constVertices()) vtx.setUser(VertexState{0, 0});

        // Start traversals through variables
        for (DfgVertexVar& vtx : m_dfg.varVertices()) {
            VertexState& vtxState = vtx.user<VertexState>();
            // If it has no input or no outputs, it cannot be part of a non-trivial SCC.
            if (vtx.arity() == 0 || !vtx.hasSinks()) {
                UDEBUGONLY(UASSERT_OBJ(vtxState.index == UNASSIGNED || vtxState.component == 0,
                                       &vtx, "Non circular variable must be in a trivial SCC"););
                vtxState.index = 0;
                vtxState.component = 0;
                continue;
            }
            // If not yet visited, start a traversal
            if (vtxState.index == UNASSIGNED) visitColorSCCs(vtx, vtxState);
        }

        // Start traversals through operations
        for (DfgVertex& vtx : m_dfg.opVertices()) {
            VertexState& vtxState = vtx.user<VertexState>();
            // If not yet visited, start a traversal
            if (vtxState.index == UNASSIGNED) visitColorSCCs(vtx, vtxState);
        }
    }

    ColorStronglyConnectedComponents(DfgGraph& dfg)
        : m_dfg{dfg} {
        UASSERT(dfg.size() < UNASSIGNED, "Graph too big " << dfg.name());
        // Yet another implementation of Pearce's algorithm.
        colorSCCs();
        // Re-assign user values
        m_dfg.forEachVertex([](DfgVertex& vtx) {
            const uint64_t component = vtx.getUser<VertexState>().component;
            vtx.setUser<uint64_t>(component);
        });
    }

public:
    // Sets DfgVertex::user<uint64_t>() for all vertext to:
    // - 0, if the vertex is not part of a non-trivial strongly connected component
    //   and is not part of a self-loop. That is: the Vertex is not part of any cycle.
    // - N, if the vertex is part of a non-trivial strongly conneced component or self-loop N.
    //   That is: each set of vertices that are reachable from each other will have the same
    //   non-zero value assigned.
    // Returns the number of non-trivial SCCs (~distinct cycles)
    static uint32_t apply(DfgGraph& dfg) {
        return ColorStronglyConnectedComponents{dfg}.m_nonTrivialSCCs;
    }
};

uint32_t V3DfgPasses::colorStronglyConnectedComponents(DfgGraph& dfg) {
    return ColorStronglyConnectedComponents::apply(dfg);
}
