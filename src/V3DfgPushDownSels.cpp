// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Push DfgSels through DfgConcat to avoid temporaries
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
// If a DfgConcat drives both a DfgSel and a DfgConcat, and would othersiwe
// not need a temporary, then push the DfgSel down to the lower DfgConcat.
// This avoids having to insert a temporary for many intermediate results.
//
// We need to be careful not to create a cycle by pushing down a DfgSel
// that in turn feeds the concat it is being redirected to. To handle this,
// we use the Pierce-Kelly algorithm to check if a cycle would be created by
// adding a new edge. See: "A Dynamic Topological Sort Algorithm for
// Directed Acyclic Graphs", David J. Pearce, Paul H.J. Kelly, 2007
//
//*************************************************************************

#include "V3PchAstNoMT.h"  // VL_MT_DISABLED_CODE_UNIT

#include "V3Dfg.h"
#include "V3DfgPasses.h"
#include "V3Error.h"

VL_DEFINE_DEBUG_FUNCTIONS;

class V3DfgPushDownSels final {
    // TYPES

    // Each vertex has an associated State via DfgUserMap
    struct State final {
        // -- For Pearce-Kelly algorithm only
        // Topological ordering index. For all pair of vertices (a, b),
        // ord(a) < ord(b) iff there is no path from b to a in the graph.
        uint32_t ord = 0;
        bool visited = false;  // Whether the vertex has been visited during DFS
        // -- For the actial optimization only management
        bool onWorklist = false;  // Whether the vertex is in m_catps
    };

    // STATE
    // The graph being processed - must be acyclic (DAG)
    DfgGraph& m_dfg;
    // Context for pass
    V3DfgPushDownSelsContext& m_ctx;
    // Map from DfgVertex to State
    DfgUserMap<State> m_stateMap = m_dfg.makeUserMap<State>();

    // STATE - Temporaries for Pearce-Kelly algorithm - as members to avoid reallocations
    std::vector<DfgVertex*> m_stack;  // DFS stack for various steps
    std::vector<DfgVertex*> m_fwdVtxps;  // Vertices found during forward DFS
    std::vector<DfgVertex*> m_bwdVtxps;  // Vertices found during backward DFS - also work buffer
    std::vector<uint32_t> m_ords;  // Ordering numbers reassigned in current ordering update

    // STATE - For vertex movement
    std::vector<DfgConcat*> m_catps;  // DfgConcat vertices that may be optimizable

    // METHODS - Pearce-Kelly algorithm
    void debugCheck() {
        if (!v3Global.opt.debugCheck()) return;
        m_dfg.forEachVertex([&](const DfgVertex& src) {
            const State& srcState = m_stateMap[src];
            UASSERT_OBJ(!srcState.visited, &src, "Visit marker not reset");
            UASSERT_OBJ(srcState.ord > 0, &src, "No ordering assigned");
            src.foreachSink([&](const DfgVertex& dst) {
                const State& dstState = m_stateMap[dst];
                UASSERT_OBJ(srcState.ord < dstState.ord, &src, "Invalid ordering");
                return false;
            });
        });
    }

    // Find initial topological ordering using reverse post order numbering via DFS
    void initializeOrdering() {
        // Start from all vertices with no inputs
        m_stack.reserve(m_dfg.size());
        for (DfgVertexVar& vtx : m_dfg.varVertices()) {
            if (vtx.srcp() || vtx.defaultp()) continue;
            m_stack.push_back(&vtx);
        }
        for (DfgConst& vtx : m_dfg.constVertices()) m_stack.push_back(&vtx);

        // Reverse post order number to assign to next vertex
        uint32_t rpoNext = m_dfg.size();

        // DFS loop
        while (!m_stack.empty()) {
            DfgVertex& vtx = *m_stack.back();
            State& vtxState = m_stateMap[vtx];
            // If the ordering already assigned, just pop. It was visited
            // through another path through a different child.
            if (vtxState.ord) {
                UASSERT_OBJ(vtxState.visited, &vtx, "Not visited, but ordering assigned");
                m_stack.pop_back();
                continue;
            }
            // When exiting a vertex, assign the reverse post order number as ordering
            if (vtxState.visited) {
                vtxState.ord = rpoNext--;
                m_stack.pop_back();
                continue;
            }
            // Entering vertex. Enqueue all unvisited children.
            vtxState.visited = true;
            vtx.foreachSink([&](DfgVertex& dst) {
                State& dstState = m_stateMap[dst];
                if (dstState.visited) return false;
                m_stack.push_back(&dst);
                return false;
            });
        }

        // Should reach exact zero
        UASSERT(!rpoNext, "All vertics should have been visited exactly once");

        // Reset marks
        m_dfg.forEachVertex([&](DfgVertex& vtx) { m_stateMap[vtx].visited = false; });

        // Make sure it's valid
        debugCheck();
    }

    // Attempt to add an edge to the graph. Returns false if this would create
    // a cycle, and in that case, no state is modified, so it is safe to then
    // not add the actual edge. Otherwise returns true and updates state as
    // if the edge was indeed added, so caller must add the actual edge.
    bool addEdge(DfgVertex& src, DfgVertex& dst) {
        UASSERT_OBJ(&src != &dst, &src, "Should be different");
        State& srcState = m_stateMap[src];
        State& dstState = m_stateMap[dst];
        // If 'dst' is after 'src' in the topological ordering,
        // then ok to add edge and no need to update the ordering.
        if (dstState.ord > srcState.ord) return true;
        // Pearce-Kelly dicovery step
        if (pkFwdDfs(src, dst)) return false;
        pkBwdDfs(src, dst);
        // Pearce-Kelly update step
        pkReorder();
        return true;
    }

    // Pearce-Kelly forward DFS discovery step. Record visited vertices.
    // Returns true if a cycle would be created by adding the edge (src, dst).
    bool pkFwdDfs(DfgVertex& src, DfgVertex& dst) {
        const uint32_t srcOrd = m_stateMap[src].ord;
        // DFS forward from dst
        m_stack.push_back(&dst);
        while (!m_stack.empty()) {
            DfgVertex& vtx = *m_stack.back();
            m_stack.pop_back();
            State& vtxState = m_stateMap[vtx];

            // Ignore if already visited through another path through different sink
            if (vtxState.visited) continue;

            // Save vertex, mark visited
            m_fwdVtxps.push_back(&vtx);
            vtxState.visited = true;

            // Enqueue unvisited sinks in affeced area
            const bool cyclic = vtx.foreachSink([&](DfgVertex& sink) {
                State& sinkState = m_stateMap[sink];
                if (sinkState.ord == srcOrd) return true;  // Stop completely if cyclic
                if (sinkState.visited) return false;  // Stop search if already visited
                if (sinkState.ord > srcOrd) return false;  // Stop search if outside critical area
                m_stack.push_back(&sink);
                return false;
            });

            // If would be cyclic, reset state and return true
            if (cyclic) {
                for (DfgVertex* const vtxp : m_fwdVtxps) m_stateMap[vtxp].visited = false;
                m_fwdVtxps.clear();
                m_stack.clear();
                return true;
            }
        }
        // Won't be cyclic, return false
        return false;
    }

    // Pearce-Kelly backward DFS discovery step. Record visited vertices.
    void pkBwdDfs(DfgVertex& src, DfgVertex& dst) {
        const uint32_t dstOrd = m_stateMap[dst].ord;
        // DFS backward from src
        m_stack.push_back(&src);
        while (!m_stack.empty()) {
            DfgVertex& vtx = *m_stack.back();
            m_stack.pop_back();
            State& vtxState = m_stateMap[vtx];

            // Ignore if already visited through another path through different source
            if (vtxState.visited) continue;

            // Save vertex, mark visited
            m_bwdVtxps.push_back(&vtx);
            vtxState.visited = true;

            // Enqueue unvisited sources in affeced area
            vtx.foreachSource([&](DfgVertex& source) {
                State& sourceState = m_stateMap[source];
                if (sourceState.visited) return false;  // Stop search if already visited
                if (sourceState.ord < dstOrd)
                    return false;  // Stop search if outside critical area
                m_stack.push_back(&source);
                return false;
            });
        }
    }

    // Pearce-Kelly reorder step
    void pkReorder() {
        // Sort vertices found during forward and backward search
        const auto cmp = [this](const DfgVertex* const ap, const DfgVertex* const bp) {
            return m_stateMap[ap].ord < m_stateMap[bp].ord;
        };
        std::sort(m_bwdVtxps.begin(), m_bwdVtxps.end(), cmp);
        std::sort(m_fwdVtxps.begin(), m_fwdVtxps.end(), cmp);
        // Will use m_bwdVtxps for processing to avoid copying. Save the size.
        const size_t bwdSize = m_bwdVtxps.size();
        // Append forward vertices to the backward list for processing
        m_bwdVtxps.insert(m_bwdVtxps.end(), m_fwdVtxps.begin(), m_fwdVtxps.end());
        // Save the current ordering numbers, reset visitation marks
        for (DfgVertex* const vtxp : m_bwdVtxps) {
            State& state = m_stateMap[vtxp];
            state.visited = false;
            m_ords.push_back(state.ord);
        }
        // The current ordering numbers are sorted in the two sub lists, merge them
        std::inplace_merge(m_ords.begin(), m_ords.begin() + bwdSize, m_ords.end());
        // Assign new ordering
        for (size_t i = 0; i < m_ords.size(); ++i) m_stateMap[m_bwdVtxps[i]].ord = m_ords[i];
        // Reset sate
        m_fwdVtxps.clear();
        m_bwdVtxps.clear();
        m_ords.clear();
        // Make sure it's valid
        debugCheck();
    }

    // METHODS - Vertex processing

    static bool ignoredSink(const DfgVertex& sink) {
        // Ignore non observable variable sinks. These will be eliminated.
        if (const DfgVarPacked* const varp = sink.cast<DfgVarPacked>()) {
            if (!varp->hasSinks() && !varp->isObserved()) return true;
        }
        return false;
    }

    // Find all concatenations that feed another concatenation and may be
    // optimizable. These are the ones that feed a DfgSel, and no other
    // observable sinks. (If there were other observable sinks, a temporary
    // would be required anyway.)
    void findCandidatess() {
        for (DfgVertex& vtx : m_dfg.opVertices()) {
            // Consider only concatenations ...
            DfgConcat* const catp = vtx.cast<DfgConcat>();
            if (!catp) continue;

            // Count the various types of sinks
            uint32_t nSels = 0;
            uint32_t nCats = 0;
            uint32_t nOther = 0;
            vtx.foreachSink([&](const DfgVertex& sink) {
                if (sink.is<DfgSel>()) {
                    ++nSels;
                } else if (sink.is<DfgConcat>()) {
                    ++nCats;
                } else if (!ignoredSink(sink)) {
                    ++nOther;
                }
                return false;
            });

            // Consider if optimizable
            if (nSels > 0 && nCats == 1 && nOther == 0) {
                m_catps.push_back(catp);
                m_stateMap[catp].onWorklist = true;
            }
        }
    }

    void pushDownSels() {
        // Selects driven by the current vertex. Outside loop to avoid reallocation.
        std::vector<DfgSel*> selps;
        selps.reserve(m_dfg.size());
        // Consider each concatenation
        while (!m_catps.empty()) {
            DfgConcat* const catp = m_catps.back();
            m_catps.pop_back();
            m_stateMap[catp].onWorklist = false;

            // Iterate sinks, collect selects, check if should be optimized
            selps.clear();
            DfgVertex* sinkp = nullptr;  // The only non DfgSel sink (ignoring some DfgVars)
            const bool multipleNonSelSinks = catp->foreachSink([&](DfgVertex& sink) {
                // Collect selects
                if (DfgSel* const selp = sink.cast<DfgSel>()) {
                    selps.emplace_back(selp);
                    return false;
                }
                // Skip ignored sinks
                if (ignoredSink(sink)) return false;
                // If already found a non DfgSel sink, return true
                if (sinkp) return true;
                // Save the non DfgSel sink
                sinkp = &sink;
                return false;
            });

            // It it has multiple non DfgSel sinks, it will need a temporary, so don't bother
            if (multipleNonSelSinks) continue;
            // We only add DfgConcats to the work list that drive a select.
            UASSERT_OBJ(!selps.empty(), catp, "Should have selects");
            // If no other sink, then nothing to do
            if (!sinkp) continue;
            // If the only other sink is not a concatenation, then nothing to do
            DfgConcat* const sinkCatp = sinkp->cast<DfgConcat>();
            if (!sinkCatp) continue;

            // Ok, we can try to push the selects down to the sink DfgConcat
            const uint32_t offset = sinkCatp->rhsp() == catp ? 0 : sinkCatp->rhsp()->width();
            const uint32_t pushedDownBefore = m_ctx.m_pushedDown;
            for (DfgSel* const selp : selps) {
                // Don't do it if it would create a cycle
                if (!addEdge(*sinkCatp, *selp)) {
                    ++m_ctx.m_wouldBeCyclic;
                    continue;
                }
                // Otherwise redirect the select
                ++m_ctx.m_pushedDown;
                selp->lsb(selp->lsb() + offset);
                selp->fromp(sinkCatp);
            }
            // If we pushed down any selects, then we need to consider the sink concatenation
            // again
            State& sinkCatState = m_stateMap[sinkCatp];
            if (pushedDownBefore != m_ctx.m_pushedDown && !sinkCatState.onWorklist) {
                m_catps.push_back(sinkCatp);
                sinkCatState.onWorklist = true;
            }
        }
    }

    // CONSTRUCTOR
    V3DfgPushDownSels(DfgGraph& dfg, V3DfgPushDownSelsContext& ctx)
        : m_dfg{dfg}
        , m_ctx{ctx} {

        // Find optimization candidates
        m_catps.reserve(m_dfg.size());
        findCandidatess();
        // Early exit if nothing to do
        if (m_catps.empty()) return;

        // Pre-allocate storage
        m_stack.reserve(m_dfg.size());
        m_fwdVtxps.reserve(m_dfg.size());
        m_bwdVtxps.reserve(m_dfg.size());
        m_ords.reserve(m_dfg.size());

        // Initialize topologicel ordering
        initializeOrdering();

        // Sort candidates in topological order so we process them the least amount
        std::sort(m_catps.begin(), m_catps.end(),
                  [this](const DfgConcat* const ap, const DfgConcat* const bp) {
                      return m_stateMap[ap].ord < m_stateMap[bp].ord;
                  });

        // Push selects down to the lowest concatenation
        pushDownSels();
    }

public:
    static void apply(DfgGraph& dfg, V3DfgPushDownSelsContext& ctx) {
        V3DfgPushDownSels{dfg, ctx};
    }
};

void V3DfgPasses::pushDownSels(DfgGraph& dfg, V3DfgPushDownSelsContext& ctx) {
    V3DfgPushDownSels::apply(dfg, ctx);
}
