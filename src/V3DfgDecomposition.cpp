// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: DfgGraph decomposition algorithms
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
//  Algorithms that take a DfgGraph and decompose it into multiple DfgGraphs.
//
//*************************************************************************

#include "V3PchAstNoMT.h"  // VL_MT_DISABLED_CODE_UNIT

#include "V3Dfg.h"
#include "V3DfgPasses.h"
#include "V3File.h"

#include <deque>
#include <unordered_map>
#include <vector>

VL_DEFINE_DEBUG_FUNCTIONS;

class SplitIntoComponents final {

    // STATE
    DfgGraph& m_dfg;  // The input graph
    const std::string m_prefix;  // Component name prefix
    std::vector<std::unique_ptr<DfgGraph>> m_components;  // The extracted components
    // Component counter - starting from 1 as 0 is the default value used as a marker
    size_t m_componentCounter = 1;

    void colorComponents() {
        // Work queue for depth first traversal starting from this vertex
        std::vector<DfgVertex*> queue;
        queue.reserve(m_dfg.size());

        // any sort of interesting logic must involve a variable, so we only need to iterate them
        for (DfgVertexVar& vtx : m_dfg.varVertices()) {
            // If already assigned this vertex to a component, then continue
            if (vtx.user<size_t>()) continue;

            // Start depth first traversal at this vertex
            queue.push_back(&vtx);

            // Depth first traversal
            do {
                // Pop next work item
                DfgVertex& item = *queue.back();
                queue.pop_back();

                // Move on if already visited
                if (item.user<size_t>()) continue;

                // Assign to current component
                item.user<size_t>() = m_componentCounter;

                // Enqueue all sources and sinks of this vertex.
                item.forEachSource([&](DfgVertex& src) { queue.push_back(&src); });
                item.forEachSink([&](DfgVertex& dst) { queue.push_back(&dst); });
            } while (!queue.empty());

            // Done with this component
            ++m_componentCounter;
        }
    }

    template <typename Vertex>
    void moveVertices(DfgVertex::List<Vertex>& list) {
        for (DfgVertex* const vtxp : list.unlinkable()) {
            if (const size_t component = vtxp->user<size_t>()) {
                m_dfg.removeVertex(*vtxp);
                m_components[component - 1]->addVertex(*vtxp);
            } else {
                // This vertex is not connected to a variable and is hence unused, remove here
                VL_DO_DANGLING(vtxp->unlinkDelete(m_dfg), vtxp);
            }
        }
    }

    SplitIntoComponents(DfgGraph& dfg, const std::string& label)
        : m_dfg{dfg}
        , m_prefix{dfg.name() + (label.empty() ? "" : "-") + label + "-component-"} {
        // Component number is stored as DfgVertex::user<size_t>()
        const auto userDataInUse = m_dfg.userDataInUse();
        // Color each component of the graph
        colorComponents();
        // Allocate the component graphs
        m_components.resize(m_componentCounter - 1);
        for (size_t i = 1; i < m_componentCounter; ++i) {
            m_components[i - 1].reset(new DfgGraph{m_dfg.modulep(), m_prefix + cvtToStr(i - 1)});
        }
        // Move the vertices to the component graphs
        moveVertices(m_dfg.varVertices());
        moveVertices(m_dfg.constVertices());
        moveVertices(m_dfg.opVertices());
        //
        UASSERT(m_dfg.size() == 0, "'this' DfgGraph should have been emptied");
    }

public:
    static std::vector<std::unique_ptr<DfgGraph>> apply(DfgGraph& dfg, const std::string& label) {
        return std::move(SplitIntoComponents{dfg, label}.m_components);
    }
};

std::vector<std::unique_ptr<DfgGraph>> DfgGraph::splitIntoComponents(const std::string& label) {
    return SplitIntoComponents::apply(*this, label);
}

class ExtractCyclicComponents final {
    // TYPES
    // We reuse the DfgVertex::user state set by V3DfgPasses::colorStronglyConnectedComponents.
    // We sneak an extra flag into the MSB to indicate the vertex was merged already.
    class VertexState final {
        uint64_t& m_userr;

    public:
        explicit VertexState(DfgVertex& vtx)
            : m_userr{vtx.getUser<uint64_t>()} {}
        bool merged() const { return m_userr >> 63; }
        void setMerged() { m_userr |= 1ULL << 63; }
        uint64_t component() const { return m_userr & ~(1ULL << 63); }
        void component(uint64_t value) { m_userr = (m_userr & (1ULL << 63)) | value; }
    };

    // STATE
    DfgGraph& m_dfg;  // The input graph
    const std::string m_prefix;  // Component name prefix
    const bool m_doExpensiveChecks = v3Global.opt.debugCheck();
    // The extracted cyclic components
    std::vector<std::unique_ptr<DfgGraph>> m_components;
    // Map from 'variable vertex' -> 'component index' -> 'clone in that component'
    std::unordered_map<const DfgVertexVar*, std::unordered_map<uint64_t, DfgVertexVar*>> m_clones;

    // METHODS
    void visitMergeSCCs(DfgVertex& vtx, uint64_t targetComponent) {
        VertexState vtxState{vtx};

        // Move on if already visited
        if (vtxState.merged()) return;

        // Visiting vertex
        vtxState.setMerged();

        // Assign vertex to the target component
        vtxState.component(targetComponent);

        // Visit all neighbors. We stop at variable boundaries,
        // which is where we will split the graphs
        vtx.forEachSource([this, targetComponent](DfgVertex& other) {
            if (other.is<DfgVertexVar>()) return;
            visitMergeSCCs(other, targetComponent);
        });
        vtx.forEachSink([this, targetComponent](DfgVertex& other) {
            if (other.is<DfgVertexVar>()) return;
            visitMergeSCCs(other, targetComponent);
        });
    }

    void mergeSCCs() {
        // Ensure that component boundaries are always at variables, by merging SCCs. Merging stops
        // at variable boundaries, so we don't need to iterate variables. Constants are reachable
        // from their sinks, or are unused, so we don't need to iterate them either.
        for (DfgVertex& vtx : m_dfg.opVertices()) {
            // Start DFS from each vertex that is in a non-trivial SCC, and merge everything
            // that is reachable from it into this component.
            if (const uint64_t target = VertexState{vtx}.component()) visitMergeSCCs(vtx, target);
        }
    }

    // Retrieve clone of vertex in the given component
    DfgVertexVar& getClone(DfgVertexVar& vtx, uint64_t component) {
        UASSERT_OBJ(VertexState{vtx}.component() != component, &vtx,
                    "Vertex is in that component");
        DfgVertexVar*& clonep = m_clones[&vtx][component];
        if (!clonep) {
            if (DfgVarPacked* const pVtxp = vtx.cast<DfgVarPacked>()) {
                if (AstVarScope* const vscp = pVtxp->varScopep()) {
                    clonep = new DfgVarPacked{m_dfg, vscp};
                } else {
                    clonep = new DfgVarPacked{m_dfg, pVtxp->varp()};
                }
            } else if (DfgVarArray* const aVtxp = vtx.cast<DfgVarArray>()) {
                if (AstVarScope* const vscp = aVtxp->varScopep()) {
                    clonep = new DfgVarArray{m_dfg, vscp};
                } else {
                    clonep = new DfgVarArray{m_dfg, aVtxp->varp()};
                }
            }
            UASSERT_OBJ(clonep, &vtx, "Unhandled 'DfgVertexVar' sub-type");
            clonep->setUser<uint64_t>(component);
            clonep->tmpForp(vtx.tmpForp());
        }
        return *clonep;
    }

    // Fix edges that cross components
    void fixEdges(DfgVertexVar& vtx) {
        const uint64_t component = VertexState{vtx}.component();

        // Fix up sources in a different component
        vtx.forEachSourceEdge([&](DfgEdge& edge, size_t) {
            DfgVertex* const srcp = edge.sourcep();
            if (!srcp) return;
            const uint64_t sourceComponent = VertexState{*srcp}.component();
            // Same component is OK
            if (sourceComponent == component) return;
            // Relink the source to write the clone
            edge.unlinkSource();
            getClone(vtx, sourceComponent).srcp(srcp);
        });

        // Fix up sinks in a different component
        vtx.forEachSinkEdge([&](DfgEdge& edge) {
            const uint64_t sinkComponent = VertexState{*edge.sinkp()}.component();
            // Same component is OK
            if (sinkComponent == component) return;
            // Relink the sink to read the clone
            edge.relinkSource(&getClone(vtx, sinkComponent));
        });
    }

    template <typename Vertex>
    void moveVertices(DfgVertex::List<Vertex>& list) {
        for (DfgVertex* const vtxp : list.unlinkable()) {
            DfgVertex& vtx = *vtxp;
            if (const uint64_t component = VertexState{vtx}.component()) {
                m_dfg.removeVertex(vtx);
                m_components[component - 1]->addVertex(vtx);
            }
        }
    }

    void checkEdges(DfgGraph& dfg) const {
        // Check that:
        // - Edges only cross components at variable boundaries
        // - Variable vertex sources are all connected.
        dfg.forEachVertex([&](DfgVertex& vtx) {
            const uint64_t component = VertexState{vtx}.component();
            vtx.forEachSource([&](DfgVertex& src) {
                if (src.is<DfgVertexVar>()) return;  // OK to cross at variables
                UASSERT_OBJ(component == VertexState{src}.component(), &vtx,
                            "Edge crossing components without variable involvement");
            });
            vtx.forEachSink([&](DfgVertex& snk) {
                if (snk.is<DfgVertexVar>()) return;  // OK to cross at variables
                UASSERT_OBJ(component == VertexState{snk}.component(), &vtx,
                            "Edge crossing components without variable involvement");
            });
        });
    }

    void checkGraph(DfgGraph& dfg) const {
        // Build set of vertices
        std::unordered_set<const DfgVertex*> vertices{dfg.size()};
        dfg.forEachVertex([&](const DfgVertex& vtx) { vertices.insert(&vtx); });

        // Check that each edge connects to a vertex that is within the same graph
        dfg.forEachVertex([&](const DfgVertex& vtx) {
            vtx.forEachSource([&](const DfgVertex& src) {
                UASSERT_OBJ(vertices.count(&src), &vtx, "Source vertex not in graph");
            });
            vtx.forEachSink([&](const DfgVertex& snk) {
                UASSERT_OBJ(vertices.count(&snk), &snk, "Sink vertex not in graph");
            });
        });
    }

    void extractComponents(uint32_t numNonTrivialSCCs) {
        // Allocate result graphs
        m_components.resize(numNonTrivialSCCs);
        for (uint32_t i = 0; i < numNonTrivialSCCs; ++i) {
            m_components[i].reset(new DfgGraph{m_dfg.modulep(), m_prefix + cvtToStr(i)});
        }

        // Fix up edges crossing components (we can only do this at variable boundaries, and the
        // earlier merging of components ensured crossing in fact only happen at variable
        // boundaries). Note that fixing up the edges can create clones of variables. Clones do
        // not need fixing up, so we do not need to iterate them.
        const DfgVertex* const lastp = m_dfg.varVertices().backp();
        for (DfgVertexVar& vtx : m_dfg.varVertices()) {
            // Fix up the edges crossing components
            fixEdges(vtx);
            // Don't iterate clones added during this loop
            if (&vtx == lastp) break;
        }

        // Check results for consistency
        if (VL_UNLIKELY(m_doExpensiveChecks)) {
            checkEdges(m_dfg);
            for (const auto& dfgp : m_components) checkEdges(*dfgp);
        }

        // Move other vertices to their component graphs
        // After this, vertex states are invalid as we moved the vertices
        moveVertices(m_dfg.varVertices());
        moveVertices(m_dfg.constVertices());
        moveVertices(m_dfg.opVertices());

        // Check results for consistency
        if (VL_UNLIKELY(m_doExpensiveChecks)) {
            checkGraph(m_dfg);
            for (const auto& dfgp : m_components) checkGraph(*dfgp);
        }
    }

    // CONSTRUCTOR - entry point
    explicit ExtractCyclicComponents(DfgGraph& dfg, const std::string& label)
        : m_dfg{dfg}
        , m_prefix{dfg.name() + (label.empty() ? "" : "-") + label + "-component-"} {
        // DfgVertex::user<uint64_t> is set to the SCC number by colorStronglyConnectedComponents,
        // Then we use VertexState to handle the MSB as an extra flag.
        const auto userDataInUse = dfg.userDataInUse();
        // Find all the non-trivial SCCs (and trivial cycles) in the graph
        const uint32_t numNonTrivialSCCs = V3DfgPasses::colorStronglyConnectedComponents(dfg);
        // If the graph was acyclic (which should be the common case), then we are done.
        if (!numNonTrivialSCCs) return;
        // Ensure that component boundaries are always at variables, by merging SCCs
        mergeSCCs();
        // Extract the components
        extractComponents(numNonTrivialSCCs);
    }

public:
    static std::vector<std::unique_ptr<DfgGraph>> apply(DfgGraph& dfg, const std::string& label) {
        return std::move(ExtractCyclicComponents{dfg, label}.m_components);
    }
};

std::vector<std::unique_ptr<DfgGraph>>
DfgGraph::extractCyclicComponents(const std::string& label) {
    return ExtractCyclicComponents::apply(*this, label);
}
