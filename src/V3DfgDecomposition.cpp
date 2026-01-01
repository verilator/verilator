// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: DfgGraph decomposition algorithms
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
    // Map from vertices to the weekly connected component they belong to
    DfgUserMap<size_t> m_component = m_dfg.makeUserMap<size_t>();
    const std::string m_prefix;  // Component name prefix
    std::vector<std::unique_ptr<DfgGraph>> m_components;  // The extracted components
    // Component counter - starting from 1 as 0 is the default value used as a marker
    size_t m_componentCounter = 1;

    void colorComponents() {
        // Work queue for depth first traversal starting from this vertex
        std::vector<DfgVertex*> queue;
        queue.reserve(m_dfg.size());

        // Any sort of interesting logic must involve a variable, so we only need to iterate them
        for (DfgVertexVar& vtx : m_dfg.varVertices()) {
            // If already assigned this vertex to a component, then continue
            if (m_component[vtx]) continue;

            // Start depth first traversal at this vertex
            queue.push_back(&vtx);

            // Depth first traversal
            do {
                // Pop next work item
                DfgVertex& item = *queue.back();
                queue.pop_back();

                // Move on if already visited
                if (m_component[item]) continue;

                // Assign to current component
                m_component[item] = m_componentCounter;

                // Enqueue all sources and sinks of this vertex.
                item.foreachSource([&](DfgVertex& src) {
                    queue.push_back(&src);
                    return false;
                });
                item.foreachSink([&](DfgVertex& dst) {
                    queue.push_back(&dst);
                    return false;
                });
            } while (!queue.empty());

            // Done with this component
            ++m_componentCounter;
        }
    }

    template <typename Vertex>
    void moveVertices(DfgVertex::List<Vertex>& list) {
        for (DfgVertex* const vtxp : list.unlinkable()) {
            if (const size_t component = m_component[vtxp]) {
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
    // STATE
    DfgGraph& m_dfg;  // The input graph
    // Map from vertices to the component they belong to
    DfgUserMap<uint64_t> m_component = m_dfg.makeUserMap<uint64_t>();
    const std::string m_prefix;  // Component name prefix
    const bool m_doExpensiveChecks = v3Global.opt.debugCheck();
    // The extracted cyclic components
    std::vector<std::unique_ptr<DfgGraph>> m_components;
    // Map from 'variable vertex' -> 'component index' -> 'clone in that component'
    std::unordered_map<const DfgVertexVar*, std::unordered_map<uint64_t, DfgVertexVar*>> m_clones;

    // METHODS
    void addVertexAndExpandSiblings(DfgVertex& vtx, uint64_t component) {
        // Do not go past a variable, we will partition the graph there
        if (vtx.is<DfgVertexVar>()) return;
        // Pick up component value reference
        uint64_t& vtxComponentr = m_component.at(vtx);
        // Don't need to recurse if the vertex is already in the same component,
        // it was either marked through an earlier traversal, in which case it
        // was processed recursively, or it will be processed later.
        if (vtxComponentr == component) return;
        // Because all cycles are through a variable, we can't reach another SCC.
        UASSERT_OBJ(!vtxComponentr, &vtx, "Cycle without variable involvement");
        // Put this vertex in the component, and continue recursively
        vtxComponentr = component;
        expandSiblings(vtx, component);
    }

    void expandSiblings(DfgVertex& vtx, uint64_t component) {
        UASSERT_OBJ(m_component.at(vtx) == component, &vtx, "Traversal didn't stop");
        vtx.foreachSink([&](DfgVertex& v) {
            addVertexAndExpandSiblings(v, component);
            return false;
        });
        vtx.foreachSource([&](DfgVertex& v) {
            addVertexAndExpandSiblings(v, component);
            return false;
        });
    }

    void expandComponents() {
        // Important fact that we will assume below: There are no path between
        // any two SCCs that do not go through a variable before reaching the
        // destination SCC. That is, to get from one SCC to another, you must
        // go through a variable that is not part of the destination SCC. This
        // holds because no operation vertex can have multiple sinks at this
        // point (constants have no inputs, so they are not in an SCC).
        if (m_doExpensiveChecks) {
            for (DfgVertex& vtx : m_dfg.opVertices()) {
                UASSERT_OBJ(!vtx.hasMultipleSinks(), &vtx, "Operation has multiple sinks");
            }
        }

        // We will break the graph at variable boundaries, but we want both
        // 'srcp', and 'defaultp' to be in the same component, so for each
        // cyclic variable, put both its 'srcp' and 'defaultp' into the same
        // component if they are not variables themselves. The assertions below
        // must hold because of the assumption above.
        for (DfgVertexVar& vtx : m_dfg.varVertices()) {
            const uint64_t varComponent = m_component.at(vtx);
            if (!varComponent) continue;
            if (DfgVertex* const srcp = vtx.srcp()) {
                if (!srcp->is<DfgVertexVar>()) {
                    uint64_t& srcComponent = m_component.at(srcp);
                    UASSERT_OBJ(!srcComponent || srcComponent == varComponent, srcp,
                                "Cycle through 'srcp' that does not go through variable.");
                    srcComponent = varComponent;
                }
            }
            if (DfgVertex* const defp = vtx.defaultp()) {
                if (!defp->is<DfgVertexVar>()) {
                    uint64_t& defComponent = m_component.at(defp);
                    UASSERT_OBJ(!defComponent || defComponent == varComponent, defp,
                                "Cycle through 'defaultp' that does not go through variable");
                    defComponent = varComponent;
                }
            }
        }

        // To ensure all component boundaries are at variables, expand
        // components to include all reachable non-variable vertices. Constants
        // are reachable from their sinks, so only need to process op vertices.
        // We do this by staring a DFS from each vertex that is part of an
        // component and add all reachable non-variable vertices to the same.
        for (DfgVertex& vtx : m_dfg.opVertices()) {
            if (const uint64_t targetComponent = m_component.at(vtx)) {
                expandSiblings(vtx, targetComponent);
            }
        }
    }

    // Retrieve clone of vertex in the given component
    DfgVertexVar* getClone(DfgVertexVar& vtx, uint64_t component) {
        UASSERT_OBJ(m_component.at(vtx) != component, &vtx, "Vertex is in that component");
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
            m_component[clonep] = component;
            clonep->tmpForp(vtx.tmpForp());
        }
        return clonep;
    }

    // Fix edges that cross components
    void fixEdges(DfgVertexVar& vtx) {
        const uint64_t component = m_component.at(vtx);

        // Fix up srcp and dstp (they must be the same component, or variable)
        if (DfgVertex* const sp = vtx.srcp()) {
            const uint64_t srcComponent = m_component.at(sp);
            if (srcComponent != component) {
                UASSERT_OBJ(sp->is<DfgVertexVar>(), &vtx, "'srcp' in different component");
                getClone(vtx, srcComponent)->srcp(sp);
                vtx.srcp(nullptr);
            }
        }
        if (DfgVertex* const dp = vtx.defaultp()) {
            const uint64_t defaultComponent = m_component.at(dp);
            if (defaultComponent != component) {
                UASSERT_OBJ(dp->is<DfgVertexVar>(), &vtx, "'defaultp' in different component");
                getClone(vtx, defaultComponent)->defaultp(dp);
                vtx.defaultp(nullptr);
            }
        }
        // Fix up sinks in a different component to read the clone
        std::vector<DfgVertex*> sinkps;
        vtx.foreachSink([&](DfgVertex& sink) {
            sinkps.emplace_back(&sink);
            return false;
        });
        for (DfgVertex* const sinkp : sinkps) {
            const uint64_t sinkComponent = m_component.at(sinkp);
            // Same component is OK
            if (sinkComponent == component) continue;
            DfgVertex* const clonep = getClone(vtx, sinkComponent);
            for (size_t i = 0; i < sinkp->nInputs(); ++i) {
                if (sinkp->inputp(i) == &vtx) sinkp->inputp(i, clonep);
            }
        }
    }

    template <typename Vertex>
    void moveVertices(DfgVertex::List<Vertex>& list) {
        for (DfgVertex* const vtxp : list.unlinkable()) {
            DfgVertex& vtx = *vtxp;
            if (const uint64_t component = m_component.at(vtx)) {
                m_dfg.removeVertex(vtx);
                m_components[component - 1]->addVertex(vtx);
            }
        }
    }

    void checkEdges(DfgGraph& dfg) const {
        // Check that edges only cross components at variable boundaries
        dfg.forEachVertex([&](DfgVertex& vtx) {
            if (vtx.is<DfgVarPacked>()) return;
            const uint64_t component = m_component.at(vtx);
            vtx.foreachSink([&](DfgVertex& snk) {
                if (snk.is<DfgVertexVar>()) return false;  // OK to cross at variables
                UASSERT_OBJ(component == m_component.at(snk), &vtx,
                            "Edge crossing components without variable involvement");
                return false;
            });
        });
    }

    void checkGraph(DfgGraph& dfg) const {
        // Build set of vertices
        std::unordered_set<const DfgVertex*> vertices{dfg.size()};
        dfg.forEachVertex([&](const DfgVertex& vtx) { vertices.insert(&vtx); });

        // Check that each edge connects to a vertex that is within the same graph
        dfg.forEachVertex([&](const DfgVertex& vtx) {
            vtx.foreachSource([&](const DfgVertex& src) {
                UASSERT_OBJ(vertices.count(&src), &vtx, "Source vertex not in graph");
                return false;
            });
            vtx.foreachSink([&](const DfgVertex& snk) {
                UASSERT_OBJ(vertices.count(&snk), &snk, "Sink vertex not in graph");
                return false;
            });
        });
    }

    void extractComponents(uint32_t nComponents) {
        // Allocate result graphs
        m_components.resize(nComponents);
        for (uint32_t i = 0; i < nComponents; ++i) {
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
        // Find all the non-trivial SCCs (and trivial cycles) in the graph
        const uint32_t nSCCs = V3DfgPasses::colorStronglyConnectedComponents(dfg, m_component);
        // If the graph was acyclic (which should be the common case), then we are done.
        if (!nSCCs) return;
        // Ensure that component boundaries are always at variables, by expanding SCCs
        expandComponents();
        // Extract the components
        extractComponents(nSCCs);
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
