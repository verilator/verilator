// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: DfgGraph decomposition algorithms
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
//
//  Algorithms that take a DfgGraph and decompose it into multiple DfgGraphs.
//
//*************************************************************************

#include "V3PchAstNoMT.h"  // VL_MT_DISABLED_CODE_UNIT

#include "V3Dfg.h"
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
        for (DfgVertexVar *vtxp = m_dfg.varVerticesBeginp(), *nextp; vtxp; vtxp = nextp) {
            nextp = vtxp->verticesNext();
            // If already assigned this vertex to a component, then continue
            if (vtxp->user<size_t>()) continue;

            // Start depth first traversal at this vertex
            queue.push_back(vtxp);

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

    void moveVertices(DfgVertex* headp) {
        for (DfgVertex *vtxp = headp, *nextp; vtxp; vtxp = nextp) {
            nextp = vtxp->verticesNext();
            DfgVertex& vtx = *vtxp;
            if (const size_t component = vtx.user<size_t>()) {
                m_dfg.removeVertex(vtx);
                m_components[component - 1]->addVertex(vtx);
            } else {
                // This vertex is not connected to a variable and is hence unused, remove here
                vtx.unlinkDelete(m_dfg);
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
            m_components[i - 1].reset(new DfgGraph{*m_dfg.modulep(), m_prefix + cvtToStr(i - 1)});
        }
        // Move the vertices to the component graphs
        moveVertices(m_dfg.varVerticesBeginp());
        moveVertices(m_dfg.constVerticesBeginp());
        moveVertices(m_dfg.opVerticesBeginp());
        //
        UASSERT(m_dfg.size() == 0, "'this' DfgGraph should have been emptied");
    }

public:
    static std::vector<std::unique_ptr<DfgGraph>> apply(DfgGraph& dfg, const std::string& label) {
        return std::move(SplitIntoComponents{dfg, label}.m_components);
    }
};

std::vector<std::unique_ptr<DfgGraph>> DfgGraph::splitIntoComponents(std::string label) {
    return SplitIntoComponents::apply(*this, label);
}

class ExtractCyclicComponents final {
    static constexpr size_t UNASSIGNED = std::numeric_limits<size_t>::max();

    // TYPES
    struct VertexState {
        size_t index = UNASSIGNED;  // Used by Pearce's algorithm for detecting SCCs
        size_t component = UNASSIGNED;  // Result component number (0 stays in input graph)
        bool merged = false;  // Visited in the merging pass
        VertexState(){};
    };

    // STATE

    //==========================================================================
    // Shared state

    DfgGraph& m_dfg;  // The input graph
    std::deque<VertexState> m_stateStorage;  // Container for VertexState instances
    const std::string m_prefix;  // Component name prefix
    size_t m_nonTrivialSCCs = 0;  // Number of non-trivial SCCs in the graph
    const bool m_doExpensiveChecks = v3Global.opt.debugCheck();

    //==========================================================================
    // State for Pearce's algorithm for detecting SCCs

    size_t m_index = 0;  // Visitation index counter
    std::vector<DfgVertex*> m_stack;  // The stack used by the algorithm

    //==========================================================================
    // State for extraction

    // The extracted cyclic components
    std::vector<std::unique_ptr<DfgGraph>> m_components;
    // Map from 'variable vertex' -> 'component index' -> 'clone in that component'
    std::unordered_map<const DfgVertexVar*, std::unordered_map<size_t, DfgVertexVar*>> m_clones;

    // METHODS

    //==========================================================================
    // Shared methods

    VertexState& state(DfgVertex& vtx) const { return *vtx.getUser<VertexState*>(); }

    VertexState& allocState(DfgVertex& vtx) {
        VertexState*& statep = vtx.user<VertexState*>();
        UASSERT_OBJ(!statep, &vtx, "Vertex state already allocated " << cvtToHex(statep));
        m_stateStorage.emplace_back();
        statep = &m_stateStorage.back();
        return *statep;
    }

    VertexState& getOrAllocState(DfgVertex& vtx) {
        VertexState*& statep = vtx.user<VertexState*>();
        if (!statep) {
            m_stateStorage.emplace_back();
            statep = &m_stateStorage.back();
        }
        return *statep;
    }

    //==========================================================================
    // Methods for Pearce's algorithm to detect strongly connected components

    void visitColorSCCs(DfgVertex& vtx, VertexState& vtxState) {
        UDEBUGONLY(UASSERT_OBJ(vtxState.index == UNASSIGNED, &vtx, "Already visited vertex"););

        // Visiting vertex
        const size_t rootIndex = vtxState.index = ++m_index;

        // Visit children
        vtx.forEachSink([&](DfgVertex& child) {
            VertexState& childSatate = getOrAllocState(child);
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
            const bool isTrivial = m_stack.empty() || state(*m_stack.back()).index < rootIndex;
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
                    VertexState& topState = state(*m_stack.back());
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
        // Implements Pearce's algorithm to color the strongly connected components. For reference
        // see "An Improved Algorithm for Finding the Strongly Connected Components of a Directed
        // Graph", David J.Pearce, 2005.

        // We can leverage some properties of the input graph to gain a bit of speed. Firstly, we
        // know constant nodes have no in edges, so they cannot be part of a non-trivial SCC. Mark
        // them as such without starting a whole traversal.
        for (DfgConst *vtxp = m_dfg.constVerticesBeginp(), *nextp; vtxp; vtxp = nextp) {
            nextp = vtxp->verticesNext();
            VertexState& vtxState = allocState(*vtxp);
            vtxState.index = 0;
            vtxState.component = 0;
        }

        // Next, we know that all SCCs must include a variable (as the input graph was converted
        // from an AST, we can only have a cycle by going through a variable), so we only start
        // traversals through them, and only if we know they have both in and out edges.
        for (DfgVertexVar *vtxp = m_dfg.varVerticesBeginp(), *nextp; vtxp; vtxp = nextp) {
            nextp = vtxp->verticesNext();
            if (vtxp->arity() > 0 && vtxp->hasSinks()) {
                VertexState& vtxState = getOrAllocState(*vtxp);
                // If not yet visited, start a traversal
                if (vtxState.index == UNASSIGNED) visitColorSCCs(*vtxp, vtxState);
            } else {
                VertexState& vtxState = getOrAllocState(*vtxp);
                UDEBUGONLY(UASSERT_OBJ(vtxState.index == UNASSIGNED || vtxState.component == 0,
                                       vtxp, "Non circular variable must be in a trivial SCC"););
                vtxState.index = 0;
                vtxState.component = 0;
            }
        }

        // Finally, everything we did not visit through the traversal of a variable cannot be in an
        // SCC, (otherwise we would have found it from a variable).
        for (DfgVertex *vtxp = m_dfg.opVerticesBeginp(), *nextp; vtxp; vtxp = nextp) {
            nextp = vtxp->verticesNext();
            VertexState& vtxState = getOrAllocState(*vtxp);
            if (vtxState.index == UNASSIGNED) {
                vtxState.index = 0;
                vtxState.component = 0;
            }
        }
    }

    //==========================================================================
    // Methods for merging

    void visitMergeSCCs(DfgVertex& vtx, size_t targetComponent) {
        VertexState& vtxState = state(vtx);

        // Move on if already visited
        if (vtxState.merged) return;

        // Visiting vertex
        vtxState.merged = true;

        // Assign vertex to the target component
        vtxState.component = targetComponent;

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
        for (DfgVertex *vtxp = m_dfg.opVerticesBeginp(), *nextp; vtxp; vtxp = nextp) {
            nextp = vtxp->verticesNext();
            DfgVertex& vtx = *vtxp;
            // Start DFS from each vertex that is in a non-trivial SCC, and merge everything
            // that is reachable from it into this component.
            if (const size_t target = state(vtx).component) visitMergeSCCs(vtx, target);
        }
    }

    //==========================================================================
    // Methods for extraction

    // Retrieve clone of vertex in the given component
    DfgVertexVar& getClone(DfgVertexVar& vtx, size_t component) {
        UASSERT_OBJ(state(vtx).component != component, &vtx, "Vertex is in that component");
        DfgVertexVar*& clonep = m_clones[&vtx][component];
        if (!clonep) {
            if (DfgVarPacked* const pVtxp = vtx.cast<DfgVarPacked>()) {
                clonep = new DfgVarPacked{m_dfg, pVtxp->varp()};
            } else if (DfgVarArray* const aVtxp = vtx.cast<DfgVarArray>()) {
                clonep = new DfgVarArray{m_dfg, aVtxp->varp()};
            }
            UASSERT_OBJ(clonep, &vtx, "Unhandled 'DfgVertexVar' sub-type");
            VertexState& cloneStatep = allocState(*clonep);
            cloneStatep.component = component;
            // We need to mark both the original and the clone as having additional references
            vtx.setHasModRefs();
            clonep->setHasModRefs();
        }
        return *clonep;
    }

    // Fix up non-variable sources of a DfgVertexVar that are in a different component,
    // using the provided 'relink' callback
    template <typename T_Vertex>
    void fixSources(T_Vertex& vtx, std::function<void(T_Vertex&, DfgVertex&, size_t)> relink) {
        static_assert(std::is_base_of<DfgVertexVar, T_Vertex>::value,
                      "'Vertex' must be a 'DfgVertexVar'");
        const size_t component = state(vtx).component;
        vtx.forEachSourceEdge([&](DfgEdge& edge, size_t idx) {
            DfgVertex& source = *edge.sourcep();
            // DfgVertexVar sources are fixed up by `fixSinks` on those sources
            if (source.is<DfgVertexVar>()) return;
            const size_t sourceComponent = state(source).component;
            // Same component is OK
            if (sourceComponent == component) return;
            // Unlink the source edge (source is reconnected by 'relink'
            edge.unlinkSource();
            // Apply the fixup
            // cppcheck-has-bug-suppress constVariable
            DfgVertexVar& clone = getClone(vtx, sourceComponent);
            relink(*(clone.as<T_Vertex>()), source, idx);
        });
    }

    // Fix up sinks of given variable vertex that are in a different component
    void fixSinks(DfgVertexVar& vtx) {
        const size_t component = state(vtx).component;
        vtx.forEachSinkEdge([&](DfgEdge& edge) {
            const size_t sinkComponent = state(*edge.sinkp()).component;
            // Same component is OK
            if (sinkComponent == component) return;
            // Relink the sink to read the clone
            edge.relinkSource(&getClone(vtx, sinkComponent));
        });
    }

    // Fix edges that cross components
    void fixEdges(DfgVertexVar& vtx) {
        if (DfgVarPacked* const vvtxp = vtx.cast<DfgVarPacked>()) {
            fixSources<DfgVarPacked>(
                *vvtxp, [&](DfgVarPacked& clone, DfgVertex& driver, size_t driverIdx) {
                    clone.addDriver(vvtxp->driverFileLine(driverIdx),  //
                                    vvtxp->driverLsb(driverIdx), &driver);
                });
            fixSinks(*vvtxp);
            return;
        }

        if (DfgVarArray* const vvtxp = vtx.cast<DfgVarArray>()) {
            fixSources<DfgVarArray>(  //
                *vvtxp, [&](DfgVarArray& clone, DfgVertex& driver, size_t driverIdx) {
                    clone.addDriver(vvtxp->driverFileLine(driverIdx),  //
                                    vvtxp->driverIndex(driverIdx), &driver);
                });
            fixSinks(*vvtxp);
            return;
        }
    }

    static void packSources(DfgGraph& dfg) {
        // Remove undriven variable sources
        for (DfgVertexVar *vtxp = dfg.varVerticesBeginp(), *nextp; vtxp; vtxp = nextp) {
            nextp = vtxp->verticesNext();
            if (DfgVarPacked* const varp = vtxp->cast<DfgVarPacked>()) {
                varp->packSources();
                if (!varp->hasSinks() && varp->arity() == 0) {
                    VL_DO_DANGLING(varp->unlinkDelete(dfg), varp);
                }
                continue;
            }
            if (DfgVarArray* const varp = vtxp->cast<DfgVarArray>()) {
                varp->packSources();
                if (!varp->hasSinks() && varp->arity() == 0) {
                    VL_DO_DANGLING(varp->unlinkDelete(dfg), varp);
                }
                continue;
            }
        }
    }

    void moveVertices(DfgVertex* headp) {
        for (DfgVertex *vtxp = headp, *nextp; vtxp; vtxp = nextp) {
            nextp = vtxp->verticesNext();
            DfgVertex& vtx = *vtxp;
            if (const size_t component = state(vtx).component) {
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
            const size_t component = state(vtx).component;
            vtx.forEachSource([&](DfgVertex& src) {
                if (src.is<DfgVertexVar>()) return;  // OK to cross at variables
                UASSERT_OBJ(component == state(src).component, &vtx,
                            "Edge crossing components without variable involvement");
            });
            vtx.forEachSink([&](DfgVertex& snk) {
                if (snk.is<DfgVertexVar>()) return;  // OK to cross at variables
                UASSERT_OBJ(component == state(snk).component, &vtx,
                            "Edge crossing components without variable involvement");
            });
            if (const DfgVertexVar* const vtxp = vtx.cast<DfgVertexVar>()) {
                vtxp->forEachSourceEdge([](const DfgEdge& edge, size_t) {
                    UASSERT_OBJ(edge.sourcep(), edge.sinkp(), "Missing source on variable vertex");
                });
            }
        });
    }

    void checkGraph(DfgGraph& dfg) const {
        // Build set of vertices
        std::unordered_set<const DfgVertex*> vertices{dfg.size()};
        dfg.forEachVertex([&](const DfgVertex& vtx) { vertices.insert(&vtx); });

        // Check that each edge connects to a vertex that is within the same graph
        dfg.forEachVertex([&](DfgVertex& vtx) {
            vtx.forEachSource([&](DfgVertex& src) {
                UASSERT_OBJ(vertices.count(&src), &vtx, "Source vertex not in graph");
            });
            vtx.forEachSink([&](DfgVertex& snk) {
                UASSERT_OBJ(vertices.count(&snk), &snk, "Sink vertex not in graph");
            });
        });
    }

    void extractComponents() {
        // Allocate result graphs
        m_components.resize(m_nonTrivialSCCs);
        for (size_t i = 0; i < m_nonTrivialSCCs; ++i) {
            m_components[i].reset(new DfgGraph{*m_dfg.modulep(), m_prefix + cvtToStr(i)});
        }

        // Fix up edges crossing components (we can only do this at variable boundaries, and the
        // earlier merging of components ensured crossing in fact only happen at variable
        // boundaries). Note that fixing up the edges can create clones of variables. Clones do
        // not need fixing up, so we do not need to iterate them.
        DfgVertex* const lastp = m_dfg.varVerticesRbeginp();
        for (DfgVertexVar *vtxp = m_dfg.varVerticesBeginp(), *nextp; vtxp; vtxp = nextp) {
            // It is possible the last vertex (with a nullptr for 'nextp') gets cloned, and hence
            // it's 'nextp' would become none nullptr as the clone is added. However, we don't need
            // to iterate clones anyway, so it's ok to get the 'nextp' early in the loop.
            nextp = vtxp->verticesNext();
            DfgVertexVar& vtx = *vtxp;
            // Fix up the edges crossing components
            fixEdges(vtx);
            // Don't iterate clones added during this loop
            if (vtxp == lastp) break;
        }

        // Pack sources of variables to remove the now undriven inputs
        // (cloning might have unlinked some of the inputs),
        packSources(m_dfg);
        for (const auto& dfgp : m_components) packSources(*dfgp);

        // Check results for consistency
        if (VL_UNLIKELY(m_doExpensiveChecks)) {
            checkEdges(m_dfg);
            for (const auto& dfgp : m_components) checkEdges(*dfgp);
        }

        // Move other vertices to their component graphs
        // After this, vertex states are invalid as we moved the vertices
        moveVertices(m_dfg.varVerticesBeginp());
        moveVertices(m_dfg.constVerticesBeginp());
        moveVertices(m_dfg.opVerticesBeginp());

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
        // VertexState is stored as user data
        const auto userDataInUse = dfg.userDataInUse();
        // Find all the non-trivial SCCs (and trivial cycles) in the graph
        colorSCCs();
        // If the graph was acyclic (which should be the common case),
        // there will be no non-trivial SCCs, so we are done.
        if (!m_nonTrivialSCCs) return;
        // Ensure that component boundaries are always at variables, by merging SCCs
        mergeSCCs();
        // Extract the components
        extractComponents();
    }

public:
    static std::vector<std::unique_ptr<DfgGraph>> apply(DfgGraph& dfg, const std::string& label) {
        return std::move(ExtractCyclicComponents{dfg, label}.m_components);
    }
};

std::vector<std::unique_ptr<DfgGraph>> DfgGraph::extractCyclicComponents(std::string label) {
    return ExtractCyclicComponents::apply(*this, label);
}
