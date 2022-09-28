// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Data flow graph (DFG) representation of logic
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2022 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#include "config_build.h"
#include "verilatedos.h"

#include "V3Dfg.h"

#include "V3File.h"

#include <cctype>
#include <type_traits>
#include <unordered_map>

VL_DEFINE_DEBUG_FUNCTIONS;

//------------------------------------------------------------------------------
// DfgGraph
//------------------------------------------------------------------------------

DfgGraph::DfgGraph(AstModule& module, const string& name)
    : m_modulep{&module}
    , m_name{name} {}

DfgGraph::~DfgGraph() {
    forEachVertex([](DfgVertex& vtxp) { delete &vtxp; });
}

void DfgGraph::addGraph(DfgGraph& other) {
    other.forEachVertex([&](DfgVertex& vtx) {
        other.removeVertex(vtx);
        this->addVertex(vtx);
    });
}

bool DfgGraph::sortTopologically(bool reverse) {
    // Vertices in reverse topological order
    std::vector<DfgVertex*> order;

    // Markings for algorithm
    enum class Mark : uint8_t { Scheduled, OnPath, Finished };
    std::unordered_map<DfgVertex*, Mark> marks;

    // Stack of nodes in depth first search. The second element of the pair is true if the vertex
    // is on the current DFS path, and false if it's only scheduled for visitation.
    std::vector<std::pair<DfgVertex*, bool>> stack;

    // Schedule vertex for visitation
    const auto scheudle = [&](DfgVertex& vtx) {
        // Nothing to do if already finished
        if (marks.emplace(&vtx, Mark::Scheduled).first->second == Mark::Finished) return;
        // Otherwise scheule for visitation
        stack.emplace_back(&vtx, false);
    };

    // For each vertex (direct loop, so we can return early)
    for (DfgVertex* vtxp = m_vertices.begin(); vtxp; vtxp = vtxp->m_verticesEnt.nextp()) {
        // Initiate DFS from this vertex
        scheudle(*vtxp);
        while (!stack.empty()) {
            // Pick up stack top
            const auto pair = stack.back();
            stack.pop_back();
            DfgVertex* const currp = pair.first;
            const bool onPath = pair.second;
            Mark& mark = marks.at(currp);

            if (onPath) {  // Popped node on path
                // Mark it as done
                UASSERT_OBJ(mark == Mark::OnPath, currp, "DFS got lost");
                mark = Mark::Finished;
                // Add to order
                order.push_back(currp);
            } else {  // Otherwise node was scheduled for visitation, so visit it
                // If already finished, then nothing to do
                if (mark == Mark::Finished) continue;
                // If already on path, then not a DAG
                if (mark == Mark::OnPath) return false;
                // Push to path and mark as such
                mark = Mark::OnPath;
                stack.emplace_back(currp, true);
                // Schedule children
                currp->forEachSink(scheudle);
            }
        }
    }

    // Move given vertex to end of vertex list
    const auto reinsert = [this](DfgVertex& vtx) {
        // Remove from current location
        removeVertex(vtx);
        // 'addVertex' appends to the end of the vertex list, so can do this in one loop
        addVertex(vtx);
    };

    // Remember 'order' is in reverse topological order
    if (!reverse) {
        for (DfgVertex* vtxp : vlstd::reverse_view(order)) reinsert(*vtxp);
    } else {
        for (DfgVertex* vtxp : order) reinsert(*vtxp);
    }

    // Done
    return true;
}

std::vector<std::unique_ptr<DfgGraph>> DfgGraph::splitIntoComponents(std::string label) {
    size_t componentNumber = 0;
    std::unordered_map<const DfgVertex*, unsigned> vertex2component;

    forEachVertex([&](const DfgVertex& vtx) {
        // If already assigned this vertex to a component, then continue
        if (vertex2component.count(&vtx)) return;

        // Work queue for depth first traversal starting from this vertex
        std::vector<const DfgVertex*> queue{&vtx};

        // Depth first traversal
        while (!queue.empty()) {
            // Pop next work item
            const DfgVertex& item = *queue.back();
            queue.pop_back();

            // Mark vertex as belonging to current component (if it's not marked yet)
            const bool isFirstEncounter = vertex2component.emplace(&item, componentNumber).second;

            // If we have already visited this vertex during the traversal, then move on.
            if (!isFirstEncounter) continue;

            // Enqueue all sources and sinks of this vertex.
            item.forEachSource([&](const DfgVertex& src) { queue.push_back(&src); });
            item.forEachSink([&](const DfgVertex& dst) { queue.push_back(&dst); });
        }

        // Done with this component
        ++componentNumber;
    });

    // Create the component graphs
    std::vector<std::unique_ptr<DfgGraph>> results{componentNumber};

    const std::string prefix{name() + (label.empty() ? "" : "-") + label + "-component-"};

    for (size_t i = 0; i < componentNumber; ++i) {
        results[i].reset(new DfgGraph{*m_modulep, prefix + cvtToStr(i)});
    }

    // Move all vertices under the corresponding component graphs
    forEachVertex([&](DfgVertex& vtx) {
        this->removeVertex(vtx);
        results[vertex2component[&vtx]]->addVertex(vtx);
    });

    UASSERT(size() == 0, "'this' DfgGraph should have been emptied");

    return results;
}

class ExtractCyclicComponents final {
    static constexpr size_t UNASSIGNED = std::numeric_limits<size_t>::max();

    // TYPES
    struct VertexState {
        size_t index;  // Used by Pearce's algorithm for detecting SCCs
        size_t component = UNASSIGNED;  // Result component number (0 stays in input graph)
        VertexState(size_t index)
            : index{index} {}
    };

    // STATE

    //==========================================================================
    // Shared state

    DfgGraph& m_dfg;  // The input graph
    const std::string m_prefix;  // Component name prefix
    std::unordered_map<const DfgVertex*, VertexState> m_state;  // Vertex state
    size_t m_nonTrivialSCCs = 0;  // Number of non-trivial SCCs in the graph
    const bool m_doExpensiveChecks = v3Global.opt.debugCheck();

    //==========================================================================
    // State for Pearce's algorithm for detecting SCCs

    size_t m_index = 0;  // Visitation index counter
    std::vector<DfgVertex*> m_stack;  // The stack used by the algorithm

    //==========================================================================
    // State for merging

    std::unordered_set<const DfgVertex*> m_merged;  // Marks visited vertices

    //==========================================================================
    // State for extraction

    // The extracted cyclic components
    std::vector<std::unique_ptr<DfgGraph>> m_components;
    // Map from 'variable vertex' -> 'component index' -> 'clone in that component'
    std::unordered_map<const DfgVertexLValue*, std::unordered_map<size_t, DfgVertexLValue*>>
        m_clones;

    // METHODS

    //==========================================================================
    // Methods for Pearce's algorithm to detect strongly connected components

    void visitColorSCCs(DfgVertex& vtx) {
        const auto pair = m_state.emplace(std::piecewise_construct,  //
                                          std::forward_as_tuple(&vtx),  //
                                          std::forward_as_tuple(m_index));

        // If already visited, then nothing to do
        if (!pair.second) return;

        // Visiting node
        const size_t rootIndex = m_index++;

        vtx.forEachSink([&](DfgVertex& child) {
            // Visit child
            visitColorSCCs(child);
            auto& childSatate = m_state.at(&child);
            // If the child is not in an SCC
            if (childSatate.component == UNASSIGNED) {
                auto& vtxState = m_state.at(&vtx);
                if (vtxState.index > childSatate.index) vtxState.index = childSatate.index;
            }
        });

        auto& vtxState = m_state.at(&vtx);
        if (vtxState.index == rootIndex) {
            // This is the 'root' of an SCC

            // A trivial SCC contains only a single vertex
            const bool isTrivial = m_stack.empty() || m_state.at(m_stack.back()).index < rootIndex;
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
                    DfgVertex* const topp = m_stack.back();
                    auto& topState = m_state.at(topp);
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
        // Graph", David J.Pearce, 2005
        m_state.reserve(m_dfg.size());
        m_dfg.forEachVertex([&](DfgVertex& vtx) { visitColorSCCs(vtx); });
    }

    //==========================================================================
    // Methods for merging

    void visitMergeSCCs(const DfgVertex& vtx, size_t targetComponent) {
        // We stop at variable boundaries, which is where we will split the graphs
        if (vtx.is<DfgVarPacked>() || vtx.is<DfgVarArray>()) return;

        // Mark visited/move on if already visited
        if (!m_merged.insert(&vtx).second) return;

        // Assign vertex to the target component
        m_state.at(&vtx).component = targetComponent;

        // Visit all neighbours
        vtx.forEachSource([=](const DfgVertex& other) { visitMergeSCCs(other, targetComponent); });
        vtx.forEachSink([=](const DfgVertex& other) { visitMergeSCCs(other, targetComponent); });
    }

    void mergeSCCs() {
        // Ensure that component boundaries are always at variables, by merging SCCs
        m_merged.reserve(m_dfg.size());
        m_dfg.forEachVertex([this](DfgVertex& vtx) {
            // Start DFS from each vertex that is in a non-trivial SCC, and merge everything that
            // is reachable from it into this component.
            if (const size_t target = m_state.at(&vtx).component) visitMergeSCCs(vtx, target);
        });
    }

    //==========================================================================
    // Methods for extraction

    // Retrieve clone of vertex in the given component
    DfgVertexLValue& getClone(DfgVertexLValue& vtx, size_t component) {
        UASSERT_OBJ(m_state.at(&vtx).component != component, &vtx, "Vertex is in that component");
        DfgVertexLValue*& clonep = m_clones[&vtx][component];
        if (!clonep) {
            DfgGraph& dfg = component == 0 ? m_dfg : *m_components[component - 1];
            if (DfgVarPacked* const pVtxp = vtx.cast<DfgVarPacked>()) {
                clonep = new DfgVarPacked{dfg, pVtxp->varp()};
            } else if (DfgVarArray* const aVtxp = vtx.cast<DfgVarArray>()) {
                clonep = new DfgVarArray{dfg, aVtxp->varp()};
            }
            UASSERT_OBJ(clonep, &vtx, "Unhandled 'DfgVertexLValue' sub-type");
            if (VL_UNLIKELY(m_doExpensiveChecks)) {
                // Assign component number of clone for later checks
                m_state
                    .emplace(std::piecewise_construct, std::forward_as_tuple(clonep),
                             std::forward_as_tuple(0))
                    .first->second.component
                    = component;
            }
            // We need to mark both the original and the clone as having additional references
            vtx.setHasModRefs();
            clonep->setHasModRefs();
        }
        return *clonep;
    }

    // Fix up non-variable sources of a DfgVertexLValue that are in a different component,
    // using the provided 'relink' callback
    template <typename T_Vertex>
    void fixSources(T_Vertex& vtx, std::function<void(T_Vertex&, DfgVertex&, size_t)> relink) {
        static_assert(std::is_base_of<DfgVertexLValue, T_Vertex>::value,
                      "'Vertex' must be a 'DfgVertexLValue'");
        const size_t component = m_state.at(&vtx).component;
        vtx.forEachSourceEdge([&](DfgEdge& edge, size_t idx) {
            DfgVertex& source = *edge.sourcep();
            // DfgVertexLValue sources are fixed up by `fixSinks` on those sources
            if (source.is<DfgVarPacked>() || source.is<DfgVarArray>()) return;
            const size_t sourceComponent = m_state.at(&source).component;
            // Same component is OK
            if (sourceComponent == component) return;
            // Unlink the source edge (source is reconnected by 'relink'
            edge.unlinkSource();
            // Apply the fixup
            DfgVertexLValue& clone = getClone(vtx, sourceComponent);
            relink(*(clone.as<T_Vertex>()), source, idx);
        });
    }

    // Fix up sinks of given variable vertex that are in a different component
    void fixSinks(DfgVertexLValue& vtx) {
        const size_t component = m_state.at(&vtx).component;
        vtx.forEachSinkEdge([&](DfgEdge& edge) {
            const size_t sinkComponent = m_state.at(edge.sinkp()).component;
            // Same component is OK
            if (sinkComponent == component) return;
            // Relink the sink to read the clone
            edge.relinkSource(&getClone(vtx, sinkComponent));
        });
    }

    // Fix edges that cross components
    void fixEdges(DfgVertex& vtx) {
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

        if (VL_UNLIKELY(m_doExpensiveChecks)) {
            // Non-variable vertex. Just check that edges do not cross components
            const size_t component = m_state.at(&vtx).component;
            vtx.forEachSourceEdge([&](DfgEdge& edge, size_t) {
                DfgVertex& source = *edge.sourcep();
                // OK to cross at variables
                if (source.is<DfgVarPacked>() || source.is<DfgVarArray>()) return;
                UASSERT_OBJ(component == m_state.at(&source).component, &vtx,
                            "Component crossing edge without variable involvement");
            });
        }
    }

    static void packSources(DfgGraph& dfg) {
        // Remove undriven variable sources
        dfg.forEachVertex([&](DfgVertex& vtx) {
            if (DfgVarPacked* const vtxp = vtx.cast<DfgVarPacked>()) {
                vtxp->packSources();
                return;
            }
            if (DfgVarArray* const vtxp = vtx.cast<DfgVarArray>()) {
                vtxp->packSources();
                return;
            }
        });
    }

    static void checkEdges(DfgGraph& dfg) {
        // Check that each edge connects to a vertex that is within the same graph.
        // Also check variable vertex sources are all connected.
        std::unordered_set<const DfgVertex*> vertices{dfg.size()};
        dfg.forEachVertex([&](const DfgVertex& vtx) { vertices.insert(&vtx); });
        dfg.forEachVertex([&](const DfgVertex& vtx) {
            vtx.forEachSource([&](const DfgVertex& src) {
                UASSERT_OBJ(vertices.count(&src), &vtx, "Source vertex not in graph");
            });
            vtx.forEachSink([&](const DfgVertex& snk) {
                UASSERT_OBJ(vertices.count(&snk), &snk, "Sink vertex not in graph");
            });
            if (const DfgVarPacked* const vtxp = vtx.cast<DfgVarPacked>()) {
                vtxp->forEachSourceEdge([](const DfgEdge& edge, size_t) {
                    UASSERT_OBJ(edge.sourcep(), edge.sinkp(), "Missing source on variable vertex");
                });
                return;
            }
            if (const DfgVarArray* const vtxp = vtx.cast<DfgVarArray>()) {
                vtxp->forEachSourceEdge([](const DfgEdge& edge, size_t) {
                    UASSERT_OBJ(edge.sourcep(), edge.sinkp(), "Missing source on variable vertex");
                });
                return;
            }
        });
    }

    void extractComponents() {
        // If the graph was acyclic (which should be the common case), there will be no non-trivial
        // SCCs, so we are done.
        if (!m_nonTrivialSCCs) return;

        // Allocate result graphs
        m_components.resize(m_nonTrivialSCCs);
        for (size_t i = 0; i < m_nonTrivialSCCs; ++i) {
            m_components[i].reset(new DfgGraph{*m_dfg.modulep(), m_prefix + cvtToStr(i)});
        }

        // Fix up edges crossing components, and move vertices into their correct component. Note
        // that fixing up the edges can create clones. Clones are added to the correct component,
        // which also means that they might be added to the original DFG. Clones do not need
        // fixing up, but also are not necessarily in the m_state map (in fact they are only there
        // in debug mode), so we only iterate up to the original vertices. Because any new vertex
        // is added at the end of the vertex list, we can just do this by iterating a fixed number
        // of vertices.
        size_t vertexCount = m_dfg.size();
        m_dfg.forEachVertex([&](DfgVertex& vtx) {
            if (!vertexCount) return;
            --vertexCount;
            // Fix up the edges crossing components
            fixEdges(vtx);
            // Move the vertex to the component graph (leave component 0, which is the originally
            // acyclic sub-graph, in the original graph)
            if (const size_t component = m_state.at(&vtx).component) {
                m_dfg.removeVertex(vtx);
                m_components[component - 1]->addVertex(vtx);
            }
        });

        // Pack sources of variables to remove the now undriven inputs
        // (cloning might have unlinked some of the inputs),
        packSources(m_dfg);
        for (const auto& dfgp : m_components) packSources(*dfgp);

        if (VL_UNLIKELY(m_doExpensiveChecks)) {
            // Check results for consistency
            checkEdges(m_dfg);
            for (const auto& dfgp : m_components) checkEdges(*dfgp);
        }
    }

    // CONSTRUCTOR - entry point
    explicit ExtractCyclicComponents(DfgGraph& dfg, std::string label)
        : m_dfg{dfg}
        , m_prefix{dfg.name() + (label.empty() ? "" : "-") + label + "-component-"} {
        // Find all the non-trivial SCCs (and trivial cycles) in the graph
        colorSCCs();
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

void DfgGraph::runToFixedPoint(std::function<bool(DfgVertex&)> f) {
    bool changed;
    const auto apply = [&](DfgVertex& vtx) -> void {
        if (f(vtx)) changed = true;
    };
    while (true) {
        // Do one pass over the graph.
        changed = false;
        forEachVertex(apply);
        if (!changed) break;
        // Do another pass in the opposite direction. Alternating directions reduces
        // the pathological complexity with left/right leaning trees.
        changed = false;
        forEachVertexInReverse(apply);
        if (!changed) break;
    }
}

static const string toDotId(const DfgVertex& vtx) { return '"' + cvtToHex(&vtx) + '"'; }

// Dump one DfgVertex in Graphviz format
static void dumpDotVertex(std::ostream& os, const DfgVertex& vtx) {
    os << toDotId(vtx);

    if (const DfgVarPacked* const varVtxp = vtx.cast<DfgVarPacked>()) {
        AstVar* const varp = varVtxp->varp();
        os << " [label=\"" << varp->name() << "\nW" << varVtxp->width() << " / F"
           << varVtxp->fanout() << '"';

        if (varp->direction() == VDirection::INPUT) {
            os << ", shape=box, style=filled, fillcolor=chartreuse2";  // Green
        } else if (varp->direction() == VDirection::OUTPUT) {
            os << ", shape=box, style=filled, fillcolor=cyan2";  // Cyan
        } else if (varp->direction() == VDirection::INOUT) {
            os << ", shape=box, style=filled, fillcolor=darkorchid2";  // Purple
        } else if (varVtxp->hasExtRefs()) {
            os << ", shape=box, style=filled, fillcolor=firebrick2";  // Red
        } else if (varVtxp->hasModRefs()) {
            os << ", shape=box, style=filled, fillcolor=gold2";  // Yellow
        } else if (varVtxp->keep()) {
            os << ", shape=box, style=filled, fillcolor=grey";
        } else {
            os << ", shape=box";
        }
        os << "]" << endl;
        return;
    }

    if (const DfgVarArray* const arrVtxp = vtx.cast<DfgVarArray>()) {
        AstVar* const varp = arrVtxp->varp();
        os << " [label=\"" << varp->name() << "[]\"";
        if (varp->direction() == VDirection::INPUT) {
            os << ", shape=box3d, style=filled, fillcolor=chartreuse2";  // Green
        } else if (varp->direction() == VDirection::OUTPUT) {
            os << ", shape=box3d, style=filled, fillcolor=cyan2";  // Cyan
        } else if (varp->direction() == VDirection::INOUT) {
            os << ", shape=box3d, style=filled, fillcolor=darkorchid2";  // Purple
        } else if (arrVtxp->hasExtRefs()) {
            os << ", shape=box3d, style=filled, fillcolor=firebrick2";  // Red
        } else if (arrVtxp->hasModRefs()) {
            os << ", shape=box3d, style=filled, fillcolor=gold2";  // Yellow
        } else if (arrVtxp->keep()) {
            os << ", shape=box3d, style=filled, fillcolor=grey";
        } else {
            os << ", shape=box3d";
        }
        os << "]" << endl;
        return;
    }

    if (const DfgConst* const constVtxp = vtx.cast<DfgConst>()) {
        const V3Number& num = constVtxp->constp()->num();
        os << " [label=\"";
        if (num.width() <= 32 && !num.isSigned()) {
            const bool feedsSel = !constVtxp->findSink<DfgVertex>([](const DfgVertex& vtx) {  //
                return !vtx.is<DfgSel>() && !vtx.is<DfgArraySel>();
            });
            if (feedsSel) {
                os << num.toUInt();
            } else {
                os << constVtxp->width() << "'d" << num.toUInt() << "\n";
                os << constVtxp->width() << "'h" << std::hex << num.toUInt() << std::dec;
            }
        } else {
            os << num.ascii();
        }
        os << '"';
        os << ", shape=plain";
        os << "]" << endl;
        return;
    }

    os << " [label=\"" << vtx.typeName() << "\nW" << vtx.width() << " / F" << vtx.fanout() << '"';
    if (vtx.hasMultipleSinks()) {
        os << ", shape=doublecircle";
    } else {
        os << ", shape=circle";
    }
    os << "]" << endl;
}

// Dump one DfgEdge in Graphviz format
static void dumpDotEdge(std::ostream& os, const DfgEdge& edge, const string& headlabel) {
    os << toDotId(*edge.sourcep()) << " -> " << toDotId(*edge.sinkp());
    if (!headlabel.empty()) os << " [headlabel=\"" << headlabel << "\"]";
    os << endl;
}

// Dump one DfgVertex and all of its source DfgEdges in Graphviz format
static void dumpDotVertexAndSourceEdges(std::ostream& os, const DfgVertex& vtx) {
    dumpDotVertex(os, vtx);
    vtx.forEachSourceEdge([&](const DfgEdge& edge, size_t idx) {  //
        if (edge.sourcep()) {
            string headLabel;
            if (vtx.arity() > 1 || vtx.is<DfgVarPacked>() || vtx.is<DfgVarArray>()) {
                headLabel = vtx.srcName(idx);
            }
            dumpDotEdge(os, edge, headLabel);
        }
    });
}

void DfgGraph::dumpDot(std::ostream& os, const string& label) const {
    // Header
    os << "digraph dfg {" << endl;
    os << "graph [label=\"" << name();
    if (!label.empty()) os << "-" << label;
    os << "\", labelloc=t, labeljust=l]" << endl;
    os << "graph [rankdir=LR]" << endl;

    // Emit all vertices
    forEachVertex([&](const DfgVertex& vtx) { dumpDotVertexAndSourceEdges(os, vtx); });

    // Footer
    os << "}" << endl;
}

void DfgGraph::dumpDotFile(const string& fileName, const string& label) const {
    // This generates a file used by graphviz, https://www.graphviz.org
    // "hardcoded" parameters:
    const std::unique_ptr<std::ofstream> os{V3File::new_ofstream(fileName)};
    if (os->fail()) v3fatal("Cannot write to file: " << fileName);
    dumpDot(*os.get(), label);
    os->close();
}

void DfgGraph::dumpDotFilePrefixed(const string& label) const {
    string fileName = name();
    if (!label.empty()) fileName += "-" + label;
    dumpDotFile(v3Global.debugFilename(fileName) + ".dot", label);
}

// Dump upstream logic cone starting from given vertex
static void dumpDotUpstreamConeFromVertex(std::ostream& os, const DfgVertex& vtx) {
    // Work queue for depth first traversal starting from this vertex
    std::vector<const DfgVertex*> queue{&vtx};

    // Set of already visited vertices
    std::unordered_set<const DfgVertex*> visited;

    // Depth first traversal
    while (!queue.empty()) {
        // Pop next work item
        const DfgVertex* const itemp = queue.back();
        queue.pop_back();

        // Mark vertex as visited
        const bool isFirstEncounter = visited.insert(itemp).second;

        // If we have already visited this vertex during the traversal, then move on.
        if (!isFirstEncounter) continue;

        // Enqueue all sources of this vertex.
        itemp->forEachSource([&](const DfgVertex& src) { queue.push_back(&src); });

        // Emit this vertex and all of its source edges
        dumpDotVertexAndSourceEdges(os, *itemp);
    }

    // Emit all DfgVarPacked vertices that have external references driven by this vertex
    vtx.forEachSink([&](const DfgVertex& dst) {
        if (const DfgVarPacked* const varVtxp = dst.cast<DfgVarPacked>()) {
            if (varVtxp->hasRefs()) dumpDotVertexAndSourceEdges(os, dst);
        }
    });
}

// LCOV_EXCL_START // Debug function for developer use only
void DfgGraph::dumpDotUpstreamCone(const string& fileName, const DfgVertex& vtx,
                                   const string& name) const {
    // Open output file
    const std::unique_ptr<std::ofstream> os{V3File::new_ofstream(fileName)};
    if (os->fail()) v3fatal("Cannot write to file: " << fileName);

    // Header
    *os << "digraph dfg {" << endl;
    if (!name.empty()) *os << "graph [label=\"" << name << "\", labelloc=t, labeljust=l]" << endl;
    *os << "graph [rankdir=LR]" << endl;

    // Dump the cone
    dumpDotUpstreamConeFromVertex(*os, vtx);

    // Footer
    *os << "}" << endl;

    // Done
    os->close();
}
// LCOV_EXCL_STOP

void DfgGraph::dumpDotAllVarConesPrefixed(const string& label) const {
    const string prefix = label.empty() ? name() + "-cone-" : name() + "-" + label + "-cone-";
    forEachVertex([&](const DfgVertex& vtx) {
        // Check if this vertex drives a variable referenced outside the DFG.
        const DfgVarPacked* const sinkp
            = vtx.findSink<DfgVarPacked>([](const DfgVarPacked& sink) {  //
                  return sink.hasRefs();
              });

        // We only dump cones driving an externally referenced variable
        if (!sinkp) return;

        // Open output file
        const string coneName{prefix + sinkp->varp()->name()};
        const string fileName{v3Global.debugFilename(coneName) + ".dot"};
        const std::unique_ptr<std::ofstream> os{V3File::new_ofstream(fileName)};
        if (os->fail()) v3fatal("Cannot write to file: " << fileName);

        // Header
        *os << "digraph dfg {" << endl;
        *os << "graph [label=\"" << coneName << "\", labelloc=t, labeljust=l]" << endl;
        *os << "graph [rankdir=LR]" << endl;

        // Dump this cone
        dumpDotUpstreamConeFromVertex(*os, vtx);

        // Footer
        *os << "}" << endl;

        // Done with this logic cone
        os->close();
    });
}

//------------------------------------------------------------------------------
// DfgEdge
//------------------------------------------------------------------------------

void DfgEdge::unlinkSource() {
    if (!m_sourcep) return;
#ifdef VL_DEBUG
    {
        DfgEdge* sinkp = m_sourcep->m_sinksp;
        while (sinkp) {
            if (sinkp == this) break;
            sinkp = sinkp->m_nextp;
        }
        UASSERT(sinkp, "'m_sourcep' does not have this edge as sink");
    }
#endif
    // Relink pointers of predecessor and successor
    if (m_prevp) m_prevp->m_nextp = m_nextp;
    if (m_nextp) m_nextp->m_prevp = m_prevp;
    // If head of list in source, update source's head pointer
    if (m_sourcep->m_sinksp == this) m_sourcep->m_sinksp = m_nextp;
    // Mark source as unconnected
    m_sourcep = nullptr;
    // Clear links. This is not strictly necessary, but might catch bugs.
    m_prevp = nullptr;
    m_nextp = nullptr;
}

void DfgEdge::relinkSource(DfgVertex* newSourcep) {
    // Unlink current source, if any
    unlinkSource();
    // Link new source
    m_sourcep = newSourcep;
    // Prepend to sink list in source
    m_nextp = newSourcep->m_sinksp;
    if (m_nextp) m_nextp->m_prevp = this;
    newSourcep->m_sinksp = this;
}

//------------------------------------------------------------------------------
// DfgVertex
//------------------------------------------------------------------------------

DfgVertex::DfgVertex(DfgGraph& dfg, FileLine* flp, AstNodeDType* dtypep, DfgType type)
    : m_filelinep{flp}
    , m_dtypep{dtypep}
    , m_type{type} {
    dfg.addVertex(*this);
}

DfgVertex::~DfgVertex() {
    // TODO: It would be best to intern these via AstTypeTable to save the effort
    if (VN_IS(m_dtypep, UnpackArrayDType)) VL_DO_DANGLING(delete m_dtypep, m_dtypep);
}

bool DfgVertex::selfEquals(const DfgVertex& that) const {
    return this->m_type == that.m_type && this->dtypep() == that.dtypep();
}

V3Hash DfgVertex::selfHash() const { return V3Hash{m_type} + width(); }

bool DfgVertex::equals(const DfgVertex& that, EqualsCache& cache) const {
    if (this == &that) return true;
    if (!this->selfEquals(that)) return false;

    const auto key = (this < &that) ? EqualsCache::key_type{this, &that}  //
                                    : EqualsCache::key_type{&that, this};
    const auto pair = cache.emplace(key, true);
    bool& result = pair.first->second;
    if (pair.second) {
        auto thisPair = this->sourceEdges();
        const DfgEdge* const thisSrcEdgesp = thisPair.first;
        const size_t thisArity = thisPair.second;
        auto thatPair = that.sourceEdges();
        const DfgEdge* const thatSrcEdgesp = thatPair.first;
        const size_t thatArity = thatPair.second;
        UASSERT_OBJ(thisArity == thatArity, this, "Same type vertices must have same arity!");
        for (size_t i = 0; i < thisArity; ++i) {
            const DfgVertex* const thisSrcVtxp = thisSrcEdgesp[i].m_sourcep;
            const DfgVertex* const thatSrcVtxp = thatSrcEdgesp[i].m_sourcep;
            if (thisSrcVtxp == thatSrcVtxp) continue;
            if (!thisSrcVtxp || !thatSrcVtxp || !thisSrcVtxp->equals(*thatSrcVtxp, cache)) {
                result = false;
                break;
            }
        }
    }
    return result;
}

V3Hash DfgVertex::hash(HashCache& cache) const {
    const auto pair = cache.emplace(this, V3Hash{});
    V3Hash& result = pair.first->second;
    if (pair.second) {
        result += selfHash();
        // Variables are defined by themselves, so there is no need to hash the sources. This
        // enables sound hashing of graphs circular only through variables, which we rely on.
        if (!is<DfgVarPacked>() && !is<DfgVarArray>()) {
            forEachSource([&result, &cache](const DfgVertex& src) { result += src.hash(cache); });
        }
    }
    return result;
}

uint32_t DfgVertex::fanout() const {
    uint32_t result = 0;
    forEachSinkEdge([&](const DfgEdge&) { ++result; });
    return result;
}

void DfgVertex::unlinkDelete(DfgGraph& dfg) {
    // Unlink source edges
    forEachSourceEdge([](DfgEdge& edge, size_t) { edge.unlinkSource(); });
    // Unlink sink edges
    forEachSinkEdge([](DfgEdge& edge) { edge.unlinkSource(); });
    // Remove from graph
    dfg.removeVertex(*this);
    // Delete
    delete this;
}

void DfgVertex::replaceWith(DfgVertex* newSorucep) {
    while (m_sinksp) m_sinksp->relinkSource(newSorucep);
}

//------------------------------------------------------------------------------
// Vertex classes
//------------------------------------------------------------------------------

// DfgVarPacked ----------
void DfgVarPacked::accept(DfgVisitor& visitor) { visitor.visit(this); }

bool DfgVarPacked::selfEquals(const DfgVertex& that) const {
    if (const DfgVarPacked* otherp = that.cast<DfgVarPacked>()) {
        UASSERT_OBJ(varp() != otherp->varp(), this,
                    "There should only be one DfgVarPacked for a given AstVar");
    }
    return false;
}

V3Hash DfgVarPacked::selfHash() const { return V3Hasher::uncachedHash(varp()); }

// DfgVarPacked ----------
void DfgVarArray::accept(DfgVisitor& visitor) { visitor.visit(this); }

bool DfgVarArray::selfEquals(const DfgVertex& that) const {
    if (const DfgVarArray* otherp = that.cast<DfgVarArray>()) {
        UASSERT_OBJ(varp() != otherp->varp(), this,
                    "There should only be one DfgVarArray for a given AstVar");
    }
    return false;
}

V3Hash DfgVarArray::selfHash() const { return V3Hasher::uncachedHash(varp()); }

// DfgConst ----------
void DfgConst::accept(DfgVisitor& visitor) { visitor.visit(this); }

bool DfgConst::selfEquals(const DfgVertex& that) const {
    if (const DfgConst* otherp = that.cast<DfgConst>()) {
        return constp()->sameTree(otherp->constp());
    }
    return false;
}

V3Hash DfgConst::selfHash() const { return V3Hasher::uncachedHash(m_constp); }

//------------------------------------------------------------------------------
// DfgVisitor
//------------------------------------------------------------------------------

void DfgVisitor::visit(DfgVarPacked* vtxp) { visit(static_cast<DfgVertex*>(vtxp)); }
void DfgVisitor::visit(DfgVarArray* vtxp) { visit(static_cast<DfgVertex*>(vtxp)); }
void DfgVisitor::visit(DfgConst* vtxp) { visit(static_cast<DfgVertex*>(vtxp)); }

//------------------------------------------------------------------------------
// 'astgen' generated definitions
//------------------------------------------------------------------------------

#include "V3Dfg__gen_definitions.h"
