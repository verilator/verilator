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
#include <unordered_map>

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

std::vector<std::unique_ptr<DfgGraph>> DfgGraph::splitIntoComponents() {
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

    for (size_t i = 0; i < componentNumber; ++i) {
        results[i].reset(new DfgGraph{*m_modulep, name() + "-component-" + cvtToStr(i)});
    }

    // Move all vertices under the corresponding component graphs
    forEachVertex([&](DfgVertex& vtx) {
        this->removeVertex(vtx);
        results[vertex2component[&vtx]]->addVertex(vtx);
    });

    UASSERT(size() == 0, "'this' DfgGraph should have been emptied");

    return results;
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
    if (const DfgVar* const varVtxp = vtx.cast<DfgVar>()) {
        AstVar* const varp = varVtxp->varp();
        os << " [label=\"" << varp->name() << "\nW" << varVtxp->width() << " / F"
           << varVtxp->fanout() << '"';
        if (varp->isIO()) {
            if (varp->direction() == VDirection::INPUT) {
                os << ", shape=house, orientation=270";
            } else if (varp->direction() == VDirection::OUTPUT) {
                os << ", shape=house, orientation=90";
            } else {
                os << ", shape=star";
            }
        } else if (varVtxp->hasExtRefs()) {
            os << ", shape=box, style=diagonals,filled, fillcolor=red";
        } else if (varVtxp->hasModRefs()) {
            os << ", shape=box, style=diagonals";
        } else {
            os << ", shape=box";
        }
        os << "]";
    } else if (const DfgConst* const constVtxp = vtx.cast<DfgConst>()) {
        const V3Number& num = constVtxp->constp()->num();
        os << " [label=\"";
        if (num.width() <= 32 && !num.isSigned()) {
            const bool feedsSel = !constVtxp->findSink<DfgVertex>([](const DfgVertex& vtx) {  //
                return !vtx.is<DfgSel>();
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
        os << "]";
    } else {
        os << " [label=\"" << vtx.typeName() << "\nW" << vtx.width() << " / F" << vtx.fanout()
           << '"';
        if (vtx.hasMultipleSinks())
            os << ", shape=doublecircle";
        else
            os << ", shape=circle";
        os << "]";
    }
    os << endl;
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
            if (vtx.arity() > 1) headLabel = std::toupper(vtx.srcName(idx)[0]);
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

    // Emit all DfgVar vertices that have external references driven by this vertex
    vtx.forEachSink([&](const DfgVertex& dst) {
        if (const DfgVar* const varVtxp = dst.cast<DfgVar>()) {
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
        const DfgVar* const sinkp = vtx.findSink<DfgVar>([](const DfgVar& sink) {  //
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
        forEachSource([&result, &cache](const DfgVertex& src) { result += src.hash(cache); });
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

// DfgVar ----------
void DfgVar::accept(DfgVisitor& visitor) { visitor.visit(this); }

bool DfgVar::selfEquals(const DfgVertex& that) const {
    if (const DfgVar* otherp = that.cast<DfgVar>()) return varp() == otherp->varp();
    return false;
}

V3Hash DfgVar::selfHash() const { return V3Hasher::uncachedHash(m_varp); }

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

void DfgVisitor::visit(DfgVar* vtxp) { visit(static_cast<DfgVertex*>(vtxp)); }

void DfgVisitor::visit(DfgConst* vtxp) { visit(static_cast<DfgVertex*>(vtxp)); }

//------------------------------------------------------------------------------
// 'astgen' generated definitions
//------------------------------------------------------------------------------

#include "V3Dfg__gen_definitions.h"
