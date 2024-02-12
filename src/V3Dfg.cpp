// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Data flow graph (DFG) representation of logic
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

#include "V3PchAstNoMT.h"  // VL_MT_DISABLED_CODE_UNIT

#include "V3Dfg.h"

#include "V3File.h"

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
    m_size += other.m_size;
    other.m_size = 0;

    const auto moveVertexList = [this](V3List<DfgVertex*>& src, V3List<DfgVertex*>& dst) {
        if (DfgVertex* vtxp = src.begin()) {
            vtxp->m_verticesEnt.moveAppend(src, dst, vtxp);
            do {
                vtxp->m_userCnt = 0;
                vtxp->m_graphp = this;
                vtxp = vtxp->verticesNext();
            } while (vtxp);
        }
    };

    moveVertexList(other.m_varVertices, m_varVertices);
    moveVertexList(other.m_constVertices, m_constVertices);
    moveVertexList(other.m_opVertices, m_opVertices);
}

static const string toDotId(const DfgVertex& vtx) { return '"' + cvtToHex(&vtx) + '"'; }

// Dump one DfgVertex in Graphviz format
static void dumpDotVertex(std::ostream& os, const DfgVertex& vtx) {

    if (const DfgVarPacked* const varVtxp = vtx.cast<DfgVarPacked>()) {
        AstVar* const varp = varVtxp->varp();
        os << toDotId(vtx);
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
            os << ", shape=box, style=filled, fillcolor=darkorange1";  // Orange
        } else if (varVtxp->hasDfgRefs()) {
            os << ", shape=box, style=filled, fillcolor=gold2";  // Yellow
        } else if (varVtxp->keep()) {
            os << ", shape=box, style=filled, fillcolor=grey";
        } else {
            os << ", shape=box";
        }
        os << "]\n";
        return;
    }

    if (const DfgVarArray* const arrVtxp = vtx.cast<DfgVarArray>()) {
        AstVar* const varp = arrVtxp->varp();
        const int elements = VN_AS(arrVtxp->dtypep(), UnpackArrayDType)->elementsConst();
        os << toDotId(vtx);
        os << " [label=\"" << varp->name() << "[" << elements << "]\"";
        if (varp->direction() == VDirection::INPUT) {
            os << ", shape=box3d, style=filled, fillcolor=chartreuse2";  // Green
        } else if (varp->direction() == VDirection::OUTPUT) {
            os << ", shape=box3d, style=filled, fillcolor=cyan2";  // Cyan
        } else if (varp->direction() == VDirection::INOUT) {
            os << ", shape=box3d, style=filled, fillcolor=darkorchid2";  // Purple
        } else if (arrVtxp->hasExtRefs()) {
            os << ", shape=box3d, style=filled, fillcolor=firebrick2";  // Red
        } else if (arrVtxp->hasModRefs()) {
            os << ", shape=box3d, style=filled, fillcolor=darkorange1";  // Orange
        } else if (arrVtxp->hasDfgRefs()) {
            os << ", shape=box3d, style=filled, fillcolor=gold2";  // Yellow
        } else if (arrVtxp->keep()) {
            os << ", shape=box3d, style=filled, fillcolor=grey";
        } else {
            os << ", shape=box3d";
        }
        os << "]\n";
        return;
    }

    if (const DfgConst* const constVtxp = vtx.cast<DfgConst>()) {
        const V3Number& num = constVtxp->num();

        os << toDotId(vtx);
        os << " [label=\"";
        if (num.width() <= 32 && !num.isSigned()) {
            os << constVtxp->width() << "'d" << num.toUInt() << "\n";
            os << constVtxp->width() << "'h" << std::hex << num.toUInt() << std::dec;
        } else {
            os << num.ascii();
        }
        os << '"';
        os << ", shape=plain";
        os << "]\n";
        return;
    }

    if (const DfgSel* const selVtxp = vtx.cast<DfgSel>()) {
        const uint32_t lsb = selVtxp->lsb();
        const uint32_t msb = lsb + selVtxp->width() - 1;
        os << toDotId(vtx);
        os << " [label=\"SEL\n_[" << msb << ":" << lsb << "]\nW" << vtx.width() << " / F"
           << vtx.fanout() << '"';
        if (vtx.hasMultipleSinks()) {
            os << ", shape=doublecircle";
        } else {
            os << ", shape=circle";
        }
        os << "]\n";
        return;
    }

    os << toDotId(vtx);
    os << " [label=\"" << vtx.typeName() << "\nW" << vtx.width() << " / F" << vtx.fanout() << '"';
    if (vtx.hasMultipleSinks()) {
        os << ", shape=doublecircle";
    } else {
        os << ", shape=circle";
    }
    os << "]\n";
}

// Dump one DfgEdge in Graphviz format
static void dumpDotEdge(std::ostream& os, const DfgEdge& edge, const string& headlabel) {
    os << toDotId(*edge.sourcep()) << " -> " << toDotId(*edge.sinkp());
    if (!headlabel.empty()) os << " [headlabel=\"" << headlabel << "\"]";
    os << "\n";
}

// Dump one DfgVertex and all of its source DfgEdges in Graphviz format
static void dumpDotVertexAndSourceEdges(std::ostream& os, const DfgVertex& vtx) {
    dumpDotVertex(os, vtx);
    vtx.forEachSourceEdge([&](const DfgEdge& edge, size_t idx) {  //
        if (edge.sourcep()) {
            string headLabel;
            if (vtx.arity() > 1 || vtx.is<DfgVertexVar>()) headLabel = vtx.srcName(idx);
            dumpDotEdge(os, edge, headLabel);
        }
    });
}

void DfgGraph::dumpDot(std::ostream& os, const string& label) const {
    // Header
    os << "digraph dfg {\n";
    os << "graph [label=\"" << name();
    if (!label.empty()) os << "-" << label;
    os << "\", labelloc=t, labeljust=l]\n";
    os << "graph [rankdir=LR]\n";

    // Emit all vertices
    forEachVertex([&](const DfgVertex& vtx) { dumpDotVertexAndSourceEdges(os, vtx); });

    // Footer
    os << "}\n";
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
            if (varVtxp->hasNonLocalRefs()) dumpDotVertexAndSourceEdges(os, dst);
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
    *os << "digraph dfg {\n";
    if (!name.empty()) *os << "graph [label=\"" << name << "\", labelloc=t, labeljust=l]\n";
    *os << "graph [rankdir=LR]\n";

    // Dump the cone
    dumpDotUpstreamConeFromVertex(*os, vtx);

    // Footer
    *os << "}\n";

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
                  return sink.hasNonLocalRefs();
              });

        // We only dump cones driving an externally referenced variable
        if (!sinkp) return;

        // Open output file
        const string coneName{prefix + sinkp->varp()->name()};
        const string fileName{v3Global.debugFilename(coneName) + ".dot"};
        const std::unique_ptr<std::ofstream> os{V3File::new_ofstream(fileName)};
        if (os->fail()) v3fatal("Cannot write to file: " << fileName);

        // Header
        *os << "digraph dfg {\n";
        *os << "graph [label=\"" << coneName << "\", labelloc=t, labeljust=l]\n";
        *os << "graph [rankdir=LR]\n";

        // Dump this cone
        dumpDotUpstreamConeFromVertex(*os, vtx);

        // Footer
        *os << "}\n";

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

DfgVertex::DfgVertex(DfgGraph& dfg, VDfgType type, FileLine* flp, AstNodeDType* dtypep)
    : m_filelinep{flp}
    , m_dtypep{dtypep}
    , m_type{type} {
    dfg.addVertex(*this);
}

DfgVertex::~DfgVertex() {
    // TODO: It would be best to intern these via AstTypeTable to save the effort
    if (VN_IS(m_dtypep, UnpackArrayDType)) VL_DO_DANGLING(delete m_dtypep, m_dtypep);
}

bool DfgVertex::selfEquals(const DfgVertex& that) const { return true; }

V3Hash DfgVertex::selfHash() const { return V3Hash{}; }

bool DfgVertex::equals(const DfgVertex& that, EqualsCache& cache) const {
    if (this == &that) return true;
    if (this->type() != that.type()) return false;
    if (this->dtypep() != that.dtypep()) return false;
    if (!this->selfEquals(that)) return false;

    const auto key = (this < &that) ? EqualsCache::key_type{this, &that}  //
                                    : EqualsCache::key_type{&that, this};
    // Note: the recursive invocation can cause a re-hash of the cache which invalidates iterators
    uint8_t result = cache[key];
    if (!result) {
        result = 2;  // Assume equals
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
                result = 1;  // Mark not equal
                break;
            }
        }
        cache[key] = result;
    }
    return result >> 1;
}

V3Hash DfgVertex::hash() {
    V3Hash& result = user<V3Hash>();
    if (!result.value()) {
        V3Hash hash{selfHash()};
        // Variables are defined by themselves, so there is no need to hash them further
        // (especially the sources). This enables sound hashing of graphs circular only through
        // variables, which we rely on.
        if (!is<DfgVertexVar>()) {
            hash += m_type;
            hash += width();  // Currently all non-variable vertices are packed, so this is safe
            const auto pair = sourceEdges();
            const DfgEdge* const edgesp = pair.first;
            const size_t arity = pair.second;
            // Sources must always be connected in well-formed graphs
            for (size_t i = 0; i < arity; ++i) hash += edgesp[i].m_sourcep->hash();
        }
        result = hash;
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

// DfgConst ----------

bool DfgConst::selfEquals(const DfgVertex& that) const {
    return num().isCaseEq(that.as<DfgConst>()->num());
}

V3Hash DfgConst::selfHash() const { return num().toHash(); }

// DfgSel ----------

bool DfgSel::selfEquals(const DfgVertex& that) const { return lsb() == that.as<DfgSel>()->lsb(); }

V3Hash DfgSel::selfHash() const { return V3Hash{lsb()}; }

// DfgVertexVar ----------

bool DfgVertexVar::selfEquals(const DfgVertex& that) const {
    UASSERT_OBJ(varp() != that.as<DfgVertexVar>()->varp(), this,
                "There should only be one DfgVertexVar for a given AstVar");
    return false;
}

V3Hash DfgVertexVar::selfHash() const {
    V3Hash hash;
    hash += m_varp->name();
    hash += m_varp->varType();
    return hash;
}

//------------------------------------------------------------------------------
// DfgVisitor
//------------------------------------------------------------------------------

#include "V3Dfg__gen_visitor_defns.h"  // From ./astgen
