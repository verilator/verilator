// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Data flow graph (DFG) representation of logic
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

#include "V3PchAstNoMT.h"  // VL_MT_DISABLED_CODE_UNIT

#include "V3Dfg.h"

#include "V3File.h"

VL_DEFINE_DEBUG_FUNCTIONS;

//------------------------------------------------------------------------------
// DfgGraph
//------------------------------------------------------------------------------

DfgGraph::DfgGraph(AstModule* modulep, const string& name)
    : m_modulep{modulep}
    , m_name{name} {}

DfgGraph::~DfgGraph() {
    forEachVertex([](DfgVertex& vtxp) { delete &vtxp; });
}

void DfgGraph::addGraph(DfgGraph& other) {
    m_size += other.m_size;
    other.m_size = 0;

    for (DfgVertexVar& vtx : other.m_varVertices) {
        vtx.m_userCnt = 0;
        vtx.m_graphp = this;
    }
    m_varVertices.splice(m_varVertices.end(), other.m_varVertices);
    for (DfgConst& vtx : other.m_constVertices) {
        vtx.m_userCnt = 0;
        vtx.m_graphp = this;
    }
    m_constVertices.splice(m_constVertices.end(), other.m_constVertices);
    for (DfgVertex& vtx : other.m_opVertices) {
        vtx.m_userCnt = 0;
        vtx.m_graphp = this;
    }
    m_opVertices.splice(m_opVertices.end(), other.m_opVertices);
}

std::string DfgGraph::makeUniqueName(const std::string& prefix, size_t n) {
    // Construct the tmpNameStub if we have not done so yet
    if (m_tmpNameStub.empty()) {
        // Use the hash of the graph name (avoid long names and non-identifiers)
        const std::string name = V3Hash{m_name}.toString();
        // We need to keep every variable globally unique, and graph hashed
        // names might not be, so keep a static table to track multiplicity
        static std::unordered_map<std::string, uint32_t> s_multiplicity;
        m_tmpNameStub += '_' + name + '_' + std::to_string(s_multiplicity[name]++) + '_';
    }
    // Assemble the globally unique name
    return "__Vdfg" + prefix + m_tmpNameStub + std::to_string(n);
}

DfgVertexVar* DfgGraph::makeNewVar(FileLine* flp, const std::string& name, AstNodeDType* dtypep,
                                   AstScope* scopep) {
    UASSERT_OBJ(!!scopep != !!modulep(), flp,
                "makeNewVar scopep should only be provided for a scoped DfgGraph");

    // Create AstVar
    AstVar* const varp = new AstVar{flp, VVarType::MODULETEMP, name, dtypep};

    if (scopep) {
        // Add AstVar to the scope's module
        scopep->modp()->addStmtsp(varp);
        // Create AstVarScope
        AstVarScope* const vscp = new AstVarScope{flp, scopep, varp};
        // Add to scope
        scopep->addVarsp(vscp);
        // Create and return the corresponding variable vertex
        if (VN_IS(varp->dtypeSkipRefp(), UnpackArrayDType)) return new DfgVarArray{*this, vscp};
        return new DfgVarPacked{*this, vscp};
    } else {
        // Add AstVar to containing module
        modulep()->addStmtsp(varp);
        // Create and return the corresponding variable vertex
        if (VN_IS(varp->dtypeSkipRefp(), UnpackArrayDType)) return new DfgVarArray{*this, varp};
        return new DfgVarPacked{*this, varp};
    }
}

static const string toDotId(const DfgVertex& vtx) { return '"' + cvtToHex(&vtx) + '"'; }

// Dump one DfgVertex in Graphviz format
static void dumpDotVertex(std::ostream& os, const DfgVertex& vtx) {

    if (const DfgVarPacked* const varVtxp = vtx.cast<DfgVarPacked>()) {
        AstNode* const nodep = varVtxp->nodep();
        AstVar* const varp = varVtxp->varp();
        os << toDotId(vtx);
        os << " [label=\"" << nodep->name() << "\nW" << varVtxp->width() << " / F"
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
        AstNode* const nodep = arrVtxp->nodep();
        AstVar* const varp = arrVtxp->varp();
        const int elements = VN_AS(arrVtxp->dtypep(), UnpackArrayDType)->elementsConst();
        os << toDotId(vtx);
        os << " [label=\"" << nodep->name() << "[" << elements << "]\"";
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

void DfgGraph::dumpDotFile(const string& filename, const string& label) const {
    // This generates a file used by graphviz, https://www.graphviz.org
    // "hardcoded" parameters:
    const std::unique_ptr<std::ofstream> os{V3File::new_ofstream(filename)};
    if (os->fail()) v3fatal("Can't write file: " << filename);
    dumpDot(*os.get(), label);
    os->close();
}

void DfgGraph::dumpDotFilePrefixed(const string& label) const {
    string filename = name();
    if (!label.empty()) filename += "-" + label;
    dumpDotFile(v3Global.debugFilename(filename) + ".dot", label);
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
    if (os->fail()) v3fatal("Can't write file: " << fileName);

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
        const string coneName{prefix + sinkp->nodep()->name()};
        const string fileName{v3Global.debugFilename(coneName) + ".dot"};
        const std::unique_ptr<std::ofstream> os{V3File::new_ofstream(fileName)};
        if (os->fail()) v3fatal("Can't write file: " << fileName);

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

DfgVertex::~DfgVertex() {}

bool DfgVertex::selfEquals(const DfgVertex& that) const { return true; }

V3Hash DfgVertex::selfHash() const { return V3Hash{}; }

bool DfgVertex::equals(const DfgVertex& that, EqualsCache& cache) const {
    if (this == &that) return true;
    if (this->type() != that.type()) return false;
    if (this->dtypep() != that.dtypep()) return false;
    if (!this->selfEquals(that)) return false;

    const auto key = (this < &that) ? EqualsCache::key_type{this, &that}  //
                                    : EqualsCache::key_type{&that, this};
    // Note: the recursive invocation can cause a re-hash but that will not invalidate references
    uint8_t& result = cache[key];
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

DfgVarPacked* DfgVertex::getResultVar() {
    UASSERT_OBJ(!this->is<DfgVarArray>(), this, "Arrays are not supported by " << __FUNCTION__);

    // It's easy if the vertex is already a variable ...
    if (DfgVarPacked* const varp = this->cast<DfgVarPacked>()) return varp;

    // Inspect existing variables fully written by this vertex, and choose one
    DfgVarPacked* resp = nullptr;
    // cppcheck-has-bug-suppress constParameter
    this->forEachSink([&resp](DfgVertex& sink) {
        DfgVarPacked* const varp = sink.cast<DfgVarPacked>();
        if (!varp) return;
        if (!varp->isDrivenFullyByDfg()) return;
        // Ignore SystemC variables, they cannot participate in expressions or
        // be assigned rvalue expressions.
        if (varp->varp()->isSc()) return;
        // First variable found
        if (!resp) {
            resp = varp;
            return;
        }
        // Prefer those variables that must be kept anyway
        const bool keepOld = resp->keep() || resp->hasDfgRefs();
        const bool keepNew = varp->keep() || varp->hasDfgRefs();
        if (keepOld != keepNew) {
            if (!keepOld) resp = varp;
            return;
        }
        // Prefer those that already have module references
        if (resp->hasModRefs() != varp->hasModRefs()) {
            if (!resp->hasModRefs()) resp = varp;
            return;
        }
        // Prefer the earlier one in source order
        const FileLine& oldFlp = *(resp->fileline());
        const FileLine& newFlp = *(varp->fileline());
        if (const int cmp = oldFlp.operatorCompare(newFlp)) {
            if (cmp > 0) resp = varp;
            return;
        }
        // Prefer the one with the lexically smaller name
        if (const int cmp = resp->nodep()->name().compare(varp->nodep()->name())) {
            if (cmp > 0) resp = varp;
            return;
        }
        // 'resp' and 'varp' are all the same, keep using the existing 'resp'
    });
    return resp;
}

AstScope* DfgVertex::scopep(ScopeCache& cache, bool tryResultVar) VL_MT_DISABLED {
    // If this is a variable, we are done
    if (DfgVertexVar* const varp = this->cast<DfgVertexVar>()) return varp->varScopep()->scopep();

    // Try the result var first if instructed (usully only in the recursive case)
    if (tryResultVar) {
        if (DfgVertexVar* const varp = this->getResultVar()) return varp->varScopep()->scopep();
    }

    // Look up cache
    const auto pair = cache.emplace(this, nullptr);
    if (pair.second) {
        // Find scope based on sources, falling back on the root scope
        AstScope* const rootp = v3Global.rootp()->topScopep()->scopep();
        AstScope* foundp = rootp;
        const auto edges = sourceEdges();
        for (size_t i = 0; i < edges.second; ++i) {
            DfgEdge& edge = edges.first[i];
            foundp = edge.sourcep()->scopep(cache, true);
            if (foundp != rootp) break;
        }
        pair.first->second = foundp;
    }

    // If the cache entry exists, but have not set the mapping yet, then we have a circualr graph
    UASSERT_OBJ(pair.first->second, this,
                "DfgVertex::scopep called on graph with circular operations");

    // Done
    return pair.first->second;
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
    UASSERT_OBJ(nodep()->type() == that.as<DfgVertexVar>()->nodep()->type(), this,
                "Both DfgVertexVar should be scoped or unscoped");
    UASSERT_OBJ(nodep() != that.as<DfgVertexVar>()->nodep(), this,
                "There should only be one DfgVertexVar for a given AstVar or AstVarScope");
    return false;
}

V3Hash DfgVertexVar::selfHash() const {
    V3Hash hash;
    hash += nodep()->name();
    hash += varp()->varType();
    return hash;
}

//------------------------------------------------------------------------------
// DfgVisitor
//------------------------------------------------------------------------------

#include "V3Dfg__gen_visitor_defns.h"  // From ./astgen
