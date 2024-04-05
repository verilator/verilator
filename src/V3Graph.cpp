// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Graph optimizations
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

#define VL_MT_DISABLED_CODE_UNIT 1

#include "config_build.h"
#include "verilatedos.h"

#include "V3Graph.h"

#include "V3File.h"
#include "V3Global.h"

#include <map>
#include <memory>
#include <unordered_map>
#include <unordered_set>
#include <vector>

VL_DEFINE_DEBUG_FUNCTIONS;

//######################################################################
//######################################################################
// Vertices

V3GraphVertex::V3GraphVertex(V3Graph* graphp, const V3GraphVertex& old)
    : m_fanout{old.m_fanout}
    , m_color{old.m_color}
    , m_rank{old.m_rank} {
    m_userp = nullptr;
    graphp->vertices().linkBack(this);
}

V3GraphVertex::V3GraphVertex(V3Graph* graphp)
    : m_fanout{0}
    , m_color{0}
    , m_rank{0} {
    m_userp = nullptr;
    graphp->vertices().linkBack(this);
}

void V3GraphVertex::unlinkEdges(V3Graph*) {
    while (V3GraphEdge* const ep = m_outs.frontp()) VL_DO_DANGLING(ep->unlinkDelete(), ep);
    while (V3GraphEdge* const ep = m_ins.frontp()) VL_DO_DANGLING(ep->unlinkDelete(), ep);
}

void V3GraphVertex::unlinkDelete(V3Graph* graphp) {
    // Delete edges
    unlinkEdges(graphp);
    // Unlink from vertex list
    graphp->m_vertices.unlink(this);
    // Delete
    delete this;  // this=nullptr;
}

void V3GraphVertex::rerouteEdges(V3Graph* graphp) {
    // Make new edges for each from/to pair
    for (V3GraphEdge& iedge : inEdges()) {
        for (V3GraphEdge& oedge : outEdges()) {
            new V3GraphEdge{graphp, iedge.fromp(), oedge.top(),
                            std::min(iedge.weight(), oedge.weight()),
                            iedge.cutable() && oedge.cutable()};
        }
    }
    // Remove old edges
    unlinkEdges(graphp);
}

template <GraphWay::en T_Way>
V3GraphEdge* V3GraphVertex::findConnectingEdgep(V3GraphVertex* waywardp) {
    // O(edges) linear search. Searches search both nodes' edge lists in
    // parallel.  The lists probably aren't _both_ huge, so this is
    // unlikely to blow up even on fairly nasty graphs.
    constexpr GraphWay way{T_Way};
    constexpr GraphWay inv = way.invert();
    auto& aEdges = this->edges<way>();
    auto aIt = aEdges.begin();
    auto aEnd = aEdges.end();
    auto& bEdges = waywardp->edges<inv>();
    auto bIt = bEdges.begin();
    auto bEnd = bEdges.end();
    while (aIt != aEnd && bIt != bEnd) {
        V3GraphEdge& aedge = *aIt++;
        if (aedge.furtherp<way>() == waywardp) return &aedge;
        V3GraphEdge& bedge = *bIt++;
        if (bedge.furtherp<inv>() == this) return &bedge;
    }
    return nullptr;
}

template V3GraphEdge* V3GraphVertex::findConnectingEdgep<GraphWay::FORWARD>(V3GraphVertex*);
template V3GraphEdge* V3GraphVertex::findConnectingEdgep<GraphWay::REVERSE>(V3GraphVertex*);

// cppcheck-has-bug-suppress constParameter
void V3GraphVertex::v3errorEnd(std::ostringstream& str) const VL_RELEASE(V3Error::s().m_mutex) {
    std::ostringstream nsstr;
    nsstr << str.str();
    if (debug()) {
        nsstr << endl;
        nsstr << "-vertex: " << this << endl;
    }
    if (FileLine* const flp = fileline()) {
        flp->v3errorEnd(nsstr);
    } else {
        V3Error::v3errorEnd(nsstr);
    }
}
void V3GraphVertex::v3errorEndFatal(std::ostringstream& str) const
    VL_RELEASE(V3Error::s().m_mutex) {
    v3errorEnd(str);
    assert(0);  // LCOV_EXCL_LINE
    VL_UNREACHABLE;
}

std::ostream& operator<<(std::ostream& os, V3GraphVertex* vertexp) {
    os << "  VERTEX=" << vertexp->name();
    if (vertexp->rank()) os << " r" << vertexp->rank();
    if (vertexp->fanout() != 0.0) os << " f" << vertexp->fanout();
    if (vertexp->color()) os << " c" << vertexp->color();
    return os;
}

//######################################################################
//######################################################################
// Edges

void V3GraphEdge::init(V3Graph* /*graphp*/, V3GraphVertex* fromp, V3GraphVertex* top, int weight,
                       bool cutable) {
    UASSERT(fromp, "Null from pointer");
    UASSERT(top, "Null to pointer");
    m_fromp = fromp;
    m_top = top;
    m_weight = weight;
    m_cutable = cutable;
    m_userp = nullptr;
    // Link vertices to this edge
    m_fromp->outEdges().linkBack(this);
    m_top->inEdges().linkBack(this);
}

void V3GraphEdge::relinkFromp(V3GraphVertex* newFromp) {
    m_fromp->outEdges().unlink(this);
    m_fromp = newFromp;
    m_fromp->outEdges().linkBack(this);
}

void V3GraphEdge::relinkTop(V3GraphVertex* newTop) {
    m_top->inEdges().unlink(this);
    m_top = newTop;
    m_top->inEdges().linkBack(this);
}

void V3GraphEdge::unlinkDelete() {
    // Unlink from side
    m_fromp->outEdges().unlink(this);
    // Unlink to side
    m_top->inEdges().unlink(this);
    // Delete
    delete this;
}

std::string V3GraphEdge::name() const { return m_fromp->name() + "->" + m_top->name(); }

int V3GraphEdge::sortCmp(const V3GraphEdge* rhsp) const {
    if (!m_weight || !rhsp->m_weight) return 0;
    return top()->sortCmp(rhsp->top());
}

//######################################################################
//######################################################################
// Graph top level
// Constructors

V3Graph::V3Graph() {}

V3Graph::~V3Graph() { clear(); }

void V3Graph::clear() {
    // Empty it of all points, as if making a new object
    // Delete the old edges
    for (V3GraphVertex& vertex : vertices()) {
        while (V3GraphEdge* const edgep = vertex.outEdges().unlinkFront()) {
            VL_DO_DANGLING(delete edgep, edgep);
        }
    }
    // Delete the old vertices
    while (V3GraphVertex* const vertexp = vertices().unlinkFront()) {
        VL_DO_DANGLING(delete vertexp, vertexp);
    }
}

void V3Graph::userClearVertices() {
    // Clear user() in all of tree
    // We may use the userCnt trick in V3Ast later... (but gblCnt would be
    // in V3Graph instead of static - which has the complication of finding
    // the graph pointer given a vertex.)  For now, we don't call this often, and
    // the extra code on each read of user() would probably slow things
    // down more than help.
    for (V3GraphVertex& vertex : vertices()) {
        vertex.user(0);
        vertex.userp(nullptr);  // It's a union, but might be different size than user()
    }
}

void V3Graph::userClearEdges() {
    // Clear user() in all of tree
    for (V3GraphVertex& vertex : vertices()) {
        for (V3GraphEdge& edge : vertex.outEdges()) {
            edge.user(0);
            edge.userp(nullptr);  // It's a union, but might be different size than user()
        }
    }
}

void V3Graph::clearColors() {
    // Reset colors
    for (V3GraphVertex& vertex : vertices()) vertex.color(0);
}

//======================================================================
// Dumping

void V3Graph::loopsMessageCb(V3GraphVertex* vertexp) {
    vertexp->v3fatalSrc("Loops detected in graph: " << vertexp);
}

void V3Graph::loopsVertexCb(V3GraphVertex* vertexp) {
    // Needed here as V3GraphVertex<< isn't defined until later in header
    if (debug()) std::cerr << "-Info-Loop: " << cvtToHex(vertexp) << " " << vertexp << endl;
}

void V3Graph::dump(std::ostream& os) const {
    // This generates a file used by graphviz, https://www.graphviz.org
    os << " Graph:\n";
    // Print vertices
    for (const V3GraphVertex& vertex : vertices()) {
        os << "\tNode: " << vertex.name();
        if (vertex.color()) os << "  color=" << vertex.color();
        os << '\n';
        // Print edges
        for (const V3GraphEdge& edge : vertex.inEdges()) dumpEdge(os, vertex, edge);
        for (const V3GraphEdge& edge : vertex.outEdges()) dumpEdge(os, vertex, edge);
    }
}

void V3Graph::dumpEdge(std::ostream& os, const V3GraphVertex& vertex,
                       const V3GraphEdge& edge) const {
    if (edge.weight() && (edge.fromp() == &vertex || edge.top() == &vertex)) {
        os << "\t\t";
        if (edge.fromp() == &vertex) os << "-> " << edge.top()->name();
        if (edge.top() == &vertex) os << "<- " << edge.fromp()->name();
        if (edge.cutable()) os << "  [CUTABLE]";
        os << '\n';
    }
}
void V3Graph::dumpEdges(std::ostream& os, const V3GraphVertex& vertex) const {
    for (const V3GraphEdge& edge : vertex.inEdges()) dumpEdge(os, vertex, edge);
    for (const V3GraphEdge& edge : vertex.outEdges()) dumpEdge(os, vertex, edge);
}

void V3Graph::dumpDotFilePrefixed(const string& nameComment, bool colorAsSubgraph) const {
    dumpDotFile(v3Global.debugFilename(nameComment) + ".dot", colorAsSubgraph);
}

//! Variant of dumpDotFilePrefixed without --dump option check
void V3Graph::dumpDotFilePrefixedAlways(const string& nameComment, bool colorAsSubgraph) const {
    dumpDotFile(v3Global.debugFilename(nameComment) + ".dot", colorAsSubgraph);
}

void V3Graph::dumpDotFile(const string& filename, bool colorAsSubgraph) const {
    // This generates a file used by graphviz, https://www.graphviz.org
    // "hardcoded" parameters:
    const std::unique_ptr<std::ofstream> logp{V3File::new_ofstream(filename)};
    if (logp->fail()) v3fatal("Can't write " << filename);

    // Header
    *logp << "digraph v3graph {\n";
    *logp << "\tgraph\t[label=\"" << filename << "\",\n";
    *logp << "\t\t labelloc=t, labeljust=l,\n";
    *logp << "\t\t //size=\"7.5,10\",\n";
    *logp << "\t\t rankdir=" << dotRankDir() << "];\n";

    // List of all possible subgraphs
    // Collections of explicit ranks
    std::unordered_set<std::string> ranks;
    std::unordered_multimap<std::string, const V3GraphVertex*> rankSets;
    std::multimap<std::string, const V3GraphVertex*> subgraphs;
    for (const V3GraphVertex& vertex : vertices()) {
        const string vertexSubgraph
            = (colorAsSubgraph && vertex.color()) ? cvtToStr(vertex.color()) : "";
        subgraphs.emplace(vertexSubgraph, &vertex);
        const string& dotRank = vertex.dotRank();
        if (!dotRank.empty()) {
            ranks.emplace(dotRank);
            rankSets.emplace(dotRank, &vertex);
        }
    }

    // We use a map here, as we don't want to corrupt anything (userp) in the graph,
    // and we don't care if this is slow.
    std::unordered_map<const V3GraphVertex*, int> numMap;

    // Print vertices
    int n = 0;
    string subgr;
    for (auto it = subgraphs.cbegin(); it != subgraphs.cend(); ++it) {
        const string vertexSubgraph = it->first;
        const V3GraphVertex* vertexp = it->second;
        numMap[vertexp] = n;
        if (subgr != vertexSubgraph) {
            if (subgr != "") *logp << "\t};\n";
            subgr = vertexSubgraph;
            if (subgr != "") {
                *logp << "\tsubgraph cluster_" << subgr << " {\n";
                *logp << "\tlabel=\"" << subgr << "\"\n";
            }
        }
        if (subgr != "") *logp << "\t";
        *logp << "\tn" << vertexp->dotName() << (n++) << "\t[fontsize=8 "
              << "label=\"" << (vertexp->name() != "" ? vertexp->name() : "\\N");
        if (vertexp->rank()) *logp << " r" << vertexp->rank();
        if (vertexp->fanout() != 0.0) *logp << " f" << vertexp->fanout();
        if (vertexp->color()) *logp << "\\n c" << vertexp->color();
        *logp << "\"";
        *logp << ", color=" << vertexp->dotColor();
        if (vertexp->dotStyle() != "") *logp << ", style=" << vertexp->dotStyle();
        if (vertexp->dotShape() != "") *logp << ", shape=" << vertexp->dotShape();
        *logp << "];\n";
    }
    if (subgr != "") *logp << "\t};\n";

    // Print edges
    for (const V3GraphVertex& vertex : vertices()) {
        for (const V3GraphEdge& edge : vertex.outEdges()) {
            if (edge.weight()) {
                const int fromVnum = numMap[edge.fromp()];
                const int toVnum = numMap[edge.top()];
                *logp << "\tn" << edge.fromp()->dotName() << fromVnum << " -> n"
                      << edge.top()->dotName() << toVnum
                      << " ["
                      // <<"fontsize=8 label=\""<<(edge.name()!="" ? edge.name() : "\\E")<<"\""
                      << "fontsize=8 label=\"" << (edge.dotLabel() != "" ? edge.dotLabel() : "")
                      << "\""
                      << " weight=" << edge.weight() << " color=" << edge.dotColor();
                if (edge.dotStyle() != "") *logp << " style=" << edge.dotStyle();
                // if (edge.cutable()) *logp << ",constraint=false";  // to rank without
                // following edges
                *logp << "];\n";
            }
        }
    }

    // Print ranks
    for (const auto& dotRank : ranks) {
        *logp << "\t{ rank=";
        if (dotRank != "sink" && dotRank != "source" && dotRank != "min" && dotRank != "max") {
            *logp << "same";
        } else {
            *logp << dotRank;
        }
        *logp << "; ";
        auto bounds = rankSets.equal_range(dotRank);
        for (auto it{bounds.first}; it != bounds.second; ++it) {
            if (it != bounds.first) *logp << ", ";
            *logp << 'n' << numMap[it->second] << "";
        }
        *logp << " }\n";
    }

    // Vertex::m_user end, now unused

    // Trailer
    *logp << "}\n";
    logp->close();

    cout << "dot -Tpdf -o ~/a.pdf " << filename << "\n";
}
