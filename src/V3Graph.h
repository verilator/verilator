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

#ifndef VERILATOR_V3GRAPH_H_
#define VERILATOR_V3GRAPH_H_

#include "config_build.h"
#include "verilatedos.h"

#include "V3Error.h"
#include "V3List.h"
#include "V3Rtti.h"
#include "V3ThreadSafety.h"

#include <algorithm>
#include <functional>

class FileLine;
class V3Graph;
class V3GraphVertex;
class V3GraphEdge;
class GraphAcycEdge;
class OrderEitherVertex;
class OrderLogicVertex;

//=============================================================================
// Most graph algorithms accept an arbitrary function that returns
// True for those edges we should honor.

using V3EdgeFuncP = bool (*)(const V3GraphEdge* edgep);

//=============================================================================
// When the Graph represents a directional acyclical graph (DAG), following
// the to() edges is forward, and back() is reverse.  However, sometimes
// it's useful to have algorithms that can walk in either direction, hence
// some methods take GraphWay to programmatically select the direction.

class GraphWay final {
public:
    enum en : uint8_t {
        FORWARD = 0,
        REVERSE = 1,
        NUM_WAYS = 2  // NUM_WAYS is not an actual way, it's typically
        //          // an array dimension or loop bound.
    };
    enum en m_e;
    GraphWay()
        : m_e{FORWARD} {}
    // cppcheck-suppress noExplicitConstructor
    constexpr GraphWay(en _e)
        : m_e{_e} {}
    explicit constexpr GraphWay(int _e)
        : m_e(static_cast<en>(_e)) {}  // Need () or GCC 4.8 false warning
    constexpr operator en() const { return m_e; }
    const char* ascii() const {
        static const char* const names[] = {"FORWARD", "REVERSE"};
        return names[m_e];
    }
    // METHODS unique to this class
    constexpr GraphWay invert() const { return GraphWay{m_e ^ 1}; }
    constexpr bool forward() const { return m_e == FORWARD; }
    constexpr bool reverse() const { return m_e != FORWARD; }
};
constexpr bool operator==(const GraphWay& lhs, const GraphWay& rhs) { return lhs.m_e == rhs.m_e; }
constexpr bool operator==(const GraphWay& lhs, GraphWay::en rhs) { return lhs.m_e == rhs; }
constexpr bool operator==(GraphWay::en lhs, const GraphWay& rhs) { return lhs == rhs.m_e; }

//============================================================================
// TODO should we have a smaller edge structure when we don't need weight etc?

class V3GraphEdge VL_NOT_FINAL {
    VL_RTTI_IMPL_BASE(V3GraphEdge)
    // Wires/variables aren't edges.  Edges have only a single to/from vertex
public:
    // ENUMS
    enum Cutable : uint8_t { NOT_CUTABLE = false, CUTABLE = true };  // For passing to V3GraphEdge
protected:
    friend class V3Graph;
    friend class V3GraphVertex;
    friend class GraphAcyc;
    friend class GraphAcycEdge;

    V3ListLinks<V3GraphEdge> m_oLinks;  // List links to store instances of this class (out edges)
    V3ListLinks<V3GraphEdge> m_iLinks;  // List links to store instances of this class (in edges)
    //
    V3GraphVertex* m_fromp;  // Vertices pointing to this edge
    V3GraphVertex* m_top;  // Vertices this edge points to
    int m_weight;  // Weight of the connection
    bool m_cutable;  // Interconnect may be broken in order sorting
    union {
        void* m_userp;  // Marker for some algorithms
        uint64_t m_user;  // Marker for some algorithms
    };
    // METHODS
    void init(V3Graph* graphp, V3GraphVertex* fromp, V3GraphVertex* top, int weight,
              bool cutable = false) VL_MT_DISABLED;
    void cut() { m_weight = 0; }  // 0 weight is same as disconnected
    // CONSTRUCTORS
protected:
    V3GraphEdge(V3Graph* graphp, V3GraphVertex* fromp, V3GraphVertex* top,
                const V3GraphEdge& old) VL_MT_DISABLED {
        init(graphp, fromp, top, old.m_weight, old.m_cutable);
    }

private:
    V3ListLinks<V3GraphEdge>& oLinks() { return m_oLinks; }
    V3ListLinks<V3GraphEdge>& iLinks() { return m_iLinks; }

public:
    // List types to store instances of this class
    using OList = V3List<V3GraphEdge, &V3GraphEdge::oLinks>;
    using IList = V3List<V3GraphEdge, &V3GraphEdge::iLinks>;

    //! Add DAG from one node to the specified node
    V3GraphEdge(V3Graph* graphp, V3GraphVertex* fromp, V3GraphVertex* top, int weight,
                bool cutable = false) VL_MT_DISABLED {
        init(graphp, fromp, top, weight, cutable);
    }
    //! Clone copy constructor.  Doesn't copy existing vertices or user/userp.
    virtual V3GraphEdge* clone(V3Graph* graphp, V3GraphVertex* fromp,
                               V3GraphVertex* top) const VL_MT_DISABLED {
        return new V3GraphEdge{graphp, fromp, top, *this};
    }
    virtual ~V3GraphEdge() = default;
    // METHODS
    // Return true iff of type T
    template <typename T>
    bool is() const {
        static_assert(std::is_base_of<V3GraphEdge, T>::value,
                      "'T' must be a subtype of V3GraphEdge");
        static_assert(std::is_same<typename std::remove_cv<T>::type,
                                   VTypeListFront<typename T::RttiThisAndBaseClassesList>>::value,
                      "Missing VL_RTTI_IMPL(...) call in 'T'");
        return this->isInstanceOfClassWithId(T::rttiClassId());
    }

    // Return cast to subtype T and assert of that type
    template <typename T>
    T* as() {
        UASSERT(is<T>(), "V3GraphEdge is not of expected type");
        return static_cast<T*>(this);
    }
    template <typename T>
    const T* as() const {
        UASSERT(is<T>(), "V3GraphEdge is not of expected type");
        return static_cast<const T*>(this);
    }

    // Return cast to subtype T, else nullptr if different type
    template <typename T>
    T* cast() {
        return is<T>() ? static_cast<T*>(this) : nullptr;
    }
    template <typename T>
    const T* cast() const {
        return is<T>() ? static_cast<const T*>(this) : nullptr;
    }

    virtual string name() const VL_MT_DISABLED;
    virtual string dotLabel() const { return ""; }
    virtual string dotColor() const { return cutable() ? "yellowGreen" : "red"; }
    virtual string dotStyle() const { return cutable() ? "dashed" : ""; }
    virtual int sortCmp(const V3GraphEdge* rhsp) const VL_MT_DISABLED;
    void unlinkDelete() VL_MT_DISABLED;
    void relinkFromp(V3GraphVertex* newFromp) VL_MT_DISABLED;
    void relinkTop(V3GraphVertex* newTop) VL_MT_DISABLED;
    // ACCESSORS
    int weight() const { return m_weight; }
    void weight(int weight) { m_weight = weight; }
    bool cutable() const { return m_cutable; }
    void cutable(bool cutable) { m_cutable = cutable; }
    void userp(void* user) { m_userp = user; }
    void* userp() const { return m_userp; }
    void user(uint64_t user) { m_user = user; }
    uint64_t user() const { return m_user; }
    V3GraphVertex* fromp() const { return m_fromp; }
    V3GraphVertex* top() const { return m_top; }
    template <GraphWay::en T_Way>
    V3GraphVertex* furtherp() const {
        return T_Way == GraphWay::FORWARD ? top() : fromp();
    }
    // STATIC ACCESSORS
    static bool followNotCutable(const V3GraphEdge* edgep) { return !edgep->m_cutable; }
    static bool followAlwaysTrue(const V3GraphEdge*) { return true; }
};

//============================================================================

class V3GraphVertex VL_NOT_FINAL {
    VL_RTTI_IMPL_BASE(V3GraphVertex)
    // Vertices may be a 'gate'/wire statement OR a variable
protected:
    friend class V3Graph;
    friend class V3GraphEdge;
    friend class GraphAcyc;
    friend class GraphAlgRank;
    V3ListLinks<V3GraphVertex> m_links;  // List links to store instances of this class
    V3GraphEdge::OList m_outs;  // List of outbound edges
    V3GraphEdge::IList m_ins;  // List of inbound edges
    double m_fanout;  // Order fanout
    uint32_t m_color;  // Color of the node
    uint32_t m_rank;  // Rank of edge
    union {
        void* m_userp;  // Marker for some algorithms
        uint32_t m_user;  // Marker for some algorithms
    };
    // ACCESSORS
    void fanout(double fanout) { m_fanout = fanout; }

protected:
    // CONSTRUCTORS
    V3GraphVertex(V3Graph* graphp, const V3GraphVertex& old) VL_MT_DISABLED;

private:
    V3ListLinks<V3GraphVertex>& links() { return m_links; }

public:
    // List types to store instances of this class
    using List = V3List<V3GraphVertex, &V3GraphVertex::links>;

    explicit V3GraphVertex(V3Graph* graphp) VL_MT_DISABLED;
    //! Clone copy constructor. Doesn't copy edges or user/userp.
    virtual V3GraphVertex* clone(V3Graph* graphp) const VL_MT_DISABLED {
        return new V3GraphVertex{graphp, *this};
    }
    virtual ~V3GraphVertex() = default;
    void unlinkEdges(V3Graph* graphp) VL_MT_DISABLED;
    void unlinkDelete(V3Graph* graphp) VL_MT_DISABLED;

    // METHODS
    // Return true iff of type T
    template <typename T>
    bool is() const {
        static_assert(std::is_base_of<V3GraphVertex, T>::value,
                      "'T' must be a subtype of V3GraphVertex");
        static_assert(std::is_same<typename std::remove_cv<T>::type,
                                   VTypeListFront<typename T::RttiThisAndBaseClassesList>>::value,
                      "Missing VL_RTTI_IMPL(...) call in 'T'");
        return this->isInstanceOfClassWithId(T::rttiClassId());
    }

    // Return cast to subtype T and assert of that type
    template <typename T>
    T* as() {
        UASSERT_OBJ(is<T>(), this, "V3GraphVertex is not of expected type");
        return static_cast<T*>(this);
    }
    template <typename T>
    const T* as() const {
        UASSERT_OBJ(is<T>(), this, "V3GraphVertex is not of expected type");
        return static_cast<const T*>(this);
    }

    // Return cast to subtype T, else nullptr if different type
    template <typename T>
    T* cast() {
        return is<T>() ? static_cast<T*>(this) : nullptr;
    }
    template <typename T>
    const T* cast() const {
        return is<T>() ? static_cast<const T*>(this) : nullptr;
    }

    // ACCESSORS
    virtual string name() const { return ""; }
    virtual string dotColor() const { return "black"; }
    virtual string dotShape() const { return ""; }
    virtual string dotStyle() const { return ""; }
    virtual string dotName() const { return ""; }
    virtual string dotRank() const { return ""; }
    virtual uint32_t rankAdder() const { return 1; }
    virtual FileLine* fileline() const { return nullptr; }  // nullptr for unknown
    virtual int sortCmp(const V3GraphVertex* rhsp) const {
        // LHS goes first if of lower rank, or lower fanout
        if (m_rank < rhsp->m_rank) return -1;
        if (m_rank > rhsp->m_rank) return 1;
        if (m_fanout < rhsp->m_fanout) return -1;
        if (m_fanout > rhsp->m_fanout) return 1;
        return 0;
    }
    uint32_t color() const { return m_color; }
    void color(uint32_t color) { m_color = color; }
    uint32_t rank() const { return m_rank; }
    void rank(uint32_t rank) { m_rank = rank; }
    double fanout() const { return m_fanout; }
    void user(uint32_t user) { m_user = user; }
    uint32_t user() const VL_MT_STABLE { return m_user; }
    void userp(void* userp) { m_userp = userp; }
    void* userp() const VL_MT_STABLE { return m_userp; }
    V3GraphEdge::IList& inEdges() { return m_ins; }
    const V3GraphEdge::IList& inEdges() const { return m_ins; }
    template <GraphWay::en T_Way>
    inline auto& edges();
    template <GraphWay::en T_Way>
    inline const auto& edges() const;
    bool inEmpty() const { return m_ins.empty(); }
    bool inSize1() const { return m_ins.hasSingleElement(); }
    V3GraphEdge::OList& outEdges() { return m_outs; }
    const V3GraphEdge::OList& outEdges() const { return m_outs; }
    bool outEmpty() const { return m_outs.empty(); }
    bool outSize1() const { return m_outs.hasSingleElement(); }
    // METHODS
    /// Error reporting
    void v3errorEnd(std::ostringstream& str) const VL_RELEASE(V3Error::s().m_mutex) VL_MT_DISABLED;
    void v3errorEndFatal(std::ostringstream& str) const
        VL_RELEASE(V3Error::s().m_mutex) VL_MT_DISABLED;
    /// Edges are routed around this vertex to point from "from" directly to "to"
    void rerouteEdges(V3Graph* graphp) VL_MT_DISABLED;
    // Find the edge connecting this vertex to the given vertex.
    // If edge is not found returns nullptr. O(edges) performance.
    template <GraphWay::en T_Way>
    V3GraphEdge* findConnectingEdgep(V3GraphVertex* otherp) VL_MT_DISABLED;
};

std::ostream& operator<<(std::ostream& os, V3GraphVertex* vertexp) VL_MT_DISABLED;

template <>
inline auto& V3GraphVertex::edges<GraphWay::FORWARD>() {
    return m_outs;
}

template <>
inline auto& V3GraphVertex::edges<GraphWay::REVERSE>() {
    return m_ins;
}

template <>
inline const auto& V3GraphVertex::edges<GraphWay::FORWARD>() const {
    return m_outs;
}

template <>
inline const auto& V3GraphVertex::edges<GraphWay::REVERSE>() const {
    return m_ins;
}

//============================================================================

class V3Graph VL_NOT_FINAL {
    // MEMBERS
    V3GraphVertex::List m_vertices;  // All vertices

protected:
    friend class V3GraphVertex;
    friend class V3GraphEdge;
    friend class GraphAcyc;
    // METHODS
    double orderDFSIterate(V3GraphVertex* vertexp) VL_MT_DISABLED;
    void dumpEdge(std::ostream& os, const V3GraphVertex& vertex,
                  const V3GraphEdge& edge) const VL_MT_DISABLED;
    // ACCESSORS

public:
    V3Graph() VL_MT_DISABLED;
    virtual ~V3Graph() VL_MT_DISABLED;
    virtual string dotRankDir() const { return "TB"; }  // rankdir for dot plotting

    // METHODS
    void clear() VL_MT_DISABLED;  // Empty it of all vertices/edges, as if making a new object
    bool empty() const { return m_vertices.empty(); }
    V3GraphVertex::List& vertices() { return m_vertices; }
    const V3GraphVertex::List& vertices() const { return m_vertices; }

    // METHODS - ALGORITHMS

    /// Clears color
    void clearColors() VL_MT_DISABLED;

    /// Assign same color to all vertices in the same weakly connected component
    /// Thus different color if there's no edges between the two subgraphs
    void weaklyConnected(V3EdgeFuncP edgeFuncp) VL_MT_DISABLED;

    /// Assign same color to all vertices that are strongly connected
    /// Thus different color if there's no directional circuit within the subgraphs.
    /// (I.E. all loops will occur within each color, not between them.)
    /// Side-effect: changes user()
    void stronglyConnected(V3EdgeFuncP edgeFuncp) VL_MT_DISABLED;

    /// Assign an ordering number to all vertexes in a tree.
    /// All nodes with no inputs will get rank 1
    /// Side-effect: changes user()
    void rank(V3EdgeFuncP edgeFuncp) VL_MT_DISABLED;
    void rank() VL_MT_DISABLED;

    /// Sort all vertices and edges using the V3GraphVertex::sortCmp() function
    void sortVertices() VL_MT_DISABLED;
    /// Sort all edges and edges using the V3GraphEdge::sortCmp() function
    void sortEdges() VL_MT_DISABLED;

    /// Order all vertices by rank and fanout, lowest first
    /// Sort all vertices by rank and fanout, lowest first
    /// Sort all edges by weight, lowest first
    /// Side-effect: assigns ranks to every node, and changes user()
    void order() VL_MT_DISABLED;

    /// Similar to order() but does not assign ranks. Caller must
    /// ensure that the graph has been ranked ahead of the call.
    /// Side-effect: assigns ranks to every node, and changes user()
    void orderPreRanked() VL_MT_DISABLED;

    /// Make acyclical (into a tree) by breaking a minimal subset of cutable edges.
    /// Side-effect: changes rank(), changes user()
    void acyclic(V3EdgeFuncP edgeFuncp) VL_MT_DISABLED;

    /// Remove any redundant edges, weights become MAX of any other weight
    /// Side-effect: changes user()
    void removeRedundantEdgesMax(V3EdgeFuncP edgeFuncp) VL_MT_DISABLED;

    /// Remove any redundant edges, weights become SUM of any other weight
    /// Side-effect: changes user()
    void removeRedundantEdgesSum(V3EdgeFuncP edgeFuncp) VL_MT_DISABLED;

    /// Remove any transitive edges.  E.g. if have edges A->B, B->C, and A->C
    /// then A->C is a "transitive" edge; it's implied by the first two
    /// (assuming the DAG is a dependency graph.)
    /// This algorithm can be expensive.
    void removeTransitiveEdges() VL_MT_DISABLED;

    /// Call loopsVertexCb on any one loop starting where specified
    /// Side-effect: changes user()
    void reportLoops(V3EdgeFuncP edgeFuncp, V3GraphVertex* vertexp) VL_MT_DISABLED;

    /// Build a subgraph of all loops starting where specified
    /// Side-effect: changes user()
    void subtreeLoops(V3EdgeFuncP edgeFuncp, V3GraphVertex* vertexp,
                      V3Graph* loopGraphp) VL_MT_DISABLED;

    /// Clear user()
    void userClearVertices() VL_MT_DISABLED;
    void userClearEdges() VL_MT_DISABLED;

    /// Debugging
    void dump(std::ostream& os = std::cout) const VL_MT_DISABLED;
    void dumpDotFile(const string& filename, bool colorAsSubgraph) const VL_MT_DISABLED;
    void dumpDotFilePrefixed(const string& nameComment,
                             bool colorAsSubgraph = false) const VL_MT_DISABLED;
    void dumpDotFilePrefixedAlways(const string& nameComment,
                                   bool colorAsSubgraph = false) const VL_MT_DISABLED;
    void dumpEdges(std::ostream& os, const V3GraphVertex& vertex) const VL_MT_DISABLED;
    static void selfTest() VL_MT_DISABLED;

    class ParallelismReport final {
        friend class GraphAlgParallelismReport;
        // Total cost of evaluating the whole graph. The ratio of m_totalGraphCost to
        // m_criticalPathCost gives us an estimate of the parallelizability of this graph which is
        // only as good as the guess returned by vertexCost.
        uint64_t m_totalGraphCost = 0;

        // Cost of the critical path, in abstract units (the same units returned by the vertexCost)
        uint64_t m_criticalPathCost = 0;

        uint64_t m_vertexCount = 0;  // Number of vertexes in the graph
        uint64_t m_edgeCount = 0;  // Number of edges in the grap

        ParallelismReport() = default;

    public:
        ~ParallelismReport() = default;
        ParallelismReport(const ParallelismReport&) = default;
        ParallelismReport& operator=(const ParallelismReport&) = default;

        uint64_t totalGraphCost() const { return m_totalGraphCost; }
        uint64_t criticalPathCost() const { return m_criticalPathCost; }
        uint64_t vertexCount() const { return m_vertexCount; }
        uint64_t edgeCount() const { return m_edgeCount; }
        double parallelismFactor() const {
            return (static_cast<double>(m_totalGraphCost) / m_criticalPathCost);
        }
    };

    ParallelismReport
    parallelismReport(std::function<uint64_t(const V3GraphVertex*)> vertexCost) VL_MT_DISABLED;

    // CALLBACKS
    virtual void loopsMessageCb(V3GraphVertex* vertexp) VL_MT_DISABLED;
    virtual void loopsVertexCb(V3GraphVertex* vertexp) VL_MT_DISABLED;
};

//============================================================================

#endif  // Guard
