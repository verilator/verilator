// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Dependency graph iterator. Iterates over nodes
//                         in any DAG, following dependency order.
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

#ifndef VERILATOR_V3GRAPHSTREAM_H_
#define VERILATOR_V3GRAPHSTREAM_H_

#include "config_build.h"
#include "verilatedos.h"

#include "V3Graph.h"

#include <functional>
#include <map>
#include <set>
#include <unordered_map>
#include <vector>

//######################################################################
// GraphStream
//
// Template 'T_Compare' is a tie-breaker for ordering nodes that the DAG
// itself does not order. It must provide an operator() that does a logical
// less-than on two V3GraphVertex*'s, with the same signature as
// std::less<const V3GraphVertex*>::operator().  This does not default to
// std::less<const V3GraphVertex*> because that is nondeterministic, and so
// not generally safe. If you want a raw pointer compare, see
// GraphStreamUnordered below.

template <class T_Compare>
class GraphStream final {
private:
    // TYPES
    class VxHolder final {
    public:
        // MEMBERS
        const V3GraphVertex* const m_vxp;  // [mtask] Vertex
        const uint32_t m_pos;  // Sort position
        uint32_t m_numBlockingEdges;  // Number of blocking edges
        // CONSTRUCTORS
        VxHolder(const V3GraphVertex* vxp, uint32_t pos, uint32_t numBlockingEdges)
            : m_vxp{vxp}
            , m_pos{pos}
            , m_numBlockingEdges{numBlockingEdges} {}
        // METHODS
        const V3GraphVertex* vertexp() const { return m_vxp; }
        // Decrement blocking edges count, return true if the vertex is
        // newly unblocked
        bool unblock() {
            UASSERT_OBJ(m_numBlockingEdges > 0, vertexp(), "Underflow of blocking edges");
            --m_numBlockingEdges;
            return (m_numBlockingEdges == 0);
        }
    };

    class VxHolderCmp final {
    public:
        // MEMBERS
        const T_Compare m_lessThan;  // Sorting functor
        // CONSTRUCTORS
        explicit VxHolderCmp(const T_Compare& lessThan)
            : m_lessThan{lessThan} {}
        // METHODS
        bool operator()(const VxHolder& a, const VxHolder& b) const {
            if (m_lessThan.operator()(a.vertexp(), b.vertexp())) return true;
            if (m_lessThan.operator()(b.vertexp(), a.vertexp())) return false;
            return a.m_pos < b.m_pos;
        }

    private:
        VL_UNCOPYABLE(VxHolderCmp);
    };

    using ReadyVertices = std::set<VxHolder, VxHolderCmp&>;

    // MEMBERS
    VxHolderCmp m_vxHolderCmp;  // Vertext comparison functor
    ReadyVertices m_readyVertices;  // List of ready vertices
    std::map<const V3GraphVertex*, VxHolder> m_waitingVertices;  // List of waiting vertices
    typename ReadyVertices::iterator m_last;  // Previously returned element
    const GraphWay m_way;  // FORWARD or REVERSE order of traversal

public:
    // CONSTRUCTORS
    explicit GraphStream(const V3Graph* graphp, GraphWay way = GraphWay::FORWARD,
                         const T_Compare& lessThan = T_Compare())
        // NOTE: Perhaps REVERSE way should also reverse the sense of the
        // lessThan function? For now the only usage of REVERSE is not
        // sensitive to its lessThan at all, so it doesn't matter.
        : m_vxHolderCmp{lessThan}
        , m_readyVertices{m_vxHolderCmp}
        , m_last{m_readyVertices.end()}
        , m_way{way} {
        uint32_t pos = 0;
        for (const V3GraphVertex* vxp = graphp->verticesBeginp(); vxp;
             vxp = vxp->verticesNextp()) {
            // Every vertex initially is waiting, or ready.
            if (way == GraphWay::FORWARD) {
                if (vxp->inEmpty()) {
                    const VxHolder newVx(vxp, pos++, 0);
                    m_readyVertices.insert(newVx);
                } else {
                    uint32_t depCount = 0;
                    for (V3GraphEdge* depp = vxp->inBeginp(); depp; depp = depp->inNextp()) {
                        ++depCount;
                    }
                    const VxHolder newVx(vxp, pos++, depCount);
                    m_waitingVertices.emplace(vxp, newVx);
                }
            } else {  // REVERSE
                if (vxp->outEmpty()) {
                    const VxHolder newVx(vxp, pos++, 0);
                    m_readyVertices.insert(newVx);
                } else {
                    uint32_t depCount = 0;
                    for (V3GraphEdge* depp = vxp->outBeginp(); depp; depp = depp->outNextp()) {
                        ++depCount;
                    }
                    const VxHolder newVx(vxp, pos++, depCount);
                    m_waitingVertices.emplace(vxp, newVx);
                }
            }
        }
    }
    ~GraphStream() = default;

    // METHODS

    // Each call to nextp() returns a unique vertex in the graph, in
    // dependency order.
    //
    // Dependencies alone don't fully specify the order. Usually a graph
    // has many "ready" vertices, any of which might return next.
    //
    // To decide among the "ready" vertices, GraphStream keeps an ordered
    // list of ready vertices, sorted first by lessThan and second by
    // original graph order.
    //
    // You might expect that nextp() would return the first item from this
    // sorted list -- but that's not what it does!  What nextp() actually
    // does is to return the next item in the list, following the position
    // where the previously-returned item would have been.  This maximizes
    // locality: given an appropriate lessThan, nextp() will stay on a
    // given domain (or domscope, or mtask, or whatever) for as long as
    // possible before an unmet dependency forces us to switch to another
    // one.
    //
    // Within a group of vertices that lessThan considers equivalent,
    // nextp() returns them in the original graph order (presumably also
    // good locality.) V3Order.cpp relies on this to order the logic
    // vertices within a given mtask without jumping over domains too much.
    const V3GraphVertex* nextp() {
        const V3GraphVertex* resultp = nullptr;

        typename ReadyVertices::iterator curIt;
        if (m_last == m_readyVertices.end()) {
            // First call to nextp()
            curIt = m_readyVertices.begin();
        } else {
            // Subsequent call to nextp()
            curIt = m_last;
            ++curIt;
            // Remove previously-returned element
            m_readyVertices.erase(m_last);
            // Wrap curIt. Expect to wrap, and make another pass, to find
            // newly-ready elements that could have appeared ahead of the
            // m_last iterator
            if (curIt == m_readyVertices.end()) curIt = m_readyVertices.begin();
        }

        if (curIt != m_readyVertices.end()) {
            resultp = curIt->vertexp();
            unblockDeps(resultp);
        } else {
            // No ready vertices; waiting should be empty too, otherwise we
            // were fed a graph with cycles (which is not supported.)
            UASSERT(m_waitingVertices.empty(), "DGS fed non-DAG");
        }

        m_last = curIt;
        return resultp;
    }

private:
    void unblockDeps(const V3GraphVertex* vertexp) {
        if (m_way == GraphWay::FORWARD) {
            for (V3GraphEdge* edgep = vertexp->outBeginp(); edgep; edgep = edgep->outNextp()) {
                const V3GraphVertex* const toVertexp = edgep->top();

                const auto it = m_waitingVertices.find(toVertexp);
                UASSERT_OBJ(it != m_waitingVertices.end(), toVertexp,
                            "Found edge into vertex not in waiting list.");
                if (it->second.unblock()) {
                    m_readyVertices.insert(it->second);
                    m_waitingVertices.erase(it);
                }
            }
        } else {
            for (V3GraphEdge* edgep = vertexp->inBeginp(); edgep; edgep = edgep->inNextp()) {
                const V3GraphVertex* const fromVertexp = edgep->fromp();

                const auto it = m_waitingVertices.find(fromVertexp);
                UASSERT_OBJ(it != m_waitingVertices.end(), fromVertexp,
                            "Found edge into vertex not in waiting list.");
                if (it->second.unblock()) {
                    m_readyVertices.insert(it->second);
                    m_waitingVertices.erase(it);
                }
            }
        }
    }

    VL_UNCOPYABLE(GraphStream);
};

//=================================================================================================
// GraphStreamUnordered is similar to GraphStream, but iterates un-ordered vertices (those that are
// not ordered by dependencies) in an arbitrary order. Iteration order is still deterministic.

class GraphStreamUnordered final {
    // MEMBERS
    const GraphWay m_way;  // Direction of traversal
    size_t m_nextIndex = 0;  // Which index to return from m_nextVertices next
    std::vector<const V3GraphVertex*> m_nextVertices;  // List of ready vertices returned next
    std::vector<const V3GraphVertex*> m_readyVertices;  // List of other ready vertices

public:
    // CONSTRUCTORS
    VL_UNCOPYABLE(GraphStreamUnordered);
    explicit GraphStreamUnordered(const V3Graph* graphp, GraphWay way = GraphWay::FORWARD)
        : m_way{way} {
        if (m_way == GraphWay::FORWARD) {
            init<GraphWay::FORWARD>(graphp);
        } else {
            init<GraphWay::REVERSE>(graphp);
        }
    }
    ~GraphStreamUnordered() = default;

    // METHODS

    // Each call to nextp() returns a unique vertex in the graph, in dependency order. Dependencies
    // alone do not specify a total ordering. Un-ordered vertices are returned in an arbitrary but
    // deterministic order.
    const V3GraphVertex* nextp() {
        if (VL_UNLIKELY(m_nextIndex == m_nextVertices.size())) {
            if (VL_UNLIKELY(m_readyVertices.empty())) return nullptr;
            m_nextIndex = 0;
            // Use swap to avoid reallocation
            m_nextVertices.swap(m_readyVertices);
            m_readyVertices.clear();
        }
        const V3GraphVertex* const resultp = m_nextVertices[m_nextIndex++];
        if (m_way == GraphWay::FORWARD) {
            return unblock<GraphWay::FORWARD>(resultp);
        } else {
            return unblock<GraphWay::REVERSE>(resultp);
        }
    }

private:
    template <uint8_t T_Way>  //
    VL_ATTR_NOINLINE void init(const V3Graph* graphp) {
        constexpr GraphWay way{T_Way};
        constexpr GraphWay inv = way.invert();
        // Assign every vertex without an incoming edge to ready, others to waiting
        for (V3GraphVertex *vertexp = graphp->verticesBeginp(), *nextp; vertexp; vertexp = nextp) {
            nextp = vertexp->verticesNextp();
            uint32_t nDeps = 0;
            for (V3GraphEdge* edgep = vertexp->beginp(inv); edgep; edgep = edgep->nextp(inv)) {
                ++nDeps;
            }
            vertexp->color(nDeps);  // Using color instead of user, as user might be used by client
            if (VL_UNLIKELY(nDeps == 0)) m_nextVertices.push_back(vertexp);
        }
    }

    template <uint8_t T_Way>  //
    VL_ATTR_NOINLINE const V3GraphVertex* unblock(const V3GraphVertex* resultp) {
        constexpr GraphWay way{T_Way};
        for (V3GraphEdge *edgep = resultp->beginp(way), *nextp; edgep; edgep = nextp) {
            nextp = edgep->nextp(way);
            V3GraphVertex* const vertexp = edgep->furtherp(way);
#if VL_DEBUG
            UASSERT_OBJ(vertexp->color() != 0, vertexp, "Should not be on waiting list");
#endif
            vertexp->color(vertexp->color() - 1);
            if (!vertexp->color()) m_readyVertices.push_back(vertexp);
        }
        return resultp;  // Returning input so we can tail call this method
    }
};

#endif  // Guard
