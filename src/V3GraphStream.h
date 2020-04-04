// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Dependency graph iterator. Iterates over nodes
//                         in any DAG, following dependency order.
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2020 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#ifndef _V3GRAPHSTREAM_H_
#define _V3GRAPHSTREAM_H_

#include "config_build.h"
#include "verilatedos.h"

#include "V3Graph.h"

#include <set>
#include VL_INCLUDE_UNORDERED_MAP

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

template <class T_Compare> class GraphStream {
private:
    // TYPES
    class VxHolder {
    public:
        // MEMBERS
        const V3GraphVertex* m_vxp;  // [mtask] Vertex
        uint32_t m_pos;  // Sort position
        uint32_t m_numBlockingEdges;  // Number of blocking edges
        // CONSTRUCTORS
        VxHolder(const V3GraphVertex* vxp, uint32_t pos, uint32_t numBlockingEdges)
            : m_vxp(vxp)
            , m_pos(pos)
            , m_numBlockingEdges(numBlockingEdges) {}
        // METHODS
        const V3GraphVertex* vertexp() const { return m_vxp; }
        // Decrement blocking edges count, return true if the vertex is
        // newly unblocked
        bool unblock() {
            UASSERT_OBJ(m_numBlockingEdges > 0, vertexp(), "Underflow of blocking edges");
            m_numBlockingEdges--;
            return (m_numBlockingEdges == 0);
        }
    };

    class VxHolderCmp {
    public:
        // MEMBERS
        T_Compare m_lessThan;  // Sorting functor
        // CONSTRUCTORS
        explicit VxHolderCmp(const T_Compare& lessThan)
            : m_lessThan(lessThan) {}
        // METHODS
        bool operator() (const VxHolder& a, const VxHolder& b) const {
            if (m_lessThan.operator()(a.vertexp(), b.vertexp())) return true;
            if (m_lessThan.operator()(b.vertexp(), a.vertexp())) return false;
            return a.m_pos < b.m_pos;
        }
    private:
        VL_UNCOPYABLE(VxHolderCmp);
    };

    typedef std::set<VxHolder, VxHolderCmp&> ReadyVertices;
    typedef vl_unordered_map<const V3GraphVertex*, VxHolder> WaitingVertices;

    // MEMBERS
    VxHolderCmp m_vxHolderCmp;  // Vertext comparison functor
    ReadyVertices m_readyVertices;  // List of ready vertices
    WaitingVertices m_waitingVertices;  // List of waiting vertices
    typename ReadyVertices::iterator m_last;  // Previously returned element
    GraphWay m_way;  // FORWARD or REVERSE order of traversal

public:
    // CONSTRUCTORS
    explicit GraphStream(const V3Graph* graphp,
                         GraphWay way = GraphWay::FORWARD,
                         const T_Compare& lessThan = T_Compare())
        // NOTE: Perhaps REVERSE way should also reverse the sense of the
        // lessThan function? For now the only usage of REVERSE is not
        // sensitive to its lessThan at all, so it doesn't matter.
        : m_vxHolderCmp(lessThan)
        , m_readyVertices(m_vxHolderCmp)
        , m_last(m_readyVertices.end())
        , m_way(way) {
        uint32_t pos = 0;
        for (const V3GraphVertex* vxp = graphp->verticesBeginp();
             vxp; vxp=vxp->verticesNextp()) {
            // Every vertex initially is waiting, or ready.
            if (way == GraphWay::FORWARD) {
                if (vxp->inEmpty()) {
                    VxHolder newVx(vxp, pos++, 0);
                    m_readyVertices.insert(newVx);
                } else {
                    uint32_t depCount = 0;
                    for (V3GraphEdge* depp = vxp->inBeginp();
                         depp; depp = depp->inNextp()) {
                        depCount++;
                    }
                    VxHolder newVx(vxp, pos++, depCount);
                    m_waitingVertices.insert(make_pair(vxp, newVx));
                }
            } else {  // REVERSE
                if (vxp->outEmpty()) {
                    VxHolder newVx(vxp, pos++, 0);
                    m_readyVertices.insert(newVx);
                } else {
                    uint32_t depCount = 0;
                    for (V3GraphEdge* depp = vxp->outBeginp();
                         depp; depp = depp->outNextp()) {
                        depCount++;
                    }
                    VxHolder newVx(vxp, pos++, depCount);
                    m_waitingVertices.insert(make_pair(vxp, newVx));
                }
            }
        }
    }
    ~GraphStream() {}

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
        const V3GraphVertex* resultp = NULL;

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
            if (curIt == m_readyVertices.end()) {
                curIt = m_readyVertices.begin();
            }
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
            for (V3GraphEdge* edgep = vertexp->outBeginp();
                 edgep; edgep=edgep->outNextp()) {
                V3GraphVertex* toVertexp = edgep->top();

                typename WaitingVertices::iterator it =
                    m_waitingVertices.find(toVertexp);
                UASSERT_OBJ(it != m_waitingVertices.end(), toVertexp,
                            "Found edge into vertex not in waiting list.");
                if (it->second.unblock()) {
                    m_readyVertices.insert(it->second);
                    m_waitingVertices.erase(it);
                }
            }
        } else {
            for (V3GraphEdge* edgep = vertexp->inBeginp();
                 edgep; edgep=edgep->inNextp()) {
                V3GraphVertex* fromVertexp = edgep->fromp();

                typename WaitingVertices::iterator it =
                    m_waitingVertices.find(fromVertexp);
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

//######################################################################

// GraphStreamUnordered is GraphStream using a plain pointer compare to
// break ties in the graph order. This WILL return nodes in
// nondeterministic order.
typedef GraphStream<std::less<const V3GraphVertex*> > GraphStreamUnordered;

#endif  // Guard
