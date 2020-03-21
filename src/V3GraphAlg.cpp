// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Graph optimizations
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

#include "config_build.h"
#include "verilatedos.h"

#include "V3Global.h"
#include "V3GraphAlg.h"
#include "V3GraphPathChecker.h"

#include <cstdarg>
#include <algorithm>
#include <vector>
#include <map>
#include <list>

//######################################################################
//######################################################################
// Algorithms - delete

void V3Graph::deleteCutableOnlyEdges() {
    // Any vertices with only cutable edges will get deleted

    // Vertex::m_user begin: indicates can be deleted
    // Pass 1, mark those.  Don't delete now, as we don't want to rip out whole trees
    for (V3GraphVertex* vertexp = verticesBeginp(); vertexp; vertexp=vertexp->verticesNextp()) {
        vertexp->user(true);
        for (V3GraphEdge* edgep = vertexp->inBeginp(); edgep; edgep=edgep->inNextp()) {
            if (!edgep->cutable()) {
                vertexp->user(false);  // Can't delete it
                break;
            }
        }
        for (V3GraphEdge* edgep = vertexp->outBeginp(); edgep; edgep=edgep->outNextp()) {
            if (!edgep->cutable()) {
                vertexp->user(false);  // Can't delete it
                break;
            }
        }
    }

    // Pass 2, delete those marked
    // Rather than doing a delete() we set the weight to 0 which disconnects the edge.
    for (V3GraphVertex* vertexp = verticesBeginp(); vertexp; vertexp=vertexp->verticesNextp()) {
        if (vertexp->user()) {
            //UINFO(7,"Disconnect "<<vertexp->name()<<endl);
            for (V3GraphEdge* edgep = vertexp->outBeginp(); edgep; edgep=edgep->outNextp()) {
                edgep->cut();
            }
        }
    }

    // Vertex::m_user end, now unused
}

//######################################################################
//######################################################################
// Algorithms - weakly connected components

class GraphRemoveRedundant : GraphAlg<> {
    bool        m_sumWeights;  ///< Sum, rather then maximize weights
private:
    void main() {
        for (V3GraphVertex* vertexp = m_graphp->verticesBeginp();
             vertexp; vertexp=vertexp->verticesNextp()) {
            vertexIterate(vertexp);
        }
    }
    void vertexIterate(V3GraphVertex* vertexp) {
        // Clear marks
        for (V3GraphEdge* edgep = vertexp->outBeginp(); edgep; edgep=edgep->outNextp()) {
            edgep->top()->userp(NULL);
        }
        // Mark edges and detect duplications
        for (V3GraphEdge* nextp, *edgep = vertexp->outBeginp(); edgep; edgep=nextp) {
            nextp = edgep->outNextp();
            if (followEdge(edgep)) {
                V3GraphVertex* outVertexp = edgep->top();
                V3GraphEdge* prevEdgep = static_cast<V3GraphEdge*>(outVertexp->userp());
                if (!prevEdgep) {  // No previous assignment
                    outVertexp->userp(edgep);
                } else {  // Duplicate
                    bool saveOld = true;
                    if (prevEdgep->cutable() && !edgep->cutable()) {
                        saveOld = false;  // new !cutable more important than old
                    } else if (!prevEdgep->cutable() && edgep->cutable()) {
                        saveOld = true;  // old !cutable more important than new
                    } else {
                        saveOld = true;
                        if (!m_sumWeights && (prevEdgep->weight() < edgep->weight())) {  // Keep max weight
                            prevEdgep->weight(edgep->weight());
                        }
                    }
                    if (saveOld) {
                        if (m_sumWeights) prevEdgep->weight(prevEdgep->weight() + edgep->weight());
                        VL_DO_DANGLING(edgep->unlinkDelete(), edgep);
                    } else {
                        if (m_sumWeights) edgep->weight(prevEdgep->weight() + edgep->weight());
                        VL_DO_DANGLING(prevEdgep->unlinkDelete(), prevEdgep);
                        outVertexp->userp(edgep);
                    }
                }
            }
        }
    }
public:
    GraphRemoveRedundant(V3Graph* graphp, V3EdgeFuncP edgeFuncp, bool sumWeights)
        : GraphAlg<>(graphp, edgeFuncp), m_sumWeights(sumWeights) {
        main();
    }
    ~GraphRemoveRedundant() {}
};

void V3Graph::removeRedundantEdges(V3EdgeFuncP edgeFuncp) {
    GraphRemoveRedundant(this, edgeFuncp, false);
}
void V3Graph::removeRedundantEdgesSum(V3EdgeFuncP edgeFuncp) {
    GraphRemoveRedundant(this, edgeFuncp, true);
}

//######################################################################
//######################################################################
// Algorithms - remove transitive

class GraphAlgRemoveTransitiveEdges : GraphAlg<> {
public:
    explicit GraphAlgRemoveTransitiveEdges(V3Graph* graphp)
        : GraphAlg<>(graphp, NULL) {}
    void go() {
        GraphPathChecker checker(m_graphp);
        for (V3GraphVertex* vxp = m_graphp->verticesBeginp();
             vxp; vxp = vxp->verticesNextp()) {
            V3GraphEdge* deletep = NULL;
            for (V3GraphEdge* edgep = vxp->outBeginp();
                 edgep; edgep = edgep->outNextp()) {
                if (deletep) VL_DO_CLEAR(deletep->unlinkDelete(), deletep = NULL);
                // It should be safe to modify the graph, despite using
                // the GraphPathChecker, as none of the modifications will
                // change what can be reached from what, nor should they
                // change the rank or CP of any node.
                if (checker.isTransitiveEdge(edgep)) {
                    deletep = edgep;
                }
            }
            if (deletep) {
                VL_DO_DANGLING(deletep->unlinkDelete(), deletep);
            }
        }
    }
private:
    VL_DEBUG_FUNC;  // Declare debug()
    VL_UNCOPYABLE(GraphAlgRemoveTransitiveEdges);
};

void V3Graph::removeTransitiveEdges() {
    GraphAlgRemoveTransitiveEdges(this).go();
}

//######################################################################
//######################################################################
// Algorithms - weakly connected components

class GraphAlgWeakly : GraphAlg<> {
private:
    void main() {
        // Initialize state
        m_graphp->clearColors();
        // Color graph
        uint32_t currentColor = 0;
        for (V3GraphVertex* vertexp = m_graphp->verticesBeginp();
             vertexp; vertexp=vertexp->verticesNextp()) {
            currentColor ++;
            vertexIterate(vertexp, currentColor);
        }
    }

    void vertexIterate(V3GraphVertex* vertexp, uint32_t currentColor) {
        // Assign new color to each unvisited node
        // then visit each of its edges, giving them the same color
        if (vertexp->color()) return;  // Already colored it
        vertexp->color(currentColor);
        for (V3GraphEdge* edgep = vertexp->outBeginp(); edgep; edgep=edgep->outNextp()) {
            if (followEdge(edgep)) {
                vertexIterate(edgep->top(), currentColor);
            }
        }
        for (V3GraphEdge* edgep = vertexp->inBeginp(); edgep; edgep=edgep->inNextp()) {
            if (followEdge(edgep)) {
                vertexIterate(edgep->fromp(), currentColor);
            }
        }
    }
public:
    GraphAlgWeakly(V3Graph* graphp, V3EdgeFuncP edgeFuncp)
        : GraphAlg<>(graphp, edgeFuncp) {
        main();
    }
    ~GraphAlgWeakly() {}
};

void V3Graph::weaklyConnected(V3EdgeFuncP edgeFuncp) {
    GraphAlgWeakly(this, edgeFuncp);
}

//######################################################################
//######################################################################
// Algorithms - strongly connected components

class GraphAlgStrongly : GraphAlg<> {
private:
    uint32_t m_currentDfs;  // DFS count
    std::vector<V3GraphVertex*> m_callTrace;  // List of everything we hit processing so far

    void main() {
        // Use Tarjan's algorithm to find the strongly connected subgraphs.
        // Node State:
        //     Vertex::user     // DFS number indicating possible root of subtree, 0=not iterated
        //     Vertex::color    // Output subtree number (fully processed)

        // Clear info
        for (V3GraphVertex* vertexp = m_graphp->verticesBeginp();
             vertexp; vertexp=vertexp->verticesNextp()) {
            vertexp->color(0);
            vertexp->user(0);
        }
        // Color graph
        for (V3GraphVertex* vertexp = m_graphp->verticesBeginp();
             vertexp; vertexp=vertexp->verticesNextp()) {
            if (!vertexp->user()) {
                m_currentDfs++;
                vertexIterate(vertexp);
            }
        }
        // If there's a single vertex of a color, it doesn't need a subgraph
        // This simplifies the consumer's code, and reduces graph debugging clutter
        for (V3GraphVertex* vertexp = m_graphp->verticesBeginp();
             vertexp; vertexp=vertexp->verticesNextp()) {
            bool onecolor = true;
            for (V3GraphEdge* edgep = vertexp->outBeginp(); edgep; edgep=edgep->outNextp()) {
                if (followEdge(edgep)) {
                    if (vertexp->color() == edgep->top()->color()) {
                        onecolor = false;
                        break;
                    }
                }
            }
            if (onecolor) vertexp->color(0);
        }
    }

    void vertexIterate(V3GraphVertex* vertexp) {
        uint32_t thisDfsNum = m_currentDfs++;
        vertexp->user(thisDfsNum);
        vertexp->color(0);
        for (V3GraphEdge* edgep = vertexp->outBeginp(); edgep; edgep=edgep->outNextp()) {
            if (followEdge(edgep)) {
                V3GraphVertex* top = edgep->top();
                if (!top->user()) {  // Dest not computed yet
                    vertexIterate(top);
                }
                if (!top->color()) {  // Dest not in a component
                    if (vertexp->user() > top->user()) vertexp->user(top->user());
                }
            }
        }
        if (vertexp->user() == thisDfsNum) {  // New head of subtree
            vertexp->color(thisDfsNum);  // Mark as component
            while (!m_callTrace.empty()) {
                V3GraphVertex* popVertexp = m_callTrace.back();
                if (popVertexp->user() >= thisDfsNum) {  // Lower node is part of this subtree
                    m_callTrace.pop_back();
                    popVertexp->color(thisDfsNum);
                } else {
                    break;
                }
            }
        } else {  // In another subtree (maybe...)
            m_callTrace.push_back(vertexp);
        }
    }
public:
    GraphAlgStrongly(V3Graph* graphp, V3EdgeFuncP edgeFuncp)
        : GraphAlg<>(graphp, edgeFuncp) {
        m_currentDfs = 0;
        main();
    }
    ~GraphAlgStrongly() {}
};

void V3Graph::stronglyConnected(V3EdgeFuncP edgeFuncp) {
    GraphAlgStrongly(this, edgeFuncp);
}

//######################################################################
//######################################################################
// Algorithms - ranking

class GraphAlgRank : GraphAlg<> {
private:
    void main() {
        // Rank each vertex, ignoring cutable edges
        // Vertex::m_user begin: 1 indicates processing, 2 indicates completed
        // Clear existing ranks
        for (V3GraphVertex* vertexp = m_graphp->verticesBeginp();
             vertexp; vertexp=vertexp->verticesNextp()) {
            vertexp->rank(0);
            vertexp->user(0);
        }
        for (V3GraphVertex* vertexp = m_graphp->verticesBeginp();
             vertexp; vertexp=vertexp->verticesNextp()) {
            if (!vertexp->user()) {
                vertexIterate(vertexp, 1);
            }
        }
    }

    void vertexIterate(V3GraphVertex* vertexp, uint32_t currentRank) {
        // Assign rank to each unvisited node
        // If larger rank is found, assign it and loop back through
        // If we hit a back node make a list of all loops
        if (vertexp->user() == 1) {
            m_graphp->reportLoops(m_edgeFuncp, vertexp);
            m_graphp->loopsMessageCb(vertexp);
            return;
        }
        if (vertexp->rank() >= currentRank) return;  // Already processed it
        vertexp->user(1);
        vertexp->rank(currentRank);
        for (V3GraphEdge* edgep = vertexp->outBeginp(); edgep; edgep=edgep->outNextp()) {
            if (followEdge(edgep)) {
                vertexIterate(edgep->top(), currentRank + vertexp->rankAdder());
            }
        }
        vertexp->user(2);
    }
public:
    GraphAlgRank(V3Graph* graphp, V3EdgeFuncP edgeFuncp)
        : GraphAlg<>(graphp, edgeFuncp) {
        main();
    }
    ~GraphAlgRank() {}
};

void V3Graph::rank() {
    GraphAlgRank(this, &V3GraphEdge::followAlwaysTrue);
}

void V3Graph::rank(V3EdgeFuncP edgeFuncp) {
    GraphAlgRank(this, edgeFuncp);
}

//######################################################################
//######################################################################
// Algorithms - ranking

class GraphAlgRLoops : GraphAlg<> {
private:
    std::vector<V3GraphVertex*> m_callTrace;  // List of everything we hit processing so far
    bool m_done;  // Exit algorithm

    void main(V3GraphVertex* vertexp) {
        // Vertex::m_user begin: 1 indicates processing, 2 indicates completed
        // Clear existing ranks
        m_graphp->userClearVertices();
        m_callTrace.reserve(100);
        vertexIterate(vertexp, 0);
    }

    void vertexIterate(V3GraphVertex* vertexp, uint32_t currentRank) {
        // Assign rank to each unvisited node
        // When we hit ourself again, return the list of all loops
        if (m_done) return;

        // Can't just reserve(), unless we modify size() before setting array directly
        while (m_callTrace.size() <= currentRank) m_callTrace.push_back(vertexp);
        m_callTrace[currentRank++] = vertexp;

        if (vertexp->user() == 1) {
            for (unsigned i=0; i<currentRank; i++) {
                m_graphp->loopsVertexCb(m_callTrace[i]);
            }
            m_done = true;
            return;
        }
        if (vertexp->user() == 2) return;  // Already processed it
        vertexp->user(1);
        for (V3GraphEdge* edgep = vertexp->outBeginp(); edgep; edgep=edgep->outNextp()) {
            if (followEdge(edgep)) {
                vertexIterate(edgep->top(), currentRank);
            }
        }
        vertexp->user(2);
    }
public:
    GraphAlgRLoops(V3Graph* graphp, V3EdgeFuncP edgeFuncp, V3GraphVertex* vertexp)
        : GraphAlg<>(graphp, edgeFuncp) {
        m_done = false;
        main(vertexp);
    }
    ~GraphAlgRLoops() {}
};

void V3Graph::reportLoops(V3EdgeFuncP edgeFuncp, V3GraphVertex* vertexp) {
    GraphAlgRLoops(this, edgeFuncp, vertexp);
}


//######################################################################
//######################################################################
// Algorithms - subtrees

class GraphAlgSubtrees : GraphAlg<> {
private:
    V3Graph* m_loopGraphp;

    //! Iterate through all connected nodes of a graph with a loop or loops.
    V3GraphVertex* vertexIterateAll(V3GraphVertex* vertexp) {
        if (V3GraphVertex* newVertexp = static_cast<V3GraphVertex*>(vertexp->userp())) {
            return newVertexp;
        } else {
            newVertexp = vertexp->clone(m_loopGraphp);
            vertexp->userp(newVertexp);

            for (V3GraphEdge* edgep = vertexp->outBeginp();
                 edgep; edgep=edgep->outNextp()) {
                if (followEdge(edgep)) {
                    V3GraphEdge* newEdgep = static_cast<V3GraphEdge*>(edgep->userp());
                    if (!newEdgep) {
                        V3GraphVertex* newTop = vertexIterateAll(edgep->top());
                        newEdgep = edgep->clone(m_loopGraphp, newVertexp,
                                                newTop);
                        edgep->userp(newEdgep);
                    }
                }
            }
            return newVertexp;
        }
    }

public:
    GraphAlgSubtrees(V3Graph* graphp, V3Graph* loopGraphp,
                     V3EdgeFuncP edgeFuncp, V3GraphVertex* vertexp)
        : GraphAlg<>(graphp, edgeFuncp), m_loopGraphp(loopGraphp) {
        // Vertex::m_userp - New vertex if we have seen this vertex already
        // Edge::m_userp - New edge if we have seen this edge already
        m_graphp->userClearVertices();
        m_graphp->userClearEdges();
        (void) vertexIterateAll(vertexp);
    }
    ~GraphAlgSubtrees() {}
};

//! Report the entire connected graph with a loop or loops
void V3Graph::subtreeLoops(V3EdgeFuncP edgeFuncp, V3GraphVertex* vertexp,
                           V3Graph* loopGraphp) {
    GraphAlgSubtrees(this, loopGraphp, edgeFuncp, vertexp);
}

//######################################################################
//######################################################################
// Algorithms - make non cutable

void V3Graph::makeEdgesNonCutable(V3EdgeFuncP edgeFuncp) {
    for (V3GraphVertex* vertexp = verticesBeginp(); vertexp; vertexp=vertexp->verticesNextp()) {
        // Only need one direction, we'll always see the other at some point...
        for (V3GraphEdge* edgep = vertexp->inBeginp(); edgep; edgep = edgep->inNextp()) {
            if (edgep->cutable() && edgep->weight() && (edgeFuncp)(edgep)) {
                edgep->cutable(false);
            }
        }
    }
}

//######################################################################
//######################################################################
// Algorithms - sorting

struct GraphSortVertexCmp {
    inline bool operator() (const V3GraphVertex* lhsp, const V3GraphVertex* rhsp) const {
        return lhsp->sortCmp(rhsp) < 0;
    }
};
struct GraphSortEdgeCmp {
    inline bool operator() (const V3GraphEdge* lhsp, const V3GraphEdge* rhsp) const {
        return lhsp->sortCmp(rhsp) < 0;
    }
};

void V3Graph::sortVertices() {
    // Sort list of vertices by rank, then fanout
    std::vector<V3GraphVertex*> vertices;
    for (V3GraphVertex* vertexp = verticesBeginp(); vertexp; vertexp=vertexp->verticesNextp()) {
        vertices.push_back(vertexp);
    }
    std::stable_sort(vertices.begin(), vertices.end(), GraphSortVertexCmp());
    this->verticesUnlink();
    for (std::vector<V3GraphVertex*>::iterator it = vertices.begin(); it!=vertices.end(); ++it) {
        (*it)->verticesPushBack(this);
    }
}

void V3Graph::sortEdges() {
    // Sort edges by rank then fanout of node they point to
    std::vector<V3GraphEdge*> edges;
    for (V3GraphVertex* vertexp = verticesBeginp(); vertexp; vertexp=vertexp->verticesNextp()) {
        // Make a vector
        for (V3GraphEdge* edgep = vertexp->outBeginp(); edgep; edgep = edgep->outNextp()) {
            edges.push_back(edgep);
        }
        // Sort
        std::stable_sort(edges.begin(), edges.end(), GraphSortEdgeCmp());

        // Relink edges in specified order
        // We know the vector contains all of the edges that were
        // there originally (didn't delete or add)
        vertexp->outUnlink();
        for (std::vector<V3GraphEdge*>::const_iterator it = edges.begin(); it!=edges.end(); ++it) {
            (*it)->outPushBack();
        }
        // Prep for next
        edges.clear();
    }
}

//######################################################################
//######################################################################
// Algorithms - ordering
//      Compute near optimal ordering of the nodes, where:
//          If a required    edge is A->B, rank(A)<rank(B)
//          Visit edges and assign ranks to keep minimal crossings
//              (Results in better dcache packing.)

void V3Graph::order() {
    UINFO(2,"Order:\n");

    // Compute rankings again
    rank(&V3GraphEdge::followAlwaysTrue);
    orderPreRanked();
}

void V3Graph::orderPreRanked() {
    // Compute fanouts
    // Vertex::m_user begin: 1 indicates processing, 2 indicates completed
    userClearVertices();
    for (V3GraphVertex* vertexp = verticesBeginp(); vertexp; vertexp=vertexp->verticesNextp()) {
        if (!vertexp->user()) {
            orderDFSIterate(vertexp);
        }
    }

    // Sort list of vertices by rank, then fanout. Fanout is a bit of a
    // misnomer. It is the sum of all the fanouts of nodes reached from a node
    // *plus* the count of edges in to that node.
    sortVertices();
    // Sort edges by rank then fanout of node they point to
    sortEdges();
}

double V3Graph::orderDFSIterate(V3GraphVertex* vertexp) {
    // Compute fanouts of each node
    // If forward edge, don't double count that fanout
    if (vertexp->user() == 2) return vertexp->fanout();  // Already processed it
    UASSERT_OBJ(vertexp->user() != 1, vertexp, "Loop found, backward edges should be dead");
    vertexp->user(1);
    double fanout = 0;
    for (V3GraphEdge* edgep = vertexp->outBeginp(); edgep; edgep = edgep->outNextp()) {
        if (edgep->weight()) fanout += orderDFSIterate(edgep->m_top);
    }
    // Just count inbound edges
    for (V3GraphEdge* edgep = vertexp->inBeginp(); edgep; edgep = edgep->inNextp()) {
        if (edgep->weight()) fanout ++;
    }
    vertexp->fanout(fanout);
    vertexp->user(2);
    return vertexp->fanout();
}
