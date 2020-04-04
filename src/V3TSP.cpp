// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Implementation of Christofides' algorithm to
//              approximate the solution to the traveling salesman problem.
//
// ISSUES: This isn't exactly Christofides algorithm; see the TODO
//         in perfectMatching(). True minimum-weight perfect matching
//         would produce a better result. How much better is TBD.
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

#include "V3Error.h"
#include "V3Global.h"
#include "V3File.h"
#include "V3Graph.h"
#include "V3TSP.h"

#include <cassert>
#include <cmath>
#include <fstream>
#include <limits>
#include <list>
#include <map>
#include <memory>
#include <set>
#include <sstream>
#include <string>
#include <utility>
#include <vector>
#include VL_INCLUDE_UNORDERED_SET
#include VL_INCLUDE_UNORDERED_MAP

//######################################################################
// Support classes

namespace V3TSP {
    static unsigned edgeIdNext = 0;

    static void selfTestStates();
    static void selfTestString();

    VL_DEBUG_FUNC;  // Declare debug()
}  // namespace V3TSP

// Vertex that tracks a per-vertex key
template <typename T_Key>
class TspVertexTmpl : public V3GraphVertex {
private:
    T_Key m_key;
public:
    TspVertexTmpl(V3Graph* graphp, const T_Key& k)
        : V3GraphVertex(graphp), m_key(k) {}
    virtual ~TspVertexTmpl() {}
    const T_Key& key() const { return m_key; }
private:
    VL_UNCOPYABLE(TspVertexTmpl);
};

// TspGraphTmpl represents a complete graph, templatized to work with
// different T_Key types.
template <typename T_Key>
class TspGraphTmpl : public V3Graph {
public:
    // TYPES
    typedef TspVertexTmpl<T_Key> Vertex;

    // MEMBERS
    typedef vl_unordered_map<T_Key, Vertex*> VMap;
    VMap m_vertices;  // T_Key to Vertex lookup map

    // CONSTRUCTORS
    TspGraphTmpl() : V3Graph() {}
    virtual ~TspGraphTmpl() {}

    // METHODS
    void addVertex(const T_Key &key) {
        typename VMap::iterator itr = m_vertices.find(key);
        UASSERT(itr == m_vertices.end(), "Vertex already exists with same key");
        Vertex *v = new Vertex(this, key);
        m_vertices[key] = v;
    }

    // For purposes of TSP, we are using non-directional graphs.
    // Map that onto the normally-directional V3Graph by creating
    // a matched pairs of opposite-directional edges to represent
    // each non-directional edge:
    void addEdge(const T_Key& from, const T_Key& to, int cost) {
        UASSERT(from != to, "Adding edge would form a loop");
        Vertex* fp = findVertex(from);
        Vertex* tp = findVertex(to);

        // No need to dedup edges.
        // The only time we may create duplicate edges is when
        // combining the MST with the perfect-matched pairs,
        // and in that case, we want to permit duplicate edges.
        unsigned edgeId = ++V3TSP::edgeIdNext;

        // Record the 'id' which identifies a single bidir edge
        // in the user field of each V3GraphEdge:
        (new V3GraphEdge(this, fp, tp, cost))->user(edgeId);
        (new V3GraphEdge(this, tp, fp, cost))->user(edgeId);
    }

    bool empty() const { return m_vertices.empty(); }

    std::list<Vertex*> keysToVertexList(const std::vector<T_Key>& odds) {
        std::list<Vertex*> vertices;
        for(unsigned i = 0; i < odds.size(); ++i) {
            vertices.push_back(findVertex(odds.at(i)));
        }
        return vertices;
    }

    class EdgeCmp {
        // Provides a deterministic compare for outgoing V3GraphEdge's
        // to be used in Prim's algorithm below. Also used in the
        // perfectMatching() routine.
    public:
        // CONSTRUCTORS
        EdgeCmp() {}
        // METHODS
        bool operator() (const V3GraphEdge* ap, const V3GraphEdge* bp) {
            int aCost = ap->weight();
            int bCost = bp->weight();
            // Sort first on cost, lowest cost edges first:
            if (aCost < bCost) return true;
            if (bCost < aCost) return false;
            // Costs are equal. Compare edgeId's which should be unique.
            return ap->user() < bp->user();
        }
    private:
        VL_UNCOPYABLE(EdgeCmp);
    };

    static Vertex* castVertexp(V3GraphVertex* vxp) {
        return dynamic_cast<Vertex*>(vxp);
    }

    // From *this, populate *mstp with the minimum spanning tree.
    // *mstp must be initially empty.
    void makeMinSpanningTree(TspGraphTmpl* mstp) {
        UASSERT(mstp->empty(), "Output graph must start empty");

        // Use Prim's algorithm to efficiently construct the MST.
        vl_unordered_set<Vertex*> visited_set;

        EdgeCmp cmp;
        typedef std::set<V3GraphEdge*, EdgeCmp&> PendingEdgeSet;
        // This is the set of pending edges from visited to unvisited
        // nodes.
        PendingEdgeSet pendingEdges(cmp);

        vluint32_t vertCount = 0;
        for (V3GraphVertex* vxp = verticesBeginp();
             vxp; vxp = vxp->verticesNextp()) {
            mstp->addVertex(castVertexp(vxp)->key());
            vertCount++;
        }

        // Choose an arbitrary start vertex and visit it;
        // all incident edges from this vertex go into a pending edge set.
        Vertex* start_vertexp = castVertexp(verticesBeginp());
        visited_set.insert(start_vertexp);
        for (V3GraphEdge* edgep = start_vertexp->outBeginp();
             edgep; edgep = edgep->outNextp()) {
            pendingEdges.insert(edgep);
        }

        // Repeatedly find the least costly edge in the pending set.
        // If it connects to an unvisited node, visit that node and update
        // the pending edge set. If it connects to an already visited node,
        // discard it and repeat again.
        unsigned edges_made = 0;
        while (!pendingEdges.empty()) {
            typename PendingEdgeSet::iterator firstIt = pendingEdges.begin();
            V3GraphEdge* bestEdgep = *firstIt;
            pendingEdges.erase(firstIt);

            // bestEdgep->fromp() should be already seen
            Vertex* from_vertexp = castVertexp(bestEdgep->fromp());
            UASSERT(visited_set.find(from_vertexp) != visited_set.end(), "Can't find vertex");

            // If the neighbor is not yet visited, visit it and add its edges
            // to the pending set.
            Vertex* neighborp = castVertexp(bestEdgep->top());
            if (visited_set.find(neighborp) == visited_set.end()) {
                int bestCost = bestEdgep->weight();
                UINFO(6, "bestCost = "<<bestCost
                      <<"  from "<<from_vertexp->key()
                      <<" to "<<neighborp->key()<<endl);

                // Create the edge in our output MST graph
                mstp->addEdge(from_vertexp->key(), neighborp->key(), bestCost);
                edges_made++;

                // Mark this vertex as visited
                visited_set.insert(neighborp);

                // Update the pending edges with new edges
                for (V3GraphEdge* edgep = neighborp->outBeginp();
                     edgep; edgep = edgep->outNextp()) {
                    pendingEdges.insert(edgep);
                }
            } else {
                UINFO(6, "Discarding edge to already-visited neighbor "
                      <<neighborp->key()<<endl);
            }
        }

        UASSERT(edges_made + 1 == vertCount, "Algorithm failed");
        UASSERT(visited_set.size() == vertCount, "Algorithm failed");
    }

    // Populate *outp with a minimal perfect matching of *this.
    // *outp must be initially empty.
    void perfectMatching(const std::vector<T_Key>& oddKeys,
                         TspGraphTmpl* outp) {
        UASSERT(outp->empty(), "Output graph must start empty");

        std::list<Vertex*> odds = keysToVertexList(oddKeys);
        vl_unordered_set<Vertex*> unmatchedOdds;
        typedef typename std::list<Vertex*>::iterator VertexListIt;
        for (VertexListIt it = odds.begin(); it != odds.end(); ++it) {
            outp->addVertex((*it)->key());
            unmatchedOdds.insert(*it);
        }

        UASSERT(odds.size() % 2 == 0, "number of odd-order nodes should be even");

        // TODO: The true Chrisofides algorithm calls for minimum-weight
        // perfect matching. Instead, we have a simple greedy algorithm
        // which might get close to the minimum, maybe, with luck?
        //
        // TODO: Revisit this. It's possible to compute the true minimum in
        // N*N*log(N) time using variants of the Blossom algorithm.
        // Implementing Blossom looks hard, maybe we can use an existing
        // open source implementation -- for example the "LEMON" library
        // which has a TSP solver.

        // -----

        // Reuse the comparator from Prim's routine. The logic is the same
        // here.  Note that the two V3GraphEdge's representing a single
        // bidir edge will collide in the pendingEdges set here, but this
        // is OK, we'll ignore the direction on the edge anyway.
        EdgeCmp cmp;
        typedef std::set<V3GraphEdge*, EdgeCmp&> PendingEdgeSet;
        PendingEdgeSet pendingEdges(cmp);

        for (VertexListIt it = odds.begin(); it != odds.end(); ++it) {
            for (V3GraphEdge* edgep = (*it)->outBeginp();
                 edgep; edgep = edgep->outNextp()) {
                pendingEdges.insert(edgep);
            }
        }

        // Iterate over all edges, in order from low to high cost.
        // For any edge whose ends are both odd-order vertices which
        // haven't been matched yet, match them.
        for (typename PendingEdgeSet::iterator it = pendingEdges.begin();
             it != pendingEdges.end(); ++it) {
            Vertex* fromp = castVertexp((*it)->fromp());
            Vertex* top = castVertexp((*it)->top());
            if ((unmatchedOdds.find(fromp) != unmatchedOdds.end())
                && (unmatchedOdds.find(top) != unmatchedOdds.end())) {
                outp->addEdge(fromp->key(), top->key(), (*it)->weight());
                unmatchedOdds.erase(fromp);
                unmatchedOdds.erase(top);
            }
        }
        UASSERT(unmatchedOdds.empty(), "Algorithm should have processed all vertices");
    }

    void combineGraph(const TspGraphTmpl& g) {
        vl_unordered_set<vluint32_t> edges_done;
        for (V3GraphVertex* vxp = g.verticesBeginp(); vxp; vxp = vxp->verticesNextp()) {
            Vertex* fromp = castVertexp(vxp);
            for (V3GraphEdge* edgep = fromp->outBeginp(); edgep; edgep = edgep->outNextp()) {
                Vertex* top = castVertexp(edgep->top());
                if (edges_done.find(edgep->user()) == edges_done.end()) {
                    addEdge(fromp->key(), top->key(), edgep->weight());
                    edges_done.insert(edgep->user());
                }
            }
        }
    }

    void findEulerTourRecurse(vl_unordered_set<unsigned>* markedEdgesp,
                              Vertex* startp,
                              std::vector<T_Key>* sortedOutp) {
        Vertex* cur_vertexp = startp;

        // Go on a random tour. Fun!
        std::vector<Vertex*> tour;
        do {
            UINFO(6, "Adding "<<cur_vertexp->key()<<" to tour.\n");
            tour.push_back(cur_vertexp);

            // Look for an arbitrary edge we've not yet marked
            for (V3GraphEdge* edgep = cur_vertexp->outBeginp();
                 edgep; edgep = edgep->outNextp()) {
                vluint32_t edgeId = edgep->user();
                if (markedEdgesp->end() == markedEdgesp->find(edgeId)) {
                    // This edge is not yet marked, so follow it.
                    markedEdgesp->insert(edgeId);
                    Vertex* neighborp = castVertexp(edgep->top());
                    UINFO(6, "following edge "<<edgeId
                          <<" from "<<cur_vertexp->key()
                          <<" to "<<neighborp->key()<<endl);
                    cur_vertexp = neighborp;
                    goto found;
                }
            }
            v3fatalSrc("No unmarked edges found in tour");
          found:
            ;
        } while (cur_vertexp != startp);
        UINFO(6, "stopped, got back to start of tour @ "<<cur_vertexp->key()<<endl);

        // Look for nodes on the tour that still have
        // un-marked edges. If we find one, recurse.
        for (typename std::vector<Vertex*>::iterator it = tour.begin();
             it != tour.end(); ++it) {
            Vertex* vxp = *it;
            bool recursed;
            do {
                recursed = false;
                // Look for an arbitrary edge at vxp we've not yet marked
                for (V3GraphEdge* edgep = vxp->outBeginp();
                     edgep; edgep = edgep->outNextp()) {
                    vluint32_t edgeId = edgep->user();
                    if (markedEdgesp->end() == markedEdgesp->find(edgeId)) {
                        UINFO(6, "Recursing.\n");
                        findEulerTourRecurse(markedEdgesp, vxp, sortedOutp);
                        recursed = true;
                        goto recursed;
                    }
                }
              recursed:
                ;
            } while (recursed);
            sortedOutp->push_back(vxp->key());
        }

        UINFO(6, "Tour was: ");
        for (typename std::vector<Vertex*>::iterator it = tour.begin();
             it != tour.end(); ++it) {
            Vertex* vxp = *it;
            UINFONL(6, " "<<vxp->key());
        }
        UINFONL(6, "\n");
    }

    void dumpGraph(std::ostream& os, const string& nameComment) const {
        // UINFO(0) as controlled by caller
        os<<"At "<<nameComment<<", dumping graph. Keys:\n";
        for (V3GraphVertex* vxp = verticesBeginp(); vxp; vxp = vxp->verticesNextp()) {
            Vertex* tspvp = castVertexp(vxp);
            os<<" "<<tspvp->key()<<endl;
            for (V3GraphEdge* edgep = tspvp->outBeginp(); edgep; edgep = edgep->outNextp()) {
                Vertex* neighborp = castVertexp(edgep->top());
                os<<"   has edge "<<edgep->user()<<" to "<<neighborp->key()<<endl;
            }
        }
    }
    void dumpGraphFilePrefixed(const string& nameComment) const {
        if (v3Global.opt.dumpTree()) {
            string filename = v3Global.debugFilename(nameComment)+".txt";
            const vl_unique_ptr<std::ofstream> logp(V3File::new_ofstream(filename));
            if (logp->fail()) v3fatal("Can't write "<<filename);
            dumpGraph(*logp, nameComment);
        }
    }

    void findEulerTour(std::vector<T_Key>* sortedOutp) {
        UASSERT(sortedOutp->empty(), "Output graph must start empty");
        if (debug() >= 6) dumpDotFilePrefixed("findEulerTour");
        vl_unordered_set<unsigned /*edgeID*/> markedEdges;
        // Pick a start node
        Vertex* start_vertexp = castVertexp(verticesBeginp());
        findEulerTourRecurse(&markedEdges, start_vertexp, sortedOutp);
    }

    std::vector<T_Key> getOddDegreeKeys() const {
        std::vector<T_Key> result;
        for (V3GraphVertex* vxp = verticesBeginp(); vxp; vxp = vxp->verticesNextp()) {
            Vertex* tspvp = castVertexp(vxp);
            vluint32_t degree = 0;
            for (V3GraphEdge* edgep = vxp->outBeginp(); edgep; edgep = edgep->outNextp()) {
                degree++;
            }
            if (degree & 1) {
                result.push_back(tspvp->key());
            }
        }
        return result;
    }

private:
    Vertex* findVertex(const T_Key& key) const {
        typename VMap::const_iterator it = m_vertices.find(key);
        UASSERT(it != m_vertices.end(), "Vertex not found");
        return it->second;
    }
    VL_UNCOPYABLE(TspGraphTmpl);
};

//######################################################################
// Main algorithm

void V3TSP::tspSort(const V3TSP::StateVec& states, V3TSP::StateVec* resultp) {
    UASSERT(resultp->empty(), "Output graph must start empty");

    // Make this TSP implementation work for graphs of size 0 or 1
    // which, unfortunately, is a special case as the following
    // code assumes >= 2 nodes.
    if (states.empty()) {
        return;
    }
    if (states.size() == 1) {
        resultp->push_back(*(states.begin()));
        return;
    }

    // Build the initial graph from the starting state set.
    typedef TspGraphTmpl<const TspStateBase*> Graph;
    Graph graph;
    for (V3TSP::StateVec::const_iterator it = states.begin(); it != states.end(); ++it) {
        graph.addVertex(*it);
    }
    for (V3TSP::StateVec::const_iterator it = states.begin(); it != states.end(); ++it) {
        for (V3TSP::StateVec::const_iterator jt = it; jt != states.end(); ++jt) {
            if (it == jt) continue;
            graph.addEdge(*it, *jt, (*it)->cost(*jt));
        }
    }

    // Create the minimum spanning tree
    Graph minGraph;
    graph.makeMinSpanningTree(&minGraph);
    if (debug() >= 6) minGraph.dumpGraphFilePrefixed("minGraph");

    std::vector<const TspStateBase*> oddDegree = minGraph.getOddDegreeKeys();
    Graph matching;
    graph.perfectMatching(oddDegree, &matching);
    if (debug() >= 6) matching.dumpGraphFilePrefixed("matching");

    // Adds edges to minGraph, the resulting graph will have even number of
    // edge counts at every vertex:
    minGraph.combineGraph(matching);

    V3TSP::StateVec prelim_result;
    minGraph.findEulerTour(&prelim_result);

    UASSERT(prelim_result.size() >= states.size(), "Algorithm size error");

    // Discard duplicate nodes that the Euler tour might contain.
    {
        vl_unordered_set<const TspStateBase*> seen;
        for (V3TSP::StateVec::iterator it = prelim_result.begin();
             it != prelim_result.end(); ++it) {
            const TspStateBase* elemp = *it;
            if (seen.find(elemp) == seen.end()) {
                seen.insert(elemp);
                resultp->push_back(elemp);
            }
        }
    }

    UASSERT(resultp->size() == states.size(), "Algorithm size error");

    // Find the most expensive arc and rotate the list so that the most
    // expensive arc connects the last and first elements. (Since we're not
    // modeling something that actually cycles back, we don't need to pay
    // that cost at all.)
    {
        unsigned max_cost = 0;
        unsigned max_cost_idx = 0;
        for (unsigned i = 0; i < resultp->size(); ++i) {
            const TspStateBase* ap = (*resultp)[i];
            const TspStateBase* bp
                = (i+1 == resultp->size()) ? (*resultp)[0] : (*resultp)[i+1];
            unsigned cost = ap->cost(bp);
            if (cost > max_cost) {
                max_cost = cost;
                max_cost_idx = i;
            }
        }

        if (max_cost_idx == resultp->size() - 1) {
            // List is already rotated for minimum cost. stop.
            return;
        }

        V3TSP::StateVec new_result;
        unsigned i = max_cost_idx + 1;
        UASSERT(i < resultp->size(), "Algorithm size error");
        while(i != max_cost_idx) {
            new_result.push_back((*resultp)[i]);
            i++;
            if (i >= resultp->size()) {
                i = 0;
            }
        }
        new_result.push_back((*resultp)[i]);

        UASSERT(resultp->size() == new_result.size(), "Algorithm size error");
        *resultp = new_result;
    }
}

//######################################################################
// Self Tests

class TspTestState : public V3TSP::TspStateBase {
public:
    TspTestState(unsigned xpos, unsigned ypos) :
        m_xpos(xpos),
        m_ypos(ypos),
        m_serial(++m_serialNext) {}
    ~TspTestState() {}
    virtual int cost(const TspStateBase* otherp) const {
        return cost(dynamic_cast<const TspTestState*>(otherp));
    }
    static unsigned diff(unsigned a, unsigned b) {
        if (a>b) return a-b;
        return b-a;
    }
    virtual int cost(const TspTestState* otherp) const {
        // For test purposes, each TspTestState is merely a point
        // on the Cartesian plane; cost is the linear distance
        // between two points.
        unsigned xabs, yabs;
        xabs = diff(otherp->m_xpos, m_xpos);
        yabs = diff(otherp->m_ypos, m_ypos);
        return lround(sqrt(xabs*xabs + yabs*yabs));
    }
    unsigned xpos() const {
        return m_xpos;
    }
    unsigned ypos() const {
        return m_ypos;
    }

    bool operator< (const TspStateBase& other) const {
        return operator< (dynamic_cast<const TspTestState&>(other));
    }
    bool operator< (const TspTestState& other) const {
        return m_serial < other.m_serial;
    }
private:
    unsigned m_xpos;
    unsigned m_ypos;
    unsigned m_serial;
    static unsigned m_serialNext;
};

unsigned TspTestState::m_serialNext = 0;

void V3TSP::selfTestStates() {
    // Linear test -- coords all along the x-axis
    {
        V3TSP::StateVec states;
        TspTestState s10(10,0);
        TspTestState s60(60,0);
        TspTestState s20(20,0);
        TspTestState s100(100,0);
        TspTestState s5(5,0);
        states.push_back(&s10);
        states.push_back(&s60);
        states.push_back(&s20);
        states.push_back(&s100);
        states.push_back(&s5);

        V3TSP::StateVec result;
        tspSort(states, &result);

        V3TSP::StateVec expect;
        expect.push_back(&s100);
        expect.push_back(&s60);
        expect.push_back(&s20);
        expect.push_back(&s10);
        expect.push_back(&s5);
        if (VL_UNCOVERABLE(expect != result)) {
            for (V3TSP::StateVec::iterator it = result.begin();
                 it != result.end(); ++it) {
                const TspTestState* statep = dynamic_cast<const TspTestState*>(*it);
                cout<<statep->xpos()<<" ";
            }
            cout<<endl;
            v3fatalSrc("TSP linear self-test fail. Result (above) did not match expectation.");
        }
    }

    // Second test. Coords are distributed in 2D space.
    // Test that tspSort() will rotate the list for minimum cost.
    {
        V3TSP::StateVec states;
        TspTestState a(0,0);
        TspTestState b(100,0);
        TspTestState c(200,0);
        TspTestState d(200,100);
        TspTestState e(150,150);
        TspTestState f(0,150);
        TspTestState g(0,100);

        states.push_back(&a);
        states.push_back(&b);
        states.push_back(&c);
        states.push_back(&d);
        states.push_back(&e);
        states.push_back(&f);
        states.push_back(&g);

        V3TSP::StateVec result;
        tspSort(states, &result);

        V3TSP::StateVec expect;
        expect.push_back(&f);
        expect.push_back(&g);
        expect.push_back(&a);
        expect.push_back(&b);
        expect.push_back(&c);
        expect.push_back(&d);
        expect.push_back(&e);

        if (VL_UNCOVERABLE(expect != result)) {
            for (V3TSP::StateVec::iterator it = result.begin();
                 it != result.end(); ++it) {
                const TspTestState* statep = dynamic_cast<const TspTestState*>(*it);
                cout<<statep->xpos()<<","<<statep->ypos()<<" ";
            }
            cout<<endl;
            v3fatalSrc("TSP 2d cycle=false self-test fail. Result (above) did not match expectation.");
        }
    }
}

void V3TSP::selfTestString() {
    typedef TspGraphTmpl<string> Graph;
    Graph graph;
    graph.addVertex("0");
    graph.addVertex("1");
    graph.addVertex("2");
    graph.addVertex("3");

    graph.addEdge("0", "1", 3943);
    graph.addEdge("0", "2", 3456);
    graph.addEdge("0", "3", 4920);
    graph.addEdge("1", "2", 2730);
    graph.addEdge("1", "3", 8199);
    graph.addEdge("2", "3", 4130);

    Graph minGraph;
    graph.makeMinSpanningTree(&minGraph);
    if (debug() >= 6) minGraph.dumpGraphFilePrefixed("minGraph");

    std::vector<string> oddDegree = minGraph.getOddDegreeKeys();
    Graph matching;
    graph.perfectMatching(oddDegree, &matching);
    if (debug() >= 6) matching.dumpGraphFilePrefixed("matching");

    minGraph.combineGraph(matching);

    std::vector<string> result;
    minGraph.findEulerTour(&result);

    std::vector<string> expect;
    expect.push_back("0");
    expect.push_back("2");
    expect.push_back("1");
    expect.push_back("2");
    expect.push_back("3");

    if (VL_UNCOVERABLE(expect != result)) {
        for (std::vector<string>::const_iterator it = result.begin(); it != result.end(); ++it) {
            cout<<*it<<" ";
        }
        cout<<endl;
        v3fatalSrc("TSP string self-test fail. Result (above) did not match expectation.");
    }
}

void V3TSP::selfTest() {
    selfTestString();
    selfTestStates();
}
