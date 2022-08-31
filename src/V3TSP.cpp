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
// Copyright 2003-2022 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#include "config_build.h"
#include "verilatedos.h"

#include "V3TSP.h"

#include "V3Error.h"
#include "V3File.h"
#include "V3Global.h"
#include "V3Graph.h"

#include <algorithm>
#include <cmath>
#include <list>
#include <memory>
#include <sstream>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <vector>

//######################################################################
// Support classes

namespace V3TSP {
static uint32_t edgeIdNext = 0;

static void selfTestStates();
static void selfTestString();

VL_DEBUG_FUNC;  // Declare debug()
}  // namespace V3TSP

// Vertex that tracks a per-vertex key
template <typename T_Key>
class TspVertexTmpl final : public V3GraphVertex {
private:
    const T_Key m_key;

public:
    TspVertexTmpl(V3Graph* graphp, const T_Key& k)
        : V3GraphVertex{graphp}
        , m_key{k} {}
    virtual ~TspVertexTmpl() override = default;
    const T_Key& key() const { return m_key; }

private:
    VL_UNCOPYABLE(TspVertexTmpl);
};

// TspGraphTmpl represents a complete graph, templatized to work with
// different T_Key types.
template <typename T_Key>
class TspGraphTmpl final : public V3Graph {
public:
    // TYPES
    using Vertex = TspVertexTmpl<T_Key>;

    enum VertexState : uint32_t { CLEAR = 0, MST_VISITED = 1, UNMATCHED_ODD = 2 };

    // MEMBERS
    std::unordered_map<T_Key, Vertex*> m_vertices;  // T_Key to Vertex lookup map

    // CONSTRUCTORS
    TspGraphTmpl()
        : V3Graph{} {}
    virtual ~TspGraphTmpl() override = default;

    // METHODS
    void addVertex(const T_Key& key) {
        const auto itr = m_vertices.find(key);
        UASSERT(itr == m_vertices.end(), "Vertex already exists with same key");
        Vertex* v = new Vertex(this, key);
        m_vertices[key] = v;
    }

    // For purposes of TSP, we are using non-directional graphs.
    // Map that onto the normally-directional V3Graph by creating
    // a matched pairs of opposite-directional edges to represent
    // each non-directional edge:
    void addEdge(const T_Key& from, const T_Key& to, int cost) {
#if VL_DEBUG  // Hot, so only in debug
        UASSERT(from != to, "Adding edge would form a loop");
        UASSERT(cost >= 0, "Negative weight edge");
#endif
        Vertex* const fp = findVertex(from);
        Vertex* const tp = findVertex(to);

        // No need to dedup edges.
        // The only time we may create duplicate edges is when
        // combining the MST with the perfect-matched pairs,
        // and in that case, we want to permit duplicate edges.
        const uint32_t edgeId = ++V3TSP::edgeIdNext;

        // We want to be able to compare edges quickly for a total
        // ordering, so pre-compute a sorting key and store it in
        // the edge user field. We also want easy access to the 'id'
        // which uniquely identifies a single bidir edge. Luckily we
        // can do both efficiently.
        const uint64_t userValue = (static_cast<uint64_t>(cost) << 32) | edgeId;
        (new V3GraphEdge(this, fp, tp, cost))->user(userValue);
        (new V3GraphEdge(this, tp, fp, cost))->user(userValue);
    }

    inline static uint32_t getEdgeId(const V3GraphEdge* edgep) {
        return static_cast<uint32_t>(edgep->user());
    }

    bool empty() const { return m_vertices.empty(); }

    const std::list<Vertex*> keysToVertexList(const std::vector<T_Key>& odds) {
        std::list<Vertex*> vertices;
        for (unsigned i = 0; i < odds.size(); ++i) { vertices.push_back(findVertex(odds.at(i))); }
        return vertices;
    }

private:
    // We will keep sorted lists of edges as vectors
    using EdgeList = std::vector<V3GraphEdge*>;

    inline static bool edgeCmp(const V3GraphEdge* ap, const V3GraphEdge* bp) {
        // We pre-computed these when adding the edge to sort first by cost, then by identity
        return ap->user() > bp->user();
    }

    struct EdgeListCmp final {
        bool operator()(const EdgeList* ap, const EdgeList* bp) const {
            // Compare heads
            return edgeCmp(bp->back(), ap->back());
        }
    };

    inline static Vertex* castVertexp(V3GraphVertex* vxp) { return static_cast<Vertex*>(vxp); }

public:
    // From *this, populate *mstp with the minimum spanning tree.
    // *mstp must be initially empty.
    void makeMinSpanningTree(TspGraphTmpl* mstp) {
        UASSERT(mstp->empty(), "Output graph must start empty");

        // Use Prim's algorithm to efficiently construct the MST.

        uint32_t vertCount = 0;
        for (V3GraphVertex* vxp = verticesBeginp(); vxp; vxp = vxp->verticesNextp()) {
            mstp->addVertex(castVertexp(vxp)->key());
            vertCount++;
        }

        // Allocate storage for per vertex edge lists up front.
        std::vector<EdgeList> allocatedEdgeLists{vertCount};

        // Index of vertex in visitation order (used for indexing allocatedEdgeLists)
        uint32_t vertIdx = 0;

        // We keep pending edges as a sorted set of sorted vectors. This allows us to find the
        // lowest cost edge quickly, while also reducing the cost of inserting batches of new
        // edges, which is what we need in this algorithm.
        std::set<EdgeList*, EdgeListCmp> pendingEdgeListps;

        const auto visit = [&](V3GraphVertex* vtxp) {
#ifdef VL_DEBUG  // Very hot, so only in debug
            UASSERT(vtxp->user() == VertexState::CLEAR, "Vertex visited twice");
#endif
            // Mark vertex as visited
            vtxp->user(VertexState::MST_VISITED);
            // Allocate new edge list
            EdgeList* const newEdgesp = &allocatedEdgeLists[vertIdx++];
            // Gather out edges of this vertex
            for (V3GraphEdge* edgep = vtxp->outBeginp(); edgep; edgep = edgep->outNextp()) {
                // Don't add edges leading to vertices we already visited. This is a highly
                // connected graph, so this greatly reduces the cost of maintaining the pending
                // set.
                if (edgep->top()->user() == VertexState::MST_VISITED) continue;
                newEdgesp->push_back(edgep);
            }
            // If no relevant out edges, then we are done
            if (newEdgesp->empty()) return;
            // Sort new edge list
            std::sort(newEdgesp->begin(), newEdgesp->end(), edgeCmp);
            // Add edge list to pending set
            pendingEdgeListps.insert(newEdgesp);
        };

        // To start, choose an arbitrary vertex and visit it.
        visit(verticesBeginp());

        // Repeatedly find the least costly edge in the pending set.
        // If it connects to an unvisited node, visit that node and update
        // the pending edge set. If it connects to an already visited node,
        // discard it and repeat again.
        while (!pendingEdgeListps.empty()) {
            // Grab lowest cost edge list
            auto it = pendingEdgeListps.begin();

            // Grab lowest cost edge
            EdgeList* const bestEdgeListp = *it;
            const V3GraphEdge* const bestEdgep = bestEdgeListp->back();

            // Remove the lowest cost edge list. We will remove its lowest cost element, and either
            // we are done with (if it had a single element) it in which case it will be discarded,
            // or the cost of the new head element might be different, so we will need to re-insert
            // it in the right place. In either case, it needs to be removed.
            pendingEdgeListps.erase(it);

            // If the lowest cost edge list is not a singleton list, then pop the lowest cost
            // edge and re-insert the remaining edge list into the pending set.
            if (bestEdgeListp->size() > 1) {
                bestEdgeListp->pop_back();
                pendingEdgeListps.insert(bestEdgeListp);
            }

            // Grab the target vertex
            Vertex* const neighborp = castVertexp(bestEdgep->top());

            // If the neighbour is not yet visited
            if (neighborp->user() == VertexState::CLEAR) {
                // Visit it
                visit(neighborp);

                // Create the edge in our output MST graph
                Vertex* const from_vertexp = castVertexp(bestEdgep->fromp());
                mstp->addEdge(from_vertexp->key(), neighborp->key(), bestEdgep->weight());

#if VL_DEBUG  // Very hot loop, so only in debug
                UASSERT(from_vertexp->user() == MST_VISITED,
                        "bestEdgep->fromp() should be already seen");
#endif
            }
        }

        UASSERT(vertIdx == vertCount, "Should have visited all vertices");
    }

    // Populate *outp with a minimal perfect matching of *this.
    // *outp must be initially empty.
    void perfectMatching(const std::vector<T_Key>& oddKeys, TspGraphTmpl* outp) {
        UASSERT(outp->empty(), "Output graph must start empty");

        const std::list<Vertex*>& odds = keysToVertexList(oddKeys);
        UASSERT(odds.size() % 2 == 0, "number of odd-order nodes should be even");

        for (Vertex* const vtxp : odds) {
            outp->addVertex(vtxp->key());
            vtxp->user(VertexState::UNMATCHED_ODD);
        }

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

        // Gather and sort all edges. We use a vector then sort, because this is faster than a
        // sorted set. Reuse the comparator from Prim's routine (note it a 'greater', not a
        // 'lesser' comparator). The logic is the same here.
        //
        // Note that there are two V3GraphEdge's representing a single bidir edge. While we could
        // just add both to the pending list and get the same result, we will only add one (based
        // on fast pointer comparison - this still yields deterministic results), in order to
        // reduce the size of the working set.
        std::vector<V3GraphEdge*> pendingEdges;

        for (Vertex* const fromp : odds) {
            for (V3GraphEdge* edgep = fromp->outBeginp(); edgep; edgep = edgep->outNextp()) {
                Vertex* const top = castVertexp(edgep->top());
                // There are two edges (in both directions) between these two vertices. Keep one.
                if (fromp > top) continue;
                // We only care about edges between the odd-order vertices
                if (top->user() != VertexState::UNMATCHED_ODD) continue;
                // Add to candidate list
                pendingEdges.push_back(edgep);
            }
        }

        // Sort reverse iterators. This yields ascending order with a 'greater' comparator.
        std::sort(pendingEdges.rbegin(), pendingEdges.rend(), edgeCmp);

        // Iterate over all edges, in order from low to high cost.
        // For any edge whose ends are both odd-order vertices which
        // haven't been matched yet, match them.
        for (V3GraphEdge* const edgep : pendingEdges) {
            Vertex* const fromp = castVertexp(edgep->fromp());
            Vertex* const top = castVertexp(edgep->top());
            if (fromp->user() == VertexState::UNMATCHED_ODD
                && top->user() == VertexState::UNMATCHED_ODD) {
                outp->addEdge(fromp->key(), top->key(), edgep->weight());
                fromp->user(VertexState::CLEAR);
                top->user(VertexState::CLEAR);
            }
        }
    }

    void combineGraph(const TspGraphTmpl& g) {
        std::unordered_set<uint32_t> edges_done;
        for (V3GraphVertex* vxp = g.verticesBeginp(); vxp; vxp = vxp->verticesNextp()) {
            const Vertex* const fromp = castVertexp(vxp);
            for (V3GraphEdge* edgep = fromp->outBeginp(); edgep; edgep = edgep->outNextp()) {
                const Vertex* const top = castVertexp(edgep->top());
                if (edges_done.insert(getEdgeId(edgep)).second) {
                    addEdge(fromp->key(), top->key(), edgep->weight());
                }
            }
        }
    }

    void findEulerTourRecurse(std::unordered_set<unsigned>* markedEdgesp, Vertex* startp,
                              std::vector<T_Key>* sortedOutp) {
        Vertex* cur_vertexp = startp;

        // Go on a random tour. Fun!
        std::vector<Vertex*> tour;
        do {
            UINFO(6, "Adding " << cur_vertexp->key() << " to tour.\n");
            tour.push_back(cur_vertexp);

            // Look for an arbitrary edge we've not yet marked
            for (V3GraphEdge* edgep = cur_vertexp->outBeginp(); edgep; edgep = edgep->outNextp()) {
                const uint32_t edgeId = getEdgeId(edgep);
                if (markedEdgesp->end() == markedEdgesp->find(edgeId)) {
                    // This edge is not yet marked, so follow it.
                    markedEdgesp->insert(edgeId);
                    Vertex* const neighborp = castVertexp(edgep->top());
                    UINFO(6, "following edge " << edgeId << " from " << cur_vertexp->key()
                                               << " to " << neighborp->key() << endl);
                    cur_vertexp = neighborp;
                    goto found;
                }
            }
            v3fatalSrc("No unmarked edges found in tour");
        found:;
        } while (cur_vertexp != startp);
        UINFO(6, "stopped, got back to start of tour @ " << cur_vertexp->key() << endl);

        // Look for nodes on the tour that still have
        // un-marked edges. If we find one, recurse.
        for (Vertex* vxp : tour) {
            bool recursed;
            do {
                recursed = false;
                // Look for an arbitrary edge at vxp we've not yet marked
                for (V3GraphEdge* edgep = vxp->outBeginp(); edgep; edgep = edgep->outNextp()) {
                    const uint32_t edgeId = getEdgeId(edgep);
                    if (markedEdgesp->end() == markedEdgesp->find(edgeId)) {
                        UINFO(6, "Recursing.\n");
                        findEulerTourRecurse(markedEdgesp, vxp, sortedOutp);
                        recursed = true;
                        goto recursed;
                    }
                }
            recursed:;
            } while (recursed);
            sortedOutp->push_back(vxp->key());
        }

        UINFO(6, "Tour was: ");
        for (const Vertex* vxp : tour) UINFONL(6, " " << vxp->key());
        UINFONL(6, "\n");
    }

    void dumpGraph(std::ostream& os, const string& nameComment) const {
        // UINFO(0) as controlled by caller
        os << "At " << nameComment << ", dumping graph. Keys:\n";
        for (V3GraphVertex* vxp = verticesBeginp(); vxp; vxp = vxp->verticesNextp()) {
            const Vertex* const tspvp = castVertexp(vxp);
            os << " " << tspvp->key() << '\n';
            for (V3GraphEdge* edgep = tspvp->outBeginp(); edgep; edgep = edgep->outNextp()) {
                const Vertex* const neighborp = castVertexp(edgep->top());
                os << "   has edge " << getEdgeId(edgep) << " to " << neighborp->key() << '\n';
            }
        }
    }
    void dumpGraphFilePrefixed(const string& nameComment) const {
        if (v3Global.opt.dumpTree()) {
            const string filename = v3Global.debugFilename(nameComment) + ".txt";
            const std::unique_ptr<std::ofstream> logp{V3File::new_ofstream(filename)};
            if (logp->fail()) v3fatal("Can't write " << filename);
            dumpGraph(*logp, nameComment);
        }
    }

    void findEulerTour(std::vector<T_Key>* sortedOutp) {
        UASSERT(sortedOutp->empty(), "Output graph must start empty");
        if (debug() >= 6) dumpDotFilePrefixed("findEulerTour");
        std::unordered_set<unsigned /*edgeID*/> markedEdges;
        // Pick a start node
        Vertex* const start_vertexp = castVertexp(verticesBeginp());
        findEulerTourRecurse(&markedEdges, start_vertexp, sortedOutp);
    }

    std::vector<T_Key> getOddDegreeKeys() const {
        std::vector<T_Key> result;
        for (V3GraphVertex* vxp = verticesBeginp(); vxp; vxp = vxp->verticesNextp()) {
            const Vertex* const tspvp = castVertexp(vxp);
            uint32_t degree = 0;
            for (V3GraphEdge* edgep = vxp->outBeginp(); edgep; edgep = edgep->outNextp()) {
                degree++;
            }
            if (degree & 1) result.push_back(tspvp->key());
        }
        return result;
    }

private:
    Vertex* findVertex(const T_Key& key) const {
        const auto it = m_vertices.find(key);
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
    if (states.empty()) return;
    if (states.size() == 1) {
        resultp->push_back(*(states.begin()));
        return;
    }

    // Build the initial graph from the starting state set.
    using Graph = TspGraphTmpl<const TspStateBase*>;
    Graph graph;
    for (const auto& state : states) graph.addVertex(state);
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

    const std::vector<const TspStateBase*> oddDegree = minGraph.getOddDegreeKeys();
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
        std::unordered_set<const TspStateBase*> seen;
        for (V3TSP::StateVec::iterator it = prelim_result.begin(); it != prelim_result.end();
             ++it) {
            const TspStateBase* const elemp = *it;
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
            const TspStateBase* const ap = (*resultp)[i];
            const TspStateBase* const bp
                = (i + 1 == resultp->size()) ? (*resultp)[0] : (*resultp)[i + 1];
            const unsigned cost = ap->cost(bp);
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
        while (i != max_cost_idx) {
            new_result.push_back((*resultp)[i]);
            i++;
            if (i >= resultp->size()) i = 0;
        }
        new_result.push_back((*resultp)[i]);

        UASSERT(resultp->size() == new_result.size(), "Algorithm size error");
        *resultp = new_result;
    }
}

//######################################################################
// Self Tests

class TspTestState final : public V3TSP::TspStateBase {
public:
    TspTestState(unsigned xpos, unsigned ypos)
        : m_xpos{xpos}
        , m_ypos{ypos}
        , m_serial{++s_serialNext} {}
    virtual ~TspTestState() override = default;
    virtual int cost(const TspStateBase* otherp) const override {
        return cost(dynamic_cast<const TspTestState*>(otherp));
    }
    static unsigned diff(unsigned a, unsigned b) {
        if (a > b) return a - b;
        return b - a;
    }
    virtual int cost(const TspTestState* otherp) const {
        // For test purposes, each TspTestState is merely a point
        // on the Cartesian plane; cost is the linear distance
        // between two points.
        unsigned xabs;
        unsigned yabs;
        xabs = diff(otherp->m_xpos, m_xpos);
        yabs = diff(otherp->m_ypos, m_ypos);
        return std::lround(std::sqrt(xabs * xabs + yabs * yabs));
    }
    unsigned xpos() const { return m_xpos; }
    unsigned ypos() const { return m_ypos; }

    bool operator<(const TspStateBase& other) const override {
        return operator<(dynamic_cast<const TspTestState&>(other));
    }
    bool operator<(const TspTestState& other) const { return m_serial < other.m_serial; }

private:
    const unsigned m_xpos;
    const unsigned m_ypos;
    const unsigned m_serial;
    static unsigned s_serialNext;
};

unsigned TspTestState::s_serialNext = 0;

void V3TSP::selfTestStates() {
    // Linear test -- coords all along the x-axis
    {
        V3TSP::StateVec states;
        const TspTestState s10(10, 0);
        const TspTestState s60(60, 0);
        const TspTestState s20(20, 0);
        const TspTestState s100(100, 0);
        const TspTestState s5(5, 0);
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
            for (V3TSP::StateVec::iterator it = result.begin(); it != result.end(); ++it) {
                const TspTestState* const statep = dynamic_cast<const TspTestState*>(*it);
                cout << statep->xpos() << " ";
            }
            cout << endl;
            v3fatalSrc("TSP linear self-test fail. Result (above) did not match expectation.");
        }
    }

    // Second test. Coords are distributed in 2D space.
    // Test that tspSort() will rotate the list for minimum cost.
    {
        V3TSP::StateVec states;
        const TspTestState a(0, 0);
        const TspTestState b(100, 0);
        const TspTestState c(200, 0);
        const TspTestState d(200, 100);
        const TspTestState e(150, 150);
        const TspTestState f(0, 150);
        const TspTestState g(0, 100);

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
            for (V3TSP::StateVec::iterator it = result.begin(); it != result.end(); ++it) {
                const TspTestState* const statep = dynamic_cast<const TspTestState*>(*it);
                cout << statep->xpos() << "," << statep->ypos() << " ";
            }
            cout << endl;
            v3fatalSrc(
                "TSP 2d cycle=false self-test fail. Result (above) did not match expectation.");
        }
    }
}

void V3TSP::selfTestString() {
    using Graph = TspGraphTmpl<std::string>;
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

    const std::vector<string> oddDegree = minGraph.getOddDegreeKeys();
    Graph matching;
    graph.perfectMatching(oddDegree, &matching);
    if (debug() >= 6) matching.dumpGraphFilePrefixed("matching");

    minGraph.combineGraph(matching);

    std::vector<string> result;
    minGraph.findEulerTour(&result);

    std::vector<string> expect;
    expect.emplace_back("0");
    expect.emplace_back("2");
    expect.emplace_back("1");
    expect.emplace_back("2");
    expect.emplace_back("3");

    if (VL_UNCOVERABLE(expect != result)) {
        for (const string& i : result) cout << i << " ";
        cout << endl;
        v3fatalSrc("TSP string self-test fail. Result (above) did not match expectation.");
    }
}

void V3TSP::selfTest() {
    selfTestString();
    selfTestStates();
}
