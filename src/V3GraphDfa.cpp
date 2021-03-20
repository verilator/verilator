// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Graph optimizations
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2005-2021 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#include "config_build.h"
#include "verilatedos.h"

#include "V3Global.h"
#include "V3GraphDfa.h"
#include "V3GraphAlg.h"

#include <map>
#include <set>
#include <stack>

//######################################################################
//######################################################################
// Algorithms - find starting node

DfaVertex* DfaGraph::findStart() {
    DfaVertex* startp = nullptr;
    for (V3GraphVertex* vertexp = this->verticesBeginp(); vertexp;
         vertexp = vertexp->verticesNextp()) {
        if (DfaVertex* vvertexp = dynamic_cast<DfaVertex*>(vertexp)) {
            if (vvertexp->start()) {
                UASSERT_OBJ(!startp, vertexp, "Multiple start points in NFA graph");
                startp = vvertexp;
            }
        } else {
            vertexp->v3fatalSrc("Non DfaVertex in DfaGraph");
        }
    }
    if (!startp) v3fatalSrc("No start point in NFA graph");
    return startp;
}

//######################################################################
//######################################################################
// Algorithms - convert NFA to a DFA
// Uses the Subset Construction Algorithm

class GraphNfaToDfa final : GraphAlg<> {
    // We have two types of nodes in one graph, NFA and DFA nodes.
    // Edges from NFA to NFA come from the user, and indicate input or epsilon transitions
    // Edges from DFA to NFA indicate the NFA from which that DFA was formed.
    // Edges from DFA to DFA indicate a completed input transition
private:
    // TYPES
    using DfaStates = std::deque<DfaVertex*>;
    using HashMap = std::multimap<vluint64_t, DfaVertex*>;

    // MEMBERS
    uint32_t m_step;  // Processing step, so we can avoid clearUser all the time
    HashMap m_hashMap;  // Dfa Vertex for each set of NFA vertexes

#ifdef VL_CPPCHECK
    static int debug() { return 9; }
#else
    static int debug() { return 0; }
#endif

    // METHODS
    DfaGraph* graphp() { return static_cast<DfaGraph*>(m_graphp); }
    static bool nfaState(V3GraphVertex* vertexp) { return vertexp->color() == 0; }
    // static bool dfaState(V3GraphVertex* vertexp) { return vertexp->color()==1; }

    void nextStep() { m_step++; }

    bool unseenNfaThisStep(V3GraphVertex* vertexp) {
        // A nfa node not already seen this processing step
        return (nfaState(vertexp) && !(vertexp->user() == m_step));
    }

    DfaVertex* newDfaVertex(DfaVertex* nfaTemplatep = nullptr) {
        DfaVertex* vertexp = new DfaVertex(graphp());
        vertexp->color(1);  // Mark as dfa
        if (nfaTemplatep && nfaTemplatep->start()) vertexp->start(true);
        if (nfaTemplatep && nfaTemplatep->accepting()) vertexp->accepting(true);
        UINFO(9, "        New " << vertexp << endl);
        return vertexp;
    }

    // Hashing
    static uint32_t hashVertex(V3GraphVertex* vertexp) {
        union {
            void* up;
            struct {
                uint32_t upper;
                uint32_t lower;
            } l;
        } u;
        u.l.upper = 0;
        u.l.lower = 0;
        u.up = vertexp;
        return u.l.upper ^ u.l.lower;
    }

    uint32_t hashDfaOrigins(DfaVertex* dfaStatep) {
        // Find the NFA states this dfa came from,
        // Record a checksum, so we can search for it later by the list of nfa nodes.
        // The order of the nodes is not deterministic; the hash thus must
        // not depend on order of edges
        uint32_t hash = 0;
        // Foreach NFA state (this DFA state was formed from)
        if (debug()) nextStep();
        for (V3GraphEdge* dfaEdgep = dfaStatep->outBeginp(); dfaEdgep;
             dfaEdgep = dfaEdgep->outNextp()) {
            if (nfaState(dfaEdgep->top())) {
                DfaVertex* nfaStatep = static_cast<DfaVertex*>(dfaEdgep->top());
                hash ^= hashVertex(nfaStatep);
                if (debug()) {
                    UASSERT_OBJ(nfaStatep->user() != m_step, nfaStatep,
                                "DFA state points to duplicate NFA state.");
                    nfaStatep->user(m_step);
                }
            }
        }
        return hash;
    }

    uint32_t hashDfaOrigins(const DfaStates& nfasWithInput) {
        // Find the NFA states this dfa came from,
        uint32_t hash = 0;
        for (DfaVertex* nfaStatep : nfasWithInput) hash ^= hashVertex(nfaStatep);
        return hash;
    }

    bool compareDfaOrigins(const DfaStates& nfasWithInput, DfaVertex* dfa2p) {
        // Return true if the NFA nodes both DFAs came from are the same list
        // Assume there are no duplicates in either input list or NFAs under dfa2
        nextStep();
        // Mark all input vertexes
        int num1s = 0;
        for (DfaVertex* nfaStatep : nfasWithInput) {
            nfaStatep->user(m_step);
            num1s++;
        }
        if (!num1s) v3fatalSrc("DFA node construction that contains no NFA states");

        // Check comparison; must all be marked
        // (Check all in dfa2p were in dfa1p)
        int num2s = 0;
        for (V3GraphEdge* dfaEdgep = dfa2p->outBeginp(); dfaEdgep;
             dfaEdgep = dfaEdgep->outNextp()) {
            if (nfaState(dfaEdgep->top())) {
                if (dfaEdgep->top()->user() != m_step) return false;
                num2s++;
            }
        }
        // If we saw all of the nodes, then they have the same number of hits
        // (Else something in dfa1p that wasn't in dfa2p)
        return (num1s == num2s);
    }

    void insertDfaOrigins(DfaVertex* dfaStatep) {
        // Record the NFA states this dfa came from
        uint32_t hash = hashDfaOrigins(dfaStatep);
        m_hashMap.emplace(hash, dfaStatep);
    }

    DfaVertex* findDfaOrigins(const DfaStates& nfasWithInput) {
        // Find another DFA state which comes from the identical set of NFA states
        // The order of the nodes is not deterministic; the hash thus must
        // not depend on order of edges
        uint32_t hash = hashDfaOrigins(nfasWithInput);

        const auto eqrange = m_hashMap.equal_range(hash);
        for (auto it = eqrange.first; it != eqrange.second; ++it) {
            DfaVertex* testp = it->second;
            if (compareDfaOrigins(nfasWithInput, testp)) {
                UINFO(9, "              DFA match for set: " << testp << endl);
                return testp;  // Identical
            }
        }
        return nullptr;  // No match
    }

    void findNfasWithInput(DfaVertex* dfaStatep, const DfaInput& input, DfaStates& nfasWithInput) {
        // Return all NFA states, with the given input transition from
        // the nfa states a given dfa state was constructed from.
        nextStep();
        nfasWithInput.clear();  // NFAs with given input

        // Foreach NFA state (this DFA state was formed from)
        for (V3GraphEdge* dfaEdgep = dfaStatep->outBeginp(); dfaEdgep;
             dfaEdgep = dfaEdgep->outNextp()) {
            if (nfaState(dfaEdgep->top())) {
                DfaVertex* nfaStatep = static_cast<DfaVertex*>(dfaEdgep->top());
                // Foreach input transition (on this nfaStatep)
                for (V3GraphEdge* nfaEdgep = nfaStatep->outBeginp(); nfaEdgep;
                     nfaEdgep = nfaEdgep->outNextp()) {
                    DfaEdge* cNfaEdgep = static_cast<DfaEdge*>(nfaEdgep);
                    if (cNfaEdgep->input().toNodep() == input.toNodep()) {
                        DfaVertex* nextStatep = static_cast<DfaVertex*>(cNfaEdgep->top());
                        if (unseenNfaThisStep(nextStatep)) {  // Not processed?
                            nfasWithInput.push_back(nextStatep);
                            nextStatep->user(m_step);
                            UINFO(9, "      Reachable " << nextStatep << endl);
                        }
                    }
                }
            }
        }

        // Expand the nfasWithInput list to include epsilon states
        // reachable by those on nfasWithInput
        {
            DfaStates nfasTodo = nfasWithInput;
            nfasWithInput.clear();  // Now the completed list
            while (!nfasTodo.empty()) {
                DfaVertex* nfaStatep = nfasTodo.front();
                nfasTodo.pop_front();
                nfasWithInput.push_back(nfaStatep);
                // Foreach epsilon-reachable (on this nfaStatep)
                for (V3GraphEdge* nfaEdgep = nfaStatep->outBeginp(); nfaEdgep;
                     nfaEdgep = nfaEdgep->outNextp()) {
                    DfaEdge* cNfaEdgep = static_cast<DfaEdge*>(nfaEdgep);
                    if (cNfaEdgep->epsilon()) {
                        DfaVertex* nextStatep = static_cast<DfaVertex*>(cNfaEdgep->top());
                        if (unseenNfaThisStep(nextStatep)) {  // Not processed?
                            nfasTodo.push_back(nextStatep);
                            nextStatep->user(m_step);
                            UINFO(9, "      Epsilon Reachable " << nextStatep << endl);
                        }
                    }
                }
            }
        }
    }

    void main() {
        UINFO(5, "Dfa to Nfa conversion...\n");
        // Vertex::color() begin: 1 indicates vertex on DFA graph, 0=NFA graph
        m_graphp->clearColors();
        // Vertex::m_user begin: # indicates processed this m_step number
        m_graphp->userClearVertices();

        if (debug() >= 6) m_graphp->dumpDotFilePrefixed("dfa_nfa");

        // Find NFA start
        DfaVertex* nfaStartp = graphp()->findStart();

        // Create new DFA State (start state) from the NFA states
        DfaVertex* dfaStartp = newDfaVertex(nfaStartp);

        DfaStates dfaUnprocps;  // Unprocessed DFA nodes
        dfaUnprocps.push_back(dfaStartp);

        UINFO(5, "Starting state conversion...\n");
        // Form DFA starting state from epsilon closure of NFA start
        nextStep();
        DfaStates workps;
        workps.push_back(nfaStartp);

        while (!workps.empty()) {  // While work
            DfaVertex* nfaStatep = workps.back();
            workps.pop_back();
            // UINFO(9," Processing "<<nfaStatep<<endl);
            nfaStatep->user(m_step);  // Mark as processed
            // Add a edge so we can find NFAs from a given DFA.
            // The NFA will never see this edge, because we only look at TO edges.
            new DfaEdge(graphp(), dfaStartp, nfaStatep, DfaEdge::NA());
            // Find epsilon closure of this nfa node, and destinations to work list
            for (V3GraphEdge* nfaEdgep = nfaStatep->outBeginp(); nfaEdgep;
                 nfaEdgep = nfaEdgep->outNextp()) {
                DfaEdge* cNfaEdgep = static_cast<DfaEdge*>(nfaEdgep);
                DfaVertex* ecNfaStatep = static_cast<DfaVertex*>(nfaEdgep->top());
                // UINFO(9,"   Consider "<<nfaEdgep->top()<<" EP "<<cNfaEdgep->epsilon()<<endl);
                if (cNfaEdgep->epsilon() && unseenNfaThisStep(ecNfaStatep)) {  // Not processed?
                    workps.push_back(ecNfaStatep);
                }
            }
        }
        if (debug() >= 6) m_graphp->dumpDotFilePrefixed("dfa_start");
        insertDfaOrigins(dfaStartp);

        int i = 0;
        UINFO(5, "Main state conversion...\n");
        while (!dfaUnprocps.empty()) {
            DfaVertex* dfaStatep = dfaUnprocps.back();
            dfaUnprocps.pop_back();
            UINFO(9, "  On dfaState " << dfaStatep << endl);

            // From this dfaState, what corresponding nfaStates have what inputs?
            std::unordered_set<int> inputs;
            // Foreach NFA state (this DFA state was formed from)
            for (V3GraphEdge* dfaEdgep = dfaStatep->outBeginp(); dfaEdgep;
                 dfaEdgep = dfaEdgep->outNextp()) {
                if (nfaState(dfaEdgep->top())) {
                    DfaVertex* nfaStatep = static_cast<DfaVertex*>(dfaEdgep->top());
                    // Foreach input on this nfaStatep
                    for (V3GraphEdge* nfaEdgep = nfaStatep->outBeginp(); nfaEdgep;
                         nfaEdgep = nfaEdgep->outNextp()) {
                        DfaEdge* cNfaEdgep = static_cast<DfaEdge*>(nfaEdgep);
                        if (!cNfaEdgep->epsilon()) {
                            if (inputs.find(cNfaEdgep->input().toInt()) == inputs.end()) {
                                inputs.insert(cNfaEdgep->input().toInt());
                                UINFO(9, "    Input to " << dfaStatep << " is "
                                                         << (cNfaEdgep->input().toInt()) << " via "
                                                         << nfaStatep << endl);
                            }
                        }
                    }
                }
            }

            // Foreach input state (NFA inputs of this DFA state)
            for (int inIt : inputs) {
                DfaInput input = inIt;
                UINFO(9, "    ===" << ++i << "=======================\n");
                UINFO(9, "    On input " << cvtToHex(input.toNodep()) << endl);

                // Find all states reachable for given input
                DfaStates nfasWithInput;
                findNfasWithInput(dfaStatep, input, nfasWithInput /*ref*/);

                // nfasWithInput now maps to the DFA we want a transition to.
                // Does a DFA already exist with this, and only this subset of NFA's?
                DfaVertex* toDfaStatep = findDfaOrigins(nfasWithInput);
                if (!toDfaStatep) {
                    // Doesn't exist, make new dfa state corresponding to this one,
                    toDfaStatep = newDfaVertex();
                    dfaUnprocps.push_back(toDfaStatep);  // Add to process list
                    // Track what nfa's point to it.
                    for (DfaStates::const_iterator nfaIt = nfasWithInput.begin();
                         nfaIt != nfasWithInput.end(); ++nfaIt) {
                        UINFO(9, "          NewContainsNfa " << *nfaIt << endl);
                        new DfaEdge(graphp(), toDfaStatep, *nfaIt, DfaEdge::NA());
                        if ((*nfaIt)->accepting()) toDfaStatep->accepting(true);
                    }
                    insertDfaOrigins(toDfaStatep);
                }
                // Add input transition
                new DfaEdge(graphp(), dfaStatep, toDfaStatep, input);

                if (debug() >= 6) m_graphp->dumpDotFilePrefixed("step");
            }
        }

        // Remove old NFA states
        UINFO(5, "Removing NFA states...\n");
        if (debug() >= 6) m_graphp->dumpDotFilePrefixed("dfa_withnfa");
        for (V3GraphVertex *nextp, *vertexp = m_graphp->verticesBeginp(); vertexp;
             vertexp = nextp) {
            nextp = vertexp->verticesNextp();
            if (nfaState(vertexp)) VL_DO_DANGLING(vertexp->unlinkDelete(m_graphp), vertexp);
        }

        UINFO(5, "Done.\n");
        if (debug() >= 6) m_graphp->dumpDotFilePrefixed("dfa_done");
    }

public:
    GraphNfaToDfa(V3Graph* graphp, V3EdgeFuncP edgeFuncp)
        : GraphAlg<>{graphp, edgeFuncp} {
        m_step = 0;
        main();
    }
    ~GraphNfaToDfa() = default;
};

void DfaGraph::nfaToDfa() { GraphNfaToDfa(this, &V3GraphEdge::followAlwaysTrue); }

//######################################################################
//######################################################################
// Algorithms - optimize a DFA structure
//
// Scan the DFA, cleaning up trailing states.

class DfaGraphReduce final : GraphAlg<> {
private:
    // METHODS
#ifdef VL_CPPCHECK
    static int debug() { return 9; }
#else
    static int debug() { return 0; }
#endif
    DfaGraph* graphp() { return static_cast<DfaGraph*>(m_graphp); }

    bool isDead(DfaVertex* vertexp) {
        // A state is dead if not accepting, and goes nowhere
        if (vertexp->accepting() || vertexp->start()) return false;
        for (V3GraphEdge* edgep = vertexp->outBeginp(); edgep; edgep = edgep->outNextp()) {
            if (edgep->top() != vertexp) return false;
        }
        return true;
    }

    void optimize_accepting_out() {
        // Delete outbound edges from accepting states
        // (As once we've accepted, we no longer care about anything else.)
        for (V3GraphVertex* vertexp = m_graphp->verticesBeginp(); vertexp;
             vertexp = vertexp->verticesNextp()) {
            if (DfaVertex* vvertexp = dynamic_cast<DfaVertex*>(vertexp)) {
                if (vvertexp->accepting()) {
                    for (V3GraphEdge *nextp, *edgep = vertexp->outBeginp(); edgep; edgep = nextp) {
                        nextp = edgep->outNextp();
                        VL_DO_DANGLING(edgep->unlinkDelete(), edgep);
                    }
                }
            }
        }
    }

    void optimize_orphans() {
        // Remove states that don't come from start
        // Presumably the previous optimization orphaned them.

        // Vertex::m_user begin: 1 indicates on the work list, 2 processed
        // (Otherwise we might have nodes on the list twice, and reference after deleting them.)
        m_graphp->userClearVertices();

        DfaVertex* startp = graphp()->findStart();
        std::stack<V3GraphVertex*> workps;
        workps.push(startp);

        // Mark all nodes connected to start
        while (!workps.empty()) {
            V3GraphVertex* vertexp = workps.top();
            workps.pop();
            vertexp->user(2);  // Processed
            // Add nodes from here to the work list
            for (V3GraphEdge* edgep = vertexp->outBeginp(); edgep; edgep = edgep->outNextp()) {
                V3GraphVertex* tovertexp = edgep->top();
                if (!tovertexp->user()) {
                    workps.push(tovertexp);
                    tovertexp->user(1);
                }
            }
        }

        // Delete all nodes not connected
        for (V3GraphVertex *nextp, *vertexp = m_graphp->verticesBeginp(); vertexp;
             vertexp = nextp) {
            nextp = vertexp->verticesNextp();
            if (!vertexp->user()) VL_DO_DANGLING(vertexp->unlinkDelete(m_graphp), vertexp);
        }
    }

    void optimize_no_outbound() {
        // Non-accepting states with no outbound transitions may be
        // deleted.  Then, any arcs feeding those states, and perhaps those
        // states...

        // Vertex::m_user begin: 1 indicates on the work list
        // (Otherwise we might have nodes on the list twice, and reference after deleting them.)
        m_graphp->userClearVertices();

        // Find all dead vertexes
        std::stack<DfaVertex*> workps;
        for (V3GraphVertex* vertexp = m_graphp->verticesBeginp(); vertexp;
             vertexp = vertexp->verticesNextp()) {
            if (DfaVertex* vvertexp = dynamic_cast<DfaVertex*>(vertexp)) {
                workps.push(vvertexp);
                vertexp->user(1);
            } else {
                // If ever remove this, need dyn cast below
                vertexp->v3fatalSrc("Non DfaVertex in dfa graph");
            }
        }

        // While deadness... Delete and find new dead nodes.
        while (!workps.empty()) {
            DfaVertex* vertexp = workps.top();
            workps.pop();
            vertexp->user(0);
            if (isDead(vertexp)) {
                // Add nodes that go here to the work list
                for (V3GraphEdge* edgep = vertexp->inBeginp(); edgep; edgep = edgep->inNextp()) {
                    DfaVertex* fromvertexp = static_cast<DfaVertex*>(edgep->fromp());
                    if (fromvertexp != vertexp && !fromvertexp->user()) {
                        workps.push(fromvertexp);
                        fromvertexp->user(1);
                    }
                }
                // Transitions to this state removed by the unlink function
                VL_DO_DANGLING(vertexp->unlinkDelete(m_graphp), vertexp);
            }
        }
    }

public:
    DfaGraphReduce(V3Graph* graphp, V3EdgeFuncP edgeFuncp)
        : GraphAlg<>{graphp, edgeFuncp} {
        if (debug() >= 6) m_graphp->dumpDotFilePrefixed("opt_in");
        optimize_accepting_out();
        if (debug() >= 6) m_graphp->dumpDotFilePrefixed("opt_acc");
        optimize_orphans();
        if (debug() >= 6) m_graphp->dumpDotFilePrefixed("opt_orph");
        optimize_no_outbound();
        if (debug() >= 6) m_graphp->dumpDotFilePrefixed("opt_noout");
    }
    ~DfaGraphReduce() = default;
};

void DfaGraph::dfaReduce() { DfaGraphReduce(this, &V3GraphEdge::followAlwaysTrue); }

//######################################################################
//######################################################################
// Algorithms - complement a DFA
//
// The traditional algorithm is to make a rejecting state, add edges to
// reject from all missing values, then swap accept and reject.  Rather
// than swap at the end, it's faster if we swap up front, then do the edge
// changes.
//
// 1. Since we didn't log rejecting states, make a temp state (this will be
// the old accept, and new reject).
//
// 2. All vertexes except start/accept get edges to NEW accept for any
// non-existing case.  Weedely we don't have a nice way of representing
// this so we just create a edge for each case and mark it "complemented."
//
// 3. Delete temp vertex (old accept/new reject) and related edges.
// The user's old accept is now the new accept.  This is important as
// we want the virtual type of it to be intact.

class DfaGraphComplement final : GraphAlg<> {
private:
    // MEMBERS
    DfaVertex* m_tempNewerReject;

    // METHODS
    static int debug() { return 9; }
    DfaGraph* graphp() { return static_cast<DfaGraph*>(m_graphp); }

    void add_complement_edges() {
        // Find accepting vertex
        DfaVertex* acceptp = nullptr;
        for (V3GraphVertex* vertexp = m_graphp->verticesBeginp(); vertexp;
             vertexp = vertexp->verticesNextp()) {
            if (DfaVertex* vvertexp = dynamic_cast<DfaVertex*>(vertexp)) {
                if (vvertexp->accepting()) {
                    acceptp = vvertexp;
                    break;
                }
            }
        }
        if (!acceptp) v3fatalSrc("No accepting vertex in DFA");

        // Remap edges
        for (V3GraphVertex* vertexp = m_graphp->verticesBeginp(); vertexp;
             vertexp = vertexp->verticesNextp()) {
            if (DfaVertex* vvertexp = dynamic_cast<DfaVertex*>(vertexp)) {
                // UINFO(9, "   on vertex "<<vvertexp->name()<<endl);
                if (!vvertexp->accepting() && vvertexp != m_tempNewerReject) {
                    for (V3GraphEdge *nextp, *edgep = vertexp->outBeginp(); edgep; edgep = nextp) {
                        nextp = edgep->outNextp();
                        if (!edgep->user()) {  // Not processed
                            // Old edges to accept now go to new reject
                            DfaEdge* vedgep = static_cast<DfaEdge*>(edgep);
                            DfaVertex* tovertexp = static_cast<DfaVertex*>(edgep->top());
                            if (tovertexp->accepting()) {
                                new DfaEdge(graphp(), vvertexp, m_tempNewerReject, vedgep);
                                VL_DO_DANGLING(edgep->unlinkDelete(), edgep);
                            }

                            // NOT of all values goes to accept
                            // We make a edge for each value to OR, IE
                            // edge(complemented,a) edge(complemented,b) means !(a | b)
                            if (!tovertexp->accepting()) {
                                // Note we must include edges moved above to reject
                                DfaEdge* newp = new DfaEdge(graphp(), vvertexp, acceptp, vedgep);
                                newp->complement(!newp->complement());
                                newp->user(1);
                            }
                        }
                    }
                }
            }
        }
    }

public:
    DfaGraphComplement(V3Graph* dfagraphp, V3EdgeFuncP edgeFuncp)
        : GraphAlg<>{dfagraphp, edgeFuncp} {
        if (debug() >= 6) m_graphp->dumpDotFilePrefixed("comp_in");

        // Vertex::m_user begin: 1 indicates new edge, no more processing
        m_graphp->userClearEdges();

        m_tempNewerReject = new DfaVertex(graphp());
        add_complement_edges();
        if (debug() >= 6) m_graphp->dumpDotFilePrefixed("comp_preswap");

        VL_DO_CLEAR(m_tempNewerReject->unlinkDelete(graphp()), m_tempNewerReject = nullptr);
        if (debug() >= 6) m_graphp->dumpDotFilePrefixed("comp_out");
    }
    ~DfaGraphComplement() = default;
    VL_UNCOPYABLE(DfaGraphComplement);
};

void DfaGraph::dfaComplement() { DfaGraphComplement(this, &V3GraphEdge::followAlwaysTrue); }
