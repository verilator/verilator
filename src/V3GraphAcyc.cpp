// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Graph acyclic algorithm
//
// Code available from: http://www.veripool.org/verilator
//
//*************************************************************************
//
// Copyright 2003-2015 by Wilson Snyder.  This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
//
// Verilator is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
//*************************************************************************

#include "config_build.h"
#include "verilatedos.h"
#include <cstdio>
#include <cstdarg>
#include <unistd.h>
#include <algorithm>
#include <vector>
#include <list>

#include "V3Global.h"
#include "V3Graph.h"

//######################################################################
//######################################################################
// Algorithms - acyclic
//	Break the minimal number of backward edges to make the graph acyclic

class GraphAcycVertex : public V3GraphVertex {
    // user() is used for various sub-algorithm pieces
    V3GraphVertex*	m_origVertexp;		// Pointer to first vertex this represents
protected:
    friend class GraphAcyc;
    V3ListEnt<GraphAcycVertex*>	m_work;		// List of vertices with optimization work left
    uint32_t		m_storedRank;		// Rank held until commit to edge placement
    bool		m_onWorkList;		// True if already on list of work to do
    bool		m_deleted;		// True if deleted
public:

    GraphAcycVertex(V3Graph* graphp, V3GraphVertex* origVertexp)
	: V3GraphVertex(graphp), m_origVertexp(origVertexp)
	, m_storedRank(0), m_onWorkList(false), m_deleted(false) {
    }
    virtual ~GraphAcycVertex() {}
    V3GraphVertex* origVertexp() const { return m_origVertexp; }
    void setDelete() { m_deleted = true; }
    bool isDelete() const { return m_deleted; }
    virtual string name() const { return m_origVertexp->name(); }
    virtual string dotColor() const { return m_origVertexp->dotColor(); }
};

//--------------------------------------------------------------------

class GraphAcycEdge : public V3GraphEdge {
    // userp() is always used to point to the head original graph edge
private:
    typedef list<V3GraphEdge*>	OrigEdgeList;	// List of orig edges, see also GraphAcyc's decl
    V3GraphEdge*	origEdgep() const {
	OrigEdgeList* oEListp = ((OrigEdgeList*)userp());
	if (!oEListp) v3fatalSrc("No original edge associated with acyc edge "<<this<<endl);
	return (oEListp->front());
    }
public:
    GraphAcycEdge(V3Graph* graphp, V3GraphVertex* fromp, V3GraphVertex* top, int weight, bool cutable=false)
	: V3GraphEdge(graphp, fromp, top, weight, cutable) {
    }
    virtual ~GraphAcycEdge() {}
    // yellow=we might still cut it, else oldEdge: yellowGreen=made uncutable, red=uncutable
    virtual string dotColor() const { return (cutable()?"yellow":origEdgep()->dotColor()); }
};

//--------------------------------------------------------------------

struct GraphAcycEdgeCmp {
    inline bool operator () (const V3GraphEdge* lhsp, const V3GraphEdge* rhsp) const {
	if (lhsp->weight() > rhsp->weight()) return 1;  // LHS goes first
	if (lhsp->weight() < rhsp->weight()) return 0;  // RHS goes first
	return 0;
    }
};

//--------------------------------------------------------------------

// CLASSES
class GraphAcyc {
private:
    typedef list<V3GraphEdge*>	OrigEdgeList;	// List of orig edges, see also GraphAcycEdge's decl
    // GRAPH USERS
    //  origGraph
    //    GraphVertex::user() 	GraphAycVerted*	New graph node
    //  m_breakGraph
    //    GraphEdge::user()  	OrigEdgeList*	Old graph edges
    //	  GraphVertex::user	bool		Detection of loops in simplifyDupIterate
    // MEMBERS
    V3Graph*		m_origGraphp;		// Original graph
    V3Graph		m_breakGraph;		// Graph with only breakable edges represented
    V3List<GraphAcycVertex*>	m_work;		// List of vertices with optimization work left
    vector<OrigEdgeList*>	m_origEdgeDelp;	// List of deletions to do when done
    V3EdgeFuncP		m_origEdgeFuncp;	// Function that says we follow this edge (in original graph)
    uint32_t		m_placeStep;		// Number that user() must be equal to to indicate processing

    static int debug() { return V3Graph::debug(); }

    // METHODS
    void buildGraph (V3Graph* origGraphp);
    void buildGraphIterate (V3GraphVertex* overtexp, GraphAcycVertex* avertexp);
    void simplify (bool allowCut);
    void simplifyNone (GraphAcycVertex* vertexp);
    void simplifyOne (GraphAcycVertex* vertexp);
    void simplifyOut (GraphAcycVertex* vertexp);
    void simplifyDup (GraphAcycVertex* vertexp);
    void cutBasic (GraphAcycVertex* vertexp);
    void cutBackward (GraphAcycVertex* vertexp);
    void deleteMarked();
    void place();
    void placeTryEdge(V3GraphEdge* edgep);
    bool placeIterate(GraphAcycVertex* vertexp, uint32_t currentRank);

    inline bool origFollowEdge(V3GraphEdge* edgep) {
	return (edgep->weight() && (m_origEdgeFuncp)(edgep));
    }
    V3GraphEdge* edgeFromEdge (V3GraphEdge* oldedgep, V3GraphVertex* fromp, V3GraphVertex* top) {
	// Make new breakGraph edge, with old edge as a template
	GraphAcycEdge* newEdgep = new GraphAcycEdge (&m_breakGraph, fromp, top,
						     oldedgep->weight(), oldedgep->cutable());
	newEdgep->userp(oldedgep->userp());	// Keep pointer to OrigEdgeList
	return newEdgep;
    }
    void addOrigEdgep (V3GraphEdge* toEdgep, V3GraphEdge* addEdgep) {
	// Add addEdge (or it's list) to list of edges that break edge represents
	// Note addEdge may already have a bunch of similar linked edge representations.  Yuk.
	UASSERT(addEdgep, "Adding NULL");
	if (!toEdgep->userp()) {
	    OrigEdgeList* oep = new OrigEdgeList;
	    m_origEdgeDelp.push_back(oep);
	    toEdgep->userp(oep);
	}
	OrigEdgeList* oEListp = (OrigEdgeList*)(toEdgep->userp());
	if (OrigEdgeList* addListp = (OrigEdgeList*)(addEdgep->userp())) {
	    for (OrigEdgeList::iterator it = addListp->begin(); it != addListp->end(); ++it) {
		oEListp->push_back(*it);
	    }
	    addListp->clear();  // Done with it
	} else {
	    oEListp->push_back(addEdgep);
	}
    }
    void cutOrigEdge (V3GraphEdge* breakEdgep, const char* why) {
	// From the break edge, cut edges in original graph it represents
	UINFO(8,why<<" CUT "<<breakEdgep->fromp()<<endl);
	breakEdgep->cut();
	OrigEdgeList* oEListp = (OrigEdgeList*)(breakEdgep->userp());
	if (!oEListp) v3fatalSrc("No original edge associated with cutting edge "<<breakEdgep<<endl);
	// The breakGraph edge may represent multiple real edges; cut them all
	for (OrigEdgeList::iterator it = oEListp->begin(); it != oEListp->end(); ++it) {
	    V3GraphEdge* origEdgep = *it;
	    origEdgep->cut();
	    UINFO(8,"  "<<why<<"   "<<origEdgep->fromp()<<" ->"<<origEdgep->top()<<endl);
	}
    }
    // Work Que
    void workPush(V3GraphVertex* vertexp) {
	GraphAcycVertex* avertexp = (GraphAcycVertex*)vertexp;
	// Add vertex to list of nodes needing further optimization trials
	if (!avertexp->m_onWorkList) {
	    avertexp->m_onWorkList = true;
	    avertexp->m_work.pushBack(m_work, avertexp);
	}
    }
    GraphAcycVertex* workBeginp() { return m_work.begin(); }
    void workPop() {
	GraphAcycVertex* avertexp = workBeginp();
	avertexp->m_onWorkList = false;
	avertexp->m_work.unlink(m_work, avertexp); }
public:
    // CONSTRUCTORS
    GraphAcyc(V3Graph* origGraphp, V3EdgeFuncP edgeFuncp) {
	m_origGraphp = origGraphp;
	m_origEdgeFuncp = edgeFuncp;
	m_placeStep = 0;
    }
    ~GraphAcyc() {
	for (vector<OrigEdgeList*>::iterator it = m_origEdgeDelp.begin(); it != m_origEdgeDelp.end(); ++it) {
	    delete (*it);
	}
	m_origEdgeDelp.clear();
    }
    void main();
};

//--------------------------------------------------------------------

void GraphAcyc::buildGraph (V3Graph* origGraphp) {
    // Presumes the graph has been strongly ordered,
    // and thus there's a unique color if there are loops in this subgraph.

    // For each old node, make a new graph node for optimization
    origGraphp->userClearVertices();
    origGraphp->userClearEdges();
    for (V3GraphVertex* overtexp = origGraphp->verticesBeginp(); overtexp; overtexp=overtexp->verticesNextp()) {
	if (overtexp->color()) {
	    GraphAcycVertex* avertexp = new GraphAcycVertex(&m_breakGraph, overtexp);
	    overtexp->userp(avertexp);  // Stash so can look up later
	}
    }

    // Build edges between logic vertices
    for (V3GraphVertex* overtexp = origGraphp->verticesBeginp(); overtexp; overtexp=overtexp->verticesNextp()) {
	if (overtexp->color()) {
	    GraphAcycVertex* avertexp = (GraphAcycVertex*)(overtexp->userp());
	    buildGraphIterate(overtexp, avertexp);
	}
    }
}

void GraphAcyc::buildGraphIterate (V3GraphVertex* overtexp, GraphAcycVertex* avertexp) {
    // Make new edges
    for (V3GraphEdge* edgep = overtexp->outBeginp(); edgep; edgep=edgep->outNextp()) {
	if (origFollowEdge(edgep)) { // not cut
	    V3GraphVertex* toVertexp = edgep->top();
	    if (toVertexp->color()) {
		GraphAcycVertex* toAVertexp = (GraphAcycVertex*)(toVertexp->userp());
		// Replicate the old edge into the new graph
		// There may be multiple edges between same pairs of vertices
		V3GraphEdge* breakEdgep = new GraphAcycEdge
		    (&m_breakGraph, avertexp, toAVertexp, edgep->weight(), edgep->cutable());
		addOrigEdgep (breakEdgep, edgep);  // So can find original edge
	    }
	}
    }
}

void GraphAcyc::simplify (bool allowCut) {
    // Add all nodes to list of work to do
    for (V3GraphVertex* vertexp = m_breakGraph.verticesBeginp(); vertexp; vertexp=vertexp->verticesNextp()) {
	workPush(vertexp);
    }
    // Optimize till everything finished
    while (GraphAcycVertex* vertexp = workBeginp()) {
	workPop();
	simplifyNone(vertexp);
	simplifyOne(vertexp);
	simplifyOut(vertexp);
	simplifyDup(vertexp);
	if (allowCut) {
	    // The main algorithm works without these, though slower
	    // So if changing the main algorithm, comment these out for a test run
	    if (v3Global.opt.oAcycSimp()) {
		cutBasic(vertexp);
		cutBackward(vertexp);
	    }
	}
    }
    deleteMarked();
}

void GraphAcyc::deleteMarked () {
    // Delete nodes marked for removal
    for (V3GraphVertex* nextp, *vertexp = m_breakGraph.verticesBeginp(); vertexp; vertexp=nextp) {
	nextp = vertexp->verticesNextp();
	GraphAcycVertex* avertexp = (GraphAcycVertex*)vertexp;
	if (avertexp->isDelete()) {
	    avertexp->unlinkDelete(&m_breakGraph); avertexp=NULL;
	}
    }
}

void GraphAcyc::simplifyNone (GraphAcycVertex* avertexp) {
    // Don't need any vertices with no inputs, There's no way they can have a loop.
    // Likewise, vertices with no outputs
    if (avertexp->isDelete()) return;
    if (avertexp->inEmpty() || avertexp->outEmpty()) {
	UINFO(9,"  SimplifyNoneRemove "<<avertexp<<endl);
	avertexp->setDelete();	// Mark so we won't delete it twice
	// Remove edges
	while (V3GraphEdge* edgep = avertexp->outBeginp()) {
	    V3GraphVertex* otherVertexp = edgep->top();
	    //UINFO(9,"  out "<<otherVertexp<<endl);
	    edgep->unlinkDelete(); edgep = NULL;
	    workPush(otherVertexp);
	}
	while (V3GraphEdge* edgep = avertexp->inBeginp()) {
	    V3GraphVertex* otherVertexp = edgep->fromp();
	    //UINFO(9,"  in  "<<otherVertexp<<endl);
	    edgep->unlinkDelete(); edgep = NULL;
	    workPush(otherVertexp);
	}
    }
}

void GraphAcyc::simplifyOne (GraphAcycVertex* avertexp) {
    // If a node has one input and one output, we can remove it and change the edges
    if (avertexp->isDelete()) return;
    if (avertexp->inSize1() && avertexp->outSize1()) {
	V3GraphEdge* inEdgep = avertexp->inBeginp();
	V3GraphEdge* outEdgep = avertexp->outBeginp();
	V3GraphVertex* inVertexp = inEdgep->fromp();
	V3GraphVertex* outVertexp = outEdgep->top();
	// The in and out may be the same node; we'll make a loop
	// The in OR out may be THIS node; we can't delete it then.
	if (inVertexp!=avertexp && outVertexp!=avertexp) {
	    UINFO(9,"  SimplifyOneRemove "<<avertexp<<endl);
	    avertexp->setDelete();	// Mark so we won't delete it twice
	    // Make a new edge connecting the two vertices directly
	    // If both are breakable, we pick the one with less weight, else it's arbitrary
	    // We can forget about the origEdge list for the "non-selected" set of edges,
	    // as we need to break only one set or the other set of edges, not both.
	    // (This is why we must give preference to the cutable set.)
	    V3GraphEdge* templateEdgep = ( (inEdgep->cutable()
					    && (!outEdgep->cutable()
						|| inEdgep->weight()<outEdgep->weight() ))
					   ? inEdgep : outEdgep);
	    edgeFromEdge(templateEdgep, inVertexp, outVertexp);
	    // Remove old edge
	    inEdgep->unlinkDelete(); inEdgep = NULL;
	    outEdgep->unlinkDelete(); outEdgep = NULL; templateEdgep=NULL;
	    workPush(inVertexp);
	    workPush(outVertexp);
	}
    }
}

void GraphAcyc::simplifyOut (GraphAcycVertex* avertexp) {
    // If a node has one output that's not cutable, all its inputs can be reassigned
    // to the next node in the list
    if (avertexp->isDelete()) return;
    if (avertexp->outSize1()) {
	V3GraphEdge* outEdgep = avertexp->outBeginp();
	if (!outEdgep->cutable()) {
	    V3GraphVertex* outVertexp = outEdgep->top();
	    UINFO(9,"  SimplifyOutRemove "<<avertexp<<endl);
	    avertexp->setDelete();	// Mark so we won't delete it twice
	    for (V3GraphEdge* nextp, *inEdgep = avertexp->inBeginp(); inEdgep; inEdgep=nextp) {
		nextp = inEdgep->inNextp();
		V3GraphVertex* inVertexp = inEdgep->fromp();
		if (inVertexp == avertexp) {
		    if (debug()) v3error("Non-cutable edge forms a loop, vertex="<<avertexp);
		    v3error("Circular logic when ordering code (non-cutable edge loop)");
		    m_origGraphp->reportLoops(&V3GraphEdge::followNotCutable,
					      avertexp->origVertexp()); // calls OrderGraph::loopsVertexCb
		    // Things are unlikely to end well at this point,
		    // but we'll try something to get to further errors...
		    inEdgep->cutable(true);
		    return;
		}
		// Make a new edge connecting the two vertices directly
		edgeFromEdge(inEdgep, inVertexp, outVertexp);
		// Remove old edge
		inEdgep->unlinkDelete(); inEdgep = NULL;
		workPush(inVertexp);
	    }
	    outEdgep->unlinkDelete(); outEdgep = NULL;
	    workPush(outVertexp);
	}
    }
}

void GraphAcyc::simplifyDup (GraphAcycVertex* avertexp) {
    // Remove redundant edges
    if (avertexp->isDelete()) return;
    // Clear marks
    for (V3GraphEdge* edgep = avertexp->outBeginp(); edgep; edgep=edgep->outNextp()) {
	edgep->top()->userp(NULL);
    }
    // Mark edges and detect duplications
    for (V3GraphEdge* nextp, *edgep = avertexp->outBeginp(); edgep; edgep=nextp) {
	nextp = edgep->outNextp();
	V3GraphVertex* outVertexp = edgep->top();
	V3GraphEdge* prevEdgep = (V3GraphEdge*)outVertexp->userp();
	if (prevEdgep) {
	    if (!prevEdgep->cutable()) {
		// !cutable duplicates prev !cutable: we can ignore it, redundant
		//  cutable duplicates prev !cutable: know it's not a relevant loop, ignore it
		UINFO(8,"    DelDupEdge "<<avertexp<<" -> "<<edgep->top()<<endl);
		edgep->unlinkDelete(); edgep = NULL;
	    } else if (!edgep->cutable()) {
		// !cutable duplicates prev  cutable: delete the earlier cutable
		UINFO(8,"    DelDupPrev "<<avertexp<<" -> "<<prevEdgep->top()<<endl);
		prevEdgep->unlinkDelete(); prevEdgep = NULL;
		outVertexp->userp(edgep);
	    } else {
		//  cutable duplicates prev  cutable: combine weights
		UINFO(8,"    DelDupComb "<<avertexp<<" -> "<<edgep->top()<<endl);
		prevEdgep->weight (prevEdgep->weight() + edgep->weight());
		addOrigEdgep (prevEdgep, edgep);
		edgep->unlinkDelete(); edgep = NULL;
	    }
	    workPush(outVertexp);
	    workPush(avertexp);
	} else {
	    // No previous assignment
	    outVertexp->userp(edgep);
	}
    }
}

void GraphAcyc::cutBasic (GraphAcycVertex* avertexp) {
    // Detect and cleanup any loops from node to itself
    if (avertexp->isDelete()) return;
    for (V3GraphEdge* nextp, *edgep = avertexp->outBeginp(); edgep; edgep=nextp) {
	nextp = edgep->outNextp();
	if (edgep->cutable() && edgep->top()==avertexp) {
	    cutOrigEdge (edgep, "  Cut Basic");
	    edgep->unlinkDelete(); edgep = NULL;
	    workPush(avertexp);
	}
    }
}

void GraphAcyc::cutBackward (GraphAcycVertex* avertexp) {
    // If a cutable edge is from A->B, and there's a non-cutable edge B->A, then must cut!
    if (avertexp->isDelete()) return;
    // Clear marks
    for (V3GraphEdge* edgep = avertexp->outBeginp(); edgep; edgep=edgep->outNextp()) {
	edgep->top()->user(false);
    }
    for (V3GraphEdge* edgep = avertexp->inBeginp(); edgep; edgep=edgep->inNextp()) {
	if (!edgep->cutable()) edgep->fromp()->user(true);
    }
    // Detect duplications
    for (V3GraphEdge* nextp, *edgep = avertexp->outBeginp(); edgep; edgep=nextp) {
	nextp = edgep->outNextp();
	if (edgep->cutable() && edgep->top()->user()) {
	    cutOrigEdge (edgep, "  Cut A->B->A");
	    edgep->unlinkDelete(); edgep = NULL;
	    workPush(avertexp);
	}
    }
}

void GraphAcyc::place() {
    // Input is m_breakGraph with ranks already assigned on non-breakable edges

    // Make a list of all cutable edges in the graph
    int numEdges = 0;
    for (V3GraphVertex* vertexp = m_breakGraph.verticesBeginp(); vertexp; vertexp=vertexp->verticesNextp()) {
	for (V3GraphEdge* edgep = vertexp->outBeginp(); edgep; edgep=edgep->outNextp()) {
	    if (edgep->weight() && edgep->cutable()) {
		numEdges++;
	    }
	}
    }
    UINFO(4, "    Cutable edges = "<<numEdges<<endl);

    vector<V3GraphEdge*>	edges;	// List of all edges to be processed
    edges.reserve(numEdges+1); // Make the vector properly sized right off the bat -- faster than reallocating
    for (V3GraphVertex* vertexp = m_breakGraph.verticesBeginp(); vertexp; vertexp=vertexp->verticesNextp()) {
	vertexp->user(0);	// Clear in prep of next step
	for (V3GraphEdge* edgep = vertexp->outBeginp(); edgep; edgep=edgep->outNextp()) {
	    if (edgep->weight() && edgep->cutable()) {
		edges.push_back(edgep);
	    }
	}
    }

    // Sort by weight, then by vertex (so that we completely process one vertex, when possible)
    stable_sort(edges.begin(), edges.end(), GraphAcycEdgeCmp());

    // Process each edge in weighted order
    m_placeStep = 10;
    for (vector<V3GraphEdge*>::iterator it = edges.begin(); it!=edges.end(); ++it) {
	V3GraphEdge* edgep = (*it);
	placeTryEdge(edgep);
    }
}

void GraphAcyc::placeTryEdge(V3GraphEdge* edgep) {
    // Try to make this edge uncutable
    m_placeStep++;
    UINFO(8, "    PlaceEdge s"<<m_placeStep<<" w"<<edgep->weight()<<" "<<edgep->fromp()<<endl);
    // Make the edge uncutable so we detect it in placement
    edgep->cutable(false);
    // Vertex::m_user begin: number indicates this edge was completed
    // Try to assign ranks, presuming this edge is in place
    // If we come across user()==placestep, we've detected a loop and must back out
    bool loop=placeIterate((GraphAcycVertex*)edgep->top(), edgep->fromp()->rank()+1);
    if (!loop) {
	// No loop, we can keep it as uncutable
	// Commit the new ranks we calculated
	// Just cleanup the list.  If this is slow, we can add another set of
	// user counters to avoid cleaning up the list.
	while (workBeginp()) {
	    workPop();
	}
    } else {
	// Adding this edge would cause a loop, kill it
	edgep->cutable(true);  // So graph still looks pretty
	cutOrigEdge (edgep, "  Cut loop");
	edgep->unlinkDelete(); edgep = NULL;
	// Backout the ranks we calculated
	while (GraphAcycVertex* vertexp = workBeginp()) {
	    workPop();
	    vertexp->rank(vertexp->m_storedRank);
	}
    }
}

bool GraphAcyc::placeIterate(GraphAcycVertex* vertexp, uint32_t currentRank) {
    // Assign rank to each unvisited node
    //   rank() is the "committed rank" of the graph known without loops
    // If larger rank is found, assign it and loop back through
    // If we hit a back node make a list of all loops
    if (vertexp->rank() >= currentRank) return false;  // Already processed it
    if (vertexp->user() == m_placeStep) return true;  // Loop detected
    vertexp->user(m_placeStep);
    // Remember we're changing the rank of this node; might need to back out
    if (!vertexp->m_onWorkList) {
	vertexp->m_storedRank = vertexp->rank();
	workPush(vertexp);
    }
    vertexp->rank(currentRank);
    // Follow all edges and increase their ranks
    for (V3GraphEdge* edgep = vertexp->outBeginp(); edgep; edgep=edgep->outNextp()) {
	if (edgep->weight() && !edgep->cutable()) {
	    if (placeIterate((GraphAcycVertex*)edgep->top(), currentRank+1)) {
		// We don't need to reset user(); we'll use a different placeStep for the next edge
		return true; // Loop detected
	    }
	}
    }
    vertexp->user(0);
    return false;
}

//----- Main algorithm entry point

void GraphAcyc::main () {
    m_breakGraph.userClearEdges();

    // Color based on possible loops
    m_origGraphp->stronglyConnected(m_origEdgeFuncp);

    // Make a new graph with vertices that have only a single vertex
    // for each group of old vertices that are interconnected with unbreakable
    // edges (and thus can't represent loops - if we did the unbreakable
    // marking right, anyways)
    buildGraph (m_origGraphp);
    if (debug()>=6) m_breakGraph.dumpDotFilePrefixed("acyc_pre");

    // Perform simple optimizations before any cuttings
    simplify(false);
    if (debug()>=5) m_breakGraph.dumpDotFilePrefixed("acyc_simp");

    UINFO(4, " Cutting trivial loops\n");
    simplify(true);
    if (debug()>=6) m_breakGraph.dumpDotFilePrefixed("acyc_mid");

    UINFO(4, " Ranking\n");
    m_breakGraph.rank(&V3GraphEdge::followNotCutable);
    if (debug()>=6) m_breakGraph.dumpDotFilePrefixed("acyc_rank");

    UINFO(4, " Placement\n");
    place();
    if (debug()>=6) m_breakGraph.dumpDotFilePrefixed("acyc_place");

    UINFO(4, " Final Ranking\n");
    // Only needed to assert there are no loops in completed graph
    m_breakGraph.rank(&V3GraphEdge::followAlwaysTrue);
    if (debug()>=6) m_breakGraph.dumpDotFilePrefixed("acyc_done");
}

void V3Graph::acyclic(V3EdgeFuncP edgeFuncp) {
    UINFO(4, "Acyclic\n");
    GraphAcyc acyc (this, edgeFuncp);
    acyc.main();
    UINFO(4, "Acyclic done\n");
}
