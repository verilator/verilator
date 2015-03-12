// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Break always into sensitivity active domains
//
// Code available from: http://www.veripool.org/verilator
//
//*************************************************************************
//
// Copyright 2008-2015 by Wilson Snyder.  This program is free software; you can
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
// V3ClkGater's Transformations:
//
//   Look for clock gaters
//   Note there's overlap between this process and V3Split's
//	ALWAYS: Build graph
// 	    IF: Form vertex pointing to any IFs or ALWAYS above
//	    VARREF: Form vertex pointing to IFs it is under
//	    ASSIGN: If under normal assignment, disable optimization
//          FUTURE OPTIMIZE: If signal is set to itself, consider that OK for gating.
// 	    !splitable: Mark all VARREFs in this statement as comming from it
//	Optimize graph so if signal is referenced under multiple IF branches it moves up
//	Make ALWAYS for each new gating term, and move statements there
//*************************************************************************

#include "config_build.h"
#include "verilatedos.h"
#include <cstdio>
#include <cstdarg>
#include <unistd.h>
#include <map>
#include <algorithm>
#include <vector>

#include "V3Global.h"
#include "V3Ast.h"
#include "V3Stats.h"
#include "V3Graph.h"
#include "V3ClkGater.h"

//######################################################################
// Base for debug

class GaterBaseVisitor : public AstNVisitor {
protected:
    static int debug() {
	static int level = -1;
	if (VL_UNLIKELY(level < 0)) level = v3Global.opt.debugSrcLevel(__FILE__);
	return level;
    }
};

//######################################################################
// Support classes

class GaterVarVertex;

class GaterVertex : public V3GraphVertex {
    static uint32_t s_rankNum;
public:
    GaterVertex(V3Graph* graphp)
	: V3GraphVertex(graphp) {
	s_rankNum++; rank(s_rankNum);
    }
    virtual ~GaterVertex() {}
    virtual int typeNum() const = 0;
    static void clearRank() { s_rankNum=0; }
    virtual int sortCmp(const V3GraphVertex* rhsp) const;
};
uint32_t GaterVertex::s_rankNum = 0;

class GaterHeadVertex : public GaterVertex {
public:
    GaterHeadVertex(V3Graph* graphp)
	: GaterVertex(graphp) {}
    virtual ~GaterHeadVertex() {}
    virtual int typeNum() const { return __LINE__; }  // C++ typeof() equivelent
    virtual string name() const { return "*HEAD*"; }
    virtual string dotColor() const { return "green"; }
};

class GaterPliVertex : public GaterVertex {
public:
    GaterPliVertex(V3Graph* graphp)
	: GaterVertex(graphp) {}
    virtual ~GaterPliVertex() {}
    virtual int typeNum() const { return __LINE__; }  // C++ typeof() equivelent
    virtual string name() const { return "*PLI*"; }
    virtual string dotColor() const { return "red"; }
};

class GaterIfVertex : public GaterVertex {
    AstNodeIf*	m_nodep;
public:
    AstNodeIf* nodep() const { return m_nodep; }
    GaterIfVertex(V3Graph* graphp, AstNodeIf* nodep)
	: GaterVertex(graphp), m_nodep(nodep) { }
    virtual ~GaterIfVertex() {}
    virtual int typeNum() const { return __LINE__; }  // C++ typeof() equivelent
    virtual string name() const { return cvtToStr((void*)m_nodep)+" {"+cvtToStr(m_nodep->fileline()->lineno())+"}"; }
};

class GaterVarVertex : public GaterVertex {
    AstVarScope*	m_nodep;
public:
    AstVarScope* nodep() const { return m_nodep; }
    GaterVarVertex(V3Graph* graphp, AstVarScope* nodep)
	: GaterVertex(graphp), m_nodep(nodep) { }
    virtual ~GaterVarVertex() {}
    virtual int typeNum() const { return __LINE__; }  // C++ typeof() equivelent
    virtual string name() const { return nodep()->name(); }
    virtual string dotColor() const { return "skyblue"; }
};

//######################################################################
// Edge types

class GaterEdge : public V3GraphEdge {
    uint32_t	m_ifelse;	// True branch of if
public:
    // These are used as shift amounts into node's user()
#define VU_DEFINE  enum VarUsage { VU_NONE=0, VU_IF=1, VU_ELSE=2, VU_PLI=4, VU_MADE=8}
    VU_DEFINE;

    uint32_t ifelse() const { return m_ifelse; }
    bool ifelseTrue()  const { return m_ifelse & VU_IF; }
    bool ifelseFalse() const { return m_ifelse & VU_ELSE; }
    bool ifelseBoth() const { return ifelseTrue() && ifelseFalse(); }
    GaterEdge(V3Graph* graphp, V3GraphVertex* fromp, V3GraphVertex* top, uint32_t ifelse)
	: V3GraphEdge(graphp, fromp, top, 10, false), m_ifelse(ifelse) {}
    virtual ~GaterEdge() {}
    virtual string dotColor() const { return ((ifelse() & VU_PLI) ? "red"
					      : (ifelseBoth() ? "blue"
						 : (ifelseTrue() ? "green"
						    : "darkgreen"))); }
    virtual int sortCmp(const V3GraphEdge* rEdgep) const {
	// Our master sort sorts by edges first, so we don't want to
	// consider the upstream vertex::sortCmp when sorting by edges.
	// We do want to order by something though; rank works
	if (fromp()->rank() < rEdgep->fromp()->rank()) return -1;
	if (fromp()->rank() > rEdgep->fromp()->rank()) return 1;
	// If same, resolve by ifelse
	const GaterEdge* crEdgep = static_cast<const GaterEdge*>(rEdgep);
	if (m_ifelse < crEdgep->m_ifelse) return -1;
	if (m_ifelse > crEdgep->m_ifelse) return 1;
	return 0;
    }
};

int GaterVertex::sortCmp(const V3GraphVertex* rhsp) const {
    const GaterVertex* crhsp = static_cast<const GaterVertex*>(rhsp);
    // We really only care about ordering Var's together, but...
    // First put same type together
    if (typeNum() < crhsp->typeNum()) return -1;
    if (typeNum() > crhsp->typeNum()) return 1;
    // If variable, group by same input fanin
    // (know they're the same type based on above compare)
    if (dynamic_cast<const GaterVarVertex*>(this)) {
	// We've already sorted by edges, so just see if same tree
	// If this gets too slow, we could compute a hash up front
	V3GraphEdge* lEdgep = this->inBeginp();
	V3GraphEdge* rEdgep = rhsp->inBeginp();
	while (lEdgep && rEdgep) {
	    const GaterEdge* clEdgep = static_cast<const GaterEdge*>(lEdgep);
	    const GaterEdge* crEdgep = static_cast<const GaterEdge*>(rEdgep);
	    if (lEdgep->fromp()->rank() < rEdgep->fromp()->rank()) return -1;
	    if (lEdgep->fromp()->rank() > rEdgep->fromp()->rank()) return 1;
	    if (clEdgep->ifelse() < crEdgep->ifelse()) return -1;
	    if (clEdgep->ifelse() > crEdgep->ifelse()) return 1;
	    lEdgep = lEdgep->inNextp();
	    rEdgep = rEdgep->inNextp();
	}
	if (!lEdgep && !rEdgep) return 0;
	return lEdgep ? -1 : 1;
    }
    // Finally by rank of this vertex
    if (rank() < rhsp->rank()) return -1;
    if (rank() > rhsp->rank()) return 1;
    return 0;
}

//######################################################################
// Check for non-simple gating equations

class GaterCondVisitor : public GaterBaseVisitor {
private:
    // RETURN STATE
    bool		m_isSimple;	// Set false when we know it isn't simple
    // METHODS
    inline void okIterate(AstNode* nodep) {
	if (m_isSimple) nodep->iterateChildren(*this);
    }
    // VISITORS
    virtual void visit(AstOr* nodep, AstNUser*) {	okIterate(nodep); }
    virtual void visit(AstAnd* nodep, AstNUser*) {	okIterate(nodep); }
    virtual void visit(AstNot* nodep, AstNUser*) {	okIterate(nodep); }
    virtual void visit(AstLogOr* nodep, AstNUser*) {	okIterate(nodep); }
    virtual void visit(AstLogAnd* nodep, AstNUser*) {	okIterate(nodep); }
    virtual void visit(AstLogNot* nodep, AstNUser*) {	okIterate(nodep); }
    virtual void visit(AstVarRef* nodep, AstNUser*) {	okIterate(nodep); }

    // Other possibilities are equals, etc
    // But, we don't want to get too complicated or it will take too much
    // effort to calculate the gater

    virtual void visit(AstNode* nodep, AstNUser*) {
	m_isSimple = false;
	//nodep->iterateChildren(*this);
    }
public:
    // CONSTUCTORS
    GaterCondVisitor(AstNode* nodep) {
	m_isSimple = true;
	nodep->accept(*this);
    }
    virtual ~GaterCondVisitor() {}
    // PUBLIC METHODS
    bool isSimple() const { return m_isSimple; }
};

//######################################################################
// Check for non-simple gating equations

class GaterBodyVisitor : public GaterBaseVisitor {
    // NODE STATE
    // Input state
    //  AstVarScope::user2p()	-> AstAlways* moving this variable to

    enum State {
	// This is used as a bitmask
	STATE_UNKNOWN=0,
	STATE_KEEP=1,	// Seen a variable we need, keep this statement
	STATE_DELETE=2	// Seen a variable we need, delete this statement
	// 3=keep & delete
    };

    bool	m_original;	// Deleting original statements, vs deleting new var statements
    AstNode*	m_exprp;	// New gater expression we are building
    bool	m_cloning;	// Clone this object 0=not sure yet, 1=do
    uint32_t	m_state;	// Parsing state

    // VISITORS
    virtual void visit(AstVarRef* nodep, AstNUser*) {
	if (nodep->lvalue()) {
	    AstVarScope* vscp = nodep->varScopep();
	    if (vscp->user2p()->castNode() == m_exprp) {
		// This variable's block needs to move to the new always
		if (m_original) {
		    UINFO(9,"  VARREF delete in old: "<<nodep<<endl);
		    m_state |= STATE_DELETE;
		} else {
		    UINFO(9,"  VARREF stays in new:  "<<nodep<<endl);
		    m_state |= STATE_KEEP;
		}
	    } else {
		if (m_original) {
		    UINFO(9,"  VARREF other stays in old\n");
		    m_state |= STATE_KEEP;
		} else {
		    UINFO(9,"  VARREF other delete in new\n");
		    m_state |= STATE_DELETE;
		}
	    }
	}
    }

    //virtual void visit(AstNodeIf* nodep, AstNUser*) { ... }
    // Not needed, it's the same handling as any other statement.  Cool, huh?
    // (We may get empty IFs but the constant propagater will rip them up for us)

    virtual void visit(AstNodeStmt* nodep, AstNUser*) {
	uint32_t oldstate = m_state;
	// Find if children want to delete this or not.
	// Note children may bicker, and want to both keep and delete (branches on a if)
	uint32_t childstate;
	{
	    m_state = STATE_UNKNOWN;
	    nodep->iterateChildren(*this);
	    childstate = m_state;
	}
	m_state = oldstate;
	UINFO(9,"    Did state="<<childstate<<"  "<<nodep<<endl);

	// Indeterminate (statement with no lvalue), so keep only in original
	if (childstate == STATE_UNKNOWN) {
	    if (m_original) childstate |= STATE_KEEP;
	    else childstate |= STATE_DELETE;
	}

	if ((childstate & STATE_DELETE) && !(childstate & STATE_KEEP)) {
	    nodep->unlinkFrBack()->deleteTree(); nodep=NULL;
	    // Pass upwards we did delete
	    m_state |= STATE_DELETE;
	} else {
	    // Pass upwards we must keep
	    m_state |= STATE_KEEP;
	}
    }
    virtual void visit(AstNode* nodep, AstNUser*) {
	nodep->iterateChildren(*this);
    }
public:
    // CONSTUCTORS
    GaterBodyVisitor(AstAlways* nodep, AstNode* exprp, bool original) {
	m_exprp = exprp;
	m_original = original;
	m_state = STATE_UNKNOWN;
	m_cloning = false;
	if (debug()>=9) nodep->dumpTree(cout,"  GateBodyIn:  ");
	nodep->bodysp()->iterateAndNext(*this);
	if (debug()>=9) nodep->dumpTree(cout,"  GateBodyOut: ");
	// If there's no statements we shouldn't have had a resulting graph
	// vertex asking for this creation
    }
    virtual ~GaterBodyVisitor() {}
};

//######################################################################
// Create clock gaters

class GaterVisitor : public GaterBaseVisitor {
    // NODE STATE
    // Cleared on Always
    //  AstVarScope::user1p()	-> GaterVarVertex*
    //  AstAlways::user4()	-> bool.  True indicates processed
    // Cleared on each new Always
    //  AstVarScope::user2p()	-> AstAlways* moving this variable to
    AstUser1InUse	m_inuser1;
    AstUser2InUse	m_inuser2;
    AstUser4InUse	m_inuser4;

    // GRAPH STATE
    // Cleared on simplify
    //  Vertex::user()		-> VarUsage: Mark of which if/else edges are hit

    // TYPES
    VU_DEFINE;

    enum MiscConsts {
	IF_DEPTH_MAX = 4,	// IFs deep we bother to analyze
	DOMAINS_MAX = 32	// Clock domains before avoiding O(N^2) blowup
    };

    // MEMBERS
    string	m_nonopt;		// Reason block is not optimizable
    V3Double0	m_statGaters;		// Statistic tracking
    V3Double0	m_statBits;		// Statistic tracking
    bool	m_directlyUnderAlw;	// Immediately under Always or If
    int		m_ifDepth;		// Depth of IF statements
    int		m_numIfs;		// Number of IF statements
    V3Graph	m_graph;		// Scoreboard of var usages/dependencies
    GaterPliVertex*	m_pliVertexp;	// Element specifying PLI ordering
    GaterHeadVertex*	m_headVertexp;	// Top vertex
    V3GraphVertex*	m_aboveVertexp;	// Vertex above this point in tree
    uint32_t		m_aboveTrue;	// Vertex above this point is true branch
    AstVarScope*	m_stmtVscp;	// Current statement had variable assigned
    bool		m_stmtInPli;	// Current statement has PLI

    // METHODS
    void nonOptimizable(AstNode* nodep, const char* reasonp) {
	if (m_nonopt=="") {
	    UINFO(9,"    Nonopt: "<<reasonp<<": "<<nodep<<endl);
	    m_nonopt = reasonp;
	}
    }
    void scoreboardPli(AstNode* nodep) {
	// Order all PLI statements with other PLI statements
	// This insures $display's and such remain in proper order
	// We don't prevent splitting out other non-pli statements, however,
	// because it is common to have $uasserts sprinkled about.
	if (!m_pliVertexp) {
	    m_pliVertexp = new GaterPliVertex(&m_graph);
	}
	if (m_stmtVscp) {  // Already saw a variable, be sure to mark it!
	    GaterVarVertex* varVtxp = (GaterVarVertex*)(m_stmtVscp->user1p());
	    new GaterEdge(&m_graph, m_pliVertexp, varVtxp, VU_PLI);
	}
	m_stmtInPli = true;  // Mark all followon variables too
    }

    // METHODS -- GRAPH stuff
    void simplifyGraph() {
	if (debug()>=9) m_graph.dumpDotFilePrefixed("gater_init", false);

	// We now have all PLI variables with edges FROM the pli vertex
	simplifyPli();
	if (debug()>=9) m_graph.dumpDotFilePrefixed("gater_pli", false);

	// Any vertex that points along both true & false path to variable
	// can be simplfied so parent points to that vertex.  Any vertex
	// that points to a (great...) grandparent of a variable can just
	// point to the edge.
	m_graph.userClearVertices();	// user() will contain VarUsage
	simplifyIfElseRecurse(m_headVertexp);
	if (debug()>=9) m_graph.dumpDotFilePrefixed("gater_ifelse", false);

	m_graph.userClearVertices();	// user() will contain VarUsage
	simplifyGrandRecurse(m_headVertexp, 1);
	if (debug()>=9) m_graph.dumpDotFilePrefixed("gater_grand", false);

	simplifyRemoveUngated(m_headVertexp);

	// Give all signals with same gating term same color
	graphColorSameFeeder();

	if (debug()>=9) m_graph.dumpDotFilePrefixed("gater_done", false);
    }

    void simplifyPli() {
	// For now, we'll not gate any logic with PLI lvariables in it.  In
	// the future we may move PLI statements.  One way to do so is to
	// all below pli VARs to go IfVertex -> PliVertex -> VarVertex then
	// they all must get colored the same. There may be a lot of
	// duplicated edges to the PLI; they'll need cleanup.  All of the
	// later optimizations need to deal, and the GaterBodyVisitor needs
	// to know how to move them.
	if (m_pliVertexp) {
	    // Follow PLI out edges to find all relevant variables
	    for (V3GraphEdge* nextp,* edgep = m_pliVertexp->outBeginp(); edgep; edgep = nextp) {
		nextp = edgep->outNextp();  // We may edit the list
		if (GaterVarVertex* vVxp = dynamic_cast<GaterVarVertex*>(edgep->top())) {
		    vVxp->unlinkDelete(&m_graph); vVxp=NULL; edgep=NULL;
		} else {
		    m_graph.dump();
		    v3fatalSrc("PLI vertex points to non-signal");
		}
	    }
	    m_pliVertexp->unlinkDelete(&m_graph); m_pliVertexp = NULL;
	}
    }

    void simplifyIfElseRecurse(V3GraphVertex* vertexp) {
	// From bottom-up, propagate duplicate IF/ELSE branches to grandparent
	for (V3GraphEdge* edgep = vertexp->outBeginp(); edgep; edgep=edgep->outNextp()) {
	    simplifyIfElseRecurse(edgep->top());
	}
	//UINFO(9,"IERecurse "<<vertexp<<endl);
	if (dynamic_cast<GaterIfVertex*>(vertexp)) {
	    // Clear indications
	    for (V3GraphEdge* edgep = vertexp->outBeginp(); edgep; edgep=edgep->outNextp()) {
		edgep->top()->user(VU_NONE);
	    }
	    // Mark nodes on to/from side
	    for (V3GraphEdge* edgep = vertexp->outBeginp(); edgep; edgep=edgep->outNextp()) {
		V3GraphVertex* toVxp = edgep->top();
		GaterEdge* cedgep = static_cast<GaterEdge*>(edgep);
		// We may mark this twice in one pass - if so it's duplicated; no worries
		if (cedgep->ifelseTrue()) toVxp->user(toVxp->user() | VU_IF);
		if (cedgep->ifelseFalse()) toVxp->user(toVxp->user() | VU_ELSE);
		//UINFO(9,"  mark "<<edgep<<" "<<toVxp<<endl);
	    }
	    // Any with both IF & ELSE mark get removal mark, and new parent edge
	    for (V3GraphEdge* nextp,* edgep = vertexp->outBeginp(); edgep; edgep = nextp) {
		nextp = edgep->outNextp();  // We may edit the list
		V3GraphVertex* toVxp = edgep->top();
		//UINFO(9," to "<<toVxp->user()<<" "<<toVxp<<endl);
		if ((toVxp->user() & VU_IF) && (toVxp->user() & VU_ELSE)) {
		    edgep->unlinkDelete(); edgep = NULL;
		    if (!(toVxp->user() & VU_MADE)) {   // Make an edge only once
			toVxp->user(toVxp->user() | VU_MADE);
			GaterEdge* inedgep = static_cast<GaterEdge*>(vertexp->inBeginp());
			V3GraphVertex* grandparent = inedgep->fromp();
			new GaterEdge(&m_graph, grandparent, toVxp, inedgep->ifelse());
		    }
		}
	    }
	}
    }

    void simplifyGrandRecurse(V3GraphVertex* vertexp, uint32_t depth) {
	// From top-down delete any vars that grandparents source
	// IE    A -> B -> C -> VAR
	//         \----------^
	//UINFO(9,"GRecurse "<<depth<<" "<<vertexp<<endl);
	// Mark all variables to be swept
	for (V3GraphEdge *nextp, *edgep = vertexp->outBeginp(); edgep; edgep=nextp) {
	    nextp = edgep->outNextp();  // We may edit the list
	    if (GaterVarVertex* toVxp = dynamic_cast<GaterVarVertex*>(edgep->top())) {
		if (toVxp->user() && toVxp->user() < depth) {
		    // A recursion "above" us marked it,
		    // Remove this edge, it's redundant with the upper edge
		    edgep->unlinkDelete(); edgep=NULL;
		} else {
		    GaterEdge* cedgep = static_cast<GaterEdge*>(edgep);
		    if (cedgep->ifelseBoth()) {
			toVxp->user(depth);
		    }
		}
	    }
	}
	// Recurse
	for (V3GraphEdge* edgep = vertexp->outBeginp(); edgep; edgep=edgep->outNextp()) {
	    simplifyGrandRecurse(edgep->top(), depth+1);
	}
	// Clean our marks
	for (V3GraphEdge* edgep = vertexp->outBeginp(); edgep; edgep=edgep->outNextp()) {
	    V3GraphVertex* toVxp = edgep->top();
	    if (toVxp->user() && toVxp->user() < depth) {  // A recursion "above" us marked it; don't mess with it
	    } else {
		toVxp->user(0);  // We marked it originally, so unmark now
	    }
	}
	// Delete any If nodes with no children
	// Last, as want bottom-up cleanup
	for (V3GraphEdge *nextp, *edgep = vertexp->outBeginp(); edgep; edgep=nextp) {
	    nextp = edgep->outNextp();  // We may edit the list
	    if (GaterIfVertex* toVxp = dynamic_cast<GaterIfVertex*>(edgep->top())) {
		if (!toVxp->outBeginp()) {
		    if (!nextp || nextp->top() != edgep->top()) {  // Else next would disappear; we'll do it next loop
			toVxp->unlinkDelete(&m_graph); toVxp=NULL; edgep=NULL;
		    }
		}
	    }
	}
    }

    void simplifyRemoveUngated(V3GraphVertex* vertexp) {
	// Remove variables that are ungated
	// At this point, any variable under the head is ungated
	for (V3GraphEdge *nextp, *edgep = vertexp->outBeginp(); edgep; edgep=nextp) {
	    nextp = edgep->outNextp();  // We may edit the list
	    if (GaterVarVertex* toVxp = dynamic_cast<GaterVarVertex*>(edgep->top())) {
		if (!nextp || nextp->top() != edgep->top()) {  // Else next would disappear; we'll do it next loop
		    toVxp->unlinkDelete(&m_graph); toVxp=NULL; edgep=NULL;
		}
	    }
	}
    }

    void graphColorSameFeeder() {
	// Assign same color to all destination vertices that have same
	// subgraph feeding into them
	// (I.E. all "from" nodes are common within each color)
	// We could hash, but instead it's faster to sort edges, so we know
	// the same edge list is always adjacent.  The result is a
	// O(vertices*edges) loop, but we'd need that to hash too.
	if (debug()>9) { cout<<"PreColor:\n"; m_graph.dump(); }

	m_graph.sortEdges();

	// Now sort vertices, so same inbound edge set ends up adjacent
	m_graph.sortVertices();

	// Now walk and assign colors; same color is adjacent
	m_graph.clearColors();
	m_graph.userClearEdges(); // Used by newExprFromGraph
	uint32_t color = 1;
	GaterVarVertex* lastVxp	= NULL;
	for (V3GraphVertex* vertexp = m_graph.verticesBeginp(); vertexp; vertexp=vertexp->verticesNextp()) {
	    if (GaterVarVertex* vVxp = dynamic_cast<GaterVarVertex*>(vertexp)) {
		if (!vVxp->inBeginp()) {
		    // At this point, any variable not linked is an error
		    // (It should have at least landed under the Head node)
		    vVxp->nodep()->v3fatalSrc("Variable became stranded in clk gate detection\n");
		}
		if (!lastVxp || vVxp->sortCmp(lastVxp)) {
		    // Different sources for this new node
		    color++;
		}
		vVxp->color(color);
		lastVxp = vVxp;
	    }
	}

	if (debug()>9) { cout<<"PostColor:\n"; m_graph.dump(); }
    }

    AstNode* newExprFromGraph(GaterVarVertex* vertexp) {
	// Recurse backwards, then form equation on return path
	// We could use user()!=0, but zeroing it is slow, so instead we'll mark with a generation
	// We get equations like "a | (!a & b)" which obviously could be reduced here,
	// instead out of generality, there's a V3Const::matchOrAndNot that'll clean it up
	static uint32_t s_generation = 0;
	++s_generation;
	nafgMarkRecurse(vertexp, s_generation);
	AstNode* nodep = nafgCreateRecurse(m_headVertexp, s_generation);
	if (debug()>=9) nodep->dumpTree(cout,"  GateExpr: ");
	return nodep;
    }
    void nafgMarkRecurse(V3GraphVertex* vertexp, uint32_t generation) {
	// Backwards mark user() on the path we recurse
	//UINFO(9," nafgMark: v "<<(void*)(vertexp)<<" "<<vertexp->name()<<endl);
	for (V3GraphEdge* edgep = vertexp->inBeginp(); edgep; edgep = edgep->inNextp()) {
	    //UINFO(9," nafgMark: "<<(void*)(edgep)<<" "<<edgep->name()<<endl);
	    edgep->user(generation);
	    nafgMarkRecurse(edgep->fromp(), generation);
	}
    }
    AstNode* nafgCreateRecurse(V3GraphVertex* vertexp, uint32_t generation) {
	// Forewards follow user() marked previously and build tree
	AstNode* nodep = NULL;
	// OR across all edges found at this level
	//UINFO(9," nafgEnter: v "<<(void*)(vertexp)<<" "<<vertexp->name()<<endl);
	for (V3GraphEdge* edgep = vertexp->outBeginp(); edgep; edgep = edgep->outNextp()) {
	    if (edgep->user() == generation) {
		GaterEdge* cedgep = static_cast<GaterEdge*>(edgep);
		AstNode* eqnp = NULL;
		//UINFO(9," nafgFollow: "<<(void*)(edgep)<<" "<<edgep->name()<<endl);
		if (dynamic_cast<GaterHeadVertex*>(edgep->fromp())) {
		    // Just OR in all lower terms
		    eqnp = nafgCreateRecurse(edgep->top(), generation);
		} else if (GaterIfVertex* cVxp = dynamic_cast<GaterIfVertex*>(edgep->fromp())) {
		    // Edges from IFs represent a real IF branch in the equation tree
		    //UINFO(9,"  ifver "<<(void*)(edgep)<<" cc"<<edgep->dotColor()<<endl);
		    eqnp = cVxp->nodep()->condp()->cloneTree(true);
		    if (eqnp && cedgep->ifelseFalse()) {
			eqnp = new AstNot(eqnp->fileline(),eqnp);
		    }
		    // We need to AND this term onto whatever was found below it
		    AstNode* belowp = nafgCreateRecurse(edgep->top(), generation);
		    if (belowp) eqnp = new AstAnd(eqnp->fileline(),eqnp,belowp);
		}
		// Top level we could choose to make multiple gaters, or ORs under the gater
		// Right now we'll put OR lower down and let other optimizations deal
		if (nodep) nodep = new AstOr(eqnp->fileline(),nodep,eqnp);
		else nodep = eqnp;
		//if (debug()>=9) nodep->dumpTree(cout,"      followExpr: ");
	    }
	}
	//UINFO(9," nafgExit:  "<<(void*)(vertexp)<<" "<<vertexp->name()<<endl);
	return nodep;
    }

    void newAlwaysTrees(AstAlways* nodep) {
	// Across all variables we're moving
	uint32_t lastColor = 0;
	AstNode* lastExprp = NULL;
	for (V3GraphVertex* vertexp = m_graph.verticesBeginp(); vertexp; vertexp=vertexp->verticesNextp()) {
	    if (GaterVarVertex* vVxp = dynamic_cast<GaterVarVertex*>(vertexp)) {
		if (!lastExprp || lastColor != vVxp->color()) {
		    lastColor = vVxp->color();
		    // Create the block we've just finished
		    if (lastExprp) newAlwaysTree(nodep, lastExprp); // Duplicate below
		    // New expression for this color
		    lastExprp = newExprFromGraph(vVxp);
		}
		// Mark variable to move
		if (vVxp->nodep()->user2p()) vVxp->nodep()->v3fatalSrc("One variable got marked under two gaters");
		vVxp->nodep()->user2p(lastExprp);
		m_statBits += vVxp->nodep()->width();  // Moving a wide bus counts more!
		// There shouldn't be two possibilities we want to
		// move to, IE {A,B} <= Z because we marked such
		// things as unoptimizable
	    }
	}
	// Create the final block we've just finished
	if (lastExprp) newAlwaysTree(nodep, lastExprp);   // Duplicate above
    }

    void newAlwaysTree(AstAlways* nodep, AstNode* exprp) {
	// Create new always with specified gating expression
	// Relevant vars are already marked with user2p

	// Should we put the gater under the always itself,
	// or make a new signal?
	//   New signal: May cause replicated logic until we can combine
	//		Need way to toggle signal on complicated pos/negedge
	//   Under Always: More complicated, may not propagate logic with gateer
	//	Untill we get better gate optimization, we'll go this route.
//#define GATER_NOP
#ifdef GATER_NOP
	// For testing only, don't clock gate but still make new always
	AstSenTree* sensesp = nodep->sensesp()->cloneTree(true);
#else
	// Make a SenGate
	AstSenItem* oldsenitemsp = nodep->sensesp()->sensesp()->castSenItem();
	if (!oldsenitemsp) nodep->v3fatalSrc("SenTree doesn't have any SenItem under it");

	AstSenTree* sensesp = new AstSenTree(nodep->fileline(),
					     new AstSenGate(nodep->fileline(),
							    oldsenitemsp->cloneTree(true),
							    exprp));
#endif

	// Make new body; note clone will preserve user2p() indicating moving vars
	AstNode* bodyp = nodep->bodysp()->cloneTree(true);

	AstAlways* alwp = new AstAlways(nodep->fileline(),
					nodep->keyword(),
					sensesp,
					bodyp);

	alwp->user4(1);  // No need to process the new always again!
	nodep->addNextHere(alwp);

	// Blow moved statements from old body
	GaterBodyVisitor(nodep,exprp,true);
	// Blow old statements from new body
	GaterBodyVisitor(alwp,exprp,false);

	++m_statGaters;
	if (debug()>=9) alwp->dumpTree(cout,"  new: ");
    }

    // VISITORS
    virtual void visit(AstAlways* nodep, AstNUser*) {
	if (debug()>=9) cout<<endl<<endl<<endl;
	UINFO(5, "Gater: ALWAYS: "<<nodep<<endl);
	if (nodep->user4SetOnce()) return;

	clear();

	if (debug()>=9) nodep->dumpTree(cout,"  Alwin:  ");

	// Look for constructs we can't optimize
	// Form graph with Vertices at each IF, and each Variable
	m_aboveTrue = VU_IF | VU_ELSE;
	iterateChildrenAlw(nodep, true);

	// Other reasons to not optimize
	if (!m_numIfs) nonOptimizable(nodep, "No if statements");

	// Something to optimize, oh my!
	if (m_nonopt!="") {
	    UINFO(5, "  Gater non-opt: "<<m_nonopt<<endl);
	} else {
	    // Process it
	    simplifyGraph();

	    // See how much moves
	    uint32_t lastColor = 0;
	    for (V3GraphVertex* vertexp = m_graph.verticesBeginp(); vertexp; vertexp=vertexp->verticesNextp()) {
		if (GaterVarVertex* vVxp = dynamic_cast<GaterVarVertex*>(vertexp)) {
		    if (lastColor < vVxp->color()) {
			lastColor = vVxp->color();
		    }
		}
	    }
	    if (lastColor == 0) { // Nothing we moved!
		nonOptimizable(nodep, "Nothing moved");
	    }
	    else if (lastColor > DOMAINS_MAX) {
		// Our move algorithm is fairly slow and if we're splitting
		// up too much it'll get really nasty.  It's probably a bad
		// move for performance to split too much, anyhow, as the
		// number of gaters will result in calling many small c functions.
		nonOptimizable(nodep, "Too much moved");
	    }
	    if (m_nonopt=="") {
		newAlwaysTrees(nodep);
		if (debug()>=9) nodep->dumpTree(cout,"  Gaterout: ");
	    }
	}
	UINFO(5, "  Gater done"<<endl);
    }
    virtual void visit(AstVarRef* nodep, AstNUser*) {
	if (nodep->lvalue()) {
	    AstVarScope* vscp = nodep->varScopep();
	    if (nodep->varp()->isSigPublic()) {
		// Public signals shouldn't be changed, pli code might be messing with them
		scoreboardPli(nodep);
	    }
	    // If another lvalue in this node, give up optimizing.
	    // We could just not optimize this variable, but we've already marked the
	    // other variable as optimizable, so we can instead pretend it's a PLI node.
	    if (m_stmtVscp) {
		UINFO(5, "   Multiple lvalues in one statement: "<<nodep<<endl);
		scoreboardPli(nodep);  // This will set m_stmtInPli
	    }
	    m_stmtVscp = vscp;
	    // Find, or make new Vertex
	    GaterVarVertex* vertexp = (GaterVarVertex*)(vscp->user1p());
	    if (!vertexp) {
		vertexp = new GaterVarVertex(&m_graph, vscp);
		vscp->user1p(vertexp);
	    }
	    new GaterEdge(&m_graph, m_aboveVertexp, vertexp, m_aboveTrue);
	    if (m_stmtInPli) {
		new GaterEdge(&m_graph, m_pliVertexp, vertexp, VU_PLI);
	    }
	}
    }
    virtual void visit(AstNodeIf* nodep, AstNUser*) {
	m_ifDepth++;
	bool allowGater = m_directlyUnderAlw && m_ifDepth <= IF_DEPTH_MAX;
	if (allowGater) {
	    GaterCondVisitor condVisitor(nodep->condp());
	    if (!condVisitor.isSimple()) {
		// Don't clear optimization, simply drop this IF as part of the gating
		UINFO(5,"   IFnon-simple-condition: "<<nodep<<endl);
		allowGater = false;
	    }
	}
	if (!allowGater) {
	    // IF burried under something complicated
	    iterateChildrenAlw(nodep, true);
	} else {
	    UINFO(5, "  IF: "<<nodep<<endl);
	    m_numIfs++;
	    // Recurse to next level of if.
	    V3GraphVertex*	lastabovep = m_aboveVertexp;
	    uint32_t		lasttrue = m_aboveTrue;
	    GaterIfVertex* vertexp = new GaterIfVertex(&m_graph, nodep);
	    new GaterEdge(&m_graph, m_aboveVertexp, vertexp, m_aboveTrue);
	    {
		nodep->condp()->iterateAndNext(*this);  // directlyUnder stays as-is
	    }
	    {
		m_aboveVertexp = vertexp;  // Vars will point at this edge
		m_aboveTrue = VU_IF;
		nodep->ifsp()->iterateAndNext(*this);  // directlyUnder stays as-is (true)
	    }
	    {
		m_aboveVertexp = vertexp;  // Vars will point at this edge
		m_aboveTrue = VU_ELSE;
		nodep->elsesp()->iterateAndNext(*this);  // directlyUnder stays as-is (true)
	    }
	    m_aboveVertexp = lastabovep;
	    m_aboveTrue = lasttrue;
	}
	m_ifDepth--;
    }

    virtual void visit(AstAssignDly* nodep, AstNUser*) {
	// iterateChildrenAlw will detect this is a statement for us
	iterateChildrenAlw(nodep, false);
    }

    virtual void visit(AstNodeAssign* nodep, AstNUser*) {
	// Note NOT AssignDly; handled above, We'll just mark this block as
	// not optimizable.
	//
	// A future alternative is to look for any lvalues that are also
	// variables in the sensitivity list, or rvalues in this block.  If
	// any hit, disable optimization.  Unlikely to be useful (For loops
	// being an exception, but they're already unrolled.)
	nonOptimizable(nodep, "Non-delayed assignment");
	// No reason to iterate.
    }

    virtual void visit(AstSenItem* nodep, AstNUser*) {
	if (!nodep->isClocked()) {
	    nonOptimizable(nodep, "Non-clocked sensitivity");
	}
	iterateChildrenAlw(nodep, false);
    }

    //--------------------
    virtual void visit(AstNode* nodep, AstNUser*) {
	if (m_nonopt=="") {  // Else accelerate
	    iterateChildrenAlw(nodep, false);
	}
    }
    inline void iterateChildrenAlw(AstNode* nodep, bool under) {
	// **** USE THIS INSTEAD OF iterateChildren!
	// Note If visitor doesn't call here; does it its own way
	bool lastdua = m_directlyUnderAlw;
	AstVarScope* lastvscp = m_stmtVscp;
	bool lastpli = m_stmtInPli;
	m_directlyUnderAlw = under;
	if (nodep->castNodeStmt()) {  // Restored below
	    UINFO(9,"       Stmt: "<<nodep<<endl);
	    m_stmtVscp = NULL;
	    m_stmtInPli = false;
	}
	if (!nodep->isPure() || nodep->isBrancher()) {
	    // May also be a new statement (above if); if so we mark it immediately
	    UINFO(9,"         NotPure "<<nodep<<endl);
	    scoreboardPli(nodep);
	}
	{
	    nodep->iterateChildren(*this);
	}
	m_directlyUnderAlw = lastdua;
	if (nodep->castNodeStmt()) {  // Reset what set above; else propagate up to above statement
	    m_stmtVscp = lastvscp;
	    m_stmtInPli = lastpli;
	}
    }

public:
    // CONSTUCTORS
    GaterVisitor(AstNode* nodep) {
	// AstAlways visitor does the real work, so most zeroing needs to be in clear()
	clear();
	nodep->accept(*this);
    }
    void clear() {
	m_nonopt = "";
	m_directlyUnderAlw = false;
	m_ifDepth = 0;
	m_numIfs = 0;
	AstNode::user1ClearTree();
	AstNode::user2ClearTree();
	// Prepare graph
	m_graph.clear();
	GaterVertex::clearRank();
	m_pliVertexp = NULL;
	m_headVertexp = new GaterHeadVertex(&m_graph);
	m_aboveVertexp = m_headVertexp;
	m_aboveTrue = false;
	m_stmtVscp = NULL;
	m_stmtInPli = false;
    }
    virtual ~GaterVisitor() {
	V3Stats::addStat("Optimizations, Gaters inserted", m_statGaters);
	V3Stats::addStat("Optimizations, Gaters impacted bits", m_statBits);
    }
};

//######################################################################
// Active class functions

void V3ClkGater::clkGaterAll(AstNetlist* nodep) {
    UINFO(2,__FUNCTION__<<": "<<endl);
    // While the gater does well at some modules, it seems to slow down many others
    UINFO(5,"ClkGater is disabled due to performance issues\n");
    //GaterVisitor visitor (nodep);
    V3Global::dumpCheckGlobalTree("clkgater.tree", 0, v3Global.opt.dumpTreeLevel(__FILE__) >= 3);
}
