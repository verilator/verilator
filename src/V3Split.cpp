// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Break always into separate statements to reduce temps
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
// V3Split's Transformations:
//
// Note this can be called multiple times.
//	ALWAYS
//		ASSIGN ({var} <= {cons})
//		Record as generating var_DLY (independent of use of var), consumers
//		ASSIGN ({var} = {cons}
//		Record generator and consumer
//	Any var that is only consumed can be ignored.
//	Then we split into a separate ALWAYS block for each top level statement.
//
// Furthermore, optionally
//	NODEASSIGN/NODEIF/WHILE
//		S1: ASSIGN {v1} <= 0.   // Duplicate of below
//		S2: ASSIGN {v1} <= {v0}
//		S3: IF (...,
//			X1: ASSIGN {v2} <= {v1}
//			X2: ASSIGN {v3} <= {v2}
//	We'd like to swap S2 and S3, and X1 and X2.
//
//  Create a graph in split assignment order.
//  	v3 -breakable-> v3Dly --> X2 --> v2 -brk-> v2Dly -> X1 -> v1
//	Likewise on each "upper" statement vertex
//		v3Dly & v2Dly -> S3 -> v1 & v2
//		v1 -brk-> v1Dly -> S2 -> v0
//			  v1Dly -> S1 -> {empty}
//  Multiple assignments to the same variable must remain in order
//
//  Also vars must not be "public" and we also scoreboard nodep->isPure()
//
//*************************************************************************

#include "config_build.h"
#include "verilatedos.h"
#include <cstdio>
#include <cstdarg>
#include <unistd.h>
#include <algorithm>
#include <vector>
#include <map>

#include "V3Global.h"
#include "V3Split.h"
#include "V3Stats.h"
#include "V3Ast.h"
#include "V3Graph.h"

//######################################################################
// Support classes

class SplitPliVertex : public V3GraphVertex {
public:
    SplitPliVertex(V3Graph* graphp)
	: V3GraphVertex(graphp) {}
    virtual ~SplitPliVertex() {}
    virtual string name() const { return "*PLI*"; }
    virtual string dotColor() const { return "green"; }
};

class SplitNodeVertex : public V3GraphVertex {
    AstNode*	m_nodep;
protected:
    SplitNodeVertex(V3Graph* graphp, AstNode* nodep)
	: V3GraphVertex(graphp), m_nodep(nodep) {}
    virtual ~SplitNodeVertex() {}
    // Accessors
    // Do not make accessor for nodep(),  It may change due to
    // reordering a lower block, but we don't repair it
    virtual string name() const {
	if (m_nodep->name() == "") {
	    return cvtToStr((void*)m_nodep);
	} else {
	    return m_nodep->name();
	}
    }
};

class SplitLogicVertex : public SplitNodeVertex {
    uint32_t	m_splitColor;	// Copied from color() when determined
public:
    SplitLogicVertex(V3Graph* graphp, AstNode* nodep)
	: SplitNodeVertex(graphp,nodep), m_splitColor(0) {}
    void splitColor(uint32_t flag) { m_splitColor=flag; }
    uint32_t splitColor() const { return m_splitColor; }
    virtual ~SplitLogicVertex() {}
    virtual string dotColor() const { return "yellow"; }
};

class SplitVarStdVertex : public SplitNodeVertex {
public:
    SplitVarStdVertex(V3Graph* graphp, AstNode* nodep)
	: SplitNodeVertex(graphp,nodep) {}
    virtual ~SplitVarStdVertex() {}
    virtual string dotColor() const { return "skyblue"; }
};

class SplitVarPostVertex : public SplitNodeVertex {
public:
    SplitVarPostVertex(V3Graph* graphp, AstNode* nodep)
	: SplitNodeVertex(graphp,nodep) {}
    virtual ~SplitVarPostVertex() {}
    virtual string name() const { return (string)"POST "+SplitNodeVertex::name(); }
    virtual string dotColor() const { return "CadetBlue"; }
};

//######################################################################
// Edge types

class SplitEdge : public V3GraphEdge {
    uint32_t	m_ignoreInStep;	// Step number that if set to, causes this edge to be ignored
    static uint32_t	s_stepNum;	// Global step number
protected:
    enum { WEIGHT_NORMAL=10 };
    SplitEdge(V3Graph* graphp, V3GraphVertex* fromp, V3GraphVertex* top,
		int weight, bool cutable=CUTABLE)
	: V3GraphEdge(graphp, fromp, top, weight, cutable)
	,m_ignoreInStep(0) {}
    virtual ~SplitEdge() {}
public:
    // Iterator for graph functions
    static void incrementStep() { ++s_stepNum; }
    bool ignoreThisStep() const { return m_ignoreInStep == s_stepNum; }
    void setIgnoreThisStep() { m_ignoreInStep = s_stepNum; }
    virtual bool followScoreboard() const = 0;
    static bool followScoreboard(const V3GraphEdge* edgep) {
	const SplitEdge* oedgep = dynamic_cast<const SplitEdge*>(edgep);
	if (!oedgep) v3fatalSrc("Following edge of non-SplitEdge type");
	if (oedgep->ignoreThisStep()) return false;
	return oedgep->followScoreboard();
    }
    static bool followCyclic(const V3GraphEdge* edgep) {
	const SplitEdge* oedgep = dynamic_cast<const SplitEdge*>(edgep);
	if (!oedgep) v3fatalSrc("Following edge of non-SplitEdge type");
	if (oedgep->ignoreThisStep()) return false;
	return true;
    }
};
uint32_t	SplitEdge::s_stepNum = 0;

class SplitPostEdge : public SplitEdge {
public:
    SplitPostEdge(V3Graph* graphp, V3GraphVertex* fromp, V3GraphVertex* top)
	: SplitEdge(graphp, fromp, top, WEIGHT_NORMAL) {}
    virtual ~SplitPostEdge() {}
    virtual bool followScoreboard() const { return false; }
    virtual string dotColor() const { return "khaki"; }
    virtual string dotStyle() const { return ignoreThisStep()?"dotted":V3GraphEdge::dotStyle(); }
};

class SplitLVEdge : public SplitEdge {
public:
    SplitLVEdge(V3Graph* graphp, V3GraphVertex* fromp, V3GraphVertex* top)
	: SplitEdge(graphp, fromp, top, WEIGHT_NORMAL) {}
    virtual ~SplitLVEdge() {}
    virtual bool followScoreboard() const { return true; }
    virtual string dotColor() const { return "yellowGreen"; }
    virtual string dotStyle() const { return ignoreThisStep()?"dotted":V3GraphEdge::dotStyle(); }
};

class SplitRVEdge : public SplitEdge {
public:
    SplitRVEdge(V3Graph* graphp, V3GraphVertex* fromp, V3GraphVertex* top)
	: SplitEdge(graphp, fromp, top, WEIGHT_NORMAL) {}
    virtual ~SplitRVEdge() {}
    virtual bool followScoreboard() const { return true; }
    virtual string dotColor() const { return "green"; }
    virtual string dotStyle() const { return ignoreThisStep()?"dotted":V3GraphEdge::dotStyle(); }
};

struct SplitScorebdEdge : public SplitEdge {
public:
    SplitScorebdEdge(V3Graph* graphp, V3GraphVertex* fromp, V3GraphVertex* top)
	: SplitEdge(graphp, fromp, top, WEIGHT_NORMAL) {}
    virtual ~SplitScorebdEdge() {}
    virtual bool followScoreboard() const { return true; }
    virtual string dotColor() const { return "blue"; }
    virtual string dotStyle() const { return ignoreThisStep()?"dotted":V3GraphEdge::dotStyle(); }
};

struct SplitStrictEdge : public SplitEdge {
    // A strict order, based on the original statement order in the graph
    // The only non-cutable edge type
public:
    SplitStrictEdge(V3Graph* graphp, V3GraphVertex* fromp, V3GraphVertex* top)
	: SplitEdge(graphp, fromp, top, WEIGHT_NORMAL, NOT_CUTABLE) {}
    virtual ~SplitStrictEdge() {}
    virtual bool followScoreboard() const { return true; }
    virtual string dotColor() const { return "blue"; }
    virtual string dotStyle() const { return ignoreThisStep()?"dotted":V3GraphEdge::dotStyle(); }
};

//######################################################################
// Split class functions

class SplitVisitor : public AstNVisitor {
private:
    // NODE STATE
    // AstVarScope::user1p	-> Var SplitNodeVertex* for usage var, 0=not set yet
    // AstVarScope::user2p	-> Var SplitNodeVertex* for delayed assignment var, 0=not set yet
    // Ast*::user3p		-> Statement SplitLogicVertex* (temporary only)
    // Ast*::user4		-> Current ordering number (reorderBlock usage)
    AstUser1InUse	m_inuser1;
    AstUser2InUse	m_inuser2;
    AstUser3InUse	m_inuser3;
    AstUser4InUse	m_inuser4;

    // TYPES
    typedef vector<SplitLogicVertex*> VStack;

    // STATE
    bool		m_reorder;	// Reorder statements vs. just splitting
    string		m_noReorderWhy;	// Reason we can't reorder
    VStack		m_stmtStackps;	// Current statements being tracked
    SplitPliVertex*	m_pliVertexp;	// Element specifying PLI ordering
    V3Graph		m_graph;	// Scoreboard of var usages/dependencies
    bool		m_inDly;	// Inside ASSIGNDLY
    V3Double0		m_statSplits;	// Statistic tracking

    // METHODS
    static int debug() {
	static int level = -1;
	if (VL_UNLIKELY(level < 0)) level = v3Global.opt.debugSrcLevel(__FILE__);
	return level;
    }

    void scoreboardClear() {
	//VV*****  We reset user1p() and user2p on each block!!!
	m_inDly = false;
	m_graph.clear();
	m_stmtStackps.clear();
	m_pliVertexp = NULL;
	m_noReorderWhy = "";
	AstNode::user1ClearTree();
	AstNode::user2ClearTree();
	AstNode::user3ClearTree();
	AstNode::user4ClearTree();
    }

    void scoreboardPli() {
	// Order all PLI statements with other PLI statements
	// This insures $display's and such remain in proper order
	// We don't prevent splitting out other non-pli statements, however.
	if (!m_pliVertexp) {
	    m_pliVertexp = new SplitPliVertex(&m_graph);  // m_graph.clear() will delete it
	}
	for (VStack::iterator it = m_stmtStackps.begin(); it != m_stmtStackps.end(); ++it) {
	    // Both ways...
	    new SplitScorebdEdge(&m_graph, *it, m_pliVertexp);
	    new SplitScorebdEdge(&m_graph, m_pliVertexp, *it);
	}
    }
    void scoreboardPushStmt(AstNode* nodep) {
	//UINFO(9,"    push "<<nodep<<endl);
	SplitLogicVertex* vertexp = new SplitLogicVertex(&m_graph, nodep);
	m_stmtStackps.push_back(vertexp);
	if (nodep->user3p()) nodep->v3fatalSrc("user3p should not be used; cleared in processBlock\n");
	nodep->user3p(vertexp);
    }
    void scoreboardPopStmt() {
	//UINFO(9,"    pop"<<endl);
	if (m_stmtStackps.empty()) v3fatalSrc("Stack underflow\n");
	m_stmtStackps.pop_back();
    }

    void scanBlock(AstNode* nodep) {
	// Iterate across current block, making the scoreboard
	for (AstNode* nextp=nodep; nextp; nextp=nextp->nextp()) {
	    scoreboardPushStmt(nextp);
	    nextp->accept(*this);
	    scoreboardPopStmt();
	}
    }

    void cleanupBlockGraph(AstNode* nodep) {
	// Transform the graph into what we need
	UINFO(5, "ReorderBlock "<<nodep<<endl);
	m_graph.removeRedundantEdges(&V3GraphEdge::followAlwaysTrue);

	if (debug()>=9) {
	    m_graph.dumpDotFilePrefixed("splitg_nodup", false);
	    //m_graph.dump(); cout<<endl;
	}

	// Mark all the logic for this step
	// Vertex::m_user begin: true indicates logic for this step
	m_graph.userClearVertices();
	for (AstNode* nextp=nodep; nextp; nextp=nextp->nextp()) {
	    SplitLogicVertex* vvertexp = (SplitLogicVertex*)nextp->user3p();
	    vvertexp->user(true);
	}

	// If a var vertex has only inputs, it's a input-only node,
	// and can be ignored for coloring **this block only**
	SplitEdge::incrementStep();
	uint32_t numVertexes = 1;  // As colors start at 1, not 0
	for (V3GraphVertex* vertexp = m_graph.verticesBeginp(); vertexp; vertexp=vertexp->verticesNextp()) {
	    numVertexes++;
	    if (!vertexp->outBeginp() && dynamic_cast<SplitVarStdVertex*>(vertexp)) {
		for (V3GraphEdge* edgep = vertexp->inBeginp(); edgep; edgep=edgep->inNextp()) {
		    SplitEdge* oedgep = dynamic_cast<SplitEdge*>(edgep);
		    oedgep->setIgnoreThisStep();
		}
	    }
	    // Mark all logic vertexes not involved with this step as unimportant
	    if (SplitLogicVertex* vvertexp = dynamic_cast<SplitLogicVertex*>(vertexp)) {
		if (!vvertexp->user()) {
		    for (V3GraphEdge* edgep = vertexp->inBeginp(); edgep; edgep=edgep->inNextp()) {
			SplitEdge* oedgep = dynamic_cast<SplitEdge*>(edgep);
			oedgep->setIgnoreThisStep();
		    }
		    for (V3GraphEdge* edgep = vertexp->outBeginp(); edgep; edgep=edgep->outNextp()) {
			SplitEdge* oedgep = dynamic_cast<SplitEdge*>(edgep);
			oedgep->setIgnoreThisStep();
		    }
		}
	    }
	}

	// Weak coloring to determine what needs to remain in order
	// This follows all step-relevant edges excluding PostEdges, which are done later
	m_graph.weaklyConnected(&SplitEdge::followScoreboard);

	// Add hard orderings between all nodes of same color, in the order they appeared
	vector<SplitLogicVertex*> lastOfColor;  lastOfColor.resize(numVertexes);
	for (uint32_t i=0; i<numVertexes; i++) lastOfColor[i] = NULL;
	for (AstNode* nextp=nodep; nextp; nextp=nextp->nextp()) {
	    SplitLogicVertex* vvertexp = (SplitLogicVertex*)nextp->user3p();
	    vvertexp->splitColor(vvertexp->color());
	    uint32_t color = vvertexp->splitColor();
	    if (color >= numVertexes) nextp->v3fatalSrc("More colors than vertexes!\n");
	    if (!color) nextp->v3fatalSrc("No node color assigned\n");
	    if (lastOfColor[color]) {
		new SplitStrictEdge(&m_graph, lastOfColor[color], vvertexp);
	    }
	    lastOfColor[color] = vvertexp;
	}

	// And a real ordering to get the statements into something reasonable
	// We don't care if there's cutable violations here...
	// Non-cutable violations should be impossible; as those edges are program-order
	if (debug()>=9) m_graph.dumpDotFilePrefixed((string)"splitg_preo", false);
	m_graph.acyclic(&SplitEdge::followCyclic);
	m_graph.rank(&SplitEdge::followCyclic);  // Or order(), but that's more expensive
	if (debug()>=9) m_graph.dumpDotFilePrefixed((string)"splitg_opt", false);
    }

    void reorderBlock(AstNode* nodep) {
	// Reorder statements in the completed graph
	AstAlways* splitAlwaysp = nodep->backp()->castAlways();

	// Map the rank numbers into nodes they associate with
	typedef multimap<uint32_t,AstNode*> RankNodeMap;
	typedef map<uint32_t,RankNodeMap> ColorRankMap;
	ColorRankMap colorRankMap;
	uint32_t firstColor = 0;  bool multiColors = false;
	int currOrder = 0;	// Existing sequence number of assignment
	for (AstNode* nextp=nodep; nextp; nextp=nextp->nextp()) {
	    SplitLogicVertex* vvertexp = (SplitLogicVertex*)nextp->user3p();
	    if (!splitAlwaysp) vvertexp->splitColor(1);  // All blocks remain as-is
	    RankNodeMap& rankMap = colorRankMap[vvertexp->splitColor()];
	    rankMap.insert(make_pair(vvertexp->rank(), nextp));
	    if (firstColor && firstColor != vvertexp->splitColor()) multiColors = true;
	    firstColor = vvertexp->splitColor();
	    nextp->user4(++currOrder);   // Record current ordering
	}
	// If there was only one color, we don't need multiple always blocks
	if (!multiColors) splitAlwaysp = NULL;

	// Is the current ordering OK?
	bool leaveAlone=true;
	if (splitAlwaysp) leaveAlone=false;
	int newOrder = 0;	// New sequence number of assignment
	for (ColorRankMap::iterator colorIt = colorRankMap.begin(); colorIt != colorRankMap.end(); ++colorIt) {
	    RankNodeMap& rankMap = colorIt->second;
	    for (RankNodeMap::iterator it = rankMap.begin(); it != rankMap.end(); ++it) {
		AstNode* nextp = it->second;
		if (++newOrder != nextp->user4()) leaveAlone=false;
	    }
	}
	if (leaveAlone) {
	    UINFO(6,"   No changes\n");
	} else {
	    AstNRelinker replaceHandle;	// Where to add the list
	    AstNode* addAfterp = splitAlwaysp;

	    for (ColorRankMap::iterator colorIt = colorRankMap.begin(); colorIt != colorRankMap.end(); ++colorIt) {
		uint32_t color = colorIt->first;
		RankNodeMap& rankMap = colorIt->second;
		AstNode* newListp = NULL;
		for (RankNodeMap::iterator it = rankMap.begin(); it != rankMap.end(); ++it) {
		    AstNode* nextp = it->second;
		    UINFO(6, "    Color="<<color<<"  New order: "<<nextp<<endl);
		    if (nextp == nodep && !splitAlwaysp) nodep->unlinkFrBack(&replaceHandle);
		    else nextp->unlinkFrBack();
		    newListp = newListp->addNext(nextp);
		}
		if (splitAlwaysp) {
		    ++m_statSplits;
		    AstAlways* alwaysp = new AstAlways(newListp->fileline(), VAlwaysKwd::ALWAYS, NULL, NULL);
		    addAfterp->addNextHere(alwaysp);  addAfterp=alwaysp;
		    alwaysp->addStmtp(newListp);
		} else {
		    // Just reordering
		    replaceHandle.relink(newListp);
		}
	    }
	    if (splitAlwaysp) {
		pushDeletep(splitAlwaysp->unlinkFrBack());
	    }
	} // leaveAlone
    }

    void processBlock(AstNode* nodep) {
	if (!nodep) return;	// Empty lists are ignorable
	// Pass the first node in a list of block items, we'll process them
	// Check there's >= 2 sub statements, else nothing to analyze
	// Save recursion state
	AstNode* firstp = nodep;   // We may reorder, and nodep is no longer first.
	void* oldBlockUser3 = nodep->user3p();   // May be overloaded in below loop, save it
	nodep->user3p(NULL);
	if (!nodep->firstAbovep()) nodep->v3fatalSrc("Node passed is in next list; should have processed all list at once");
	// Process it
	if (!nodep->nextp()) {
	    // Just one, so can't reorder.  Just look for more blocks/statements.
	    nodep->accept(*this);
	} else {
	    UINFO(9,"  processBlock "<<nodep<<endl);
	    // Process block and followers
	    scanBlock(nodep);
	    if (m_noReorderWhy != "") {  // Jump or something nasty
		UINFO(9,"  NoReorderBlock because "<<m_noReorderWhy<<endl);
	    } else {
		// Reorder statements in this block
		cleanupBlockGraph(nodep);
		reorderBlock(nodep);
		// Delete old vertexes and edges only applying to this block
		while (firstp->backp()->nextp()==firstp) firstp = firstp->backp();  // Walk back to first in list
		for (AstNode* nextp=firstp; nextp; nextp=nextp->nextp()) {
		    SplitLogicVertex* vvertexp = (SplitLogicVertex*)nextp->user3p();
		    vvertexp->unlinkDelete(&m_graph);
		}
	    }
	}
	// Again, nodep may no longer be first.
	firstp->user3p(oldBlockUser3);
    }

    // VISITORS
    virtual void visit(AstAlways* nodep, AstNUser*) {
	UINFO(4,"   ALW   "<<nodep<<endl);
	if (debug()>=9) nodep->dumpTree(cout,"   alwIn:: ");
	scoreboardClear();
	processBlock(nodep->bodysp());
	if (debug()>=9) nodep->dumpTree(cout,"   alwOut: ");
    }
    virtual void visit(AstNodeIf* nodep, AstNUser*) {
	if (!m_reorder) {
	    nodep->iterateChildren(*this);
	} else {
	    UINFO(4,"     IF "<<nodep<<endl);
	    nodep->condp()->iterateAndNext(*this);
	    processBlock(nodep->ifsp());
	    processBlock(nodep->elsesp());
	}
    }
    // We don't do AstNodeFor/AstWhile loops, due to the standard question
    // of what is before vs. after

    virtual void visit(AstAssignDly* nodep, AstNUser*) {
	m_inDly = true;
	UINFO(4,"    ASSIGNDLY "<<nodep<<endl);
	nodep->iterateChildren(*this);
	m_inDly = false;
    }
    virtual void visit(AstVarRef* nodep, AstNUser*) {
	if (!m_stmtStackps.empty()) {
	    AstVarScope* vscp = nodep->varScopep();
	    if (!vscp) nodep->v3fatalSrc("Not linked");
	    if (!nodep->varp()->isConst()) {  // Constant lookups can be ignored
		if (nodep->varp()->isSigPublic()) {
		    // Public signals shouldn't be changed, pli code might be messing with them
		    scoreboardPli();
		}

		// Create vertexes for variable
		if (!vscp->user1p()) {
		    SplitVarStdVertex*  vstdp  = new SplitVarStdVertex(&m_graph, vscp);
		    vscp->user1p(vstdp);
		}
		SplitVarStdVertex*  vstdp  = (SplitVarStdVertex*) vscp->user1p();

		// SPEEDUP: We add duplicate edges, that should be fixed
		if (m_inDly && nodep->lvalue()) {
		    UINFO(4,"     VARREFDLY: "<<nodep<<endl);
		    // Delayed variable is different from non-delayed variable
		    if (!vscp->user2p()) {
			SplitVarPostVertex* vpostp = new SplitVarPostVertex(&m_graph, vscp);
			vscp->user2p(vpostp);
			new SplitPostEdge(&m_graph, vstdp, vpostp);
		    }
		    SplitVarPostVertex* vpostp = (SplitVarPostVertex*)vscp->user2p();
		    // Add edges
		    for (VStack::iterator it = m_stmtStackps.begin(); it != m_stmtStackps.end(); ++it) {
			new SplitLVEdge(&m_graph, vpostp, *it);
		    }
		} else {  // Nondelayed assignment
		    if (nodep->lvalue()) {
			// Non-delay; need to maintain existing ordering with all consumers of the signal
			UINFO(4,"     VARREFLV: "<<nodep<<endl);
			for (VStack::iterator it = m_stmtStackps.begin(); it != m_stmtStackps.end(); ++it) {
			    new SplitLVEdge(&m_graph, vstdp, *it);
			}
		    } else {
			UINFO(4,"     VARREF:   "<<nodep<<endl);
			for (VStack::iterator it = m_stmtStackps.begin(); it != m_stmtStackps.end(); ++it) {
			    new SplitRVEdge(&m_graph, *it, vstdp);
			}
		    }
		}
	    }
	}
    }
    virtual void visit(AstJumpGo* nodep, AstNUser*) {
	// Jumps will disable reordering at all levels
	// This is overly pessimistic; we could treat jumps as barriers, and
	// reorder everything between jumps/labels, however jumps are rare
	// in always, so the performance gain probably isn't worth the work.
	UINFO(9,"         NoReordering "<<nodep<<endl);
	m_noReorderWhy = "JumpGo";
	nodep->iterateChildren(*this);
    }

    //--------------------
    // Default
    virtual void visit(AstNode* nodep, AstNUser*) {
	// **** SPECIAL default type that sets PLI_ORDERING
	if (!m_stmtStackps.empty() && !nodep->isPure()) {
	    UINFO(9,"         NotSplittable "<<nodep<<endl);
	    scoreboardPli();
	}
	nodep->iterateChildren(*this);
    }

public:
    // CONSTUCTORS
    SplitVisitor(AstNetlist* nodep, bool reorder)
	: m_reorder(reorder) {
	scoreboardClear();
	nodep->accept(*this);
    }
    virtual ~SplitVisitor() {
	V3Stats::addStat("Optimizations, Split always", m_statSplits);
    }
};

//######################################################################
// Split class functions

void V3Split::splitReorderAll(AstNetlist* nodep) {
    UINFO(2,__FUNCTION__<<": "<<endl);
    SplitVisitor visitor (nodep, true);
    V3Global::dumpCheckGlobalTree("reorder.tree", 0, v3Global.opt.dumpTreeLevel(__FILE__) >= 3);
}
void V3Split::splitAlwaysAll(AstNetlist* nodep) {
    UINFO(2,__FUNCTION__<<": "<<endl);
    SplitVisitor visitor (nodep, false);
    V3Global::dumpCheckGlobalTree("split.tree", 0, v3Global.opt.dumpTreeLevel(__FILE__) >= 6);
}
