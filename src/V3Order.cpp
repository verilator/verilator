// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Block code ordering
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
// V3Order's Transformations:
//
//  Compute near optimal scheduling of always/wire statements
//  Make a graph of the entire netlist
//
//	Add master "*INPUTS*" vertex.
//	For inputs on top level
//	    Add vertex for each input var.
//		Add edge INPUTS->var_vertex
//
//	For seq logic
//	    Add logic_sensitive_vertex for this list of SenItems
//		Add edge for each sensitive_var->logic_sensitive_vertex
//	    For AssignPre's
//		Add vertex for this logic
//		    Add edge logic_sensitive_vertex->logic_vertex
//		    Add edge logic_consumed_var_PREVAR->logic_vertex
//		    Add edge logic_vertex->logic_generated_var (same as if comb)
//		    Add edge logic_vertex->generated_var_PREORDER
//			Cutable dependency to attempt to order dlyed
//			assignments to avoid saving state, thus we prefer
//				a <= b ...      As the opposite order would
//				b <= c ...	require the old value of b.
//	    For	Logic
//		Add vertex for this logic
//		    Add edge logic_sensitive_vertex->logic_vertex
//		    Add edge logic_generated_var_PREORDER->logic_vertex
//			This insures the AssignPre gets scheduled before this logic
//		    Add edge logic_vertex->consumed_var_PREVAR
//		    Add edge logic_vertex->consumed_var_POSTVAR
//		    Add edge logic_vertex->logic_generated_var (same as if comb)
//	    For AssignPost's
//		Add vertex for this logic
//		    Add edge logic_sensitive_vertex->logic_vertex
//		    Add edge logic_consumed_var->logic_vertex (same as if comb)
//		    Add edge logic_vertex->logic_generated_var (same as if comb)
//
//	For comb logic
//	    For comb logic
//		Add vertex for this logic
//		Add edge logic_consumed_var->logic_vertex
//		Add edge logic_vertex->logic_generated_var
//		    Mark it cutable, as circular logic may require
//		    the generated signal to become a primary input again.
//
//
//
//   Rank the graph starting at INPUTS (see V3Graph)
//
//   Visit the graph's logic vertices in ranked order
//	For all logic vertices with all inputs already ordered
//	   Make ordered block for this module
//	   For all ^^ in same domain
//		Move logic to ordered activation
//	When we have no more choices, we move to the next module
//	and make a new block.  Add that new activation block to the list of calls to make.
//
//*************************************************************************

#include "config_build.h"
#include "verilatedos.h"
#include <cstdio>
#include <cstdarg>
#include <unistd.h>
#include <algorithm>
#include <vector>
#include <deque>
#include <map>
#include <iomanip>
#include <sstream>
#include <memory>

#include "V3Global.h"
#include "V3File.h"
#include "V3Ast.h"
#include "V3Graph.h"
#include "V3List.h"
#include "V3SenTree.h"
#include "V3Stats.h"
#include "V3EmitCBase.h"
#include "V3Const.h"

#include "V3Order.h"
#include "V3OrderGraph.h"
#include "V3EmitV.h"

class OrderMoveDomScope;

//######################################################################
// Functions for above graph classes

void OrderGraph::loopsVertexCb(V3GraphVertex* vertexp) {
    if (debug()) cout<<"-Info-Loop: "<<vertexp<<" "<<endl;
    if (OrderLogicVertex* vvertexp = dynamic_cast<OrderLogicVertex*>(vertexp)) {
	cerr<<V3Error::msgPrefix()<<"     Example path: "<<vvertexp->nodep()->fileline()<<" "<<vvertexp->nodep()->typeName()<<endl;
    }
    if (OrderVarVertex* vvertexp = dynamic_cast<OrderVarVertex*>(vertexp)) {
	cerr<<V3Error::msgPrefix()<<"     Example path: "<<vvertexp->varScp()->fileline()<<" "<<vvertexp->varScp()->prettyName()<<endl;
    }
};

//######################################################################

class OrderMoveDomScope {
    // Information stored for each unique loop, domain & scope trifecta
public:
    V3ListEnt<OrderMoveDomScope*>	m_readyDomScopeE;// List of next ready dom scope
    V3List<OrderMoveVertex*>	m_readyVertices;	// Ready vertices with same domain & scope
private:
    bool			m_onReadyList;		// True if DomScope is already on list of ready dom/scopes
    AstSenTree*			m_domainp;		// Domain all vertices belong to
    AstScope*			m_scopep;		// Scope all vertices belong to
    OrderLoopId			m_inLoop;		// Loop member of

    typedef pair<pair<OrderLoopId, AstSenTree*>, AstScope*> DomScopeKey;
    typedef std::map<DomScopeKey, OrderMoveDomScope*> DomScopeMap;
    static DomScopeMap	s_dsMap;	// Structure registered for each dom/scope pairing

public:
    OrderMoveDomScope(OrderLoopId inLoop, AstSenTree* domainp, AstScope* scopep)
	: m_onReadyList(false), m_domainp(domainp), m_scopep(scopep), m_inLoop(inLoop) {}
    OrderMoveDomScope* readyDomScopeNextp() const { return m_readyDomScopeE.nextp(); }
    OrderLoopId inLoop() const { return m_inLoop; }
    AstSenTree* domainp() const { return m_domainp; }
    AstScope*   scopep() const { return m_scopep; }
    void ready(OrderVisitor* ovp);	// Check the domScope is on ready list, add if not
    void movedVertex(OrderVisitor* ovp, OrderMoveVertex* vertexp);	// Mark one vertex as finished, remove from ready list if done
    // STATIC MEMBERS (for lookup)
    static void clear() {
	for (DomScopeMap::iterator it=s_dsMap.begin(); it!=s_dsMap.end(); ++it) {
	    delete it->second;
	}
	s_dsMap.clear();
    }
    V3List<OrderMoveVertex*>& readyVertices() { return m_readyVertices; }
    static OrderMoveDomScope* findCreate (OrderLoopId inLoop, AstSenTree* domainp, AstScope* scopep) {
	const DomScopeKey key = make_pair(make_pair(inLoop,domainp),scopep);
	DomScopeMap::iterator iter = s_dsMap.find(key);
	if (iter != s_dsMap.end()) {
	    return iter->second;
	} else {
	    OrderMoveDomScope* domScopep = new OrderMoveDomScope(inLoop, domainp, scopep);
	    s_dsMap.insert(make_pair(key, domScopep));
	    return domScopep;
	}
    }
    string name() const {
	return (string("MDS:")
		+" lp="+cvtToStr(inLoop())
		+" d="+cvtToStr((void*)domainp())
		+" s="+cvtToStr((void*)scopep()));
    }
};

OrderMoveDomScope::DomScopeMap	OrderMoveDomScope::s_dsMap;

inline ostream& operator<< (ostream& lhs, const OrderMoveDomScope& rhs) {
    lhs<<rhs.name();
    return lhs;
}

//######################################################################
// Order information stored under each AstNode::user1p()...

// Types of vertex we can create
enum WhichVertex { WV_STD, WV_PRE, WV_PORD, WV_POST, WV_SETL,
		   WV_MAX};

class OrderUser {
    // Stored in AstVarScope::user1p, a list of all the various vertices
    // that can exist for one given variable
private:
    OrderVarVertex*	m_vertexp[WV_MAX];	// Vertex of each type (if non NULL)
public:
    // METHODS
    OrderVarVertex* newVarUserVertex(V3Graph* graphp, AstScope* scopep,
				     AstVarScope* varscp, WhichVertex type, bool* createdp=NULL) {
	if (type>=WV_MAX) varscp->v3fatalSrc("Bad Case\n");
	OrderVarVertex* vertexp = m_vertexp[type];
	if (!vertexp) {
	    UINFO(6,"New vertex "<<varscp<<endl);
	    if (createdp) *createdp=true;
	    switch (type) {
	    case WV_STD:  vertexp = new OrderVarStdVertex   (graphp, scopep, varscp); break;
	    case WV_PRE:  vertexp = new OrderVarPreVertex   (graphp, scopep, varscp); break;
	    case WV_PORD: vertexp = new OrderVarPordVertex  (graphp, scopep, varscp); break;
	    case WV_POST: vertexp = new OrderVarPostVertex  (graphp, scopep, varscp); break;
	    case WV_SETL: vertexp = new OrderVarSettleVertex(graphp, scopep, varscp); break;
	    default: varscp->v3fatalSrc("Bad Case\n");
	    }
	    m_vertexp[type] = vertexp;
	} else {
	    if (createdp) *createdp=false;
	}
	return vertexp;
    }

public:
    // CONSTRUCTORS
    OrderUser() {
	for (int i=0; i<WV_MAX; i++) m_vertexp[i]=NULL;
    }
    ~OrderUser() {}
};


//######################################################################
// Comparator classes

//! Comparator for width of associated variable
struct OrderVarWidthCmp {
    bool operator() (OrderVarStdVertex* vsv1p, OrderVarStdVertex* vsv2p) {
	return vsv1p->varScp()->varp()->width()
	    > vsv2p->varScp()->varp()->width();
    }
};

//! Comparator for fanout of vertex
struct OrderVarFanoutCmp {
    bool operator() (OrderVarStdVertex* vsv1p, OrderVarStdVertex* vsv2p) {
	return vsv1p->fanout() > vsv2p->fanout();
    }
};

//######################################################################
// The class is used for propagating the clocker attribute for further 
// avoiding marking clock signals as circular.
// Transformation:
//    while (newClockerMarked)
//        check all assignments
//            if RHS is marked as clocker:
//                mark LHS as clocker as well.
//                newClockerMarked = true;
//
// In addition it also check whether clock and data signals are mixed, and 
// produce a CLKDATA warning if so.
//
class OrderClkMarkVisitor : public AstNVisitor {
private:
    bool m_hasClk;		// flag indicating whether there is clock signal on rhs
    bool m_inClocked;		// Currently inside a sequential block
    bool m_newClkMarked;	// Flag for deciding whether a new run is needed
    bool m_inAss;		// Currently inside of a assignment
    int	 m_childClkWidth;	// If in hasClk, width of clock signal in child
    int  m_rightClkWidth;	// Clk width on the RHS

    // METHODS
    static int debug() {
	static int level = -1;
	if (VL_UNLIKELY(level < 0)) level = v3Global.opt.debugSrcLevel(__FILE__);
	return level;
    }

    virtual void visit(AstNodeAssign* nodep, AstNUser*) {
	m_hasClk = false;
	if (AstVarRef* varrefp = nodep->rhsp()->castVarRef()) {
	    this->visit(varrefp, NULL);
	    m_rightClkWidth = varrefp->width();
	    if (varrefp->varp()->attrClocker() == AstVarAttrClocker::CLOCKER_YES) {
		if (m_inClocked) {
		    varrefp->v3warn(CLKDATA, "Clock used as data (on rhs of assignment) in sequential block "<<varrefp<<endl);
		} else {
		    m_hasClk = true;
		    UINFO(5, "node is already marked as clocker "<<varrefp<<endl);
		}
	    }
	} else {
	    m_inAss = true;
	    m_childClkWidth = 0;
	    nodep->rhsp()->iterateAndNext(*this);
	    m_rightClkWidth = m_childClkWidth;
	    m_inAss = false;
	}

	// do the marking
	if (m_hasClk) {
	    if (nodep->lhsp()->width() > m_rightClkWidth) {
		nodep->v3warn(CLKDATA, "Clock is assigned to part of data signal "<< nodep->lhsp()<<endl);
		UINFO(4, "CLKDATA: lhs with width " << nodep->lhsp()->width() <<endl);
		UINFO(4, "     but rhs clock with width " << m_rightClkWidth <<endl);
		return; // skip the marking
	    }

	    AstVarRef* lhsp = nodep->lhsp()->castVarRef();
	    if (lhsp && (lhsp->varp()->attrClocker() == AstVarAttrClocker::CLOCKER_UNKNOWN)) {
		lhsp->varp()->attrClocker(AstVarAttrClocker::CLOCKER_YES); // mark as clocker
		m_newClkMarked = true; // enable a further run since new clocker is marked
		UINFO(5, "node is newly marked as clocker by assignment "<<lhsp<<endl);
	    }
	}
    }

    virtual void visit(AstVarRef* nodep, AstNUser*) {
	if (m_inAss && nodep->varp()->attrClocker() == AstVarAttrClocker::CLOCKER_YES) {
	    if (m_inClocked) {
		nodep->v3warn(CLKDATA, "Clock used as data (on rhs of assignment) in sequential block "<<nodep->prettyName());
	    } else {
		m_hasClk = true;
		m_childClkWidth = nodep->width();  // Pass up
		UINFO(5, "node is already marked as clocker "<<nodep<<endl);
	    }
	}
    }
    virtual void visit(AstConcat* nodep, AstNUser* wp) {
	if (m_inAss) {
	    nodep->lhsp()->iterateAndNext(*this);
	    int lw = m_childClkWidth;
	    nodep->rhsp()->iterateAndNext(*this);
	    int rw = m_childClkWidth;
	    m_childClkWidth = lw + rw;  // Pass up
	}
    }
    virtual void visit(AstNodeSel* nodep, AstNUser* wp) {
	if (m_inAss) {
	    nodep->iterateChildren(*this);
	    // Pass up result width
	    if (m_childClkWidth > nodep->width()) m_childClkWidth = nodep->width();
	}
    }
    virtual void visit(AstSel* nodep, AstNUser*) {
	if (m_inAss) {
	    nodep->iterateChildren(*this);
	    if (m_childClkWidth > nodep->width()) m_childClkWidth = nodep->width();
	}
    }
    virtual void visit(AstReplicate* nodep, AstNUser*) {
	if (m_inAss) {
	    nodep->iterateChildren(*this);
	    if (nodep->rhsp()->castConst()) {
		m_childClkWidth = m_childClkWidth * nodep->rhsp()->castConst()->toUInt();
	    } else {
		m_childClkWidth = nodep->width(); // can not check in this case.
	    }
	}
    }
    virtual void visit(AstActive* nodep, AstNUser*) {
	m_inClocked = nodep->hasClocked();
	nodep->iterateChildren(*this);
	m_inClocked = false;
    }
    virtual void visit(AstNode* nodep, AstNUser*) {
	nodep->iterateChildren(*this);
    }

public:
    // CONSTUCTORS
    OrderClkMarkVisitor(AstNode* nodep) {
	m_hasClk    = false;
	m_inClocked = false;
	m_inAss     = false;
	m_childClkWidth = 0;
	m_rightClkWidth = 0;
	do {
	    m_newClkMarked = false;
	    nodep->accept(*this);
	} while (m_newClkMarked);
    }
    virtual ~OrderClkMarkVisitor() {}
};


//######################################################################
// The class used to check if the assignment has clocker inside.
class OrderClkAssVisitor : public AstNVisitor {
private:
    bool m_clkAss; 	// There is signals marked as clocker in the assignment

    // METHODS
    static int debug() {
	static int level = -1;
	if (VL_UNLIKELY(level < 0)) level = v3Global.opt.debugSrcLevel(__FILE__);
	return level;
    }
    virtual void visit(AstNodeAssign* nodep, AstNUser*) {
	if (AstVarRef* varrefp = nodep->lhsp()->castVarRef() )
	    if (varrefp->varp()->attrClocker() == AstVarAttrClocker::CLOCKER_YES) {
		m_clkAss = true;
		UINFO(6, "node was marked as clocker "<<varrefp<<endl);
	    }
	nodep->rhsp()->iterateChildren(*this);
    }
    virtual void visit(AstVarRef* nodep, AstNUser*) {
	if (nodep->varp()->attrClocker() == AstVarAttrClocker::CLOCKER_YES) {
	    m_clkAss = true;
	    UINFO(6, "node was marked as clocker "<<nodep<<endl);
	}
    }
    virtual void visit(AstNode* nodep, AstNUser*) {
	nodep->iterateChildren(*this);
    }

public:
    // CONSTUCTORS
    OrderClkAssVisitor(AstNode* nodep) {
	m_clkAss = false;
	nodep->accept(*this);
    }
    virtual ~OrderClkAssVisitor() {}

    // METHODS
    bool isClkAss() {return m_clkAss;}
};


//######################################################################
// Order class functions

class OrderVisitor : public AstNVisitor {
private:
    // NODE STATE
    // Forming graph:
    //   Entire Netlist:
    //    AstVarScope::user1p	-> OrderUser* for usage var
    //    {statement}Node::user1p-> AstModule* statement is under
    //   USER4 Cleared on each Logic stmt
    //    AstVarScope::user4()	-> VarUsage(gen/con/both).	Where already encountered signal
    // Ordering (user3/4/5 cleared between forming and ordering)
    //	  AstScope::user1p()	-> AstNodeModule*. Module this scope is under
    //    AstNodeModule::user3()    -> Number of routines created
    //  Each call to V3Const::constify
    //   AstNode::user4()		Used by V3Const::constify, called below
    AstUser1InUse	m_inuser1;
    AstUser2InUse	m_inuser2;
    AstUser3InUse	m_inuser3;
    //AstUser4InUse	m_inuser4;	// Used only when building tree, so below

    // STATE
    OrderGraph		m_graph;	// Scoreboard of var usages/dependencies
    SenTreeFinder	m_finder;	// Find global sentree's and add them
    AstSenTree*		m_comboDomainp;	// Combo activation tree
    AstSenTree*		m_deleteDomainp;// Delete this from tree
    AstSenTree*		m_settleDomainp;// Initial activation tree
    OrderInputsVertex*	m_inputsVxp;	// Top level vertex all inputs point from
    OrderSettleVertex*	m_settleVxp;	// Top level vertex all settlement vertexes point from
    OrderLogicVertex*	m_logicVxp;	// Current statement being tracked, NULL=ignored
    AstTopScope*	m_topScopep;	// Current top scope being processed
    AstScope*		m_scopetopp;	// Scope under TOPSCOPE
    AstNodeModule*	m_modp;		// Current module
    AstScope*		m_scopep;	// Current scope being processed
    AstActive*		m_activep;	// Current activation block
    bool		m_inSenTree;	// Underneath AstSenItem; any varrefs are clocks
    bool		m_inClocked;	// Underneath clocked block
    bool		m_inClkAss;	// Underneath AstAssign
    bool		m_inPre;	// Underneath AstAssignPre
    bool		m_inPost;	// Underneath AstAssignPost
    OrderLogicVertex*	m_activeSenVxp;	// Sensitivity vertex
    deque<OrderUser*>	m_orderUserps;	// All created OrderUser's for later deletion.
    // STATE... for inside process
    OrderLoopId			m_loopIdMax;	// Maximum BeginLoop id number assigned
    vector<OrderLoopEndVertex*> m_pmlLoopEndps;	// processInsLoop: End vertex for each color
    vector<OrderLoopBeginVertex*> m_pomLoopMoveps;// processMoveLoop: Loops next nodes are under
    AstCFunc*			m_pomNewFuncp;	// Current function being created
    int				m_pomNewStmts;	// Statements in function being created
    V3Graph			m_pomGraph;	// Graph of logic elements to move
    V3List<OrderMoveVertex*>	m_pomWaiting;	// List of nodes needing inputs to become ready
protected:
    friend class OrderMoveDomScope;
    V3List<OrderMoveDomScope*>  m_pomReadyDomScope;	// List of ready domain/scope pairs, by loopId
    vector<OrderVarStdVertex*>	m_unoptflatVars;	// Vector of variables in UNOPTFLAT loop

private:
    // STATS
    V3Double0		m_statCut[OrderVEdgeType::_ENUM_END];	// Count of each edge type cut

    // TYPES
    enum VarUsage { VU_NONE=0, VU_CON=1, VU_GEN=2 };

    // METHODS
    static int debug() {
	static int level = -1;
	if (VL_UNLIKELY(level < 0)) level = v3Global.opt.debugSrcLevel(__FILE__);
	return level;
    }

    void iterateNewStmt(AstNode* nodep) {
	if (m_scopep) {
	    UINFO(4,"   STMT "<<nodep<<endl);
	    //VV*****  We reset user4p()
	    AstNode::user4ClearTree();
	    if (!m_activep || !m_activep->sensesp()) nodep->v3fatalSrc("NULL");
	    // If inside combo logic, ignore the domain, we'll assign one based on interconnect
	    AstSenTree* startDomainp = m_activep->sensesp();
	    if (startDomainp->hasCombo()) startDomainp=NULL;
	    m_logicVxp = new OrderLogicVertex(&m_graph, m_scopep, startDomainp, nodep);
	    if (m_activeSenVxp) {
		// If in a clocked activation, add a link from the sensitivity to this block
		// Add edge logic_sensitive_vertex->logic_vertex
		new OrderEdge(&m_graph, m_activeSenVxp, m_logicVxp, WEIGHT_NORMAL);
	    }
	    nodep->user1p(m_modp);
	    nodep->iterateChildren(*this);
	    m_logicVxp = NULL;
	}
    }

    OrderVarVertex* newVarUserVertex(AstVarScope* varscp, WhichVertex type, bool* createdp=NULL) {
	if (!varscp->user1p()) {
	    OrderUser* newup = new OrderUser();
	    m_orderUserps.push_back(newup);
	    varscp->user1p(newup);
	}
	OrderUser* up = (OrderUser*)(varscp->user1p());
	OrderVarVertex* varVxp = up->newVarUserVertex(&m_graph, m_scopep, varscp, type, createdp);
	return varVxp;
    }

    V3GraphEdge* findEndEdge(V3GraphVertex* vertexp, AstNode* errnodep, OrderLoopEndVertex*& evertexpr) {
	// Given a vertex, find the end block corresponding to it
	// Every vertex should have a pointer to the end block (one hopes)
	for (V3GraphEdge* edgep = vertexp->outBeginp(); edgep; edgep = edgep->outNextp()) {
	    if (OrderLoopEndVertex* evertexp = dynamic_cast<OrderLoopEndVertex*>(edgep->top())) {
		evertexpr = evertexp;
		return edgep;
	    }
	}
	errnodep->v3fatalSrc("Loop-broken vertex doesn't have pointer to LoopEndVertex: "<<vertexp);
	return NULL;
    }

    bool isClkAssign(AstNodeAssign* nodep) {
	if (AstVarRef* varrefp = nodep->lhsp()->castVarRef()) {
	    if (varrefp->varp()->attrClocker() == AstVarAttrClocker::CLOCKER_YES) {
		return true;
	    }
	}
	return false;
    }

    void process();
    void processCircular();
    typedef deque<OrderEitherVertex*> VertexVec;
    void processInputs();
    void processInputsInIterate(OrderEitherVertex* vertexp, VertexVec& todoVec);
    void processInputsOutIterate(OrderEitherVertex* vertexp, VertexVec& todoVec);
    void processSensitive();
    void processDomains();
    void processDomainsIterate(OrderEitherVertex* vertexp);
    void processEdgeReport();

    void processMove();
    void processMoveClear();
    void processMoveBuildGraph();
    void processMoveBuildGraphIterate (OrderMoveVertex* moveVxp, V3GraphVertex* vertexp, int weightmin);
    void processMovePrepScopes();
    void processMovePrepReady();
    void processMoveReadyOne(OrderMoveVertex* vertexp);
    void processMoveDoneOne(OrderMoveVertex* vertexp);
    void processMoveOne(OrderMoveVertex* vertexp, OrderMoveDomScope* domScopep, int level);
    void processMoveLoopPush(OrderLoopBeginVertex* beginp);
    void processMoveLoopPop(OrderLoopBeginVertex* beginp);
    void processMoveLoopStmt(AstNode* newSubnodep);
    OrderLoopId processMoveLoopCurrent();

    string cfuncName(AstNodeModule* modp, AstSenTree* domainp, AstScope* scopep, AstNode* forWhatp) {
	modp->user3Inc();
	int funcnum = modp->user3();
	string name = (domainp->hasCombo() ? "_combo"
		       : (domainp->hasInitial() ? "_initial"
			  : (domainp->hasSettle() ? "_settle"
			     : (domainp->isMulti() ? "_multiclk" : "_sequent"))));
	name = name+"__"+scopep->nameDotless()+"__"+cvtToStr(funcnum);
	if (v3Global.opt.profileCFuncs()) {
	    name += "__PROF__"+forWhatp->fileline()->profileFuncname();
	}
	return name;
    }

    void nodeMarkCircular(OrderVarVertex* vertexp, OrderEdge* edgep) {
	AstVarScope* nodep = vertexp->varScp();
	OrderLogicVertex* fromLVtxp = NULL;
	OrderLogicVertex* toLVtxp = NULL;
	if (edgep) {
	    fromLVtxp = dynamic_cast<OrderLogicVertex*>(edgep->fromp());
	    toLVtxp = dynamic_cast<OrderLogicVertex*>(edgep->top());
	}
	//
	if ((fromLVtxp && fromLVtxp->nodep()->castInitial())
	    || (toLVtxp && toLVtxp->nodep()->castInitial())) {
	    // IEEE does not specify ordering between initial blocks, so we can do whatever we want
	    // We especially do not want to evaluate multiple times, so do not mark the edge circular
	}
	else {
	    nodep->circular(true);
	    ++m_statCut[vertexp->type()];
	    if (edgep) ++m_statCut[edgep->type()];
	    //
	    if (vertexp->isClock()) {
		// Seems obvious; no warning yet
		//nodep->v3warn(GENCLK,"Signal unoptimizable: Generated clock: "<<nodep->prettyName());
	    } else if (nodep->varp()->isSigPublic()) {
		nodep->v3warn(UNOPT,"Signal unoptimizable: Feedback to public clock or circular logic: "<<nodep->prettyName());
		if (!nodep->fileline()->warnIsOff(V3ErrorCode::UNOPT)) {
		    nodep->fileline()->modifyWarnOff(V3ErrorCode::UNOPT, true);  // Complain just once
		    // Give the user an example.
		    bool tempWeight = (edgep && edgep->weight()==0);
		    if (tempWeight) edgep->weight(1);  // Else the below loop detect can't see the loop
		    m_graph.reportLoops(&OrderEdge::followComboConnected, vertexp); // calls OrderGraph::loopsVertexCb
		    if (tempWeight) edgep->weight(0);
		}
	    } else {
		// We don't use UNOPT, as there are lots of V2 places where it was needed, that aren't any more
		// First v3warn not inside warnIsOff so we can see the suppressions with --debug
		nodep->v3warn(UNOPTFLAT,"Signal unoptimizable: Feedback to clock or circular logic: "<<nodep->prettyName());
		if (!nodep->fileline()->warnIsOff(V3ErrorCode::UNOPTFLAT)) {
		    nodep->fileline()->modifyWarnOff(V3ErrorCode::UNOPTFLAT, true);  // Complain just once
		    // Give the user an example.
		    bool tempWeight = (edgep && edgep->weight()==0);
		    if (tempWeight) edgep->weight(1);  // Else the below loop detect can't see the loop
		    m_graph.reportLoops(&OrderEdge::followComboConnected, vertexp); // calls OrderGraph::loopsVertexCb
		    if (tempWeight) edgep->weight(0);
		    if (v3Global.opt.reportUnoptflat()) {
			// Report candidate variables for splitting
			reportLoopVars(vertexp);
			// Do a subgraph for the UNOPTFLAT loop
			OrderGraph loopGraph;
			m_graph.subtreeLoops(&OrderEdge::followComboConnected,
					     vertexp, &loopGraph);
			loopGraph.dumpDotFilePrefixedAlways("unoptflat");
		    }
		}
	    }
	}
    }

    //! Find all variables in an UNOPTFLAT loop
    //!
    //! Ignore vars that are 1-bit wide and don't worry about generated
    //! variables (PRE and POST vars, __Vdly__, __Vcellin__ and __VCellout).
    //! What remains are candidates for splitting to break loops.
    //!
    //! node->user3 is used to mark if we have done a particular variable.
    //! vertex->user is used to mark if we have seen this vertex before.
    //!
    //! @todo We could be cleverer in the future and consider just
    //!       the width that is generated/consumed.
    void reportLoopVars(OrderVarVertex* vertexp) {
	m_graph.userClearVertices();
	AstNode::user3ClearTree();
	m_unoptflatVars.clear();
	reportLoopVarsIterate (vertexp, vertexp->color());
	AstNode::user3ClearTree();
	m_graph.userClearVertices();
	// May be very large vector, so only report the "most important"
	// elements. Up to 10 of the widest
	cerr<<V3Error::msgPrefix()
	    <<"     Widest candidate vars to split:"<<endl;
	std::stable_sort (m_unoptflatVars.begin(), m_unoptflatVars.end(), OrderVarWidthCmp());
	int lim = m_unoptflatVars.size() < 10 ? m_unoptflatVars.size() : 10;
	for (int i = 0; i < lim; i++) {
	    OrderVarStdVertex* vsvertexp = m_unoptflatVars[i];
	    AstVar* varp = vsvertexp->varScp()->varp();
	    cerr<<V3Error::msgPrefix()<<"          "
		<<varp->fileline()<<" "<<varp->prettyName()<<dec
		<<", width "<<varp->width()<<", fanout "
		<<vsvertexp->fanout()<<endl;
	}
	// Up to 10 of the most fanned out
	cerr<<V3Error::msgPrefix()
	    <<"     Most fanned out candidate vars to split:"<<endl;
	std::stable_sort (m_unoptflatVars.begin(), m_unoptflatVars.end(),
			  OrderVarFanoutCmp());
	lim = m_unoptflatVars.size() < 10 ? m_unoptflatVars.size() : 10;
	for (int i = 0; i < lim; i++) {
	    OrderVarStdVertex* vsvertexp = m_unoptflatVars[i];
	    AstVar* varp = vsvertexp->varScp()->varp();
	    cerr<<V3Error::msgPrefix()<<"          "
		<<varp->fileline()<<" "<<varp->prettyName()
		<<", width "<<dec<<varp->width()
		<<", fanout "<<vsvertexp->fanout()<<endl;
	}
	m_unoptflatVars.clear();
    }

    void reportLoopVarsIterate(V3GraphVertex* vertexp, uint32_t color) {
	if (vertexp->user()) return; // Already done
	vertexp->user(1);
	if (OrderVarStdVertex* vsvertexp = dynamic_cast<OrderVarStdVertex*>(vertexp)) {
	    // Only reporting on standard variable vertices
	    AstVar* varp = vsvertexp->varScp()->varp();
	    if (!varp->user3()) {
		string name = varp->prettyName();
		if ((varp->width() != 1)
		    && (name.find("__Vdly") == string::npos)
		    && (name.find("__Vcell") == string::npos)) {
		    // Variable to report on and not yet done
		    m_unoptflatVars.push_back(vsvertexp);
		}
		varp->user3Inc();
	    }
	}
	// Iterate through all the to and from vertices of the same color
	for (V3GraphEdge* edgep = vertexp->outBeginp(); edgep;
	     edgep = edgep->outNextp()) {
	    if (edgep->top()->color() == color) {
		reportLoopVarsIterate(edgep->top(), color);
	    }
	}
	for (V3GraphEdge* edgep = vertexp->inBeginp(); edgep;
	     edgep = edgep->inNextp()) {
	    if (edgep->fromp()->color() == color) {
		reportLoopVarsIterate(edgep->fromp(), color);
	    }
	}
    }
    // VISITORS
    virtual void visit(AstNetlist* nodep, AstNUser*) {
	{
	    AstUser4InUse	m_inuser4;	// Used only when building tree, so below
	    nodep->iterateChildren(*this);
	}
	// We're finished, complete the topscopes
	if (m_topScopep) { process(); m_topScopep=NULL; }
    }
    virtual void visit(AstTopScope* nodep, AstNUser*) {
	// Process the last thing we're finishing
	if (m_topScopep) nodep->v3fatalSrc("Only one topscope should ever be created");
	UINFO(2,"  Loading tree...\n");
	//VV*****  We reset userp()
	AstNode::user1ClearTree();
	AstNode::user3ClearTree();
	m_graph.clear();
	m_activep = NULL;
	m_topScopep = nodep;
	m_scopetopp = nodep->scopep();
	// Find sentree's
	m_finder.main(m_topScopep);
	// ProcessDomainsIterate will use these when it needs to move
	// something to a combodomain.  This saves a ton of find() operations.
	AstSenTree* combp = new AstSenTree (nodep->fileline(),	// Gets cloned() so ok if goes out of scope
					    new AstSenItem(nodep->fileline(), AstSenItem::Combo()));
	m_comboDomainp = m_finder.getSenTree(nodep->fileline(), combp);
	pushDeletep(combp);  // Cleanup when done
	AstSenTree* settlep = new AstSenTree (nodep->fileline(),  // Gets cloned() so ok if goes out of scope
					      new AstSenItem(nodep->fileline(), AstSenItem::Settle()));
	m_settleDomainp = m_finder.getSenTree(nodep->fileline(), settlep);
	pushDeletep(settlep);  // Cleanup when done
	// Fake AstSenTree we set domainp to indicate needs deletion
	m_deleteDomainp = new AstSenTree (nodep->fileline(),
					  new AstSenItem(nodep->fileline(), AstSenItem::Settle()));
	pushDeletep(m_deleteDomainp);  // Cleanup when done
	UINFO(5,"    DeleteDomain = "<<m_deleteDomainp<<endl);
	// Base vertices
	m_activeSenVxp = NULL;
	m_inputsVxp = new OrderInputsVertex(&m_graph, NULL);
	//
	nodep->iterateChildren(*this);
	// Done topscope, erase extra user information
	// user1p passed to next process() operation
	AstNode::user3ClearTree();
	AstNode::user4ClearTree();
    }
    virtual void visit(AstNodeModule* nodep, AstNUser*) {
	m_modp = nodep;
	nodep->iterateChildren(*this);
	m_modp = NULL;
    }
    virtual void visit(AstScope* nodep, AstNUser*) {
	UINFO(4," SCOPE "<<nodep<<endl);
	m_scopep = nodep;
	m_logicVxp = NULL;
	m_activeSenVxp = NULL;
	nodep->user1p(m_modp);
	// Iterate
	nodep->iterateChildren(*this);
	m_scopep = NULL;
    }
    virtual void visit(AstActive* nodep, AstNUser*) {
	// Create required activation blocks and add to module
	UINFO(4,"  ACTIVE  "<<nodep<<endl);
	m_activep = nodep;
	m_activeSenVxp = NULL;
	m_inClocked = nodep->hasClocked();
	// Grab the sensitivity list
	if (nodep->sensesStorep()) nodep->v3fatalSrc("Senses should have been activeTop'ed to be global!");
	nodep->sensesp()->accept(*this);
	// Collect statements under it
	nodep->iterateChildren(*this);
	m_activep = NULL;
    }
    virtual void visit(AstVarScope* nodep, AstNUser*) {
	// Create links to all input signals
	if (m_modp->isTop() && nodep->varp()->isInput()) {
	    OrderVarVertex* varVxp = newVarUserVertex(nodep, WV_STD);
	    new OrderEdge(&m_graph, m_inputsVxp, varVxp, WEIGHT_INPUT);
	}
    }
    virtual void visit(AstNodeVarRef* nodep, AstNUser*) {
	if (m_scopep) {
	    AstVarScope* varscp = nodep->varScopep();
	    if (!varscp) nodep->v3fatalSrc("Var didn't get varscoped in V3Scope.cpp\n");
	    if (m_inSenTree) {
		// Add CLOCK dependency... This is a root of the tree we'll trace
		if (nodep->lvalue()) nodep->v3fatalSrc("How can a sensitivity be setting a var?\n");
		OrderVarVertex* varVxp = newVarUserVertex(varscp, WV_STD);
		varVxp->isClock(true);
		new OrderEdge(&m_graph, varVxp, m_activeSenVxp, WEIGHT_MEDIUM);
	    } else {
		if (!m_logicVxp) nodep->v3fatalSrc("Var ref not under a logic block\n");
		// What new directions is this used
		// We don't want to add extra edges if the logic block has many usages of same var
		bool gen = false;
		bool con = false;
		if (nodep->lvalue()) {
		    gen = !(varscp->user4() & VU_GEN);
		} else {
		    con = !(varscp->user4() & VU_CON);
		    if ((varscp->user4() & VU_GEN) && !m_inClocked) {
			// Dangerous assumption:
			// If a variable is used in the same activation which defines it first,
			// consider it something like:
			//		foo = 1
			//		foo = foo + 1
			// and still optimize.  This is the rule verilog-mode assumes for /*AS*/
			// Note this will break though:
			//		if (sometimes) foo = 1
			//		foo = foo + 1
			con = false;
		    }
		    if (varscp->varp()->attrClockEn() && !m_inPre && !m_inPost && !m_inClocked) {
			// clock_enable attribute: user's worring about it for us
			con = false;
		    }
		    if (m_inClkAss && (varscp->varp()->attrClocker()) != AstVarAttrClocker::CLOCKER_YES) {
			con = false;
			UINFO(4, "nodep used as clock_enable "<<varscp<<" in "<<m_logicVxp->nodep()<<endl);
		    }
		}
		if (gen) varscp->user4(varscp->user4() | VU_GEN);
		if (con) varscp->user4(varscp->user4() | VU_CON);
		// Add edges
		if (!m_inClocked
		    || m_inPost
		    ) {
		    // Combo logic
		    { // not settle and (combo or inPost)
			if (gen) {
			    // Add edge logic_vertex->logic_generated_var
			    OrderVarVertex* varVxp = newVarUserVertex(varscp, WV_STD);
			    if (m_inPost) {
				new OrderPostCutEdge(&m_graph, m_logicVxp, varVxp);
				// Mark the vertex. Used to control marking
				// internal clocks circular, which must only
				// happen if they are generated by delayed
				// assignment.
				UINFO(5, "     Found delayed assignment (post) "
				      << varVxp << endl);
				varVxp->isDelayed(true);
			    } else {
				// If the lhs is a clocker, avoid marking that as circular by
				// putting a hard edge instead of normal cuttable
				if (varscp->varp()->attrClocker() == AstVarAttrClocker::CLOCKER_YES)
				    new OrderEdge(&m_graph, m_logicVxp, varVxp, WEIGHT_NORMAL);
				else
				    new OrderComboCutEdge(&m_graph, m_logicVxp, varVxp);
			    }
			    // For m_inPost:
			    //    Add edge consumed_var_POST->logic_vertex
			    //    This prevents a consumer of the "early" value to be scheduled
			    //   after we've changed to the next-cycle value
			    // ALWAYS do it:
			    //    There maybe a wire a=b; between the two blocks
			    OrderVarVertex* postVxp = newVarUserVertex(varscp, WV_POST);
			    new OrderEdge(&m_graph, postVxp, m_logicVxp, WEIGHT_POST);
			}
			if (con) {
			    // Add edge logic_consumed_var->logic_vertex
			    OrderVarVertex* varVxp = newVarUserVertex(varscp, WV_STD);
			    new OrderEdge(&m_graph, varVxp, m_logicVxp, WEIGHT_MEDIUM);
			}
		    }
		} else if (m_inPre) {
		    // AstAssignPre logic
		    if (gen) {
			// Add edge logic_vertex->generated_var_PREORDER
			OrderVarVertex* ordVxp = newVarUserVertex(varscp, WV_PORD);
			new OrderEdge(&m_graph, m_logicVxp, ordVxp, WEIGHT_NORMAL);
			// Add edge logic_vertex->logic_generated_var (same as if comb)
			OrderVarVertex* varVxp = newVarUserVertex(varscp, WV_STD);
			new OrderEdge(&m_graph, m_logicVxp, varVxp, WEIGHT_NORMAL);
		    }
		    if (con) {
			// Add edge logic_consumed_var_PREVAR->logic_vertex
			// This one is cutable (vs the producer) as there's only one of these, but many producers
			OrderVarVertex* preVxp = newVarUserVertex(varscp, WV_PRE);
			new OrderPreCutEdge(&m_graph, preVxp, m_logicVxp);
		    }
		} else {
		    // Seq logic
		    if (gen) {
			// Add edge logic_generated_var_PREORDER->logic_vertex
			OrderVarVertex* ordVxp = newVarUserVertex(varscp, WV_PORD);
			new OrderEdge(&m_graph, ordVxp, m_logicVxp, WEIGHT_NORMAL);
			// Add edge logic_vertex->logic_generated_var (same as if comb)
			OrderVarVertex* varVxp = newVarUserVertex(varscp, WV_STD);
			new OrderEdge(&m_graph, m_logicVxp, varVxp, WEIGHT_NORMAL);
		    }
		    if (con) {
			// Add edge logic_vertex->consumed_var_PREVAR
			// Generation of 'pre' because we want to indicate it should be before AstAssignPre
			OrderVarVertex* preVxp = newVarUserVertex(varscp, WV_PRE);
			new OrderEdge(&m_graph, m_logicVxp, preVxp, WEIGHT_NORMAL);
			// Add edge logic_vertex->consumed_var_POST
			OrderVarVertex* postVxp = newVarUserVertex(varscp, WV_POST);
			new OrderEdge(&m_graph, m_logicVxp, postVxp, WEIGHT_POST);
		    }
		}
	    }
	}
    }
    virtual void visit(AstSenTree* nodep, AstNUser*) {
	// Having a node derived from the sentree isn't required for
	// correctness, it mearly makes the graph better connected
	// and improves graph algorithmic performance
	if (m_scopep) {	// Else TOPSCOPE's SENTREE list
	    m_inSenTree = true;
	    if (nodep->hasClocked()) {
		if (!m_activeSenVxp) {
		    m_activeSenVxp = new OrderLogicVertex(&m_graph, m_scopep, nodep, m_activep);
		}
		nodep->iterateChildren(*this);
	    }
	    m_inSenTree = false;
	}
    }
    virtual void visit(AstAlways* nodep, AstNUser*) {
	iterateNewStmt(nodep);
    }
    virtual void visit(AstAlwaysPost* nodep, AstNUser*) {
	m_inPost = true;
	iterateNewStmt(nodep);
	m_inPost = false;
    }
    virtual void visit(AstAlwaysPublic* nodep, AstNUser*) {
	iterateNewStmt(nodep);
    }
    virtual void visit(AstAssignAlias* nodep, AstNUser*) {
	iterateNewStmt(nodep);
    }
    virtual void visit(AstAssignW* nodep, AstNUser*) {
	OrderClkAssVisitor visitor(nodep);
	m_inClkAss = visitor.isClkAss();
	iterateNewStmt(nodep);
	m_inClkAss = false;
    }
    virtual void visit(AstAssignPre* nodep, AstNUser*) {
	OrderClkAssVisitor visitor(nodep);
	m_inClkAss = visitor.isClkAss();
	m_inPre = true;
	iterateNewStmt(nodep);
	m_inPre = false;
	m_inClkAss = false;
    }
    virtual void visit(AstAssignPost* nodep, AstNUser*) {
	OrderClkAssVisitor visitor(nodep);
	m_inClkAss = visitor.isClkAss();
	m_inPost = true;
	iterateNewStmt(nodep);
	m_inPost = false;
	m_inClkAss = false;
    }
    virtual void visit(AstCoverToggle* nodep, AstNUser*) {
	iterateNewStmt(nodep);
    }
    virtual void visit(AstInitial* nodep, AstNUser*) {
	// We use initials to setup parameters and static consts's which may be referenced
	// in user initial blocks.  So use ordering to sort them all out.
	iterateNewStmt(nodep);
    }
    virtual void visit(AstCFunc*, AstNUser*) {
	// Ignore for now
	// We should detect what variables are set in the function, and make
	// settlement code for them, then set a global flag, so we call "settle"
	// on the next evaluation loop.
    }
    //--------------------
    // Default
    virtual void visit(AstNode* nodep, AstNUser*) {
	nodep->iterateChildren(*this);
    }
public:
    // CONSTUCTORS
    OrderVisitor() {
	m_topScopep = NULL;
	m_scopetopp = NULL;
	m_modp = NULL;
	m_scopep = NULL;
	m_activep = NULL;
	m_inSenTree = false;
	m_inClocked = false;
	m_inClkAss = false;
	m_inPre = m_inPost = false;
	m_comboDomainp = NULL;
	m_deleteDomainp = NULL;
	m_settleDomainp = NULL;
	m_settleVxp = NULL;
	m_inputsVxp = NULL;
	m_activeSenVxp = NULL;
	m_logicVxp = NULL;
	m_pomNewFuncp = NULL;
	m_loopIdMax = LOOPID_FIRST;
	m_pomNewStmts = 0;
	if (debug()) m_graph.debug(5); // 3 is default if global debug; we want acyc debugging
    }
    virtual ~OrderVisitor() {
	// Stats
	for (int type=0; type<OrderVEdgeType::_ENUM_END; type++) {
	    if (double count = double(m_statCut[type])) {
		V3Stats::addStat(string("Order, cut, ")+OrderVEdgeType(type).ascii(), count);
	    }
	}
	// Destruction
	for (deque<OrderUser*>::iterator it=m_orderUserps.begin(); it!=m_orderUserps.end(); ++it) {
	    delete *it;
	}
	m_graph.debug(V3Error::debugDefault());
    }
    void main(AstNode* nodep) {
	nodep->accept(*this);
    }
};

//######################################################################
// Clock propagation

void OrderVisitor::processInputs() {
    m_graph.userClearVertices();  // Vertex::user()   // 1 if input recursed, 2 if marked as input, 3 if out-edges recursed
    // Start at input vertex, process from input-to-output order
    VertexVec todoVec; // List of newly-input marked vectors we need to process
    todoVec.push_front(m_inputsVxp);
    m_inputsVxp->isFromInput(true);  // By definition
    while (!todoVec.empty()) {
	OrderEitherVertex* vertexp = todoVec.back(); todoVec.pop_back();
	processInputsOutIterate(vertexp, todoVec);
    }
}

void OrderVisitor::processInputsInIterate(OrderEitherVertex* vertexp, VertexVec& todoVec) {
    // Propagate PrimaryIn through simple assignments
    if (vertexp->user()) return;  // Already processed
    if (0 && debug()>=9) {
	UINFO(9," InIIter "<<vertexp<<endl);
	if (OrderLogicVertex* vvertexp = dynamic_cast<OrderLogicVertex*>(vertexp)) {
	    vvertexp->nodep()->dumpTree(cout,"-            TT: ");
	}
    }
    vertexp->user(1);  // Processing
    // First handle all inputs to this vertex, in most cases they'll be already processed earlier
    // Also, determine if this vertex is an input
    int inonly = 1;  // 0=no, 1=maybe, 2=yes until a no
    for (V3GraphEdge* edgep = vertexp->inBeginp(); edgep; edgep=edgep->inNextp()) {
	OrderEitherVertex* frVertexp = (OrderEitherVertex*)edgep->fromp();
	processInputsInIterate(frVertexp, todoVec);
	if (frVertexp->isFromInput()) {
	    if (inonly==1) inonly = 2;
	} else if (dynamic_cast<OrderVarPostVertex*>(frVertexp)) {
	    // Ignore post assignments, just for ordering
	} else {
	    //UINFO(9,"    InItStopDueTo "<<frVertexp<<endl);
	    inonly = 0;
	    break;
	}
    }

    if (inonly == 2 && vertexp->user()<2) {  // Set it.  Note may have already been set earlier, too
	UINFO(9,"   Input reassignment: "<<vertexp<<endl);
	vertexp->isFromInput(true);
	vertexp->user(2);  // 2 means on list
	// Can't work on out-edges of a node we know is an input immediately,
	// as it might visit other nodes before their input state is resolved.
	// So push to list and work on it later when all in-edges known resolved
	todoVec.push_back(vertexp);
    }
    //UINFO(9,"  InIdone "<<vertexp<<endl);
}

void OrderVisitor::processInputsOutIterate(OrderEitherVertex* vertexp, VertexVec& todoVec) {
    if (vertexp->user()==3) return;  // Already out processed
    //UINFO(9," InOIter "<<vertexp<<endl);
    // First make sure input path is fully recursed
    processInputsInIterate(vertexp, todoVec);
    // Propagate PrimaryIn through simple assignments
    if (!vertexp->isFromInput()) v3fatalSrc("processInputsOutIterate only for input marked vertexes");
    vertexp->user(3);  // out-edges processed

    {
	// Propagate PrimaryIn through simple assignments, followint target of vertex
	for (V3GraphEdge* edgep = vertexp->outBeginp(); edgep; edgep=edgep->outNextp()) {
	    OrderEitherVertex* toVertexp = (OrderEitherVertex*)edgep->top();
	    if (OrderVarStdVertex* vvertexp = dynamic_cast<OrderVarStdVertex*>(toVertexp)) {
		processInputsInIterate(vvertexp, todoVec);
	    }
	    if (OrderLogicVertex* vvertexp = dynamic_cast<OrderLogicVertex*>(toVertexp)) {
		if (vvertexp->nodep()->castNodeAssign()) {
		    processInputsInIterate(vvertexp, todoVec);
		}
	    }
	}
    }
}

//######################################################################
// Circular detection

void OrderVisitor::processCircular() {
    // Take broken edges and add circular flags
    // The change detect code will use this to force changedets
    for (V3GraphVertex* itp = m_graph.verticesBeginp(); itp; itp=itp->verticesNextp()) {
	if (OrderVarStdVertex* vvertexp = dynamic_cast<OrderVarStdVertex*>(itp)) {
	    if (vvertexp->isClock() && !vvertexp->isFromInput()) {
		// If a clock is generated internally, we need to do another
		// loop through the entire evaluation.  This fixes races; see
		// t_clk_dpulse test.
		//
		// This all seems to hinge on how the clock is generated. If
		// it is generated by delayed assignment, we need the loop. If
		// it is combinatorial, we do not (and indeed it will break
		// other tests such as t_gated_clk_1.
		if (!v3Global.opt.orderClockDly()) {
		    UINFO(5,"Circular Clock, no-order-clock-delay "<<vvertexp<<endl);
		    nodeMarkCircular(vvertexp, NULL);
		}
		else if (vvertexp->isDelayed()) {
		    UINFO(5,"Circular Clock, delayed "<<vvertexp<<endl);
		    nodeMarkCircular(vvertexp, NULL);
		}
		else {
		    UINFO(5,"Circular Clock, not delayed "<<vvertexp<<endl);
		}
	    }
	    // Also mark any cut edges
	    for (V3GraphEdge* edgep = vvertexp->outBeginp(); edgep; edgep=edgep->outNextp()) {
		if (edgep->weight()==0) { // was cut
		    OrderEdge* oedgep = dynamic_cast<OrderEdge*>(edgep);
		    if (!oedgep) vvertexp->varScp()->v3fatalSrc("Cuttable edge not of proper type");
		    UINFO(6,"      CutCircularO: "<<vvertexp->name()<<endl);
		    nodeMarkCircular(vvertexp, oedgep);
		}
	    }
	    for (V3GraphEdge* edgep = vvertexp->inBeginp(); edgep; edgep = edgep->inNextp()) {
		if (edgep->weight()==0) { // was cut
		    OrderEdge* oedgep = dynamic_cast<OrderEdge*>(edgep);
		    if (!oedgep) vvertexp->varScp()->v3fatalSrc("Cuttable edge not of proper type");
		    UINFO(6,"      CutCircularI: "<<vvertexp->name()<<endl);
		    nodeMarkCircular(vvertexp, oedgep);
		}
	    }
	}
    }
}

void OrderVisitor::processSensitive() {
    // Sc sensitives are required on all inputs that go to a combo
    // block.  (Not inputs that go only to clocked blocks.)
    for (V3GraphVertex* itp = m_graph.verticesBeginp(); itp; itp=itp->verticesNextp()) {
	if (OrderVarStdVertex* vvertexp = dynamic_cast<OrderVarStdVertex*>(itp)) {
	    if (vvertexp->varScp()->varp()->isInput()) {
		//UINFO(0,"  scsen "<<vvertexp<<endl);
		for (V3GraphEdge* edgep = vvertexp->outBeginp(); edgep; edgep=edgep->outNextp()) {
		    if (OrderEitherVertex* toVertexp = dynamic_cast<OrderEitherVertex*>(edgep->top())) {
			if (edgep->weight() && toVertexp->domainp()) {
			    //UINFO(0,"      "<<toVertexp->domainp()<<endl);
			    if (toVertexp->domainp()->hasCombo()) {
				vvertexp->varScp()->varp()->scSensitive(true);
			    }
			}
		    }
		}
	    }
	}
    }
}

void OrderVisitor::processDomains() {
    for (V3GraphVertex* itp = m_graph.verticesBeginp(); itp; itp=itp->verticesNextp()) {
	OrderEitherVertex* vertexp = dynamic_cast<OrderEitherVertex*>(itp);
	UASSERT(vertexp, "Null or vertex not derived from EitherVertex\n");
	processDomainsIterate(vertexp);
    }
}

void OrderVisitor::processDomainsIterate(OrderEitherVertex* vertexp) {
    // The graph routines have already sorted the vertexes and edges into best->worst order
    // Assign clock domains to each signal.
    //     Sequential logic is forced into the same sequential domain.
    //     Combo logic may be pushed into a seq domain if all its inputs are the same domain,
    //     else, if all inputs are from flops, it's end-of-sequential code
    //     else, it's full combo code
    if (!vertexp->inLoop()) vertexp->inLoop(LOOPID_NOTLOOPED);
    if (vertexp->domainp()) return;	// Already processed, or sequential logic
    UINFO(5,"    pdi: "<<vertexp<<endl);
    OrderVarVertex* vvertexp = dynamic_cast<OrderVarVertex*>(vertexp);
    AstSenTree* domainp = NULL;
    UASSERT(m_comboDomainp, "not preset");
    if (vvertexp && vvertexp->varScp()->varp()->isInput()) {
	domainp = m_comboDomainp;
    }
    if (vvertexp && vvertexp->varScp()->isCircular()) {
	domainp = m_comboDomainp;
    }
    if (!domainp) {
	for (V3GraphEdge* edgep = vertexp->inBeginp(); edgep; edgep = edgep->inNextp()) {
	    OrderEitherVertex* fromVertexp = (OrderEitherVertex*)edgep->fromp();
	    if (edgep->weight()
		&& fromVertexp->domainMatters()
		) {
		UINFO(9,"     from d="<<(void*)fromVertexp->domainp()<<" "<<fromVertexp<<endl);
		if (!domainp  // First input to this vertex
		    || domainp->hasSettle()	// or, we can ignore being in the settle domain
		    || domainp->hasInitial()) {
		    domainp = fromVertexp->domainp();
		}
		else if (domainp->hasCombo()) {
		    // Once in combo, keep in combo; already as severe as we can get
		}
		else if (fromVertexp->domainp()->hasCombo()) {
		    // Any combo input means this vertex must remain combo
		    domainp = m_comboDomainp;
		}
		else if (fromVertexp->domainp()->hasSettle()
			 || fromVertexp->domainp()->hasInitial()) {
		    // Ignore that we have a constant (initial) input
		}
		else if (domainp != fromVertexp->domainp()) {
		    // Make a domain that merges the two domains
		    bool ddebug = debug()>=9;
		    if (ddebug) {
			cout<<endl;
			UINFO(0,"      conflicting domain "<<fromVertexp<<endl);
			UINFO(0,"         dorig="<<domainp<<endl);
			domainp->dumpTree(cout);
			UINFO(0,"         d2   ="<<fromVertexp->domainp()<<endl);
			fromVertexp->domainp()->dumpTree(cout);
		    }
		    AstSenTree* newtreep = domainp->cloneTree(false);
		    AstNodeSenItem* newtree2p = fromVertexp->domainp()->sensesp()->cloneTree(true);
		    if (!newtree2p) fromVertexp->domainp()->v3fatalSrc("No senitem found under clocked domain");
		    newtreep->addSensesp(newtree2p);
		    newtree2p=NULL; // Below edit may replace it
		    V3Const::constifyExpensiveEdit(newtreep);	// Remove duplicates
		    newtreep->multi(true);	// Comment that it was made from 2 clock domains
		    domainp = m_finder.getSenTree(domainp->fileline(), newtreep);
		    if (ddebug) {
			UINFO(0,"         dnew ="<<newtreep<<endl);
			newtreep->dumpTree(cout);
			UINFO(0,"         find ="<<domainp<<endl);
			domainp->dumpTree(cout);
			cout<<endl;
		    }
		    newtreep->deleteTree(); newtreep=NULL;
		}
	    }
	} // next input edgep
	// Default the domain
	// This is a node which has only constant inputs, or is otherwise indeterminate.
	// It should have already been copied into the settle domain.  Presumably it has
	// inputs which we never trigger, or nothing it's sensitive to, so we can rip it out.
	if (!domainp && vertexp->scopep()) {
	    domainp = m_deleteDomainp;
	}
    }
    //
    vertexp->domainp(domainp);
    if (vertexp->domainp()) {
	UINFO(5,"      done d="<<(void*)vertexp->domainp()
	      <<(vertexp->domainp()->hasCombo()?" [COMB]":"")
	      <<(vertexp->domainp()->isMulti()?" [MULT]":"")
	      <<" "<<vertexp<<endl);
    }
}

//######################################################################
// Move graph construction

void OrderVisitor::processEdgeReport() {
    // Make report of all signal names and what clock edges they have
    string filename = v3Global.debugFilename("order_edges.txt");
    const VL_UNIQUE_PTR<ofstream> logp (V3File::new_ofstream(filename));
    if (logp->fail()) v3fatalSrc("Can't write "<<filename);
    //Testing emitter: V3EmitV::verilogForTree(v3Global.rootp(), *logp);

    deque<string> report;

    for (V3GraphVertex* itp = m_graph.verticesBeginp(); itp; itp=itp->verticesNextp()) {
	if (OrderVarVertex* vvertexp = dynamic_cast<OrderVarVertex*>(itp)) {
	    string name (vvertexp->varScp()->prettyName());
	    if (dynamic_cast<OrderVarPreVertex*>(itp)) name += " {PRE}";
	    else if (dynamic_cast<OrderVarPostVertex*>(itp)) name += " {POST}";
	    else if (dynamic_cast<OrderVarPordVertex*>(itp)) name += " {PORD}";
	    else if (dynamic_cast<OrderVarSettleVertex*>(itp)) name += " {STL}";
	    ostringstream os;
	    os.setf(ios::left);
	    os<<"  "<<(void*)(vvertexp->varScp())<<" "<<setw(50)<<name<<" ";
	    AstSenTree* sentreep = vvertexp->domainp();
	    if (sentreep) V3EmitV::verilogForTree(sentreep, os);
	    report.push_back(os.str());
	}
    }

    *logp<<"Signals and their clock domains:"<<endl;
    stable_sort(report.begin(), report.end());
    for (deque<string>::iterator it=report.begin(); it!=report.end(); ++it) {
	*logp<<(*it)<<endl;
    }

}

//######################################################################
// Move graph construction

void OrderVisitor::processMoveClear() {
    OrderMoveDomScope::clear();
    m_pomWaiting.reset();
    m_pomReadyDomScope.reset();
    m_pomGraph.clear();
}

void OrderVisitor::processMoveBuildGraph() {
    // Build graph of only vertices
    UINFO(5,"  MoveBuildGraph\n");
    processMoveClear();
    m_pomGraph.userClearVertices();  // Vertex::user()   // OrderMoveVertex*, last edge added or NULL for none

    // For each logic node, make a graph node
    for (V3GraphVertex* itp = m_graph.verticesBeginp(); itp; itp=itp->verticesNextp()) {
	if (OrderLogicVertex* lvertexp = dynamic_cast<OrderLogicVertex*>(itp)) {
	    OrderMoveVertex* moveVxp = new OrderMoveVertex(&m_pomGraph, lvertexp);
	    moveVxp->m_pomWaitingE.pushBack(m_pomWaiting, moveVxp);
	    // Cross link so we can find it later
	    lvertexp->moveVxp(moveVxp);
	}
    }
    // Build edges between logic vertices
    for (V3GraphVertex* itp = m_graph.verticesBeginp(); itp; itp=itp->verticesNextp()) {
	if (OrderLogicVertex* lvertexp = dynamic_cast<OrderLogicVertex*>(itp)) {
	    OrderMoveVertex* moveVxp = lvertexp->moveVxp();
	    processMoveBuildGraphIterate(moveVxp, lvertexp, 0);
	}
    }
}

void OrderVisitor::processMoveBuildGraphIterate (OrderMoveVertex* moveVxp, V3GraphVertex* vertexp, int weightmin) {
    // Search forward from given logic vertex, making new edges based on moveVxp
    for (V3GraphEdge* edgep = vertexp->outBeginp(); edgep; edgep=edgep->outNextp()) {
	if (edgep->weight()!=0) { // was cut
	    int weight = weightmin;
	    if (weight==0 || weight>edgep->weight()) weight=edgep->weight();
	    if (OrderLogicVertex* toLVertexp = dynamic_cast<OrderLogicVertex*>(edgep->top())) {
		// Path from vertexp to a logic vertex; new edge
		// Note we use the last edge's weight, not some function of multiple edges
		new OrderEdge(&m_pomGraph, moveVxp, toLVertexp->moveVxp(), weight);
	    }
	    else { // Keep hunting forward for a logic node
		processMoveBuildGraphIterate(moveVxp, edgep->top(), weight);
	    }
	}
    }
}

//######################################################################
// Moving

void OrderVisitor::processMove() {
    // The graph routines have already sorted the vertexes and edges into best->worst order
    //   Make a new waiting graph with only OrderLogicVertex's
    //   (Order is preserved in the recreation so the sorting is preserved)
    //   Move any node with all inputs ready to a "ready" graph mapped by domain and then scope
    //	 While waiting graph ! empty  (and also known: something in ready graph)
    //     For all scopes in domain of top ready vertex
    //       For all vertexes in domain&scope of top ready vertex
    //	         Make ordered activation block for this module
    //	         Add that new activation to the list of calls to make.
    //	    	 Move logic to ordered active
    //		 Any children that have all inputs now ready move from waiting->ready graph
    //		 (This may add nodes the for loop directly above needs to detext)
    processMovePrepScopes();
    processMovePrepReady();

    // New domain... another loop
    UINFO(5,"  MoveIterate\n");
    while (!m_pomReadyDomScope.empty()) {
	// Start with top node on ready list's domain & scope
	OrderMoveDomScope* domScopep = m_pomReadyDomScope.begin();
	OrderMoveVertex* topVertexp = domScopep->readyVertices().begin(); // lintok-begin-on-ref
	UASSERT(topVertexp, "domScope on ready list without any nodes ready under it");
	// Work on all scopes ready inside this domain
	while (domScopep) {
	    UINFO(6,"   MoveDomain l="<<domScopep->domainp()<<endl);
	    // Process all nodes ready under same domain & scope
	    m_pomNewFuncp = NULL;
	    while (OrderMoveVertex* vertexp = domScopep->readyVertices().begin()) { // lintok-begin-on-ref
		processMoveOne(vertexp, domScopep, 1);
	    }
	    // Done with scope/domain pair, pick new scope under same domain, or NULL if none left
	    OrderMoveDomScope* domScopeNextp = NULL;
	    for (OrderMoveDomScope* huntp = m_pomReadyDomScope.begin();
		 huntp; huntp = huntp->readyDomScopeNextp()) {
		if (huntp->domainp() == domScopep->domainp()) {
		    domScopeNextp = huntp;
		    break;
		}
	    }
	    domScopep = domScopeNextp;
	}
    }
    UASSERT (m_pomWaiting.empty(), "Didn't converge; nodes waiting, none ready, perhaps some input activations lost.");
    // Cleanup memory
    processMoveClear();
}

void OrderVisitor::processMovePrepScopes() {
    UINFO(5,"  MovePrepScopes\n");
    // Create a OrderMoveDomScope every domain/scope pairing
    for (OrderMoveVertex* vertexp = m_pomWaiting.begin(); vertexp; vertexp=vertexp->pomWaitingNextp()) {
	AstSenTree* domainp = vertexp->logicp()->domainp();
	AstScope* scopep = vertexp->logicp()->scopep();
	OrderLoopId inLoop = vertexp->logicp()->inLoop();
	// Create the dom pairing for later lookup
	OrderMoveDomScope* domScopep = OrderMoveDomScope::findCreate(inLoop, domainp, scopep);
	vertexp->domScopep(domScopep);
    }
}

void OrderVisitor::processMovePrepReady() {
    // Make list of ready nodes
    UINFO(5,"  MovePrepReady\n");
    for (OrderMoveVertex* vertexp = m_pomWaiting.begin(); vertexp; ) {
	OrderMoveVertex* nextp = vertexp->pomWaitingNextp();
	if (vertexp->isWait() && vertexp->inEmpty()) {
	    processMoveReadyOne(vertexp);
	}
	vertexp = nextp;
    }
}

void OrderVisitor::processMoveReadyOne(OrderMoveVertex* vertexp) {
    // Recursive!
    // Move one node from waiting to ready list
    vertexp->setReady();
    // Remove node from waiting list
    vertexp->m_pomWaitingE.unlink(m_pomWaiting, vertexp);
    // Add to ready list (indexed by domain and scope)
    vertexp->m_readyVerticesE.pushBack(vertexp->domScopep()->m_readyVertices, vertexp);
    vertexp->domScopep()->ready (this);
}

void OrderVisitor::processMoveDoneOne(OrderMoveVertex* vertexp) {
    // Move one node from ready to completion
    vertexp->setMoved();
    // Unlink from ready lists
    vertexp->m_readyVerticesE.unlink(vertexp->domScopep()->m_readyVertices, vertexp);
    vertexp->domScopep()->movedVertex (this, vertexp);
    // Don't need to add it to another list, as we're done with it
    // Mark our outputs as one closer to ready
    for (V3GraphEdge* edgep = vertexp->outBeginp(), *nextp; edgep; edgep=nextp) {
	nextp = edgep->outNextp();
	OrderMoveVertex* toVertexp = (OrderMoveVertex*)edgep->top();
	UINFO(9,"          Clear to "<<(toVertexp->inEmpty()?"[EMP] ":"      ")
	      <<toVertexp<<endl);
	// Delete this edge
	edgep->unlinkDelete(); edgep=NULL;
	if (toVertexp->inEmpty()) {
	    // If destination node now has all inputs resolved; recurse to move that vertex
	    // This is thus depth first (before width) which keeps the resulting executable's d-cache happy.
	    processMoveReadyOne(toVertexp);
	}
    }
}

void OrderVisitor::processMoveOne(OrderMoveVertex* vertexp, OrderMoveDomScope* domScopep, int level) {
    UASSERT(vertexp->domScopep() == domScopep, "Domain mismatch; list misbuilt?\n");
    OrderLogicVertex* lvertexp = vertexp->logicp();
    AstScope* scopep = lvertexp->scopep();
    UINFO(5,"    POSmove l"<<setw(3)<<level<<" d="<<(void*)(lvertexp->domainp())
	  <<" s="<<(void*)(scopep)<<" "<<lvertexp<<endl);
    AstSenTree* domainp = lvertexp->domainp();
    AstNode* nodep = lvertexp->nodep();
    AstNodeModule* modp = scopep->user1p()->castNode()->castNodeModule();  UASSERT(modp,"NULL"); // Stashed by visitor func
    if (nodep->castUntilStable()) {
	nodep->v3fatalSrc("Not implemented");
    }
    else if (nodep->castSenTree()) {
	// Just ignore sensitivities, we'll deal with them when we move statements that need them
    }
    else {  // Normal logic
	// Make or borrow a CFunc to contain the new statements
	if (v3Global.opt.profileCFuncs()
	    || (v3Global.opt.outputSplitCFuncs()
		&& v3Global.opt.outputSplitCFuncs() < m_pomNewStmts)) {
	    // Put every statement into a unique function to ease profiling or reduce function size
	    m_pomNewFuncp = NULL;
	}
	if (!m_pomNewFuncp && domainp != m_deleteDomainp) {
	    string name = cfuncName(modp, domainp, scopep, nodep);
	    m_pomNewFuncp = new AstCFunc(nodep->fileline(), name, scopep);
	    m_pomNewFuncp->argTypes(EmitCBaseVisitor::symClassVar());
	    m_pomNewFuncp->symProlog(true);
	    m_pomNewStmts = 0;
	    if (domainp->hasInitial() || domainp->hasSettle()) m_pomNewFuncp->slow(true);
	    scopep->addActivep(m_pomNewFuncp);
	    // Where will we be adding the call?
	    AstActive* callunderp = new AstActive(nodep->fileline(), name, domainp);
	    processMoveLoopStmt(callunderp);
	    // Add a top call to it
	    AstCCall* callp = new AstCCall(nodep->fileline(), m_pomNewFuncp);
	    callp->argTypes("vlSymsp");
	    callunderp->addStmtsp(callp);
	    UINFO(6,"      New "<<m_pomNewFuncp<<endl);
	}

	// Move the logic to the function we're creating
	nodep->unlinkFrBack();
	if (domainp == m_deleteDomainp) {
	    UINFO(4," Ordering deleting pre-settled "<<nodep<<endl);
	    pushDeletep(nodep); nodep=NULL;
	} else {
	    m_pomNewFuncp->addStmtsp(nodep);
	    if (v3Global.opt.outputSplitCFuncs()) {
		// Add in the number of nodes we're adding
		EmitCBaseCounterVisitor visitor(nodep);
		m_pomNewStmts += visitor.count();
	    }
	}
    }
    processMoveDoneOne (vertexp);
}

inline void OrderVisitor::processMoveLoopPush(OrderLoopBeginVertex* beginp) {
    UINFO(6,"      LoopPush  "<<beginp<<endl);
    m_pomLoopMoveps.push_back(beginp);
}

inline void OrderVisitor::processMoveLoopPop(OrderLoopBeginVertex* beginp) {
    UINFO(6,"      LoopPop   "<<beginp<<endl);
    if (m_pomLoopMoveps.empty()) beginp->nodep()->v3fatalSrc("processMoveLoopPop with no push'ed loops");
    OrderLoopBeginVertex* topBeginp = m_pomLoopMoveps.back();
    if (topBeginp != beginp) beginp->nodep()->v3fatalSrc("processMoveLoopPop had different vertex then one expected, got="<<topBeginp<<" exp="<<beginp<<endl);
    m_pomLoopMoveps.pop_back();
}

inline void OrderVisitor::processMoveLoopStmt(AstNode* newSubnodep) {
    if (m_pomLoopMoveps.empty()) {
	// Not in any loops, statements go into main body
	m_scopetopp->addActivep(newSubnodep);
    } else {
	// In a loop, put statements under appropriate loop body
	OrderLoopBeginVertex* topBeginp = m_pomLoopMoveps.back();
	topBeginp->untilp()->addBodysp(newSubnodep);
    }
}

inline OrderLoopId OrderVisitor::processMoveLoopCurrent() {
    // Return loopID we're currently processing
    if (m_pomLoopMoveps.empty()) {
	return LOOPID_NOTLOOPED;
    } else {
	OrderLoopBeginVertex* topBeginp = m_pomLoopMoveps.back();
	return topBeginp->loopId();  // Not inLoop, the begin is in the upper subloop.
    }
}

inline void OrderMoveDomScope::ready(OrderVisitor* ovp) {	// Check the domScope is on ready list, add if not
    if (!m_onReadyList) {
	m_onReadyList = true;
	UASSERT (inLoop()!=0, "Loop# 0 is illegal, perhaps should be LOOPID_NOTLOOPED?");
	m_readyDomScopeE.pushBack(ovp->m_pomReadyDomScope, this);
    }
}

inline void OrderMoveDomScope::movedVertex(OrderVisitor* ovp, OrderMoveVertex* vertexp) {	// Mark one vertex as finished, remove from ready list if done
    UASSERT(m_onReadyList, "Moving vertex from ready when nothing was on que as ready.");
    if (m_readyVertices.empty()) {	// Else more work to get to later
	m_onReadyList = false;
	m_readyDomScopeE.unlink(ovp->m_pomReadyDomScope, this);
    }
}

//######################################################################
// Top processing

void OrderVisitor::process() {
    // Dump data
    m_graph.dumpDotFilePrefixed("orderg_pre");

    // Break cycles. Each strongly connected subgraph (including cutable
    // edges) will have its own color, and corresponds to a loop in the
    // original graph. However the new graph will be acyclic (the removed
    // edges are actually still there, just with weight 0).
    UINFO(2,"  Acyclic & Order...\n");
    m_graph.acyclic(&V3GraphEdge::followAlwaysTrue);
    m_graph.dumpDotFilePrefixed("orderg_acyc");

    // Assign ranks so we know what to follow
    // Then, sort vertices and edges by that ordering
    m_graph.order();
    m_graph.dumpDotFilePrefixed("orderg_order");

    // This finds everything that can be traced from an input (which by
    // definition are the source clocks). After this any vertex which was
    // traced has isFromInput() true.
    UINFO(2,"  Process Clocks...\n");
    processInputs();  // must be before processCircular

    UINFO(2,"  Process Circulars...\n");
    processCircular();  // must be before processDomains

    // Assign logic verticesto new domains
    UINFO(2,"  Domains...\n");
    processDomains();
    m_graph.dumpDotFilePrefixed("orderg_domain");

    if (debug() && v3Global.opt.dumpTree()) processEdgeReport();

    UINFO(2,"  Construct Move Graph...\n");
    processMoveBuildGraph();
    if (debug()>=4) m_pomGraph.dumpDotFilePrefixed("ordermv_start");  // Different prefix (ordermv) as it's not the same graph
    m_pomGraph.removeRedundantEdges(&V3GraphEdge::followAlwaysTrue);
    m_pomGraph.dumpDotFilePrefixed("ordermv_simpl");

    UINFO(2,"  Move...\n");
    processMove();

    // Any SC inputs feeding a combo domain must be marked, so we can make them sc_sensitive
    UINFO(2,"  Sensitive...\n");
    processSensitive();  // must be after processDomains

    // Dump data
    m_graph.dumpDotFilePrefixed("orderg_done");
    if (0 && debug()) {
	string dfilename = v3Global.opt.makeDir()+"/"+v3Global.opt.prefix()+"_INT_order.tree";
	const auto_ptr<ofstream> logp (V3File::new_ofstream(dfilename));
	if (logp->fail()) v3fatalSrc("Can't write "<<dfilename);
	m_graph.dump(*logp);
    }
}

//######################################################################
// Order class functions

void V3Order::orderAll(AstNetlist* nodep) {
    UINFO(2,__FUNCTION__<<": "<<endl);
    OrderClkMarkVisitor markVisitor(nodep);
    OrderVisitor visitor;
    visitor.main(nodep);
    V3Global::dumpCheckGlobalTree("order.tree", 0, v3Global.opt.dumpTreeLevel(__FILE__) >= 3);
}
