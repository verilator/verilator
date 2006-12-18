// $Id$
//*************************************************************************
// DESCRIPTION: Verilator: Gate optimizations, such as wire elimination
//
// Code available from: http://www.veripool.com/verilator
//
// AUTHORS: Wilson Snyder with Paul Wasson, Duane Gabli
//
//*************************************************************************
//
// Copyright 2003-2006 by Wilson Snyder.  This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// General Public License or the Perl Artistic License.
//
// Verilator is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
//*************************************************************************
// V3Gate's Transformations:
//		
// Extract a graph of the *entire* netlist with cells expanded
// Perform constant optimization across the graph
// Create VARSCOPEs for any variables we can rip out
//
//*************************************************************************

#include "config_build.h"
#include "verilatedos.h"
#include <stdio.h>
#include <stdarg.h>
#include <unistd.h>
#include <algorithm>
#include <iomanip>
#include <vector>
#include <list>

#include "V3Global.h"
#include "V3Gate.h"
#include "V3Ast.h"
#include "V3Graph.h"
#include "V3Const.h"
#include "V3Stats.h"

typedef list<AstNodeVarRef*> GateVarRefList;

//######################################################################

class GateBaseVisitor : public AstNVisitor {
public:
    //int debug() { return 9; }
};

//######################################################################
// Support classes

class GateEitherVertex : public V3GraphVertex {
    AstScope*	m_scopep;
    bool	m_reducible;	// True if this node should be able to be eliminated
    bool	m_consumed;		// Output goes to something meaningful
public:
    GateEitherVertex(V3Graph* graphp, AstScope* scopep)
	: V3GraphVertex(graphp), m_scopep(scopep), m_reducible(true), m_consumed(false) {}
    virtual ~GateEitherVertex() {}
    // Accessors
    virtual string dotStyle() const { return m_consumed?"":"dotted"; }
    AstScope* scopep() const { return m_scopep; }
    bool reducible() const { return m_reducible; }
    void setConsumed(const char* consumedReason) {
	m_consumed = true;
	//UINFO(0,"\t\tSetConsumed "<<consumedReason<<" "<<this<<endl);
    }
    bool consumed() const { return m_consumed; }
    void clearReducible(const char* nonReducibleReason) {
	m_reducible = false;
	//UINFO(0,"     NR: "<<nonReducibleReason<<"  "<<name()<<endl);
    }
};

class GateVarVertex : public GateEitherVertex {
    AstVarScope* m_varScp;
    bool	 m_isTop;
    bool	 m_isClock;
public:
    GateVarVertex(V3Graph* graphp, AstScope* scopep, AstVarScope* varScp)
	: GateEitherVertex(graphp, scopep), m_varScp(varScp), m_isTop(false)
	, m_isClock(false) {}
    virtual ~GateVarVertex() {}
    // Accessors
    AstVarScope* varScp() const { return m_varScp; }
    virtual string name() const { return (cvtToStr((void*)m_varScp)+" "+varScp()->name()); }
    virtual string dotColor() const { return "blue"; }
    void	setIsTop() { m_isTop = true; }
    void	setIsClock() { m_isClock = true; setConsumed("isclk"); }
    bool isTop() const { return m_isTop; }
    bool isClock() const { return m_isClock; }
};

class GateLogicVertex : public GateEitherVertex {
    AstNode*	m_nodep;
    AstActive*	m_activep;	// Under what active; NULL is ok (under cfunc or such)
    bool	m_slow;		// In slow block
public:
    GateLogicVertex(V3Graph* graphp, AstScope* scopep, AstNode* nodep, AstActive* activep, bool slow)
	: GateEitherVertex(graphp,scopep), m_nodep(nodep), m_activep(activep), m_slow(slow) {}
    virtual ~GateLogicVertex() {}
    // Accessors
    virtual string name() const { return (cvtToStr((void*)m_nodep)+"@"+scopep()->name()); }
    virtual string dotColor() const { return "yellow"; }
    AstNode* nodep() const { return m_nodep; }
    AstActive* activep() const { return m_activep; }
    bool	slow() const { return m_slow; }
};

//######################################################################
// Is this a simple math expression with a single input and single output?

class GateOkVisitor : public GateBaseVisitor {
private:
    // RETURN STATE
    bool		m_isSimple;	// Set false when we know it isn't simple
    GateVarRefList	m_rhsVarRefs;	// VarRefs on rhs of assignment
    AstNode*		m_substTreep;	// What to replace the variable with
    // STATE
    bool		m_buffersOnly;	// Set when we only allow simple buffering, no equations (for clocks)
    AstNodeVarRef*	m_lhsVarRef;	// VarRef on lhs of assignment (what we're replacing)

    // METHODS
    void clearSimple(const char* because) {
	if (m_isSimple) {
	    m_isSimple = false;
	    UINFO(9, "Clear simple "<<because<<endl);
	}
    }
    // VISITORS
    virtual void visit(AstNodeVarRef* nodep, AstNUser*) {
	nodep->iterateChildren(*this);
	// We only allow a LHS ref for the var being set, and a RHS ref for something else being read.
	if (nodep->varScopep()->varp()->isSc()) {
	    clearSimple("SystemC sig");  // Don't want to eliminate the VL_ASSIGN_SI's
	}
	if (nodep->lvalue()) {
	    if (m_lhsVarRef) clearSimple(">1 lhs varRefs");
	    m_lhsVarRef = nodep;
	} else {
	    if (m_rhsVarRefs.size()>1) {
		AstNodeVarRef* lastRefp = m_rhsVarRefs.back();
		if (0) { // Diable the multiple-input optimization
		    clearSimple(">1 rhs varRefs");
		} else {
		    if (m_buffersOnly) clearSimple(">1 rhs varRefs");
		    if (!nodep->varScopep()->varp()->gateMultiInputOptimizable()
			// We didn't check multiInput on the first varref, so check it here
			|| !lastRefp->varScopep()->varp()->gateMultiInputOptimizable()) {
			clearSimple("!gateMultiInputOptimizable");
		    }
		}
	    }
	    m_rhsVarRefs.push_back(nodep);
	}
    }
    virtual void visit(AstNodeAssign* nodep, AstNUser*) {
	m_substTreep = nodep->rhsp();
	if (!nodep->lhsp()->castNodeVarRef())
	    clearSimple("ASSIGN(non VARREF)");
	else nodep->iterateChildren(*this);
	// We don't push logic other then assignments/NOTs into SenItems
	// This avoids a mess in computing what exactly a POSEDGE is
	// V3Const cleans up any NOTs by flipping the edges for us
	if (m_buffersOnly
	    && !(nodep->rhsp()->castVarRef()
		 // Until NEW_ORDERING, avoid making non-clocked logic into clocked, 
		 // as it slows down the verilator_sim_benchmark
		 || (nodep->rhsp()->castNot()
		     && nodep->rhsp()->castNot()->lhsp()->castVarRef()
		     && nodep->rhsp()->castNot()->lhsp()->castVarRef()->varp()->isUsedClock())
		)) {
	    clearSimple("Not a buffer (goes to a clock)");
	}
    }
    //--------------------
    // Default
    virtual void visit(AstNode* nodep, AstNUser*) {
	// *** Special iterator
	if (!m_isSimple) return;	// Fastpath
	if (!nodep->isGateOptimizable()
	    || !nodep->isSplittable()) {
	    UINFO(5, "Non optimizable type: "<<nodep<<endl);
	    clearSimple("Non optimizable type");
	}
	else nodep->iterateChildren(*this);
    }
public:
    // CONSTUCTORS
    GateOkVisitor(AstNode* nodep, bool buffersOnly) {
	m_isSimple = true;
	m_substTreep = NULL;
	m_buffersOnly = buffersOnly;
	m_lhsVarRef = NULL;
	nodep->accept(*this);
	if (!m_substTreep) {
	    clearSimple("No assignment found\n");
	}
	if (debug()>=9 && !m_isSimple) {
	    nodep->dumpTree(cout,"\tgate!Ok: ");
	}
    }
    virtual ~GateOkVisitor() {}
    // PUBLIC METHODS
    bool isSimple() const { return m_isSimple; }
    AstNode* substTree() const { return m_substTreep; }
    const GateVarRefList& rhsVarRefs() const {
	return m_rhsVarRefs;
    }
};

//######################################################################
// Gate class functions

class GateVisitor : public GateBaseVisitor {
private:
    // NODE STATE
    //Entire netlist:
    // AstVarScope::userp	-> GateVarVertex* for usage var, 0=not set yet
    // {statement}Node::userp	-> GateLogicVertex* for this statement
    // STATE
    V3Graph		m_graph;	// Scoreboard of var usages/dependencies
    GateLogicVertex*	m_logicVertexp;	// Current statement being tracked, NULL=ignored
    AstScope*		m_scopep;	// Current scope being processed
    AstModule*		m_modp;		// Current module
    AstActive*		m_activep;	// Current active
    bool		m_activeReducible;	// Is activation block reducible?
    bool		m_inSenItem;	// Underneath AstSenItem; any varrefs are clocks
    bool		m_inSlow;	// Inside a slow structure
    V3Double0		m_statSigs;	// Statistic tracking
    V3Double0		m_statRefs;	// Statistic tracking

    // METHODS
    void iterateNewStmt(AstNode* nodep, const char* nonReducibleReason, const char* consumeReason) {
	if (m_scopep) {
	    UINFO(4,"   STMT "<<nodep<<endl);
	    // m_activep is null under AstCFunc's, that's ok.
	    m_logicVertexp = new GateLogicVertex(&m_graph, m_scopep, nodep, m_activep, m_inSlow);
	    if (!m_activeReducible) nonReducibleReason="Block Unreducible";
	    if (nonReducibleReason) {
		m_logicVertexp->clearReducible(nonReducibleReason);
	    }
	    if (consumeReason) m_logicVertexp->setConsumed(consumeReason);
	    if (nodep->castSenItem()) m_logicVertexp->setConsumed("senItem");
	    nodep->iterateChildren(*this);
	    m_logicVertexp = NULL;
	}
    }

    GateVarVertex* makeVarVertex(AstVarScope* varscp) {
	GateVarVertex* vertexp = (GateVarVertex*)(varscp->userp());
	if (!vertexp) {
	    UINFO(6,"New vertex "<<varscp<<endl);
	    vertexp = new GateVarVertex(&m_graph, m_scopep, varscp);
	    varscp->userp(vertexp);
	    if (varscp->varp()->isSigPublic()) {
		// Public signals shouldn't be changed, pli code might be messing with them
		vertexp->clearReducible("SigPublic");
		vertexp->setConsumed("SigPublic");
	    }
	    if (varscp->varp()->isIO() && varscp->scopep()->isTop()) {
		// We may need to convert to/from sysc/reg sigs
		vertexp->setIsTop();
		vertexp->clearReducible("isTop");
		vertexp->setConsumed("isTop");
	    }
	    if (varscp->varp()->isUsedClock()) 	vertexp->setConsumed("clock");
	}
	if (m_inSenItem) vertexp->setIsClock();
	return vertexp;
    }

    void optimizeSignals(bool allowMultiIn);
    void optimizeElimVar(AstVarScope* varscp, AstNode* logicp, AstNode* consumerp);
    void consumedMark();
    void consumedMarkRecurse(GateEitherVertex* vertexp);
    void consumedMove();
    void replaceAssigns();

    // VISITORS
    virtual void visit(AstNetlist* nodep, AstNUser*) {
	//VV*****  We reset userp() and user2p
	AstNode::userClearTree();
	nodep->iterateChildren(*this);
	//if (debug()>6) m_graph.dump();
	if (debug()>6) m_graph.dumpDotFilePrefixed("gate_pre");
	m_graph.removeRedundantEdgesSum(&V3GraphEdge::followAlwaysTrue);
	m_graph.dumpDotFilePrefixed("gate_simp");
	// Find gate interconnect and optimize
	m_graph.userClearVertices();	// vertex->user(): bool.  True indicates we've set it as consumed
	// Get rid of buffers first,
	optimizeSignals(false);
	// Then propagate more complicated equations
	optimizeSignals(true);
	consumedMark();
	m_graph.dumpDotFilePrefixed("gate_opt");
	// Rewrite assignments
	consumedMove();
	replaceAssigns();
    }
    virtual void visit(AstModule* nodep, AstNUser*) {
	m_modp = nodep;
	m_activeReducible = true;
	nodep->iterateChildren(*this);
    }
    virtual void visit(AstScope* nodep, AstNUser*) {
	UINFO(4," SCOPE "<<nodep<<endl);
	m_scopep = nodep;
	m_logicVertexp = NULL;
	nodep->iterateChildren(*this);
	m_scopep = NULL;
    }
    virtual void visit(AstActive* nodep, AstNUser*) {
	// Create required blocks and add to module
	UINFO(4,"  BLOCK  "<<nodep<<endl);
	m_activeReducible = !(nodep->hasClocked());  // Seq logic outputs aren't reducible
	m_activep = nodep;
	nodep->iterateChildren(*this);
	m_activep = NULL;
	m_activeReducible = true;
    }
    virtual void visit(AstNodeVarRef* nodep, AstNUser*) {
	if (m_scopep) {
	    if (!m_logicVertexp) nodep->v3fatalSrc("Var ref not under a logic block\n");
	    AstVarScope* varscp = nodep->varScopep();
	    if (!varscp) nodep->v3fatalSrc("Var didn't get varscoped in V3Scope.cpp\n");
	    GateVarVertex* varvertexp = makeVarVertex(varscp);
	    UINFO(5," VARREF to "<<varscp<<endl);
	    // We use weight of one; if we ref the var more then once, when we simplify,
	    // the weight will increase
	    if (nodep->lvalue()) {	
		new V3GraphEdge(&m_graph, m_logicVertexp, varvertexp, 1);
	    } else {
		new V3GraphEdge(&m_graph, varvertexp, m_logicVertexp, 1);
	    }
	}
    }
    virtual void visit(AstAlways* nodep, AstNUser*) {
	iterateNewStmt(nodep, (nodep->isJustOneBodyStmt()?NULL:"Multiple Stmts"), NULL);
    }
    virtual void visit(AstCFunc* nodep, AstNUser*) {
	iterateNewStmt(nodep, "User C Function", "User C Function");
    }
    virtual void visit(AstSenItem* nodep, AstNUser*) {
	m_inSenItem = true;
	iterateNewStmt(nodep, NULL, NULL);
	m_inSenItem = false;
    }
    virtual void visit(AstInitial* nodep, AstNUser*) {
	bool lastslow = m_inSlow;
	m_inSlow = true;
	iterateNewStmt(nodep, (nodep->isJustOneBodyStmt()?NULL:"Multiple Stmts"), NULL);
	m_inSlow = lastslow;
    }
    virtual void visit(AstAssignAlias* nodep, AstNUser*) {
	iterateNewStmt(nodep, NULL, NULL);
    }
    virtual void visit(AstAssignW* nodep, AstNUser*) {
	iterateNewStmt(nodep, NULL, NULL);
    }
    virtual void visit(AstTraceInc* nodep, AstNUser*) {
	bool lastslow = m_inSlow;
	m_inSlow = true;
	iterateNewStmt(nodep, "Tracing", "Tracing");
	m_inSlow = lastslow;
    }
    virtual void visit(AstConcat* nodep, AstNUser*) {
	if (nodep->backp()->castNodeAssign() && nodep->backp()->castNodeAssign()->lhsp()==nodep) {
	    nodep->v3fatalSrc("Concat on LHS of assignment; V3Const should have deleted it\n");
	}
	nodep->iterateChildren(*this);
    }

    //--------------------
    // Default
    virtual void visit(AstNode* nodep, AstNUser*) {
	nodep->iterateChildren(*this);
	if (nodep->isOutputter() && m_logicVertexp) m_logicVertexp->setConsumed("outputter");
    }

public:
    // CONSTUCTORS
    GateVisitor(AstNode* nodep) {
	m_logicVertexp = NULL;
	m_scopep = NULL;
	m_modp = NULL;
	m_activep = NULL;
	m_activeReducible = true;
	m_inSenItem = false;
	m_inSlow = false;
	nodep->accept(*this);
    }
    virtual ~GateVisitor() {
	V3Stats::addStat("Optimizations, Gate sigs deleted", m_statSigs);
	V3Stats::addStat("Optimizations, Gate inputs replaced", m_statRefs);
    }
};

//----------------------------------------------------------------------

void GateVisitor::optimizeSignals(bool allowMultiIn) {
    for (V3GraphVertex* itp = m_graph.verticesBeginp(); itp; itp=itp->verticesNextp()) {
	if (GateVarVertex* vvertexp = dynamic_cast<GateVarVertex*>(itp)) {
	    if (vvertexp->inEmpty()) {
		vvertexp->clearReducible("inEmpty");	// Can't deal with no sources
		if (!vvertexp->isTop()		// Ok if top inputs are driverless
		    && !vvertexp->varScp()->varp()->initp()
		    && !vvertexp->varScp()->varp()->isSigPublic()) {
		    UINFO(1, "No drivers "<<vvertexp->varScp()<<endl);
		    if (0) {
			// If we warned here after constant propagation, what the user considered
			// reasonable logic may have disappeared.  Issuing a warning would
			// thus be confusing.
			vvertexp->varScp()->varp()->v3warn(UNDRIVEN,"Signal has no drivers "
							   <<vvertexp->scopep()->prettyName()<<"."
							   <<vvertexp->varScp()->varp()->prettyName());
		    }
		}
	    }
	    else if (!vvertexp->inSize1()) {
		vvertexp->clearReducible("size!1");	// Can't deal with more then one src
	    }
	    // Reduce it?
	    if (!vvertexp->reducible()) {
		UINFO(8, "SigNotRed "<<vvertexp->name()<<endl);
	    } else {
		UINFO(8, "Sig "<<vvertexp->name()<<endl);
		GateLogicVertex* logicVertexp = dynamic_cast<GateLogicVertex*>
		    (vvertexp->inBeginp()->fromp());
		UINFO(8, "  From "<<logicVertexp->name()<<endl);
		AstNode* logicp = logicVertexp->nodep();
		if (logicVertexp->reducible()) {
		    // Can we eliminate?
		    GateOkVisitor okVisitor(logicp, vvertexp->isClock());
		    bool multiInputs = okVisitor.rhsVarRefs().size() > 1;
		    // Was it ok?
		    bool doit = okVisitor.isSimple();
		    if (doit && multiInputs) {
			if (!allowMultiIn) doit = false;
			// Doit if one input, or not used, or used only once, ignoring traces
			int n=0;
			for (V3GraphEdge* edgep = vvertexp->outBeginp(); edgep; edgep = edgep->outNextp()) {
			    GateLogicVertex* consumeVertexp = dynamic_cast<GateLogicVertex*>(edgep->top());
			    if (!consumeVertexp->slow()) { // Not tracing or other slow path junk
				if (edgep->top()->outBeginp()) {  // Destination is itself used
				    n += edgep->weight();
				}
			    }
			    if (n>1) {
				doit = false;
				break;
			    }
			}
		    }
		    if (!doit) {
			if (allowMultiIn && (debug()>=9)) {
			    UINFO(9, "Not ok simp"<<okVisitor.isSimple()<<" mi"<<multiInputs
				  <<" ob"<<vvertexp->outBeginp()<<" on"<<(vvertexp->outBeginp()?vvertexp->outBeginp()->outNextp():0)
				  <<" "<<vvertexp->name()
				  <<endl);
			    for (V3GraphEdge* edgep = vvertexp->outBeginp(); edgep; edgep = edgep->outNextp()) {
				GateLogicVertex* consumeVertexp = dynamic_cast<GateLogicVertex*>(edgep->top());
				UINFO(9, "    edge "<<edgep<<" to: "<<consumeVertexp->nodep()<<endl);
			    }
			    for (V3GraphEdge* edgep = vvertexp->inBeginp(); edgep; edgep = edgep->inNextp()) {
				GateLogicVertex* consumeVertexp = dynamic_cast<GateLogicVertex*>(edgep->fromp());
				UINFO(9, "    edge "<<edgep<<" from: "<<consumeVertexp->nodep()<<endl);
			    }
			}
		    }
		    else {
			AstNode* substp = okVisitor.substTree();
			if (debug()>=5) logicp->dumpTree(cout,"\telimVar:  ");
			if (debug()>=5) substp->dumpTree(cout,"\t  subst:  ");
			m_statSigs++;
			while (V3GraphEdge* edgep = vvertexp->outBeginp()) {
 			    GateLogicVertex* consumeVertexp = dynamic_cast<GateLogicVertex*>(edgep->top());
			    AstNode* consumerp = consumeVertexp->nodep();
			    optimizeElimVar(vvertexp->varScp(), substp, consumerp);
			    // If the new replacement referred to a signal,
			    // Correct the graph to point to this new generating variable
			    for (GateVarRefList::const_iterator it = okVisitor.rhsVarRefs().begin();
				 it != okVisitor.rhsVarRefs().end(); ++it) {
				AstVarScope* newvarscp = (*it)->varScopep();
				UINFO(9,"         Point-to-new vertex "<<newvarscp<<endl);
				GateVarVertex* varvertexp = makeVarVertex(newvarscp);
				new V3GraphEdge(&m_graph, varvertexp, consumeVertexp, 1);
				newvarscp->varp()->propagateAttrFrom(vvertexp->varScp()->varp());
				if (vvertexp->isClock()) {
				    // Propagate clock attribute onto generating node
				    newvarscp->varp()->usedClock(true);
				    varvertexp->setIsClock();
				}
			    }
			    // Remove the edge
			    edgep->unlinkDelete(); edgep=NULL;
			    m_statRefs++;
			}
			// Remove input links
			while (V3GraphEdge* edgep = vvertexp->inBeginp()) {
			    edgep->unlinkDelete(); edgep=NULL;
			}
			// Clone tree so we remember it for tracing, and keep the pointer
			// to the "ALWAYS" part of the tree as part of this statement
			// That way if a later signal optimization that retained a pointer to the always
			// can optimize it further
			logicp->unlinkFrBack();
			vvertexp->varScp()->valuep(logicp);
			logicp = NULL;
			// Mark the vertex so we don't mark it as being unconsumed in the next step
			vvertexp->user(true);
			logicVertexp->user(true);
		    }
		}
	    }
	}
    }
}

void GateVisitor::replaceAssigns() {
    for (V3GraphVertex* itp = m_graph.verticesBeginp(); itp; itp=itp->verticesNextp()) {
	if (GateVarVertex* vvertexp = dynamic_cast<GateVarVertex*>(itp)) {
	    // Take the Comments/assigns that were moved to the VarScope and change them to a
	    // simple value assignment
	    AstVarScope* vscp = vvertexp->varScp();
	    if (vscp->valuep() && !vscp->valuep()->castNodeMath()) {
		//if (debug()>9) vscp->dumpTree(cout, "-vscPre:  ");
		while (AstNode* delp=vscp->valuep()->castComment()) {
		    delp->unlinkFrBack()->deleteTree(); delp=NULL;
		}
		if (AstInitial* delp=vscp->valuep()->castInitial()) {
		    AstNode* bodyp=delp->bodysp();
		    bodyp->unlinkFrBackWithNext();
		    delp->replaceWith(bodyp);
		    delp->deleteTree(); delp=NULL;
		}
		if (AstAlways* delp=vscp->valuep()->castAlways()) {
		    AstNode* bodyp=delp->bodysp();
		    bodyp->unlinkFrBackWithNext();
		    delp->replaceWith(bodyp);
		    delp->deleteTree(); delp=NULL;
		}
		if (AstNodeAssign* delp=vscp->valuep()->castNodeAssign()) {
		    AstNode* rhsp=delp->rhsp();
		    rhsp->unlinkFrBack();
		    delp->replaceWith(rhsp);
		    delp->deleteTree(); delp=NULL;
		}
		//if (debug()>9) {vscp->dumpTree(cout, "-vscDone: "); cout<<endl;}
		if (!vscp->valuep()->castNodeMath()
		    || vscp->valuep()->nextp()) {
		    vscp->dumpTree(cout, "vscStrange: ");
		    vscp->v3fatalSrc("Value of varscope not mathematical\n");
		}
	    }
	}
    }
}

//----------------------------------------------------------------------

void GateVisitor::consumedMark() {
    // Propagate consumed signals backwards to all producers into a consumed node
    m_graph.userClearVertices();
    for (V3GraphVertex* vertexp = m_graph.verticesBeginp(); vertexp; vertexp=vertexp->verticesNextp()) {
	GateEitherVertex* evertexp = (GateEitherVertex*)vertexp;
	if (!evertexp->user() && evertexp->consumed()) {
	    consumedMarkRecurse(evertexp);
	}
    }
}

void GateVisitor::consumedMarkRecurse(GateEitherVertex* vertexp) {
    if (vertexp->user()) return;	// Already marked
    vertexp->user(true);
    if (!vertexp->consumed()) vertexp->setConsumed("propagated");
    // Walk sources and mark them too
    for (V3GraphEdge* edgep = vertexp->inBeginp(); edgep; edgep = edgep->inNextp()) {
	GateEitherVertex* eFromVertexp = (GateEitherVertex*)edgep->fromp();
	consumedMarkRecurse(eFromVertexp);
    }
}

void GateVisitor::consumedMove() {
    // Remove unused logic (logic that doesn't hit a combo block or a display statement)
    // We need the "usually" block logic to do a better job at this
    for (V3GraphVertex* vertexp = m_graph.verticesBeginp(); vertexp; vertexp=vertexp->verticesNextp()) {
	if (GateVarVertex* vvertexp = dynamic_cast<GateVarVertex*>(vertexp)) {
	    if (!vvertexp->consumed() && !vvertexp->user()) {
		UINFO(8, "Unconsumed "<<vvertexp->varScp()<<endl);
	    }
	}
	if (GateLogicVertex* lvertexp = dynamic_cast<GateLogicVertex*>(vertexp)) {
	    AstNode* nodep = lvertexp->nodep();
	    AstActive* oldactp = lvertexp->activep();  // NULL under cfunc
	    if (!lvertexp->consumed() && oldactp) {
		// Eventually: Move the statement to a new active block with "tracing-on" sensitivity
		UINFO(8,"    Remove unconsumed "<<nodep<<endl);
		nodep->unlinkFrBack();
		pushDeletep(nodep); nodep=NULL;
	    }
	}
    }
}

//######################################################################
// Push constant into expressions and reevaluate

class GateElimVisitor : public GateBaseVisitor {
private:
    // NODE STATE
    // STATE
    AstVarScope* m_elimVarScp;		// Variable being eliminated
    AstNode*	 m_replaceTreep;	// What to replace the variable with
    bool	 m_didReplace;		// Did we do any replacements
    // VISITORS
    virtual void visit(AstNodeVarRef* nodep, AstNUser*) {
	if (nodep->varScopep() == m_elimVarScp) {
	    // Substitute in the new tree
	    // It's possible we substitute into something that will be reduced more later
	    // however, as we never delete the top Always/initial statement, all should be well.
	    m_didReplace = true;
	    if (nodep->lvalue()) nodep->v3fatalSrc("Can't replace lvalue assignments with const var");
	    AstNode* substp = m_replaceTreep->cloneTree(false);
	    if (nodep->castNodeVarRef()
		&& substp->castNodeVarRef()
		&& nodep->same(substp)) {
		// Prevent a infinite loop...
		substp->v3fatalSrc("Replacing node with itself; perhaps circular logic?");
	    }
	    nodep->replaceWith(substp);
	    nodep->deleteTree(); nodep=NULL;
	}
    }
    virtual void visit(AstNode* nodep, AstNUser*) {
	nodep->iterateChildren(*this);
    }
public:
    // CONSTUCTORS
    virtual ~GateElimVisitor() {}
    GateElimVisitor(AstNode* nodep, AstVarScope* varscp, AstNode* replaceTreep) {
	m_didReplace = false;
	m_elimVarScp = varscp;
	m_replaceTreep = replaceTreep;
	nodep->accept(*this);
    }
    bool didReplace() const { return m_didReplace; }
};

void GateVisitor::optimizeElimVar(AstVarScope* varscp, AstNode* substp, AstNode* consumerp) {
    if (debug()>=5) consumerp->dumpTree(cout,"\telimUsePre: ");
    GateElimVisitor elimVisitor (consumerp, varscp, substp);
    if (elimVisitor.didReplace()) {
	if (debug()>=9) consumerp->dumpTree(cout,"\telimUseCns: ");
	//Caution: Can't let V3Const change our handle to consumerp, such as by
	// optimizing away this assignment, etc.
	V3Const::constifyTree(consumerp);
	if (debug()>=5) consumerp->dumpTree(cout,"\telimUseDne: ");
    }
}

//######################################################################
// Convert VARSCOPE(ASSIGN(default, VARREF)) to just VARSCOPE(default)

class GateDeassignVisitor : public GateBaseVisitor {
private:
    // VISITORS
    virtual void visit(AstVarScope* nodep, AstNUser*) {
	if (AstNodeAssign* assp = nodep->valuep()->castNodeAssign()) {
	    UINFO(5," Removeassign "<<assp<<endl);
	    AstNode* valuep = assp->rhsp();
	    valuep->unlinkFrBack();
	    assp->replaceWith(valuep);
	    assp->deleteTree(); assp=NULL;
	}
    }
    // Speedups
    virtual void visit(AstVar* nodep, AstNUser*) {}
    virtual void visit(AstActive* nodep, AstNUser*) {}
    virtual void visit(AstNode* nodep, AstNUser*) {
	nodep->iterateChildren(*this);
    }

public:
    // CONSTUCTORS
    GateDeassignVisitor(AstNode* nodep) {
	nodep->accept(*this);
    }
    virtual ~GateDeassignVisitor() {}
};

//######################################################################
// Gate class functions

void V3Gate::gateAll(AstNetlist* nodep) {
    UINFO(2,__FUNCTION__<<": "<<endl);
    GateVisitor visitor (nodep);
    GateDeassignVisitor deassign (nodep);
}
