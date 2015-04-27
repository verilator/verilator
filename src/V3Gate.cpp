// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Gate optimizations, such as wire elimination
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
// V3Gate's Transformations:
//
// Extract a graph of the *entire* netlist with cells expanded
// Perform constant optimization across the graph
// Create VARSCOPEs for any variables we can rip out
//
//*************************************************************************

#include "config_build.h"
#include "verilatedos.h"
#include <cstdio>
#include <cstdarg>
#include <unistd.h>
#include <algorithm>
#include <iomanip>
#include <vector>
#include <list>
#include <map>

#include "V3Global.h"
#include "V3Gate.h"
#include "V3Ast.h"
#include "V3Graph.h"
#include "V3Const.h"
#include "V3Stats.h"
#include "V3Hashed.h"

typedef list<AstNodeVarRef*> GateVarRefList;

//######################################################################

class GateBaseVisitor : public AstNVisitor {
public:
    static int debug() {
	static int level = -1;
	if (VL_UNLIKELY(level < 0)) level = v3Global.opt.debugSrcLevel(__FILE__);
	return level;
    }
};

//######################################################################

class GateLogicVertex;
class GateVarVertex;
class GateGraphBaseVisitor {
public:
    virtual AstNUser* visit(GateLogicVertex* vertexp, AstNUser* vup=NULL) =0;
    virtual AstNUser* visit(GateVarVertex* vertexp, AstNUser* vup=NULL) =0;
    virtual ~GateGraphBaseVisitor() {}
};

//######################################################################
// Support classes

class GateEitherVertex : public V3GraphVertex {
    AstScope*	m_scopep;
    bool	m_reducible;	// True if this node should be able to be eliminated
    bool	m_dedupable;	// True if this node should be able to be deduped
    bool	m_consumed;		// Output goes to something meaningful
public:
    GateEitherVertex(V3Graph* graphp, AstScope* scopep)
	: V3GraphVertex(graphp), m_scopep(scopep), m_reducible(true), m_dedupable(true), m_consumed(false) {}
    virtual ~GateEitherVertex() {}
    // ACCESSORS
    virtual string dotStyle() const { return m_consumed?"":"dotted"; }
    AstScope* scopep() const { return m_scopep; }
    bool reducible() const { return m_reducible; }
    bool dedupable() const { return m_dedupable; }
    void setConsumed(const char* consumedReason) {
	m_consumed = true;
	//UINFO(0,"\t\tSetConsumed "<<consumedReason<<" "<<this<<endl);
    }
    bool consumed() const { return m_consumed; }
    void clearReducible(const char* nonReducibleReason) {
	m_reducible = false;
	//UINFO(0,"     NR: "<<nonReducibleReason<<"  "<<name()<<endl);
    }
    void clearDedupable(const char* nonDedupableReason) {
	m_dedupable = false;
	//UINFO(0,"     ND: "<<nonDedupableReason<<"  "<<name()<<endl);
    }
    void clearReducibleAndDedupable(const char* nonReducibleReason) {
	clearReducible(nonReducibleReason);
	clearDedupable(nonReducibleReason);
    }
    virtual AstNUser* accept(GateGraphBaseVisitor& v, AstNUser* vup=NULL) =0;
    // Returns only the result from the LAST vertex iterated over
    AstNUser* iterateInEdges(GateGraphBaseVisitor& v, AstNUser* vup=NULL) {
	AstNUser* retp = NULL;
	for (V3GraphEdge* edgep = inBeginp(); edgep; edgep = edgep->inNextp()) {
	    retp = dynamic_cast<GateEitherVertex*>(edgep->fromp())->accept(v, vup);
	}
	return retp;
    }
};

class GateVarVertex : public GateEitherVertex {
    AstVarScope* m_varScp;
    bool	 m_isTop;
    bool	 m_isClock;
    AstNode*	 m_rstSyncNodep;	// Used as reset and not in SenItem, in clocked always
    AstNode*	 m_rstAsyncNodep;	// Used as reset and in SenItem, in clocked always
public:
    GateVarVertex(V3Graph* graphp, AstScope* scopep, AstVarScope* varScp)
	: GateEitherVertex(graphp, scopep), m_varScp(varScp), m_isTop(false)
	, m_isClock(false), m_rstSyncNodep(NULL), m_rstAsyncNodep(NULL) {}
    virtual ~GateVarVertex() {}
    // ACCESSORS
    AstVarScope* varScp() const { return m_varScp; }
    virtual string name() const { return (cvtToStr((void*)m_varScp)+" "+varScp()->name()); }
    virtual string dotColor() const { return "blue"; }
    bool isTop() const { return m_isTop; }
    void setIsTop() { m_isTop = true; }
    bool isClock() const { return m_isClock; }
    void setIsClock() { m_isClock = true; setConsumed("isclk"); }
    AstNode* rstSyncNodep() const { return m_rstSyncNodep; }
    void rstSyncNodep(AstNode* nodep) { m_rstSyncNodep=nodep; }
    AstNode* rstAsyncNodep() const { return m_rstAsyncNodep; }
    void rstAsyncNodep(AstNode* nodep) { m_rstAsyncNodep=nodep; }
    // METHODS
    void propagateAttrClocksFrom(GateVarVertex* fromp) {
	// Propagate clock and general attribute onto this node
	varScp()->varp()->propagateAttrFrom(fromp->varScp()->varp());
	if (fromp->isClock()) {
	    varScp()->varp()->usedClock(true);
	    setIsClock();
	}
    }
    AstNUser* accept(GateGraphBaseVisitor& v, AstNUser* vup=NULL) { return v.visit(this,vup); }
};

class GateLogicVertex : public GateEitherVertex {
    AstNode*	m_nodep;
    AstActive*	m_activep;	// Under what active; NULL is ok (under cfunc or such)
    bool	m_slow;		// In slow block
public:
    GateLogicVertex(V3Graph* graphp, AstScope* scopep, AstNode* nodep, AstActive* activep, bool slow)
	: GateEitherVertex(graphp,scopep), m_nodep(nodep), m_activep(activep), m_slow(slow) {}
    virtual ~GateLogicVertex() {}
    // ACCESSORS
    virtual string name() const { return (cvtToStr((void*)m_nodep)+"@"+scopep()->prettyName()); }
    virtual string dotColor() const { return "yellow"; }
    AstNode* nodep() const { return m_nodep; }
    AstActive* activep() const { return m_activep; }
    bool	slow() const { return m_slow; }
    AstNUser* accept(GateGraphBaseVisitor& v, AstNUser* vup=NULL) { return v.visit(this,vup); }
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
    bool		m_dedupe;	// Set when we use isGateDedupable instead of isGateOptimizable

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
	    clearSimple("ASSIGN(non-VARREF)");
	else nodep->iterateChildren(*this);
	// We don't push logic other then assignments/NOTs into SenItems
	// This avoids a mess in computing what exactly a POSEDGE is
	// V3Const cleans up any NOTs by flipping the edges for us
	if (m_buffersOnly
	    && !(nodep->rhsp()->castVarRef()
		 // Avoid making non-clocked logic into clocked,
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
	if (!(m_dedupe ? nodep->isGateDedupable() : nodep->isGateOptimizable())
	    || !nodep->isPure()
	    || nodep->isBrancher()) {
	    UINFO(5, "Non optimizable type: "<<nodep<<endl);
	    clearSimple("Non optimizable type");
	}
	else nodep->iterateChildren(*this);
    }
public:
    // CONSTUCTORS
    GateOkVisitor(AstNode* nodep, bool buffersOnly, bool dedupe) {
	m_isSimple = true;
	m_substTreep = NULL;
	m_buffersOnly = buffersOnly;
	m_lhsVarRef = NULL;
	m_dedupe = dedupe;
	// Iterate
	nodep->accept(*this);
	// Check results
	if (!m_substTreep) {
	    clearSimple("No assignment found\n");
	}
	for (GateVarRefList::const_iterator it = m_rhsVarRefs.begin();
	     it != m_rhsVarRefs.end(); ++it) {
	    if (m_lhsVarRef && m_lhsVarRef->varScopep() == (*it)->varScopep()) {
		clearSimple("Circular logic\n");  // Oh my, we'll get a UNOPTFLAT much later.
	    }
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
    // AstVarScope::user1p	-> GateVarVertex* for usage var, 0=not set yet
    // {statement}Node::user1p	-> GateLogicVertex* for this statement
    // AstVarScope::user2	-> bool: Signal used in SenItem in *this* always statement
    // AstVar::user2		-> bool: Warned about SYNCASYNCNET
    AstUser1InUse	m_inuser1;
    AstUser2InUse	m_inuser2;

    // STATE
    V3Graph		m_graph;	// Scoreboard of var usages/dependencies
    GateLogicVertex*	m_logicVertexp;	// Current statement being tracked, NULL=ignored
    AstScope*		m_scopep;	// Current scope being processed
    AstNodeModule*	m_modp;		// Current module
    AstActive*		m_activep;	// Current active
    bool		m_activeReducible;	// Is activation block reducible?
    bool		m_inSenItem;	// Underneath AstSenItem; any varrefs are clocks
    bool		m_inSlow;	// Inside a slow structure
    V3Double0		m_statSigs;	// Statistic tracking
    V3Double0		m_statRefs;	// Statistic tracking
    V3Double0		m_statDedupLogic;	// Statistic tracking
    V3Double0		m_statAssignMerged;	// Statistic tracking

    // METHODS
    void iterateNewStmt(AstNode* nodep, const char* nonReducibleReason, const char* consumeReason) {
	if (m_scopep) {
	    UINFO(4,"   STMT "<<nodep<<endl);
	    // m_activep is null under AstCFunc's, that's ok.
	    m_logicVertexp = new GateLogicVertex(&m_graph, m_scopep, nodep, m_activep, m_inSlow);
	    if (nonReducibleReason) {
		m_logicVertexp->clearReducibleAndDedupable(nonReducibleReason);
	    } else if (!m_activeReducible) {
		m_logicVertexp->clearReducible("Block Unreducible");  // Sequential logic is dedupable
	    }
	    if (consumeReason) m_logicVertexp->setConsumed(consumeReason);
	    if (nodep->castSenItem()) m_logicVertexp->setConsumed("senItem");
	    nodep->iterateChildren(*this);
	    m_logicVertexp = NULL;
	}
    }

    GateVarVertex* makeVarVertex(AstVarScope* varscp) {
	GateVarVertex* vertexp = (GateVarVertex*)(varscp->user1p());
	if (!vertexp) {
	    UINFO(6,"New vertex "<<varscp<<endl);
	    vertexp = new GateVarVertex(&m_graph, m_scopep, varscp);
	    varscp->user1p(vertexp);
	    if (varscp->varp()->isSigPublic()) {
		// Public signals shouldn't be changed, pli code might be messing with them
		vertexp->clearReducibleAndDedupable("SigPublic");
		vertexp->setConsumed("SigPublic");
	    }
	    if (varscp->varp()->isIO() && varscp->scopep()->isTop()) {
		// We may need to convert to/from sysc/reg sigs
		vertexp->setIsTop();
		vertexp->clearReducibleAndDedupable("isTop");
		vertexp->setConsumed("isTop");
	    }
	    if (varscp->varp()->isUsedClock()) 	vertexp->setConsumed("clock");
	}
	return vertexp;
    }

    void optimizeSignals(bool allowMultiIn);
    bool elimLogicOkOutputs(GateLogicVertex* consumeVertexp, const GateOkVisitor& okVisitor);
    void optimizeElimVar(AstVarScope* varscp, AstNode* logicp, AstNode* consumerp);
    void warnSignals();
    void consumedMark();
    void consumedMarkRecurse(GateEitherVertex* vertexp);
    void consumedMove();
    void replaceAssigns();
    void dedupe();
    void mergeAssigns();

    // VISITORS
    virtual void visit(AstNetlist* nodep, AstNUser*) {
	nodep->iterateChildren(*this);
	//if (debug()>6) m_graph.dump();
	if (debug()>6) m_graph.dumpDotFilePrefixed("gate_pre");
	warnSignals();  // Before loss of sync/async pointers
	m_graph.removeRedundantEdgesSum(&V3GraphEdge::followAlwaysTrue);
	m_graph.dumpDotFilePrefixed("gate_simp");
	// Find gate interconnect and optimize
	m_graph.userClearVertices();	// vertex->user(): bool.  True indicates we've set it as consumed
	// Get rid of buffers first,
	optimizeSignals(false);
	// Then propagate more complicated equations
	optimizeSignals(true);
	// Remove redundant logic
	if (v3Global.opt.oDedupe()) dedupe();
	if (v3Global.opt.oAssemble()) mergeAssigns();
	// Consumption warnings
	consumedMark();
	m_graph.dumpDotFilePrefixed("gate_opt");
	// Rewrite assignments
	consumedMove();
	replaceAssigns();
    }
    virtual void visit(AstNodeModule* nodep, AstNUser*) {
	m_modp = nodep;
	m_activeReducible = true;
	nodep->iterateChildren(*this);
	m_modp = NULL;
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
	AstNode::user2ClearTree();
	nodep->iterateChildren(*this);
	AstNode::user2ClearTree();
	m_activep = NULL;
	m_activeReducible = true;
    }
    virtual void visit(AstNodeVarRef* nodep, AstNUser*) {
	if (m_scopep) {
	    if (!m_logicVertexp) nodep->v3fatalSrc("Var ref not under a logic block\n");
	    AstVarScope* varscp = nodep->varScopep();
	    if (!varscp) nodep->v3fatalSrc("Var didn't get varscoped in V3Scope.cpp\n");
	    GateVarVertex* vvertexp = makeVarVertex(varscp);
	    UINFO(5," VARREF to "<<varscp<<endl);
	    if (m_inSenItem) vvertexp->setIsClock();
	    // For SYNCASYNCNET
	    if (m_inSenItem) varscp->user2(true);
	    else if (m_activep && m_activep->hasClocked() && !nodep->lvalue()) {
		if (varscp->user2()) {
		    if (!vvertexp->rstSyncNodep()) vvertexp->rstSyncNodep(nodep);
		} else {
		    if (!vvertexp->rstAsyncNodep()) vvertexp->rstAsyncNodep(nodep);
		}
	    }
	    // We use weight of one; if we ref the var more than once, when we simplify,
	    // the weight will increase
	    if (nodep->lvalue()) {
		new V3GraphEdge(&m_graph, m_logicVertexp, vvertexp, 1);
	    } else {
		new V3GraphEdge(&m_graph, vvertexp, m_logicVertexp, 1);
	    }
	}
    }
    virtual void visit(AstAlways* nodep, AstNUser*) {
	iterateNewStmt(nodep, (nodep->isJustOneBodyStmt()?NULL:"Multiple Stmts"), NULL);
    }
    virtual void visit(AstAlwaysPublic* nodep, AstNUser*) {
	bool lastslow = m_inSlow;
	m_inSlow = true;
	iterateNewStmt(nodep, "AlwaysPublic", NULL);
	m_inSlow = lastslow;
    }
    virtual void visit(AstCFunc* nodep, AstNUser*) {
	iterateNewStmt(nodep, "User C Function", "User C Function");
    }
    virtual void visit(AstSenItem* nodep, AstNUser*) {
	// Note we look at only AstSenItems, not AstSenGate's
	// The gating term of a AstSenGate is normal logic
	m_inSenItem = true;
	if (m_logicVertexp) {  // Already under logic; presumably a SenGate
	    nodep->iterateChildren(*this);
	} else {  // Standalone item, probably right under a SenTree
	    iterateNewStmt(nodep, NULL, NULL);
	}
	m_inSenItem = false;
    }
    virtual void visit(AstSenGate* nodep, AstNUser*) {
	// First handle the clock part will be handled in a minute by visit AstSenItem
	// The logic gating term is delt with as logic
	iterateNewStmt(nodep, "Clock gater", "Clock gater");
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
    virtual void visit(AstCoverToggle* nodep, AstNUser*) {
	iterateNewStmt(nodep, "CoverToggle", "CoverToggle");
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
	AstNode::user1ClearTree();
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
	V3Stats::addStat("Optimizations, Gate sigs deduped", m_statDedupLogic);
	V3Stats::addStat("Optimizations, Gate assign merged", m_statAssignMerged);
    }
};

//----------------------------------------------------------------------

void GateVisitor::optimizeSignals(bool allowMultiIn) {
    for (V3GraphVertex* itp = m_graph.verticesBeginp(); itp; itp=itp->verticesNextp()) {
	if (GateVarVertex* vvertexp = dynamic_cast<GateVarVertex*>(itp)) {
	    if (vvertexp->inEmpty()) {
		vvertexp->clearReducibleAndDedupable("inEmpty");	// Can't deal with no sources
		if (!vvertexp->isTop()		// Ok if top inputs are driverless
		    && !vvertexp->varScp()->varp()->valuep()
		    && !vvertexp->varScp()->varp()->isSigPublic()) {
		    UINFO(4, "No drivers "<<vvertexp->varScp()<<endl);
		    if (0) {
			// If we warned here after constant propagation, what the user considered
			// reasonable logic may have disappeared.  Issuing a warning would
			// thus be confusing.  V3Undriven now handles this.
			vvertexp->varScp()->varp()->v3warn(UNDRIVEN,"Signal has no drivers "
							   <<vvertexp->scopep()->prettyName()<<"."
							   <<vvertexp->varScp()->varp()->prettyName());
		    }
		}
	    }
	    else if (!vvertexp->inSize1()) {
		vvertexp->clearReducibleAndDedupable("size!1");	// Can't deal with more than one src
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
		    GateOkVisitor okVisitor(logicp, vvertexp->isClock(), false);
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
		    // Process it
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
			++m_statSigs;
			bool removedAllUsages = true;
			for (V3GraphEdge* edgep = vvertexp->outBeginp();
			     edgep; ) {
			    GateLogicVertex* consumeVertexp = dynamic_cast<GateLogicVertex*>(edgep->top());
			    AstNode* consumerp = consumeVertexp->nodep();
			    if (!elimLogicOkOutputs(consumeVertexp, okVisitor/*ref*/)) {
				// Cannot optimize this replacement
				removedAllUsages = false;
				edgep = edgep->outNextp();
			    } else {
				optimizeElimVar(vvertexp->varScp(), substp, consumerp);
				// If the new replacement referred to a signal,
				// Correct the graph to point to this new generating variable
				const GateVarRefList& rhsVarRefs = okVisitor.rhsVarRefs();
				for (GateVarRefList::const_iterator it = rhsVarRefs.begin();
				     it != rhsVarRefs.end(); ++it) {
				    AstVarScope* newvarscp = (*it)->varScopep();
				    UINFO(9,"         Point-to-new vertex "<<newvarscp<<endl);
				    GateVarVertex* varvertexp = makeVarVertex(newvarscp);
				    new V3GraphEdge(&m_graph, varvertexp, consumeVertexp, 1);
				    // Propagate clock attribute onto generating node
				    varvertexp->propagateAttrClocksFrom(vvertexp);
				}
				// Remove the edge
				edgep->unlinkDelete(); edgep=NULL;
				++m_statRefs;
				edgep = vvertexp->outBeginp();
			    }
			}
			if (removedAllUsages) {
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
}

bool GateVisitor::elimLogicOkOutputs(GateLogicVertex* consumeVertexp, const GateOkVisitor& okVisitor) {
    // Return true if can optimize
    // Return false if the consuming logic has an output signal that the replacement logic has as an input
    typedef set<AstVarScope*> VarScopeSet;
    // Use map to find duplicates between two lists
    VarScopeSet varscopes;
    // Replacement logic usually has shorter input list, so faster to build list based on it
    const GateVarRefList& rhsVarRefs = okVisitor.rhsVarRefs();
    for (GateVarRefList::const_iterator it = rhsVarRefs.begin();
	 it != rhsVarRefs.end(); ++it) {
	AstVarScope* vscp = (*it)->varScopep();
	if (varscopes.find(vscp) == varscopes.end()) varscopes.insert(vscp);
    }
    for (V3GraphEdge* edgep = consumeVertexp->outBeginp(); edgep; edgep = edgep->outNextp()) {
	GateVarVertex* consVVertexp = dynamic_cast<GateVarVertex*>(edgep->top());
	AstVarScope* vscp = consVVertexp->varScp();
	if (varscopes.find(vscp) != varscopes.end()) {
	    UINFO(9,"    Block-unopt, insertion generates input vscp "<<vscp<<endl);
	    return false;
	}
    }
    return true;
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
		    vscp->dumpTree(cerr, "vscStrange: ");
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

//----------------------------------------------------------------------

void GateVisitor::warnSignals() {
    AstNode::user2ClearTree();
    for (V3GraphVertex* itp = m_graph.verticesBeginp(); itp; itp=itp->verticesNextp()) {
	if (GateVarVertex* vvertexp = dynamic_cast<GateVarVertex*>(itp)) {
	    AstVarScope* vscp = vvertexp->varScp();
	    AstNode* sp = vvertexp->rstSyncNodep();
	    AstNode* ap = vvertexp->rstAsyncNodep();
	    if (ap && sp && !vscp->varp()->user2()) {
		// This is somewhat wrong, as marking one flop as ok for sync
		// may mean a different flop now fails.  However it's a pain to
		// then report a warning in a new place - we should report them all at once.
		// Instead we'll disable if any disabled
		if (!vscp->fileline()->warnIsOff(V3ErrorCode::SYNCASYNCNET)
		    && !ap->fileline()->warnIsOff(V3ErrorCode::SYNCASYNCNET)
		    && !sp->fileline()->warnIsOff(V3ErrorCode::SYNCASYNCNET)
		    ) {
		    vscp->varp()->user2(true);  // Warn only once per signal
		    vscp->v3warn(SYNCASYNCNET,"Signal flopped as both synchronous and async: "<<vscp->prettyName()<<endl
				 <<ap->warnMore()<<"... Location of async usage"<<endl
				 <<sp->warnMore()<<"... Location of sync usage"<<endl);
		}
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
	    // Which fileline() to use?
	    // If replacing with logic, an error/warning is likely to want to point to the logic
	    // IE what we're replacing with.
	    // However a VARREF should point to the original as it's otherwise confusing
	    // to throw warnings that point to a PIN rather than where the pin us used.
	    if (substp->castVarRef()) substp->fileline(nodep->fileline());
	    // Make the substp an rvalue like nodep. This facilitate the hashing in dedupe.
	    if (AstNodeVarRef* varrefp = substp->castNodeVarRef()) varrefp->lvalue(false);
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
	consumerp = V3Const::constifyEdit(consumerp);
	if (debug()>=5) consumerp->dumpTree(cout,"\telimUseDne: ");
    }
}

//######################################################################
// Auxiliary hash class for GateDedupeVarVisitor

class GateDedupeHash : public V3HashedUserCheck {
private:
    // NODE STATE
    // Ast*::user2p	-> parent AstNodeAssign* for this rhsp
    // Ast*::user3p	-> AstNode* checked in test for duplicate
    // Ast*::user5p	-> AstNode* checked in test for duplicate
    // AstUser2InUse	m_inuser2;	(Allocated for use in GateVisitor)
    AstUser3InUse	m_inuser3;
    AstUser5InUse	m_inuser5;
    V3Hashed		m_hashed;	// Hash, contains rhs of assigns

    void hash(AstNode* nodep) {
	// !NULL && the object is hashable
	if (nodep && !nodep->sameHash().isIllegal()) {
	    m_hashed.hash(nodep);
	}
    }
    bool sameHash(AstNode* node1p, AstNode* node2p) {
	return (node1p && node2p
		&& !node1p->sameHash().isIllegal()
		&& !node2p->sameHash().isIllegal()
		&& m_hashed.sameNodes(node1p,node2p));
    }
    bool same(AstNUser* node1p, AstNUser* node2p) {
	return node1p == node2p || sameHash((AstNode*)node1p,(AstNode*)node2p);
    }
public:
    bool check(AstNode* node1p,AstNode* node2p)  {
	return same(node1p->user3p(),node2p->user3p()) && same(node1p->user5p(),node2p->user5p())
	    && node1p->user2p()->castNode()->type() == node2p->user2p()->castNode()->type()
	    ;
    }

    AstNodeAssign* hashAndFindDupe(AstNodeAssign* assignp, AstNode* extra1p, AstNode* extra2p) {
	AstNode *rhsp = assignp->rhsp();
	rhsp->user2p(assignp);
	rhsp->user3p(extra1p);
	rhsp->user5p(extra2p);

	hash(extra1p);
	hash(extra2p);

	V3Hashed::iterator inserted = m_hashed.hashAndInsert(rhsp);
	V3Hashed::iterator dupit = m_hashed.findDuplicate(rhsp, this);
	// Even though rhsp was just inserted, V3Hashed::findDuplicate doesn't
	// return anything in the hash that has the same pointer (V3Hashed.cpp::findDuplicate)
	// So dupit is either a different, duplicate rhsp, or the end of the hash.
	if (dupit != m_hashed.end()) {
	    m_hashed.erase(inserted);
	    return m_hashed.iteratorNodep(dupit)->user2p()->castNode()->castNodeAssign();
	}
	return NULL;
    }
};

//######################################################################
// Have we seen the rhs of this assign before?

class GateDedupeVarVisitor : public GateBaseVisitor {
    // Given a node, it is visited to try to find the AstNodeAssign under it that can used for dedupe.
    // Right now, only the following node trees are supported for dedupe.
    // 1. AstNodeAssign
    // 2. AstAlways -> AstNodeAssign
    //   (Note, the assign must also be the only node under the always)
    // 3. AstAlways -> AstNodeIf -> AstNodeAssign
    //   (Note, the IF must be the only node under the always,
    //    and the assign must be the only node under the if, other than the ifcond)
    // Any other ordering or node type, except for an AstComment, makes it not dedupable
private:
    // STATE
    GateDedupeHash	m_hash;			// Hash used to find dupes of rhs of assign
    AstNodeAssign*	m_assignp;		// Assign found for dedupe
    AstNode*		m_ifCondp;		// IF condition that assign is under
    bool		m_always;		// Assign is under an always
    bool		m_dedupable;		// Determined the assign to be dedupable

    // VISITORS
    virtual void visit(AstNodeAssign* assignp, AstNUser*) {
	if (m_dedupable) {
	    // I think we could safely dedupe an always block with multiple non-blocking statements, but erring on side of caution here
	    if (!m_assignp) {
		m_assignp = assignp;
	    } else {
		m_dedupable = false;
	    }
	}
    }
    virtual void visit(AstAlways* alwaysp, AstNUser*) {
	if (m_dedupable) {
	    if (!m_always) {
		m_always = true;
		alwaysp->bodysp()->iterateAndNext(*this);
	    } else {
		m_dedupable = false;
	    }
	}
    }
    // Ugly support for latches of the specific form -
    //  always @(...)
    //    if (...)
    //       foo = ...; // or foo <= ...;
    virtual void visit(AstNodeIf* ifp, AstNUser*) {
	if (m_dedupable) {
	    if (m_always && !m_ifCondp && !ifp->elsesp()) {  //we're under an always, this is the first IF,  and there's no else
		m_ifCondp = ifp->condp();
		ifp->ifsp()->iterateAndNext(*this);
	    } else {
		m_dedupable = false;
	    }
	}
    }

    virtual void visit(AstComment*, AstNUser*) {}  // NOP
    //--------------------
    // Default
    virtual void visit(AstNode*, AstNUser*) {
	m_dedupable = false;
    }

public:
    // CONSTUCTORS
    GateDedupeVarVisitor() {
	m_assignp = NULL;
	m_ifCondp = NULL;
	m_always = false;
	m_dedupable = true;
    }
    // PUBLIC METHODS
    AstNodeVarRef* findDupe(AstNode* nodep, AstVarScope* consumerVarScopep, AstActive* activep) {
	m_assignp = NULL;
	m_ifCondp = NULL;
	m_always = false;
	m_dedupable = true;
	nodep->accept(*this);
	if (m_dedupable && m_assignp) {
	    AstNode* lhsp = m_assignp->lhsp();
	    // Possible todo, handle more complex lhs expressions
	    if (AstNodeVarRef* lhsVarRefp = lhsp->castNodeVarRef()) {
		if (lhsVarRefp->varScopep() != consumerVarScopep) consumerVarScopep->v3fatalSrc("Consumer doesn't match lhs of assign");
		if (AstNodeAssign* dup =  m_hash.hashAndFindDupe(m_assignp,activep,m_ifCondp)) {
		    return (AstNodeVarRef*) dup->lhsp();
		}
	    }
	}
	return NULL;
    }
};

//######################################################################
// Recurse through the graph, looking for duplicate expressions on the rhs of an assign

class GateDedupeGraphVisitor : public GateGraphBaseVisitor {
private:
    // NODE STATE
    // AstVarScope::user2p	-> bool: already visited
    // AstUser2InUse		m_inuser2;	(Allocated for use in GateVisitor)
    V3Double0			m_numDeduped;	// Statistic tracking
    GateDedupeVarVisitor	m_varVisitor;	// Looks for a dupe of the logic

    virtual AstNUser* visit(GateVarVertex *vvertexp, AstNUser*) {
	// Check that we haven't been here before
	if (vvertexp->varScp()->user2()) return NULL;
	vvertexp->varScp()->user2(true);

	AstNodeVarRef* dupVarRefp = (AstNodeVarRef*) vvertexp->iterateInEdges(*this, (AstNUser*) vvertexp);

	if (dupVarRefp && vvertexp->inSize1()) {
	    V3GraphEdge* edgep = vvertexp->inBeginp();
	    GateLogicVertex* lvertexp = (GateLogicVertex*)edgep->fromp();
	    if (!vvertexp->dedupable()) vvertexp->varScp()->v3fatalSrc("GateLogicVertex* visit should have returned NULL if consumer var vertex is not dedupable.");
	    GateOkVisitor okVisitor(lvertexp->nodep(), false, true);
	    if (okVisitor.isSimple()) {
		AstVarScope* dupVarScopep = dupVarRefp->varScopep();
		GateVarVertex* dupVvertexp = (GateVarVertex*) (dupVarScopep->user1p());
		UINFO(4,"replacing " << vvertexp << " with " << dupVvertexp << endl);
		++m_numDeduped;
		// Replace all of this varvertex's consumers with dupVarRefp
		for (V3GraphEdge* outedgep = vvertexp->outBeginp();outedgep;) {
		    GateLogicVertex* consumeVertexp = dynamic_cast<GateLogicVertex*>(outedgep->top());
		    AstNode* consumerp = consumeVertexp->nodep();
		    GateElimVisitor elimVisitor(consumerp,vvertexp->varScp(),dupVarRefp);
		    outedgep = outedgep->relinkFromp(dupVvertexp);
		}

		// Propogate attributes
		dupVvertexp->propagateAttrClocksFrom(vvertexp);

		// Remove inputs links
		while (V3GraphEdge* inedgep = vvertexp->inBeginp()) {
		    inedgep->unlinkDelete(); inedgep=NULL;
		}
		// replaceAssigns() does the deleteTree on lvertexNodep in a later step
		AstNode* lvertexNodep = lvertexp->nodep();
		lvertexNodep->unlinkFrBack();
		vvertexp->varScp()->valuep(lvertexNodep);
		lvertexNodep = NULL;
		vvertexp->user(true);
		lvertexp->user(true);
	    }
	}
	return NULL;
    }

    // Returns a varref that has the same logic input
    virtual AstNUser* visit(GateLogicVertex* lvertexp, AstNUser* vup) {
	lvertexp->iterateInEdges(*this);

	GateVarVertex* consumerVvertexpp = (GateVarVertex*) vup;
	if (lvertexp->dedupable() && consumerVvertexpp->dedupable()) {
	    AstNode* nodep = lvertexp->nodep();
	    AstVarScope* consumerVarScopep = consumerVvertexpp->varScp();
	    // TODO: Doing a simple pointer comparison of  activep won't work
	    // optimally for statements under generated clocks. Statements under
	    // different generated clocks will never compare as equal, even if the
	    // generated clocks are deduped into one clock.
	    AstActive* activep = lvertexp->activep();
	    return (AstNUser*) m_varVisitor.findDupe(nodep, consumerVarScopep, activep);
	}
	return NULL;
    }

public:
    GateDedupeGraphVisitor() {}
    void dedupeTree(GateVarVertex* vvertexp) {
	vvertexp->accept(*this);
    }
    V3Double0 numDeduped() { return m_numDeduped; }
};

//----------------------------------------------------------------------

void GateVisitor::dedupe() {
    AstNode::user2ClearTree();
    GateDedupeGraphVisitor deduper;
    // Traverse starting from each of the clocks
    for (V3GraphVertex* itp = m_graph.verticesBeginp(); itp; itp=itp->verticesNextp()) {
	if (GateVarVertex* vvertexp = dynamic_cast<GateVarVertex*>(itp)) {
	    if (vvertexp->isClock()) {
		deduper.dedupeTree(vvertexp);
	    }
	}
    }
    // Traverse starting from each of the outputs
    for (V3GraphVertex* itp = m_graph.verticesBeginp(); itp; itp=itp->verticesNextp()) {
	if (GateVarVertex* vvertexp = dynamic_cast<GateVarVertex*>(itp)) {
	    if (vvertexp->isTop() && vvertexp->varScp()->varp()->isOutput()) {
		deduper.dedupeTree(vvertexp);
	    }
	}
    }
    m_statDedupLogic += deduper.numDeduped();
}


//######################################################################
// Recurse through the graph, try to merge assigns 

class GateMergeAssignsGraphVisitor : public GateGraphBaseVisitor {
private:
    // NODE STATE
    AstNodeAssign* m_assignp;
    AstActive*     m_activep;
    GateLogicVertex* m_logicvp;
    V3Graph*         m_graphp;
    V3Double0        m_numMergedAssigns;	// Statistic tracking


    // assemble two Sel into one if possible 
    AstSel* merge(AstSel* pre, AstSel* cur) {
	AstVarRef* preVarRefp = pre->fromp()->castVarRef();
	AstVarRef* curVarRefp = cur->fromp()->castVarRef();
	if (!preVarRefp || !curVarRefp || !curVarRefp->same(preVarRefp)) return NULL; // not the same var
	AstConst* pstart = pre->lsbp()->castConst();
	AstConst* pwidth = pre->widthp()->castConst();
	AstConst* cstart = cur->lsbp()->castConst();
	AstConst* cwidth = cur->widthp()->castConst();
	if (!pstart || !pwidth || !cstart || !cwidth) return NULL; // too complicated
	if (cur->lsbConst()+cur->widthConst() == pre->lsbConst())
	    return new AstSel(curVarRefp->fileline(), curVarRefp->cloneTree(false), cur->lsbConst(), pre->widthConst()+cur->widthConst());
	else return NULL;
    }

    virtual AstNUser* visit(GateVarVertex *vvertexp, AstNUser*) {
	for (V3GraphEdge* edgep = vvertexp->inBeginp(); edgep; ) {
	    V3GraphEdge* oldedgep = edgep;
	    edgep = edgep->inNextp();  // for recursive since the edge could be deleted
	    if (GateLogicVertex* lvertexp = dynamic_cast<GateLogicVertex*>(oldedgep->fromp())) {
		if (AstNodeAssign* assignp = lvertexp->nodep()->castNodeAssign()) {
		    //if (lvertexp->outSize1() && assignp->lhsp()->castSel()) {
		    if (assignp->lhsp()->castSel() && lvertexp->outSize1()) {
			UINFO(9, "assing to the nodep["<<assignp->lhsp()->castSel()->lsbConst()<<"]"<<endl);
			// first assign with Sel-lhs
			if (!m_activep) m_activep = lvertexp->activep();
			if (!m_logicvp) m_logicvp = lvertexp;
			if (!m_assignp) m_assignp = assignp;

			// not under the same active
			if (m_activep != lvertexp->activep()) {
			    m_activep = lvertexp->activep();
			    m_logicvp = lvertexp;
			    m_assignp = assignp;
			    continue;
			}

			AstSel* preselp = m_assignp->lhsp()->castSel();
			AstSel* curselp = assignp->lhsp()->castSel();
			if (!preselp || !curselp) continue;

			if (AstSel* newselp = merge(preselp, curselp)) {
			    UINFO(5, "assemble to new sel: "<<newselp<<endl);
			    // replace preSel with newSel
			    preselp->replaceWith(newselp); preselp->deleteTree(); preselp = NULL;
			    // create new rhs for pre assignment
			    AstNode* newrhsp = new AstConcat(m_assignp->rhsp()->fileline(), m_assignp->rhsp()->cloneTree(false), assignp->rhsp()->cloneTree(false));
			    AstNode* oldrhsp = m_assignp->rhsp();
			    oldrhsp->replaceWith(newrhsp); oldrhsp->deleteTree(); oldrhsp = NULL;
			    m_assignp->dtypeChgWidthSigned(m_assignp->width()+assignp->width(), m_assignp->width()+assignp->width(), AstNumeric::fromBool(true));
			    // don't need to delete, will be handled
			    //assignp->unlinkFrBack(); assignp->deleteTree(); assignp = NULL;

			    // update the graph
			    {
				// delete all inedges to lvertexp
				if (!lvertexp->inEmpty()) { 
				    for (V3GraphEdge* ledgep = lvertexp->inBeginp(); ledgep; ) {
					V3GraphEdge* oedgep = ledgep;
					ledgep = ledgep->inNextp();
					GateEitherVertex* fromvp = dynamic_cast<GateEitherVertex*>(oedgep->fromp());
					new V3GraphEdge(m_graphp, fromvp, m_logicvp, 1);
					oedgep->unlinkDelete(); oedgep = NULL;
				    }
				}
				// delete all outedges to lvertexp, only one
				oldedgep->unlinkDelete(); oldedgep = NULL;
			    }
			    ++m_numMergedAssigns;
			} else {
			    m_assignp = assignp;
			    m_logicvp = lvertexp;
			}
		    }
		}
	    }
	}
	return NULL;
    }

    virtual AstNUser* visit(GateLogicVertex* lvertexp, AstNUser* vup) {
	return NULL;
    }

public:
    GateMergeAssignsGraphVisitor(V3Graph* graphp) {
	m_assignp = NULL;
	m_activep = NULL;
	m_logicvp = NULL;
	m_numMergedAssigns = 0;
	m_graphp = graphp;
    }
    void mergeAssignsTree(GateVarVertex* vvertexp) {
	vvertexp->accept(*this);
    }
    V3Double0 numMergedAssigns() { return m_numMergedAssigns; }
};


//----------------------------------------------------------------------

void GateVisitor::mergeAssigns() {
    GateMergeAssignsGraphVisitor merger(&m_graph);
    for (V3GraphVertex* itp = m_graph.verticesBeginp(); itp; itp=itp->verticesNextp()) {
	if (GateVarVertex* vvertexp = dynamic_cast<GateVarVertex*>(itp)) {
	    merger.mergeAssignsTree(vvertexp);
	}
    }
    m_statAssignMerged += merger.numMergedAssigns();
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
    V3Global::dumpCheckGlobalTree("gate.tree", 0, v3Global.opt.dumpTreeLevel(__FILE__) >= 3);
}
