// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Deals with tristate logic
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
// V3Tristate's Transformations:
//
// Modify the design to expand tristate logic into its
// corresponding two state representation. At the lowest levels,
//
// In detail:
//
// Over each module, from child to parent:
//   Build a graph, connecting signals together so we can propagate tristates
//     Variable becomes tristate with
//	 VAR->isInout
//	 VAR->isPullup/isPulldown (converted to AstPullup/AstPulldown
//	 BufIf0/1
//   All variables on the LHS need to become tristate when there is:
//	 CONST-> with Z value on the RHS of an assignment
//	 AstPin with lower connection a tristate
//	 A tristate signal on the RHS      (this can't generally be determined until that signal is resolved)
//   When LHS becomes tristate, then mark all RHS nodes as tristate
//   so any tristate varrefs on the right will propagate.
//
// Walk graph's tristate indication on each logic block with tristates
// propagating downstream to every other logic block.
//
// Expressions that have Z in them are converted into two state
// drivers and corresponding output enable signals are generated.
// These enable signals get transformed and regenerated through any
// logic that they may go through until they hit the module level.  At
// the module level, all the output enable signals from what can be
// many tristate drivers are combined together to produce a single
// driver and output enable. If the signal propagates up into higher
// modules, then new ports are created with for the signal with
// suffixes __en and __out. The original port is turned from an inout
// to an input and the __out port carries the output driver signal and
// the __en port carried the output enable for that driver.
//
// Note 1800-2012 adds user defined resolution functions. This suggests
// long term this code should be scoped-based and resolve all nodes at once
// rather than hierarchically.
//*************************************************************************

#include "config_build.h"
#include "verilatedos.h"
#include <cstdio>
#include <cstdarg>
#include <unistd.h>
#include <algorithm>
#include <map>

#include "V3Global.h"
#include "V3Tristate.h"
#include "V3Ast.h"
#include "V3Const.h"
#include "V3Stats.h"
#include "V3Inst.h"
#include "V3Stats.h"
#include "V3Graph.h"

//######################################################################

class TristateBaseVisitor : public AstNVisitor {
public:
    // METHODS
    static int debug() {
	static int level = -1;
	if (VL_UNLIKELY(level < 0)) level = v3Global.opt.debugSrcLevel(__FILE__);
	return level;
    }
};

//######################################################################
// Graph support classes

class TristateVertex : public V3GraphVertex {
    AstNode*	m_nodep;
    bool	m_isTristate;	// Logic indicates a tristate
    bool	m_feedsTri;	// Propagates to a tristate node (on RHS)
    bool	m_processed;	// Tristating was cleaned up
public:
    TristateVertex(V3Graph* graphp, AstNode* nodep)
	: V3GraphVertex(graphp)
	, m_nodep(nodep), m_isTristate(false), m_feedsTri(false), m_processed(false) {}
    virtual ~TristateVertex() {}
    // Accessors
    AstNode* nodep() const { return m_nodep; }
    AstVar* varp() const { return nodep()->castVar(); }
    virtual string name() const {
	return ((isTristate() ? "tri\\n"
		 :feedsTri() ? "feed\\n" : "-\\n")
		+(nodep()->prettyTypeName()+" "+cvtToStr((void*)nodep()))); }
    virtual string dotColor() const {
	return (varp()
		? (isTristate() ? "darkblue"
		   :feedsTri() ? "blue" : "lightblue")
		: (isTristate() ? "darkgreen"
		   :feedsTri() ? "green" : "lightgreen")); }
    void isTristate(bool flag) { m_isTristate = flag; }
    bool isTristate() const { return m_isTristate; }
    void feedsTri(bool flag) { m_feedsTri = flag; }
    bool feedsTri() const { return m_feedsTri; }
    void processed(bool flag) { m_processed = flag; }
    bool processed() const { return m_processed; }
};

//######################################################################

class TristateGraph {
    // NODE STATE
    //	 AstVar::user5p		-> TristateVertex* for variable being built
    //AstUser5InUse	m_inuser5;   // In visitor below

    // TYPES
public:
    typedef std::vector<AstVar*> VarVec;
private:

    // MEMBERS
    V3Graph		m_graph;	// Logic graph

public:
    // CONSTUCTORS
    TristateGraph() { clear(); }
    virtual ~TristateGraph() { clear(); }

private:
    // METHODS
    static int debug() {
	static int level = -1;
	if (VL_UNLIKELY(level < 0)) level = v3Global.opt.debugSrcLevel(__FILE__);
	return level;
    }

    TristateVertex* makeVertex(AstNode* nodep) {
	TristateVertex* vertexp = (TristateVertex*)(nodep->user5p());
	if (!vertexp) {
	    UINFO(6,"         New vertex "<<nodep<<endl);
	    vertexp = new TristateVertex(&m_graph, nodep);
	    nodep->user5p(vertexp);
	}
	return vertexp;
    }

    // METHODS - Graph optimization
    void graphWalkRecurseFwd(TristateVertex* vtxp, int level) {
	// Propagate tristate forward to all sinks
	// For example if on a CONST, propagate through CONCATS to ASSIGN to LHS VARREF of signal to tristate
	if (!vtxp->isTristate()) return; // tristate involved
	if (vtxp->user() == 1) return;
	vtxp->user(1);  // Recursed
	UINFO(9,"  Mark tri "<<level<<"  "<<vtxp<<endl);
	if (!vtxp->varp()) {  // not a var where we stop the recursion
	    for (V3GraphEdge* edgep = vtxp->outBeginp(); edgep; edgep=edgep->outNextp()) {
		TristateVertex* vvertexp = dynamic_cast<TristateVertex*>(edgep->top());
		// Doesn't hurt to not check if already set, but by doing so when we
		// print out the debug messages, we'll see this node at level 0 instead.
		if (!vvertexp->isTristate()) {
		    vvertexp->isTristate(true);
		    graphWalkRecurseFwd(vvertexp, level+1);
		}
	    }
	} else {
	    // A variable is tristated.  Find all of the LHS VARREFs that drive this signal now need tristate drivers
	    for (V3GraphEdge* edgep = vtxp->inBeginp(); edgep; edgep=edgep->inNextp()) {
		TristateVertex* vvertexp = dynamic_cast<TristateVertex*>(edgep->fromp());
		if (AstVarRef* refp = vvertexp->nodep()->castVarRef()) {
		    if (refp->lvalue()
			// Doesn't hurt to not check if already set, but by doing so when we
			// print out the debug messages, we'll see this node at level 0 instead.
			&& !vvertexp->isTristate()) {
			vvertexp->isTristate(true);
			graphWalkRecurseFwd(vvertexp, level+1);
		    }
		}
	    }
	}
    }
    void graphWalkRecurseBack(TristateVertex* vtxp, int level) {
	// Called only on a tristate node; propagate a feedsTri attribute "backwards"
	// towards any driving nodes, i.e. from a LHS VARREF back to a driving RHS VARREF
	// This way if the RHS VARREF is also tristated we'll connect the enables up to the LHS VARREF.
	// Otherwise if not marked feedsTri() we'll drop the LHS' enables, if any
	if (!(vtxp->isTristate() || vtxp->feedsTri())) return; // tristate involved
	if (vtxp->user() == 3) return;
	vtxp->user(3);  // Recursed
	UINFO(9,"  Mark feedstri "<<level<<"  "<<vtxp<<endl);
	if (!vtxp->varp()) {  // not a var where we stop the recursion
	    for (V3GraphEdge* edgep = vtxp->inBeginp(); edgep; edgep=edgep->inNextp()) {
		TristateVertex* vvertexp = dynamic_cast<TristateVertex*>(edgep->fromp());
		// Doesn't hurt to not check if already set, but by doing so when we
		// print out the debug messages, we'll see this node at level 0 instead.
		if (!vvertexp->feedsTri()) {
		    vvertexp->feedsTri(true);
		    graphWalkRecurseBack(vvertexp, level+1);
		}
	    }
	}
    }

public:
    // METHODS
    void clear() {
	for (V3GraphVertex* itp = m_graph.verticesBeginp(); itp; itp=itp->verticesNextp()) {
	    TristateVertex* vvertexp = static_cast<TristateVertex*>(itp);
	    if (vvertexp->isTristate() && !vvertexp->processed()) {
		// Not v3errorSrc as no reason to stop the world
		vvertexp->nodep()->v3error("Unsupported tristate construct (in graph; not converted): "<<vvertexp->nodep()->prettyTypeName());
	    }
	}
	m_graph.clear();
	AstNode::user5ClearTree();  // Wipe all node user5p's that point to vertexes
    }
    void graphWalk(AstNodeModule* nodep) {
	//if (debug()>=9) m_graph.dumpDotFilePrefixed("tri_pre__"+nodep->name());
	UINFO(9," Walking "<<nodep<<endl);
	for (V3GraphVertex* itp = m_graph.verticesBeginp(); itp; itp=itp->verticesNextp()) {
	    graphWalkRecurseFwd((TristateVertex*)itp, 0);
	}
	for (V3GraphVertex* itp = m_graph.verticesBeginp(); itp; itp=itp->verticesNextp()) {
	    graphWalkRecurseBack((TristateVertex*)itp, 0);
	}
	if (debug()>=9) m_graph.dumpDotFilePrefixed("tri_pos__"+nodep->name());
    }
    void setTristate(AstNode* nodep) {
	makeVertex(nodep)->isTristate(true);
    }
    void associate(AstNode* fromp, AstNode* top) {
	new V3GraphEdge(&m_graph, makeVertex(fromp), makeVertex(top), 1);
    }
    bool isTristate(AstNode* nodep) {
	TristateVertex* vertexp = (TristateVertex*)(nodep->user5p());
	return vertexp && vertexp->isTristate();
    }
    bool feedsTri(AstNode* nodep) {
	TristateVertex* vertexp = (TristateVertex*)(nodep->user5p());
	return vertexp && vertexp->feedsTri();
    }
    void didProcess(AstNode* nodep) {
	TristateVertex* vertexp = (TristateVertex*)(nodep->user5p());
	if (!vertexp) {
	    // Not v3errorSrc as no reason to stop the world
	    nodep->v3error("Unsupported tristate construct (not in propagation graph): "<<nodep->prettyTypeName());
	} else {
	    // We don't warn if no vertexp->isTristate() as the creation process makes midling nodes that don't have it set
	    vertexp->processed(true);
	}
    }
    // ITERATOR METHODS
    VarVec tristateVars() {
	// Return all tristate variables
	VarVec v;
	for (V3GraphVertex* itp = m_graph.verticesBeginp(); itp; itp=itp->verticesNextp()) {
	    TristateVertex* vvertexp = static_cast<TristateVertex*>(itp);
	    if (vvertexp->isTristate()) {
		if (AstVar* nodep = vvertexp->nodep()->castVar()) {
		    v.push_back(nodep);
		}
	    }
	}
	return v;
    }
};

//######################################################################
// Given a node, flip any VarRef from LValue to RValue (i.e. make it an input)
// See also V3LinkLValue::linkLValueSet

class TristatePinVisitor : public TristateBaseVisitor {
    TristateGraph& m_tgraph;
    bool m_lvalue;	// Flip to be an LVALUE
    // VISITORS
    virtual void visit(AstVarRef* nodep, AstNUser*) {
	if (m_lvalue && !nodep->lvalue()) {
	    UINFO(9,"  Flip-to-LValue "<<nodep<<endl);
	    nodep->lvalue(true);
	} else if (!m_lvalue && nodep->lvalue()) {
	    UINFO(9,"  Flip-to-RValue "<<nodep<<endl);
	    nodep->lvalue(false);
	    // Mark the ex-output as tristated
	    UINFO(9,"  setTristate-subpin "<<nodep->varp()<<endl);
	    m_tgraph.setTristate(nodep->varp());
	}
    }
    virtual void visit(AstArraySel* nodep, AstNUser*) {
	// Doesn't work because we'd set lvalue on the array index's var
	if (m_lvalue) nodep->v3fatalSrc("ArraySel conversion to output, under tristate node");
	nodep->iterateChildren(*this);
    }
    virtual void visit(AstNode* nodep, AstNUser*) {
	nodep->iterateChildren(*this);
    }
public:
    // CONSTUCTORS
    TristatePinVisitor(AstNode* nodep, TristateGraph& tgraph, bool lvalue)
	: m_tgraph(tgraph), m_lvalue(lvalue) {
	nodep->accept(*this);
    }
    virtual ~TristatePinVisitor() {}
};

//######################################################################

class TristateVisitor : public TristateBaseVisitor {
    // NODE STATE
    //	 *::user1p		-> pointer to output enable __en expressions
    //   *::user2		-> int - already visited, see U2_ enum
    //   AstVar::user3p		-> AstPull* pullup/pulldown direction (input Var's user3p)
    //   AstVar::user4p		-> AstVar* pointer to output __out var (input Var's user2p)
    // See TristateGraph:
    //   AstVar::user5p		-> TristateVertex* for variable being built
    //   AstStmt*::user5p	-> TristateVertex* for this statement
    AstUser1InUse	m_inuser1;
    AstUser2InUse	m_inuser2;
    AstUser3InUse	m_inuser3;
    AstUser4InUse	m_inuser4;
    AstUser5InUse	m_inuser5;

    // TYPES
    typedef std::vector<AstVarRef*> RefVec;
    typedef std::map<AstVar*, RefVec*> VarMap;
    enum { U2_GRAPHING=1,	// bit[0] if did m_graphing visit
	   U2_NONGRAPH=2,	// bit[1] if did !m_graphing visit
	   U2_BOTH=3 };  	// Both bits set

    // MEMBERS
    bool		m_graphing;	// Major mode - creating graph
    //
    AstNodeModule*	m_modp;		// Current module
    AstCell*		m_cellp;	// current cell
    VarMap		m_lhsmap;	// LHS driver map
    int			m_unique;
    bool		m_alhs;		// On LHS of assignment
    AstNode*		m_logicp;	// Current logic being built
    TristateGraph	m_tgraph;	// Logic graph

    // STATS
    V3Double0 m_statTriSigs; // stat tracking

    // METHODS
    string dbgState() {
	string o = (m_graphing?" gr ":" ng ");
	if (m_alhs) o += "alhs ";
	return o;
    }
    void associateLogic(AstNode* fromp, AstNode* top) {
	if (m_logicp) {
	    m_tgraph.associate(fromp, top);
	}
    }
    AstNode* getEnp(AstNode* nodep) {
	// checks if user1p() is null, and if so, adds a constant output
	// enable driver of all 1's. Otherwise returns the user1p() data.
	if (!nodep->user1p()) {
	    V3Number num(nodep->fileline(), nodep->width());
	    num.setAllBits1();
	    AstNode* enp = new AstConst(nodep->fileline(), num);
	    nodep->user1p(enp);
	}
	return nodep->user1p()->castNode();
    }

    AstVar* getCreateEnVarp(AstVar* invarp) {
	// Return the master __en for the specified input variable
	if (!invarp->user1p()) {
	    AstVar* newp = new AstVar(invarp->fileline(),
				      AstVarType::MODULETEMP,
				      invarp->name()+"__en",
				      invarp);
	    UINFO(9,"       newenv "<<newp<<endl);
	    if (!m_modp) { invarp->v3error("Unsupported: Creating tristate signal not underneath a module: "<<invarp->prettyName()); }
	    else m_modp->addStmtp(newp);
	    invarp->user1p(newp); // find envar given invarp
	}
	return invarp->user1p()->castNode()->castVar();
    }

    AstVar* getCreateOutVarp(AstVar* invarp) {
	// Return the master __out for the specified input variable
	if (!invarp->user4p()) {
	    AstVar* newp = new AstVar(invarp->fileline(),
				      AstVarType::MODULETEMP,
				      invarp->name()+"__out",
				      invarp);
	    UINFO(9,"       newout "<<newp<<endl);
	    if (!m_modp) { invarp->v3error("Unsupported: Creating tristate signal not underneath a module: "<<invarp->prettyName()); }
	    else m_modp->addStmtp(newp);
	    invarp->user4p(newp);  // find outvar given invarp
	}
	return invarp->user4p()->castNode()->castVar();
    }

    AstVar* getCreateUnconnVarp(AstNode* fromp, AstNodeDType* dtypep) {
	AstVar* newp =  new AstVar(fromp->fileline(),
				   AstVarType::MODULETEMP,
				   "__Vtriunconn"+cvtToStr(m_unique++),
				   dtypep);
	UINFO(9,"       newunc "<<newp<<endl);
	if (!m_modp) { newp->v3error("Unsupported: Creating tristate signal not underneath a module"); }
	else m_modp->addStmtp(newp);
	return newp;
    }

    void mapInsertLhsVarRef(AstVarRef* nodep) {
	AstVar* key = nodep->varp();
	VarMap::iterator it = m_lhsmap.find(key);
	UINFO(9,"    mapInsertLhsVarRef "<<nodep<<endl);
	if (it == m_lhsmap.end()) {  // Not found
	    RefVec* refs = new RefVec();
	    refs->push_back(nodep);
	    m_lhsmap.insert(make_pair(key, refs));
	} else {
	    (*it).second->push_back(nodep);
	}
    }

    AstNode* newEnableDeposit(AstSel* selp, AstNode* enp) {
	// Form a "deposit" instruction for given enable, using existing select as a template.
	// Would be nicer if we made this a new AST type
	AstNode* newp = new AstShiftL(selp->fileline(),
				      new AstExtend(selp->fileline(),
						    enp,
						    selp->fromp()->width()),
				      selp->lsbp()->cloneTree(false),
				      selp->fromp()->width());
	return newp;
    }

    void setPullDirection(AstVar* varp, AstPull* pullp) {
	AstPull* oldpullp = (AstPull*)varp->user3p();
	if (!oldpullp) {
	    varp->user3p(pullp); //save off to indicate the pull direction
	} else {
	    if (oldpullp->direction() != pullp->direction()) {
		pullp->v3error("Unsupported: Conflicting pull directions.");
		oldpullp->v3error("... Location of conflicting pull.");
	    }
	}
    }

    void checkUnhandled(AstNode* nodep) {
	// Check for unsupported tristate constructs. This is not a 100% check.
	// The best way would be to visit the tree again and find any user1p()
	// pointers that did not get picked up and expanded.
	if (m_alhs && nodep->user1p()) {
	    nodep->v3error("Unsupported LHS tristate construct: "<<nodep->prettyTypeName());
	}
	// Ignore Var's because they end up adjacent to statements
	if ((nodep->op1p() && nodep->op1p()->user1p() && !nodep->op1p()->castVar())
	    || (nodep->op2p() && nodep->op2p()->user1p() && !nodep->op1p()->castVar())
	    || (nodep->op3p() && nodep->op3p()->user1p() && !nodep->op1p()->castVar())
	    || (nodep->op4p() && nodep->op4p()->user1p() && !nodep->op1p()->castVar())) {
	    nodep->v3error("Unsupported tristate construct: "<<nodep->prettyTypeName());
	}
    }

    void insertTristates(AstNodeModule* nodep) {
	// Go through all the vars and find any that are outputs without drivers
	// or inouts without high-Z logic and put a 1'bz driver on them and add
	// them to the lhs map so they get expanded correctly.
	TristateGraph::VarVec vars = m_tgraph.tristateVars();
	for (TristateGraph::VarVec::iterator ii = vars.begin(); ii != vars.end(); ++ii) {
	    AstVar* varp = (*ii);
	    if (m_tgraph.isTristate(varp)) {
		VarMap::iterator it = m_lhsmap.find(varp);
		if (it == m_lhsmap.end()) {
		    // set output enable to always be off on this assign statement so that this var is floating
		    UINFO(8,"  Adding driver to var "<<varp<<endl);
		    V3Number zeros (varp->fileline(), varp->width());
		    zeros.setAllBits0();
		    AstConst* constp = new AstConst(varp->fileline(), zeros);
		    AstVarRef* varrefp = new AstVarRef(varp->fileline(), varp, true);
		    AstNode* newp = new AstAssignW(varp->fileline(), varrefp, constp);
		    UINFO(9,"       newoev "<<newp<<endl);
		    varrefp->user1p(new AstConst(varp->fileline(),zeros));
		    nodep->addStmtp(newp);
		    mapInsertLhsVarRef(varrefp);  // insertTristates will convert
		    //				  // to a varref to the __out# variable
		}
	    }
	}

	// Now go through the lhs driver map and generate the output
	// enable logic for any tristates.
	// Note there might not be any drivers.
	for (VarMap::iterator nextit, it = m_lhsmap.begin(); it != m_lhsmap.end(); it = nextit) {
	    nextit = it; ++nextit;
	    AstVar* invarp = (*it).first;
	    RefVec* refs = (*it).second;

	    // Figure out if this var needs tristate expanded.
	    if (!m_tgraph.isTristate(invarp)) {
		// This var has no tristate logic, so we leave it alone.
		UINFO(8, "  NO TRISTATE ON:" << invarp << endl);
		m_lhsmap.erase(invarp);
		delete refs;
		continue;
	    }

	    ++m_statTriSigs;
	    m_tgraph.didProcess(invarp);
	    UINFO(8, "  TRISTATE EXPANDING:" << invarp << endl);

	    // If the lhs var is a port, then we need to create ports for
	    // the output (__out) and output enable (__en) signals. The
	    // original port gets converted to an input. Don't tristate expand
	    // if this is the top level so that we can force the final
	    // tristate resolution at the top.
	    AstVar* envarp = NULL;
	    AstVar* outvarp = NULL;	// __out
	    AstVar* lhsp = invarp;	// Variable to assign drive-value to (<in> or __out)
	    if (!nodep->isTop() && invarp->isIO()) {
		// This var becomes an input
		invarp->varType2In(); // convert existing port to type input
		// Create an output port (__out)
		outvarp = getCreateOutVarp(invarp);
		outvarp->varType2Out();
		lhsp = outvarp;  // Must assign to __out, not to normal input signal
		UINFO(9, "     TRISTATE propagates up with "<<lhsp<<endl);
		// Create an output enable port (__en)
		envarp = getCreateEnVarp(invarp);  // May already be created if have foo === 1'bz somewhere
		envarp->varType2Out();
		//
		outvarp->user1p(envarp);
		outvarp->user3p(invarp->user3p()); // AstPull* propagation
		if (invarp->user3p()) UINFO(9, "propagate pull to "<<outvarp<<endl);
	    } else if (invarp->user1p()) {
		envarp = invarp->user1p()->castNode()->castVar();  // From CASEEQ, foo === 1'bz
	    }

	    AstNode* orp = NULL;
	    AstNode* enp = NULL;
	    AstNode* undrivenp = NULL;

	    // loop through the lhs drivers to build the driver resolution logic
	    for (RefVec::iterator ii=refs->begin(); ii != refs->end(); ++ii) {
		AstVarRef* refp = (*ii);
		int w = lhsp->width();

		// create the new lhs driver for this var
		AstVar* newlhsp = new AstVar(lhsp->fileline(),
					     AstVarType::MODULETEMP,
					     lhsp->name()+"__out"+cvtToStr(m_unique),
					     VFlagBitPacked(), w);  // 2-state ok; sep enable
		UINFO(9,"       newout "<<newlhsp<<endl);
		nodep->addStmtp(newlhsp);
		refp->varp(newlhsp); // assign the new var to the varref
		refp->name(newlhsp->name());

		// create a new var for this drivers enable signal
		AstVar* newenp =  new AstVar(lhsp->fileline(),
					     AstVarType::MODULETEMP,
					     lhsp->name()+"__en"+cvtToStr(m_unique++),
					     VFlagBitPacked(), w);  // 2-state ok
		UINFO(9,"       newenp "<<newenp<<endl);
		nodep->addStmtp(newenp);

		AstNode* enassp = new AstAssignW(refp->fileline(),
						 new AstVarRef(refp->fileline(), newenp, true),
						 getEnp(refp));
		UINFO(9,"       newass "<<enassp<<endl);
		nodep->addStmtp(enassp);

		// now append this driver to the driver logic.
		AstNode* ref1p = new AstVarRef(refp->fileline(), newlhsp,false);
		AstNode* ref2p = new AstVarRef(refp->fileline(), newenp, false);
		AstNode* andp = new AstAnd(refp->fileline(), ref1p, ref2p);

		// or this to the others
		orp = (!orp) ? andp : new AstOr(refp->fileline(), orp, andp);

		if (envarp) {
		    AstNode* ref3p = new AstVarRef(refp->fileline(), newenp, false);
		    enp = (!enp) ? ref3p : new AstOr(ref3p->fileline(), enp, ref3p);
		}
		AstNode* tmp = new AstNot(newenp->fileline(), new AstVarRef(newenp->fileline(), newenp, false));
		undrivenp = ((!undrivenp) ? tmp
			     : new AstAnd(refp->fileline(), tmp, undrivenp));
	    }
	    if (!undrivenp) {  // No drivers on the bus
		V3Number ones(invarp->fileline(), lhsp->width()); ones.setAllBits1();
		undrivenp = new AstConst(invarp->fileline(), ones);
	    }
	    if (!outvarp) {
		// This is the final resolution of the tristate, so we apply
		// the pull direction to any undriven pins.
		V3Number pull(invarp->fileline(), lhsp->width());
		AstPull* pullp = (AstPull*)lhsp->user3p();
		if (pullp && pullp->direction() == 1) {
		    pull.setAllBits1();
		    UINFO(9,"Has pullup "<<pullp<<endl);
		} else {
		    pull.setAllBits0(); // default pull direction is down.
		}
		undrivenp = new AstAnd(invarp->fileline(), undrivenp,
				       new AstConst(invarp->fileline(), pull));
		orp = new AstOr(invarp->fileline(), orp, undrivenp);
	    } else {
		undrivenp->deleteTree(); undrivenp=NULL;
	    }
	    if (envarp) {
		nodep->addStmtp(new AstAssignW(enp->fileline(),
					       new AstVarRef(envarp->fileline(),
							     envarp, true), enp));
	    }
	    // __out (child) or <in> (parent) = drive-value expression
	    AstNode* assp = new AstAssignW(lhsp->fileline(),
					   new AstVarRef(lhsp->fileline(),
							 lhsp,
							 true),
					   orp);
	    assp->user2(U2_BOTH);  // Don't process further; already resolved
	    if (debug()>=9) assp->dumpTree(cout,"-lhsp-eqn: ");
	    nodep->addStmtp(assp);
	    // Delete the map and vector list now that we have expanded it.
	    m_lhsmap.erase(invarp);
	    delete refs;
	}
    }

    // VISITORS
    virtual void visit(AstConst* nodep, AstNUser*) {
	UINFO(9,dbgState()<<nodep<<endl);
	if (m_graphing) {
	    if (!m_alhs && nodep->num().hasZ()) {
		m_tgraph.setTristate(nodep);
	    }
	} else {
	    // Detect any Z consts and convert them to 0's with an enable that is also 0.
	    if (m_alhs && nodep->user1p()) {
		// A pin with 1'b0 or similar connection results in an assign with constant on LHS
		// due to the pinReconnectSimple call in visit AstPin.
		// We can ignore the output override by making a temporary
		AstVar* varp = getCreateUnconnVarp(nodep, nodep->dtypep());
		AstNode* newp = new AstVarRef(nodep->fileline(), varp, true);
		UINFO(9," const->"<<newp<<endl);
		nodep->replaceWith(newp);
		pushDeletep(nodep); nodep = NULL;
	    }
	    else if (m_tgraph.isTristate(nodep)) {
		m_tgraph.didProcess(nodep);
		FileLine* fl = nodep->fileline();
		V3Number numz (fl,nodep->width()); numz.opBitsZ(nodep->num());  //Z->1, else 0
		V3Number numz0(fl,nodep->width()); numz0.opNot(numz); // Z->0, else 1
		V3Number num1 (fl,nodep->width()); num1.opAnd(nodep->num(),numz0);  // 01X->01X, Z->0
		AstConst* newconstp = new AstConst(fl, num1);
		AstConst* enp       = new AstConst(fl, numz0);
		nodep->replaceWith(newconstp);
		pushDeletep(nodep); nodep = NULL;
		newconstp->user1p(enp); // propagate up constant with non-Z bits as 1
	    }
	}
    }

    virtual void visit(AstCond* nodep, AstNUser*) {
	if (m_graphing) {
	    nodep->iterateChildren(*this);
	    if (m_alhs) {
		associateLogic(nodep, nodep->expr1p());
		associateLogic(nodep, nodep->expr2p());
	    } else {
		associateLogic(nodep->expr1p(), nodep);
		associateLogic(nodep->expr2p(), nodep);
	    }
	} else {
	    if (m_alhs && nodep->user1p()) { nodep->v3error("Unsupported LHS tristate construct: "<<nodep->prettyTypeName()); return; }
	    nodep->iterateChildren(*this);
	    UINFO(9,dbgState()<<nodep<<endl);
	    // Generate the new output enable signal for this cond if either
	    // expression 1 or 2 have an output enable '__en' signal. If the
	    // condition has an enable, not sure what to do, so generate an
	    // error.
	    AstNode* condp  = nodep->condp();
	    if (condp->user1p()) {
		condp->v3error("Unsupported: don't know how to deal with tristate logic in the conditional expression");
	    }
	    AstNode* expr1p = nodep->expr1p();
	    AstNode* expr2p = nodep->expr2p();
	    if (expr1p->user1p() || expr2p->user1p()) {  // else no tristates
		m_tgraph.didProcess(nodep);
		AstNode* en1p = getEnp(expr1p);
		AstNode* en2p = getEnp(expr2p);
		// The output enable of a cond is a cond of the output enable of the
		// two expressions with the same conditional.
		AstNode* enp = new AstCond(nodep->fileline(), condp->cloneTree(false), en1p, en2p);
		UINFO(9,"       newcond "<<enp<<endl);
		nodep->user1p(enp);  // propagate up COND(lhsp->enable, rhsp->enable)
		expr1p->user1p(NULL);
		expr2p->user1p(NULL);
	    }
	}
    }

    virtual void visit(AstSel* nodep, AstNUser*) {
	if (m_graphing) {
	    nodep->iterateChildren(*this);
	    if (m_alhs) {
		associateLogic(nodep, nodep->fromp());
	    } else {
		associateLogic(nodep->fromp(), nodep);
	    }
	} else {
	    if (m_alhs) {
		UINFO(9,dbgState()<<nodep<<endl);
		if (nodep->user1p()) {
		    // Form a "deposit" instruction.  Would be nicer if we made this a new AST type
		    AstNode* newp = newEnableDeposit(nodep, nodep->user1p()->castNode());
		    nodep->fromp()->user1p(newp);  // Push to varref (etc)
		    if (debug()>=9) newp->dumpTree(cout,"-assign-sel; ");
		    m_tgraph.didProcess(nodep);
		}
		nodep->iterateChildren(*this);
	    } else {
		nodep->iterateChildren(*this);
		UINFO(9,dbgState()<<nodep<<endl);
		if (nodep->lsbp()->user1p()) {
		    nodep->v3error("Unsupported RHS tristate construct: "<<nodep->prettyTypeName());
		}
		if (nodep->fromp()->user1p()) {  // SEL(VARREF,lsb)
		    AstNode* en1p = getEnp(nodep->fromp());
		    AstNode* enp = new AstSel(nodep->fileline(), en1p,
					      nodep->lsbp()->cloneTree(true), nodep->widthp()->cloneTree(true));
		    UINFO(9,"       newsel "<<enp<<endl);
		    nodep->user1p(enp); // propagate up SEL(fromp->enable, value)
		    m_tgraph.didProcess(nodep);
		}
	    }
	}
    }

    virtual void visit(AstConcat* nodep, AstNUser*) {
	if (m_graphing) {
	    nodep->iterateChildren(*this);
	    if (m_alhs) {
		associateLogic(nodep, nodep->lhsp());
		associateLogic(nodep, nodep->rhsp());
	    } else {
		associateLogic(nodep->lhsp(), nodep);
		associateLogic(nodep->rhsp(), nodep);
	    }
	}
	else {
	    if (m_alhs) {
		UINFO(9,dbgState()<<nodep<<endl);
		if (nodep->user1p()) {
		    // Each half of the concat gets a select of the enable expression
		    AstNode* enp = nodep->user1p()->castNode();
		    nodep->user1p(NULL);
		    nodep->lhsp()->user1p(new AstSel(nodep->fileline(),
						     enp->cloneTree(true),
						     nodep->rhsp()->width(),
						     nodep->lhsp()->width()));
		    nodep->rhsp()->user1p(new AstSel(nodep->fileline(),
						     enp,
						     0,
						     nodep->rhsp()->width()));
		    m_tgraph.didProcess(nodep);
		}
		nodep->iterateChildren(*this);
	    } else {
		nodep->iterateChildren(*this);
		UINFO(9,dbgState()<<nodep<<endl);
		// Generate the new output enable signal, just as a concat identical to the data concat
		AstNode* expr1p = nodep->lhsp();
		AstNode* expr2p = nodep->rhsp();
		if (expr1p->user1p() || expr2p->user1p()) { // else no tristates
		    m_tgraph.didProcess(nodep);
		    AstNode* en1p = getEnp(expr1p);
		    AstNode* en2p = getEnp(expr2p);
		    AstNode* enp = new AstConcat(nodep->fileline(), en1p, en2p);
		    UINFO(9,"       newconc "<<enp<<endl);
		    nodep->user1p(enp);  // propagate up CONCAT(lhsp->enable, rhsp->enable)
		    expr1p->user1p(NULL);
		    expr2p->user1p(NULL);
		}
	    }
	}
    }

    virtual void visit(AstBufIf1* nodep, AstNUser*) {
	// For BufIf1, the enable is the LHS expression
	nodep->iterateChildren(*this);
	UINFO(9,dbgState()<<nodep<<endl);
	if (m_graphing) {
	    associateLogic(nodep->rhsp(), nodep);
	    m_tgraph.setTristate(nodep);
	} else {
	    if (debug()>=9) nodep->backp()->dumpTree(cout,"-bufif: ");
	    if (m_alhs) { nodep->v3error("Unsupported LHS tristate construct: "<<nodep->prettyTypeName()); return; }
	    m_tgraph.didProcess(nodep);
	    AstNode* expr1p = nodep->lhsp()->unlinkFrBack();
	    AstNode* expr2p = nodep->rhsp()->unlinkFrBack();
	    AstNode* enp;
	    if (AstNode* en2p = expr2p->user1p()->castNode()) {
		enp = new AstAnd(nodep->fileline(), expr1p, en2p);
	    } else {
		enp = expr1p;
	    }
	    expr1p->user1p(NULL);
	    expr2p->user1p(enp);  // Becomes new node
	    // Don't need the BufIf any more, can just have the data direct
	    nodep->replaceWith(expr2p);
	    UINFO(9,"   bufif  datap="<<expr2p<<endl);
	    UINFO(9,"   bufif  enp="<<enp<<endl);
	    pushDeletep(nodep); nodep = NULL;
	}
    }

    void visitAndOr(AstNodeBiop* nodep, bool isAnd) {
	nodep->iterateChildren(*this);
	UINFO(9,dbgState()<<nodep<<endl);
	if (m_graphing) {
	    associateLogic(nodep->lhsp(), nodep);
	    associateLogic(nodep->rhsp(), nodep);
	} else {
	    if (m_alhs && nodep->user1p()) { nodep->v3error("Unsupported LHS tristate construct: "<<nodep->prettyTypeName()); return; }
	    // ANDs and Z's have issues. Earlier optimizations convert
	    // expressions like "(COND) ? 1'bz : 1'b0" to "COND & 1'bz". So we
	    // have to define what is means to AND 1'bz with other
	    // expressions. I don't think this is spec, but here I take the
	    // approach that when one expression is 1, that the Z passes. This
	    // makes the COND's work. It is probably better to not perform the
	    // conditional optimization if the bits are Z.
	    //
	    // ORs have the same issues as ANDs. Earlier optimizations convert
	    // expressions like "(COND) ? 1'bz : 1'b1" to "COND | 1'bz". So we
	    // have to define what is means to OR 1'bz with other
	    // expressions. Here I take the approach that when one expression
	    // is 0, that is passes the other.
	    AstNode* expr1p = nodep->lhsp();
	    AstNode* expr2p = nodep->rhsp();
	    if (!expr1p->user1p() && !expr2p->user1p()) {
		return; // no tristates in either expression, so nothing to do
	    }
	    m_tgraph.didProcess(nodep);
	    AstNode* en1p = getEnp(expr1p);
	    AstNode* en2p = getEnp(expr2p);
	    AstNode* subexpr1p = expr1p->cloneTree(false);
	    AstNode* subexpr2p = expr2p->cloneTree(false);
	    if (isAnd) {
		subexpr1p = new AstNot(nodep->fileline(), subexpr1p);
		subexpr2p = new AstNot(nodep->fileline(), subexpr2p);
	    }
	    // calc new output enable
	    AstNode* enp = new AstOr(nodep->fileline(),
				     new AstAnd(nodep->fileline(), en1p, en2p),
				     new AstOr(nodep->fileline(),
					       new AstAnd(nodep->fileline(),
							  en1p->cloneTree(false),
							  subexpr1p),
					       new AstAnd(nodep->fileline(),
							  en2p->cloneTree(false),
							  subexpr2p)));
	    UINFO(9,"       neweqn "<<enp<<endl);
	    nodep->user1p(enp);
	    expr1p->user1p(NULL);
	    expr2p->user1p(NULL);
	}
    }
    virtual void visit(AstAnd* nodep, AstNUser*) {
	visitAndOr(nodep,true);
    }
    virtual void visit(AstOr* nodep, AstNUser*) {
	visitAndOr(nodep,false);
    }

    void visitAssign(AstNodeAssign* nodep) {
	if (m_graphing) {
	    if (nodep->user2() & U2_GRAPHING) return;
	    nodep->user2(U2_GRAPHING);
	    m_logicp = nodep;
	    nodep->rhsp()->iterateAndNext(*this);
	    m_alhs = true;
	    nodep->lhsp()->iterateAndNext(*this);
	    m_alhs = false;
	    associateLogic(nodep->rhsp(), nodep);
	    associateLogic(nodep, nodep->lhsp());
	    m_logicp = NULL;
	} else {
	    if (nodep->user2() & U2_NONGRAPH) return;  // Iterated here, or created assignment to ignore
	    nodep->user2(U2_NONGRAPH);
	    nodep->rhsp()->iterateAndNext(*this);
	    UINFO(9,dbgState()<<nodep<<endl);
	    if (debug()>=9) nodep->dumpTree(cout,"-assign: ");
	    // if the rhsp of this assign statement has an output enable driver,
	    // then propage the corresponding output enable assign statement.
	    // down the lvalue tree by recursion for eventual attachment to
	    // the appropriate output signal's VarRef.
	    if (nodep->rhsp()->user1p()) {
		nodep->lhsp()->user1p(nodep->rhsp()->user1p());
		nodep->rhsp()->user1p(NULL);
		UINFO(9,"   enp<-rhs "<<nodep->lhsp()->user1p()<<endl);
		m_tgraph.didProcess(nodep);
	    }
	    m_alhs = true;  // And user1p() will indicate tristate equation, if any
	    nodep->lhsp()->iterateAndNext(*this);
	    m_alhs = false;
	}
    }
    virtual void visit(AstAssignW* nodep, AstNUser*) {
	visitAssign(nodep);
    }
    virtual void visit(AstAssign* nodep, AstNUser*) {
	visitAssign(nodep);
    }

    void visitCaseEq(AstNodeBiop* nodep, bool neq) {
	if (m_graphing) {
	    nodep->iterateChildren(*this);
	} else {
	    checkUnhandled(nodep);
	    // Unsupported: A === 3'b000 should compare with the enables, but we don't do
	    // so at present, we only compare if there is a z in the equation.
	    // Otherwise we'd need to attach an enable to every signal, then optimize them
	    // away later when we determine the signal has no tristate
	    nodep->iterateChildren(*this);
	    UINFO(9,dbgState()<<nodep<<endl);
	    AstConst* constp = nodep->lhsp()->castConst();  // Constification always moves const to LHS
	    AstVarRef* varrefp = nodep->rhsp()->castVarRef();  // Input variable
	    if (constp && constp->user1p() && varrefp) {
		// 3'b1z0 -> ((3'b101 == in__en) && (3'b100 == in))
		varrefp->unlinkFrBack();
		FileLine* fl = nodep->fileline();
		V3Number oneIfEn = constp->user1p()->castNode()->castConst()->num();  // visit(AstConst) already split into en/ones
		V3Number oneIfEnOne = constp->num();
		AstVar* envarp = getCreateEnVarp(varrefp->varp());
		AstNode* newp = new AstLogAnd (fl, new AstEq (fl, new AstConst(fl, oneIfEn),
							      new AstVarRef(fl, envarp, false)),
					       // Keep the caseeq if there are X's present
					       new AstEqCase(fl, new AstConst(fl, oneIfEnOne),
							     varrefp));
		if (neq) newp = new AstLogNot(fl, newp);
		UINFO(9,"       newceq "<<newp<<endl);
		if (debug()>=9) nodep->dumpTree(cout,"-caseeq-old: ");
		if (debug()>=9) newp->dumpTree(cout,"-caseeq-new: ");
		nodep->replaceWith(newp);
		pushDeletep(nodep); nodep=NULL;
	    } else {
		checkUnhandled(nodep);
	    }
	}
    }
    void visitEqNeqWild(AstNodeBiop* nodep) {
	if (!nodep->rhsp()->castConst()) {
	    nodep->v3error("Unsupported: RHS of ==? or !=? must be constant to be synthesizable");  // Says spec.
	    // rhs we want to keep X/Z intact, so otherwise ignore
	}
	nodep->lhsp()->iterateAndNext(*this);
	if (nodep->lhsp()->user1p()) { nodep->v3error("Unsupported LHS tristate construct: "<<nodep->prettyTypeName()); return; }
    }
    virtual void visit(AstEqCase* nodep, AstNUser*) {
	visitCaseEq(nodep,false);
    }
    virtual void visit(AstNeqCase* nodep, AstNUser*) {
	visitCaseEq(nodep,true);
    }
    virtual void visit(AstEqWild* nodep, AstNUser*) {
	visitEqNeqWild(nodep);
    }
    virtual void visit(AstNeqWild* nodep, AstNUser*) {
	visitEqNeqWild(nodep);
    }

    virtual void visit(AstPull* nodep, AstNUser*) {
	UINFO(9,dbgState()<<nodep<<endl);
	if (m_graphing) {
	    if (AstVarRef* lhsp = nodep->lhsp()->castVarRef()) {
		lhsp->lvalue(true);
		m_logicp = nodep;
		m_tgraph.setTristate(nodep);
		associateLogic(nodep, lhsp->varp());
		m_logicp = NULL;
	    } else {
		nodep->v3error("Unsupported pullup/down (weak driver) construct.");
	    }
	} else {
	    // Replace any pullup/pulldowns with assignw logic and set the
	    // direction of the pull in the user3() data on the var.  Given
	    // the complexity of merging tristate drivers at any level, the
	    // current limitation of this implementation is that a pullup/down
	    // gets applied to all bits of a bus and a bus cannot have drivers
	    // in opposite directions on indvidual pins.
	    if (AstVarRef* lhsp = nodep->lhsp()->castVarRef()) {
		lhsp->lvalue(true);
		m_tgraph.didProcess(nodep);
		m_tgraph.didProcess(lhsp->varp());
		AstVar* varp = lhsp->varp();
		setPullDirection(varp, nodep);
	    } else {
		nodep->v3error("Unsupported pullup/down (weak driver) construct.");
	    }
	    nodep->unlinkFrBack();
	    pushDeletep(nodep); nodep = NULL;  // Node must persist as user3p points to it
	}
    }

    void iteratePinGuts(AstPin* nodep) {
	if (m_graphing) {
	    m_logicp = nodep;
	    if (nodep->exprp()) {
		associateLogic(nodep->exprp(), nodep);
		associateLogic(nodep, nodep->exprp());
	    }
	    nodep->iterateChildren(*this);
	    m_logicp = NULL;
	} else {
	    // All heavy lifting completed in graph visitor.
	    if (nodep->exprp()) {
		m_tgraph.didProcess(nodep);
	    }
	    nodep->iterateChildren(*this);
	}
    }

    // .tri(SEL(trisig,x)) becomes
    //   INPUT:   -> (VARREF(trisig__pinin)),
    //               trisig__pinin = SEL(trisig,x)       // via pinReconnectSimple
    //   OUTPUT:  -> (VARREF(trisig__pinout))
    //               SEL(trisig,x) = trisig__pinout
    //					^-- ->user1p() == trisig__pinen
    //   ENABLE:  -> (VARREF(trisig__pinen)
    // Added complication is the signal may be an output/inout or just input with tie off (or not) up top
    //     PIN	PORT	NEW PORTS AND CONNECTIONS
    //     N/C	input	in(from-resolver), __en(to-resolver-only), __out(to-resolver-only)
    //     N/C	inout	Spec says illegal
    //     N/C	output	Unsupported; Illegal?
    //     wire	input	in(from-resolver-with-wire-value), __en(from-resolver-wire), __out(to-resolver-only)
    //     wire	inout	in, __en, __out
    //     wire	output	in, __en, __out
    //     const input	in(from-resolver-with-const-value), __en(from-resolver-const), __out(to-resolver-only)
    //     const inout	Spec says illegal
    //     const output	Unsupported; Illegal?
    virtual void visit(AstPin* nodep, AstNUser*) {
	if (m_graphing) {
	    if (nodep->user2() & U2_GRAPHING) return;  // This pin is already expanded
	    nodep->user2(U2_GRAPHING);
	    // Find child module's new variables.
	    AstVar* enModVarp = (AstVar*) nodep->modVarp()->user1p();
	    if (!enModVarp) {
		if (nodep->exprp()) {
		    // May have an output only that later connects to a tristate, so simplify now.
		    V3Inst::pinReconnectSimple(nodep, m_cellp, m_modp, false);
		}
		iteratePinGuts(nodep);
		return; // No __en signals on this pin
	    }
	    // Tristate exists:
	    UINFO(9,dbgState()<<nodep<<endl);
	    if (debug()>=9) nodep->dumpTree(cout,"-pin-pre: ");

	    // Empty/in-only; need Z to propagate
	    bool inDeclProcessing = (nodep->exprp()
				     && nodep->modVarp()->isInOnly()
				     // Need to consider the original state instead of current state
				     // as we converted tristates to inputs, which do not want to have this.
				     && !nodep->modVarp()->isDeclOutput());
	    if (!nodep->exprp()) { // No-connect; covert to empty connection
		UINFO(5,"Unconnected pin terminate "<<nodep<<endl);
		AstVar* ucVarp = getCreateUnconnVarp(nodep, nodep->modVarp()->dtypep());
		nodep->exprp(new AstVarRef(nodep->fileline(), ucVarp,
					   nodep->modVarp()->isOutput()));
		m_tgraph.setTristate(ucVarp);
		// We don't need a driver on the wire; the lack of one will default to tristate
	    } else if (inDeclProcessing) {   // Not an input that was a converted tristate
		// Input only may have driver in underneath module which would stomp
		// the input value.  So make a temporary connection.
		AstAssignW* reAssignp = V3Inst::pinReconnectSimple(nodep, m_cellp, m_modp, true, true);
		UINFO(5,"Input pin buffering: "<<reAssignp<<endl);
		m_tgraph.setTristate(reAssignp->lhsp());
	    }

	    // pinReconnectSimple needs to presume input or output behavior; we need both
	    // Therefore, create the enable, output and separate input pin, then pinReconnectSimple all

	    // Create the output enable pin, connect to new signal
	    AstNode* enrefp;
	    {
		AstVar* enVarp = new AstVar(nodep->fileline(),
					    AstVarType::MODULETEMP,
					    nodep->name() + "__en" + cvtToStr(m_unique++),
					    VFlagBitPacked(), enModVarp->width());
		UINFO(9,"       newenv "<<enVarp<<endl);
		AstPin* enpinp = new AstPin(nodep->fileline(),
					    nodep->pinNum(),
					    enModVarp->name(),  // should be {var}"__en"
					    new AstVarRef(nodep->fileline(), enVarp, true));
		enpinp->modVarp(enModVarp);
		UINFO(9,"       newpin "<<enpinp<<endl);
		enpinp->user2(U2_BOTH); // don't iterate the pin later
		nodep->addNextHere(enpinp);
		m_modp->addStmtp(enVarp);
		enrefp = new AstVarRef(nodep->fileline(), enVarp, false);
		UINFO(9,"       newvrf "<<enrefp<<endl);
		if (debug()>=9) enpinp->dumpTree(cout,"-pin-ena: ");
	    }
	    // Create new output pin
	    AstAssignW* outAssignp = NULL;  // If reconnected, the related assignment
	    AstPin* outpinp;
	    {
		AstVar* outModVarp = (AstVar*) nodep->modVarp()->user4p();
		AstNode* outexprp = nodep->exprp()->cloneTree(false);  // Note has lvalue() set
		outpinp = new AstPin(nodep->fileline(),
				     nodep->pinNum(),
				     outModVarp->name(),  // should be {var}"__out"
				     outexprp);
		outpinp->modVarp(outModVarp);
		UINFO(9,"       newpin "<<outpinp<<endl);
		outpinp->user2(U2_BOTH); // don't iterate the pin later
		nodep->addNextHere(outpinp);
		// Simplify
		if (inDeclProcessing) {   // Not an input that was a converted tristate
		    // The pin is an input, but we need an output
		    // The if() above is needed because the Visitor is simple, it will flip ArraySel's and such,
		    // but if the pin is an input the earlier reconnectSimple made it a VarRef without any ArraySel, etc
		    TristatePinVisitor visitor (outexprp, m_tgraph, true);
		}
		if (debug()>=9) outpinp->dumpTree(cout,"-pin-opr: ");
		outAssignp = V3Inst::pinReconnectSimple(outpinp, m_cellp, m_modp, true);  // Note may change outpinp->exprp()
		if (debug()>=9) outpinp->dumpTree(cout,"-pin-out: ");
		if (debug()>=9 && outAssignp) outAssignp->dumpTree(cout,"-pin-out: ");
		// Must still iterate the outAssignp, as need to build output equation
	    }

	    // Existing pin becomes an input, and we mark each resulting signal as tristate
	    TristatePinVisitor visitor (nodep->exprp(), m_tgraph, false);
	    AstNode* inAssignp = V3Inst::pinReconnectSimple(nodep, m_cellp, m_modp, true);  // Note may change nodep->exprp()
	    if (debug()>=9) nodep->dumpTree(cout,"-pin-in:  ");
	    if (debug()>=9 && inAssignp) inAssignp->dumpTree(cout,"-pin-as:  ");

	    // Connect enable to output signal
	    AstVarRef* exprrefp;  // Tristate variable that the Pin's expression refers to
	    if (!outAssignp) {
		exprrefp = outpinp->exprp()->castVarRef();
	    } else {
		exprrefp = outAssignp->rhsp()->castVarRef();  // This should be the same var as the output pin
	    }
	    if (!exprrefp) { // deal with simple varref port
		// pinReconnect should have converted this
		nodep->v3error("Unsupported tristate port expression: "<<nodep->exprp()->prettyTypeName());
	    } else {
		UINFO(9,"outref "<<exprrefp<<endl);
		exprrefp->user1p(enrefp);  // Mark as now tristated; iteration will pick it up from there
		if (!outAssignp) {
		    mapInsertLhsVarRef(exprrefp);  // insertTristates will convert
		    //			   // to a varref to the __out# variable
		} // else the assignment deals with the connection
	    }

	    // Propagate any pullups/pulldowns upwards if necessary
	    if (exprrefp) {
		if (AstPull* pullp = (AstPull*) nodep->modVarp()->user3p()) {
		    UINFO(9, "propagate pull on "<<exprrefp<<endl);
		    setPullDirection(exprrefp->varp(), pullp);
		}
	    }

	    // Don't need to visit the created assigns, as it was added at the end of the next links
	    // and normal iterateChild recursion will come back to them eventually.
	    // Mark the original signal as tristated
	    iteratePinGuts(nodep);
	}
	// Not graph building
	else {
	    if (nodep->user2() & U2_NONGRAPH) return;  // This pin is already expanded
	    nodep->user2(U2_NONGRAPH);
	    UINFO(9," "<<nodep<<endl);
	    iteratePinGuts(nodep);
	}
    }

    virtual void visit(AstVarRef* nodep, AstNUser*) {
	UINFO(9,dbgState()<<nodep<<endl);
	if (m_graphing) {
	    if (nodep->lvalue()) {
		associateLogic(nodep, nodep->varp());
	    } else {
		associateLogic(nodep->varp(), nodep);
	    }
	} else {
	    if (nodep->user2() & U2_NONGRAPH) return;  // Processed
	    nodep->user2(U2_NONGRAPH);
	    // Detect all var lhs drivers and adds them to the
	    // VarMap so that after the walk through the module we can expand
	    // any tristate logic on the driver.
	    if (nodep->lvalue() && m_tgraph.isTristate(nodep->varp())) {
		UINFO(9,"     Ref-to-lvalue "<<nodep<<endl);
		m_tgraph.didProcess(nodep);
		mapInsertLhsVarRef(nodep);
	    }
	    else if (!nodep->lvalue()
		     && !nodep->user1p()	// Not already processed, nor varref from visit(AstPin) creation
		     // Reference to another tristate variable
		     && m_tgraph.isTristate(nodep->varp())
		     // and in a position where it feeds upstream to another tristate
		     && m_tgraph.feedsTri(nodep)) {
		// Then propage the enable from the original variable
		UINFO(9,"     Ref-to-tri "<<nodep<<endl);
		AstVar* enVarp = getCreateEnVarp(nodep->varp());
		nodep->user1p(new AstVarRef(nodep->fileline(), enVarp, false));
	    }
	    if (m_alhs) {}  // NOP; user1() already passed down from assignment
	}
    }

    virtual void visit(AstVar* nodep, AstNUser*) {
	nodep->iterateChildren(*this);
	UINFO(9,dbgState()<<nodep<<endl);
	if (m_graphing) {
	    // If tri0/1 force a pullup
	    if (nodep->user2() & U2_GRAPHING) return;  // Already processed
	    nodep->user2(U2_GRAPHING);
	    if (nodep->isPulldown() || nodep->isPullup()) {
		AstNode* newp = new AstPull(nodep->fileline(),
					    new AstVarRef(nodep->fileline(), nodep, true),
					    nodep->isPullup());
		UINFO(9,"       newpul "<<newp<<endl);
		nodep->addNextHere(newp);
		// We'll iterate on the new AstPull later
	    }
	    if (nodep->isInout()
		//|| varp->isOutput()
		// Note unconnected output only changes behavior vs. previous versions and causes outputs
		// that don't come from anywhere to possibly create connection errors.
		// One example of problems is this:  "output z;  task t; z <= {something}; endtask"
		) {
		UINFO(9,"  setTristate-inout "<<nodep<<endl);
		m_tgraph.setTristate(nodep);
	    }
	} else {  // !graphing
	    if (m_tgraph.isTristate(nodep)) {
		// nodep->isPulldown() || nodep->isPullup() handled in TristateGraphVisitor
		m_tgraph.didProcess(nodep);
	    }
	}
    }

    virtual void visit(AstNodeModule* nodep, AstNUser*) {
	UINFO(8, nodep<<endl);
	if (m_graphing) nodep->v3fatalSrc("Modules under modules not supported");  // Lots of per-module state breaks
	// Clear state
	m_tgraph.clear();
	m_unique = 0;
	m_logicp = NULL;
	m_lhsmap.clear();
	m_modp = nodep;
	// Walk the graph, finding all variables and tristate constructs
	{
	    m_graphing = true;
	    nodep->iterateChildren(*this);
	    m_graphing = false;
	}
	// Use graph to find tristate signals
	m_tgraph.graphWalk(nodep);
	// Build the LHS drivers map for this module
	nodep->iterateChildren(*this);
	// Insert new logic for all tristates
	insertTristates(nodep);
	m_modp = NULL;
    }

    virtual void visit(AstNodeFTask* nodep, AstNUser*) {
	// don't deal with functions
    }

    virtual void visit(AstCaseItem* nodep, AstNUser*) {
	// don't deal with casez compare '???? values
	nodep->bodysp()->iterateAndNext(*this);
    }

    virtual void visit(AstCell* nodep, AstNUser*) {
	m_cellp = nodep;
	m_alhs = false;
	nodep->iterateChildren(*this);
	m_cellp = NULL;
    }

    virtual void visit(AstNetlist* nodep, AstNUser*) {
	nodep->iterateChildrenBackwards(*this);
    }

    // Default: Just iterate
    virtual void visit(AstNode* nodep, AstNUser*) {
	nodep->iterateChildren(*this);
	checkUnhandled(nodep);
    }

public:
    // CONSTUCTORS
    TristateVisitor(AstNode* nodep) {
	m_graphing = false;
	m_modp  = NULL;
	m_cellp = NULL;
	m_unique = 0;
	m_alhs = false;
	m_logicp = NULL;
	m_tgraph.clear();
	nodep->accept(*this);
    }
    virtual ~TristateVisitor() {
	V3Stats::addStat("Tristate, Tristate resolved nets", m_statTriSigs);
    }
};

//######################################################################
// Tristate class functions

void V3Tristate::tristateAll(AstNetlist* nodep) {
    UINFO(2,__FUNCTION__<<": "<<endl);
    TristateVisitor visitor (nodep);
    V3Global::dumpCheckGlobalTree("tristate.tree", 0, v3Global.opt.dumpTreeLevel(__FILE__) >= 3);
}
