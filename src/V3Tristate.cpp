// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Deals with tristate logic
//
// Code available from: http://www.veripool.org/verilator
//
// AUTHORS: Lane Brooks with Wilson Snyder, Paul Wasson, Duane Gabli
//
//*************************************************************************
//
// Copyright 2003-2012 by Wilson Snyder.  This program is free software; you can
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
// corresponding two state reprasentation. At the lowest levels,
// expressions that have Z in them are converted into two state
// drivers and corresponding output enable signals are generated.
// These enable signals get transformed and regenerated through any
// logic that they may go through until they hit the module level.  At
// the module level, all the output enable signals from what can be
// many tristate drivers are combined together to produce a single
// driver and output enable. If the signal propigates up into higher
// modules, then new ports are created with for the signal with
// suffixes __en and __out. The original port is turned from an inout
// to an input and the __out port carries the output driver signal and
// the __en port carried the output enable for that driver.
//
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
// Given a node, flip any VarRef from LValue to RValue (i.e. make it an input)
// See also V3LinkLValue::linkLValueSet

class TristateInPinVisitor : public TristateBaseVisitor {
    // VISITORS
    virtual void visit(AstVarRef* nodep, AstNUser*) {
	if (nodep->lvalue()) {
	    UINFO(9," Flip-to-RValue "<<nodep<<endl);
	    nodep->lvalue(false);
	}
    }
    virtual void visit(AstNode* nodep, AstNUser*) {
	nodep->iterateChildren(*this);
    }
public:
    // CONSTUCTORS
    TristateInPinVisitor(AstNode* nodep) {
	nodep->accept(*this);
    }
    virtual ~TristateInPinVisitor() {}
};

//######################################################################

class TristateVisitor : public TristateBaseVisitor {
    // NODE STATE
    //   *::user1p		-> pointer to output enable __en expressions
    //   AstVarRef::user2	-> bool - already visited
    //   AstVar::user2		-> bool - already visited
    //   AstPin::user2		-> bool - already visited
    //   AstVar::user3p		-> AstPull* pullup/pulldown direction (input Var's user3p)
    //   AstVar::user4p		-> AstVar* pointer to output __out var (input Var's user2p)
    AstUser1InUse	m_inuser1;
    AstUser2InUse	m_inuser2;
    AstUser3InUse	m_inuser3;
    AstUser4InUse	m_inuser4;

    // TYPES
    typedef std::vector<AstVar*> VarVec;
    typedef std::vector<AstVarRef*> RefVec;
    typedef std::map<AstVar*, RefVec*> VarMap;

    // MEMBERS
    AstNodeModule*	m_modp;		// Current module
    AstCell*		m_cellp;	// current cell
    VarMap		m_lhsmap;	// LHS driver map
    VarVec		m_varvec;	// list of all vars for doing a final cleanup of inouts and undriven outputs that were not detected through finding Z logic in the module itself
    int			m_unique;
    bool		m_alhs;		// On LHS of assignment

    // STATS
    V3Double0 m_statTriSigs; // stat tracking

    // METHODS
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
	if (!m_modp) { newp->v3error("Unsupported: Creating tristate signal not underneath a module"); }
	else m_modp->addStmtp(newp);
	return newp;
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
		oldpullp->v3error("... Location of conflicing pull.");
	    }
	}
    }

    void checkUnhandled(AstNode* nodep) {
	// Check for unsupported tristate constructs. This is not a 100% check.
	// The best way would be to visit the tree again and find any user1p()
	// pointers that did not get picked up and expanded.
	if (m_alhs && nodep->user1p())
	    nodep->v3error("Unsupported LHS tristate construct: "<<nodep->prettyTypeName());
	if ((nodep->op1p() && nodep->op1p()->user1p())
	     || (nodep->op2p() && nodep->op2p()->user1p())
	     || (nodep->op3p() && nodep->op3p()->user1p())
	     || (nodep->op4p() && nodep->op4p()->user1p()))
	    nodep->v3error("Unsupported tristate construct: "<<nodep->prettyTypeName());
    }

    void insertTristates(AstNodeModule* nodep) {
	// Go through all the vars and find any that are outputs without drivers
	// or inouts without high-Z logic and put a 1'bz driver on them and add
	// them to the lhs map so they get expanded correctly.
	for (VarVec::iterator ii = m_varvec.begin(); ii != m_varvec.end(); ++ii) {
	    AstVar* varp = (*ii);
	    if (varp->isInout()
		//|| varp->isOutput()
		// Note unconnected output only changes behavior vs. previous versions and causes outputs
		// that don't come from anywhere to possibly create connection errors.
		// One example of problems is this:  "output z;  task t; z <= {something}; endtask"
		) {
		VarMap::iterator it = m_lhsmap.find(varp);
		if (it == m_lhsmap.end()) {
		    UINFO(8,"  Adding driver to var "<<varp<<endl);
		    V3Number zeros (varp->fileline(), varp->width());
		    zeros.setAllBits0();
		    AstConst* constp = new AstConst(varp->fileline(), zeros);
		    AstVarRef* varrefp = new AstVarRef(varp->fileline(), varp, true);
		    nodep->addStmtp(new AstAssignW(varp->fileline(), varrefp, constp));
		    visit(varrefp, NULL);
		    varrefp->user1p(new AstConst(varp->fileline(),zeros));//set output enable to always be off on this assign statement so that this var is floating
		}
	    }
	}

	// Now go through the lhs driver map and generate the output
	// enable logic for any tristates.
	for (VarMap::iterator nextit, it = m_lhsmap.begin(); it != m_lhsmap.end(); it = nextit) {
	    nextit = it; ++nextit;
	    AstVar* invarp = (*it).first;
	    RefVec* refs = (*it).second;

	    // Figure out if this var needs tristate expanded.
	    int needs_expanded = 0;
	    // If need enable signal gets expanded
	    if (invarp->user1p()) { needs_expanded++; }
	    // all inouts get expanded
	    if (invarp->isInout()) { needs_expanded++; }
	    // loop through to find all vars that have __en logic. They get expanded.
	    for (RefVec::iterator ii = refs->begin(); ii != refs->end(); ++ii) {
		AstVarRef* refp = (*ii);
		if (refp->user1p()) { needs_expanded++; }
	    }

	    if (needs_expanded == 0) {
		// This var has no tristate logic, so we leave it alone.
		UINFO(8, "  NO TRISTATE ON:" << invarp << endl);
		m_lhsmap.erase(invarp);
		delete refs;
		continue;
	    }

	    m_statTriSigs++;
	    UINFO(8, "  TRISTATE EXPANDING("<<needs_expanded<<"):" << invarp << endl);

	    // If the lhs var is a port, then we need to create ports for
	    // the output (__out) and output enable (__en) signals. The
	    // original port gets converted to an input. Don't tristate expand
	    // if this is the top level so that we can force the final
	    // tristate resolution at the top.
	    AstVar* envarp = NULL;
	    AstVar* outvarp = NULL;
	    AstVar* lhsp = invarp;
	    if (!nodep->isTop() && invarp->isIO()) {
		// This var becomes an input
		invarp->varType2In(); // convert existing port to type input
		// Create an output port (__out)
		AstVar* outvarp = getCreateOutVarp(invarp);
		outvarp->varType2Out();
		lhsp = outvarp;  // Must assign to __out, not to normal input signal
		// Create an output enable port (__en)
		envarp = getCreateEnVarp(invarp);  // May already be created if have foo === 1'bz somewhere
		envarp->varType2Out();
		//
		outvarp->user1p(envarp);
		outvarp->user3p(invarp->user3p());
		if (invarp->user3p()) UINFO(9, "propagate pull to "<<outvarp);
	    } else if (invarp->user1p()) {
		envarp = invarp->user1p()->castNode()->castVar();  // From CASEEQ, foo === 1'bz
	    }

	    AstNode* orp = NULL;
	    AstNode* andp = NULL;
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
					     VFlagLogicPacked(), w);
		nodep->addStmtp(newlhsp);
		refp->varp(newlhsp); // assign the new var to the varref
		refp->name(newlhsp->name());

		// create a new var for this drivers enable signal
		AstVar* newenp =  new AstVar(lhsp->fileline(),
					     AstVarType::MODULETEMP,
					     lhsp->name()+"__en"+cvtToStr(m_unique++),
					     VFlagLogicPacked(), w);

		nodep->addStmtp(newenp);
		nodep->addStmtp(new AstAssignW(refp->fileline(),
					       new AstVarRef(refp->fileline(), newenp, true),
					       getEnp(refp)));

		// now append this driver to the driver logic.
		AstNode* ref1p = new AstVarRef(nodep->fileline(), newlhsp,false);
		AstNode* ref2p = new AstVarRef(nodep->fileline(), newenp, false);
		andp = new AstAnd(nodep->fileline(), ref1p, ref2p);

		// or this to the others
		orp = (!orp) ? andp : new AstOr(nodep->fileline(), orp, andp);

		if (envarp) {
		    AstNode* ref3p = new AstVarRef(nodep->fileline(), newenp, false);
		    enp = (!enp) ? ref3p : new AstOr(ref3p->fileline(), enp, ref3p);
		}
		AstNode* tmp = new AstNot(newenp->fileline(), new AstVarRef(newenp->fileline(), newenp, false));
		undrivenp = ((!undrivenp) ? tmp
			     : new AstAnd(nodep->fileline(), tmp, undrivenp));
	    }

	    if (!undrivenp) {  // No drivers on the bus
		V3Number ones(nodep->fileline(), lhsp->width()); ones.setAllBits1();
		undrivenp = new AstConst(nodep->fileline(), ones);
	    }

	    if (!outvarp) {
		// This is the final resolution of the tristate, so we apply
		// the pull direction to any undriven pins.
		V3Number pull(nodep->fileline(), lhsp->width());
		AstPull* pullp = (AstPull*)lhsp->user3p();
		if (pullp && pullp->direction() == 1) {
		    pull.setAllBits1();
		    UINFO(9,"Has pullup "<<pullp<<endl);
		} else {
		    pull.setAllBits0(); // default pull direction is down.
		}
		undrivenp = new AstAnd(nodep->fileline(), undrivenp,
				       new AstConst(nodep->fileline(), pull));
		orp = new AstOr(nodep->fileline(), orp, undrivenp);
	    }
	    if (envarp) {
		nodep->addStmtp(new AstAssignW(enp->fileline(),
					       new AstVarRef(envarp->fileline(),
							     envarp, true), enp));
	    }

	    AstNode* assp = new AstAssignW(lhsp->fileline(),
					   new AstVarRef(lhsp->fileline(),
							 lhsp,
							 true),
					   orp);
	    if (debug()>=9) assp->dumpTree(cout,"-lhsp-eqn: ");
	    nodep->addStmtp(assp);
	    // Delete the map and vector list now that we have expanded it.
	    m_lhsmap.erase(invarp);
	    delete refs;
	}
    }

    // VISITORS
    virtual void visit(AstConst* nodep, AstNUser*) {
	UINFO(9,(m_alhs?"alhs":"")<<" "<<nodep<<endl);
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
	    return;
	}
	if (nodep->num().hasZ()) {
	    FileLine* fl = nodep->fileline();
	    V3Number numz (fl,nodep->width()); numz.opBitsZ(nodep->num());  //Z->1, else 0
	    V3Number numz0(fl,nodep->width()); numz0.opNot(numz); // Z->0, else 1
	    V3Number num1 (fl,nodep->width()); num1.opAnd(nodep->num(),numz0);  // 01X->01X, Z->0
	    AstConst* newconstp = new AstConst(fl, num1);
	    AstConst* enp       = new AstConst(fl, numz0);
	    nodep->replaceWith(newconstp);
	    pushDeletep(nodep); nodep = NULL;
	    newconstp->user1p(enp);
	}
    }

    virtual void visit(AstCond* nodep, AstNUser*) {
	if (m_alhs && nodep->user1p()) { nodep->v3error("Unsupported LHS tristate construct: "<<nodep->prettyTypeName()); return; }
	nodep->iterateChildren(*this);
	UINFO(9,(m_alhs?"alhs":"")<<" "<<nodep<<endl);
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
	if (!expr1p->user1p() && !expr2p->user1p()) {
	    return; // no tristates in either expression, so nothing to do
	}
	AstNode* en1p = getEnp(expr1p);
	AstNode* en2p = getEnp(expr2p);
	// The output enable of a cond is a cond of the output enable of the
	// two expressions with the same conditional.
	AstNode* enp = new AstCond(nodep->fileline(), condp->cloneTree(false), en1p, en2p);
	nodep->user1p(enp);
	expr1p->user1p(NULL);
	expr2p->user1p(NULL);
    }

    virtual void visit(AstSel* nodep, AstNUser*) {
	if (m_alhs) {
	    UINFO(9,"alhs "<<nodep<<endl);
	    if (nodep->user1p()) {
		// Form a "deposit" instruction.  Would be nicer if we made this a new AST type
		AstNode* newp = newEnableDeposit(nodep, nodep->user1p()->castNode());
		nodep->fromp()->user1p(newp);  // Push to varref (etc)
		if (debug()>=9) newp->dumpTree(cout,"-assign-sel; ");
	    }
	    nodep->iterateChildren(*this);
	} else {
	    nodep->iterateChildren(*this);
	    UINFO(9," "<<nodep<<endl);
	    if (nodep->fromp()->user1p() || nodep->lsbp()->user1p())
		nodep->v3error("Unsupported RHS tristate construct: "<<nodep->prettyTypeName());
	}
    }

    virtual void visit(AstConcat* nodep, AstNUser*) {
	if (m_alhs) {
	    UINFO(9,(m_alhs?"alhs":"")<<" "<<nodep<<endl);
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
	    }
	    nodep->iterateChildren(*this);
	} else {
	    nodep->iterateChildren(*this);
	    UINFO(9,(m_alhs?"alhs":"")<<" "<<nodep<<endl);
	    // Generate the new output enable signal, just as a concat identical to the data concat
	    AstNode* expr1p = nodep->lhsp();
	    AstNode* expr2p = nodep->rhsp();
	    if (!expr1p->user1p() && !expr2p->user1p()) {
		return; // no tristates in either expression, so nothing to do
	    }
	    AstNode* en1p = getEnp(expr1p);
	    AstNode* en2p = getEnp(expr2p);
	    AstNode* enp = new AstConcat(nodep->fileline(), en1p, en2p);
	    nodep->user1p(enp);
	    expr1p->user1p(NULL);
	    expr2p->user1p(NULL);
 	}
    }

    virtual void visit(AstBufIf1* nodep, AstNUser*) {
	// For BufIf1, the enable is the LHS expression
	nodep->iterateChildren(*this);
	UINFO(9,(m_alhs?"alhs":"")<<" "<<nodep<<endl);
	if (debug()>=9) nodep->backp()->dumpTree(cout,"-bufif: ");
	if (m_alhs) { nodep->v3error("Unsupported LHS tristate construct: "<<nodep->prettyTypeName()); return; }
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

    virtual void visit(AstAnd* nodep, AstNUser*) {
	nodep->iterateChildren(*this);
	UINFO(9,(m_alhs?"alhs":"")<<" "<<nodep<<endl);
	if (m_alhs && nodep->user1p()) { nodep->v3error("Unsupported LHS tristate construct: "<<nodep->prettyTypeName()); return; }
	// ANDs and Z's have issues. Earlier optimizations convert
	// expressions like "(COND) ? 1'bz : 1'b0" to "COND & 1'bz". So we
	// have to define what is means to AND 1'bz with other
	// expressions. I don't think this is spec, but here I take the
	// approach that when one expression is 1, that the Z passes. This
	// makes the COND's work. It is probably better to not perform the
	// conditional optimization if the bits are Z.
	AstNode* expr1p = nodep->lhsp();
	AstNode* expr2p = nodep->rhsp();
	if (!expr1p->user1p() && !expr2p->user1p()) {
	    return; // no tristates in either expression, so nothing to do
	}
	AstNode* en1p = getEnp(expr1p);
	AstNode* en2p = getEnp(expr2p);
	// calc new output enable.
	AstNode* enp = new AstOr(nodep->fileline(),
				 new AstAnd(nodep->fileline(), en1p, en2p),
				 new AstOr(nodep->fileline(),
					   new AstAnd(nodep->fileline(),
						      en1p->cloneTree(false),
						      new AstNot(nodep->fileline(), expr1p->cloneTree(false))),
					   new AstAnd(nodep->fileline(),
						      en2p->cloneTree(false),
						      new AstNot(nodep->fileline(), expr2p->cloneTree(false)))));
	nodep->user1p(enp);
	expr1p->user1p(NULL);
	expr2p->user1p(NULL);
    }

    virtual void visit(AstOr* nodep, AstNUser*) {
	nodep->iterateChildren(*this);
	UINFO(9,(m_alhs?"alhs":"")<<" "<<nodep<<endl);
	if (m_alhs && nodep->user1p()) { nodep->v3error("Unsupported LHS tristate construct: "<<nodep->prettyTypeName()); return; }
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
	AstNode* en1p = getEnp(expr1p);
	AstNode* en2p = getEnp(expr2p);
	// calc new output enable
	AstNode* enp = new AstOr(nodep->fileline(),
				 new AstAnd(nodep->fileline(), en1p, en2p),
				 new AstOr(nodep->fileline(),
					   new AstAnd(nodep->fileline(),
						      en1p->cloneTree(false),
						      expr1p->cloneTree(false)),
					   new AstAnd(nodep->fileline(),
						      en2p->cloneTree(false),
						      expr2p->cloneTree(false))));
	nodep->user1p(enp);
	expr1p->user1p(NULL);
	expr2p->user1p(NULL);
    }

    void visitAssign(AstNodeAssign* nodep) {
	nodep->rhsp()->iterateAndNext(*this);
	UINFO(9," "<<nodep<<endl);
	// if the rhsp of this assign statement has an output enable driver,
	// then propage the corresponding output enable assign statement.
	// down the lvalue tree by recursion for eventual attachment to
	// the appropriate output signal's VarRef.
	if (nodep->rhsp()->user1p()) {
	    nodep->lhsp()->user1p(nodep->rhsp()->user1p());
	    nodep->rhsp()->user1p(NULL);
	    UINFO(9,"   enp<-rhs "<<nodep->lhsp()->user1p()<<endl);
	}
	m_alhs = true;  // And user1p() will indicate tristate equation, if any
	nodep->lhsp()->iterateAndNext(*this);
	m_alhs = false;
    }
    virtual void visit(AstAssignW* nodep, AstNUser*) {
	visitAssign(nodep);
    }
    virtual void visit(AstAssign* nodep, AstNUser*) {
	visitAssign(nodep);
    }

    void visitCaseEq(AstNodeBiop* nodep, bool neq) {
	checkUnhandled(nodep);
	// Unsupported: A === 3'b000 should compare with the enables, but we don't do
	// so at present, we only compare if there is a z in the equation.
	// Otherwise we'd need to attach an enable to every signal, then optimize then
	// away later when we determine the signal has no tristate
	nodep->iterateChildren(*this);
	UINFO(9," "<<nodep<<endl);
	AstConst* constp = nodep->lhsp()->castConst();  // Constification always moves const to LHS
	AstVarRef* varrefp = nodep->rhsp()->castVarRef();  // Input variable
	if (constp && constp->user1p() && varrefp) {
	    // 3'b1z0 -> ((3'b101 == __en) && (3'b100 == __in))
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
	    if (debug()>=9) nodep->dumpTree(cout,"-caseeq-old: ");
	    if (debug()>=9) newp->dumpTree(cout,"-caseeq-new: ");
	    nodep->replaceWith(newp);
	    pushDeletep(nodep); nodep=NULL;
	} else {
	    checkUnhandled(nodep);
	}
    }
    virtual void visit(AstEqCase* nodep, AstNUser*) {
	visitCaseEq(nodep,false);
    }
    virtual void visit(AstNeqCase* nodep, AstNUser*) {
	visitCaseEq(nodep,true);
    }

    virtual void visit(AstPull* nodep, AstNUser*) {
	UINFO(9," "<<nodep<<endl);
	// Replace any pullup/pulldowns with assignw logic and set the
	// direction of the pull in the user2() data on the var.  Given
	// the complexity of merging tristate drivers at any level, the
	// current limitation of this implementation is that a pullup/down
	// gets applied to all bits of a bus and a bus cannot have drivers
	// in opposite directions on indvidual pins.
	if (nodep->lhsp()->castVarRef()) {
	    AstVarRef* lhsp = nodep->lhsp()->unlinkFrBack()->castVarRef();
	    lhsp->lvalue(true);
	    AstVar* varp = lhsp->varp();
	    setPullDirection(varp, nodep);
	    V3Number zeros (nodep->fileline(), varp->width());
	    zeros.setAllBits0();
	    AstConst* constp = new AstConst(nodep->fileline(), zeros);
	    constp->user1p(new AstConst(nodep->fileline(), zeros));//set output enable to always be off on this assign statement.
	    AstAssignW* assp = new AstAssignW(nodep->fileline(), lhsp, constp);
	    nodep->replaceWith(assp);
	    assp->iterateChildren(*this);
	    if (!varp->user3p()) {
		varp->user3p(nodep); //save off to indicate the pull direction
		pushDeletep(nodep); nodep = NULL;
	    }
	} else {
	    nodep->v3error("Unsupported pullup/down (weak driver) construct.");
	}
    }

    // .tri(SEL(trisig,x)) becomes
    //   INPUT:   -> (VARREF(trisig__pinin)),
    //               trisig__pinin = SEL(trisig,x)       // via pinReconnectSimple
    //   OUTPUT:  -> (VARREF(trisig__pinout))
    //   ENABLE:  -> (VARREF(trisig__pinen)
    //               SEL(trisig,x) = BUFIF1(enable__temp, trisig__pinen)
    // Added complication is the signal may be an output/inout or just input with tie off (or not) up top
    //     PIN	PORT	NEW PORTS AND CONNECTIONS
    //     N/C	input	in(from-resolver), __out(to-resolver-only), __en(to-resolver-only)
    //     N/C	inout	Spec says illegal
    //     N/C	output	Unsupported; Illegal?
    //     wire	input	in(from-resolver-with-wire-value), __out(to-resolver-only), __en(to-resolver-only)
    //     wire	inout	in, __out, __en
    //     wire	output	in, __out, __en
    //     const	input	in(from-resolver-with-const-value), __out(to-resolver-only), __en(to-resolver-only)
    //     const	inout	Spec says illegal
    //     const	output	Unsupported; Illegal?
    virtual void visit(AstPin* nodep, AstNUser*) {
	UINFO(9," "<<nodep<<endl);
	AstVar* enModVarp = (AstVar*) nodep->modVarp()->user1p();
	if (!enModVarp) { // no __en signals on this pin
	    nodep->iterateChildren(*this);
	    return;
	}
	if (nodep->user2()) { // this pin is already expanded
	    return;
	}
	nodep->user2(true); // mark this pin already expanded
	if (debug()>=9) nodep->dumpTree(cout,"-pin-pre: ");

	// pinReconnectSimple needs to presume input or output behavior; we need both
	// Therefore, create the enable, output and separate input pin, then pinReconnectSimple all

	if (!nodep->exprp()) { // No-connect; covert to empty connection
	    UINFO(5,"Unconnected pin terminate "<<nodep<<endl);
	    AstVar* ucVarp = getCreateUnconnVarp(nodep, nodep->modVarp()->dtypep());
	    nodep->exprp(new AstVarRef(nodep->fileline(), ucVarp,
				       nodep->modVarp()->isOutput()));
	    // We don't need a driver on the wire; the lack of one will default to tristate
	}

	// Create the output enable pin, connect to new signal
	AstNode* enrefp;
	{
	    AstVar* enVarp = new AstVar(nodep->fileline(),
					AstVarType::MODULETEMP,
					nodep->name() + "__en" + cvtToStr(m_unique),
					VFlagLogicPacked(), enModVarp->width());
	    AstPin* enpinp = new AstPin(nodep->fileline(),
					nodep->pinNum(),
					nodep->name() + "__en" + cvtToStr(m_unique++),
					new AstVarRef(nodep->fileline(), enVarp, true));
	    enpinp->modVarp(enModVarp);
	    enpinp->user2(true); // mark this visited
	    m_cellp->addPinsp(enpinp);
	    m_modp->addStmtp(enVarp);
	    enrefp = new AstVarRef(nodep->fileline(), enVarp, false);
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
				 nodep->name() + "__out"+cvtToStr(m_unique),
				 outexprp);
	    outpinp->modVarp(outModVarp);
	    outpinp->user2(true); // mark this visited
	    m_cellp->addPinsp(outpinp);
	    // Simplify
	    if (debug()>=9) outpinp->dumpTree(cout,"-pin-opr: ");
	    outAssignp = V3Inst::pinReconnectSimple(outpinp, m_cellp, m_modp, true);  // Note may change outpinp->exprp()
	    if (debug()>=9) outpinp->dumpTree(cout,"-pin-out: ");
	    if (debug()>=9 && outAssignp) outAssignp->dumpTree(cout,"-pin-out: ");
	}

	// Existing pin becomes an input
	TristateInPinVisitor visitor (nodep->exprp());
	V3Inst::pinReconnectSimple(nodep, m_cellp, m_modp, true);  // Note may change nodep->exprp()
	if (debug()>=9) nodep->dumpTree(cout,"-pin-in:  ");

	// Connect enable to output signal
	AstVarRef* refp;
	if (!outAssignp) {
	    refp = outpinp->exprp()->castVarRef();
	} else {
	    refp = outAssignp->rhsp()->castVarRef();  // This should be the same var as the output pin
	}
	if (!refp) { // deal with simple varref port
	    nodep->v3error("Unsupported tristate port expression: "<<nodep->exprp()->prettyTypeName());
	} else {
	    refp->user1p(enrefp);  // Mark as now tristated; iteration will pick it up from there
	    visit(refp, NULL); // visit this var ref to get it in the varmap
	}

	// Propagate any pullups/pulldowns upwards if necessary
	if (refp) {
	    if (AstPull* pullp = (AstPull*) nodep->modVarp()->user3p()) {
		UINFO(9, "propagate pull to "<<refp->varp());
		//selp: Note we don't currently obey selects; all bits must be consistently pulled
		setPullDirection(refp->varp(), pullp);
	    }
	}
	// Don't need to visit the created assigns, as it was added at the end of the next links
	// and normal iterateChild recursion will come back to them eventually.
    }

    virtual void visit(AstVarRef* nodep, AstNUser*) {
	UINFO(9,(m_alhs?"alhs":"")<<" "<<nodep<<endl);
	// Detect all var lhs drivers and adds them to the
	// VarMap so that after the walk through the module we can expand
	// any tristate logic on the driver.
	if (nodep->lvalue() && !nodep->user2()) {
	    nodep->user2(true); // mark this ref as visited
	    AstVar* key = nodep->varp();
	    VarMap::iterator it = m_lhsmap.find(key);
	    if (it == m_lhsmap.end()) {  // Not found
		RefVec* refs = new RefVec();
		refs->push_back(nodep);
		m_lhsmap.insert(make_pair(key, refs));
	    } else {
		(*it).second->push_back(nodep);
	    }
	}
	if (m_alhs) {}  // NOP; user1() already passed down from assignment
	nodep->iterateChildren(*this);
    }

    virtual void visit(AstVar* nodep, AstNUser*) {
	if (nodep->user2SetOnce()) return;  // Already processed
	UINFO(9," "<<nodep<<endl);
	// Adds all vars to the m_varvec list so that we can detect undriven
	// inouts and output and make them drive Z.
	m_varvec.push_back(nodep);
	nodep->iterateChildren(*this);
	// If tri0/1 force a pullup
	if (nodep->isPulldown() || nodep->isPullup()) {
	    AstNode* newp = new AstPull(nodep->fileline(),
					new AstVarRef(nodep->fileline(), nodep, true),
					nodep->isPullup());
	    UINFO(9,"New pull "<<newp);
	    m_modp->addStmtp(newp);
	    // We'll iterate on the new AstPull later
	}
    }

    virtual void visit(AstNodeModule* nodep, AstNUser*) {
	UINFO(8, nodep<<endl);
	// expand tristate nodes and build the LHS drivers map for this module
	m_unique = 0;
	m_lhsmap.clear();
	m_varvec.clear();
	m_modp = nodep;
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
	UINFO(9," "<<nodep<<endl);
	checkUnhandled(nodep);
    }

public:
    // CONSTUCTORS
    TristateVisitor(AstNode* nodep) {
	m_unique = 0;
	m_cellp = NULL;
	m_modp  = NULL;
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
}
