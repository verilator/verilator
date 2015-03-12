// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Add Unknown assigns
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
// V3Unknown's Transformations:
//
// Each module:
//	TBD: Eliminate tristates by adding __in, __inen, __en wires in parallel
//	    Need __en in changed list if a signal is on the LHS of a assign
//	Constants:
//	    RHS, Replace 5'bx_1_x with a module global we init to a random value
//		CONST(5'bx_1_x) -> VARREF(_{numberedtemp})
//				-> VAR(_{numberedtemp})
//				-> INITIAL(VARREF(_{numberedtemp}), OR(5'bx_1_x,AND(random,5'b0_1_x))
//		OPTIMIZE: Must not collapse this initial back into the equation.
//
//*************************************************************************

#include "config_build.h"
#include "verilatedos.h"
#include <cstdio>
#include <cstdarg>
#include <unistd.h>
#include <algorithm>

#include "V3Global.h"
#include "V3Unknown.h"
#include "V3Ast.h"
#include "V3Const.h"
#include "V3Stats.h"

//######################################################################

class UnknownVisitor : public AstNVisitor {
private:
    // NODE STATE
    // Cleared on Netlist
    //  AstSel::user()		-> bool.  Set true if already processed
    //  AstArraySel::user()	-> bool.  Set true if already processed
    //  AstNode::user2p()	-> AstIf* Inserted if assignment for conditional
    AstUser1InUse	m_inuser1;
    AstUser2InUse	m_inuser2;

    // STATE
    AstNodeModule*	m_modp;		// Current module
    bool		m_constXCvt;	// Convert X's
    V3Double0		m_statUnkVars;	// Statistic tracking
    AstAssignW*		m_assignwp;	// Current assignment
    AstAssignDly*	m_assigndlyp;	// Current assignment

    // METHODS
    static int debug() {
	static int level = -1;
	if (VL_UNLIKELY(level < 0)) level = v3Global.opt.debugSrcLevel(__FILE__);
	return level;
    }

    void replaceBoundLvalue(AstNode* nodep, AstNode* condp) {
	// Spec says a out-of-range LHS SEL results in a NOP.
	// This is a PITA.  We could:
	//  1. IF(...) around an ASSIGN,
	//     but that would break a "foo[TOO_BIG]=$fopen(...)".
	//  2. Hack to extend the size of the output structure
	//     by one bit, and write to that temporary, but never read it.
	//     That makes there be two widths() and is likely a bug farm.
	//  3. Make a special SEL to choose between the real lvalue
	//     and a temporary NOP register.
	//  4. Assign to a temp, then IF that assignment.
	//     This is suspected to be nicest to later optimizations.
	// 4 seems best but breaks later optimizations.  3 was tried,
	// but makes a mess in the emitter as lvalue switching is needed.  So 4.
	// SEL(...) -> temp
	//             if (COND(LTE(bit<=maxlsb))) ASSIGN(SEL(...)),temp)
	if (m_assignwp) {
	    // Wire assigns must become always statements to deal with insertion
	    // of multiple statements.  Perhaps someday make all wassigns into always's?
	    UINFO(5,"     IM_WireRep  "<<m_assignwp<<endl);
	    m_assignwp->convertToAlways(); pushDeletep(m_assignwp); m_assignwp=NULL;
	}
	bool needDly = (m_assigndlyp != NULL);
	if (m_assigndlyp) {
	    // Delayed assignments become normal assignments,
	    // then the temp created becomes the delayed assignment
	    AstNode* newp = new AstAssign(m_assigndlyp->fileline(),
					  m_assigndlyp->lhsp()->unlinkFrBackWithNext(),
					  m_assigndlyp->rhsp()->unlinkFrBackWithNext());
	    m_assigndlyp->replaceWith(newp); pushDeletep(m_assigndlyp); m_assigndlyp=NULL;
	}
	AstNode* prep = nodep;

	// Scan back to put the condlvalue above all selects (IE top of the lvalue)
	while (prep->backp()->castNodeSel()
	       || prep->backp()->castSel()) {
	    prep=prep->backp();
	}
	FileLine* fl = nodep->fileline();
	nodep=NULL;  // Zap it so we don't use it by mistake - use prep

	// Already exists; rather than IF(a,... IF(b... optimize to IF(a&&b,
	// Saves us teaching V3Const how to optimize, and it won't be needed again.
	if (AstIf* ifp = prep->user2p()->castNode()->castIf()) {
	    if (needDly) prep->v3fatalSrc("Should have already converted to non-delay");
	    AstNRelinker replaceHandle;
	    AstNode* earliercondp = ifp->condp()->unlinkFrBack(&replaceHandle);
	    AstNode* newp = new AstLogAnd (condp->fileline(),
					   condp,
					   earliercondp);
	    UINFO(4, "Edit BOUNDLVALUE "<<newp<<endl);
	    replaceHandle.relink(newp);
	}
	else {
	    string name = ((string)"__Vlvbound"+cvtToStr(m_modp->varNumGetInc()));
	    AstVar* varp = new AstVar(fl, AstVarType::MODULETEMP, name,
				      prep->dtypep());
	    m_modp->addStmtp(varp);

	    AstNode* abovep = prep->backp();  // Grab above point before lose it w/ next replace
	    prep->replaceWith(new AstVarRef(fl, varp, true));
	    AstNode* newp = new AstIf(fl, condp,
				      (needDly
				       ? ((new AstAssignDly(fl, prep,
							    new AstVarRef(fl, varp, false)))->castNode())
				       : ((new AstAssign   (fl, prep,
							    new AstVarRef(fl, varp, false)))->castNode())),
				      NULL);
	    if (debug()>=9) newp->dumpTree(cout,"     _new: ");
	    abovep->addNextStmt(newp,abovep);
	    prep->user2p(newp);  // Save so we may LogAnd it next time
	}
    }

    // VISITORS
    virtual void visit(AstNodeModule* nodep, AstNUser*) {
	UINFO(4," MOD   "<<nodep<<endl);
	m_modp = nodep;
	m_constXCvt = true;
	nodep->iterateChildren(*this);
	m_modp = NULL;
    }
    virtual void visit(AstAssignDly* nodep, AstNUser*) {
	m_assigndlyp = nodep;
	nodep->iterateChildren(*this); nodep=NULL;  // May delete nodep.
	m_assigndlyp = NULL;
    }
    virtual void visit(AstAssignW* nodep, AstNUser*) {
	m_assignwp = nodep;
	nodep->iterateChildren(*this); nodep=NULL;  // May delete nodep.
	m_assignwp = NULL;
    }
    virtual void visit(AstCaseItem* nodep, AstNUser*) {
	m_constXCvt = false;  // Avoid losing the X's in casex
	nodep->condsp()->iterateAndNext(*this);
	m_constXCvt = true;
	nodep->bodysp()->iterateAndNext(*this);
    }
    virtual void visit(AstNodeDType* nodep, AstNUser*) {
	m_constXCvt = false;  // Avoid losing the X's in casex
	nodep->iterateChildren(*this);
	m_constXCvt = true;
    }
    void visitEqNeqCase(AstNodeBiop* nodep) {
	UINFO(4," N/EQCASE->EQ "<<nodep<<endl);
	V3Const::constifyEdit(nodep->lhsp());  // lhsp may change
	V3Const::constifyEdit(nodep->rhsp());  // rhsp may change
	if (nodep->lhsp()->castConst() && nodep->rhsp()->castConst()) {
	    // Both sides are constant, node can be constant
	    V3Const::constifyEdit(nodep); nodep=NULL;
	    return;
	} else {
	    AstNode* lhsp = nodep->lhsp()->unlinkFrBack();
	    AstNode* rhsp = nodep->rhsp()->unlinkFrBack();
	    AstNode* newp;
	    // If we got ==1'bx it can never be true (but 1'bx==1'bx can be!)
	    if (((lhsp->castConst() && lhsp->castConst()->num().isFourState())
		 || (rhsp->castConst() && rhsp->castConst()->num().isFourState()))) {
		V3Number num (nodep->fileline(), 1, (nodep->castEqCase()?0:1));
		newp = new AstConst (nodep->fileline(), num);
		lhsp->deleteTree(); lhsp=NULL;
		rhsp->deleteTree(); rhsp=NULL;
	    } else {
		if (nodep->castEqCase())
		newp = new AstEq (nodep->fileline(), lhsp, rhsp);
		else newp = new AstNeq (nodep->fileline(), lhsp, rhsp);
	    }
	    nodep->replaceWith(newp);
	    nodep->deleteTree(); nodep=NULL;
	    // Iterate tree now that we may have gotten rid of Xs
	    newp->iterateChildren(*this);
	}
    }
    void visitEqNeqWild(AstNodeBiop* nodep) {
	UINFO(4," N/EQWILD->EQ "<<nodep<<endl);
	V3Const::constifyEdit(nodep->lhsp());  // lhsp may change
	V3Const::constifyEdit(nodep->rhsp());  // rhsp may change
	if (nodep->lhsp()->castConst() && nodep->rhsp()->castConst()) {
	    // Both sides are constant, node can be constant
	    V3Const::constifyEdit(nodep); nodep=NULL;
	    return;
	} else {
	    AstNode* lhsp = nodep->lhsp()->unlinkFrBack();
	    AstNode* rhsp = nodep->rhsp()->unlinkFrBack();
	    AstNode* newp;
	    if (!rhsp->castConst()) {
		nodep->v3error("Unsupported: RHS of ==? or !=? must be constant to be synthesizable");  // Says spec.
		// Replace with anything that won't cause more errors
		newp = new AstEq (nodep->fileline(), lhsp, rhsp);
	    } else {
		// X or Z's become mask, ala case statements.
		V3Number nummask  (rhsp->fileline(), rhsp->width());
		nummask.opBitsNonX(rhsp->castConst()->num());
		V3Number numval   (rhsp->fileline(), rhsp->width());
		numval.opBitsOne  (rhsp->castConst()->num());
		AstNode* and1p = new AstAnd(nodep->fileline(), lhsp,
					    new AstConst(nodep->fileline(), nummask));
		AstNode* and2p = new AstConst(nodep->fileline(), numval);
		if (nodep->castEqWild())
		    newp  = new AstEq  (nodep->fileline(), and1p, and2p);
		else newp = new AstNeq (nodep->fileline(), and1p, and2p);
		rhsp->deleteTree(); rhsp=NULL;
	    }
	    nodep->replaceWith(newp);
	    nodep->deleteTree(); nodep=NULL;
	    // Iterate tree now that we may have gotten rid of the compare
	    newp->iterateChildren(*this);
	}
    }

    virtual void visit(AstEqCase* nodep, AstNUser*) {
	visitEqNeqCase(nodep);
    }
    virtual void visit(AstNeqCase* nodep, AstNUser*) {
	visitEqNeqCase(nodep);
    }
    virtual void visit(AstEqWild* nodep, AstNUser*) {
	visitEqNeqWild(nodep);
    }
    virtual void visit(AstNeqWild* nodep, AstNUser*) {
	visitEqNeqWild(nodep);
    }
    virtual void visit(AstIsUnknown* nodep, AstNUser*) {
	nodep->iterateChildren(*this);
	// Ahh, we're two state, so this is easy
	UINFO(4," ISUNKNOWN->0 "<<nodep<<endl);
	V3Number zero (nodep->fileline(), 1, 0);
	AstConst* newp = new AstConst (nodep->fileline(), zero);
	nodep->replaceWith(newp);
	nodep->deleteTree(); nodep=NULL;
    }
    virtual void visit(AstConst* nodep, AstNUser*) {
	if (m_constXCvt
	    && nodep->num().isFourState()) {
	    UINFO(4," CONST4 "<<nodep<<endl);
	    if (debug()>=9) nodep->dumpTree(cout,"  Const_old: ");
	    // CONST(num) -> VARREF(newvarp)
	    //		-> VAR(newvarp)
	    //		-> INITIAL(VARREF(newvarp, OR(num_No_Xs,AND(random,num_1s_Where_X))
	    V3Number numb1 (nodep->fileline(), nodep->width());
	    numb1.opBitsOne(nodep->num());
	    V3Number numbx (nodep->fileline(), nodep->width());
	    numbx.opBitsXZ(nodep->num());
	    if (v3Global.opt.xAssign()!="unique") {
		// All X bits just become 0; fastest simulation, but not nice
		V3Number numnew (nodep->fileline(), numb1.width());
		if (v3Global.opt.xAssign()=="1") {
		    numnew.opOr(numb1, numbx);
		} else {
		    numnew.opAssign(numb1);
		}
		AstConst* newp = new AstConst(nodep->fileline(), numnew);
		nodep->replaceWith(newp);
		nodep->deleteTree(); nodep=NULL;
		UINFO(4,"   -> "<<newp<<endl);
	    } else {
		// Make a Vxrand variable
		// We use the special XTEMP type so it doesn't break pure functions
		if (!m_modp) nodep->v3fatalSrc("X number not under module");
		string newvarname = ((string)"__Vxrand"
				     +cvtToStr(m_modp->varNumGetInc()));
		AstVar* newvarp
		    = new AstVar (nodep->fileline(), AstVarType::XTEMP, newvarname,
				  VFlagLogicPacked(), nodep->width());
		++m_statUnkVars;
		AstNRelinker replaceHandle;
		nodep->unlinkFrBack(&replaceHandle);
		AstNodeVarRef* newref1p = new AstVarRef(nodep->fileline(), newvarp, false);
		replaceHandle.relink(newref1p);	    // Replace const with varref
		AstInitial* newinitp
		    = new AstInitial(
			nodep->fileline(),
			new AstAssign(
			    nodep->fileline(),
			    new AstVarRef(nodep->fileline(), newvarp, true),
			    new AstOr(nodep->fileline(),
				      new AstConst(nodep->fileline(),numb1),
				      new AstAnd(nodep->fileline(),
						 new AstConst(nodep->fileline(),numbx),
						 new AstRand(nodep->fileline(),
							     nodep->dtypep(), true)))));
		// Add inits in front of other statement.
		// In the future, we should stuff the initp into the module's constructor.
		AstNode* afterp = m_modp->stmtsp()->unlinkFrBackWithNext();
		m_modp->addStmtp(newvarp);
		m_modp->addStmtp(newinitp);
		m_modp->addStmtp(afterp);
		if (debug()>=9) newref1p->dumpTree(cout,"     _new: ");
		if (debug()>=9) newvarp->dumpTree(cout,"     _new: ");
		if (debug()>=9) newinitp->dumpTree(cout,"     _new: ");
		nodep->deleteTree(); nodep=NULL;
	    }
	}
    }

    void visit(AstSel* nodep, AstNUser*) {
	nodep->iterateChildren(*this);
	if (!nodep->user1SetOnce()) {
	    // Guard against reading/writing past end of bit vector array
	    AstNode* basefromp = AstArraySel::baseFromp(nodep);
	    bool lvalue = false;
	    if (AstNodeVarRef* varrefp = basefromp->castNodeVarRef()) {
		lvalue = varrefp->lvalue();
	    }
	    // Find range of dtype we are selecting from
	    // Similar code in V3Const::warnSelect
	    int maxmsb = nodep->fromp()->dtypep()->width()-1;
	    if (debug()>=9) nodep->dumpTree(cout,"sel_old: ");
	    V3Number maxmsbnum (nodep->fileline(), nodep->lsbp()->width(), maxmsb);

	    // If (maxmsb >= selected), we're in bound
	    AstNode* condp = new AstGte (nodep->fileline(),
					 new AstConst(nodep->fileline(), maxmsbnum),
					 nodep->lsbp()->cloneTree(false));
	    // See if the condition is constant true (e.g. always in bound due to constant select)
	    // Note below has null backp(); the Edit function knows how to deal with that.
	    condp = V3Const::constifyEdit(condp);
	    if (condp->isOne()) {
		// We don't need to add a conditional; we know the existing expression is ok
		condp->deleteTree();
	    }
	    else if (!lvalue) {
		// SEL(...) -> COND(LTE(bit<=maxmsb), ARRAYSEL(...), {width{1'bx}})
		AstNRelinker replaceHandle;
		nodep->unlinkFrBack(&replaceHandle);
		V3Number xnum (nodep->fileline(), nodep->width());
		xnum.setAllBitsX();
		AstNode* newp = new AstCondBound (nodep->fileline(),
						  condp,
						  nodep,
						  new AstConst(nodep->fileline(), xnum));
		if (debug()>=9) newp->dumpTree(cout,"        _new: ");
		// Link in conditional
		replaceHandle.relink(newp);
		// Added X's, tristate them too
		newp->accept(*this);
	    }
	    else { // lvalue
		replaceBoundLvalue(nodep, condp);
	    }
	}
    }

    virtual void visit(AstArraySel* nodep, AstNUser*) {
	nodep->iterateChildren(*this);
	if (!nodep->user1SetOnce()) {
	    if (debug()==9) nodep->dumpTree(cout,"-in: ");
	    // Guard against reading/writing past end of arrays
	    AstNode* basefromp = AstArraySel::baseFromp(nodep->fromp());
	    bool lvalue = false;
	    if (AstNodeVarRef* varrefp = basefromp->castNodeVarRef()) {
		lvalue = varrefp->lvalue();
	    } else if (basefromp->castConst()) {
		// If it's a PARAMETER[bit], then basefromp may be a constant instead of a varrefp
	    } else {
		nodep->v3fatalSrc("No VarRef or Const under ArraySel\n");
	    }
	    // Find range of dtype we are selecting from
	    int declElements = -1;
	    AstNodeDType* dtypep = nodep->fromp()->dtypep()->skipRefp();
	    if (!dtypep) nodep->v3fatalSrc("Select of non-selectable type");
	    if (AstNodeArrayDType* adtypep = dtypep->castNodeArrayDType()) {
		declElements = adtypep->elementsConst();
	    } else {
		nodep->v3error("Select from non-array "<<dtypep->prettyTypeName());
	    }
	    if (debug()>=9) nodep->dumpTree(cout,"arraysel_old: ");
	    V3Number widthnum (nodep->fileline(), nodep->bitp()->width(), declElements-1);

	    // See if the condition is constant true
	    AstNode* condp = new AstGte (nodep->fileline(),
					 new AstConst(nodep->fileline(), widthnum),
					 nodep->bitp()->cloneTree(false));
	    // Note below has null backp(); the Edit function knows how to deal with that.
	    condp = V3Const::constifyEdit(condp);
	    if (condp->isOne()) {
		// We don't need to add a conditional; we know the existing expression is ok
		condp->deleteTree();
	    }
	    else if (!lvalue
		     && !nodep->backp()->castArraySel()) {	// Too complicated and slow if mid-multidimension
		// ARRAYSEL(...) -> COND(LT(bit<maxbit), ARRAYSEL(...), {width{1'bx}})
		AstNRelinker replaceHandle;
		nodep->unlinkFrBack(&replaceHandle);
		V3Number xnum (nodep->fileline(), nodep->width());
		if (nodep->isString()) {
		    xnum = V3Number(V3Number::String(), nodep->fileline(), "");
		} else {
		    xnum.setAllBitsX();
		}
		AstNode* newp = new AstCondBound (nodep->fileline(),
						  condp,
						  nodep,
						  new AstConst(nodep->fileline(), xnum));
		if (debug()>=9) newp->dumpTree(cout,"        _new: ");
		// Link in conditional, can blow away temp xor
		replaceHandle.relink(newp);
		// Added X's, tristate them too
		newp->accept(*this);
	    }
	    else if (!lvalue) {  // Mid-multidimension read, just use zero
		// ARRAYSEL(...) -> ARRAYSEL(COND(LT(bit<maxbit), bit, 0))
		AstNRelinker replaceHandle;
		AstNode* bitp = nodep->bitp()->unlinkFrBack(&replaceHandle);
		V3Number zeronum (nodep->fileline(), bitp->width(), 0);
		AstNode* newp = new AstCondBound (bitp->fileline(),
						  condp,
						  bitp,
						  new AstConst(bitp->fileline(), zeronum));
		// Added X's, tristate them too
		if (debug()>=9) newp->dumpTree(cout,"        _new: ");
		replaceHandle.relink(newp);
		newp->accept(*this);
	    }
	    else {  // lvalue
		replaceBoundLvalue(nodep, condp);
	    }
	}
    }
    //--------------------
    // Default: Just iterate
    virtual void visit(AstNode* nodep, AstNUser*) {
	nodep->iterateChildren(*this);
    }

public:
    // CONSTUCTORS
    UnknownVisitor(AstNetlist* nodep) {
	m_modp = NULL;
	m_assigndlyp = NULL;
	m_assignwp = NULL;
	m_constXCvt = false;
	nodep->accept(*this);
    }
    virtual ~UnknownVisitor() {
	V3Stats::addStat("Unknowns, variables created", m_statUnkVars);
    }
};

//######################################################################
// Unknown class functions

void V3Unknown::unknownAll(AstNetlist* nodep) {
    UINFO(2,__FUNCTION__<<": "<<endl);
    UnknownVisitor visitor (nodep);
    V3Global::dumpCheckGlobalTree("unknown.tree", 0, v3Global.opt.dumpTreeLevel(__FILE__) >= 3);
}
