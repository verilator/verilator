//*************************************************************************
// DESCRIPTION: Verilator: Add Unknown assigns
//
// Code available from: http://www.veripool.org/verilator
//
// AUTHORS: Wilson Snyder with Paul Wasson, Duane Gabli
//
//*************************************************************************
//
// Copyright 2003-2009 by Wilson Snyder.  This program is free software; you can
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
    //  AstArraySel::user()	-> bool.  Set true if already processed
    AstUser1InUse	m_inuser1;

    // STATE
    AstModule*	m_modp;		// Current module
    bool	m_constXCvt;	// Convert X's
    V3Double0	m_statUnkVars;	// Statistic tracking

    // METHODS
    static int debug() {
	static int level = -1;
	if (VL_UNLIKELY(level < 0)) level = v3Global.opt.debugSrcLevel(__FILE__);
	return level;
    }

    // VISITORS
    virtual void visit(AstModule* nodep, AstNUser*) {
	UINFO(4," MOD   "<<nodep<<endl);
	m_modp = nodep;
	m_constXCvt = true;
	nodep->iterateChildren(*this);
	m_modp = NULL;
    }
    virtual void visit(AstCaseItem* nodep, AstNUser*) {
	m_constXCvt = false;  // Avoid loosing the X's in casex
	nodep->condsp()->iterateAndNext(*this);
	m_constXCvt = true;
	nodep->bodysp()->iterateAndNext(*this);
    }
    void visitEqNeqCase(AstNodeBiop* nodep) {
	UINFO(4," N/EQCASE->EQ "<<nodep<<endl);
	V3Const::constifyTree(nodep->lhsp());
	V3Const::constifyTree(nodep->rhsp());
	if (nodep->lhsp()->castConst() && nodep->rhsp()->castConst()) {
	    // Both sides are constant, node can be constant
	    V3Const::constifyTree(nodep); nodep=NULL;
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
	V3Const::constifyTree(nodep->lhsp());
	V3Const::constifyTree(nodep->rhsp());
	if (nodep->lhsp()->castConst() && nodep->rhsp()->castConst()) {
	    // Both sides are constant, node can be constant
	    V3Const::constifyTree(nodep); nodep=NULL;
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
		string newvarname = ((string)"__Vxrand"
				     +cvtToStr(m_modp->varNumGetInc()));
		AstVar* newvarp
		    = new AstVar (nodep->fileline(), AstVarType::XTEMP, newvarname,
				  new AstRange(nodep->fileline(), nodep->width()-1, 0));
		m_statUnkVars++;
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
							     nodep->width(), true)))));
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
	if (!nodep->user1()) {
	    nodep->user1(1);
	    // Guard against reading/writing past end of bit vector array
	    int maxmsb = 0;
	    bool lvalue = false;
	    AstNode* basefromp = AstArraySel::baseFromp(nodep->fromp());
	    if (AstNodeVarRef* varrefp = basefromp->castNodeVarRef()) {
		lvalue = varrefp->lvalue();
		maxmsb = (varrefp->varp()->width()-1);
	    } else {
		// If it's a PARAMETER[bit], then basefromp may be a constant instead of a varrefp
		maxmsb = basefromp->widthMin()-1;
	    }
	    int maxlsb = maxmsb - nodep->widthMin() + 1;
	    if (debug()>=9) nodep->dumpTree(cout,"sel_old: ");
	    V3Number maxlsbnum (nodep->fileline(), nodep->lsbp()->width(), maxlsb);
	    if (!lvalue) {
		// SEL(...) -> COND(LTE(bit<=maxlsb), ARRAYSEL(...), {width{1'bx}})
		AstNRelinker replaceHandle;
		nodep->unlinkFrBack(&replaceHandle);
		V3Number xnum (nodep->fileline(), nodep->width());
		xnum.setAllBitsX();
		// Put the new nodes under a temporary XOR operator we'll rip up in a moment.
		// This way when we constify, if the expression
		// is a constant it will still be under the XOR.
		AstXor* newp = new AstXor (
		    nodep->fileline(),
		    new AstCondBound (nodep->fileline(),
				      new AstLte (nodep->fileline(),
						  nodep->lsbp()->cloneTree(false),
						  new AstConst(nodep->fileline(), maxlsbnum)),
				      nodep,
				      new AstConst(nodep->fileline(), xnum)),
		    new AstConst (nodep->fileline(), 0)); // Just so it's a valid XOR
		if (debug()>=9) newp->dumpTree(cout,"        _new: ");
		V3Const::constifyTree(newp->lhsp());  // Just the conditional
		if (debug()>=9) newp->dumpTree(cout,"        _con: ");
		// Link in conditional, can blow away temp xor
		AstNode* nnp = newp->lhsp()->unlinkFrBack();
		replaceHandle.relink(nnp); nodep=NULL;
		newp->deleteTree(); newp=NULL;
		// Added X's, tristate them too
		nnp->accept(*this);
	    }
	    else {
		// SEL(...) -> SEL(COND(LTE(bit<=maxlsb), bit, 0))
		AstNRelinker replaceHandle;
		AstNode* lsbp = nodep->lsbp()->unlinkFrBack(&replaceHandle);
		V3Number zeronum (nodep->fileline(), lsbp->width(), 0);
		AstCondBound* newp = new AstCondBound
		    (lsbp->fileline(),
		     new AstLte (lsbp->fileline(),
				 lsbp->cloneTree(false),
				 new AstConst(lsbp->fileline(), maxlsbnum)),
		     lsbp,
		     new AstConst(lsbp->fileline(), zeronum));
		replaceHandle.relink(newp);
		// Added X's, tristate them too
		if (debug()>=9) nodep->dumpTree(cout,"        _new: ");
		V3Const::constifyTree(nodep);
		if (debug()>=9) nodep->dumpTree(cout,"        _con: ");
		nodep->iterateChildren(*this);
	    }
	}
    }

    virtual void visit(AstArraySel* nodep, AstNUser*) {
	nodep->iterateChildren(*this);
	if (!nodep->user1()) {
	    nodep->user1(1);
	    // Guard against reading/writing past end of arrays
	    AstNode* basefromp = AstArraySel::baseFromp(nodep->fromp());
	    int dimension      = AstArraySel::dimension(nodep->fromp());
	    int maxmsb = 0;
	    bool lvalue = false;
	    if (AstNodeVarRef* varrefp = basefromp->castNodeVarRef()) {
		lvalue = varrefp->lvalue();
		maxmsb = (varrefp->varp()->arrayp(dimension)->elementsConst()-1);
	    } else if (AstConst* lhconstp = basefromp->castConst()) {
		// If it's a PARAMETER[bit], then basefromp may be a constant instead of a varrefp
		maxmsb = lhconstp->widthMin();
	    } else {
		nodep->v3fatalSrc("No VarRef or Const under ArraySel\n");
	    }
	    if (debug()>=9) nodep->dumpTree(cout,"arraysel_old: ");
	    V3Number widthnum (nodep->fileline(), nodep->bitp()->width(), maxmsb);
	    if (!lvalue
		&& !nodep->backp()->castArraySel()) {	// Too complicated and slow if mid-multidimension
		// ARRAYSEL(...) -> COND(LT(bit<maxbit), ARRAYSEL(...), {width{1'bx}})
		AstNRelinker replaceHandle;
		nodep->unlinkFrBack(&replaceHandle);
		V3Number xnum (nodep->fileline(), nodep->width());
		xnum.setAllBitsX();
		// Put the new nodes under a temporary XOR operator we'll rip up in a moment.
		// This way when we constify, if the expression
		// is a constant it will still be under the XOR.
		AstXor* newp = new AstXor (
		    nodep->fileline(),
		    new AstCondBound (nodep->fileline(),
				       new AstLte (nodep->fileline(),
						   nodep->bitp()->cloneTree(false),
						   new AstConst(nodep->fileline(), widthnum)),
				       nodep,
				       new AstConst(nodep->fileline(), xnum)),
		    new AstConst (nodep->fileline(), 0)); // Just so it's a valid XOR
		if (debug()>=9) newp->dumpTree(cout,"        _new: ");
		V3Const::constifyTree(newp->lhsp());  // Just the conditional
		if (debug()>=9) newp->dumpTree(cout,"        _con: ");
		// Link in conditional, can blow away temp xor
		AstNode* nnp = newp->lhsp()->unlinkFrBack();
		replaceHandle.relink(nnp); nodep=NULL;
		newp->deleteTree(); newp=NULL;
		// Added X's, tristate them too
		nnp->accept(*this);
	    }
	    else {
		// ARRAYSEL(...) -> ARRAYSEL(COND(LT(bit<maxbit), bit, 0))
		AstNRelinker replaceHandle;
		AstNode* bitp = nodep->bitp()->unlinkFrBack(&replaceHandle);
		V3Number zeronum (nodep->fileline(), bitp->width(), 0);
		AstCondBound* newp = new AstCondBound
		    (bitp->fileline(),
		     new AstLte (bitp->fileline(),
				 bitp->cloneTree(false),
				 new AstConst(bitp->fileline(), widthnum)),
		     bitp,
		     new AstConst(bitp->fileline(), zeronum));
		replaceHandle.relink(newp);
		// Added X's, tristate them too
		if (debug()>=9) nodep->dumpTree(cout,"        _new: ");
		V3Const::constifyTree(nodep);
		if (debug()>=9) nodep->dumpTree(cout,"        _con: ");
		nodep->iterateChildren(*this);
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
    UnknownVisitor(AstNode* nodep) {
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
}
