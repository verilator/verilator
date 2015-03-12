// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Add temporaries, such as for expand nodes
//
// Code available from: http://www.veripool.org/verilator
//
//*************************************************************************
//
// Copyright 2004-2015 by Wilson Snyder.  This program is free software; you can
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
// V3Expand's Transformations:
//
// Each module:
//	Expand verilated.h macros into internal micro optimizations (RTL)
//	this will enable later optimizations.
//	Wide operands become assignments to each word of the vector, (WORDSELs)
//	    Note in this case that the widthMin is not correct for the MSW of
//	    the vector.  This must be accounted for if doing later constant
//	    propagation across signals.
//
//*************************************************************************

#include "config_build.h"
#include "verilatedos.h"
#include <cstdio>
#include <cstdarg>
#include <unistd.h>
#include <algorithm>

#include "V3Global.h"
#include "V3Expand.h"
#include "V3Ast.h"

//######################################################################
// Expand state, as a visitor of each AstNode

class ExpandVisitor : public AstNVisitor {
private:
    // NODE STATE
    //  AstNode::user1()	-> bool.  Processed
    AstUser1InUse	m_inuser1;

    // STATE
    AstNode*		m_stmtp;	// Current statement

    // METHODS
    static int debug() {
	static int level = -1;
	if (VL_UNLIKELY(level < 0)) level = v3Global.opt.debugSrcLevel(__FILE__);
	return level;
    }

    int longOrQuadWidth (AstNode* nodep) {
	// Return 32 or 64...
	return (nodep->width()+(VL_WORDSIZE-1)) & ~(VL_WORDSIZE-1);
    }
    V3Number notWideMask (AstNode* nodep) {
	return V3Number (nodep->fileline(), VL_WORDSIZE, ~VL_MASK_I(nodep->widthMin()));
    }
    V3Number wordMask (AstNode* nodep) {
	if (nodep->isWide()) {
	    return V3Number (nodep->fileline(), VL_WORDSIZE, VL_MASK_I(nodep->widthMin()));
	} else {
	    V3Number mask (nodep->fileline(), longOrQuadWidth(nodep));
	    mask.setMask(nodep->widthMin());
	    return mask;
	}
    }

    void insertBefore (AstNode* placep, AstNode* newp) {
	newp->user1(1);  // Already processed, don't need to re-iterate
	AstNRelinker linker;
	placep->unlinkFrBack(&linker);
	newp->addNext(placep);
	linker.relink(newp);
    }
    void replaceWithDelete (AstNode* nodep, AstNode* newp) {
	newp->user1(1);  // Already processed, don't need to re-iterate
	nodep->replaceWith(newp);
	nodep->deleteTree(); nodep=NULL;
    }
    AstNode* newWordAssign (AstNodeAssign* placep, int word, AstNode* lhsp, AstNode* rhsp) {
	AstAssign* newp = new AstAssign (placep->fileline(),
					 new AstWordSel (placep->fileline(),
							 lhsp->cloneTree(true),
							 new AstConst (placep->fileline(),
								       word)),
					 rhsp);
	return newp;
    }
    void addWordAssign (AstNodeAssign* placep, int word, AstNode* lhsp, AstNode* rhsp) {
	insertBefore (placep, newWordAssign(placep, word, lhsp, rhsp));
    }
    void addWordAssign (AstNodeAssign* placep, int word, AstNode* rhsp) {
	addWordAssign (placep, word, placep->lhsp(), rhsp);
    }

    void fixCloneLvalue (AstNode* nodep) {
	// In AstSel transforms, we call clone() on VarRefs that were lvalues,
	// but are now being used on the RHS of the assignment
	if (nodep->castVarRef()) nodep->castVarRef()->lvalue(false);
	// Iterate
	if (nodep->op1p()) fixCloneLvalue(nodep->op1p());
	if (nodep->op2p()) fixCloneLvalue(nodep->op2p());
	if (nodep->op3p()) fixCloneLvalue(nodep->op3p());
	if (nodep->op4p()) fixCloneLvalue(nodep->op4p());
    }

    AstNode* newAstWordSelClone (AstNode* nodep, int word) {
	// Get the specified word number from a wide array
	// Or, if it's a long/quad, do appropriate conversion to wide
	// Concat may pass negative word numbers, that means it wants a zero
	if (nodep->isWide() && word>=0 && word<nodep->widthWords()) {
	    return new AstWordSel (nodep->fileline(),
				   nodep->cloneTree(true),
				   new AstConst(nodep->fileline(), word));
	} else if (nodep->isQuad() && word==0) {
	    AstNode* quadfromp = nodep->cloneTree(true);
	    quadfromp->dtypeSetBitSized(VL_QUADSIZE,quadfromp->widthMin(),AstNumeric::UNSIGNED);
	    return new AstCCast (nodep->fileline(),
				 quadfromp,
				 VL_WORDSIZE);
	} else if (nodep->isQuad() && word==1) {
	    AstNode* quadfromp = nodep->cloneTree(true);
	    quadfromp->dtypeSetBitSized(VL_QUADSIZE,quadfromp->widthMin(),AstNumeric::UNSIGNED);
	    return new AstCCast (nodep->fileline(),
				 new AstShiftR (nodep->fileline(),
						quadfromp,
						new AstConst (nodep->fileline(), VL_WORDSIZE),
						VL_WORDSIZE),
				 VL_WORDSIZE);
	} else if (!nodep->isWide() && !nodep->isQuad() && word==0) {
	    return nodep->cloneTree(true);
	} else { // Out of bounds
	    return new AstConst (nodep->fileline(), 0);
	}
    }

    AstNode* newWordGrabShift (FileLine* fl, int word, AstNode* lhsp, int shift) {
	// Extract the expression to grab the value for the specified word, if it's the shift
	// of shift bits from lhsp
	AstNode* newp;
	// Negative word numbers requested for lhs when it's "before" what we want.
	// We get a 0 then.
	int othword = word - shift/VL_WORDSIZE;
	AstNode* llowp = newAstWordSelClone (lhsp, othword);
	if (int loffset = VL_BITBIT_I(shift)) {
	    AstNode* lhip = newAstWordSelClone (lhsp, othword-1);
	    int nbitsonright = VL_WORDSIZE-loffset;  // bits that end up in lword
	    newp = new AstOr
		(fl,
		 new AstAnd(fl,
			    new AstConst (fl, VL_MASK_I(loffset)),
			    new AstShiftR (fl,
					   lhip,
					   new AstConst(fl, nbitsonright),
					   VL_WORDSIZE)),
		 new AstAnd(fl,
			    new AstConst (fl, ~VL_MASK_I(loffset)),
			    new AstShiftL(fl,
					  llowp,
					  new AstConst(fl, loffset),
					  VL_WORDSIZE)));
	} else {
	    newp = llowp;
	}
	return newp;
    }

    AstNode* newSelBitWord(AstNode* lsbp, int wordAdder) {
	// Return equation to get the VL_BITWORD of a constant or non-constant
	if (lsbp->castConst()) {
	    return new AstConst (lsbp->fileline(),
				 wordAdder + VL_BITWORD_I(lsbp->castConst()->toUInt()));
	} else {
	    AstNode* shiftp = new AstShiftR (lsbp->fileline(),
					     lsbp->cloneTree(true),
					     new AstConst(lsbp->fileline(), VL_WORDSIZE_LOG2),
					     VL_WORDSIZE);
	    if (wordAdder != 0) {
		shiftp = new AstAdd (lsbp->fileline(),
				     // This is indexing a arraysel, so a 32 bit constant is fine
				     new AstConst (lsbp->fileline(), wordAdder),
				     shiftp);
	    }
	    return shiftp;
	}
    }

    AstNode* dropCondBound(AstNode* nodep) {
	// Experimental only...
	//  If there's a CONDBOUND safety to keep arrays in bounds,
	//  we're going to AND it to a value that always fits inside a
	//  word, so we don't need it.
	//if (nodep->castCondBound() && nodep->castCondBound()->lhsp()->castLte()) {
	//    nodep = nodep->castCondBound()->rhsp();
	//}
	return nodep;
    }

    AstNode* newSelBitBit(AstNode* lsbp) {
	// Return equation to get the VL_BITBIT of a constant or non-constant
	if (lsbp->castConst()) {
	    return new AstConst (lsbp->fileline(),
				 VL_BITBIT_I(lsbp->castConst()->toUInt()));
	} else {
	    return new AstAnd   (lsbp->fileline(),
				 new AstConst(lsbp->fileline(), VL_WORDSIZE-1),
				 dropCondBound(lsbp)->cloneTree(true));
	}
    }

    //====================

    bool expandWide (AstNodeAssign* nodep, AstConst* rhsp) {
	UINFO(8,"    Wordize ASSIGN(CONST) "<<nodep<<endl);
	// -> {for each_word{ ASSIGN(WORDSEL(wide,#),WORDSEL(CONST,#))}}
	if (rhsp->num().isFourState()) {
	    rhsp->v3error("Unsupported: 4-state numbers in this context");
	}
	for (int w=0; w<nodep->widthWords(); w++) {
	    V3Number num (nodep->fileline(), VL_WORDSIZE, rhsp->num().dataWord(w));
	    addWordAssign(nodep, w, new AstConst (nodep->fileline(), num));
	}
	return true;
    }
    //-------- Uniops
    bool expandWide (AstNodeAssign* nodep, AstVarRef* rhsp) {
	UINFO(8,"    Wordize ASSIGN(VARREF) "<<nodep<<endl);
	for (int w=0; w<nodep->widthWords(); w++) {
	    addWordAssign(nodep, w, newAstWordSelClone (rhsp, w));
	}
	return true;
    }
    bool expandWide (AstNodeAssign* nodep, AstArraySel* rhsp) {
	UINFO(8,"    Wordize ASSIGN(ARRAYSEL) "<<nodep<<endl);
	if (rhsp->length()!=1) nodep->v3fatalSrc("ArraySel with length!=1 should have been removed in V3Slice");
	for (int w=0; w<nodep->widthWords(); w++) {
	    addWordAssign(nodep, w, newAstWordSelClone (rhsp, w));
	}
	return true;
    }
    bool expandWide (AstNodeAssign* nodep, AstNot* rhsp) {
	UINFO(8,"    Wordize ASSIGN(NOT) "<<nodep<<endl);
	// -> {for each_word{ ASSIGN(WORDSEL(wide,#),NOT(WORDSEL(lhs,#))) }}
	for (int w=0; w<nodep->widthWords(); w++) {
	    addWordAssign(nodep, w, new AstNot (rhsp->fileline(),
						newAstWordSelClone (rhsp->lhsp(), w)));
	}
	return true;
    }
    //-------- Biops
    bool expandWide (AstNodeAssign* nodep, AstAnd* rhsp) {
	UINFO(8,"    Wordize ASSIGN(AND) "<<nodep<<endl);
	for (int w=0; w<nodep->widthWords(); w++) {
	    addWordAssign(nodep, w, new AstAnd (nodep->fileline(),
						newAstWordSelClone (rhsp->lhsp(), w),
						newAstWordSelClone (rhsp->rhsp(), w)));
	}
	return true;
    }
    bool expandWide (AstNodeAssign* nodep, AstOr* rhsp) {
	UINFO(8,"    Wordize ASSIGN(OR) "<<nodep<<endl);
	for (int w=0; w<nodep->widthWords(); w++) {
	    addWordAssign(nodep, w, new AstOr (nodep->fileline(),
					       newAstWordSelClone (rhsp->lhsp(), w),
					       newAstWordSelClone (rhsp->rhsp(), w)));
	}
	return true;
    }
    bool expandWide (AstNodeAssign* nodep, AstXor* rhsp) {
	UINFO(8,"    Wordize ASSIGN(XOR) "<<nodep<<endl);
	for (int w=0; w<nodep->widthWords(); w++) {
	    addWordAssign(nodep, w, new AstXor (nodep->fileline(),
						newAstWordSelClone (rhsp->lhsp(), w),
						newAstWordSelClone (rhsp->rhsp(), w)));
	}
	return true;
    }
    bool expandWide (AstNodeAssign* nodep, AstXnor* rhsp) {
	UINFO(8,"    Wordize ASSIGN(XNOR) "<<nodep<<endl);
	for (int w=0; w<nodep->widthWords(); w++) {
	    addWordAssign(nodep, w, new AstXnor (nodep->fileline(),
						 newAstWordSelClone (rhsp->lhsp(), w),
						 newAstWordSelClone (rhsp->rhsp(), w)));
	}
	return true;
    }
    //-------- Triops
    bool expandWide (AstNodeAssign* nodep, AstNodeCond* rhsp) {
	UINFO(8,"    Wordize ASSIGN(COND) "<<nodep<<endl);
	for (int w=0; w<nodep->widthWords(); w++) {
	    addWordAssign(nodep, w, new AstCond (nodep->fileline(),
						 rhsp->condp()->cloneTree(true),
						 newAstWordSelClone (rhsp->expr1p(), w),
						 newAstWordSelClone (rhsp->expr2p(), w)));
	}
	return true;
    }

    // VISITORS
    virtual void visit(AstExtend* nodep, AstNUser*) {
	if (nodep->user1SetOnce()) return;  // Process once
	nodep->iterateChildren(*this);
	if (nodep->isWide()) {
	    // See under ASSIGN(EXTEND)
	} else {
	    AstNode* lhsp = nodep->lhsp()->unlinkFrBack();
	    AstNode* newp = lhsp;
	    if (nodep->isQuad()) {
		if (lhsp->isQuad()) {
		    lhsp->dtypeFrom(nodep);	// Just mark it, else nop
		} else if (lhsp->isWide()) {
		    nodep->v3fatalSrc("extending larger thing into smaller?");
		} else {
		    UINFO(8,"    EXTEND(q<-l) "<<nodep<<endl);
		    newp = new AstCCast (nodep->fileline(), lhsp, nodep);
		}
	    } else { // Long
		if (lhsp->isQuad() || lhsp->isWide()) {
		    nodep->v3fatalSrc("extending larger thing into smaller?");
		} else {
		    lhsp->dtypeFrom(nodep);	// Just mark it, else nop
		}
	    }
	    replaceWithDelete(nodep,newp); nodep=NULL;
	}
    }
    bool expandWide (AstNodeAssign* nodep, AstExtend* rhsp) {
	UINFO(8,"    Wordize ASSIGN(EXTEND) "<<nodep<<endl);
	int w=0;
	for (w=0; w<rhsp->lhsp()->widthWords(); w++) {
	    addWordAssign(nodep, w, newAstWordSelClone (rhsp->lhsp(), w));
	}
	for (; w<nodep->widthWords(); w++) {
	    addWordAssign(nodep, w, new AstConst (rhsp->fileline(), 0));
	}
	return true;
    }

    virtual void visit(AstSel* nodep, AstNUser*) {
	if (nodep->user1SetOnce()) return;  // Process once
	nodep->iterateChildren(*this);
	// Remember, Sel's may have non-integer rhs, so need to optimize for that!
	if (nodep->widthMin()!=(int)nodep->widthConst()) nodep->v3fatalSrc("Width mismatch");
	if (nodep->backp()->castNodeAssign() && nodep==nodep->backp()->castNodeAssign()->lhsp()) {
	    // Sel is an LHS assignment select
	} else if (nodep->isWide()) {
	    // See under ASSIGN(WIDE)
	}
	else if (nodep->fromp()->isWide()) {
	    UINFO(8,"    SEL(wide) "<<nodep<<endl);
	    // Selection amounts
	    // Check for constant shifts & save some constification work later.
	    // Grab lowest bit(s)
	    AstNode* lowwordp = new AstWordSel (nodep->fromp()->fileline(),
						nodep->fromp()->cloneTree(true),
						newSelBitWord(nodep->lsbp(), 0));
	    if (nodep->isQuad() && !lowwordp->isQuad()) lowwordp = new AstCCast(nodep->fileline(), lowwordp, nodep);
	    AstNode* lowp = new AstShiftR (nodep->fileline(),
					   lowwordp,
					   newSelBitBit(nodep->lsbp()),
					   nodep->width());
	    // If > 1 bit, we might be crossing the word boundary
	    AstNode* midp=NULL;
	    V3Number zero (nodep->fileline(), longOrQuadWidth(nodep));
	    if (nodep->widthConst() > 1) {
		AstNode* midwordp = // SEL(from,[1+wordnum])
		    new AstWordSel (nodep->fromp()->fileline(),
				    nodep->fromp()->cloneTree(true),
				    newSelBitWord(nodep->lsbp(), 1));
		if (nodep->isQuad() && !midwordp->isQuad()) midwordp = new AstCCast(nodep->fileline(), midwordp, nodep);
		// If we're selecting bit zero, then all 32 bits in word 1 get shifted << by 32 bits
		// else we need to form the lower word, so we << by 31 or less
		// nbitsfromlow <= (lsb==0) ? 64-bitbit(lsb) : 32-bitbit(lsb)
		AstNode* midshiftp = new AstSub (nodep->lsbp()->fileline(),
						 new AstConst(nodep->lsbp()->fileline(), VL_WORDSIZE),
						 newSelBitBit(nodep->lsbp()));
		if (nodep->isQuad()) {
		    midshiftp =
			new AstCond (nodep->fileline(),
				     new AstEq (nodep->fileline(),
						new AstConst(nodep->fileline(), 0),
						newSelBitBit(nodep->lsbp())),
				     new AstConst(nodep->lsbp()->fileline(), VL_WORDSIZE),
				     midshiftp);
		}
		AstNode* midmayp = new AstShiftL (nodep->fileline(),
						  midwordp,
						  midshiftp,
						  nodep->width());
		if (nodep->isQuad()) {
		    midp = midmayp;   // Always grab from two words
		} else {
		    midp = new AstCond (nodep->fileline(),
					new AstEq (nodep->fileline(),
						   new AstConst(nodep->fileline(), 0),
						   newSelBitBit(nodep->lsbp())),
					new AstConst(nodep->fileline(), zero),
					midmayp);
		}
	    }
	    // If > 32 bits, we might be crossing the second word boundary
	    AstNode* hip=NULL;
	    if (nodep->widthConst() > VL_WORDSIZE) {
		AstNode* hiwordp = // SEL(from,[2+wordnum])
		    new AstWordSel (nodep->fromp()->fileline(),
				    nodep->fromp()->cloneTree(true),
				    newSelBitWord(nodep->lsbp(), 2));
		if (nodep->isQuad() && !hiwordp->isQuad()) hiwordp = new AstCCast(nodep->fileline(), hiwordp, nodep);
		AstNode* himayp =
		    new AstShiftL (nodep->fileline(),
				   hiwordp,
				   // nbitsfromlow_and_mid <= 64-bitbit(lsb)
				   new AstSub (nodep->lsbp()->fileline(),
					       new AstConst(nodep->lsbp()->fileline(), 64),
					       newSelBitBit(nodep->lsbp())),
				   nodep->width());
		// if (frombit==0) then ignore, else use it
		hip = new AstCond (nodep->fileline(),
				   new AstEq (nodep->fileline(),
					      new AstConst(nodep->fileline(), 0),
					      newSelBitBit(nodep->lsbp())),
				   new AstConst(nodep->fileline(), zero),
				   himayp);
	    }

	    AstNode* newp = lowp;
	    if (midp) newp = new AstOr (nodep->fileline(), midp, newp);
	    if (hip) newp = new AstOr (nodep->fileline(), hip, newp);
	    newp->dtypeFrom(nodep);
	    replaceWithDelete(nodep,newp); nodep=NULL;
	}
	else { // Long/Quad from Long/Quad
	    UINFO(8,"    SEL->SHIFT "<<nodep<<endl);
	    AstNode* fromp = nodep->fromp()->unlinkFrBack();
	    AstNode* lsbp = nodep->lsbp()->unlinkFrBack();
	    if (nodep->isQuad() && !fromp->isQuad()) fromp = new AstCCast(nodep->fileline(), fromp, nodep);
	    AstNode* newp = new AstShiftR (nodep->fileline(),
					   fromp,
					   dropCondBound(lsbp),
					   fromp->width());  // {large}>>32 requires 64-bit shift operation; then cast
	    newp->dtypeFrom(fromp);
	    if (!nodep->isQuad() && fromp->isQuad()) {
		newp = new AstCCast (newp->fileline(), newp, nodep);
	    }
	    newp->dtypeFrom(nodep);
	    replaceWithDelete(nodep,newp); nodep=NULL;
	}
    }

    bool expandWide (AstNodeAssign* nodep, AstSel* rhsp) {
	if (nodep->widthMin()!=(int)rhsp->widthConst()) nodep->v3fatalSrc("Width mismatch");
	if (rhsp->lsbp()->castConst() && VL_BITBIT_I(rhsp->lsbConst())==0) {
	    int lsb = rhsp->lsbConst();
	    UINFO(8,"    Wordize ASSIGN(SEL,align) "<<nodep<<endl);
	    for (int w=0; w<nodep->widthWords(); w++) {
		addWordAssign(nodep, w, newAstWordSelClone (rhsp->fromp(), w + VL_BITWORD_I(lsb)));
	    }
	    return true;
	} else {
	    UINFO(8,"    Wordize ASSIGN(EXTRACT,misalign) "<<nodep<<endl);
	    for (int w=0; w<nodep->widthWords(); w++) {
		// Grab lowest bits
		AstNode* lowwordp = new AstWordSel (rhsp->fileline(),
						    rhsp->fromp()->cloneTree(true),
						    newSelBitWord(rhsp->lsbp(), w));
		AstNode* lowp = new AstShiftR (rhsp->fileline(),
					       lowwordp,
					       newSelBitBit(rhsp->lsbp()),
					       VL_WORDSIZE);
		// Upper bits
		V3Number zero (nodep->fileline(), VL_WORDSIZE, 0);
		AstNode* midwordp = // SEL(from,[1+wordnum])
		    new AstWordSel (rhsp->fromp()->fileline(),
				    rhsp->fromp()->cloneTree(true),
				    newSelBitWord(rhsp->lsbp(), w+1));
		AstNode* midshiftp = new AstSub (rhsp->lsbp()->fileline(),
						 new AstConst(rhsp->lsbp()->fileline(), VL_WORDSIZE),
						 newSelBitBit(rhsp->lsbp()));
		AstNode* midmayp = new AstShiftL (rhsp->fileline(),
						  midwordp,
						  midshiftp,
						  VL_WORDSIZE);
		AstNode* midp = new AstCond (rhsp->fileline(),
					     new AstEq (rhsp->fileline(),
							new AstConst(rhsp->fileline(), 0),
							newSelBitBit(rhsp->lsbp())),
					     new AstConst(rhsp->fileline(), zero),
					     midmayp);
		AstNode* newp = new AstOr (nodep->fileline(), midp, lowp);
		addWordAssign(nodep, w, newp);
	    }
	    return true;
	}
    }

    bool expandLhs(AstNodeAssign* nodep, AstSel* lhsp) {
	// Possibilities
	//      destp: wide or narrow
	//	rhsp:  wide (destp must be wide), narrow, or 1 bit wide
	//	rhsp:  may be allones and can remove AND NOT gate
	//	lsbp:  constant or variable
	// Yuk.
	bool destwide = lhsp->fromp()->isWide();
	bool ones = nodep->rhsp()->isAllOnesV();
	if (lhsp->lsbp()->castConst()) {
	    // The code should work without this constant test, but it won't
	    // constify as nicely as we'd like.
	    AstNode* rhsp = nodep->rhsp()->unlinkFrBack();
	    AstNode* destp = lhsp->fromp()->unlinkFrBack();
	    int lsb = lhsp->lsbConst();
	    int msb = lhsp->msbConst();
	    V3Number maskset (nodep->fileline(), destp->widthMin());
	    for (int bit=lsb; bit<(msb+1); bit++) maskset.setBit(bit,1);
	    V3Number maskold (nodep->fileline(), destp->widthMin()); maskold.opNot(maskset);
	    if (destwide) {
		UINFO(8,"    ASSIGNSEL(const,wide) "<<nodep<<endl);
		for (int w=0; w<destp->widthWords(); w++) {
		    if (w>=VL_BITWORD_I(lsb) && w<=VL_BITWORD_I(msb)) {
			// else we would just be setting it to the same exact value
			AstNode* oldvalp = newAstWordSelClone (destp, w);
			fixCloneLvalue(oldvalp);
			if (!ones) oldvalp = new AstAnd (lhsp->fileline(),
							 new AstConst (lhsp->fileline(), maskold.dataWord(w)),
							 oldvalp);
			addWordAssign(nodep, w,
				      destp,
				      new AstOr (lhsp->fileline(),
						 oldvalp,
						 newWordGrabShift(lhsp->fileline(), w,
								  rhsp, lsb)));
		    }
		}
		rhsp->deleteTree(); rhsp=NULL;
		destp->deleteTree(); destp=NULL;
	    } else {
		UINFO(8,"    ASSIGNSEL(const,narrow) "<<nodep<<endl);
		if (destp->isQuad() && !rhsp->isQuad()) rhsp = new AstCCast(nodep->fileline(), rhsp, nodep);
		AstNode* oldvalp = destp->cloneTree(true);
		fixCloneLvalue(oldvalp);
		if (!ones) oldvalp = new AstAnd (lhsp->fileline(),
						 new AstConst (lhsp->fileline(), maskold),
						 oldvalp);
		AstNode* newp
		    = new AstOr (lhsp->fileline(),
				 oldvalp,
				 new AstShiftL (lhsp->fileline(),
						rhsp,
						new AstConst (lhsp->fileline(), lsb),
						destp->width()));
		newp = new AstAssign (nodep->fileline(), destp, newp);
		insertBefore(nodep,newp);
	    }
	    return true;
	}
	else {  // non-const RHS
	    if (destwide && lhsp->widthConst()==1) {
		UINFO(8,"    ASSIGNSEL(varlsb,wide,1bit) "<<nodep<<endl);
		AstNode* rhsp = nodep->rhsp()->unlinkFrBack();
		AstNode* destp = lhsp->fromp()->unlinkFrBack();
		AstNode* oldvalp = new AstWordSel (lhsp->fileline(),
						   destp->cloneTree(true),
						   newSelBitWord(lhsp->lsbp(), 0));
		fixCloneLvalue(oldvalp);
		if (!ones)
		    oldvalp = new AstAnd (lhsp->fileline(),
					  new AstNot (lhsp->fileline(),
						      new AstShiftL (lhsp->fileline(),
								     new AstConst (nodep->fileline(),1),
								     // newSelBitBit may exceed the MSB of this variable.
								     // That's ok as we'd just AND with a larger value,
								     // but oldval would clip the upper bits to sanity
								     newSelBitBit(lhsp->lsbp()),
								     VL_WORDSIZE)),
					  oldvalp);

		// Restrict the shift amount to 0-31, see bug804.
		AstNode* shiftp = new AstAnd(nodep->fileline(), lhsp->lsbp()->cloneTree(true),
					     new AstConst(nodep->fileline(), VL_WORDSIZE-1));
		AstNode* newp = new AstOr (lhsp->fileline(),
					   oldvalp,
					   new AstShiftL (lhsp->fileline(),
							  rhsp,
							  shiftp,
							  VL_WORDSIZE));
		newp = new AstAssign (nodep->fileline(),
				      new AstWordSel (nodep->fileline(),
						      destp,
						      newSelBitWord(lhsp->lsbp(), 0)),
				      newp);
		insertBefore(nodep,newp);
		return true;
	    }
	    else if (destwide) {
		UINFO(8,"    ASSIGNSEL(varlsb,wide) -- NoOp -- "<<nodep<<endl);
		//   For wide destp, we can either form a equation for every destination word,
		// with the appropriate long equation of if it's being written or not.
		//   Or, we can use a LHS variable arraysel with non-constant index to set the vector.
		// Doing the variable arraysel is better for globals and large arrays,
		// doing every word is better for temporaries and if we're setting most words
		// since it may result in better substitution optimizations later.
		//   This results in so much code, we're better off leaving a function call.
		// Reconsider if we get subexpression elimination.
		return false;
	    } else {
		UINFO(8,"    ASSIGNSEL(varlsb,narrow) "<<nodep<<endl);
		//nodep->dumpTree(cout,"-  old: ");
		AstNode* rhsp = nodep->rhsp()->unlinkFrBack();
		AstNode* destp = lhsp->fromp()->unlinkFrBack();
		AstNode* oldvalp = destp->cloneTree(true);
		fixCloneLvalue(oldvalp);

		V3Number maskwidth (nodep->fileline(), destp->widthMin());
		for (int bit=0; bit<(int)lhsp->widthConst(); bit++) maskwidth.setBit(bit,1);

		if (destp->isQuad() && !rhsp->isQuad()) rhsp = new AstCCast(nodep->fileline(), rhsp, nodep);
		if (!ones)
		    oldvalp = new AstAnd (lhsp->fileline(),
					  new AstNot (lhsp->fileline(),
						      new AstShiftL (lhsp->fileline(),
								     new AstConst (nodep->fileline(),
										   maskwidth),
								     lhsp->lsbp()->cloneTree(true),
								     destp->width())),
					  oldvalp);
		AstNode* newp
		    = new AstOr (lhsp->fileline(),
				 oldvalp,
				 new AstShiftL (lhsp->fileline(),
						rhsp,
						lhsp->lsbp()->cloneTree(true),
						destp->width()));
		newp = new AstAssign (nodep->fileline(), destp, newp);
		//newp->dumpTree(cout,"-  new: ");
		insertBefore(nodep,newp);
		return true;
	    }
	}
    }

    virtual void visit(AstConcat* nodep, AstNUser*) {
	if (nodep->user1SetOnce()) return;  // Process once
	nodep->iterateChildren(*this);
	if (nodep->isWide()) {
	    // See under ASSIGN(WIDE)
	} else {
	    UINFO(8,"    CONCAT "<<nodep<<endl);
	    AstNode* lhsp = nodep->lhsp()->unlinkFrBack();
	    AstNode* rhsp = nodep->rhsp()->unlinkFrBack();
	    int rhsshift = rhsp->widthMin();
	    if (nodep->isQuad() && !lhsp->isQuad()) lhsp = new AstCCast(nodep->fileline(), lhsp, nodep);
	    if (nodep->isQuad() && !rhsp->isQuad()) rhsp = new AstCCast(nodep->fileline(), rhsp, nodep);
	    AstNode* newp = new AstOr (nodep->fileline(),
				       new AstShiftL (nodep->fileline(),
						      lhsp,
						      new AstConst (nodep->fileline(), rhsshift),
						      nodep->width()),
				       rhsp);
	    newp->dtypeFrom(nodep); // Unsigned
	    replaceWithDelete(nodep,newp); nodep=NULL;
	}
    }
    bool expandWide (AstNodeAssign* nodep, AstConcat* rhsp) {
	UINFO(8,"    Wordize ASSIGN(CONCAT) "<<nodep<<endl);
	// Lhs or Rhs may be word, long, or quad.
	// newAstWordSelClone nicely abstracts the difference.
	int rhsshift = rhsp->rhsp()->widthMin();
	// Sometimes doing the words backwards is preferrable.
	// When we have x={x,foo} backwards is better, when x={foo,x} forward is better
	// However V3Subst tends to rip this up, so not worth optimizing now.
	for (int w=0; w<rhsp->widthWords(); w++) {
	    addWordAssign(nodep, w,
			  new AstOr (rhsp->fileline(),
				     newWordGrabShift(rhsp->fileline(), w,
						      rhsp->lhsp(), rhsshift),
				     newAstWordSelClone (rhsp->rhsp(), w)));
	}
	return true;
    }

    virtual void visit(AstReplicate* nodep, AstNUser*) {
	if (nodep->user1SetOnce()) return;  // Process once
	nodep->iterateChildren(*this);
	if (nodep->isWide()) {
	    // See under ASSIGN(WIDE)
	} else {
	    AstNode* lhsp = nodep->lhsp()->unlinkFrBack();
	    AstNode* newp;
	    int lhswidth = lhsp->widthMin();
	    if (lhswidth==1) {
		UINFO(8,"    REPLICATE(w1) "<<nodep<<endl);
		newp = new AstNegate (nodep->fileline(), lhsp);
	    } else {
		UINFO(8,"    REPLICATE "<<nodep<<endl);
		AstConst* constp = nodep->rhsp()->castConst();
		if (!constp) nodep->v3fatalSrc("Replication value isn't a constant.  Checked earlier!");
		uint32_t times = constp->toUInt();
		if (nodep->isQuad() && !lhsp->isQuad()) lhsp = new AstCCast(nodep->fileline(), lhsp, nodep);
		newp = lhsp->cloneTree(true);
		for (unsigned repnum=1; repnum<times; repnum++) {
		    int rhsshift = repnum*lhswidth;
		    newp = new AstOr (nodep->fileline(),
				      new AstShiftL (nodep->fileline(),
						     lhsp->cloneTree(true),
						     new AstConst (nodep->fileline(), rhsshift),
						     nodep->width()),
				      newp);
		    newp->dtypeFrom(nodep); // Unsigned
		}
		lhsp->deleteTree();	// Never used
	    }
	    newp->dtypeFrom(nodep); // Unsigned
	    replaceWithDelete(nodep,newp); nodep=NULL;
	}
    }
    bool expandWide (AstNodeAssign* nodep, AstReplicate* rhsp) {
	UINFO(8,"    Wordize ASSIGN(REPLICATE) "<<nodep<<endl);
	AstNode* lhsp = rhsp->lhsp();
	int lhswidth = lhsp->widthMin();
	AstConst* constp = rhsp->rhsp()->castConst();
	if (!constp) rhsp->v3fatalSrc("Replication value isn't a constant.  Checked earlier!");
	uint32_t times = constp->toUInt();
	for (int w=0; w<rhsp->widthWords(); w++) {
	    AstNode* newp;
	    if (lhswidth==1) {
		newp = new AstNegate (nodep->fileline(), lhsp->cloneTree(true));
		newp->dtypeSetLogicSized(VL_WORDSIZE,VL_WORDSIZE,AstNumeric::UNSIGNED);  // Replicate always unsigned
	    } else {
		newp = newAstWordSelClone (lhsp, w);
		for (unsigned repnum=1; repnum<times; repnum++) {
		    newp = new AstOr (nodep->fileline(),
				      newWordGrabShift(rhsp->fileline(), w, lhsp,
						       lhswidth*repnum),
				      newp);
		}
	    }
	    addWordAssign(nodep, w, newp);
	}
	return true;
    }

    virtual void visit(AstChangeXor* nodep, AstNUser*) {
	if (nodep->user1SetOnce()) return;  // Process once
	nodep->iterateChildren(*this);
	UINFO(8,"    Wordize ChangeXor "<<nodep<<endl);
	// -> (0=={or{for each_word{WORDSEL(lhs,#)^WORDSEL(rhs,#)}}}
	AstNode* newp = NULL;
	for (int w=0; w<nodep->lhsp()->widthWords(); w++) {
	    AstNode* eqp = new AstXor (nodep->fileline(),
				       newAstWordSelClone (nodep->lhsp(), w),
				       newAstWordSelClone (nodep->rhsp(), w));
	    newp = (newp==NULL) ? eqp : (new AstOr (nodep->fileline(), newp, eqp));
	}
	replaceWithDelete(nodep,newp); nodep=NULL;
    }

    void visitEqNeq(AstNodeBiop* nodep) {
	if (nodep->user1SetOnce()) return;  // Process once
	nodep->iterateChildren(*this);
	if (nodep->lhsp()->isWide()) {
	    UINFO(8,"    Wordize EQ/NEQ "<<nodep<<endl);
	    // -> (0=={or{for each_word{WORDSEL(lhs,#)^WORDSEL(rhs,#)}}}
	    AstNode* newp = NULL;
	    for (int w=0; w<nodep->lhsp()->widthWords(); w++) {
		AstNode* eqp = new AstXor (nodep->fileline(),
					   newAstWordSelClone (nodep->lhsp(), w),
					   newAstWordSelClone (nodep->rhsp(), w));
		newp = (newp==NULL) ? eqp : (new AstOr (nodep->fileline(), newp, eqp));
	    }
	    if (nodep->castNeq()) {
		newp = new AstNeq (nodep->fileline(),
				   new AstConst (nodep->fileline(), 0), newp);
	    } else {
		newp = new AstEq (nodep->fileline(),
				  new AstConst (nodep->fileline(), 0), newp);
	    }
	    replaceWithDelete(nodep,newp); nodep=NULL;
	}
    }
    virtual void visit(AstEq* nodep, AstNUser*) { visitEqNeq (nodep); }
    virtual void visit(AstNeq* nodep, AstNUser*) { visitEqNeq (nodep); }

    virtual void visit(AstRedOr* nodep, AstNUser*) {
	if (nodep->user1SetOnce()) return;  // Process once
	nodep->iterateChildren(*this);
	if (nodep->lhsp()->isWide()) {
	    UINFO(8,"    Wordize REDOR "<<nodep<<endl);
	    // -> (0!={or{for each_word{WORDSEL(lhs,#)}}}
	    AstNode* newp = NULL;
	    for (int w=0; w<nodep->lhsp()->widthWords(); w++) {
		AstNode* eqp = newAstWordSelClone (nodep->lhsp(), w);
		newp = (newp==NULL) ? eqp : (new AstOr (nodep->fileline(), newp, eqp));
	    }
	    newp = new AstNeq (nodep->fileline(),
			       new AstConst (nodep->fileline(), 0), newp);
	    replaceWithDelete(nodep,newp); nodep=NULL;
	} else {
	    UINFO(8,"    REDOR->EQ "<<nodep<<endl);
	    AstNode* lhsp = nodep->lhsp()->unlinkFrBack();
	    V3Number zero (nodep->fileline(), longOrQuadWidth(nodep));
	    AstNode* newp = new AstNeq (nodep->fileline(),
					new AstConst (nodep->fileline(), zero),
					lhsp);
	    replaceWithDelete(nodep,newp); nodep=NULL;
	}
    }
    virtual void visit(AstRedAnd* nodep, AstNUser*) {
	if (nodep->user1SetOnce()) return;  // Process once
	nodep->iterateChildren(*this);
	if (nodep->lhsp()->isWide()) {
	    UINFO(8,"    Wordize REDAND "<<nodep<<endl);
	    // -> (0!={and{for each_word{WORDSEL(lhs,#)}}}
	    AstNode* newp = NULL;
	    for (int w=0; w<nodep->lhsp()->widthWords(); w++) {
		AstNode* eqp = newAstWordSelClone (nodep->lhsp(), w);
		if (w==nodep->lhsp()->widthWords()-1) {
		    // Rather than doing a (slowish) ==##, we OR in the bits that aren't part of the mask
		    eqp = new AstOr (nodep->fileline(),
				     new AstConst (nodep->fileline(), notWideMask(nodep->lhsp())),
				     eqp);
		}
		newp = (newp==NULL) ? eqp : (new AstAnd (nodep->fileline(), newp, eqp));
	    }
	    newp = new AstEq (nodep->fileline(),
			      new AstConst (nodep->fileline(), ~0), newp);
	    replaceWithDelete(nodep, newp); nodep=NULL;
	} else {
	    UINFO(8,"    REDAND->EQ "<<nodep<<endl);
	    AstNode* lhsp = nodep->lhsp()->unlinkFrBack();
	    AstNode* newp = new AstEq (nodep->fileline(),
				       new AstConst (nodep->fileline(), wordMask(lhsp)),
				       lhsp);
	    replaceWithDelete(nodep,newp); nodep=NULL;
	}
    }
    virtual void visit(AstRedXor* nodep, AstNUser*) {
	if (nodep->user1SetOnce()) return;  // Process once
	nodep->iterateChildren(*this);
	if (nodep->lhsp()->isWide()) {
	    UINFO(8,"    Wordize REDXOR "<<nodep<<endl);
	    // -> (0!={redxor{for each_word{XOR(WORDSEL(lhs,#))}}}
	    AstNode* newp = NULL;
	    for (int w=0; w<nodep->lhsp()->widthWords(); w++) {
		AstNode* eqp = newAstWordSelClone (nodep->lhsp(), w);
		newp = (newp==NULL) ? eqp : (new AstXor (nodep->fileline(), newp, eqp));
	    }
	    newp = new AstRedXor (nodep->fileline(), newp);
	    UINFO(8,"    Wordize REDXORnew "<<newp<<endl);
	    replaceWithDelete(nodep, newp); nodep=NULL;
	}
	// We don't reduce non-wide XORs, as its more efficient to use a temp register,
	// which the inlined function does nicely.
    }

    virtual void visit(AstNodeStmt* nodep, AstNUser*) {
	if (nodep->user1SetOnce()) return;  // Process once
	m_stmtp = nodep;
	nodep->iterateChildren(*this);
	m_stmtp = NULL;
    }
    virtual void visit(AstNodeAssign* nodep, AstNUser*) {
	if (nodep->user1SetOnce()) return;  // Process once
	m_stmtp = nodep;
	nodep->iterateChildren(*this);
	bool did = false;
	if (nodep->isWide() && ((nodep->lhsp()->castVarRef()
				|| nodep->lhsp()->castArraySel()))
	    && !AstVar::scVarRecurse(nodep->lhsp())	// Need special function for SC
	    && !AstVar::scVarRecurse(nodep->rhsp())) {
	    if (AstConst* rhsp = nodep->rhsp()->castConst()) {
		did = expandWide(nodep,rhsp);
	    } else if (AstVarRef* rhsp = nodep->rhsp()->castVarRef()) {
		did = expandWide(nodep,rhsp);
	    } else if (AstSel* rhsp = nodep->rhsp()->castSel()) {
		did = expandWide(nodep,rhsp);
	    } else if (AstArraySel* rhsp = nodep->rhsp()->castArraySel()) {
		did = expandWide(nodep,rhsp);
	    } else if (AstConcat* rhsp = nodep->rhsp()->castConcat()) {
		did = expandWide(nodep,rhsp);
	    } else if (AstReplicate* rhsp = nodep->rhsp()->castReplicate()) {
		did = expandWide(nodep,rhsp);
	    } else if (AstAnd* rhsp = nodep->rhsp()->castAnd()) {
		did = expandWide(nodep,rhsp);
	    } else if (AstOr* rhsp = nodep->rhsp()->castOr()) {
		did = expandWide(nodep,rhsp);
	    } else if (AstNot* rhsp = nodep->rhsp()->castNot()) {
		did = expandWide(nodep,rhsp);
	    } else if (AstXor* rhsp = nodep->rhsp()->castXor()) {
		did = expandWide(nodep,rhsp);
	    } else if (AstXnor* rhsp = nodep->rhsp()->castXnor()) {
		did = expandWide(nodep,rhsp);
	    } else if (AstNodeCond* rhsp = nodep->rhsp()->castNodeCond()) {
		did = expandWide(nodep,rhsp);
	    }
	} else if (AstSel* lhsp = nodep->lhsp()->castSel()) {
	    did = expandLhs(nodep,lhsp);
	}
	// Cleanup common code
	if (did) {
	    nodep->unlinkFrBack()->deleteTree(); nodep=NULL;
	}
	m_stmtp = NULL;
    }

    //--------------------
    // Default: Just iterate
    virtual void visit(AstVar*, AstNUser*) {}	// Don't hit varrefs under vars
    virtual void visit(AstNode* nodep, AstNUser*) {
	nodep->iterateChildren(*this);
    }

public:
    // CONSTUCTORS
    ExpandVisitor(AstNetlist* nodep) {
	m_stmtp=NULL;
	nodep->accept(*this);
    }
    virtual ~ExpandVisitor() {}
};

//----------------------------------------------------------------------
// Top loop

//######################################################################
// Expand class functions

void V3Expand::expandAll(AstNetlist* nodep) {
    UINFO(2,__FUNCTION__<<": "<<endl);
    ExpandVisitor visitor (nodep);
    V3Global::dumpCheckGlobalTree("expand.tree", 0, v3Global.opt.dumpTreeLevel(__FILE__) >= 3);
}
