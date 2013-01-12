// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Expression width calculations
//
// Code available from: http://www.veripool.org/verilator
//
//*************************************************************************
//
// Copyright 2003-2013 by Wilson Snyder.  This program is free software; you can
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
// V3WidthSel's Transformations:
//	Top down traversal:
//	    Replace SELPLUS/SELMINUS with SEL
//	    Replace SELEXTRACT with SEL
//	    Replace SELBIT with SEL or ARRAYSEL
//
// This code was once in V3LinkResolve, but little endian bit vectors won't
// work that early.  It was considered for V3Width and V3Param, but is
// fairly ugly both places as the nodes change in too strongly
// interconnected ways.
//
//*************************************************************************

#include "config_build.h"
#include "verilatedos.h"
#include <cstdio>
#include <cstdarg>
#include <unistd.h>

#include "V3Global.h"
#include "V3Width.h"
#include "V3Const.h"

//######################################################################
// Width state, as a visitor of each AstNode

class WidthSelVisitor : public AstNVisitor {
private:
    // IMPORTANT
    //**** This is not a normal visitor, in that all iteration is instead
    //  done by the caller (V3Width).  This avoids duplicating much of the
    //  complicated GenCase/GenFor/Cell/Function call logic that all depends
    //  on if widthing top-down or just for parameters.
#define iterateChildren DO_NOT_iterateChildern_IN_V3WidthSel

    // METHODS
    static int debug() {
	static int level = -1;
	if (VL_UNLIKELY(level < 0)) level = v3Global.opt.debugSrcLevel(__FILE__);
	return level;
    }

    void checkConstantOrReplace(AstNode* nodep, const string& message) {
	// See also V3Width::checkConstantOrReplace
	// Note can't call V3Const::constifyParam(nodep) here, as constify may change nodep on us!
	if (!nodep->castConst()) {
	    nodep->v3error(message);
	    nodep->replaceWith(new AstConst(nodep->fileline(), AstConst::Unsized32(), 1));
	    pushDeletep(nodep); nodep=NULL;
	}
    }

    AstNodeDType* dtypeForExtractp(AstNode* nodep, AstNode* basefromp, int dimension, bool rangedSelect) {
	// Perform error checks on the node
	AstNode* errp;
	AstNodeDType* bfdtypep = baseDTypeFrom(basefromp, errp/*ref*/);
	//UINFO(9,"SCD\n"); if (debug()>=9) bfdtypep->dumpTree(cout,"-dtfexvar: ");
	// This may be called on dotted variables before we've completed widthing of the dotted var.
	AstNodeDType* ddtypep = bfdtypep;
	ddtypep = ddtypep->dtypeDimensionp(dimension);
	if (debug()>=9 &&ddtypep) ddtypep->dumpTree(cout,"-ddtypep: ");
	if (AstArrayDType* adtypep = ddtypep->castArrayDType()) {
	    return adtypep;
	}
	else if (AstNodeClassDType* adtypep = ddtypep->castNodeClassDType()) {
	    return adtypep;
	}
	else if (AstBasicDType* adtypep = ddtypep->castBasicDType()) {
	    if (!adtypep->isRanged()) {
		nodep->v3error("Illegal bit select; variable does not have a bit range, or bad dimension: "<<errp->prettyName());
		return NULL;
	    }
	    return adtypep;
	}
	else {
	    nodep->v3error("Illegal bit or array select; variable already selected, or bad dimension: "<<errp->prettyName());
	}
	return NULL;
    }

    AstNode* newSubNeg(AstNode* lhsp, vlsint32_t rhs) {
	// Return lhs-rhs, but if rhs is negative use an add, so we won't
	// have to deal with signed math and related 32bit sign extension problems
	if (rhs == 0) {
	    return lhsp;
	} else if (lhsp->castConst()) {
	    // Optional vs just making add/sub below, but saves constification some work
	    V3Number num (lhsp->fileline(), lhsp->width());
	    num.opSub(lhsp->castConst()->num(), V3Number(lhsp->fileline(), 32, rhs));
	    num.isSigned(lhsp->isSigned());
	    AstNode* newp = new AstConst(lhsp->fileline(), num);
	    return newp;
	} else if (rhs > 0) {
	    AstNode* newp = new AstSub(lhsp->fileline(), lhsp,
				       new AstConst(lhsp->fileline(), AstConst::Unsized32(), rhs));
	    // We must make sure sub gets sign of original value, not from the constant
	    newp->dtypeFrom(lhsp);
	    return newp;
	} else {  // rhs < 0;
	    AstNode* newp = new AstAdd(lhsp->fileline(), lhsp,
				       new AstConst(lhsp->fileline(), AstConst::Unsized32(), -rhs));
	    // We must make sure sub gets sign of original value, not from the constant
	    newp->dtypeFrom(lhsp);
	    return newp;
	}
    }
    AstNode* newSubNeg(vlsint32_t lhs, AstNode* rhsp) {
	// Return lhs-rhs
	// We must make sure sub gets sign of original value
	AstNode* newp = new AstSub(rhsp->fileline(),
				   new AstConst(rhsp->fileline(), AstConst::Unsized32(), lhs),
				   rhsp);
	newp->dtypeFrom(rhsp);  // Important as AstSub default is lhs's sign
	return newp;
    }

    AstNodeDType* baseDTypeFrom(AstNode* basefromp, AstNode*& errpr) {
	errpr = basefromp;
	if (AstNodeVarRef* varrefp = basefromp->castNodeVarRef()) {
	    AstVar* varp = varrefp->varp(); if (!varp) { varrefp->v3fatalSrc("Signal not linked"); return NULL; }
	    errpr = varp;
	    AstNodeDType* bfdtypep = varp->subDTypep();
	    if (!bfdtypep) basefromp->v3fatalSrc("No datatype found for variable in select");
	    return bfdtypep;
	} else if (AstMemberSel* selp = basefromp->castMemberSel()) {
	    errpr = selp;
	    AstNodeDType* bfdtypep = selp->dtypep();
	    if (!bfdtypep) basefromp->v3fatalSrc("No datatype found for variable in select");
	    return bfdtypep;
	} else {
	    basefromp->v3fatalSrc("Bit/array selection of non-variable");
	}
	return NULL;
    }

    AstNode* newSubLsbOf(AstNode* underp, AstNode* basefromp) {
	// Account for a variable's LSB in bit selections
	// Will likely become SUB(underp, lsb_of_signal)
	// Don't report WIDTH warnings etc here, as may be inside a generate branch that will be deleted
	AstNode* errp;
	AstNodeDType* bfdtypep = baseDTypeFrom(basefromp, errp/*ref*/);
	// SUB #'s Not needed when LSB==0 and MSB>=0 (ie [0:-13] must still get added!)
	if (!bfdtypep->basicp()->isRanged()) {
	    // vector without range, or 0 lsb is ok, for example a INTEGER x; y = x[21:0];
	    return underp;
	} else {
	    if (bfdtypep->basicp()->rangep()
		&& (!bfdtypep->basicp()->rangep()->msbp()->castConst()
		    || !bfdtypep->basicp()->rangep()->lsbp()->castConst()))
		bfdtypep->v3fatalSrc("Non-constant variable range; errored earlier");  // in constifyParam(bfdtypep)
	    if (bfdtypep->basicp()->littleEndian()) {
		// reg [1:3] was swapped to [3:1] (lsbEndianedp==3) and needs a SUB(3,under)
		AstNode* newp = newSubNeg(bfdtypep->basicp()->msb(), underp);
		return newp;
	    } else {
		// reg [3:1] needs a SUB(under,1)
		AstNode* newp = newSubNeg(underp, bfdtypep->basicp()->lsb());
		return newp;
	    }
	}
    }

    // VISITORS
    // If adding new visitors, insure V3Width's visit(TYPE) calls into here

    virtual void visit(AstSelBit* nodep, AstNUser*) {
	// Select of a non-width specified part of an array, i.e. "array[2]"
	// This select style has a lsb and msb (no user specified width)
	UINFO(6,"SELBIT "<<nodep<<endl);
	if (debug()>=9) nodep->backp()->dumpTree(cout,"-vsbin(-1): ");
	// lhsp/rhsp do not need to be constant
	AstNode* basefromp = AstArraySel::baseFromp(nodep->attrp());
	int dimension      = AstArraySel::dimension(nodep->fromp());  // Not attrp as need hierarchy
	AstNodeDType* ddtypep = dtypeForExtractp(nodep, basefromp, dimension, false);
	AstNode* fromp = nodep->lhsp()->unlinkFrBack();
	AstNode* rhsp = nodep->rhsp()->unlinkFrBack();  // bit we're extracting
	if (debug()>=9) ddtypep->dumpTree(cout,"-ddtypep: ");
	if (debug()>=9) nodep->dumpTree(cout,"-vsbmd: ");
	if (AstArrayDType* adtypep = ddtypep->castArrayDType()) {
	    // SELBIT(array, index) -> ARRAYSEL(array, index)
	    AstNode* subp = rhsp;
	    if (adtypep->lsb()!=0 || adtypep->msb()<0) {
		subp = newSubNeg (subp, adtypep->lsb());
	    }
	    AstArraySel* newp = new AstArraySel	(nodep->fileline(),
						 fromp, subp);
	    UINFO(6,"   newd"<<dimension<<" "<<newp<<endl);
	    nodep->replaceWith(newp); pushDeletep(nodep); nodep=NULL;
	}
	else if (AstBasicDType* adtypep = ddtypep->castBasicDType()) {
	    if (adtypep) {} // unused
	    // SELBIT(range, index) -> SEL(array, index, 1)
	    AstSel* newp = new AstSel (nodep->fileline(),
				       fromp,
				       newSubLsbOf(rhsp, basefromp),
				       // Unsized so width from user
				       new AstConst (nodep->fileline(),AstConst::Unsized32(),1));
	    UINFO(6,"   new "<<newp<<endl); if (debug()>=9) newp->dumpTree(cout,"-vsbnw: ");
	    nodep->replaceWith(newp); pushDeletep(nodep); nodep=NULL;
	}
	else if (AstNodeClassDType* adtypep = ddtypep->castNodeClassDType()) {
	    if (adtypep) {} // unused
	    // SELBIT(range, index) -> SEL(array, index, 1)
	    AstSel* newp = new AstSel (nodep->fileline(),
				       fromp,
				       newSubLsbOf(rhsp, basefromp),
				       // Unsized so width from user
				       new AstConst (nodep->fileline(),AstConst::Unsized32(),1));
	    UINFO(6,"   new "<<newp<<endl); if (debug()>=9) newp->dumpTree(cout,"-vsbnw: ");
	    nodep->replaceWith(newp); pushDeletep(nodep); nodep=NULL;
	}
	else {  // NULL=bad extract, or unknown node type
	    nodep->v3error("Illegal bit or array select; variable already selected, or bad dimension");
	    // How to recover?  We'll strip a dimension.
	    nodep->replaceWith(fromp); pushDeletep(nodep); nodep=NULL;
	}
	if (!rhsp->backp()) pushDeletep(rhsp); rhsp=NULL;
    }

    virtual void visit(AstSelExtract* nodep, AstNUser*) {
	// Select of a range specified part of an array, i.e. "array[2:3]"
	// SELEXTRACT(from,msb,lsb) -> SEL(from, lsb, 1+msb-lsb)
	// This select style has a (msb or lsb) and width
	UINFO(6,"SELEXTRACT "<<nodep<<endl);
	//if (debug()>=9) nodep->dumpTree(cout,"--SLEX0: ");
	// Below 2 lines may change nodep->widthp()
	V3Const::constifyParamsEdit(nodep->lsbp()); // May relink pointed to node
	V3Const::constifyParamsEdit(nodep->msbp()); // May relink pointed to node
	//if (debug()>=9) nodep->dumpTree(cout,"--SLEX3: ");
	checkConstantOrReplace(nodep->lsbp(), "First value of [a:b] isn't a constant, maybe you want +: or -:");
	checkConstantOrReplace(nodep->msbp(), "Second value of [a:b] isn't a constant, maybe you want +: or -:");
	AstNode* basefromp = AstArraySel::baseFromp(nodep->attrp());
	int dimension      = AstArraySel::dimension(nodep->fromp());  // Not attrp as need hierarchy
	AstNode* fromp = nodep->lhsp()->unlinkFrBack();
	AstNode* msbp = nodep->rhsp()->unlinkFrBack();
	AstNode* lsbp = nodep->thsp()->unlinkFrBack();
	AstNode* errp;
	AstNodeDType* bfdtypep = baseDTypeFrom(basefromp, errp/*ref*/);
	vlsint32_t msb = msbp->castConst()->toSInt();
	vlsint32_t lsb = lsbp->castConst()->toSInt();
	AstNodeDType* ddtypep = dtypeForExtractp(nodep, basefromp, dimension, msb!=lsb);
	if (AstArrayDType* adtypep = ddtypep->castArrayDType()) {
	    if (adtypep) {}
	    // Slice extraction
	    AstArraySel* newp = new AstArraySel (nodep->fileline(), fromp, lsbp);
	    newp->start(lsb);
	    newp->length((msb - lsb) + 1);
	    nodep->replaceWith(newp); pushDeletep(nodep); nodep=NULL;
	} else if (AstBasicDType* adtypep = ddtypep->castBasicDType()) {
	    if (adtypep) {} // Unused
	    if (bfdtypep->basicp()->littleEndian()) {
		// Below code assumes big bit endian; just works out if we swap
		int x = msb; msb = lsb; lsb = x;
	    }
	    if (lsb > msb) {
		nodep->v3error("["<<msb<<":"<<lsb<<"] Range extract has backward bit ordering, perhaps you wanted ["<<lsb<<":"<<msb<<"]");
		int x = msb; msb = lsb; lsb = x;
	    }
	    AstNode* widthp = new AstConst (msbp->fileline(), AstConst::Unsized32(), // Unsized so width from user
					    msb +1-lsb);
	    AstSel* newp = new AstSel (nodep->fileline(),
				       fromp,
				       newSubLsbOf(lsbp, basefromp),
				       widthp);
	    UINFO(6,"   new "<<newp<<endl);
	    //if (debug()>=9) newp->dumpTree(cout,"--SLEXnew: ");
	    nodep->replaceWith(newp); pushDeletep(nodep); nodep=NULL;
	} else if (AstNodeClassDType* adtypep = ddtypep->castNodeClassDType()) {
	    if (adtypep) {} // Unused
	    // Classes aren't little endian
	    if (lsb > msb) {
		nodep->v3error("["<<msb<<":"<<lsb<<"] Range extract has backward bit ordering, perhaps you wanted ["<<lsb<<":"<<msb<<"]");
		int x = msb; msb = lsb; lsb = x;
	    }
	    AstNode* widthp = new AstConst (msbp->fileline(), AstConst::Unsized32(), // Unsized so width from user
					    msb +1-lsb);
	    AstSel* newp = new AstSel (nodep->fileline(),
				       fromp,
				       newSubLsbOf(lsbp, basefromp),
				       widthp);
	    UINFO(6,"   new "<<newp<<endl);
	    //if (debug()>=9) newp->dumpTree(cout,"--SLEXnew: ");
	    nodep->replaceWith(newp); pushDeletep(nodep); nodep=NULL;
	}
	else {  // NULL=bad extract, or unknown node type
	    nodep->v3error("Illegal range select; variable already selected, or bad dimension");
	    // How to recover?  We'll strip a dimension.
	    nodep->replaceWith(fromp); pushDeletep(nodep); nodep=NULL;
	}
	// delete whataver we didn't use in reconstruction
	if (!fromp->backp()) pushDeletep(fromp); fromp=NULL;
	if (!msbp->backp()) pushDeletep(msbp); msbp=NULL;
	if (!lsbp->backp()) pushDeletep(lsbp); lsbp=NULL;
    }

    void replaceSelPlusMinus(AstNodePreSel* nodep) {
	// Select of a range specified with +: or -:, i.e. "array[2+:3], [2-:3]"
	// This select style has a lsb and width
	UINFO(6,"SELPLUS/MINUS "<<nodep<<endl);
	// Below 2 lines may change nodep->widthp()
	V3Const::constifyParamsEdit(nodep->thsp()); // May relink pointed to node
	checkConstantOrReplace(nodep->thsp(), "Width of :+ or :- bit extract isn't a constant");
	// Now replace it with an AstSel
	AstNode* basefromp = AstArraySel::baseFromp(nodep->attrp());
	int dimension      = AstArraySel::dimension(nodep->fromp());  // Not attrp as need hierarchy
	AstNode* fromp = nodep->lhsp()->unlinkFrBack();
	AstNode* rhsp  = nodep->rhsp()->unlinkFrBack();
	AstNode* widthp = nodep->thsp()->unlinkFrBack();
	int width = widthp->castConst()->toSInt();
	if (width > (1<<28)) nodep->v3error("Width of :+ or :- is huge; vector of over 1billion bits: "<<widthp->prettyName());
	if (width<0) nodep->v3error("Width of :+ or :- is < 0: "<<widthp->prettyName());
	AstNodeDType* ddtypep = dtypeForExtractp(nodep, basefromp, dimension, width!=1);
	if (AstBasicDType* adtypep = ddtypep->castBasicDType()) {
	    AstSel* newp = NULL;
	    if (nodep->castSelPlus()) {
		if (adtypep->littleEndian()) {
		    // SELPLUS(from,lsb,width) -> SEL(from, (vector_msb-width+1)-sel, width)
		    newp = new AstSel (nodep->fileline(),
				       fromp,
				       newSubNeg((adtypep->msb()-width+1), rhsp),
				       widthp);
		} else {
		    // SELPLUS(from,lsb,width) -> SEL(from, lsb-vector_lsb, width)
		    newp = new AstSel (nodep->fileline(),
				       fromp,
				       newSubLsbOf(rhsp, basefromp),
				       widthp);
		}
	    } else if (nodep->castSelMinus()) {
		if (adtypep->littleEndian()) {
		    // SELMINUS(from,msb,width) -> SEL(from, msb-[bit])
		    newp = new AstSel (nodep->fileline(),
				       fromp,
				       newSubNeg(adtypep->msb(), rhsp),
				       widthp);
		} else {
		    // SELMINUS(from,msb,width) -> SEL(from, msb-(width-1)-lsb#)
		    newp = new AstSel (nodep->fileline(),
				       fromp,
				       newSubNeg(rhsp, adtypep->lsb()+(width-1)),
				       widthp);
		}
	    } else {
		nodep->v3fatalSrc("Bad Case");
	    }
	    UINFO(6,"   new "<<newp<<endl);
	    nodep->replaceWith(newp); pushDeletep(nodep); nodep=NULL;
	}
	else {  // NULL=bad extract, or unknown node type
	    nodep->v3error("Illegal +: or -: select; variable already selected, or bad dimension");
	    // How to recover?  We'll strip a dimension.
	    nodep->replaceWith(fromp); pushDeletep(nodep); nodep=NULL;
	}
	// delete whataver we didn't use in reconstruction
	if (!fromp->backp()) pushDeletep(fromp); fromp=NULL;
	if (!rhsp->backp()) pushDeletep(rhsp); rhsp=NULL;
	if (!widthp->backp()) pushDeletep(widthp); widthp=NULL;
    }
    virtual void visit(AstSelPlus* nodep, AstNUser*) {
	replaceSelPlusMinus(nodep);
    }
    virtual void visit(AstSelMinus* nodep, AstNUser*) {
	replaceSelPlusMinus(nodep);
    }
    // If adding new visitors, insure V3Width's visit(TYPE) calls into here

    //--------------------
    // Default
    virtual void visit(AstNode* nodep, AstNUser*) {
	// See notes above; we never iterate
	nodep->v3fatalSrc("Shouldn't iterate in V3WidthSel");
    }

public:
    // CONSTUCTORS
    WidthSelVisitor() {}
    AstNode* mainAcceptEdit(AstNode* nodep) {
	return nodep->acceptSubtreeReturnEdits(*this);
    }
    virtual ~WidthSelVisitor() {}
};

//######################################################################
// Width class functions

AstNode* V3Width::widthSelNoIterEdit(AstNode* nodep) {
    UINFO(4,__FUNCTION__<<": "<<nodep<<endl);
    WidthSelVisitor visitor;
    nodep = visitor.mainAcceptEdit(nodep);
    return nodep;
}

#undef iterateChildren
