// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Expression width calculations
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

    // RETURN TYPE
    struct FromData {
	AstNode* m_errp;  // Node that was found, for error reporting if not known type
	AstNodeDType* m_dtypep;  // Data type for the 'from' slice
	VNumRange m_fromRange;  // Numeric range bounds for the 'from' slice
	FromData(AstNode* errp, AstNodeDType* dtypep, VNumRange fromRange)
	    { m_errp=errp; m_dtypep=dtypep; m_fromRange=fromRange; }
	~FromData() {}
    };
    FromData fromDataForArray(AstNode* nodep, AstNode* basefromp, bool rangedSelect) {
	// What is the data type and information for this SEL-ish's from()?
	UINFO(9,"  fromData start ddtypep = "<<basefromp<<endl);
	VNumRange fromRange;  // constructs to isRanged(false)
	while (basefromp) {
	    if (basefromp->castAttrOf()) {
		basefromp = basefromp->castAttrOf()->fromp();
		continue;
	    }
	    break;
	}
	if (!basefromp || !basefromp->dtypep()) nodep->v3fatalSrc("Select with no from dtype");
	AstNodeDType* ddtypep = basefromp->dtypep()->skipRefp();
	AstNode* errp = ddtypep;
	UINFO(9,"  fromData.ddtypep = "<<ddtypep<<endl);
	if (AstNodeArrayDType* adtypep = ddtypep->castNodeArrayDType()) {
	    fromRange = adtypep->declRange();
	}
	else if (AstNodeClassDType* adtypep = ddtypep->castNodeClassDType()) {
	    fromRange = adtypep->declRange();
	}
	else if (AstBasicDType* adtypep = ddtypep->castBasicDType()) {
	    if (adtypep->isRanged()) {
		if (adtypep->rangep()
		    && (!adtypep->rangep()->msbp()->castConst()
			|| !adtypep->rangep()->lsbp()->castConst()))
		    nodep->v3fatalSrc("Non-constant variable range; errored earlier");  // in constifyParam(bfdtypep)
		fromRange = adtypep->declRange();
	    } else {
		nodep->v3error("Illegal bit or array select; type does not have a bit range, or bad dimension: type is "
			       <<errp->prettyName());
	    }
	}
	else {
	    nodep->v3error("Illegal bit or array select; type already selected, or bad dimension: type is "
			   <<errp->prettyName());
	}
	return FromData(errp,ddtypep,fromRange);
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

    AstNode* newSubLsbOf(AstNode* underp, VNumRange fromRange) {
	// Account for a variable's LSB in bit selections
	// Will likely become SUB(underp, lsb_of_signal)
	// Don't report WIDTH warnings etc here, as may be inside a generate branch that will be deleted
	// SUB #'s Not needed when LSB==0 and MSB>=0 (ie [0:-13] must still get added!)
	if (!fromRange.ranged()) {
	    // vector without range, or 0 lsb is ok, for example a INTEGER x; y = x[21:0];
	    return underp;
	} else {
	    if (fromRange.littleEndian()) {
		// reg [1:3] was swapped to [3:1] (lsbEndianedp==3) and needs a SUB(3,under)
		AstNode* newp = newSubNeg(fromRange.hi(), underp);
		return newp;
	    } else {
		// reg [3:1] needs a SUB(under,1)
		AstNode* newp = newSubNeg(underp, fromRange.lo());
		return newp;
	    }
	}
    }

    AstNodeDType* sliceDType(AstPackArrayDType* nodep, int msb, int lsb) {
	// Return slice needed for msb/lsb, either as original dtype or a new slice dtype
	if (nodep->declRange().elements() == (msb-lsb+1) // Extracting whole of original array
	    && nodep->declRange().lo() == lsb) {
	    return nodep;
	} else {
	    // Need a slice data type, which is an array of the extracted type, but with (presumably) different size
	    VNumRange newRange (msb, lsb, nodep->declRange().littleEndian());
	    AstNodeDType* vardtypep = new AstPackArrayDType(nodep->fileline(),
							    nodep->subDTypep(), // Need to strip off array reference
							    new AstRange(nodep->fileline(), newRange));
	    v3Global.rootp()->typeTablep()->addTypesp(vardtypep);
	    return vardtypep;
	}
    }

    // VISITORS
    // If adding new visitors, insure V3Width's visit(TYPE) calls into here

    virtual void visit(AstSelBit* nodep, AstNUser*) {
	// Select of a non-width specified part of an array, i.e. "array[2]"
	// This select style has a lsb and msb (no user specified width)
	UINFO(6,"SELBIT "<<nodep<<endl);
	if (debug()>=9) nodep->backp()->dumpTree(cout,"--SELBT0: ");
	// lhsp/rhsp do not need to be constant
	AstNode* fromp = nodep->lhsp()->unlinkFrBack();
	AstNode* rhsp = nodep->rhsp()->unlinkFrBack();  // bit we're extracting
	if (debug()>=9) nodep->dumpTree(cout,"--SELBT2: ");
	FromData fromdata = fromDataForArray(nodep, fromp, false);
	AstNodeDType* ddtypep = fromdata.m_dtypep;
	VNumRange fromRange = fromdata.m_fromRange;
	UINFO(6,"  ddtypep "<<ddtypep<<endl);
	if (AstUnpackArrayDType* adtypep = ddtypep->castUnpackArrayDType()) {
	    // SELBIT(array, index) -> ARRAYSEL(array, index)
	    AstNode* subp = rhsp;
	    if (fromRange.lo()!=0 || fromRange.hi()<0) {
		subp = newSubNeg (subp, fromRange.lo());
	    }
	    AstArraySel* newp = new AstArraySel (nodep->fileline(),
						 fromp, subp);
	    newp->dtypeFrom(adtypep->subDTypep());  // Need to strip off array reference
	    if (debug()>=9) newp->dumpTree(cout,"--SELBTn: ");
	    nodep->replaceWith(newp); pushDeletep(nodep); nodep=NULL;
	}
	else if (AstPackArrayDType* adtypep = ddtypep->castPackArrayDType()) {
	    // SELBIT(array, index) -> SEL(array, index*width-of-subindex, width-of-subindex)
	    AstNode* subp = rhsp;
	    if (fromRange.lo()!=0 || fromRange.hi()<0) {
		subp = newSubNeg (subp, fromRange.lo());
	    }
	    if (!fromRange.elements() || (adtypep->width() % fromRange.elements())!=0)
		adtypep->v3fatalSrc("Array extraction with width miscomputed "
				    <<adtypep->width()<<"/"<<fromRange.elements());
	    int elwidth = adtypep->width() / fromRange.elements();
	    AstSel* newp = new AstSel (nodep->fileline(),
				       fromp,
				       new AstMul(nodep->fileline(),
						  new AstConst(nodep->fileline(),AstConst::Unsized32(),elwidth),
						  subp),
				       new AstConst (nodep->fileline(),AstConst::Unsized32(),elwidth));
	    newp->declRange(fromRange);
	    newp->declElWidth(elwidth);
	    newp->dtypeFrom(adtypep->subDTypep());  // Need to strip off array reference
	    if (debug()>=9) newp->dumpTree(cout,"--SELBTn: ");
	    nodep->replaceWith(newp); pushDeletep(nodep); nodep=NULL;
	}
	else if (ddtypep->castBasicDType()) {
	    // SELBIT(range, index) -> SEL(array, index, 1)
	    AstSel* newp = new AstSel (nodep->fileline(),
				       fromp,
				       newSubLsbOf(rhsp, fromRange),
				       // Unsized so width from user
				       new AstConst (nodep->fileline(),AstConst::Unsized32(),1));
	    newp->declRange(fromRange);
	    UINFO(6,"   new "<<newp<<endl);
	    if (debug()>=9) newp->dumpTree(cout,"--SELBTn: ");
	    nodep->replaceWith(newp); pushDeletep(nodep); nodep=NULL;
	}
	else if (ddtypep->castNodeClassDType()) {  // It's packed, so a bit from the packed struct
	    // SELBIT(range, index) -> SEL(array, index, 1)
	    AstSel* newp = new AstSel (nodep->fileline(),
				       fromp,
				       newSubLsbOf(rhsp, fromRange),
				       // Unsized so width from user
				       new AstConst (nodep->fileline(),AstConst::Unsized32(),1));
	    newp->declRange(fromRange);
	    UINFO(6,"   new "<<newp<<endl);
	    if (debug()>=9) newp->dumpTree(cout,"--SELBTn: ");
	    nodep->replaceWith(newp); pushDeletep(nodep); nodep=NULL;
	}
	else {  // NULL=bad extract, or unknown node type
	    nodep->v3error("Illegal bit or array select; type already selected, or bad dimension: type is"
			   <<fromdata.m_errp->prettyName());
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
	//if (debug()>=9) nodep->dumpTree(cout,"--SELEX0: ");
	// Below 2 lines may change nodep->widthp()
	V3Const::constifyParamsEdit(nodep->lsbp()); // May relink pointed to node
	V3Const::constifyParamsEdit(nodep->msbp()); // May relink pointed to node
	//if (debug()>=9) nodep->dumpTree(cout,"--SELEX3: ");
	checkConstantOrReplace(nodep->lsbp(), "First value of [a:b] isn't a constant, maybe you want +: or -:");
	checkConstantOrReplace(nodep->msbp(), "Second value of [a:b] isn't a constant, maybe you want +: or -:");
	AstNode* fromp = nodep->lhsp()->unlinkFrBack();
	AstNode* msbp = nodep->rhsp()->unlinkFrBack();
	AstNode* lsbp = nodep->thsp()->unlinkFrBack();
	vlsint32_t msb = msbp->castConst()->toSInt();
	vlsint32_t lsb = lsbp->castConst()->toSInt();
	FromData fromdata = fromDataForArray(nodep, fromp, false);
	AstNodeDType* ddtypep = fromdata.m_dtypep;
	VNumRange fromRange = fromdata.m_fromRange;
	if (ddtypep->castUnpackArrayDType()) {
	    // Slice extraction
	    if (fromRange.elements() == (msb-lsb+1)
		&& fromRange.lo() == lsb) { // Extracting whole of original array
		nodep->replaceWith(fromp); pushDeletep(nodep); nodep=NULL;
	    } else {
		// TODO when unpacked arrays fully supported probably need new data type here
		AstArraySel* newp = new AstArraySel (nodep->fileline(), fromp, lsbp);
		newp->start(lsb);
		newp->length((msb - lsb) + 1);
		nodep->replaceWith(newp); pushDeletep(nodep); nodep=NULL;
	    }
	}
	else if (AstPackArrayDType* adtypep = ddtypep->castPackArrayDType()) {
	    // SELEXTRACT(array, msb, lsb) -> SEL(array, lsb*width-of-subindex, width-of-subindex*(msb-lsb))
	    if (!fromRange.elements() || (adtypep->width() % fromRange.elements())!=0)
		adtypep->v3fatalSrc("Array extraction with width miscomputed "
				    <<adtypep->width()<<"/"<<fromRange.elements());
	    int elwidth = adtypep->width() / fromRange.elements();
	    AstSel* newp = new AstSel (nodep->fileline(),
				       fromp,
				       new AstConst(nodep->fileline(),AstConst::Unsized32(),lsb*elwidth),
				       new AstConst(nodep->fileline(),AstConst::Unsized32(),(msb-lsb+1)*elwidth));
	    newp->declRange(fromRange);
	    newp->declElWidth(elwidth);
	    newp->dtypeFrom(sliceDType(adtypep, msb, lsb));
	    //if (debug()>=9) newp->dumpTree(cout,"--EXTBTn: ");
	    if (newp->widthMin()!=(int)newp->widthConst()) nodep->v3fatalSrc("Width mismatch");
	    nodep->replaceWith(newp); pushDeletep(nodep); nodep=NULL;
	}
	else if (ddtypep->castBasicDType()) {
	    if (fromRange.littleEndian()) {
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
				       newSubLsbOf(lsbp, fromRange),
				       widthp);
	    newp->declRange(fromRange);
	    UINFO(6,"   new "<<newp<<endl);
	    //if (debug()>=9) newp->dumpTree(cout,"--SELEXnew: ");
	    nodep->replaceWith(newp); pushDeletep(nodep); nodep=NULL;
	}
	else if (ddtypep->castNodeClassDType()) {
	    // Classes aren't little endian
	    if (lsb > msb) {
		nodep->v3error("["<<msb<<":"<<lsb<<"] Range extract has backward bit ordering, perhaps you wanted ["<<lsb<<":"<<msb<<"]");
		int x = msb; msb = lsb; lsb = x;
	    }
	    AstNode* widthp = new AstConst (msbp->fileline(), AstConst::Unsized32(), // Unsized so width from user
					    msb +1-lsb);
	    AstSel* newp = new AstSel (nodep->fileline(),
				       fromp,
				       newSubLsbOf(lsbp, fromRange),
				       widthp);
	    newp->declRange(fromRange);
	    UINFO(6,"   new "<<newp<<endl);
	    //if (debug()>=9) newp->dumpTree(cout,"--SELEXnew: ");
	    nodep->replaceWith(newp); pushDeletep(nodep); nodep=NULL;
	}
	else {  // NULL=bad extract, or unknown node type
	    nodep->v3error("Illegal range select; type already selected, or bad dimension: type is "
			   <<fromdata.m_errp->prettyName());
	    UINFO(1,"    Related ddtype: "<<ddtypep<<endl);
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
	if (debug()>=9) nodep->dumpTree(cout,"--SELPM0: ");
	V3Const::constifyParamsEdit(nodep->thsp()); // May relink pointed to node
	checkConstantOrReplace(nodep->thsp(), "Width of :+ or :- bit extract isn't a constant");
	if (debug()>=9) nodep->dumpTree(cout,"--SELPM3: ");
	// Now replace it with an AstSel
	AstNode* fromp = nodep->lhsp()->unlinkFrBack();
	AstNode* rhsp  = nodep->rhsp()->unlinkFrBack();
	AstNode* widthp = nodep->thsp()->unlinkFrBack();
	int width = widthp->castConst()->toSInt();
	if (width > (1<<28)) nodep->v3error("Width of :+ or :- is huge; vector of over 1billion bits: "<<widthp->prettyName());
	if (width<0) nodep->v3error("Width of :+ or :- is < 0: "<<widthp->prettyName());
	FromData fromdata = fromDataForArray(nodep, fromp, width!=1);
	AstNodeDType* ddtypep = fromdata.m_dtypep;
	VNumRange fromRange = fromdata.m_fromRange;
	if (ddtypep->castBasicDType()
	    || ddtypep->castPackArrayDType()
	    || (ddtypep->castNodeClassDType()
		&& ddtypep->castNodeClassDType()->packedUnsup())) {
	    int elwidth = 1;
	    AstNode* newwidthp = widthp;
	    if (AstPackArrayDType* adtypep = ddtypep->castPackArrayDType()) {
		elwidth = adtypep->width() / fromRange.elements();
		newwidthp = new AstConst (nodep->fileline(),AstConst::Unsized32(), width * elwidth);
	    }
	    AstNode* newlsbp = NULL;
	    if (nodep->castSelPlus()) {
		if (fromRange.littleEndian()) {
		    // SELPLUS(from,lsb,width) -> SEL(from, (vector_msb-width+1)-sel, width)
		    newlsbp = newSubNeg((fromRange.hi()-width+1), rhsp);
		} else {
		    // SELPLUS(from,lsb,width) -> SEL(from, lsb-vector_lsb, width)
		    newlsbp = newSubNeg(rhsp, fromRange.lo());
		}
	    } else if (nodep->castSelMinus()) {
		if (fromRange.littleEndian()) {
		    // SELMINUS(from,msb,width) -> SEL(from, msb-[bit])
		    newlsbp = newSubNeg(fromRange.hi(), rhsp);
		} else {
		    // SELMINUS(from,msb,width) -> SEL(from, msb-(width-1)-lsb#)
		    newlsbp = newSubNeg(rhsp, fromRange.lo()+(width-1));
		}
	    } else {
		nodep->v3fatalSrc("Bad Case");
	    }
	    if (elwidth != 1) newlsbp = new AstMul (nodep->fileline(), newlsbp,
						    new AstConst (nodep->fileline(), elwidth));
	    AstSel* newp = new AstSel (nodep->fileline(),
				       fromp, newlsbp, newwidthp);
	    newp->declRange(fromRange);
	    newp->declElWidth(elwidth);
	    UINFO(6,"   new "<<newp<<endl);
	    if (debug()>=9) newp->dumpTree(cout,"--SELNEW: ");
	    nodep->replaceWith(newp); pushDeletep(nodep); nodep=NULL;
	}
	else {  // NULL=bad extract, or unknown node type
	    nodep->v3error("Illegal +: or -: select; type already selected, or bad dimension: type is "
			   <<fromdata.m_errp->prettyTypeName());
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
