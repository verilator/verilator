//*************************************************************************
// DESCRIPTION: Verilator: Expression width calculations
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
// V3Width's Transformations:
//	Top down traversal:
//	    Determine width of sub-expressions
//		width() = # bits upper expression wants, 0 for anything-goes
//		widthUnsized() = # bits for unsized constant, or 0 if it's sized
//		widthMin() = Alternative acceptable width for linting, or width() if sized
//		Determine this subop's width, can be either:
//		    Fixed width X
//		    Unsized, min width X   ('d5 is unsized, min 3 bits.)
//		Pass up:
//		    width() = # bits this expression generates
//		    widthSized() = true if all constants sized, else false
//	    Compute size of this expression
//	    Lint warn about mismatches
//		If expr size != subop fixed, bad
//		If expr size  < subop unsized minimum, bad
//		If expr size != subop, edit netlist
//			For == and similar ops, if multibit underneath, add a REDOR
//			If subop larger, add a EXTRACT
//			If subop smaller, add a EXTEND
//	    Pass size to sub-expressions if required (+/-* etc)
//		FINAL = true.
//		Subexpressions lint and extend as needed
//
//*************************************************************************

#include "config_build.h"
#include "verilatedos.h"
#include <cstdio>
#include <cstdarg>
#include <unistd.h>

#include "V3Global.h"
#include "V3Width.h"
#include "V3Signed.h"
#include "V3Number.h"
#include "V3Const.h"

//######################################################################
// Width state, as a visitor of each AstNode

    enum Stage { PRELIM=1,FINAL=2,BOTH=3 };

    class WidthVP : public AstNUser {
	// Parameters to pass down hierarchy with visit functions.
	int	m_width;	// Expression width, for (2+2), it's 32 bits
	int	m_minWidth;	// Minimum width, for (2+2), it's 2 bits, for 32'2+32'2 it's 32 bits
	Stage	m_stage;	// If true, report errors
    public:
	WidthVP(int width, int minWidth, Stage stage) : m_width(width), m_minWidth(minWidth), m_stage(stage) {}
	int width() const { return m_width; }
	int widthMin() const { return m_minWidth?m_minWidth:m_width; }
	bool prelim() const { return m_stage&1; }
	bool final() const { return m_stage&2; }
    };


class WidthVisitor : public AstNVisitor {
private:
    // STATE
    int		m_taskDepth;	// Recursion check
    bool	m_paramsOnly;	// Computing parameter value; limit operation
    AstRange*	m_cellRangep;	// Range for arrayed instantiations, NULL for normal instantiations
    AstNodeCase* m_casep;	// Current case statement CaseItem is under

    // CLASSES
#define ANYSIZE 0

    // METHODS
    static int debug() {
	static int level = -1;
	if (VL_UNLIKELY(level < 0)) level = v3Global.opt.debugSrcLevel(__FILE__);
	return level;
    }

    // VISITORS
    //   Naming:  width_{output size rule}_{lhs rule}_{rhs rule}
    // Widths: 1 bit out, lhs 1 bit
    void width_O1_L1(AstNode* nodep, AstNUser* vup);
    virtual void visit(AstLogNot* nodep, AstNUser* vup) {	width_O1_L1(nodep,vup); }
    virtual void visit(AstPslBool* nodep, AstNUser* vup) {	width_O1_L1(nodep,vup); }

    // Widths: 1 bit out, lhs 1 bit, rhs 1 bit
    void width_O1_L1_R1(AstNode* nodep, AstNUser* vup);
    virtual void visit(AstLogAnd* nodep, AstNUser* vup) {	width_O1_L1_R1(nodep,vup); }
    virtual void visit(AstLogOr* nodep, AstNUser* vup) {	width_O1_L1_R1(nodep,vup); }
    virtual void visit(AstLogIf* nodep, AstNUser* vup) {	width_O1_L1_R1(nodep,vup); }
    virtual void visit(AstLogIff* nodep, AstNUser* vup) {	width_O1_L1_R1(nodep,vup); }

    // Widths: 1 bit out, Any width lhs
    void width_O1_L(AstNode* nodep, AstNUser* vup);
    virtual void visit(AstRedAnd* nodep, AstNUser* vup) {	width_O1_L(nodep,vup); }
    virtual void visit(AstRedOr* nodep, AstNUser* vup) {	width_O1_L(nodep,vup); }
    virtual void visit(AstRedXnor* nodep, AstNUser* vup){	width_O1_L(nodep,vup); }
    virtual void visit(AstRedXor* nodep,AstNUser* vup) {	width_O1_L(nodep,vup); }
    virtual void visit(AstIsUnknown* nodep,AstNUser* vup) {	width_O1_L(nodep,vup); }
    virtual void visit(AstOneHot* nodep,AstNUser* vup) {	width_O1_L(nodep,vup); }
    virtual void visit(AstOneHot0* nodep,AstNUser* vup) {	width_O1_L(nodep,vup); }

    // Widths: 1 bit out, lhs width == rhs width
    void width_O1_L_Rlhs(AstNode* nodep, AstNUser* vup);
    virtual void visit(AstEq* nodep, AstNUser* vup) {		width_O1_L_Rlhs(nodep,vup); }
    virtual void visit(AstEqCase* nodep, AstNUser* vup) {	width_O1_L_Rlhs(nodep,vup); }
    virtual void visit(AstEqWild* nodep, AstNUser* vup) {	width_O1_L_Rlhs(nodep,vup); }
    virtual void visit(AstGt* nodep, AstNUser* vup) {		width_O1_L_Rlhs(nodep,vup); }
    virtual void visit(AstGtS* nodep, AstNUser* vup) {		width_O1_L_Rlhs(nodep,vup); }
    virtual void visit(AstGte* nodep, AstNUser* vup) {		width_O1_L_Rlhs(nodep,vup); }
    virtual void visit(AstGteS* nodep, AstNUser* vup) {		width_O1_L_Rlhs(nodep,vup); }
    virtual void visit(AstLt* nodep, AstNUser* vup) {		width_O1_L_Rlhs(nodep,vup); }
    virtual void visit(AstLtS* nodep, AstNUser* vup) {		width_O1_L_Rlhs(nodep,vup); }
    virtual void visit(AstLte* nodep, AstNUser* vup) {		width_O1_L_Rlhs(nodep,vup); }
    virtual void visit(AstLteS* nodep, AstNUser* vup) {		width_O1_L_Rlhs(nodep,vup); }
    virtual void visit(AstNeq* nodep, AstNUser* vup) {		width_O1_L_Rlhs(nodep,vup); }
    virtual void visit(AstNeqCase* nodep, AstNUser* vup){	width_O1_L_Rlhs(nodep,vup); }
    virtual void visit(AstNeqWild* nodep, AstNUser* vup){	width_O1_L_Rlhs(nodep,vup); }

    // Widths: out width = lhs width = rhs width
    void width_Omax_L_Rlhs(AstNode* nodep, AstNUser* vup);
    virtual void visit(AstAnd* nodep, AstNUser* vup) {		width_Omax_L_Rlhs(nodep,vup); }
    virtual void visit(AstOr* nodep, AstNUser* vup) {		width_Omax_L_Rlhs(nodep,vup); }
    virtual void visit(AstXnor* nodep, AstNUser* vup) {		width_Omax_L_Rlhs(nodep,vup); }
    virtual void visit(AstXor* nodep, AstNUser* vup) {		width_Omax_L_Rlhs(nodep,vup); }
    // Multiple possible reasonable division width conversions.  Just keep our code simple, they aren't common.
    virtual void visit(AstModDiv* nodep, AstNUser* vup) {	width_Omax_L_Rlhs(nodep,vup); }
    virtual void visit(AstModDivS* nodep, AstNUser* vup) {	width_Omax_L_Rlhs(nodep,vup); }
    virtual void visit(AstDiv* nodep, AstNUser* vup) {		width_Omax_L_Rlhs(nodep,vup); }
    virtual void visit(AstDivS* nodep, AstNUser* vup) {		width_Omax_L_Rlhs(nodep,vup); }
    // Special warning suppression rules
    virtual void visit(AstSub* nodep, AstNUser* vup) {		width_Omax_L_Rlhs(nodep,vup); }
    virtual void visit(AstAdd* nodep, AstNUser* vup) {		width_Omax_L_Rlhs(nodep,vup); }
    virtual void visit(AstMul* nodep, AstNUser* vup) {		width_Omax_L_Rlhs(nodep,vup); }
    virtual void visit(AstMulS* nodep, AstNUser* vup) {		width_Omax_L_Rlhs(nodep,vup); }

    // Widths: out width = lhs width, but upper matters
    void width_Olhs_L(AstNodeUniop* nodep, AstNUser* vup);
    virtual void visit(AstNot* nodep, AstNUser* vup) {		width_Olhs_L(nodep,vup); }
    virtual void visit(AstUnaryMin* nodep, AstNUser* vup) {	width_Olhs_L(nodep,vup); }

    // Widths: out width = lhs width, upper doesn't matter
    void width_Olhs_Lforce(AstNodeUniop* nodep, AstNUser* vup);
    virtual void visit(AstSigned* nodep, AstNUser* vup) {	width_Olhs_Lforce(nodep,vup); }
    virtual void visit(AstUnsigned* nodep, AstNUser* vup) {	width_Olhs_Lforce(nodep,vup); }

    // Widths: Output width from lhs, rhs<33 bits
    void width_Olhs_L_R32(AstNode* nodep, AstNUser* vup);
    virtual void visit(AstPow* nodep, AstNUser* vup) {		width_Olhs_L_R32(nodep,vup); }
    virtual void visit(AstPowS* nodep, AstNUser* vup) {		width_Olhs_L_R32(nodep,vup); }
    virtual void visit(AstShiftL* nodep, AstNUser* vup) {	width_Olhs_L_R32(nodep,vup); }
    virtual void visit(AstShiftR* nodep, AstNUser* vup) {	width_Olhs_L_R32(nodep,vup); }
    virtual void visit(AstShiftRS* nodep, AstNUser* vup) {	width_Olhs_L_R32(nodep,vup); }

    // Special cases.  So many....
    virtual void visit(AstNodeCond* nodep, AstNUser* vup) {
	// op=cond?expr1:expr2 is a Good large example of the propagation mess
	if (vup->c()->prelim()) {  // First stage evaluation
	    // Just once, do the conditional, expect one bit out.
	    nodep->condp()->iterateAndNext(*this,WidthVP(1,1,BOTH).p());
	    // Determine sub expression widths only relying on what's in the subops
	    nodep->expr1p()->iterateAndNext(*this,WidthVP(ANYSIZE,0,PRELIM).p());
	    nodep->expr2p()->iterateAndNext(*this,WidthVP(ANYSIZE,0,PRELIM).p());
	}
	// Calculate width of this expression.
	// First call (prelim()) vup->c()->width() is probably zero, so we'll return
	//  the size of this subexpression only.
	// Second call (final()) vup->c()->width() is probably the expression size, so
	//  the expression includes the size of the output too.
	int width  = max(vup->c()->width(),    max(nodep->expr1p()->width(),    nodep->expr2p()->width()));
	int mwidth = max(vup->c()->widthMin(), max(nodep->expr1p()->widthMin(), nodep->expr2p()->widthMin()));
	nodep->width(width,mwidth);
	if (vup->c()->final()) {
	    // Final width known, so make sure children recompute & check their sizes
	    nodep->expr1p()->iterateAndNext(*this,WidthVP(width,mwidth,FINAL).p());
	    nodep->expr2p()->iterateAndNext(*this,WidthVP(width,mwidth,FINAL).p());
	    // Error report and change sizes for suboperands of this node.
	    widthCheckReduce(nodep,"Conditional Expression",nodep->condp(),1,0);
	    widthCheck(nodep,"Conditional True",nodep->expr1p(),width,mwidth);
	    widthCheck(nodep,"Conditional False",nodep->expr2p(),width,mwidth);
	}
    }
    virtual void visit(AstConcat* nodep, AstNUser* vup) {
	if (vup->c()->prelim()) {
	    nodep->lhsp()->iterateAndNext(*this,WidthVP(ANYSIZE,0,BOTH).p());
	    nodep->rhsp()->iterateAndNext(*this,WidthVP(ANYSIZE,0,BOTH).p());
	    nodep->width(nodep->lhsp()->width() + nodep->rhsp()->width(),
			 nodep->lhsp()->widthMin() + nodep->rhsp()->widthMin());
	    // Cleanup zero width Verilog2001 {x,{0{foo}}} now,
	    // otherwise having width(0) will cause later assertions to fire
	    if (AstReplicate* repp=nodep->lhsp()->castReplicate()) {
		if (repp->width()==0) {  // Keep rhs
		    nodep->replaceWith(nodep->rhsp()->unlinkFrBack());
		    pushDeletep(nodep); nodep=NULL;
		    return;
		}
	    }
	    if (AstReplicate* repp=nodep->rhsp()->castReplicate()) {
		if (repp->width()==0) {  // Keep lhs
		    nodep->replaceWith(nodep->lhsp()->unlinkFrBack());
		    pushDeletep(nodep); nodep=NULL;
		    return;
		}
	    }
	}
	if (vup->c()->final()) {
	    if (!nodep->widthSized()) {
		// See also error in V3Number
		nodep->v3warn(WIDTHCONCAT,"Unsized numbers/parameters not allowed in concatenations.");
	    }
	}
    }
    virtual void visit(AstReplicate* nodep, AstNUser* vup) {
	if (vup->c()->prelim()) {
	    nodep->lhsp()->iterateAndNext(*this,WidthVP(ANYSIZE,0,BOTH).p());
	    nodep->rhsp()->iterateAndNext(*this,WidthVP(ANYSIZE,0,BOTH).p());
	    V3Const::constifyParam(nodep->rhsp());
	    AstConst* constp = nodep->rhsp()->castConst();
	    if (!constp) { nodep->v3error("Replication value isn't a constant."); return; }
	    uint32_t times = constp->toUInt();
	    if (times==0 && !nodep->backp()->castConcat()) {  // Concat Visitor will clean it up.
		nodep->v3error("Replication value of 0 is only legal under a concatenation."); times=1;
	    }
	    nodep->width((nodep->lhsp()->width() * times),
			 (nodep->lhsp()->widthMin() * times));
	}
	if (vup->c()->final()) {
	    if (!nodep->widthSized()) {
		// See also error in V3Number
		nodep->v3warn(WIDTHCONCAT,"Unsized numbers/parameters not allowed in replications.");
	    }
	}
    }
    virtual void visit(AstRange* nodep, AstNUser* vup) {
	if (vup->c()->prelim()) {
	    nodep->msbp()->iterateAndNext(*this,WidthVP(ANYSIZE,0,BOTH).p());
	    nodep->lsbp()->iterateAndNext(*this,WidthVP(ANYSIZE,0,BOTH).p());
	    V3Const::constifyParam(nodep->msbp());
	    V3Const::constifyParam(nodep->lsbp());
	    AstConst* msbConstp = nodep->msbp()->castConst();
	    AstConst* lsbConstp = nodep->lsbp()->castConst();
	    if (!msbConstp || !lsbConstp) {
		if (!msbConstp) nodep->v3error("MSB of bit range isn't a constant");
		if (!lsbConstp) nodep->v3error("LSB of bit range isn't a constant");
		nodep->width(1,1); return;
	    }
	    int msb = msbConstp->toSInt();
	    int lsb = lsbConstp->toSInt();
	    if (msb > (1<<28)) nodep->v3error("MSB of bit range is huge; vector of over 1billion bits: 0x"<<hex<<msb);
	    if (msb<lsb) {
		// If it's a array, ok to have either ordering, we'll just correct
		// So, see if we're sitting under a variable's arrayp.
		AstNode* huntbackp = nodep;
		while (huntbackp->backp()->castRange()) huntbackp=huntbackp->backp();
		if (huntbackp->backp()->castVar()
		    && huntbackp->backp()->castVar()->arraysp()==huntbackp) {
		} else {
		    nodep->v3error("Unsupported: MSB < LSB of bit range: "<<msb<<"<"<<lsb);
		}
		// Correct it.
		swap(msbConstp, lsbConstp);
		int x=msb; msb=lsb; lsb=x;
	    }
	    int width = msb-lsb+1;
	    nodep->width(width,width);
	}
    }
    virtual void visit(AstSel* nodep, AstNUser* vup) {
	if (vup->c()->prelim()) {
	    nodep->fromp()->iterateAndNext(*this,WidthVP(ANYSIZE,0,BOTH).p());
	    nodep->lsbp()->iterateAndNext(*this,WidthVP(ANYSIZE,0,BOTH).p());
	    nodep->widthp()->iterateAndNext(*this,WidthVP(ANYSIZE,0,BOTH).p());
	    V3Const::constifyParam(nodep->widthp());
	    AstConst* widthConstp = nodep->widthp()->castConst();
	    if (!widthConstp) {
		nodep->v3error("Width of bit extract isn't a constant");
		nodep->width(1,1); return;
	    }
	    int width = nodep->widthConst();
	    nodep->width(width,width);
	    if (nodep->lsbp()->castConst()
		&& nodep->msbConst() < nodep->lsbConst()) {
		nodep->v3error("Unsupported: MSB < LSB of bit extract: "
			       <<nodep->msbConst()<<"<"<<nodep->lsbConst());
		width = (nodep->lsbConst() - nodep->msbConst() + 1);
		nodep->width(width,width);
		nodep->widthp()->replaceWith(new AstConst(nodep->widthp()->fileline(),
							  width));
		nodep->lsbp()->replaceWith(new AstConst(nodep->lsbp()->fileline(), 0));
	    }
	    // We're extracting, so just make sure the expression is at least wide enough.
	    if (nodep->fromp()->width() < width) {
		nodep->v3error("Extracting "<<width
			       <<" bits from only "<<nodep->fromp()->width()<<" bit number");
		// Extend it.
		widthCheck(nodep,"errorless...",nodep->fromp(),width,width,true/*noerror*/);
	    }
	    // Check bit indexes.
	    // What is the MSB?  We want the true MSB, not one starting at 0,
	    // because a 4 bit index is required to look at a one-bit variable[15:15]
	    int frommsb = nodep->fromp()->width() - 1;
	    int fromlsb = 0;
	    AstNodeVarRef* varrp = nodep->fromp()->castNodeVarRef();
	    if (varrp && varrp->varp()->rangep()) {	// Selecting a bit from a multibit register
		frommsb = varrp->varp()->msbMaxSelect();  // Corrected for negative lsb
		fromlsb = varrp->varp()->lsb();
	    }
	    int selwidth = V3Number::log2b(frommsb+1-1)+1;	// Width to address a bit
	    nodep->fromp()->iterateAndNext(*this,WidthVP(selwidth,selwidth,BOTH).p());
	    if (widthBad(nodep->lsbp(),selwidth,selwidth)
		&& nodep->lsbp()->width()!=32) {
		nodep->v3warn(WIDTH,"Bit extraction of var["<<frommsb<<":"<<fromlsb<<"] requires "
			      <<selwidth<<" bit index, not "
			      <<nodep->lsbp()->width()
			      <<(nodep->lsbp()->width()!=nodep->lsbp()->widthMin()
				 ?" or "+cvtToStr(nodep->lsbp()->widthMin()):"")
			      <<" bits.");
	    }
	    if (nodep->lsbp()->castConst() && nodep->msbConst() > frommsb) {
		// See also warning in V3Const
		// We need to check here, because the widthCheck may silently
		// add another SEL which will loose the out-of-range check
		nodep->v3error("Selection index out of range: "
 			       <<nodep->msbConst()<<":"<<nodep->lsbConst()
			       <<" outside "<<frommsb<<":"<<fromlsb);
	    }
	    widthCheck(nodep,"Extract Range",nodep->lsbp(),selwidth,selwidth,true);
	}
    }

    virtual void visit(AstArraySel* nodep, AstNUser* vup) {
	if (vup->c()->prelim()) {
	    nodep->bitp()->iterateAndNext(*this,WidthVP(ANYSIZE,0,BOTH).p());
	    nodep->fromp()->iterateAndNext(*this,WidthVP(ANYSIZE,0,BOTH).p());
	    AstNode* basefromp = AstArraySel::baseFromp(nodep->fromp());
	    int dimension      = AstArraySel::dimension(nodep->fromp());
	    AstNodeVarRef* varrp = basefromp->castNodeVarRef();
	    if (!varrp) nodep->v3fatalSrc("No VarRef found under ArraySel(s)");
	    //
	    int frommsb;
	    int fromlsb;
	    if (!varrp->varp()->arrayp(dimension)) {
		nodep->v3fatalSrc("Array reference exceeds dimension of array");
	    }
	    if (1) {	// ARRAY slice extraction
		int outwidth = varrp->width();		// Width of variable
		frommsb = varrp->varp()->arrayp(dimension)->msbConst();
		fromlsb = varrp->varp()->arrayp(dimension)->lsbConst();
		if (fromlsb>frommsb) {int t=frommsb; frommsb=fromlsb; fromlsb=t; }
		// However, if the lsb<0 we may go negative, so need more bits!
		if (fromlsb < 0) frommsb += -fromlsb;
		nodep->width(outwidth,outwidth);		// Width out = width of array
	    }
	    int selwidth = V3Number::log2b(frommsb+1-1)+1;	// Width to address a bit
	    nodep->fromp()->iterateAndNext(*this,WidthVP(selwidth,selwidth,BOTH).p());
	    if (widthBad(nodep->bitp(),selwidth,selwidth)
		&& nodep->bitp()->width()!=32)
		nodep->v3warn(WIDTH,"Bit extraction of array["<<frommsb<<":"<<fromlsb<<"] requires "
			      <<selwidth<<" bit index, not "
			      <<nodep->bitp()->width()
			      <<(nodep->bitp()->width()!=nodep->bitp()->widthMin()
				 ?" or "+cvtToStr(nodep->bitp()->widthMin()):"")
			      <<" bits.");
	    widthCheck(nodep,"Extract Range",nodep->bitp(),selwidth,selwidth,true);
	}
    }
    virtual void visit(AstExtend* nodep, AstNUser* vup) {
	// Only created by this process, so we know width from here down it is correct.
    }
    virtual void visit(AstExtendS* nodep, AstNUser* vup) {
	// Only created by signing process, so we know width from here down it is correct.
    }
    virtual void visit(AstConst* nodep, AstNUser* vup) {
	if (vup && vup->c()->prelim()) {
	    if (nodep->num().sized()) {
		nodep->width(nodep->num().width(), nodep->num().width());
	    } else {
		nodep->width(nodep->num().width(), nodep->num().minWidth());
	    }
	}
    }
    virtual void visit(AstRand* nodep, AstNUser* vup) {
	if (vup->c()->prelim()) {
	    nodep->width(32,32);  // Says the spec
	}
    }
    virtual void visit(AstTime* nodep, AstNUser*) {
	nodep->width(64,64);
    }
    virtual void visit(AstUCFunc* nodep, AstNUser* vup) {
	// Give it the size the user wants.
	if (vup && vup->c()->prelim()) {
	    nodep->width(32,1);  // We don't care
	}
	if (vup->c()->final()) {
	    nodep->width(vup->c()->width(),vup->c()->widthMin());  // We don't care
	    if (nodep->width()>64) nodep->v3error("Unsupported: $c can't generate wider than 64 bits");
	}
	// Just let all arguments seek their natural sizes
	nodep->iterateChildren(*this,WidthVP(ANYSIZE,0,BOTH).p());
    }
    virtual void visit(AstCLog2* nodep, AstNUser* vup) {
	if (vup->c()->prelim()) {
	    nodep->lhsp()->iterateAndNext(*this,WidthVP(ANYSIZE,0,BOTH).p());
	    nodep->width(32,32);
	}
    }
    virtual void visit(AstCountOnes* nodep, AstNUser* vup) {
	if (vup->c()->prelim()) {
	    nodep->lhsp()->iterateAndNext(*this,WidthVP(ANYSIZE,0,BOTH).p());
	    // If it's a 32 bit number, we need a 6 bit number as we need to return '32'.
	    int selwidth = V3Number::log2b(nodep->lhsp()->width())+1;
	    nodep->width(selwidth,selwidth);
	}
    }
    virtual void visit(AstAttrOf* nodep, AstNUser*) {
	nodep->fromp()->iterateAndNext(*this,WidthVP(ANYSIZE,0,BOTH).p());
	nodep->width(32,1);	// Approximation, unsized 32
    }
    virtual void visit(AstText* nodep, AstNUser* vup) {
	// Only used in CStmts which don't care....
    }
    virtual void visit(AstScopeName* nodep, AstNUser* vup) {
	// Only used in Displays which don't care....
    }
    virtual void visit(AstVar* nodep, AstNUser* vup) {
	//if (debug()) nodep->dumpTree(cout,"  InitPre: ");
	// Must have deterministic constant width
	// We can't skip this step when width()!=0, as creating a AstVar
	// with non-constant range gets size 1, not size 0.
	int width=1; int mwidth=1;
	nodep->arraysp()->iterateAndNext(*this,WidthVP(ANYSIZE,0,BOTH).p());
	if (nodep->rangep()) {
	    nodep->rangep()->iterateAndNext(*this,WidthVP(ANYSIZE,0,BOTH).p());
	    width = mwidth = nodep->rangep()->width();
	}
	else if (nodep->isInteger() || nodep->isGenVar()) {
	    width = 32;
	    mwidth = 1;	// Consider it unsized, as we want x[int] to work, and also want {int} to fail.
	}
	else if (nodep->isParam()) { // unranged
	    width = mwidth = 0;  // But see below later.
	}
	if (nodep->initp()) {
	    nodep->initp()->iterateAndNext(*this,WidthVP(width,0,BOTH).p());
	    if (nodep->isParam()) {
		if (nodep->rangep()) {
		    // Parameters need to preserve widthMin from the value, not get a constant size
		    mwidth = nodep->initp()->widthMin();
		} else if (nodep->initp()->widthSized()) {
		    width = mwidth = nodep->initp()->width();
		} else {
		    if (nodep->initp()->width()>32) nodep->initp()->v3warn(WIDTH,"Assigning >32 bit to unranged parameter (defaults to 32 bits)\n");
		    width = 32;
		    mwidth = nodep->initp()->widthMin();
		}
	    }
	    //if (debug()) nodep->dumpTree(cout,"  final: ");
	}
	if (nodep->isParam() && !nodep->rangep()) {
	    // Parameter sizes can come from the thing they get assigned from
	    // They then "stick" to that width.
	    if (!width) width=32;	// Or, if nothing, they're 32 bits.
	    nodep->rangep(new AstRange(nodep->fileline(),width-1,0));
	    nodep->rangep()->width(width,width);
	}
	nodep->width(width,mwidth);  // No need to check; varrefs are the "checkers"
	if (nodep->initp()) widthCheck(nodep,"Initial value",nodep->initp(),width,mwidth);
	UINFO(4,"varWidthed "<<nodep<<endl);
	//if (debug()) nodep->dumpTree(cout,"  InitPos: ");
    }
    virtual void visit(AstNodeVarRef* nodep, AstNUser* vup) {
	if (nodep->varp()->width()==0) {
	    // Var hasn't been widthed, so make it so.
	    nodep->varp()->iterate(*this);
	}
	if ((nodep->varp()->isInteger() || nodep->varp()->isGenVar())
	    && nodep->backp()->castNodeAssign()) {  // On LHS
	    // Consider Integers on LHS to sized (else would be unsized.)
	    nodep->width(32,32);
	} else {
	    nodep->width(nodep->varp()->width(), nodep->varp()->widthMin());
	}
    }
    virtual void visit(AstPslClocked* nodep, AstNUser*) {
	nodep->propp()->iterateAndNext(*this,WidthVP(1,1,BOTH).p());
	nodep->sensesp()->iterateAndNext(*this);
	if (nodep->disablep()) {
	    nodep->disablep()->iterateAndNext(*this,WidthVP(1,1,BOTH).p());
	    widthCheckReduce(nodep,"Disable",nodep->disablep(),1,1); // it's like an if() condition.
	}
	widthCheckReduce(nodep,"Property",nodep->propp(),1,1);	// it's like an if() condition.
	nodep->width(1,1);
    }

    //--------------------
    // Top levels

    virtual void visit(AstNodeCase* nodep, AstNUser*) {
	// TOP LEVEL NODE
	AstNodeCase* lastCasep = m_casep;
	m_casep = nodep;
	nodep->exprp()->iterateAndNext(*this,WidthVP(ANYSIZE,0,PRELIM).p());
	for (AstCaseItem* itemp = nodep->itemsp(); itemp; itemp=itemp->nextp()->castCaseItem()) {
	    itemp->iterate(*this,WidthVP(ANYSIZE,0,PRELIM).p());
	}
	int width = nodep->exprp()->width();
	int mwidth = nodep->exprp()->widthMin();
	for (AstCaseItem* itemp = nodep->itemsp(); itemp; itemp=itemp->nextp()->castCaseItem()) {
	    width = max(width,itemp->width());
	    mwidth = max(mwidth,itemp->widthMin());
	}
	nodep->exprp()->iterateAndNext(*this,WidthVP(width,mwidth,FINAL).p());
	for (AstCaseItem* itemp = nodep->itemsp(); itemp; itemp=itemp->nextp()->castCaseItem()) {
	    itemp->iterate(*this,WidthVP(width,mwidth,FINAL).p());
	}
        widthCheck(nodep,"Case expression",nodep->exprp(),width,mwidth);
	m_casep = lastCasep;
    }
    virtual void visit(AstCaseItem* nodep, AstNUser* vup) {
	// Same for both prelim() and final()
	if (!m_casep->castGenCase()) nodep->bodysp()->iterateAndNext(*this);
	if (!nodep->condsp()) {
	    // Else "default:" of the case, just return benign value
	    nodep->width(vup->c()->width(),vup->c()->widthMin());
	} else {
	    // Need to look across multiple case values for one set of statements
	    int width = nodep->condsp()->width();
	    int mwidth = nodep->condsp()->widthMin();
	    for (AstNode* condp = nodep->condsp(); condp; condp=condp->nextp()) {
		condp->iterate(*this,vup);
		width = max(width,condp->width());
		mwidth = max(mwidth,condp->widthMin());
		if (vup->c()->final()) {
		    widthCheck(nodep,"Case Item",condp,vup->c()->width(),vup->c()->widthMin());
		}
	    }
	    nodep->width(width,mwidth);
	}
    }
    virtual void visit(AstNodeFor* nodep, AstNUser*) {
	// TOP LEVEL NODE
	nodep->initsp()->iterateAndNext(*this);
	nodep->condp()->iterateAndNext(*this,WidthVP(1,1,BOTH).p());
	if (!nodep->castGenFor()) nodep->bodysp()->iterateAndNext(*this);
	nodep->incsp()->iterateAndNext(*this);
	widthCheckReduce(nodep,"For Test Condition",nodep->condp(),1,1);	// it's like an if() condition.
    }
    virtual void visit(AstRepeat* nodep, AstNUser*) {
	nodep->countp()->iterateAndNext(*this,WidthVP(ANYSIZE,0,BOTH).p());
	nodep->bodysp()->iterateAndNext(*this);
    }
    virtual void visit(AstWhile* nodep, AstNUser*) {
	// TOP LEVEL NODE
	nodep->precondsp()->iterateAndNext(*this);
	nodep->condp()->iterateAndNext(*this,WidthVP(1,1,BOTH).p());
	nodep->bodysp()->iterateAndNext(*this);
	widthCheckReduce(nodep,"For Test Condition",nodep->condp(),1,1);	// it's like an if() condition.
    }
    virtual void visit(AstNodeIf* nodep, AstNUser*) {
	// TOP LEVEL NODE
	//if (debug()) nodep->dumpTree(cout,"  IfPre: ");
	if (!nodep->castGenIf()) {
	    nodep->ifsp()->iterateAndNext(*this);
	    nodep->elsesp()->iterateAndNext(*this);
	}
	nodep->condp()->iterateAndNext(*this,WidthVP(1,1,BOTH).p());
	widthCheckReduce(nodep,"If",nodep->condp(),1,1);	// it's like an if() condition.
	//if (debug()) nodep->dumpTree(cout,"  IfPos: ");
    }
    virtual void visit(AstNodeAssign* nodep, AstNUser*) {
	// TOP LEVEL NODE
	//if (debug()) nodep->dumpTree(cout,"  AssignPre: ");
	nodep->lhsp()->iterateAndNext(*this,WidthVP(ANYSIZE,0,BOTH).p());
	nodep->rhsp()->iterateAndNext(*this,WidthVP(ANYSIZE,0,PRELIM).p());
	if(!nodep->lhsp()->widthSized()) nodep->v3fatalSrc("How can LHS be unsized?");
	int awidth = nodep->lhsp()->width();
	if (awidth==0) {
	    awidth = nodep->rhsp()->width();	// Parameters can propagate by unsized assignment
	}
	nodep->rhsp()->iterateAndNext(*this,WidthVP(awidth,awidth,FINAL).p());
	nodep->width(awidth,awidth);  // We know the assign will truncate, so rather
	//UINFO(0,"aw "<<awidth<<" w"<<nodep->rhsp()->width()<<" m"<<nodep->rhsp()->widthMin()<<endl);
	// than using "width" and have the optimizer truncate the result, we do
	// it using the normal width reduction checks.
	widthCheck(nodep,"Assign RHS",nodep->rhsp(),awidth,awidth);
	//if (debug()) nodep->dumpTree(cout,"  AssignPos: ");
    }
    virtual void visit(AstNodePli* nodep, AstNUser*) {
	// Excludes NodeDisplay, see below
	// TOP LEVEL NODE
	// Just let all arguments seek their natural sizes
	nodep->iterateChildren(*this,WidthVP(ANYSIZE,0,BOTH).p());
    }
    virtual void visit(AstDisplay* nodep, AstNUser*) {
	if (nodep->filep()) {
	    nodep->filep()->iterateAndNext(*this,WidthVP(64,64,BOTH).p());
	    widthCheck(nodep,"file_descriptor (see docs)",nodep->filep(),64,64);
	}
	// Just let all arguments seek their natural sizes
	nodep->iterateChildren(*this,WidthVP(ANYSIZE,0,BOTH).p());
    }
    virtual void visit(AstFOpen* nodep, AstNUser*) {
	nodep->filep()->iterateAndNext(*this,WidthVP(64,64,BOTH).p());
	nodep->filenamep()->iterateAndNext(*this,WidthVP(ANYSIZE,0,BOTH).p());
	nodep->modep()->iterateAndNext(*this,WidthVP(ANYSIZE,0,BOTH).p());
	widthCheck(nodep,"file_descriptor (see docs)",nodep->filep(),64,64);
    }
    virtual void visit(AstFClose* nodep, AstNUser*) {
	nodep->filep()->iterateAndNext(*this,WidthVP(64,64,BOTH).p());
	widthCheck(nodep,"file_descriptor (see docs)",nodep->filep(),64,64);
    }
    virtual void visit(AstFEof* nodep, AstNUser*) {
	nodep->filep()->iterateAndNext(*this,WidthVP(64,64,BOTH).p());
	nodep->width(1,1);
	widthCheck(nodep,"file_descriptor (see docs)",nodep->filep(),64,64);
    }
    virtual void visit(AstFFlush* nodep, AstNUser*) {
	if (nodep->filep()) {
	    nodep->filep()->iterateAndNext(*this,WidthVP(64,64,BOTH).p());
	    widthCheck(nodep,"file_descriptor (see docs)",nodep->filep(),64,64);
	}
    }
    virtual void visit(AstFGetC* nodep, AstNUser* vup) {
	nodep->filep()->iterateAndNext(*this,WidthVP(64,64,BOTH).p());
	if (vup->c()->prelim()) {
	    nodep->width(32,8);
	}
	widthCheck(nodep,"file_descriptor (see docs)",nodep->filep(),64,64);
    }
    virtual void visit(AstFGetS* nodep, AstNUser* vup) {
	nodep->filep()->iterateAndNext(*this,WidthVP(64,64,BOTH).p());
	nodep->strgp()->iterateAndNext(*this,WidthVP(ANYSIZE,0,BOTH).p());
	if (vup->c()->prelim()) {
	    nodep->width(32,32);
	}
	widthCheck(nodep,"file_descriptor (see docs)",nodep->filep(),64,64);
    }
    virtual void visit(AstFScanF* nodep, AstNUser* vup) {
	nodep->filep()->iterateAndNext(*this,WidthVP(64,64,BOTH).p());
	nodep->exprsp()->iterateAndNext(*this,WidthVP(ANYSIZE,0,BOTH).p());
	if (vup->c()->prelim()) {
	    nodep->width(32,32);
	}
	widthCheck(nodep,"file_descriptor (see docs)",nodep->filep(),64,64);
    }
    virtual void visit(AstSScanF* nodep, AstNUser* vup) {
	nodep->fromp()->iterateAndNext(*this,WidthVP(ANYSIZE,0,BOTH).p());
	nodep->exprsp()->iterateAndNext(*this,WidthVP(ANYSIZE,0,BOTH).p());
	if (vup->c()->prelim()) {
	    nodep->width(32,32);
	}
    }
    virtual void visit(AstReadMem* nodep, AstNUser*) {
	nodep->filenamep()->iterateAndNext(*this,WidthVP(ANYSIZE,0,BOTH).p());
	nodep->memp()->iterateAndNext(*this,WidthVP(ANYSIZE,0,BOTH).p());
	nodep->lsbp()->iterateAndNext(*this,WidthVP(ANYSIZE,0,BOTH).p());
	nodep->msbp()->iterateAndNext(*this,WidthVP(ANYSIZE,0,BOTH).p());
    }
    virtual void visit(AstUCStmt* nodep, AstNUser*) {
	// TOP LEVEL NODE
	// Just let all arguments seek their natural sizes
	nodep->iterateChildren(*this,WidthVP(ANYSIZE,0,BOTH).p());
    }
    virtual void visit(AstPslCover* nodep, AstNUser*) {
	// TOP LEVEL NODE
	nodep->propp()->iterateAndNext(*this,WidthVP(1,1,BOTH).p());
	nodep->stmtsp()->iterateChildren(*this,WidthVP(ANYSIZE,0,BOTH).p());
	widthCheckReduce(nodep,"Property",nodep->propp(),1,1);	// it's like an if() condition.
    }
    virtual void visit(AstPslAssert* nodep, AstNUser*) {
	// TOP LEVEL NODE
	nodep->propp()->iterateAndNext(*this,WidthVP(1,1,BOTH).p());
	widthCheckReduce(nodep,"Property",nodep->propp(),1,1);	// it's like an if() condition.
    }
    virtual void visit(AstVAssert* nodep, AstNUser*) {
	// TOP LEVEL NODE
	nodep->propp()->iterateAndNext(*this,WidthVP(1,1,BOTH).p());
	nodep->passsp()->iterateAndNext(*this);
	nodep->failsp()->iterateAndNext(*this);
	widthCheckReduce(nodep,"Property",nodep->propp(),1,1);	// it's like an if() condition.
    }
    virtual void visit(AstPin* nodep, AstNUser*) {
	//if (debug()) nodep->dumpTree(cout,"-  PinPre: ");
	// TOP LEVEL NODE
	if (nodep->modVarp() && nodep->modVarp()->isGParam()) {
	    // Widthing handled as special init() case
	    nodep->iterateChildren(*this,WidthVP(ANYSIZE,0,BOTH).p());
	} else if (!m_paramsOnly){
	    if (nodep->modVarp()->width()==0) {
		// Var hasn't been widthed, so make it so.
		nodep->modVarp()->iterate(*this);
	    }
	    // Very much like like an assignment, but which side is LH/RHS
	    // depends on pin being a in/output/inout.
	    nodep->exprp()->iterateAndNext(*this,WidthVP(ANYSIZE,0,PRELIM).p());
	    int pinwidth = nodep->modVarp()->width();
	    int expwidth = nodep->exprp()->width();
	    bool inputPin = nodep->modVarp()->isInput();
	    int awidth;
	    if (m_cellRangep) {
		int numInsts = m_cellRangep->width();
		if (expwidth == pinwidth) {
		    awidth = pinwidth;	// Arrayed instants: widths match so connect to each instance
		} else if (expwidth == pinwidth*numInsts) {
		    awidth = pinwidth;  // Arrayed instants: one bit for each of the instants (each assign is 1 pinwidth wide)
		} else {
		    // Must be a error according to spec
		    // (Because we need to know if to connect to one or all instants)
		    nodep->v3error("Port connection "<<nodep->prettyName()<<" as part of a module instance array "
				   <<" requires "<<pinwidth<<" or "<<pinwidth*numInsts
				   <<" bits, but connection's "<<nodep->exprp()->prettyTypeName()
				   <<" generates "<<expwidth<<" bits.");
		    awidth = expwidth;
		}
		nodep->width(awidth,awidth);
	    } else {
		if (nodep->modVarp()->isTristate()) {
		    if (pinwidth != expwidth) {
			nodep->v3error("Unsupported: Port connection "<<nodep->prettyName()<<" to inout signal "
				       <<" requires "<<pinwidth
				       <<" bits, but connection's "<<nodep->exprp()->prettyTypeName()
				       <<" generates "<<expwidth<<" bits.");
			// otherwise would need some mess to force both sides to proper size
		    }
		}
		if (inputPin) {
		    // input pin is lhs, expr is rhs; resize expr to match
		    awidth = pinwidth;
		} else {
		    // output pin is rhs, expr is lhs
		    // We can't make the RANGE/EXTEND until V3Inst phase, as need RHS of assignment
		    awidth = expwidth;
		}
		nodep->width(awidth,awidth);
		widthCheckPin(nodep, nodep->exprp(), pinwidth, inputPin);
	    }
	    nodep->exprp()->iterateAndNext(*this,WidthVP(awidth,awidth,FINAL).p());
	}
	//if (debug()) nodep->dumpTree(cout,"-  PinPos: ");
    }
    virtual void visit(AstCell* nodep, AstNUser*) {
	if (!m_paramsOnly) {
	    if (nodep->rangep()) {
		m_cellRangep = nodep->rangep();
		nodep->rangep()->iterateAndNext(*this,WidthVP(ANYSIZE,0,BOTH).p());
	    }
	    nodep->pinsp()->iterateAndNext(*this);
	}
	nodep->paramsp()->iterateAndNext(*this);
	m_cellRangep = NULL;
    }
    virtual void visit(AstFunc* nodep, AstNUser* vup) {
	// Grab width from the output variable
	UINFO(5,"  FUNC "<<nodep<<endl);
	if (nodep->width()==0) {
	    // Function hasn't been widthed, so make it so.
	    nodep->iterateChildren(*this);
	    nodep->width(nodep->fvarp()->width(), nodep->fvarp()->width());
	}
    }
    virtual void visit(AstFuncRef* nodep, AstNUser* vup) {
	visit(nodep->castNodeFTaskRef(), vup);
	nodep->widthSignedFrom(nodep->taskp());
    }
    virtual void visit(AstNodeFTaskRef* nodep, AstNUser* vup) {
	// Function hasn't been widthed, so make it so.
	if (!nodep->taskp()) nodep->v3fatalSrc("Unlinked");
	if (nodep->taskp()->width()==0) {
	    if (m_taskDepth > 100) {
		nodep->v3error("Unsupported: Recursive function or task call\n");
		nodep->width(1,1);
		nodep->taskp()->width(1,1);
		return;
	    }
	    m_taskDepth++;
	    nodep->taskp()->iterate(*this);
	    m_taskDepth--;
	}
	// And do the arguments to the task/function too
	AstNode* pinp = nodep->pinsp();
	AstNode* stmt_nextp;	// List may change, so need to keep pointer
	for (AstNode* stmtp = nodep->taskp()->stmtsp(); stmtp; stmtp=stmt_nextp) {
	    stmt_nextp = stmtp->nextp();
	    if (AstVar* portp = stmtp->castVar()) {
		if (portp->isIO()
		    && pinp!=NULL) {  // Else argument error we'll find later
		    AstNode* pin_nextp = pinp->nextp();	// List may change, so remember nextp
		    int width = portp->width();
		    int ewidth = portp->widthMin();
		    pinp->accept(*this,WidthVP(width,ewidth,BOTH).p());
		    widthCheck(nodep,"Function Argument",pinp,width,ewidth);
		    pinp = pin_nextp;
		}
	    }
	}
    }
    virtual void visit(AstNetlist* nodep, AstNUser*) {
	// Iterate modules backwards, in bottom-up order.  That's faster
	nodep->iterateChildrenBackwards(*this);
    }

    //--------------------
    // Default
    virtual void visit(AstNode* nodep, AstNUser* vup) {
	// Default: Just iterate
	if (vup) nodep->v3fatalSrc("Visit function missing? Widthed expectation for this node: "<<nodep);
	nodep->iterateChildren(*this);
    }

    // METHODS
    bool widthBad (AstNode* nodep, int expWidth, int expWidthMin);
    void widthCheck (AstNode* nodep, const char* side,
		     AstNode* underp, int expWidth, int expWidthMin,
		     bool ignoreWarn=false);
    void widthCheckReduce (AstNode* nodep, const char* side,
			   AstNode* underp, int expWidth, int expWidthMin,
			   bool ignoreWarn=false);
    void widthCheckPin (AstNode* nodep, AstNode* underp, int expWidth, bool inputPin);
    bool fixAutoExtend (AstNode*& nodepr, int expWidth);
    void fixWidthExtend (AstNode* nodep, int expWidth);
    void fixWidthReduce (AstNode* nodep, int expWidth);
    void swap (AstNode* ap, AstNode* bp) {
	AstNRelinker aHandle;
	AstNRelinker bHandle;
	ap->unlinkFrBack(&aHandle);
	bp->unlinkFrBack(&bHandle);
	aHandle.relink(bp);
	bHandle.relink(ap);
    }

public:
    // CONSTUCTORS
    WidthVisitor(AstNode* nodep, bool paramsOnly) {
	m_paramsOnly = paramsOnly;
	m_taskDepth = 0;
	m_cellRangep = NULL;
	m_casep = NULL;
	nodep->accept(*this, WidthVP(ANYSIZE,0,BOTH).p());
    }
    virtual ~WidthVisitor() {}
};

//----------------------------------------------------------------------
// METHODs

bool WidthVisitor::widthBad (AstNode* nodep, int expWidth, int expWidthMin) {
    if (nodep->width()==0) nodep->v3fatalSrc("Under node has no expected width?? Missing Visitor func?");
    if (expWidth==0) nodep->v3fatalSrc("Node has no expected width?? Missing Visitor func?");
    if (expWidthMin==0) expWidthMin = expWidth;
    if (nodep->widthSized()  && nodep->width() != expWidthMin) return true;
    if (!nodep->widthSized() && nodep->widthMin() > expWidthMin) return true;
    return false;
}

void WidthVisitor::fixWidthExtend (AstNode* nodep, int expWidth) {
    // Fix the width mismatch by extending or truncating bits
    // Truncation is rarer, but can occur:  parameter [3:0] FOO = 64'h12312;
    // A(CONSTwide)+B becomes  A(CONSTwidened)+B
    // A(somewide)+B  becomes  A(TRUNC(somewide,width))+B
    // 		      or       A(EXTRACT(somewide,width,0))+B
    UINFO(4,"  widthExtend_old: "<<nodep<<endl);
    AstConst* constp = nodep->castConst();
    if (constp && !nodep->isSigned()) {
	// Save later constant propagation work, just right-size it.
	V3Number num (nodep->fileline(), expWidth);
	num.opAssign(constp->num());
	AstNode* newp = new AstConst(nodep->fileline(), num);
	newp->signedFrom(constp);
	constp->replaceWith(newp);
	pushDeletep(constp); constp=NULL;
	nodep=newp;
    } else if (expWidth<nodep->width()) {
	// Trunc - Extract
	AstNRelinker linker;
	nodep->unlinkFrBack(&linker);
	AstNode* newp = new AstSel(nodep->fileline(), nodep, 0, expWidth);
	linker.relink(newp);
	nodep=newp;
    } else {
	// Extend
	AstNRelinker linker;
	nodep->unlinkFrBack(&linker);
	AstNode* newp = (nodep->isSigned()
			 ? (new AstExtendS(nodep->fileline(), nodep))->castNode()
			 : (new AstExtend (nodep->fileline(), nodep))->castNode());
	linker.relink(newp);
	nodep=newp;
    }
    nodep->width(expWidth,expWidth);
    UINFO(4,"             _new: "<<nodep<<endl);
}

void WidthVisitor::fixWidthReduce (AstNode* nodep, int expWidth) {
    // Fix the width mismatch by adding a reduction OR operator
    // IF (A(CONSTwide)) becomes  IF (A(CONSTreduced))
    // IF (A(somewide))  becomes  IF (A(REDOR(somewide)))
    // Attempt to fix it quietly
    UINFO(4,"  widthReduce_old: "<<nodep<<endl);
    AstConst* constp = nodep->castConst();
    if (constp) {
	V3Number num (nodep->fileline(), expWidth);
	num.opRedOr(constp->num());
	AstNode* newp = new AstConst(nodep->fileline(), num);
	newp->signedFrom(constp);
	constp->replaceWith(newp);
	nodep=newp;
    } else {
	AstNRelinker linker;
	nodep->unlinkFrBack(&linker);
	AstNode* newp = new AstRedOr(nodep->fileline(), nodep);
	linker.relink(newp);
	nodep=newp;
    }
    nodep->width(expWidth,expWidth);
    UINFO(4,"             _new: "<<nodep<<endl);
}

bool WidthVisitor::fixAutoExtend (AstNode*& nodepr, int expWidth) {
    // For SystemVerilog '0,'1,'x,'z, autoextend and don't warn
    if (AstConst* constp = nodepr->castConst()) {
	if (constp->num().autoExtend() && !constp->num().sized() && constp->width()==1) {
	    // Make it the proper size.  Careful of proper extension of 0's/1's
	    V3Number num (constp->fileline(), expWidth);
	    num.opRepl(constp->num(), expWidth);  // {width{'1}}
	    AstNode* newp = new AstConst(constp->fileline(), num);
	    // Spec says always unsigned with proper width
	    if (debug()>4) constp->dumpTree(cout,"  fixAutoExtend_old: ");
	    if (debug()>4)   newp->dumpTree(cout,"               _new: ");
	    constp->replaceWith(newp);
	    constp->deleteTree(); constp=NULL;
	    // Tell caller the new constp, and that we changed it.
	    nodepr = newp;
	    return true;
	}
    }
    return false; // No change
}

void WidthVisitor::widthCheck (AstNode* nodep, const char* side,
			      AstNode* underp, int expWidth, int expWidthMin,
			      bool ignoreWarn) {
    //UINFO(9,"wchk "<<side<<endl<<"  "<<nodep<<endl<<"  "<<underp<<endl<<"  e"<<expWidth<<" m"<<expWidthMin<<" i"<<ignoreWarn<<endl);
    if (expWidthMin==0) expWidthMin = expWidth;
    bool bad = widthBad(underp,expWidth,expWidthMin);
    if (bad && fixAutoExtend(underp/*ref*/,expWidth)) bad=false;  // Changes underp
    if (underp->castConst() && underp->castConst()->num().isFromString()
	&& expWidth > underp->width()
	&& (((expWidth - underp->width()) % 8) == 0)) {  // At least it's character sized
	// reg [31:0] == "foo" we'll consider probably fine.
	// Maybe this should be a special warning?  Not for now.
	ignoreWarn = true;
    }
    if (bad && !ignoreWarn) {
	if (debug()>4) nodep->backp()->dumpTree(cout,"  back: ");
	nodep->v3warn(WIDTH,"Operator "<<nodep->prettyTypeName()
		      <<" expects "<<expWidth
		      <<(expWidth!=expWidthMin?" or "+cvtToStr(expWidthMin):"")
		      <<" bits on the "<<side<<", but "<<side<<"'s "
		      <<underp->prettyTypeName()<<" generates "<<underp->width()
		      <<(underp->width()!=underp->widthMin()
			 ?" or "+cvtToStr(underp->widthMin()):"")
		      <<" bits.");
    }
    if (bad || underp->width()!=expWidth) {
	fixWidthExtend(underp, expWidth); underp=NULL;//Changed
    }
}

void WidthVisitor::widthCheckReduce (AstNode* nodep, const char* side,
			      AstNode* underp, int expWidth, int expWidthMin,
			      bool ignoreWarn) {
    if (expWidthMin==0) expWidthMin = expWidth;
    if (expWidth!=1) nodep->v3fatalSrc("Only for binary functions");
    bool bad = widthBad(underp,expWidth,expWidthMin);
    if (bad) {
	if (!ignoreWarn) {
	    if (debug()>4) nodep->backp()->dumpTree(cout,"  back: ");
	    nodep->v3warn(WIDTH,"Logical Operator "<<nodep->prettyTypeName()
			  <<" expects 1 bit on the "<<side<<", but "<<side<<"'s "
			  <<underp->prettyTypeName()<<" generates "<<underp->width()
			  <<(underp->width()!=underp->widthMin()
			     ?" or "+cvtToStr(underp->widthMin()):"")
			  <<" bits.");
	}
	fixWidthReduce(underp, expWidth); underp=NULL;//Changed
    }
}

void WidthVisitor::widthCheckPin (AstNode* nodep, AstNode* underp, int expWidth, bool inputPin) {
    bool bad = widthBad(underp,expWidth,expWidth);
    if (bad && fixAutoExtend(underp/*ref*/,expWidth)) bad=false;  // Changes underp
    if (bad) {
	nodep->v3warn(WIDTH,(inputPin?"Input":"Output")
		      <<" port connection "<<nodep->prettyName()
		      <<" expects "<<expWidth
		      <<" bits but connection's "
		      <<underp->prettyTypeName()<<" generates "<<underp->width()
		      <<(underp->width()!=underp->widthMin()
			 ?" or "+cvtToStr(underp->widthMin()):"")
		      <<" bits.");
    }
    // We only fix input mismatches
    if (bad && inputPin) {
	fixWidthExtend(underp, expWidth); underp=NULL;//Changed
    }
}

void WidthVisitor::width_O1_L1(AstNode* nodep, AstNUser* vup) {
    // Widths: 1 bit out, lhs 1 bit
    // We calculate the width of the UNDER expression.
    // We then check its width to see if it's legal, and edit if not
    // We finally set the width of our output
    if (nodep->op2p()) nodep->v3fatalSrc("For unary ops only!");
    if (vup->c()->prelim()) {
	nodep->op1p()->iterateAndNext(*this,WidthVP(1,0,BOTH).p());
    }
    nodep->width(1,1);
    if (vup->c()->final()) {
	widthCheckReduce(nodep,"LHS",nodep->op1p(),1,1);
    }
}

void WidthVisitor::width_O1_L1_R1(AstNode* nodep, AstNUser* vup) {
    // Widths: 1 bit out, lhs 1 bit, rhs 1 bit
    if (!nodep->op2p()) nodep->v3fatalSrc("For binary ops only!");
    if (vup->c()->prelim()) {
	nodep->op1p()->iterateAndNext(*this,WidthVP(1,0,BOTH).p());
	nodep->op2p()->iterateAndNext(*this,WidthVP(1,0,BOTH).p());
    }
    nodep->width(1,1);
    if (vup->c()->final()) {
	widthCheckReduce(nodep,"LHS",nodep->op1p(),1,1);
	widthCheckReduce(nodep,"RHS",nodep->op2p(),1,1);
    }
}

void WidthVisitor::width_O1_L(AstNode* nodep, AstNUser* vup) {
    // Widths: 1 bit out, Any width lhs
    if (nodep->op2p()) nodep->v3fatalSrc("For unary ops only!");
    if (vup->c()->prelim()) {
	nodep->op1p()->iterateAndNext(*this,WidthVP(ANYSIZE,0,BOTH).p());
    }
    nodep->width(1,1);
}

void WidthVisitor::width_O1_L_Rlhs(AstNode* nodep, AstNUser* vup) {
    // Widths: 1 bit out, lhs width == rhs width
    if (!nodep->op2p()) nodep->v3fatalSrc("For binary ops only!");
    if (vup->c()->prelim()) {
	nodep->op1p()->iterateAndNext(*this,WidthVP(ANYSIZE,0,PRELIM).p());
	nodep->op2p()->iterateAndNext(*this,WidthVP(ANYSIZE,0,PRELIM).p());
    }
    int width  = max(nodep->op1p()->width(),    nodep->op2p()->width());
    int ewidth = max(nodep->op1p()->widthMin(), nodep->op2p()->widthMin());
    nodep->width(1,1);
    if (vup->c()->final()) {
	nodep->op1p()->iterateAndNext(*this,WidthVP(width,ewidth,FINAL).p());
	nodep->op2p()->iterateAndNext(*this,WidthVP(width,ewidth,FINAL).p());
	widthCheck(nodep,"LHS",nodep->op1p(),width,ewidth);
	widthCheck(nodep,"RHS",nodep->op2p(),width,ewidth);
    }
}

void WidthVisitor::width_Olhs_L(AstNodeUniop* nodep, AstNUser* vup) {
    // Widths: out width = lhs width
    // "Interim results shall take the max of operands, including LHS of assignments"
    if (nodep->op2p()) nodep->v3fatalSrc("For unary ops only!");
    if (vup->c()->prelim()) {
	nodep->lhsp()->iterateAndNext(*this,WidthVP(ANYSIZE,0,PRELIM).p());
    }
    int width  = max(vup->c()->width(),    nodep->lhsp()->width());
    int ewidth = max(vup->c()->widthMin(), nodep->lhsp()->widthMin());
    nodep->width(width,ewidth);
    if (vup->c()->final()) {
	nodep->lhsp()->iterateAndNext(*this,WidthVP(width,ewidth,FINAL).p());
	widthCheck(nodep,"LHS",nodep->lhsp(),width,ewidth);
    }
}

void WidthVisitor::width_Olhs_Lforce(AstNodeUniop* nodep, AstNUser* vup) {
    // Widths: out width = lhs width
    // It always comes exactly from LHS; ignores any upper operand
    if (nodep->op2p()) nodep->v3fatalSrc("For unary ops only!");
    if (vup->c()->prelim()) {
	nodep->lhsp()->iterateAndNext(*this,WidthVP(ANYSIZE,0,PRELIM).p());
    }
    int width  = nodep->lhsp()->width();
    int ewidth = nodep->lhsp()->width();  // Not minWidth; force it.
    nodep->width(width,ewidth);
    if (vup->c()->final()) {
	// Final call, so make sure children check their sizes
	nodep->lhsp()->iterateAndNext(*this,WidthVP(width,ewidth,FINAL).p());
	widthCheck(nodep,"LHS",nodep->lhsp(),width,ewidth);
    }
}

void WidthVisitor::width_Olhs_L_R32(AstNode* nodep, AstNUser* vup)  {
    // Widths: Output width from lhs, rhs<33 bits
    if (!nodep->op2p()) nodep->v3fatalSrc("For binary ops only!");
    if (vup->c()->prelim()) {
	nodep->op1p()->iterateAndNext(*this,WidthVP(ANYSIZE,0,PRELIM).p());
	nodep->op2p()->iterateAndNext(*this,WidthVP(ANYSIZE,0,BOTH).p());
    }
    int width  = max(vup->c()->width(),    nodep->op1p()->width());
    int ewidth = max(vup->c()->widthMin(), nodep->op1p()->widthMin());
    nodep->width(width,ewidth);
    if (vup->c()->final()) {
	nodep->op1p()->iterateAndNext(*this,WidthVP(width,ewidth,FINAL).p());
	widthCheck(nodep,"LHS",nodep->op1p(),width,ewidth);
	if (nodep->op2p()->width()>32)
	    nodep->op2p()->v3error("Unsupported: Shifting of by a over 32 bit number isn't supported."
				   <<" (This isn't a shift of 32 bits, but a shift of 2^32, or 4 billion!)\n");
    }
}

void WidthVisitor::width_Omax_L_Rlhs(AstNode* nodep, AstNUser* vup) {
    // Widths: out width = lhs width = rhs width
    if (!nodep->op2p()) nodep->v3fatalSrc("For binary ops only!");
    // If errors are off, we need to follow the spec; thus we really need to do the max()
    // because the rhs could be larger, and we need to have proper editing to get the widths
    // to be the same for our operations.
    if (vup->c()->prelim()) {  // First stage evaluation
	// Determine expression widths only relying on what's in the subops
	nodep->op1p()->iterateAndNext(*this,WidthVP(ANYSIZE,0,PRELIM).p());
	nodep->op2p()->iterateAndNext(*this,WidthVP(ANYSIZE,0,PRELIM).p());
    }
    int width  = max(vup->c()->width(),    max(nodep->op1p()->width(),    nodep->op2p()->width()));
    int mwidth = max(vup->c()->widthMin(), max(nodep->op1p()->widthMin(), nodep->op2p()->widthMin()));
    nodep->width(width,mwidth);
    if (vup->c()->final()) {
	// Final call, so make sure children check their sizes
	nodep->op1p()->iterateAndNext(*this,WidthVP(width,mwidth,FINAL).p());
	nodep->op2p()->iterateAndNext(*this,WidthVP(width,mwidth,FINAL).p());
	// Some warning suppressions
	bool lhsOk=false; bool rhsOk = false;
	if (nodep->castAdd() || nodep->castSub()) {
	    lhsOk = (mwidth == (nodep->op1p()->widthMin()+1));	// Ok if user wants extra bit from carry
	    rhsOk = (mwidth == (nodep->op2p()->widthMin()+1));	// Ok if user wants extra bit from carry
	} else if (nodep->castMul() || nodep->castMulS()) {
	    lhsOk = (mwidth >= (nodep->op1p()->widthMin()));
	    rhsOk = (mwidth >= (nodep->op2p()->widthMin()));
	}
	// Error report and change sizes for suboperands of this node.
	widthCheck(nodep,"LHS",nodep->op1p(),width,mwidth,lhsOk);
	widthCheck(nodep,"RHS",nodep->op2p(),width,mwidth,rhsOk);
    }
}

//######################################################################

class WidthCommitVisitor : public AstNVisitor {
    // Now that all widthing is complete,
    // Copy all width() to widthMin().  V3Const expects this
private:
    // VISITORS
    virtual void visit(AstNode* nodep, AstNUser*) {
	nodep->width(nodep->width(),nodep->width());
	nodep->iterateChildren(*this);
    }
public:
    // CONSTUCTORS
    WidthCommitVisitor(AstNode* nodep) {
	nodep->iterateAndNext(*this, NULL);
    }
    virtual ~WidthCommitVisitor() {}
};

//######################################################################
// Width class functions

void V3Width::width(AstNetlist* nodep) {
    UINFO(2,__FUNCTION__<<": "<<endl);
    // We should do it in bottom-up module order, but it works in any order.
    WidthVisitor visitor (nodep, false);
}

void V3Width::widthParams(AstNode* nodep) {
    UINFO(4,__FUNCTION__<<": "<<endl);
    // We should do it in bottom-up module order, but it works in any order.
    WidthVisitor visitor (nodep, true);
}

void V3Width::widthSignedIfNotAlready(AstNode* nodep) {
    if (!nodep->width()) {
	V3Width::widthParams(nodep);
	V3Signed::signedParams(nodep);
    }
}

void V3Width::widthCommit(AstNode* nodep) {
    UINFO(2,__FUNCTION__<<": "<<endl);
    WidthCommitVisitor visitor (nodep);
}

