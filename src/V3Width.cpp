//*************************************************************************
// DESCRIPTION: Verilator: Expression width calculations
//
// Code available from: http://www.veripool.org/verilator
//
// AUTHORS: Wilson Snyder with Paul Wasson, Duane Gabli
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
// Signedness depends on:
//	Decimal numbers are signed
//	Based numbers are unsigned unless 's' prefix
//	Comparison results are unsigned
//	Bit&Part selects are unsigned, even if whole
//	Concatenates are unsigned
//	Ignore signedness of self-determined:
//		shift rhs, ** rhs, x?: lhs, concat and replicate members
//	Else, if any operand unsigned, output unsigned
//
// Real number rules:
//	Real numbers are real (duh)
//	Reals convert to integers by rounding
//	Reals init to 0.0
//	Logicals convert compared to zero
//	If any operand is real, result is real
//*************************************************************************

#include "config_build.h"
#include "verilatedos.h"
#include <cstdio>
#include <cstdarg>
#include <unistd.h>

#include "V3Global.h"
#include "V3Width.h"
#include "V3Number.h"
#include "V3Const.h"
#include "V3Task.h"

// More code; this file was getting too large; see actions there
#define _V3WIDTH_CPP_
#include "V3WidthCommit.h"

//######################################################################
// Width state, as a visitor of each AstNode

enum Stage { PRELIM=1,FINAL=2,BOTH=3 };

class WidthVP : public AstNUser {
    // Parameters to pass down hierarchy with visit functions.
    int	m_width;	// Expression width, for (2+2), it's 32 bits
    int	m_widthMin;	// Minimum width, for (2+2), it's 2 bits, for 32'2+32'2 it's 32 bits
    Stage m_stage;	// If true, report errors
public:
    WidthVP(int width, int widthMin, Stage stage) : m_width(width), m_widthMin(widthMin), m_stage(stage) {}
    int width() const { return m_width; }
    int widthMin() const { return m_widthMin?m_widthMin:m_width; }
    bool prelim() const { return m_stage&1; }
    bool final() const { return m_stage&2; }
    char stageAscii() const { return "-PFB"[m_stage]; }
};
ostream& operator<<(ostream& str, const WidthVP* vup) {
    str<<"  VUP(w="<<vup->width()<<",wm="<<vup->widthMin()<<",s="<<vup->stageAscii()<<")";
    return str;
}

//######################################################################

class WidthVisitor : public AstNVisitor {
private:
    // STATE
    bool	m_paramsOnly;	// Computing parameter value; limit operation
    AstRange*	m_cellRangep;	// Range for arrayed instantiations, NULL for normal instantiations
    AstNodeCase* m_casep;	// Current case statement CaseItem is under
    AstFunc*	m_funcp;	// Current function

    // CLASSES
#define ANYSIZE 0

    // METHODS
    static int debug() {
	static int level = -1;
	if (VL_UNLIKELY(level < 0)) level = v3Global.opt.debugSrcLevel(__FILE__);
	return level;
    }

    // VISITORS
    //   Naming:  width_O{outputtype}_L{lhstype}_R{rhstype}_W{widthing}_S{signing}
    //		Where type:
    //			_O1=boolean (width 1 unsigned)
    //			_Ou=unsigned
    //			_Os=signed
    //			_Ous=unsigned or signed
    //			_Or=real
    //			_Ox=anything
    //		Where _Wlhs = Width comes from LHS
    //		Where _Wleqrhs = Width matches LHS and RHS
    //		Where _Slandrhs  = Signed if LHS and RHS

    // Widths: 1 bit out, lhs 1 bit; Real: converts via compare with 0
    virtual void visit(AstLogNot* nodep, AstNUser* vup) {	visit_log_O1_L1rus(nodep,vup); }
    virtual void visit(AstPslBool* nodep, AstNUser* vup) {	visit_log_O1_L1rus(nodep,vup); }
    // Widths: 1 bit out, lhs 1 bit, rhs 1 bit; Real: converts via compare with 0
    virtual void visit(AstLogAnd* nodep, AstNUser* vup) {	visit_log_O1_LR1rus(nodep,vup); }
    virtual void visit(AstLogOr* nodep, AstNUser* vup) {	visit_log_O1_LR1rus(nodep,vup); }
    virtual void visit(AstLogIf* nodep, AstNUser* vup) {	visit_log_O1_LR1rus(nodep,vup); }  // Conversion from real not in IEEE, but a fallout
    virtual void visit(AstLogIff* nodep, AstNUser* vup) {	visit_log_O1_LR1rus(nodep,vup); }  // Conversion from real not in IEEE, but a fallout

    // Widths: 1 bit out, Any width lhs
    virtual void visit(AstRedAnd* nodep, AstNUser* vup) {	visit_red_O1_Lrus(nodep,vup,false); }
    virtual void visit(AstRedOr* nodep, AstNUser* vup) {	visit_red_O1_Lrus(nodep,vup,false); }
    virtual void visit(AstRedXnor* nodep, AstNUser* vup){	visit_red_O1_Lrus(nodep,vup,false); }
    virtual void visit(AstRedXor* nodep,AstNUser* vup) {	visit_red_O1_Lrus(nodep,vup,false); }
    virtual void visit(AstIsUnknown* nodep,AstNUser* vup) {	visit_red_O1_Lrus(nodep,vup,true); }  // Allow real
    virtual void visit(AstOneHot* nodep,AstNUser* vup) {	visit_red_O1_Lrus(nodep,vup,false); }
    virtual void visit(AstOneHot0* nodep,AstNUser* vup) {	visit_red_O1_Lrus(nodep,vup,false); }

    // These have different node types, as they operate differently
    // Must add to case statement below,
    // Widths: 1 bit out, lhs width == rhs width.  real if lhs|rhs real
    virtual void visit(AstEq* nodep, AstNUser* vup) {		visit_cmp_O1_DSreplace(nodep,vup); }
    virtual void visit(AstNeq* nodep, AstNUser* vup) {		visit_cmp_O1_DSreplace(nodep,vup); }
    virtual void visit(AstGt* nodep, AstNUser* vup) {		visit_cmp_O1_DSreplace(nodep,vup); }
    virtual void visit(AstGte* nodep, AstNUser* vup) {		visit_cmp_O1_DSreplace(nodep,vup); }
    virtual void visit(AstLt* nodep, AstNUser* vup) {		visit_cmp_O1_DSreplace(nodep,vup); }
    virtual void visit(AstLte* nodep, AstNUser* vup) {		visit_cmp_O1_DSreplace(nodep,vup); }
    virtual void visit(AstGtS* nodep, AstNUser* vup) {		visit_cmp_O1_DSreplace(nodep,vup); }
    virtual void visit(AstGteS* nodep, AstNUser* vup) {		visit_cmp_O1_DSreplace(nodep,vup); }
    virtual void visit(AstLtS* nodep, AstNUser* vup) {		visit_cmp_O1_DSreplace(nodep,vup); }
    virtual void visit(AstLteS* nodep, AstNUser* vup) {		visit_cmp_O1_DSreplace(nodep,vup); }
    // ...    These comparisons don't care about inbound types
    // ...    (Though they should match.  We don't check.)
    virtual void visit(AstEqCase* nodep, AstNUser* vup) {	visit_cmp_O1_LRrus(nodep,vup,false); }
    virtual void visit(AstEqWild* nodep, AstNUser* vup) {	visit_cmp_O1_LRrus(nodep,vup,false); }
    virtual void visit(AstNeqCase* nodep, AstNUser* vup) {	visit_cmp_O1_LRrus(nodep,vup,false); }
    virtual void visit(AstNeqWild* nodep, AstNUser* vup) {	visit_cmp_O1_LRrus(nodep,vup,false); }
    // ...    Real compares
    virtual void visit(AstEqD* nodep, AstNUser* vup) {		visit_cmp_O1_LRrus(nodep,vup,true); }
    virtual void visit(AstNeqD* nodep, AstNUser* vup) {		visit_cmp_O1_LRrus(nodep,vup,true); }
    virtual void visit(AstLtD* nodep, AstNUser* vup) {		visit_cmp_O1_LRrus(nodep,vup,true); }
    virtual void visit(AstLteD* nodep, AstNUser* vup) {		visit_cmp_O1_LRrus(nodep,vup,true); }
    virtual void visit(AstGtD* nodep, AstNUser* vup) {		visit_cmp_O1_LRrus(nodep,vup,true); }
    virtual void visit(AstGteD* nodep, AstNUser* vup) {		visit_cmp_O1_LRrus(nodep,vup,true); }

    // Widths: out width = lhs width = rhs width
    // Signed: Output signed iff LHS & RHS signed.
    // Real: Not allowed
    virtual void visit(AstAnd* nodep, AstNUser* vup) {		visit_boolmath_Ous_LRus(nodep,vup); }
    virtual void visit(AstOr* nodep, AstNUser* vup) {		visit_boolmath_Ous_LRus(nodep,vup); }
    virtual void visit(AstXnor* nodep, AstNUser* vup) {		visit_boolmath_Ous_LRus(nodep,vup); }
    virtual void visit(AstXor* nodep, AstNUser* vup) {		visit_boolmath_Ous_LRus(nodep,vup); }
    virtual void visit(AstBufIf1* nodep, AstNUser* vup) {	visit_boolmath_Ous_LRus(nodep,vup); }  // Signed behavior changing in 3.814
    // Width: Max(Lhs,Rhs) sort of.
    // Real: If either side real
    // Signed: If both sides real
    virtual void visit(AstAdd* nodep, AstNUser* vup) {		visit_math_Orus_DSreplace(nodep,vup,true); }
    virtual void visit(AstSub* nodep, AstNUser* vup) {		visit_math_Orus_DSreplace(nodep,vup,true); }
    virtual void visit(AstDiv* nodep, AstNUser* vup) {		visit_math_Orus_DSreplace(nodep,vup,true); }
    virtual void visit(AstMul* nodep, AstNUser* vup) {		visit_math_Orus_DSreplace(nodep,vup,true); }
    // These can't promote to real
    virtual void visit(AstModDiv* nodep, AstNUser* vup) {	visit_math_Orus_DSreplace(nodep,vup,false); }
    virtual void visit(AstModDivS* nodep, AstNUser* vup) {	visit_math_Orus_DSreplace(nodep,vup,false); }
    virtual void visit(AstMulS* nodep, AstNUser* vup) {		visit_math_Orus_DSreplace(nodep,vup,false); }
    virtual void visit(AstDivS* nodep, AstNUser* vup) {		visit_math_Orus_DSreplace(nodep,vup,false); }
    // Widths: out width = lhs width, but upper matters
    // Signed: Output signed iff LHS signed; unary operator
    // Unary promote to real
    virtual void visit(AstNegate* nodep, AstNUser* vup) {	visit_math_Orus_Dreplace(nodep,vup,true); }
    // Unary never real
    virtual void visit(AstNot* nodep, AstNUser* vup) {		visit_math_Orus_Dreplace(nodep,vup,false); }

    // Real: inputs and output real
    virtual void visit(AstAddD* nodep, AstNUser* vup) {		visit_math_Or_LRr(nodep,vup); }
    virtual void visit(AstSubD* nodep, AstNUser* vup) {		visit_math_Or_LRr(nodep,vup); }
    virtual void visit(AstDivD* nodep, AstNUser* vup) {		visit_math_Or_LRr(nodep,vup); }
    virtual void visit(AstMulD* nodep, AstNUser* vup) {		visit_math_Or_LRr(nodep,vup); }
    virtual void visit(AstPowD* nodep, AstNUser* vup) {		visit_math_Or_LRr(nodep,vup); }
    // Signed/Real: Output real or signed iff LHS signed/real
    virtual void visit(AstNegateD* nodep, AstNUser* vup) {	visit_math_Or_Lr(nodep,vup); }
    // Real: Output real
    virtual void visit(AstCeilD* nodep, AstNUser* vup) {	visit_math_Or_Lr(nodep,vup); }
    virtual void visit(AstExpD* nodep, AstNUser* vup) {		visit_math_Or_Lr(nodep,vup); }
    virtual void visit(AstFloorD* nodep, AstNUser* vup) {	visit_math_Or_Lr(nodep,vup); }
    virtual void visit(AstLogD* nodep, AstNUser* vup) {		visit_math_Or_Lr(nodep,vup); }
    virtual void visit(AstLog10D* nodep, AstNUser* vup) {	visit_math_Or_Lr(nodep,vup); }
    virtual void visit(AstSqrtD* nodep, AstNUser* vup) {	visit_math_Or_Lr(nodep,vup); }

    // Widths: out signed/unsigned width = lhs width, input un|signed
    virtual void visit(AstSigned* nodep, AstNUser* vup) {	visit_Ous_Lus_Wforce(nodep,vup,AstNumeric::SIGNED); }
    virtual void visit(AstUnsigned* nodep, AstNUser* vup) {	visit_Ous_Lus_Wforce(nodep,vup,AstNumeric::UNSIGNED); }

    // Widths: Output width from lhs, rhs<33 bits
    // Signed: If lhs signed
    virtual void visit(AstShiftL* nodep, AstNUser* vup) {	visit_shift_Ous_Lus_Rus32(nodep,vup); }
    virtual void visit(AstShiftR* nodep, AstNUser* vup) {	visit_shift_Ous_Lus_Rus32(nodep,vup); }
    // ShiftRS converts to ShiftR, but not vice-versa
    virtual void visit(AstShiftRS* nodep, AstNUser* vup) {	visit_shift_Ous_Lus_Rus32(nodep,vup); }

    //========
    // Widths: Output real, input integer signed
    virtual void visit(AstBitsToRealD* nodep, AstNUser* vup) {	visit_Or_Lu64(nodep,vup); }
    virtual void visit(AstIToRD* nodep, AstNUser* vup) {	visit_Or_Ls32(nodep,vup); }

    // Widths: Output integer signed, input real
    virtual void visit(AstRToIS* nodep, AstNUser* vup) {	visit_Os32_Lr(nodep,vup); }
    virtual void visit(AstRToIRoundS* nodep, AstNUser* vup) {	visit_Os32_Lr(nodep,vup); }

    // Widths: Output integer unsigned, input real
    virtual void visit(AstRealToBits* nodep, AstNUser* vup) {	visit_Ou64_Lr(nodep,vup); }

    // Widths: Constant, terminal
    virtual void visit(AstTime* nodep, AstNUser*) {		nodep->dtypeChgUInt64(); }
    virtual void visit(AstTimeD* nodep, AstNUser*) {		nodep->dtypeChgDouble(); }
    virtual void visit(AstTestPlusArgs* nodep, AstNUser*) {	nodep->dtypeChgSigned32(); }
    virtual void visit(AstScopeName* nodep, AstNUser*) {	nodep->dtypeChgUInt64(); }	// A pointer, but not that it matters

    // Special cases.  So many....
    virtual void visit(AstNodeCond* nodep, AstNUser* vup) {
	// op=cond?expr1:expr2 is a Good large example of the propagation mess
	// Signed: Output signed iff RHS & THS signed
	// Real: Output real if either expression is real, signed if both signed
	if (vup->c()->prelim()) {  // First stage evaluation
	    // Just once, do the conditional, expect one bit out.
	    nodep->condp()->iterateAndNext(*this,WidthVP(1,1,BOTH).p());
	    spliceCvtCmpD0(nodep->condp()); // auto-compares with zero
	    // Determine sub expression widths only relying on what's in the subops
	    nodep->expr1p()->iterateAndNext(*this,WidthVP(ANYSIZE,0,PRELIM).p());
	    nodep->expr2p()->iterateAndNext(*this,WidthVP(ANYSIZE,0,PRELIM).p());
	}
	// Calculate width of this expression.
	// First call (prelim()) vup->c()->width() is probably zero, so we'll return
	//  the size of this subexpression only.
	// Second call (final()) vup->c()->width() is probably the expression size, so
	//  the expression includes the size of the output too.
	if (nodep->expr1p()->isDouble() || nodep->expr2p()->isDouble()) {
	    spliceCvtD(nodep->expr1p());
	    spliceCvtD(nodep->expr2p());
	    nodep->dtypeChgDouble();
	} else {
	    int width  = max(vup->c()->width(),    max(nodep->expr1p()->width(),    nodep->expr2p()->width()));
	    int mwidth = max(vup->c()->widthMin(), max(nodep->expr1p()->widthMin(), nodep->expr2p()->widthMin()));
	    nodep->isSigned(nodep->expr1p()->isSigned() && nodep->expr2p()->isSigned());
	    nodep->width(width,mwidth);
	}
	if (vup->c()->final()) {
	    // Final width known, so make sure children recompute & check their sizes
	    int width  = nodep->width();
	    int mwidth = nodep->widthMin();
	    nodep->expr1p()->iterateAndNext(*this,WidthVP(width,mwidth,FINAL).p());
	    nodep->expr2p()->iterateAndNext(*this,WidthVP(width,mwidth,FINAL).p());
	    // Error report and change sizes for suboperands of this node.
	    widthCheckReduce(nodep,"Conditional Test",nodep->condp(),1,0);
	    widthCheck(nodep,"Conditional True",nodep->expr1p(),width,mwidth);
	    widthCheck(nodep,"Conditional False",nodep->expr2p(),width,mwidth);
	}
    }
    virtual void visit(AstConcat* nodep, AstNUser* vup) {
	// Real: Not allowed
	// Signed: unsigned output, input either
	if (vup->c()->prelim()) {
	    nodep->lhsp()->iterateAndNext(*this,WidthVP(ANYSIZE,0,BOTH).p());
	    nodep->rhsp()->iterateAndNext(*this,WidthVP(ANYSIZE,0,BOTH).p());
	    checkCvtUS(nodep->lhsp());
	    checkCvtUS(nodep->rhsp());
	    nodep->width(nodep->lhsp()->width() + nodep->rhsp()->width(),
			 nodep->lhsp()->widthMin() + nodep->rhsp()->widthMin());
	    nodep->numeric(AstNumeric::UNSIGNED);
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
	    checkCvtUS(nodep->lhsp());
	    checkCvtUS(nodep->rhsp());
	    V3Const::constifyParamsEdit(nodep->rhsp()); // rhsp may change
	    AstConst* constp = nodep->rhsp()->castConst();
	    if (!constp) { nodep->v3error("Replication value isn't a constant."); return; }
	    uint32_t times = constp->toUInt();
	    if (times==0 && !nodep->backp()->castConcat()) {  // Concat Visitor will clean it up.
		nodep->v3error("Replication value of 0 is only legal under a concatenation."); times=1;
	    }
	    nodep->numeric(AstNumeric::UNSIGNED);
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
	// If there's an edit, then processes the edit'ee (can't just rely on iterateChildren because sometimes we for(...) here ourself
	// Real: Not allowed
	// Signed: unsigned output, input either
	AstNode* selp = V3Width::widthSelNoIterEdit(nodep); if (selp!=nodep) { nodep=NULL; selp->iterate(*this,vup); return; }
	if (vup->c()->prelim()) {
	    nodep->msbp()->iterateAndNext(*this,WidthVP(ANYSIZE,0,BOTH).p());
	    nodep->lsbp()->iterateAndNext(*this,WidthVP(ANYSIZE,0,BOTH).p());
	    checkCvtUS(nodep->msbp());
	    checkCvtUS(nodep->lsbp());
	    int width = nodep->elementsConst();
	    if (width > (1<<28)) nodep->v3error("Width of bit range is huge; vector of over 1billion bits: 0x"<<hex<<width);
	    // Note width() not set on range; use elementsConst()
	    if (nodep->littleEndian()) {
		nodep->v3warn(LITENDIAN,"Little bit endian vector: MSB < LSB of bit range: "<<nodep->lsbConst()<<":"<<nodep->msbConst());
	    }
	}
    }

    virtual void visit(AstSel* nodep, AstNUser* vup) {
	// Signed: always unsigned; Real: Not allowed
	if (vup->c()->prelim()) {
	    if (debug()>=9) nodep->dumpTree(cout,"-selWidth: ");
	    nodep->fromp()->iterateAndNext(*this,WidthVP(ANYSIZE,0,PRELIM).p());
	    nodep->lsbp()->iterateAndNext(*this,WidthVP(ANYSIZE,0,PRELIM).p());
	    nodep->widthp()->iterateAndNext(*this,WidthVP(ANYSIZE,0,BOTH).p());
	    checkCvtUS(nodep->fromp());
	    checkCvtUS(nodep->lsbp());
	    checkCvtUS(nodep->widthp());
	    V3Const::constifyParamsEdit(nodep->widthp()); // widthp may change
	    AstConst* widthConstp = nodep->widthp()->castConst();
	    if (!widthConstp) {
		nodep->v3error("Width of bit extract isn't a constant");
		nodep->dtypeChgLogicBool(); return;
	    }
	    int width = nodep->widthConst();
	    nodep->width(width,width);
	    nodep->numeric(AstNumeric::UNSIGNED);
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
	    if (varrp && varrp->varp()->basicp()->isRanged()) {	// Selecting a bit from a multibit register
		frommsb = varrp->varp()->basicp()->msbMaxSelect();  // Corrected for negative lsb
		fromlsb = varrp->varp()->basicp()->lsb();
	    }
	    int selwidth = V3Number::log2b(frommsb+1-1)+1;	// Width to address a bit
	    nodep->fromp()->iterateAndNext(*this,WidthVP(selwidth,selwidth,FINAL).p());
	    nodep->lsbp()->iterateAndNext(*this,WidthVP(ANYSIZE,0,FINAL).p());
	    if (widthBad(nodep->lsbp(),selwidth,selwidth)
		&& nodep->lsbp()->width()!=32) {
		nodep->v3warn(WIDTH,"Bit extraction of var["<<frommsb<<":"<<fromlsb<<"] requires "
			      <<selwidth<<" bit index, not "
			      <<nodep->lsbp()->width()
			      <<(nodep->lsbp()->width()!=nodep->lsbp()->widthMin()
				 ?" or "+cvtToStr(nodep->lsbp()->widthMin()):"")
			      <<" bits.");
		if (!nodep->fileline()->warnIsOff(V3ErrorCode::WIDTH)) {
		    UINFO(1,"    Related node: "<<nodep<<endl);
		    if (varrp) UINFO(1,"    Related var: "<<varrp->varp()<<endl);
		    if (varrp) UINFO(1,"    Related dtype: "<<varrp->varp()->dtypep()<<endl);
		}
	    }
	    if (nodep->lsbp()->castConst() && nodep->msbConst() > frommsb) {
		// See also warning in V3Const
		// We need to check here, because the widthCheck may silently
		// add another SEL which will lose the out-of-range check
		nodep->v3error("Selection index out of range: "
 			       <<nodep->msbConst()<<":"<<nodep->lsbConst()
			       <<" outside "<<frommsb<<":"<<fromlsb);
		UINFO(1,"    Related node: "<<nodep<<endl);
		if (varrp) UINFO(1,"    Related var: "<<varrp->varp()<<endl);
		if (varrp) UINFO(1,"    Related dtype: "<<varrp->varp()->dtypep()<<endl);
	    }
	    // iterate FINAL is two blocks above
	    widthCheck(nodep,"Extract Range",nodep->lsbp(),selwidth,selwidth,true);
	}
    }

    virtual void visit(AstArraySel* nodep, AstNUser* vup) {
	// Signed/Real: Output signed iff LHS signed/real; binary operator
	// Note by contrast, bit extract selects are unsigned
	if (vup->c()->prelim()) {
	    nodep->bitp()->iterateAndNext(*this,WidthVP(ANYSIZE,0,BOTH).p());
	    checkCvtUS(nodep->bitp());
	    //
	    nodep->fromp()->iterateAndNext(*this,WidthVP(ANYSIZE,0,PRELIM).p());
	    AstNode* basefromp = AstArraySel::baseFromp(nodep->fromp());
	    int dimension      = AstArraySel::dimension(nodep->fromp());
	    AstNodeVarRef* varrp = basefromp->castNodeVarRef();
	    if (!varrp) nodep->v3fatalSrc("No VarRef found under ArraySel(s)");
	    //
	    int frommsb;
	    int fromlsb;
	    AstNodeDType* ddtypep = varrp->varp()->dtypep()->dtypeDimensionp(dimension);
	    if (AstArrayDType* adtypep = ddtypep->castArrayDType()) {
		int outwidth = varrp->width();		// Width of variable
		frommsb = adtypep->msb();
		fromlsb = adtypep->lsb();
		if (fromlsb>frommsb) {int t=frommsb; frommsb=fromlsb; fromlsb=t; }
		// However, if the lsb<0 we may go negative, so need more bits!
		if (fromlsb < 0) frommsb += -fromlsb;
		nodep->numericFrom(adtypep);
		nodep->width(outwidth,outwidth);		// Width out = width of array
	    }
	    else {
		nodep->v3fatalSrc("Array reference exceeds dimension of array");
		frommsb = fromlsb = 0;
	    }
	    int selwidth = V3Number::log2b(frommsb+1-1)+1;	// Width to address a bit
	    nodep->fromp()->iterateAndNext(*this,WidthVP(selwidth,selwidth,FINAL).p());
	    if (widthBad(nodep->bitp(),selwidth,selwidth)
		&& nodep->bitp()->width()!=32) {
		nodep->v3warn(WIDTH,"Bit extraction of array["<<frommsb<<":"<<fromlsb<<"] requires "
			      <<selwidth<<" bit index, not "
			      <<nodep->bitp()->width()
			      <<(nodep->bitp()->width()!=nodep->bitp()->widthMin()
				 ?" or "+cvtToStr(nodep->bitp()->widthMin()):"")
			      <<" bits.");
		if (!nodep->fileline()->warnIsOff(V3ErrorCode::WIDTH)) {
		    UINFO(1,"    Related node: "<<nodep<<endl);
		    if (varrp) UINFO(1,"    Related var: "<<varrp->varp()<<endl);
		    if (varrp) UINFO(1,"    Related depth: "<<dimension<<" dtype: "<<ddtypep<<endl);
		}
	    }
	    widthCheck(nodep,"Extract Range",nodep->bitp(),selwidth,selwidth,true);
	}
    }

    virtual void visit(AstSelBit* nodep, AstNUser* vup) {
	// Just a quick check as after V3Param these nodes instead are AstSel's
	AstNode* selp = V3Width::widthSelNoIterEdit(nodep); if (selp!=nodep) { nodep=NULL; selp->iterate(*this,vup); return; }
	nodep->v3fatalSrc("AstSelBit should disappear after widthSel");
    }
    virtual void visit(AstSelExtract* nodep, AstNUser* vup) {
	// Just a quick check as after V3Param these nodes instead are AstSel's
	AstNode* selp = V3Width::widthSelNoIterEdit(nodep); if (selp!=nodep) { nodep=NULL; selp->iterate(*this,vup); return; }
	nodep->v3fatalSrc("AstSelExtract should disappear after widthSel");
    }

    virtual void visit(AstSelPlus* nodep, AstNUser* vup) {
	AstNode* selp = V3Width::widthSelNoIterEdit(nodep); if (selp!=nodep) { nodep=NULL; selp->iterate(*this,vup); return; }
	nodep->v3fatalSrc("AstSelPlus should disappear after widthSel");
    }
    virtual void visit(AstSelMinus* nodep, AstNUser* vup) {
	AstNode* selp = V3Width::widthSelNoIterEdit(nodep); if (selp!=nodep) { nodep=NULL; selp->iterate(*this,vup); return; }
	nodep->v3fatalSrc("AstSelMinus should disappear after widthSel");
    }

    virtual void visit(AstExtend* nodep, AstNUser* vup) {
	// Only created by this process, so we know width from here down is correct.
    }
    virtual void visit(AstExtendS* nodep, AstNUser* vup) {
	// Only created by this process, so we know width from here down is correct.
    }
    virtual void visit(AstConst* nodep, AstNUser* vup) {
	// The node got setup with the signed/real state of the node.
	// However a later operation may have changed the node->signed w/o changing
	// the number's sign.  So we don't: nodep->isSigned(nodep->num().isSigned());
	if (vup && vup->c()->prelim()) {
	    if (nodep->num().sized()) {
		nodep->width(nodep->num().width(), nodep->num().width());
	    } else {
		nodep->width(nodep->num().width(), nodep->num().widthMin());
	    }
	}
	// We don't size the constant until we commit the widths, as need parameters
	// to remain unsized, and numbers to remain unsized to avoid backp() warnings
    }
    virtual void visit(AstConstString* nodep, AstNUser* vup) {
	nodep->rewidth();
    }
    virtual void visit(AstRand* nodep, AstNUser* vup) {
	if (vup->c()->prelim()) {
	    nodep->dtypeChgSigned32();  // Says the spec
	}
    }
    virtual void visit(AstUCFunc* nodep, AstNUser* vup) {
	nodep->numeric(AstNumeric::UNSIGNED);  // If want otherwise use a dpi import
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
	    checkCvtUS(nodep->lhsp());
	    nodep->dtypeChgSigned32();
	}
    }
    virtual void visit(AstPow* nodep, AstNUser* vup) {
	// Pow is special, output sign only depends on LHS sign
	// Real if either side is real (as with AstAdd)
	shift_prelim(nodep, vup);
	if (nodep->lhsp()->isDouble() || nodep->rhsp()->isDouble()) {
	    spliceCvtD(nodep->lhsp());
	    spliceCvtD(nodep->rhsp());
	    replaceWithDVersion(nodep); nodep=NULL;
	} else {
	    AstNodeBiop* newp = shift_final(nodep, vup);  nodep=NULL;
	    newp->isSigned(newp->lhsp()->isSigned());
	    if (newp->isSigned()) {
		replaceWithUOrSVersion(newp, false);  newp=NULL;
	    }
	}
    }
    virtual void visit(AstPowS* nodep, AstNUser* vup) {
	// Pow is special, output sign only depends on LHS sign
	shift_prelim(nodep, vup);
	AstNodeBiop* newp = shift_final(nodep, vup);  nodep=NULL;
	newp->isSigned(newp->lhsp()->isSigned());
	if (!newp->isSigned()) {
	    replaceWithUOrSVersion(newp, true);  newp=NULL;
	}
    }
    virtual void visit(AstCountOnes* nodep, AstNUser* vup) {
	if (vup->c()->prelim()) {
	    nodep->lhsp()->iterateAndNext(*this,WidthVP(ANYSIZE,0,BOTH).p());
	    checkCvtUS(nodep->lhsp());
	    // If it's a 32 bit number, we need a 6 bit number as we need to return '32'.
	    int selwidth = V3Number::log2b(nodep->lhsp()->width())+1;
	    nodep->numeric(AstNumeric::UNSIGNED);
	    nodep->width(selwidth,selwidth);
	}
    }
    virtual void visit(AstCvtPackString* nodep, AstNUser* vup) {
	// Opaque returns, so arbitrary
	nodep->lhsp()->iterateAndNext(*this,WidthVP(ANYSIZE,0,BOTH).p());
    }
    virtual void visit(AstAttrOf* nodep, AstNUser*) {
	nodep->fromp()->iterateAndNext(*this,WidthVP(ANYSIZE,0,BOTH).p());
	nodep->numeric(AstNumeric::UNSIGNED);
	nodep->width(32,1);	// Approximation, unsized 32
    }
    virtual void visit(AstText* nodep, AstNUser* vup) {
	// Only used in CStmts which don't care....
    }
    virtual void visit(AstArrayDType* nodep, AstNUser* vup) {
	// Lower datatype determines the width
	nodep->dtypep()->iterateAndNext(*this,vup);
	// But also cleanup array size
	nodep->arrayp()->iterateAndNext(*this,WidthVP(ANYSIZE,0,BOTH).p());
	nodep->widthFrom(nodep->dtypep());
	UINFO(4,"dtWidthed "<<nodep<<endl);
    }
    virtual void visit(AstBasicDType* nodep, AstNUser* vup) {
	if (nodep->rangep()) {
	    nodep->rangep()->iterateAndNext(*this,WidthVP(ANYSIZE,0,BOTH).p());
	    nodep->width(nodep->rangep()->elementsConst(), nodep->rangep()->elementsConst());
	}
	// else width in node is correct; it was set based on keyword().width()
	// at construction time.  Ditto signed, so "unsigned byte" etc works right.
	UINFO(4,"dtWidthed "<<nodep<<endl);
    }
    virtual void visit(AstConstDType* nodep, AstNUser* vup) {
	nodep->iterateChildren(*this, vup);
	nodep->widthFrom(nodep->dtypep());
	UINFO(4,"dtWidthed "<<nodep<<endl);
    }
    virtual void visit(AstRefDType* nodep, AstNUser* vup) {
	nodep->iterateChildren(*this, vup);
	if (nodep->defp()) nodep->defp()->iterate(*this,vup);
	nodep->widthSignedFrom(nodep->dtypeSkipRefp());
	UINFO(4,"dtWidthed "<<nodep<<endl);
    }
    virtual void visit(AstTypedef* nodep, AstNUser* vup) {
	nodep->iterateChildren(*this, vup);
	nodep->widthSignedFrom(nodep->dtypep()->skipRefp());
    }
    virtual void visit(AstCast* nodep, AstNUser* vup) {
	//if (debug()) nodep->dumpTree(cout,"  CastPre: ");
	nodep->lhsp()->iterateAndNext(*this,WidthVP(ANYSIZE,0,BOTH).p());
	nodep->dtypep()->iterateAndNext(*this,WidthVP(ANYSIZE,0,BOTH).p());
	// When more general casts are supported, the cast elimination will be done later.
	// For now, replace it ASAP, so widthing can propagate easily
	// The cast may change signing, but we don't know the sign yet.  Make it so.
	// Note we don't sign lhsp() that would make the algorithm O(n^2) if lots of casting.
	V3Width::widthParamsEdit(nodep->dtypep()); // MAY CHANGE dtypep()
	AstBasicDType* basicp = nodep->dtypep()->basicp();  if (!basicp) nodep->v3fatalSrc("Unimplemented: Casting non-simple data type");
	nodep->widthSignedFrom(basicp);
	if (!basicp->isDouble() && !nodep->lhsp()->isDouble()) {
	    // Note widthCheck might modify nodep->lhsp()
	    widthCheck(nodep,"Cast",nodep->lhsp(),nodep->width(),nodep->width(),true);
	}
	AstNode* newp = nodep->lhsp()->unlinkFrBack();
	if (basicp->numeric() == newp->numeric()) {
	    newp = newp; // Can just remove cast
	} else if (basicp->isDouble() && !newp->isDouble()) {
	    newp = new AstIToRD(nodep->fileline(), newp);
	} else if (!basicp->isDouble() && newp->isDouble()) {
	    if (basicp->isSigned()) {
		newp = new AstRToIRoundS(nodep->fileline(), newp);
	    } else {
		newp = new AstUnsigned(nodep->fileline(),
				       new AstRToIS(nodep->fileline(), newp));
	    }
	} else if (basicp->isSigned()) {
	    newp = new AstSigned(nodep->fileline(), newp);
	} else {
	    newp = new AstUnsigned(nodep->fileline(), newp);
	}
	nodep->replaceWith(newp);
	pushDeletep(nodep); nodep=NULL;
	//if (debug()) newp->dumpTree(cout,"  CastOut: ");
    }
    virtual void visit(AstVar* nodep, AstNUser* vup) {
	//if (debug()) nodep->dumpTree(cout,"  InitPre: ");
	// Must have deterministic constant width
	// We can't skip this step when width()!=0, as creating a AstVar
	// with non-constant range gets size 1, not size 0.  So use didWidth().
	if (nodep->didWidth()) return;
	if (nodep->doingWidth()) {  // Early exit if have circular parameter definition
	    if (!nodep->valuep()) nodep->v3fatalSrc("circular, but without value");
	    nodep->v3error("Variable's initial value is circular: "<<nodep->prettyName());
	    pushDeletep(nodep->valuep()->unlinkFrBack());
	    nodep->valuep(new AstConst(nodep->fileline(), AstConst::LogicTrue()));
	    nodep->widthFrom(nodep->valuep());
	    nodep->didWidth(true);
	    return;
	}
	nodep->doingWidth(true);
	// Parameters if implicit untyped inherit from what they are assigned to
	AstBasicDType* bdtypep = nodep->dtypep()->castBasicDType();
	bool implicitParam = nodep->isParam() && bdtypep && bdtypep->implicit();
	if (implicitParam) {
	    int width=0;
	    AstNumeric rs = AstNumeric::UNSIGNED;
	    if (nodep->valuep()) {
		nodep->valuep()->iterateAndNext(*this,WidthVP(width,0,PRELIM).p());
		UINFO(9,"implicitParamPRELIMIV "<<nodep->valuep()<<endl);
		// Although nodep will get a different width for parameters just below,
		// we want the init numbers to retain their width/minwidth until parameters are replaced.
		// This prevents width warnings at the location the parameter is substituted in
		if (nodep->valuep()->isDouble()) {
		    nodep->dtypeChgDouble(); bdtypep=NULL;
		    nodep->dtypep()->dtypeChgDouble(); bdtypep=NULL;
		    nodep->valuep()->iterateAndNext(*this,WidthVP(width,0,FINAL).p());
		} else {
		    nodep->valuep()->iterateAndNext(*this,WidthVP(width,0,FINAL).p());
		    if (bdtypep->nosigned()) rs = nodep->valuep()->numeric();
		    else rs = nodep->numeric();
		    if (nodep->valuep()->widthSized()) {
			width = nodep->valuep()->width();
		    } else {
			if (nodep->valuep()->width()>32) nodep->valuep()->v3warn(WIDTH,"Assigning >32 bit to unranged parameter (defaults to 32 bits)");
			width = 32;
		    }
		}
		UINFO(9,"implicitParamFromIV "<<nodep->valuep()<<endl);
		//UINFO below will print variable nodep
	    } else {
		// Or, if nothing assigned, they're 32 bits.
		width=32;
	    }
	    if (!nodep->isDouble()) {
		AstBasicDType* newp = new AstBasicDType(nodep->fileline(), AstLogicPacked(), width);
		newp->implicit(true);
		newp->numeric(rs);  // SIGNED or UNSIGNED
		bdtypep->replaceWith(newp);
		bdtypep->deleteTree(); bdtypep=NULL;
		nodep->dtypep()->iterateAndNext(*this,WidthVP(ANYSIZE,0,BOTH).p());
	    }
	}
	else { // non param or sized param
	    nodep->dtypep()->iterateAndNext(*this,WidthVP(ANYSIZE,0,BOTH).p());
	    if (nodep->valuep()) {
		nodep->valuep()->iterateAndNext(*this,WidthVP(nodep->dtypep()->width(),0,BOTH).p());
		//if (debug()) nodep->dumpTree(cout,"  final: ");
	    }
	}
	// See above note about valuep()->...FINAL
	nodep->widthSignedFrom(nodep->dtypep());
	if (nodep->valuep()) {
	    if (implicitParam && !nodep->isDouble()) {
		nodep->width(nodep->width(), nodep->valuep()->widthMin());   // Needed as mwidth might not equal width
	    }
	    widthCheck(nodep,"Initial value",nodep->valuep(),
		       nodep->width(),nodep->widthMin());
	}
	UINFO(4,"varWidthed "<<nodep<<endl);
	//if (debug()) nodep->dumpTree(cout,"  InitOut: ");
	nodep->didWidth(true);
	nodep->doingWidth(false);
    }
    virtual void visit(AstNodeVarRef* nodep, AstNUser* vup) {
	if (!nodep->varp()->didWidth()) {
	    // Var hasn't been widthed, so make it so.
	    nodep->varp()->iterate(*this);
	}
	//if (debug()>=9) { nodep->dumpTree(cout,"  VRin  "); nodep->varp()->dumpTree(cout,"   forvar "); }
	// Note genvar's are also entered as integers
	nodep->numericFrom(nodep->varp());
	if (nodep->backp()->castNodeAssign() && nodep->lvalue()) {  // On LHS
	    // Consider Integers on LHS to sized (else may inherit unsized.)
	    nodep->width(nodep->varp()->width(), nodep->varp()->width());
	} else {
	    nodep->widthFrom(nodep->varp());
	}
	//if (debug()>=9) nodep->dumpTree(cout,"  VRout ");
    }

    virtual void visit(AstEnumDType* nodep, AstNUser* vup) {
	UINFO(5,"  ENUMDTYPE "<<nodep<<endl);
	nodep->dtypep()->iterateAndNext(*this,WidthVP(ANYSIZE,0,BOTH).p());
	nodep->widthFrom(nodep->dtypep());
	// Assign widths
	nodep->itemsp()->iterateAndNext(*this,WidthVP(nodep->width(),nodep->widthMin(),BOTH).p());
	// Assign missing values
	V3Number num (nodep->fileline(), nodep->width(), 0);
	V3Number one (nodep->fileline(), nodep->width(), 1);
	map<V3Number,AstEnumItem*> inits;
	for (AstEnumItem* itemp = nodep->itemsp(); itemp; itemp=itemp->nextp()->castEnumItem()) {
	    if (itemp->valuep()) {
		if (debug()>=9) { UINFO(0,"EnumInit "<<itemp<<endl); itemp->valuep()->dumpTree(cout,"-EnumInit: "); }
		V3Const::constifyParamsEdit(itemp->valuep()); // itemp may change
		if (!itemp->valuep()->castConst()) {
		    itemp->valuep()->v3error("Enum value isn't a constant");
		    itemp->valuep()->unlinkFrBack()->deleteTree();
		}
	    }
	    if (!itemp->valuep()) itemp->valuep(new AstConst(itemp->fileline(), num));
	    num.opAssign(itemp->valuep()->castConst()->num());
	    // Look for duplicates
	    if (inits.find(num) != inits.end()) {
		itemp->v3error("Overlapping enumeration value: "<<itemp->prettyName());
		inits.find(num)->second->v3error("... Location of original declaration");
	    } else {
		inits.insert(make_pair(num,itemp));
	    }
	    num.opAdd(one, itemp->valuep()->castConst()->num());
	}
    }
    virtual void visit(AstEnumItem* nodep, AstNUser* vup) {
	UINFO(5,"   ENUMITEM "<<nodep<<endl);
	int width = vup->c()->width();
	int mwidth = vup->c()->widthMin();
	nodep->width(width, mwidth);
	if (nodep->valuep()) {
	    nodep->valuep()->iterateAndNext(*this,WidthVP(width,mwidth,BOTH).p());
	    widthCheck(nodep,"Enum value",nodep->valuep(),width,mwidth);
	}
    }
    virtual void visit(AstEnumItemRef* nodep, AstNUser* vup) {
	if (nodep->itemp()->width()==0) {
	    // We need to do the whole enum en-mass
	    AstNode* enump = nodep->itemp();
	    if (!enump) nodep->v3fatalSrc("EnumItemRef not linked");
	    for (; enump; enump=enump->backp()) {
		if (enump->castEnumDType()) break;
	    }
	    if (!enump) nodep->v3fatalSrc("EnumItemRef can't deref back to an Enum");
	    enump->iterate(*this,vup);
	}
	nodep->widthSignedFrom(nodep->itemp());
    }
    virtual void visit(AstPslClocked* nodep, AstNUser*) {
	nodep->propp()->iterateAndNext(*this,WidthVP(1,1,BOTH).p());
	nodep->sensesp()->iterateAndNext(*this);
	if (nodep->disablep()) {
	    nodep->disablep()->iterateAndNext(*this,WidthVP(1,1,BOTH).p());
	    widthCheckReduce(nodep,"Disable",nodep->disablep(),1,1); // it's like an if() condition.
	}
	widthCheckReduce(nodep,"Property",nodep->propp(),1,1);	// it's like an if() condition.
	nodep->dtypeChgLogicBool();
    }

    //--------------------
    // Top levels

    virtual void visit(AstNodeCase* nodep, AstNUser*) {
	// TOP LEVEL NODE
	AstNodeCase* lastCasep = m_casep;
	m_casep = nodep;
	nodep->exprp()->iterateAndNext(*this,WidthVP(ANYSIZE,0,PRELIM).p());
	for (AstCaseItem* nextip, *itemp = nodep->itemsp(); itemp; itemp=nextip) {
	    nextip = itemp->nextp()->castCaseItem(); // Prelim may cause the node to get replaced
	    if (!m_casep->castGenCase()) itemp->bodysp()->iterateAndNext(*this);
	    for (AstNode* nextcp, *condp = itemp->condsp(); condp; condp=nextcp) {
		nextcp = condp->nextp(); // Prelim may cause the node to get replaced
		condp->iterate(*this,WidthVP(ANYSIZE,0,PRELIM).p()); condp=NULL;
	    }
	}
	// Take width as maximum across all items
	int width = nodep->exprp()->width();
	int mwidth = nodep->exprp()->widthMin();
	for (AstCaseItem* itemp = nodep->itemsp(); itemp; itemp=itemp->nextp()->castCaseItem()) {
	    for (AstNode* condp = itemp->condsp(); condp; condp=condp->nextp()) {
		width = max(width,condp->width());
		mwidth = max(mwidth,condp->widthMin());
	    }
	}
	// Apply width
	nodep->exprp()->iterateAndNext(*this,WidthVP(width,mwidth,FINAL).p());
	for (AstCaseItem* itemp = nodep->itemsp(); itemp; itemp=itemp->nextp()->castCaseItem()) {
	    for (AstNode* condp = itemp->condsp(); condp; condp=condp->nextp()) {
		condp->iterate(*this,WidthVP(width,mwidth,FINAL).p());
		widthCheck(nodep,"Case Item",condp,width,mwidth);
	    }
	}
        widthCheck(nodep,"Case expression",nodep->exprp(),width,mwidth);
	m_casep = lastCasep;
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
	nodep->incsp()->iterateAndNext(*this);
	widthCheckReduce(nodep,"For Test Condition",nodep->condp(),1,1);	// it's like an if() condition.
    }
    virtual void visit(AstNodeIf* nodep, AstNUser*) {
	// TOP LEVEL NODE
	//if (debug()) nodep->dumpTree(cout,"  IfPre: ");
	if (!nodep->castGenIf()) {  // for m_paramsOnly
	    nodep->ifsp()->iterateAndNext(*this);
	    nodep->elsesp()->iterateAndNext(*this);
	}
	nodep->condp()->iterateAndNext(*this,WidthVP(1,1,PRELIM).p());
	spliceCvtCmpD0(nodep->condp());
	nodep->condp()->iterateAndNext(*this,WidthVP(1,1,FINAL).p());
	widthCheckReduce(nodep,"If",nodep->condp(),1,1);	// it's like an if() condition.
	//if (debug()) nodep->dumpTree(cout,"  IfOut: ");
    }
    virtual void visit(AstNodeAssign* nodep, AstNUser*) {
	// TOP LEVEL NODE
	//if (debug()) nodep->dumpTree(cout,"  AssignPre: ");
	nodep->lhsp()->iterateAndNext(*this,WidthVP(ANYSIZE,0,BOTH).p());
	nodep->rhsp()->iterateAndNext(*this,WidthVP(ANYSIZE,0,PRELIM).p());
	if (!nodep->lhsp()->widthSized()) nodep->v3fatalSrc("How can LHS be unsized?");
	if (!nodep->lhsp()->isDouble() && nodep->rhsp()->isDouble()) {
	    spliceCvtS(nodep->rhsp(), false);  // Round RHS
	} else if (nodep->lhsp()->isDouble() && !nodep->rhsp()->isDouble()) {
	    spliceCvtD(nodep->rhsp());
	}
	int awidth = nodep->lhsp()->width();
	if (awidth==0) {
	    awidth = nodep->rhsp()->width();	// Parameters can propagate by unsized assignment
	}
	nodep->rhsp()->iterateAndNext(*this,WidthVP(awidth,awidth,FINAL).p());
	nodep->numericFrom(nodep->lhsp());
	nodep->width(awidth,awidth);  // We know the assign will truncate, so rather
	// than using "width" and have the optimizer truncate the result, we do
	// it using the normal width reduction checks.
	//UINFO(0,"aw "<<awidth<<" w"<<nodep->rhsp()->width()<<" m"<<nodep->rhsp()->widthMin()<<endl);
	widthCheck(nodep,"Assign RHS",nodep->rhsp(),awidth,awidth);
	//if (debug()) nodep->dumpTree(cout,"  AssignOut: ");
    }
    virtual void visit(AstSFormatF* nodep, AstNUser*) {
	// Excludes NodeDisplay, see below
	// TOP LEVEL NODE
	// Just let all arguments seek their natural sizes
	nodep->iterateChildren(*this,WidthVP(ANYSIZE,0,BOTH).p());
	//
	UINFO(9,"  Display in "<<nodep->text()<<endl);
	string dispout = "";
	bool inPct = false;
	AstNode* argp = nodep->exprsp();
	for (const char* inp = nodep->text().c_str(); *inp; inp++) {
	    char ch = *inp;   // Breaks with iterators...
	    if (!inPct && ch=='%') {
		inPct = true;
	    } else if (inPct && isdigit(ch)) {
	    } else if (tolower(inPct)) {
		inPct = false;
		switch (tolower(ch)) {
		case '%': break;  // %% - just output a %
		case 'm': break;  // %m - auto insert "name"
		case 'd': {  // Convert decimal to either 'd' or 'u'
		    if (argp && argp->isSigned()) { // Convert it
			ch = '~';
		    }
		    if (argp) argp=argp->nextp();
		    break;
		}
		default: {  // Most operators, just move to next argument
		    if (argp) argp=argp->nextp();
		    break;
		}
		} // switch
	    }
	    dispout += ch;
	}
	nodep->text(dispout);
	UINFO(9,"  Display out "<<nodep->text()<<endl);
    }
    virtual void visit(AstDisplay* nodep, AstNUser*) {
	if (nodep->filep()) {
	    nodep->filep()->iterateAndNext(*this,WidthVP(32,32,BOTH).p());
	    widthCheck(nodep,"file_descriptor",nodep->filep(),32,32);
	}
	// Just let all arguments seek their natural sizes
	nodep->iterateChildren(*this,WidthVP(ANYSIZE,0,BOTH).p());
    }
    virtual void visit(AstFOpen* nodep, AstNUser*) {
	nodep->filep()->iterateAndNext(*this,WidthVP(32,32,BOTH).p());
	nodep->filenamep()->iterateAndNext(*this,WidthVP(ANYSIZE,0,BOTH).p());
	nodep->modep()->iterateAndNext(*this,WidthVP(ANYSIZE,0,BOTH).p());
	widthCheck(nodep,"file_descriptor",nodep->filep(),32,32);
    }
    virtual void visit(AstFClose* nodep, AstNUser*) {
	nodep->filep()->iterateAndNext(*this,WidthVP(32,32,BOTH).p());
	widthCheck(nodep,"file_descriptor",nodep->filep(),32,32);
    }
    virtual void visit(AstFEof* nodep, AstNUser*) {
	nodep->filep()->iterateAndNext(*this,WidthVP(32,32,BOTH).p());
	nodep->numeric(AstNumeric::UNSIGNED);
	nodep->width(1,1);
	widthCheck(nodep,"file_descriptor",nodep->filep(),32,32);
    }
    virtual void visit(AstFFlush* nodep, AstNUser*) {
	if (nodep->filep()) {
	    nodep->filep()->iterateAndNext(*this,WidthVP(32,32,BOTH).p());
	    widthCheck(nodep,"file_descriptor",nodep->filep(),32,32);
	}
    }
    virtual void visit(AstFGetC* nodep, AstNUser* vup) {
	nodep->filep()->iterateAndNext(*this,WidthVP(32,32,BOTH).p());
	if (vup->c()->prelim()) {
	    nodep->width(32,8);
	}
	widthCheck(nodep,"file_descriptor",nodep->filep(),32,32);
    }
    virtual void visit(AstFGetS* nodep, AstNUser* vup) {
	nodep->filep()->iterateAndNext(*this,WidthVP(32,32,BOTH).p());
	nodep->strgp()->iterateAndNext(*this,WidthVP(ANYSIZE,0,BOTH).p());
	if (vup->c()->prelim()) {
	    nodep->dtypeChgSigned32();  // Spec says integer return
	}
	widthCheck(nodep,"file_descriptor",nodep->filep(),32,32);
    }
    virtual void visit(AstFScanF* nodep, AstNUser* vup) {
	nodep->filep()->iterateAndNext(*this,WidthVP(32,32,BOTH).p());
	nodep->exprsp()->iterateAndNext(*this,WidthVP(ANYSIZE,0,BOTH).p());
	if (vup->c()->prelim()) {
	    nodep->dtypeChgSigned32();  // Spec says integer return
	}
	widthCheck(nodep,"file_descriptor",nodep->filep(),32,32);
    }
    virtual void visit(AstSScanF* nodep, AstNUser* vup) {
	nodep->fromp()->iterateAndNext(*this,WidthVP(ANYSIZE,0,BOTH).p());
	nodep->exprsp()->iterateAndNext(*this,WidthVP(ANYSIZE,0,BOTH).p());
	if (vup->c()->prelim()) {
	    nodep->dtypeChgSigned32();  // Spec says integer return
	}
    }
    virtual void visit(AstSysIgnore* nodep, AstNUser* vup) {
	nodep->exprsp()->iterateAndNext(*this,WidthVP(ANYSIZE,0,BOTH).p());
    }
    virtual void visit(AstSystemF* nodep, AstNUser*) {
	nodep->lhsp()->iterateAndNext(*this,WidthVP(ANYSIZE,0,BOTH).p());
	nodep->dtypeChgSigned32();  // Spec says integer return
    }
    virtual void visit(AstSystemT* nodep, AstNUser*) {
	nodep->lhsp()->iterateAndNext(*this,WidthVP(ANYSIZE,0,BOTH).p());
    }
    virtual void visit(AstReadMem* nodep, AstNUser*) {
	nodep->filenamep()->iterateAndNext(*this,WidthVP(ANYSIZE,0,BOTH).p());
	nodep->memp()->iterateAndNext(*this,WidthVP(ANYSIZE,0,BOTH).p());
	nodep->lsbp()->iterateAndNext(*this,WidthVP(ANYSIZE,0,BOTH).p());
	nodep->msbp()->iterateAndNext(*this,WidthVP(ANYSIZE,0,BOTH).p());
    }
    virtual void visit(AstValuePlusArgs* nodep, AstNUser* vup) {
	nodep->exprsp()->iterateAndNext(*this,WidthVP(ANYSIZE,0,BOTH).p());
	nodep->dtypeChgSigned32();  // Spec says integer return
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
		int numInsts = m_cellRangep->elementsConst();
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
	    }
	    nodep->width(awidth,awidth);
	    nodep->exprp()->iterateAndNext(*this,WidthVP(awidth,awidth,FINAL).p());
	    if (!m_cellRangep) {
		widthCheckPin(nodep, nodep->exprp(), pinwidth, inputPin);
	    }
	}
	//if (debug()) nodep->dumpTree(cout,"-  PinOut: ");
    }
    virtual void visit(AstCell* nodep, AstNUser*) {
	if (!m_paramsOnly) {
	    if (nodep->modp()->castNotFoundModule()) {
		// We've resolved parameters and hit a module that we couldn't resolve.  It's
		// finally time to report it.
		// Note only here in V3Width as this is first visitor after V3Dead.
		nodep->v3error("Cannot find file containing module: "<<nodep->modName());
		v3Global.opt.filePathLookedMsg(nodep->fileline(), nodep->modName());
	    }
	    if (nodep->rangep()) {
		m_cellRangep = nodep->rangep();
		nodep->rangep()->iterateAndNext(*this,WidthVP(ANYSIZE,0,BOTH).p());
	    }
	    nodep->pinsp()->iterateAndNext(*this);
	}
	nodep->paramsp()->iterateAndNext(*this);
	m_cellRangep = NULL;
    }
    virtual void visit(AstNodeFTask* nodep, AstNUser* vup) {
	// Grab width from the output variable (if it's a function)
	if (nodep->didWidth()) return;
	UINFO(5,"  FTASK "<<nodep<<endl);
	if (nodep->doingWidth()) {
	    nodep->v3error("Unsupported: Recursive function or task call");
	    nodep->dtypeChgLogicBool();
	    nodep->didWidth(true);
	    return;
	}
	// Function hasn't been widthed, so make it so.
	nodep->doingWidth(true);  // Would use user1 etc, but V3Width called from too many places to spend a user
	nodep->iterateChildren(*this);
	if (nodep->fvarp()) {
	    m_funcp = nodep->castFunc();
	    if (!m_funcp) nodep->v3fatalSrc("FTask with function variable, but isn't a function");
	    nodep->numericFrom(nodep->fvarp());  // Which will get it from fvarp()->dtypep()
	    nodep->width(nodep->fvarp()->width(), nodep->fvarp()->width());
	}
	nodep->didWidth(true);
	nodep->doingWidth(false);
	m_funcp = NULL;
    }
    virtual void visit(AstReturn* nodep, AstNUser* vup) {
	if (!m_funcp) {
	    if (nodep->lhsp()) {  // Return w/o value ok other places
		nodep->v3error("Return with return value isn't underneath a function");
	    }
	} else {
	    if (nodep->lhsp()) {
		// Function hasn't been widthed, so make it so.
		nodep->iterateChildren(*this,WidthVP(ANYSIZE,0,BOTH).p());
		nodep->widthSignedFrom(m_funcp->fvarp());
	    }
	}
    }
    virtual void visit(AstFuncRef* nodep, AstNUser* vup) {
	visit(nodep->castNodeFTaskRef(), vup);
	nodep->widthSignedFrom(nodep->taskp());
	//if (debug()) nodep->dumpTree(cout,"  FuncOut: ");
    }
    virtual void visit(AstNodeFTaskRef* nodep, AstNUser* vup) {
	// Function hasn't been widthed, so make it so.
	UINFO(5, "  FTASKREF "<<nodep<<endl);
	if (!nodep->taskp()) nodep->v3fatalSrc("Unlinked");
	if (nodep->didWidth()) return;
	nodep->taskp()->iterate(*this);
	//
	// And do the arguments to the task/function too
	for (int accept_mode=0; accept_mode<3; accept_mode++) {  // Avoid duplicate code; just do inner stuff several times
	  reloop:
	    V3TaskConnects tconnects = V3Task::taskConnects(nodep, nodep->taskp()->stmtsp());
	    for (V3TaskConnects::iterator it=tconnects.begin(); it!=tconnects.end(); ++it) {
		AstVar* portp = it->first;
		AstNode* pinp = it->second;
		if (pinp!=NULL) {  // Else argument error we'll find later
		    if (accept_mode==0) {
			// Prelim may cause the node to get replaced; we've lost our
			// pointer, so need to iterate separately later
			if (portp->attrSFormat()
			    && (!pinp->castSFormatF() || pinp->nextp())) {  // Not already done
			    UINFO(4,"   sformat via metacomment: "<<nodep<<endl);
			    AstNRelinker handle;
			    pinp->unlinkFrBackWithNext(&handle);  // Format + additional args, if any
			    AstNode* argsp = NULL;
			    if (pinp->nextp()) argsp = pinp->nextp()->unlinkFrBackWithNext();
			    string format;
			    if (pinp->castConst()) format = pinp->castConst()->num().toString();
			    else pinp->v3error("Format to $display-like function must have constant format string");
			    AstSFormatF* newp = new AstSFormatF(nodep->fileline(), format, false, argsp);
			    if (!newp->scopeNamep() && newp->formatScopeTracking()) {
				newp->scopeNamep(new AstScopeName(newp->fileline()));
			    }
			    handle.relink(newp);
			    // Connection list is now incorrect (has extra args in it).
			    goto reloop;  // so exit early; next loop will correct it
			}
			else if (portp->basicp() && portp->basicp()->keyword()==AstBasicDTypeKwd::STRING
				 && !pinp->castCvtPackString()
				 && !pinp->castSFormatF()  // Already generates a string
				 && !(pinp->castVarRef() && pinp->castVarRef()->varp()->basicp()->keyword()==AstBasicDTypeKwd::STRING)) {
			    UINFO(4,"   Add CvtPackString: "<<pinp<<endl);
			    AstNRelinker handle;
			    pinp->unlinkFrBack(&handle);  // No next, that's the next pin
			    AstNode* newp = new AstCvtPackString(pinp->fileline(), pinp);
			    handle.relink(newp);
			    pinp = newp;
			}
			pinp->accept(*this,WidthVP(portp->width(),portp->widthMin(),PRELIM).p());  pinp=NULL;
		    } else if (accept_mode==1) {
			// Change data types based on above accept completion
			if (portp->isDouble()) {
			    spliceCvtD(pinp); pinp=NULL;
			}
		    } else if (accept_mode==2) {
			// Do PRELIM again, because above accept may have exited early due to node replacement
			pinp->accept(*this,WidthVP(portp->width(),portp->widthMin(),BOTH).p());
			if ((portp->isOutput() || portp->isInout())
			    && pinp->width() != portp->width()) {
			    pinp->v3error("Unsupported: Function output argument '"<<portp->prettyName()<<"'"
					  <<" requires "<<portp->width()
					  <<" bits, but connection's "<<pinp->prettyTypeName()
					  <<" generates "<<pinp->width()<<" bits.");
			    // otherwise would need some mess to force both sides to proper size
			    // (get an ASSIGN with EXTEND on the lhs instead of rhs)
			}
			if (portp->basicp() && !portp->basicp()->isOpaque()) {
			    widthCheck(nodep,"Function Argument",pinp,portp->width(),portp->widthMin());
			}
		    }
		}
	    }
	}
	nodep->didWidth(true);
    }
    virtual void visit(AstNetlist* nodep, AstNUser*) {
	// Iterate modules backwards, in bottom-up order.  That's faster
	nodep->iterateChildrenBackwards(*this);
    }

    //--------------------
    // Default
    virtual void visit(AstNodeMath* nodep, AstNUser*) {
	nodep->v3fatalSrc("Visit function missing? Widthed function missing for math node: "<<nodep);
	nodep->iterateChildren(*this);
    }
    virtual void visit(AstNode* nodep, AstNUser* vup) {
	// Default: Just iterate
	if (vup) nodep->v3fatalSrc("Visit function missing? Widthed expectation for this node: "<<nodep);
	nodep->iterateChildren(*this);
    }

    //----------------------------------------------------------------------
    // WIDTH METHODs -- all iterate

    void visit_Or_Lu64(AstNodeUniop* nodep, AstNUser* vup) {
	// CALLER: AstBitsToRealD
	// Real: Output real
	if (vup->c()->prelim()) {  // First stage evaluation
	    nodep->lhsp()->iterateAndNext(*this,WidthVP(ANYSIZE,0,BOTH).p());
	    checkCvtUS(nodep->lhsp());
	    nodep->dtypeChgDouble();
	    widthCheck(nodep,"LHS",nodep->lhsp(),64,64);
	}
    }
    void visit_Or_Ls32(AstNodeUniop* nodep, AstNUser* vup) {
	// CALLER: AstIToRD
	// Real: Output real
	if (vup->c()->prelim()) {  // First stage evaluation
	    nodep->lhsp()->iterateAndNext(*this,WidthVP(ANYSIZE,0,BOTH).p());
	    checkCvtUS(nodep->lhsp());
	    nodep->dtypeChgDouble();
	    widthCheck(nodep,"LHS",nodep->lhsp(),32,32);
	}
    }
    void visit_Os32_Lr(AstNodeUniop* nodep, AstNUser* vup) {
	// CALLER: RToI
	// Real: LHS real
	if (vup->c()->prelim()) {  // First stage evaluation
	    nodep->lhsp()->iterateAndNext(*this,WidthVP(ANYSIZE,0,BOTH).p());
	    checkCvtD(nodep->lhsp());
	    nodep->dtypeChgSigned32();
	}
    }
    void visit_Ou64_Lr(AstNodeUniop* nodep, AstNUser* vup) {
	// CALLER: RealToBits
	// Real: LHS real
	if (vup->c()->prelim()) {  // First stage evaluation
	    nodep->lhsp()->iterateAndNext(*this,WidthVP(ANYSIZE,0,BOTH).p());
	    checkCvtD(nodep->lhsp());
	    nodep->dtypeChgUInt64();
	}
    }

    void visit_log_O1_L1rus(AstNode* nodep, AstNUser* vup) {
	// CALLER: LogNot, PslBool
	// Note AstPslBool isn't a AstNodeUniop, or we'd only allow that here
	// Widths: 1 bit out, lhs 1 bit
	// Real: Allowed; implicitly compares with zero
	// We calculate the width of the UNDER expression.
	// We then check its width to see if it's legal, and edit if not
	// We finally set the width of our output
	if (nodep->op2p()) nodep->v3fatalSrc("For unary ops only!");
	if (vup->c()->prelim()) {
	    nodep->op1p()->iterateAndNext(*this,WidthVP(1,0,BOTH).p());
	    spliceCvtCmpD0(nodep->op1p());
	}
	nodep->dtypeChgLogicBool();
	if (vup->c()->final()) {
	    widthCheckReduce(nodep,"LHS",nodep->op1p(),1,1);
	}
    }
    void visit_log_O1_LR1rus(AstNodeBiop* nodep, AstNUser* vup) {
	// CALLER: LogAnd, LogOr, LogIf, LogIff
	// Widths: 1 bit out, lhs 1 bit, rhs 1 bit
	if (vup->c()->prelim()) {
	    nodep->lhsp()->iterateAndNext(*this,WidthVP(1,0,BOTH).p());
	    nodep->rhsp()->iterateAndNext(*this,WidthVP(1,0,BOTH).p());
	    spliceCvtCmpD0(nodep->lhsp());
	    spliceCvtCmpD0(nodep->rhsp());
	}
	nodep->dtypeChgLogicBool();
	if (vup->c()->final()) {
	    widthCheckReduce(nodep,"LHS",nodep->lhsp(),1,1);
	    widthCheckReduce(nodep,"RHS",nodep->rhsp(),1,1);
	}
    }

    void visit_red_O1_Lrus(AstNodeUniop* nodep, AstNUser* vup, bool realok) {
	// CALLER: RedAnd, RedOr, ..., IsUnknown
	// Widths: 1 bit out, Any width lhs
	// Signed: Output unsigned, Lhs/Rhs/etc non-real
	if (vup->c()->prelim()) {
	    nodep->lhsp()->iterateAndNext(*this,WidthVP(ANYSIZE,0,BOTH).p());
	}
	if (!realok) checkCvtUS(nodep->lhsp());
	nodep->dtypeChgLogicBool();
    }
    void visit_cmp_O1_DSreplace(AstNodeBiop* nodep, AstNUser* vup) {
	// CALLER: AstEq, AstGt, ..., AstLtS
	// COMPARES
	// Widths: 1 bit out, lhs width == rhs width
	// Signed: if RHS&LHS signed, OPERATOR CHANGES to signed flavor
	// Real: allowed on RHS, if RHS|LHS is real, both become real, and OPERATOR CHANGES
	if (vup->c()->prelim()) {
	    nodep->lhsp()->iterateAndNext(*this,WidthVP(ANYSIZE,0,PRELIM).p());
	    nodep->rhsp()->iterateAndNext(*this,WidthVP(ANYSIZE,0,PRELIM).p());
	}
	if (nodep->lhsp()->isDouble() || nodep->rhsp()->isDouble()) {
	    spliceCvtD(nodep->lhsp());
	    spliceCvtD(nodep->rhsp());
	    if (AstNodeBiop* newp=replaceWithDVersion(nodep)) { nodep=NULL;
		nodep = newp;  // Process new node instead
	    }
	} else {
	    bool signedFl = nodep->lhsp()->isSigned() && nodep->rhsp()->isSigned();
	    if (AstNodeBiop* newp=replaceWithUOrSVersion(nodep, signedFl)) { nodep=NULL;
		nodep = newp;  // Process new node instead
	    }
	}
	int width  = max(nodep->lhsp()->width(),    nodep->rhsp()->width());
	int ewidth = max(nodep->lhsp()->widthMin(), nodep->rhsp()->widthMin());
	nodep->dtypeChgLogicBool();
	if (vup->c()->final()) {
	    nodep->lhsp()->iterateAndNext(*this,WidthVP(width,ewidth,FINAL).p());
	    nodep->rhsp()->iterateAndNext(*this,WidthVP(width,ewidth,FINAL).p());
	    widthCheck(nodep,"LHS",nodep->lhsp(),width,ewidth);
	    widthCheck(nodep,"RHS",nodep->rhsp(),width,ewidth);
	}
    }
    void visit_cmp_O1_LRrus(AstNodeBiop* nodep, AstNUser* vup, bool real_lhs) {
	// CALLER: (real_lhs=true) EqD, LtD
	// CALLER: (real_lhs=false) EqCase, NeqCase
	// Widths: 1 bit out, lhs width == rhs width
	// Signed doesn't matter
	// Real if and only if real_lhs set
	if (!nodep->rhsp()) nodep->v3fatalSrc("For binary ops only!");
	if (vup->c()->prelim()) {
	    nodep->lhsp()->iterateAndNext(*this,WidthVP(ANYSIZE,0,PRELIM).p());
	    nodep->rhsp()->iterateAndNext(*this,WidthVP(ANYSIZE,0,PRELIM).p());
	}
	if (real_lhs) {
	    checkCvtD(nodep->lhsp());
	    checkCvtD(nodep->rhsp());
	} else {
	    checkCvtUS(nodep->lhsp());
	    checkCvtUS(nodep->rhsp());
	}
	int width  = max(nodep->lhsp()->width(),    nodep->rhsp()->width());
	int ewidth = max(nodep->lhsp()->widthMin(), nodep->rhsp()->widthMin());
	nodep->dtypeChgLogicBool();
	if (vup->c()->final()) {
	    nodep->lhsp()->iterateAndNext(*this,WidthVP(width,ewidth,FINAL).p());
	    nodep->rhsp()->iterateAndNext(*this,WidthVP(width,ewidth,FINAL).p());
	    widthCheck(nodep,"LHS",nodep->lhsp(),width,ewidth);
	    widthCheck(nodep,"RHS",nodep->rhsp(),width,ewidth);
	}
    }

    void visit_math_Orus_Dreplace(AstNodeUniop* nodep, AstNUser* vup, bool real_ok) {
	// CALLER: (real_ok=false) Not
	// CALLER: (real_ok=true) Negate
	// Widths: out width = lhs width
	// Signed: From lhs
	// "Interim results shall take the max of operands, including LHS of assignments"
	if (nodep->op2p()) nodep->v3fatalSrc("For unary ops only!");
	if (vup->c()->prelim()) {
	    nodep->lhsp()->iterateAndNext(*this,WidthVP(ANYSIZE,0,PRELIM).p());
	    if (!real_ok) checkCvtUS(nodep->lhsp());
	}
	if (real_ok && nodep->lhsp()->isDouble()) {
	    spliceCvtD(nodep->lhsp());
	    if (AstNodeUniop* newp=replaceWithDVersion(nodep)) { nodep=NULL;
		nodep = newp;  // Process new node instead
	    }
	} else {
	    nodep->isSigned(nodep->lhsp()->isSigned());
	    // Note there aren't yet uniops that need version changes
	    // So no need to call replaceWithUOrSVersion(nodep, nodep->isSigned())
	}
	int width  = max(vup->c()->width(),    nodep->lhsp()->width());
	int ewidth = max(vup->c()->widthMin(), nodep->lhsp()->widthMin());
	nodep->width(width,ewidth);
	nodep->numericFrom(nodep->lhsp());
	if (vup->c()->final()) {
	    nodep->lhsp()->iterateAndNext(*this,WidthVP(width,ewidth,FINAL).p());
	    widthCheck(nodep,"LHS",nodep->lhsp(),width,ewidth);
	}
    }

    void visit_Ous_Lus_Wforce(AstNodeUniop* nodep, AstNUser* vup, AstNumeric rs_out) {
	// CALLER: Signed, Unsigned
	// Widths: out width = lhs width
	// It always comes exactly from LHS; ignores any upper operand
	if (nodep->op2p()) nodep->v3fatalSrc("For unary ops only!");
	if (vup->c()->prelim()) {
	    nodep->lhsp()->iterateAndNext(*this,WidthVP(ANYSIZE,0,PRELIM).p());
	    checkCvtUS(nodep->lhsp());
	}
	int width  = nodep->lhsp()->width();
	int ewidth = nodep->lhsp()->width();  // Not widthMin; force it.
	nodep->width(width,ewidth);
	nodep->numeric(rs_out);
	if (vup->c()->final()) {
	    // Final call, so make sure children check their sizes
	    nodep->lhsp()->iterateAndNext(*this,WidthVP(width,ewidth,FINAL).p());
	    widthCheck(nodep,"LHS",nodep->lhsp(),width,ewidth);
	}
    }

    void visit_shift_Ous_Lus_Rus32(AstNodeBiop* nodep, AstNUser* vup)  {
	// CALLER: ShiftL, ShiftR, ShiftRS
	// Widths: Output width from lhs, rhs<33 bits
	// Signed: Output signed iff LHS signed; unary operator
	shift_prelim(nodep,vup);
	nodep->isSigned(nodep->lhsp()->isSigned());
	AstNodeBiop* newp = shift_final(nodep,vup); nodep=NULL;
	if (newp) {}  // Ununused
    }
    void shift_prelim(AstNodeBiop* nodep, AstNUser* vup)  {
	if (vup->c()->prelim()) {
	    nodep->lhsp()->iterateAndNext(*this,WidthVP(ANYSIZE,0,PRELIM).p());
	    nodep->rhsp()->iterateAndNext(*this,WidthVP(ANYSIZE,0,BOTH).p());
	    checkCvtUS(nodep->lhsp());
	    checkCvtUS(nodep->rhsp());
	}
	int width  = max(vup->c()->width(),    nodep->lhsp()->width());
	int ewidth = max(vup->c()->widthMin(), nodep->lhsp()->widthMin());
	nodep->width(width,ewidth);
    }
    AstNodeBiop* shift_final(AstNodeBiop* nodep, AstNUser* vup)  {
	// Nodep maybe edited
	if (vup->c()->final()) {
	    // ShiftRS converts to ShiftR, but not vice-versa
	    if (nodep->castShiftRS()) {
		if (AstNodeBiop* newp=replaceWithUOrSVersion(nodep, nodep->isSigned())) { nodep=NULL;
		    nodep = newp;  // Process new node instead
		}
	    }
	    int width=nodep->width();  int ewidth=nodep->widthMin();
	    nodep->lhsp()->iterateAndNext(*this,WidthVP(width,ewidth,FINAL).p());
	    widthCheck(nodep,"LHS",nodep->lhsp(),width,ewidth);
	    if (nodep->rhsp()->width()>32)
		nodep->rhsp()->v3error("Unsupported: Shifting of by over 32-bit number isn't supported."
				       <<" (This isn't a shift of 32 bits, but a shift of 2^32, or 4 billion!)\n");
	}
	return nodep;  // May edit
    }

    void visit_boolmath_Ous_LRus(AstNodeBiop* nodep, AstNUser* vup) {
	// CALLER: And, Or, Xor, ...
	// Widths: out width = lhs width = rhs width
	// Signed: if lhs & rhs signed
	if (!nodep->rhsp()) nodep->v3fatalSrc("For binary ops only!");
	// If errors are off, we need to follow the spec; thus we really need to do the max()
	// because the rhs could be larger, and we need to have proper editing to get the widths
	// to be the same for our operations.
	if (vup->c()->prelim()) {  // First stage evaluation
	    // Determine expression widths only relying on what's in the subops
	    nodep->lhsp()->iterateAndNext(*this,WidthVP(ANYSIZE,0,PRELIM).p());
	    nodep->rhsp()->iterateAndNext(*this,WidthVP(ANYSIZE,0,PRELIM).p());
	    checkCvtUS(nodep->lhsp());
	    checkCvtUS(nodep->rhsp());
	}
	int width  = max(vup->c()->width(),    max(nodep->lhsp()->width(),    nodep->rhsp()->width()));
	int mwidth = max(vup->c()->widthMin(), max(nodep->lhsp()->widthMin(), nodep->rhsp()->widthMin()));
	nodep->width(width,mwidth);
	nodep->isSigned(nodep->lhsp()->isSigned() && nodep->rhsp()->isSigned());
	if (vup->c()->final()) {
	    // Final call, so make sure children check their sizes
	    nodep->lhsp()->iterateAndNext(*this,WidthVP(width,mwidth,FINAL).p());
	    nodep->rhsp()->iterateAndNext(*this,WidthVP(width,mwidth,FINAL).p());
	    // Some warning suppressions
	    bool lhsOk=false; bool rhsOk = false;
	    if (nodep->castAdd() || nodep->castSub()) {
		lhsOk = (mwidth == (nodep->lhsp()->widthMin()+1));	// Ok if user wants extra bit from carry
		rhsOk = (mwidth == (nodep->rhsp()->widthMin()+1));	// Ok if user wants extra bit from carry
	    } else if (nodep->castMul() || nodep->castMulS()) {
		lhsOk = (mwidth >= (nodep->lhsp()->widthMin()));
		rhsOk = (mwidth >= (nodep->rhsp()->widthMin()));
	    }
	    // Error report and change sizes for suboperands of this node.
	    widthCheck(nodep,"LHS",nodep->lhsp(),width,mwidth,lhsOk);
	    widthCheck(nodep,"RHS",nodep->rhsp(),width,mwidth,rhsOk);
	}
    }

    void visit_math_Orus_DSreplace(AstNodeBiop* nodep, AstNUser* vup, bool real_ok) {
	// CALLER: (real_ok=false) AddS, SubS, ...
	// CALLER: (real_ok=true) Add, Sub, ...
	// Widths: out width = lhs width = rhs width
	// Signed: Replace operator with signed operator, or signed to unsigned
	// Real: Replace operator with real operator
	//
	// If errors are off, we need to follow the spec; thus we really need to do the max()
	// because the rhs could be larger, and we need to have proper editing to get the widths
	// to be the same for our operations.
	if (vup->c()->prelim()) {  // First stage evaluation
	    // Determine expression widths only relying on what's in the subops
	    nodep->lhsp()->iterateAndNext(*this,WidthVP(ANYSIZE,0,PRELIM).p());
	    nodep->rhsp()->iterateAndNext(*this,WidthVP(ANYSIZE,0,PRELIM).p());
	}
	if (!real_ok) {
	    checkCvtUS(nodep->lhsp());
	    checkCvtUS(nodep->rhsp());
	}
	if (nodep->lhsp()->isDouble() || nodep->rhsp()->isDouble()) {
	    spliceCvtD(nodep->lhsp());
	    spliceCvtD(nodep->rhsp());
	    if (AstNodeBiop* newp=replaceWithDVersion(nodep)) { nodep=NULL;
		nodep = newp;  // Process new node instead
	    }
	} else {
	    nodep->isSigned(nodep->lhsp()->isSigned() && nodep->rhsp()->isSigned());
	    if (AstNodeBiop* newp=replaceWithUOrSVersion(nodep, nodep->isSigned())) { nodep=NULL;
		nodep = newp;  // Process new node instead
	    }
	}
	int width  = max(vup->c()->width(),    max(nodep->lhsp()->width(),    nodep->rhsp()->width()));
	int mwidth = max(vup->c()->widthMin(), max(nodep->lhsp()->widthMin(), nodep->rhsp()->widthMin()));
	nodep->width(width,mwidth);
	if (vup->c()->final()) {
	    // Final call, so make sure children check their sizes
	    nodep->lhsp()->iterateAndNext(*this,WidthVP(width,mwidth,FINAL).p());
	    nodep->rhsp()->iterateAndNext(*this,WidthVP(width,mwidth,FINAL).p());
	    // Some warning suppressions
	    bool lhsOk=false; bool rhsOk = false;
	    if (nodep->castAdd() || nodep->castSub()) {
		lhsOk = (mwidth == (nodep->lhsp()->widthMin()+1));	// Ok if user wants extra bit from carry
		rhsOk = (mwidth == (nodep->rhsp()->widthMin()+1));	// Ok if user wants extra bit from carry
	    } else if (nodep->castMul() || nodep->castMulS()) {
		lhsOk = (mwidth >= (nodep->lhsp()->widthMin()));
		rhsOk = (mwidth >= (nodep->rhsp()->widthMin()));
	    }
	    // Error report and change sizes for suboperands of this node.
	    widthCheck(nodep,"LHS",nodep->lhsp(),width,mwidth,lhsOk);
	    widthCheck(nodep,"RHS",nodep->rhsp(),width,mwidth,rhsOk);
	}
    }
    void visit_math_Or_LRr(AstNodeBiop* nodep, AstNUser* vup) {
	// CALLER: AddD, MulD, ...
	if (vup->c()->prelim()) {  // First stage evaluation
	    nodep->lhsp()->iterateAndNext(*this,WidthVP(ANYSIZE,0,BOTH).p());
	    nodep->rhsp()->iterateAndNext(*this,WidthVP(ANYSIZE,0,BOTH).p());
	    checkCvtD(nodep->lhsp());
	    checkCvtD(nodep->rhsp());
	    nodep->dtypeChgDouble();
	}
    }
    void visit_math_Or_Lr(AstNodeUniop* nodep, AstNUser* vup) {
	// CALLER: Negate, Ceil, Log, ...
	if (vup->c()->prelim()) {  // First stage evaluation
	    nodep->lhsp()->iterateAndNext(*this,WidthVP(ANYSIZE,0,BOTH).p());
	    checkCvtD(nodep->lhsp());
	    nodep->dtypeChgDouble();
	}
    }

    //----------------------------------------------------------------------
    // LOWER LEVEL WIDTH METHODS  (none iterate)

    bool widthBad (AstNode* nodep, int expWidth, int expWidthMin) {
	if (nodep->width()==0) nodep->v3fatalSrc("Under node "<<nodep->prettyTypeName()<<" has no expected width?? Missing Visitor func?");
	if (expWidth==0) nodep->v3fatalSrc("Node "<<nodep->prettyTypeName()<<" has no expected width?? Missing Visitor func?");
	if (expWidthMin==0) expWidthMin = expWidth;
	if (nodep->widthSized()  && nodep->width() != expWidthMin) return true;
	if (!nodep->widthSized() && nodep->widthMin() > expWidthMin) return true;
	return false;
    }

    void fixWidthExtend (AstNode* nodep, int expWidth) {
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
	    num.isSigned(nodep->isSigned());
	    AstNode* newp = new AstConst(nodep->fileline(), num);
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

    void fixWidthReduce (AstNode* nodep, int expWidth) {
	// Fix the width mismatch by adding a reduction OR operator
	// IF (A(CONSTwide)) becomes  IF (A(CONSTreduced))
	// IF (A(somewide))  becomes  IF (A(REDOR(somewide)))
	// Attempt to fix it quietly
	UINFO(4,"  widthReduce_old: "<<nodep<<endl);
	AstConst* constp = nodep->castConst();
	if (constp) {
	    V3Number num (nodep->fileline(), expWidth);
	    num.opRedOr(constp->num());
	    num.isSigned(constp->isSigned());
	    AstNode* newp = new AstConst(nodep->fileline(), num);
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

    bool fixAutoExtend (AstNode*& nodepr, int expWidth) {
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

    void widthCheck (AstNode* nodep, const char* side,
		     AstNode* underp, int expWidth, int expWidthMin,
		     bool ignoreWarn=false) {
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
	if ((nodep->castAdd() && underp->width()==1 && underp->isOne())
	    || (nodep->castSub() && underp->width()==1 && underp->isOne() && 0==strcmp(side,"RHS"))) {
	    // "foo + 1'b1", or "foo - 1'b1" are very common, people assume they extend correctly
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

    void widthCheckReduce (AstNode* nodep, const char* side,
			   AstNode* underp, int expWidth, int expWidthMin,
			   bool ignoreWarn=false) {
	// Before calling this, iterate into underp with FINAL state, so numbers get resized appropriately
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

    void widthCheckPin (AstNode* nodep, AstNode* underp, int expWidth, bool inputPin) {
	// Before calling this, iterate into underp with FINAL state, so numbers get resized appropriately
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

    //----------------------------------------------------------------------
    // SIGNED/DOUBLE METHODS

    void checkCvtUS(AstNode* nodep) {
	if (nodep && nodep->isDouble()) {
	    nodep->v3error("Expected integral (non-real) input to "<<nodep->backp()->prettyTypeName());
	    spliceCvtS(nodep, false); nodep=NULL;
	}
    }
    void checkCvtD(AstNode* nodep) {
	if (nodep && !nodep->isDouble()) {
	    nodep->v3error("Expected real input to "<<nodep->backp()->prettyTypeName());
	    spliceCvtD(nodep); nodep=NULL;
	}
    }
    void spliceCvtCmpD0(AstNode* nodep) {
	// For DOUBLE under a logical op, add implied test against zero
	// Never a warning
	if (nodep && nodep->isDouble()) {
	    UINFO(6,"   spliceCvtCmpD0: "<<nodep<<endl);
	    AstNRelinker linker;
	    nodep->unlinkFrBack(&linker);
	    AstNode* newp = new AstNeqD(nodep->fileline(), nodep,
					new AstConst(nodep->fileline(), AstConst::RealDouble(), 0.0));
	    linker.relink(newp);
	}
    }
    void spliceCvtD(AstNode* nodep) {
	// For integer used in REAL context, convert to real
	// We don't warn here, "2.0 * 2" is common and reasonable
	if (nodep && !nodep->isDouble()) {
	    UINFO(6,"   spliceCvtD: "<<nodep<<endl);
	    AstNRelinker linker;
	    nodep->unlinkFrBack(&linker);
	    AstNode* newp = new AstIToRD(nodep->fileline(), nodep);
	    linker.relink(newp);
	}
    }
    void spliceCvtS(AstNode* nodep, bool ignoreWarn) {
	if (nodep && nodep->isDouble()) {
	    UINFO(6,"   spliceCvtS: "<<nodep<<endl);
	    AstNRelinker linker;
	    nodep->unlinkFrBack(&linker);
	    if (!ignoreWarn) nodep->v3warn(REALCVT,"Implicit conversion of real to integer");
	    AstNode* newp = new AstRToIRoundS(nodep->fileline(), nodep);
	    linker.relink(newp);
	}
    }
    AstNodeBiop* replaceWithUOrSVersion(AstNodeBiop* nodep, bool signedFlavorNeeded) {
	// Given a signed/unsigned node type, create the opposite type
	// Return new node or NULL if nothing
	if (signedFlavorNeeded == nodep->signedFlavor()) {
	    return NULL;
	}
	// To simplify callers, some node types don't need to change
	switch (nodep->type()) {
	case AstType::atEQ:	nodep->isSigned(signedFlavorNeeded); return NULL;
	case AstType::atNEQ:	nodep->isSigned(signedFlavorNeeded); return NULL;
	case AstType::atADD:	nodep->isSigned(signedFlavorNeeded); return NULL;
	case AstType::atSUB:	nodep->isSigned(signedFlavorNeeded); return NULL;
	case AstType::atSHIFTL:	nodep->isSigned(signedFlavorNeeded); return NULL;
	default: break;
	}
	FileLine* fl = nodep->fileline();
	AstNode* lhsp = nodep->lhsp()->unlinkFrBack();
	AstNode* rhsp = nodep->rhsp()->unlinkFrBack();
	AstNodeBiop* newp = NULL;
	switch (nodep->type()) {
	case AstType::atGT:	newp = new AstGtS	(fl,lhsp,rhsp); break;
	case AstType::atGTS:	newp = new AstGt	(fl,lhsp,rhsp); break;
	case AstType::atGTE:	newp = new AstGteS	(fl,lhsp,rhsp); break;
	case AstType::atGTES:	newp = new AstGte	(fl,lhsp,rhsp); break;
	case AstType::atLT:	newp = new AstLtS	(fl,lhsp,rhsp); break;
	case AstType::atLTS:	newp = new AstLt	(fl,lhsp,rhsp); break;
	case AstType::atLTE:	newp = new AstLteS	(fl,lhsp,rhsp); break;
	case AstType::atLTES:	newp = new AstLte	(fl,lhsp,rhsp); break;
	case AstType::atDIV:	newp = new AstDivS	(fl,lhsp,rhsp); break;
	case AstType::atDIVS:	newp = new AstDiv	(fl,lhsp,rhsp); break;
	case AstType::atMODDIV:	newp = new AstModDivS	(fl,lhsp,rhsp); break;
	case AstType::atMODDIVS: newp = new AstModDiv 	(fl,lhsp,rhsp); break;
	case AstType::atMUL:	newp = new AstMulS	(fl,lhsp,rhsp); break;
	case AstType::atMULS:	newp = new AstMul	(fl,lhsp,rhsp); break;
	case AstType::atPOW:	newp = new AstPowS	(fl,lhsp,rhsp); break;
	case AstType::atPOWS:	newp = new AstPow	(fl,lhsp,rhsp); break;
	case AstType::atSHIFTR:	newp = new AstShiftRS	(fl,lhsp,rhsp); break;
	case AstType::atSHIFTRS: newp = new AstShiftR	(fl,lhsp,rhsp); break;
	default:
	    nodep->v3fatalSrc("Node needs sign change, but bad case: "<<nodep<<endl);
	    break;
	}
	UINFO(6,"   ReplaceWithUOrSVersion: "<<nodep<<" w/ "<<newp<<endl);
	nodep->replaceWith(newp);
	newp->widthSignedFrom(nodep);
	pushDeletep(nodep); nodep=NULL;
	return newp;
    }
    AstNodeBiop* replaceWithDVersion(AstNodeBiop* nodep) {
	// Given a signed/unsigned node type, create the opposite type
	// Return new node or NULL if nothing
	if (nodep->doubleFlavor()) {
	    return NULL;
	}
	FileLine* fl = nodep->fileline();
	AstNode* lhsp = nodep->lhsp()->unlinkFrBack();
	AstNode* rhsp = nodep->rhsp()->unlinkFrBack();
	AstNodeBiop* newp = NULL;
	switch (nodep->type()) {
	case AstType::atADD:  				newp = new AstAddD	(fl,lhsp,rhsp); break;
	case AstType::atSUB:  				newp = new AstSubD	(fl,lhsp,rhsp); break;
	case AstType::atEQ:	  			newp = new AstEqD	(fl,lhsp,rhsp); break;
	case AstType::atNEQ:				newp = new AstNeqD	(fl,lhsp,rhsp); break;
	case AstType::atGT:	case AstType::atGTS:	newp = new AstGtD	(fl,lhsp,rhsp); break;
	case AstType::atGTE:	case AstType::atGTES:	newp = new AstGteD	(fl,lhsp,rhsp); break;
	case AstType::atLT:	case AstType::atLTS:	newp = new AstLtD	(fl,lhsp,rhsp); break;
	case AstType::atLTE:	case AstType::atLTES:	newp = new AstLteD	(fl,lhsp,rhsp); break;
	case AstType::atDIV:	case AstType::atDIVS:	newp = new AstDivD	(fl,lhsp,rhsp); break;
	case AstType::atMUL:	case AstType::atMULS:	newp = new AstMulD	(fl,lhsp,rhsp); break;
	default:
	    nodep->v3fatalSrc("Node needs conversion to double, but bad case: "<<nodep<<endl);
	    break;
	}
	UINFO(6,"   ReplaceWithDVersion: "<<nodep<<" w/ "<<newp<<endl);
	nodep->replaceWith(newp);
	newp->widthSignedFrom(nodep);
	pushDeletep(nodep); nodep=NULL;
	return newp;
    }
    AstNodeUniop* replaceWithDVersion(AstNodeUniop* nodep) {
	// Given a signed/unsigned node type, create the opposite type
	// Return new node or NULL if nothing
	if (nodep->doubleFlavor()) {
	    return NULL;
	}
	FileLine* fl = nodep->fileline();
	AstNode* lhsp = nodep->lhsp()->unlinkFrBack();
	AstNodeUniop* newp = NULL;
	switch (nodep->type()) {
	case AstType::atNEGATE:			newp = new AstNegateD	(fl,lhsp); break;
	default:
	    nodep->v3fatalSrc("Node needs conversion to double, but bad case: "<<nodep<<endl);
	    break;
	}
	UINFO(6,"   ReplaceWithDVersion: "<<nodep<<" w/ "<<newp<<endl);
	nodep->replaceWith(newp);
	newp->widthSignedFrom(nodep);
	pushDeletep(nodep); nodep=NULL;
	return newp;
    }

    //----------------------------------------------------------------------
    // METHODS - special type detection
    bool backRequiresUnsigned(AstNode* nodep) {
	// The spec doesn't state this, but if you have an array select where the selection
	// index is NOT wide enough, you do not sign extend, but always zero extend.
	return (nodep->castArraySel() || nodep->castSel());
    }

public:
    // CONSTUCTORS
    WidthVisitor(bool paramsOnly) {
	m_paramsOnly = paramsOnly;
	m_cellRangep = NULL;
	m_casep = NULL;
	m_funcp = NULL;
    }
    AstNode* mainAcceptEdit(AstNode* nodep) {
	return nodep->acceptSubtreeReturnEdits(*this, WidthVP(ANYSIZE,0,BOTH).p());
    }
    virtual ~WidthVisitor() {}
};

//######################################################################
// Width class functions

void V3Width::width(AstNetlist* nodep) {
    UINFO(2,__FUNCTION__<<": "<<endl);
    // We should do it in bottom-up module order, but it works in any order.
    WidthVisitor visitor (false);
    (void)visitor.mainAcceptEdit(nodep);
    WidthRemoveVisitor rvisitor;
    (void)rvisitor.mainAcceptEdit(nodep);
}

AstNode* V3Width::widthParamsEdit(AstNode* nodep) {
    UINFO(4,__FUNCTION__<<": "<<endl);
    // We should do it in bottom-up module order, but it works in any order.
    WidthVisitor visitor (true);
    nodep = visitor.mainAcceptEdit(nodep);
    WidthRemoveVisitor rvisitor;
    nodep = rvisitor.mainAcceptEdit(nodep);
    return nodep;
}

void V3Width::widthCommit(AstNetlist* nodep) {
    UINFO(2,__FUNCTION__<<": "<<endl);
    WidthCommitVisitor visitor (nodep);
}
