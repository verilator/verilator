// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Constant folding
//
// Code available from: http://www.veripool.org/verilator
//
//*************************************************************************
//
// Copyright 2003-2019 by Wilson Snyder.  This program is free software; you can
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
// CONST TRANSFORMATIONS:
//   Call on one node for PARAM values, or netlist for overall constant folding:
//	Bottom up traversal:
//	    Attempt to convert operands to constants
//	    If operands are constant, replace this node with constant.
//*************************************************************************

#include "config_build.h"
#include "verilatedos.h"

#include "V3Global.h"
#include "V3String.h"
#include "V3Const.h"
#include "V3Ast.h"
#include "V3Width.h"
#include "V3Simulate.h"

#include <algorithm>
#include <cstdarg>
#include <map>

//######################################################################
// Utilities

class ConstVarMarkVisitor : public AstNVisitor {
    // NODE STATE
    // AstVar::user4p		-> bool, Var marked, 0=not set yet
private:
    // VISITORS
    virtual void visit(AstVarRef* nodep) {
	if (nodep->varp()) nodep->varp()->user4(1);
    }
    virtual void visit(AstNode* nodep) {
        iterateChildren(nodep);
    }
public:
    // CONSTUCTORS
    explicit ConstVarMarkVisitor(AstNode* nodep) {
	AstNode::user4ClearTree();  // Check marked InUse before we're called
        iterate(nodep);
    }
    virtual ~ConstVarMarkVisitor() {}
};

class ConstVarFindVisitor : public AstNVisitor {
    // NODE STATE
    // AstVar::user4p		-> bool, input from ConstVarMarkVisitor
    // MEMBERS
    bool m_found;
private:
    // VISITORS
    virtual void visit(AstVarRef* nodep) {
	if (nodep->varp() && nodep->varp()->user4()) m_found = true;
    }
    virtual void visit(AstNode* nodep) {
        iterateChildren(nodep);
    }
public:
    // CONSTUCTORS
    explicit ConstVarFindVisitor(AstNode* nodep) {
	m_found = false;
        iterateAndNextNull(nodep);
    }
    virtual ~ConstVarFindVisitor() {}
    // METHODS
    bool found() const { return m_found; }
};

//######################################################################
// Const state, as a visitor of each AstNode

class ConstVisitor : public AstNVisitor {
private:
    // NODE STATE
    // ** only when m_warn/m_doExpensive is set.  If state is needed other times,
    // ** must track down everywhere V3Const is called and make sure no overlaps.
    // AstVar::user4p		-> Used by ConstVarMarkVisitor/ConstVarFindVisitor
    // AstJumpLabel::user4	-> bool.  Set when AstJumpGo uses this label

    // STATE
    bool	m_params;	// If true, propogate parameterized and true numbers only
    bool	m_required;	// If true, must become a constant
    bool	m_wremove;	// Inside scope, no assignw removal
    bool	m_warn;		// Output warnings
    bool	m_doExpensive;	// Enable computationally expensive optimizations
    bool	m_doNConst;	// Enable non-constant-child simplifications
    bool	m_doShort;	// Remove expressions that short circuit
    bool	m_doV;		// Verilog, not C++ conversion
    bool	m_doGenerate;	// Postpone width checking inside generate
    bool        m_hasJumpGo;    // JumpGo under this while
    AstNodeModule*	m_modp;	// Current module
    AstArraySel*	m_selp;	// Current select
    AstNode*	m_scopep;	// Current scope
    AstAttrOf*	m_attrp;	// Current attribute

    // METHODS
    VL_DEBUG_FUNC;  // Declare debug()

    bool operandConst(AstNode* nodep) {
        return VN_IS(nodep, Const);
    }
    bool operandAsvConst(const AstNode* nodep) {
	// BIASV(CONST, BIASV(CONST,...)) -> BIASV( BIASV_CONSTED(a,b), ...)
        const AstNodeBiComAsv* bnodep = VN_CAST_CONST(nodep, NodeBiComAsv);
	if (!bnodep) return false;
        if (!VN_IS(bnodep->lhsp(), Const)) return false;
        const AstNodeBiComAsv* rnodep = VN_CAST_CONST(bnodep->rhsp(), NodeBiComAsv);
	if (!rnodep) return false;
	if (rnodep->type() != bnodep->type()) return false;
	if (rnodep->width() != bnodep->width()) return false;
	if (rnodep->lhsp()->width() != bnodep->lhsp()->width()) return false;
        if (!VN_IS(rnodep->lhsp(), Const)) return false;
	return true;
    }
    bool operandAsvSame(const AstNode* nodep) {
	// BIASV(SAMEa, BIASV(SAMEb,...)) -> BIASV( BIASV(SAMEa,SAMEb), ...)
        const AstNodeBiComAsv* bnodep = VN_CAST_CONST(nodep, NodeBiComAsv);
	if (!bnodep) return false;
        const AstNodeBiComAsv* rnodep = VN_CAST_CONST(bnodep->rhsp(), NodeBiComAsv);
	if (!rnodep) return false;
	if (rnodep->type() != bnodep->type()) return false;
	if (rnodep->width() != bnodep->width()) return false;
	return operandsSame(bnodep->lhsp(), rnodep->lhsp());
    }
    bool operandAsvLUp(const AstNode* nodep) {
        // BIASV(BIASV(CONSTll,lr),r) -> BIASV(CONSTll,BIASV(lr,r)) ?
	//
	// Example of how this is useful:
	// BIASV(BIASV(CONSTa,b...),BIASV(CONSTc,d...))	 // hits operandAsvUp
	// BIASV(CONSTa,BIASV(b...,BIASV(CONSTc,d...)))	 // hits operandAsvUp
	// BIASV(CONSTa,BIASV(CONSTc,BIASV(c...,d...)))  // hits operandAsvConst
	// BIASV(BIASV(CONSTa,CONSTc),BIASV(c...,d...))) // hits normal constant propagation
	// BIASV(CONST_a_c,BIASV(c...,d...)))
	//
	// Idea for the future: All BiComAsvs could be lists, sorted by if they're constant
        const AstNodeBiComAsv* bnodep = VN_CAST_CONST(nodep, NodeBiComAsv);
	if (!bnodep) return false;
        const AstNodeBiComAsv* lnodep = VN_CAST_CONST(bnodep->lhsp(), NodeBiComAsv);
	if (!lnodep) return false;
	if (lnodep->type() != bnodep->type()) return false;
	if (lnodep->width() != bnodep->width()) return false;
        return VN_IS(lnodep->lhsp(), Const);
    }
    bool operandAsvRUp(const AstNode* nodep) {
        // BIASV(l,BIASV(CONSTrl,rr)) -> BIASV(CONSTrl,BIASV(l,rr)) ?
        const AstNodeBiComAsv* bnodep = VN_CAST_CONST(nodep, NodeBiComAsv);
	if (!bnodep) return false;
        const AstNodeBiComAsv* rnodep = VN_CAST_CONST(bnodep->rhsp(), NodeBiComAsv);
	if (!rnodep) return false;
	if (rnodep->type() != bnodep->type()) return false;
	if (rnodep->width() != bnodep->width()) return false;
        return VN_IS(rnodep->lhsp(), Const);
    }
    static bool operandSubAdd(const AstNode* nodep) {
	// SUB( ADD(CONSTx,y), CONSTz) -> ADD(SUB(CONSTx,CONSTz), y)
        const AstNodeBiop* np = VN_CAST_CONST(nodep, NodeBiop);
        const AstNodeBiop* lp = VN_CAST_CONST(np->lhsp(), NodeBiop);
	return (lp
                && VN_IS(lp->lhsp(), Const)
                && VN_IS(np->rhsp(), Const)
		&& lp->width()==np->width());
    }

    static bool operandAndOrSame(const AstNode* nodep) {
	// OR( AND(VAL,x), AND(VAL,y)) -> AND(VAL,OR(x,y))
	// OR( AND(x,VAL), AND(y,VAL)) -> AND(OR(x,y),VAL)
        const AstNodeBiop* np = VN_CAST_CONST(nodep, NodeBiop);
        const AstNodeBiop* lp = VN_CAST_CONST(np->lhsp(), NodeBiop);
        const AstNodeBiop* rp = VN_CAST_CONST(np->rhsp(), NodeBiop);
	return (lp && rp
		&& lp->width()==rp->width()
		&& lp->type()==rp->type()
		&& (operandsSame(lp->lhsp(),rp->lhsp())
		    || operandsSame(lp->rhsp(),rp->rhsp())));
    }
    static bool matchOrAndNot(AstNodeBiop* nodep) {
	// AstOr{$a, AstAnd{AstNot{$b}, $c}} if $a.width1, $a==$b => AstOr{$a,$c}
	// Someday we'll sort the biops completely and this can be simplified
	// This often results from our simplified clock generation:
	// if (rst) ... else if (enable)... -> OR(rst,AND(!rst,enable))
	AstNode* ap;
	AstNodeBiop* andp;
        if (VN_IS(nodep->lhsp(), And)) { andp=VN_CAST(nodep->lhsp(), And); ap=nodep->rhsp(); }
        else if (VN_IS(nodep->rhsp(), And)) { andp=VN_CAST(nodep->rhsp(), And); ap=nodep->lhsp(); }
	else return false;
	AstNodeUniop* notp;
	AstNode* cp;
        if (VN_IS(andp->lhsp(), Not)) { notp=VN_CAST(andp->lhsp(), Not); cp=andp->rhsp(); }
        else if (VN_IS(andp->rhsp(), Not)) { notp=VN_CAST(andp->rhsp(), Not); cp=andp->lhsp(); }
	else return false;
	AstNode* bp = notp->lhsp();
	if (!operandsSame(ap, bp)) return false;
	// Do it
	cp->unlinkFrBack();
	andp->unlinkFrBack()->deleteTree(); VL_DANGLING(andp); VL_DANGLING(notp);
	// Replace whichever branch is now dangling
	if (nodep->rhsp()) nodep->lhsp(cp);
	else nodep->rhsp(cp);
	return true;
    }
    static bool operandShiftSame(const AstNode* nodep) {
        const AstNodeBiop* np = VN_CAST_CONST(nodep, NodeBiop);
	{
            const AstShiftL* lp = VN_CAST_CONST(np->lhsp(), ShiftL);
            const AstShiftL* rp = VN_CAST_CONST(np->rhsp(), ShiftL);
	    if (lp && rp) {
		return (lp->width() == rp->width()
			&& lp->lhsp()->width() == rp->lhsp()->width()
			&& operandsSame(lp->rhsp(), rp->rhsp()));
	    }
	}
	{
            const AstShiftR* lp = VN_CAST_CONST(np->lhsp(), ShiftR);
            const AstShiftR* rp = VN_CAST_CONST(np->rhsp(), ShiftR);
	    if (lp && rp) {
		return (lp->width() == rp->width()
			&& lp->lhsp()->width() == rp->lhsp()->width()
			&& operandsSame(lp->rhsp(), rp->rhsp()));
	    }
	}
	return false;
    }
    bool operandHugeShiftL(const AstNodeBiop* nodep) {
        return (VN_IS(nodep->rhsp(), Const)
                && !VN_CAST_CONST(nodep->rhsp(), Const)->num().isFourState()
                && (VN_CAST_CONST(nodep->rhsp(), Const)->toUInt()
                    >= static_cast<uint32_t>(nodep->width()))
		&& isTPure(nodep->lhsp()));
    }
    bool operandHugeShiftR(const AstNodeBiop* nodep) {
        return (VN_IS(nodep->rhsp(), Const)
                && !VN_CAST_CONST(nodep->rhsp(), Const)->num().isFourState()
                && (VN_CAST_CONST(nodep->rhsp(), Const)->toUInt()
                    >= static_cast<uint32_t>(nodep->lhsp()->width()))
		&& isTPure(nodep->lhsp()));
    }
    bool operandIsTwo(const AstNode* nodep) {
        return (VN_IS(nodep, Const)
                && !VN_CAST_CONST(nodep, Const)->num().isFourState()
		&& nodep->width() <= VL_QUADSIZE
                && VN_CAST_CONST(nodep, Const)->toUQuad()==2);
    }
    bool operandIsTwostate(const AstNode* nodep) {
        return (VN_IS(nodep, Const)
                && !VN_CAST_CONST(nodep, Const)->num().isFourState());
    }
    bool operandIsPowTwo(const AstNode* nodep) {
	if (!operandIsTwostate(nodep)) return false;
        return (1==VN_CAST_CONST(nodep, Const)->num().countOnes());
    }
    bool operandShiftOp(const AstNodeBiop* nodep) {
        if (!VN_IS(nodep->rhsp(), Const)) return false;
        const AstNodeBiop* lhsp = VN_CAST(nodep->lhsp(), NodeBiop);
        if (!lhsp || !(VN_IS(lhsp, And) || VN_IS(lhsp, Or) || VN_IS(lhsp, Xor))) return false;
	if (nodep->width()!=lhsp->width()) return false;
	if (nodep->width()!=lhsp->lhsp()->width()) return false;
	if (nodep->width()!=lhsp->rhsp()->width()) return false;
	return true;
    }
    bool operandShiftShift(const AstNodeBiop* nodep) {
	// We could add a AND though.
        const AstNodeBiop* lhsp = VN_CAST(nodep->lhsp(), NodeBiop);
        if (!lhsp || !(VN_IS(lhsp, ShiftL) || VN_IS(lhsp, ShiftR))) return false;
	// We can only get rid of a<<b>>c or a<<b<<c, with constant b & c
	// because bits may be masked in that process, or (b+c) may exceed the word width.
        if (!(VN_IS(nodep->rhsp(), Const) && VN_IS(lhsp->rhsp(), Const))) return false;
        if (VN_CAST_CONST(nodep->rhsp(), Const)->num().isFourState()
            || VN_CAST_CONST(lhsp->rhsp(), Const)->num().isFourState()) return false;
	if (nodep->width()!=lhsp->width()) return false;
	if (nodep->width()!=lhsp->lhsp()->width()) return false;
	return true;
    }
    bool operandWordOOB(const AstWordSel* nodep) {
	// V3Expand may make a arraysel that exceeds the bounds of the array
	// It was an expression, then got constified.  In reality, the WordSel
	// must be wrapped in a Cond, that will be false.
        return (VN_IS(nodep->rhsp(), Const)
                && VN_IS(nodep->fromp(), NodeVarRef)
                && !VN_CAST_CONST(nodep->fromp(), NodeVarRef)->lvalue()
                && (static_cast<int>(VN_CAST_CONST(nodep->rhsp(), Const)->toUInt())
                    >= VN_CAST(nodep->fromp(), NodeVarRef)->varp()->widthWords()));
    }
    bool operandSelFull(const AstSel* nodep) {
        return (VN_IS(nodep->lsbp(), Const)
                && VN_IS(nodep->widthp(), Const)
		&& nodep->lsbConst()==0
                && static_cast<int>(nodep->widthConst()) == nodep->fromp()->width());
    }
    bool operandSelExtend(AstSel* nodep) {
	// A pattern created by []'s after offsets have been removed
	// SEL(EXTEND(any,width,...),(width-1),0) -> ...
	// Since select's return unsigned, this is always an extend
        AstExtend* extendp = VN_CAST(nodep->fromp(), Extend);
	if (!(m_doV
	      && extendp
              && VN_IS(nodep->lsbp(), Const)
              && VN_IS(nodep->widthp(), Const)
	      && nodep->lsbConst()==0
              && static_cast<int>(nodep->widthConst()) == extendp->lhsp()->width()
		)) return false;
	replaceWChild(nodep, extendp->lhsp()); VL_DANGLING(nodep);
	return true;
    }
    bool operandSelBiLower(AstSel* nodep) {
	// SEL(ADD(a,b),(width-1),0) -> ADD(SEL(a),SEL(b))
	// Add or any operation which doesn't care if we discard top bits
        AstNodeBiop* bip = VN_CAST(nodep->fromp(), NodeBiop);
	if (!(m_doV
	      && bip
              && VN_IS(nodep->lsbp(), Const)
              && VN_IS(nodep->widthp(), Const)
	      && nodep->lsbConst()==0
		)) return false;
	if (debug()>=9) nodep->dumpTree(cout,"SEL(BI)-in:");
	AstNode* bilhsp = bip->lhsp()->unlinkFrBack();
	AstNode* birhsp = bip->rhsp()->unlinkFrBack();
	bip->lhsp(new AstSel(nodep->fileline(), bilhsp, 0, nodep->widthConst()));
	bip->rhsp(new AstSel(nodep->fileline(), birhsp, 0, nodep->widthConst()));
	if (debug()>=9) bip->dumpTree(cout,"SEL(BI)-ou:");
	replaceWChild(nodep, bip); VL_DANGLING(nodep);
	return true;
    }
    bool operandSelShiftLower(AstSel* nodep) {
	// AND({a}, SHIFTR({b}, {c})) is often shorthand in C for Verilog {b}[{c} :+ {a}]
	// becomes thought other optimizations
	// SEL(SHIFTR({a},{b}),{lsb},{width}) -> SEL({a},{lsb+b},{width})
        AstShiftR* shiftp = VN_CAST(nodep->fromp(), ShiftR);
	if (!(m_doV
	      && shiftp
              && VN_IS(shiftp->rhsp(), Const)
              && VN_IS(nodep->lsbp(), Const)
              && VN_IS(nodep->widthp(), Const)
		)) return false;
	AstNode* ap = shiftp->lhsp();
        AstConst* bp = VN_CAST(shiftp->rhsp(), Const);
        AstConst* lp = VN_CAST(nodep->lsbp(), Const);
	if (bp->isWide() || bp->num().isFourState() || bp->num().isNegative()
	    || lp->isWide() || lp->num().isFourState() || lp->num().isNegative()) return false;
	int newLsb = lp->toSInt() + bp->toSInt();
	if (newLsb + nodep->widthConst() > ap->width()) return false;
	//
	UINFO(9, "SEL(SHIFTR(a,b),l,w) -> SEL(a,l+b,w)\n");
	if (debug()>=9) nodep->dumpTree(cout,"SEL(SH)-in:");
	AstSel* newp = new AstSel(nodep->fileline(), ap->unlinkFrBack(), newLsb, nodep->widthConst());
	newp->dtypeFrom(nodep);
	if (debug()>=9) newp->dumpTree(cout,"SEL(SH)-ou:");
	nodep->replaceWith(newp); VL_DANGLING(nodep);
	return true;
    }

    bool operandBiExtendConstShrink(AstNodeBiop* nodep) {
	// Loop unrolling favors standalone compares
	// EQ(const{width32}, EXTEND(xx{width3})) -> EQ(const{3}, xx{3})
	// The constant must have zero bits (+ 1 if signed) or compare
	// would be incorrect. See also operandBiExtendConst
        AstExtend* extendp = VN_CAST(nodep->rhsp(), Extend);
	if (!extendp) return false;
	AstNode* smallerp = extendp->lhsp();
	int subsize = smallerp->width();
        AstConst* constp = VN_CAST(nodep->lhsp(), Const);
	if (!constp) return false;
	if (!constp->num().isBitsZero(constp->width()-1, subsize)) return false;
	//
	if (debug()>=9) nodep->dumpTree(cout,"BI(EXTEND)-in:");
	smallerp->unlinkFrBack();
	extendp->unlinkFrBack()->deleteTree();  // aka nodep->lhsp.
	nodep->rhsp(smallerp);

	constp->unlinkFrBack();
	V3Number num (constp->fileline(), subsize);
	num.opAssign(constp->num());
	nodep->lhsp(new AstConst(constp->fileline(), num));
	constp->deleteTree(); VL_DANGLING(constp);
	if (debug()>=9) nodep->dumpTree(cout,"BI(EXTEND)-ou:");
	return true;
    }
    bool operandBiExtendConstOver(const AstNodeBiop* nodep) {
	// EQ(const{width32}, EXTEND(xx{width3})) -> constant
	// When the constant has non-zero bits above the extend it's a constant.
	// Avoids compiler warning
        const AstExtend* extendp = VN_CAST_CONST(nodep->rhsp(), Extend);
	if (!extendp) return false;
	AstNode* smallerp = extendp->lhsp();
	int subsize = smallerp->width();
        const AstConst* constp = VN_CAST_CONST(nodep->lhsp(), Const);
	if (!constp) return false;
	if (constp->num().isBitsZero(constp->width()-1, subsize)) return false;
	return true;
    }

    AstNode* afterComment(AstNode* nodep) {
	// Ignore comments, such as to determine if a AstIf is empty.
	// nodep may be null, if so return null.
        while (nodep && VN_IS(nodep, Comment)) { nodep = nodep->nextp(); }
	return nodep;
    }

    bool isTPure(AstNode* nodep) {
	// Pure checks - if this node and all nodes under it are free of
	// side effects can do this optimization
	// Eventually we'll recurse through tree when unknown, memoizing results so far,
	// but for now can disable en-mass until V3Purify takes effect.
        return m_doShort || VN_IS(nodep, VarRef) || VN_IS(nodep, Const);
    }

    // Extraction checks
    bool warnSelect(AstSel* nodep) {
	if (m_doGenerate) {
	    // Never checked yet
	    V3Width::widthParamsEdit(nodep);
            iterateChildren(nodep);  // May need "constifying"
	}
	// Find range of dtype we are selecting from
	// Similar code in V3Unknown::AstSel
	bool doit = true;
	if (m_warn
            && VN_IS(nodep->lsbp(), Const)
            && VN_IS(nodep->widthp(), Const)
	    && doit) {
	    int maxDeclBit = nodep->declRange().hiMaxSelect()*nodep->declElWidth() + (nodep->declElWidth()-1);
            if (VN_CAST(nodep->lsbp(), Const)->num().isFourState()
                || VN_CAST(nodep->widthp(), Const)->num().isFourState()) {
		nodep->v3error("Selection index is constantly unknown or tristated: "
			       "lsb="<<nodep->lsbp()->name()<<" width="<<nodep->widthp()->name());
		// Replacing nodep will make a mess above, so we replace the offender
		replaceZero(nodep->lsbp());
	    }
	    else if (nodep->declRange().ranged()
		     && (nodep->msbConst() > maxDeclBit
			 || nodep->lsbConst() > maxDeclBit)) {
		// See also warning in V3Width
		// Must adjust by element width as declRange() is in number of elements
		nodep->v3warn(SELRANGE, "Selection index out of range: "
			      <<(nodep->msbConst()/nodep->declElWidth())
			      <<":"<<(nodep->lsbConst()/nodep->declElWidth())
			      <<" outside "<<nodep->declRange().hiMaxSelect()<<":0"
			      <<(nodep->declRange().lo()>=0 ? ""
				 :(" (adjusted +"+cvtToStr(-nodep->declRange().lo())
				   +" to account for negative lsb)")));
		UINFO(1,"    Related Raw index is "<<nodep->msbConst()<<":"<<nodep->lsbConst()<<endl);
		// Don't replace with zero, we'll do it later
	    }
	}
	return false;  // Not a transform, so NOP
    }

    static bool operandsSame(AstNode* node1p, AstNode* node2p) {
	// For now we just detect constants & simple vars, though it could be more generic
        if (VN_IS(node1p, Const) && VN_IS(node2p, Const)) {
	    return node1p->sameGateTree(node2p);
	}
        else if (VN_IS(node1p, VarRef) && VN_IS(node2p, VarRef)) {
	    // Avoid comparing widthMin's, which results in lost optimization attempts
	    // If cleanup sameGateTree to be smarter, this can be restored.
	    //return node1p->sameGateTree(node2p);
	    return node1p->same(node2p);
	} else {
	    return false;
	}
    }
    bool ifSameAssign(const AstNodeIf* nodep) {
        const AstNodeAssign* ifp = VN_CAST_CONST(nodep->ifsp(), NodeAssign);
        const AstNodeAssign* elsep = VN_CAST_CONST(nodep->elsesp(), NodeAssign);
	if (!ifp   || ifp->nextp()) return false;  // Must be SINGLE statement
	if (!elsep || elsep->nextp()) return false;
	if (ifp->type() != elsep->type()) return false;  // Can't mix an assigndly and an assign
	if (!ifp->lhsp()->sameGateTree(elsep->lhsp())) return false;
	if (!ifp->rhsp()->gateTree()) return false;
	if (!elsep->rhsp()->gateTree()) return false;
	return true;
    }
    bool operandIfIf(const AstNodeIf* nodep) {
	if (nodep->elsesp()) return false;
        const AstNodeIf* lowerIfp = VN_CAST_CONST(nodep->ifsp(), NodeIf);
	if (!lowerIfp || lowerIfp->nextp()) return false;
	if (nodep->type() != lowerIfp->type()) return false;
	if (afterComment(lowerIfp->elsesp())) return false;
	return true;
    }
    bool ifConcatMergeableBiop(const AstNode* nodep) {
        return (VN_IS(nodep, And)
                || VN_IS(nodep, Or)
                || VN_IS(nodep, Xor)
                || VN_IS(nodep, Xnor));
    }
    bool ifAdjacentSel(const AstSel* lhsp, const AstSel* rhsp) {
	if (!v3Global.opt.oAssemble()) return false; // opt disabled
	if (!lhsp || !rhsp) return false;
        const AstNode* lfromp = lhsp->fromp();
        const AstNode* rfromp = rhsp->fromp();
	if (!lfromp || !rfromp || !lfromp->sameGateTree(rfromp)) return false;
        const AstConst* lstart = VN_CAST_CONST(lhsp->lsbp(), Const);
        const AstConst* rstart = VN_CAST_CONST(rhsp->lsbp(), Const);
        const AstConst* lwidth = VN_CAST_CONST(lhsp->widthp(), Const);
        const AstConst* rwidth = VN_CAST_CONST(rhsp->widthp(), Const);
	if (!lstart || !rstart || !lwidth || !rwidth) return false;  // too complicated
	int rend = (rstart->toSInt() + rwidth->toSInt());
        return (rend == lstart->toSInt());
    }
    bool ifMergeAdjacent(AstNode* lhsp, AstNode* rhsp) {
	// called by concatmergeable to determine if {lhsp, rhsp} make sense
	if (!v3Global.opt.oAssemble()) return false; // opt disabled
	// two same varref
	if (operandsSame(lhsp, rhsp)) return true;
        AstSel* lselp = VN_CAST(lhsp, Sel);
        AstSel* rselp = VN_CAST(rhsp, Sel);
	// a[i:0] a
	if (lselp && !rselp && rhsp->sameGateTree(lselp->fromp()))
	    rselp = new AstSel(rhsp->fileline(), rhsp->cloneTree(false), 0, rhsp->width());
	// a[i:j] {a[j-1:k], b}
        if (lselp && !rselp && VN_IS(rhsp, Concat))
            return ifMergeAdjacent(lhsp, VN_CAST(rhsp, Concat)->lhsp());
	// a a[msb:j]
	if (rselp && !lselp && lhsp->sameGateTree(rselp->fromp()))
	    lselp = new AstSel(lhsp->fileline(), lhsp->cloneTree(false), 0, lhsp->width());
	// {b, a[j:k]} a[k-1:i]
        if (rselp && !lselp && VN_IS(lhsp, Concat))
            return ifMergeAdjacent(VN_CAST(lhsp, Concat)->rhsp(), rhsp);
	if (!lselp || !rselp) return false;

	// a[a:b] a[b-1:c] are adjacent
	AstNode* lfromp = lselp->fromp();
	AstNode* rfromp = rselp->fromp();
	if (!lfromp || !rfromp || !lfromp->sameGateTree(rfromp)) return false;
        AstConst* lstart = VN_CAST(lselp->lsbp(), Const);
        AstConst* rstart = VN_CAST(rselp->lsbp(), Const);
        AstConst* lwidth = VN_CAST(lselp->widthp(), Const);
        AstConst* rwidth = VN_CAST(rselp->widthp(), Const);
	if (!lstart || !rstart || !lwidth || !rwidth) return false;  // too complicated
	int rend = (rstart->toSInt() + rwidth->toSInt());
	// a[i:j] a[j-1:k]
	if (rend == lstart->toSInt()) return true;
	// a[i:0] a[msb:j]
	if (rend == rfromp->width() && lstart->toSInt() == 0) return true;
	return false;
    }
    bool concatMergeable(const AstNode* lhsp, const AstNode* rhsp) {
        // determine if {a OP b, c OP d} => {a, c} OP {b, d} is advantagous
	if (!v3Global.opt.oAssemble()) return false; // opt disabled
	if (lhsp->type() != rhsp->type()) return false;
	if (!ifConcatMergeableBiop(lhsp)) return false;

        const AstNodeBiop* lp = VN_CAST_CONST(lhsp, NodeBiop);
        const AstNodeBiop* rp = VN_CAST_CONST(rhsp, NodeBiop);
	if (!lp || !rp) return false;
	// {a[]&b[], a[]&b[]}
	bool lad = ifMergeAdjacent(lp->lhsp(), rp->lhsp());
	bool rad = ifMergeAdjacent(lp->rhsp(), rp->rhsp());
	if (lad && rad) return true;
	// {a[] & b[]&c[], a[] & b[]&c[]}
	else if (lad && concatMergeable(lp->rhsp(), rp->rhsp())) return true;
	// {a[]&b[] & c[], a[]&b[] & c[]}
	else if (rad && concatMergeable(lp->lhsp(), rp->lhsp())) return true;
	else {
	    // {(a[]&b[])&(c[]&d[]), (a[]&b[])&(c[]&d[])}
	    if (concatMergeable(lp->lhsp(), rp->lhsp())
		&& concatMergeable(lp->rhsp(), rp->rhsp()))
		return true;
	}
	return false;
    }

    //----------------------------------------
    // Constant Replacement functions.
    // These all take a node, delete its tree, and replaces it with a constant

    void replaceNum(AstNode* oldp, const V3Number& num) {
	// Replace oldp node with a constant set to specified value
        UASSERT(oldp, "Null old");
        if (VN_IS(oldp, Const) && !VN_CAST(oldp, Const)->num().isFourState()) {
	    oldp->v3fatalSrc("Already constant??");
	}
	AstNode* newp = new AstConst(oldp->fileline(), num);
	newp->dtypeFrom(oldp);
	if (debug()>5) oldp->dumpTree(cout,"  const_old: ");
	if (debug()>5) newp->dumpTree(cout,"       _new: ");
	oldp->replaceWith(newp);
	oldp->deleteTree(); VL_DANGLING(oldp);
    }
    void replaceNum(AstNode* nodep, uint32_t val) {
	V3Number num (nodep->fileline(), nodep->width(), val);
	replaceNum(nodep, num); VL_DANGLING(nodep);
    }
    void replaceNumSigned(AstNodeBiop* nodep, uint32_t val) {
	// We allow both sides to be constant, as one may have come from parameter propagation, etc.
        if (m_warn && !(VN_IS(nodep->lhsp(), Const) && VN_IS(nodep->rhsp(), Const))) {
	    nodep->v3warn(UNSIGNED,"Comparison is constant due to unsigned arithmetic");
	}
	replaceNum(nodep, val); VL_DANGLING(nodep);
    }
    void replaceNumLimited(AstNodeBiop* nodep, uint32_t val) {
	// Avoids gcc warning about same
	if (m_warn) nodep->v3warn(CMPCONST,"Comparison is constant due to limited range");
	replaceNum(nodep, val); VL_DANGLING(nodep);
    }
    void replaceZero(AstNode* nodep) {
	replaceNum(nodep, 0); VL_DANGLING(nodep);
    }
    void replaceZeroChkPure(AstNode* nodep, AstNode* checkp) {
	// For example, "0 * n" -> 0 if n has no side effects
	// Else strength reduce it to 0 & n.
	// If ever change the operation note AstAnd rule specially ignores this created pattern
	if (isTPure(checkp)) {
	    replaceNum(nodep, 0); VL_DANGLING(nodep);
	} else {
	    AstNode* newp = new AstAnd(nodep->fileline(),
				       new AstConst(nodep->fileline(), 0),
				       checkp->unlinkFrBack());
	    newp->dtypeFrom(nodep);
	    nodep->replaceWith(newp);
	    nodep->deleteTree(); VL_DANGLING(nodep);
	}
    }
    void replaceAllOnes(AstNode* nodep) {
	V3Number ones (nodep->fileline(), nodep->width(), 0);
	ones.setMask(nodep->width());
	replaceNum(nodep, ones); VL_DANGLING(nodep);
    }
    void replaceConst(AstNodeUniop* nodep) {
	V3Number num (nodep->fileline(), nodep->width());
        nodep->numberOperate(num, VN_CAST(nodep->lhsp(), Const)->num());
	UINFO(4,"UNICONST -> "<<num<<endl);
	replaceNum(nodep, num); VL_DANGLING(nodep);
    }
    void replaceConst(AstNodeBiop* nodep) {
	V3Number num (nodep->fileline(), nodep->width());
        nodep->numberOperate(num, VN_CAST(nodep->lhsp(), Const)->num(), VN_CAST(nodep->rhsp(), Const)->num());
	UINFO(4,"BICONST -> "<<num<<endl);
	replaceNum(nodep, num); VL_DANGLING(nodep);
    }
    void replaceConst(AstNodeTriop* nodep) {
	V3Number num (nodep->fileline(), nodep->width());
        nodep->numberOperate(num, VN_CAST(nodep->lhsp(), Const)->num(),
                             VN_CAST(nodep->rhsp(), Const)->num(),
                             VN_CAST(nodep->thsp(), Const)->num());
	UINFO(4,"TRICONST -> "<<num<<endl);
	replaceNum(nodep, num); VL_DANGLING(nodep);
    }

    void replaceConstString(AstNode* oldp, const string& num) {
	// Replace oldp node with a constant set to specified value
        UASSERT(oldp, "Null old");
	AstNode* newp = new AstConst(oldp->fileline(), AstConst::String(), num);
	if (debug()>5) oldp->dumpTree(cout,"  const_old: ");
	if (debug()>5) newp->dumpTree(cout,"       _new: ");
	oldp->replaceWith(newp);
	oldp->deleteTree(); VL_DANGLING(oldp);
    }
    //----------------------------------------
    // Replacement functions.
    // These all take a node and replace it with something else

    void replaceWChild(AstNode* nodep, AstNode* childp) {
	// NODE(..., CHILD(...)) -> CHILD(...)
	childp->unlinkFrBackWithNext();
	// If replacing a SEL for example, the data type comes from the parent (is less wide).
	// This may adversly affect the operation of the node being replaced.
	childp->dtypeFrom(nodep);
	nodep->replaceWith(childp);
	nodep->deleteTree(); VL_DANGLING(nodep);
    }

    //! Replace a ternary node with its RHS after iterating
    //! Used with short-circuting, where the RHS has not yet been iterated.
    void replaceWIteratedRhs(AstNodeTriop* nodep) {
        if (AstNode* rhsp = nodep->rhsp()) iterateAndNextNull(rhsp);
	replaceWChild(nodep, nodep->rhsp());	// May have changed
    }

    //! Replace a ternary node with its THS after iterating
    //! Used with short-circuting, where the THS has not yet been iterated.
    void replaceWIteratedThs(AstNodeTriop* nodep) {
        if (AstNode* thsp = nodep->thsp()) iterateAndNextNull(thsp);
	replaceWChild(nodep, nodep->thsp());	// May have changed
    }
    void replaceWLhs(AstNodeUniop* nodep) {
	// Keep LHS, remove RHS
	replaceWChild(nodep, nodep->lhsp());
    }
    void replaceWLhs(AstNodeBiop* nodep) {
	// Keep LHS, remove RHS
	replaceWChild(nodep, nodep->lhsp());
    }
    void replaceWRhs(AstNodeBiop* nodep) {
	// Keep RHS, remove LHS
	replaceWChild(nodep, nodep->rhsp());
    }
    void replaceAsv(AstNodeBiop* nodep) {
	// BIASV(CONSTa, BIASV(CONSTb, c)) -> BIASV( BIASV_CONSTED(a,b), c)
	// BIASV(SAMEa,  BIASV(SAMEb, c))  -> BIASV( BIASV(SAMEa,SAMEb), c)
	//nodep->dumpTree(cout, "  repAsvConst_old: ");
	AstNode* ap = nodep->lhsp();
        AstNodeBiop* rp = VN_CAST(nodep->rhsp(), NodeBiop);
	AstNode* bp = rp->lhsp();
	AstNode* cp = rp->rhsp();
	ap->unlinkFrBack();
	bp->unlinkFrBack();
	cp->unlinkFrBack();
	rp->unlinkFrBack();
	nodep->lhsp(rp);
	nodep->rhsp(cp);
	rp->lhsp(ap);
	rp->rhsp(bp);
        if (VN_IS(rp->lhsp(), Const) && VN_IS(rp->rhsp(), Const)) replaceConst(rp);
	//nodep->dumpTree(cout, "  repAsvConst_new: ");
    }
    void replaceAsvLUp(AstNodeBiop* nodep) {
	// BIASV(BIASV(CONSTll,lr),r) -> BIASV(CONSTll,BIASV(lr,r))
        AstNodeBiop* lp = VN_CAST(nodep->lhsp()->unlinkFrBack(), NodeBiop);
	AstNode* llp = lp->lhsp()->unlinkFrBack();
	AstNode* lrp = lp->rhsp()->unlinkFrBack();
	AstNode* rp  = nodep->rhsp()->unlinkFrBack();
	nodep->lhsp(llp);
	nodep->rhsp(lp);
	lp->lhsp(lrp);
	lp->rhsp(rp);
	//nodep->dumpTree(cout, "  repAsvLUp_new: ");
    }
    void replaceAsvRUp(AstNodeBiop* nodep) {
	// BIASV(l,BIASV(CONSTrl,rr)) -> BIASV(CONSTrl,BIASV(l,rr))
	AstNode* lp  = nodep->lhsp()->unlinkFrBack();
        AstNodeBiop* rp = VN_CAST(nodep->rhsp()->unlinkFrBack(), NodeBiop);
	AstNode* rlp = rp->lhsp()->unlinkFrBack();
	AstNode* rrp = rp->rhsp()->unlinkFrBack();
	nodep->lhsp(rlp);
	nodep->rhsp(rp);
	rp->lhsp(lp);
	rp->rhsp(rrp);
	//nodep->dumpTree(cout, "  repAsvRUp_new: ");
    }
    void replaceAndOr(AstNodeBiop* nodep) {
	//  OR  (AND (CONSTll,lr), AND(CONSTrl==ll,rr))    -> AND (CONSTll, OR(lr,rr))
	//  OR  (AND (CONSTll,lr), AND(CONSTrl,    rr=lr)) -> AND (OR(ll,rl), rr)
	// nodep ^lp  ^llp   ^lrp  ^rp  ^rlp       ^rrp
	// (Or/And may also be reversed)
        AstNodeBiop* lp = VN_CAST(nodep->lhsp()->unlinkFrBack(), NodeBiop);
	AstNode* llp = lp->lhsp()->unlinkFrBack();
	AstNode* lrp = lp->rhsp()->unlinkFrBack();
        AstNodeBiop* rp = VN_CAST(nodep->rhsp()->unlinkFrBack(), NodeBiop);
	AstNode* rlp = rp->lhsp()->unlinkFrBack();
	AstNode* rrp = rp->rhsp()->unlinkFrBack();
	nodep->replaceWith(lp);
	if (operandsSame(llp,rlp)) {
	    lp->lhsp(llp);
	    lp->rhsp(nodep);
	    nodep->lhsp(lrp);
	    nodep->rhsp(rrp);
	    rp->deleteTree();
	    rlp->deleteTree();
	} else if (operandsSame(lrp, rrp)) {
	    lp->lhsp(nodep);
	    lp->rhsp(rrp);
	    nodep->lhsp(llp);
	    nodep->rhsp(rlp);
	    rp->deleteTree();
	    lrp->deleteTree();
	} else {
	    nodep->v3fatalSrc("replaceAndOr on something operandAndOrSame shouldn't have matched");
	}
	//nodep->dumpTree(cout, "  repAndOr_new: ");
    }
    void replaceShiftSame(AstNodeBiop* nodep) {
	// Or(Shift(ll,CONSTlr),Shift(rl,CONSTrr==lr)) -> Shift(Or(ll,rl),CONSTlr)
	// (Or/And may also be reversed)
        AstNodeBiop* lp = VN_CAST(nodep->lhsp()->unlinkFrBack(), NodeBiop);
	AstNode* llp = lp->lhsp()->unlinkFrBack();
	AstNode* lrp = lp->rhsp()->unlinkFrBack();
        AstNodeBiop* rp = VN_CAST(nodep->rhsp()->unlinkFrBack(), NodeBiop);
	AstNode* rlp = rp->lhsp()->unlinkFrBack();
	AstNode* rrp = rp->rhsp()->unlinkFrBack();
	nodep->replaceWith(lp);
	lp->lhsp(nodep);
	lp->rhsp(lrp);
	nodep->lhsp(llp);
	nodep->rhsp(rlp);
	rp->deleteTree();
	rrp->deleteTree();
	//nodep->dumpTree(cout, "  repShiftSame_new: ");
    }
    void replaceConcatSel(AstConcat* nodep) {
	// {a[1], a[0]} -> a[1:0]
        AstSel* lselp = VN_CAST(nodep->lhsp()->unlinkFrBack(), Sel);
        AstSel* rselp = VN_CAST(nodep->rhsp()->unlinkFrBack(), Sel);
	int lstart = lselp->lsbConst();
	int lwidth = lselp->widthConst();
	int rstart = rselp->lsbConst();
	int rwidth = rselp->widthConst();

	if ((rstart + rwidth) != lstart) nodep->v3fatalSrc("tried to merge two selects which are not adjacent");
	AstSel* newselp = new AstSel(lselp->fromp()->fileline(), rselp->fromp()->cloneTree(false), rstart, lwidth+rwidth);
	UINFO(5, "merged two adjacent sel "<<lselp <<" and "<<rselp<< " to one "<<newselp<<endl);

	nodep->replaceWith(newselp);
	lselp->deleteTree(); VL_DANGLING(lselp);
	rselp->deleteTree(); VL_DANGLING(rselp);
	nodep->deleteTree(); VL_DANGLING(nodep);
    }
    void replaceConcatMerge(AstConcat* nodep) {
        AstNodeBiop* lp = VN_CAST(nodep->lhsp(), NodeBiop);
        AstNodeBiop* rp = VN_CAST(nodep->rhsp(), NodeBiop);
	AstNode* llp = lp->lhsp()->cloneTree(false);
	AstNode* lrp = lp->rhsp()->cloneTree(false);
	AstNode* rlp = rp->lhsp()->cloneTree(false);
	AstNode* rrp = rp->rhsp()->cloneTree(false);
	if (concatMergeable(lp, rp)) {
	    AstConcat* newlp = new AstConcat(rlp->fileline(), llp, rlp);
	    AstConcat* newrp = new AstConcat(rrp->fileline(), lrp, rrp);
	    // use the lhs to replace the parent concat
	    lp->lhsp()->replaceWith(newlp);
	    lp->rhsp()->replaceWith(newrp);
	    lp->dtypeChgWidthSigned(newlp->width(), newlp->width(), AstNumeric::fromBool(true));
	    UINFO(5, "merged "<< nodep <<endl);
	    rp->unlinkFrBack()->deleteTree(); VL_DANGLING(rp);
	    nodep->replaceWith(lp->unlinkFrBack()); nodep->deleteTree(); VL_DANGLING(nodep);
            iterate(lp->lhsp());
            iterate(lp->rhsp());
	} else nodep->v3fatalSrc("tried to merge two Concat which are not adjacent");
    }
    void replaceExtend(AstNode* nodep, AstNode* arg0p) {
	// -> EXTEND(nodep)
	// like a AstExtend{$rhsp}, but we need to set the width correctly from base node
	arg0p->unlinkFrBack();
        AstNode* newp = (VN_IS(nodep, ExtendS)
			 ? static_cast<AstNode*>(new AstExtendS(nodep->fileline(), arg0p))
			 : static_cast<AstNode*>(new AstExtend (nodep->fileline(), arg0p)));
	newp->dtypeFrom(nodep);
	nodep->replaceWith(newp); nodep->deleteTree(); VL_DANGLING(nodep);
    }
    void replacePowShift(AstNodeBiop* nodep) {  // Pow or PowS
	UINFO(5,"POW(2,b)->SHIFTL(1,b) "<<nodep<<endl);
	AstNode* rhsp = nodep->rhsp()->unlinkFrBack();
	AstShiftL* newp = new AstShiftL(nodep->fileline(),
					new AstConst(nodep->fileline(), 1),
					rhsp);
	newp->dtypeFrom(nodep);
	newp->lhsp()->dtypeFrom(nodep);
	nodep->replaceWith(newp); nodep->deleteTree(); VL_DANGLING(nodep);
    }
    void replaceMulShift(AstMul* nodep) {  // Mul, but not MulS as not simple shift
	UINFO(5,"MUL(2^n,b)->SHIFTL(b,n) "<<nodep<<endl);
        int amount = VN_CAST(nodep->lhsp(), Const)->num().mostSetBitP1()-1;  // 2^n->n+1
	AstNode* opp = nodep->rhsp()->unlinkFrBack();
	AstShiftL* newp = new AstShiftL(nodep->fileline(),
					opp, new AstConst(nodep->fileline(), amount));
	newp->dtypeFrom(nodep);
	nodep->replaceWith(newp); nodep->deleteTree(); VL_DANGLING(nodep);
    }
    void replaceDivShift(AstDiv* nodep) {  // Mul, but not MulS as not simple shift
	UINFO(5,"DIV(b,2^n)->SHIFTR(b,n) "<<nodep<<endl);
        int amount = VN_CAST(nodep->rhsp(), Const)->num().mostSetBitP1()-1;  // 2^n->n+1
	AstNode* opp = nodep->lhsp()->unlinkFrBack();
	AstShiftR* newp = new AstShiftR(nodep->fileline(),
					opp, new AstConst(nodep->fileline(), amount));
	newp->dtypeFrom(nodep);
	nodep->replaceWith(newp); nodep->deleteTree(); VL_DANGLING(nodep);
    }
    void replaceShiftOp(AstNodeBiop* nodep) {
	UINFO(5,"SHIFT(AND(a,b),CONST)->AND(SHIFT(a,CONST),SHIFT(b,CONST)) "<<nodep<<endl);
	AstNRelinker handle;
	nodep->unlinkFrBack(&handle);
        AstNodeBiop* lhsp = VN_CAST(nodep->lhsp(), NodeBiop); lhsp->unlinkFrBack();
	AstNode* shiftp = nodep->rhsp()->unlinkFrBack();
	AstNode* ap = lhsp->lhsp()->unlinkFrBack();
	AstNode* bp = lhsp->rhsp()->unlinkFrBack();
	AstNodeBiop* shift1p = nodep;
	AstNodeBiop* shift2p = nodep->cloneTree(true);
	shift1p->lhsp(ap); shift1p->rhsp(shiftp->cloneTree(true));
	shift2p->lhsp(bp); shift2p->rhsp(shiftp);
	AstNodeBiop* newp = lhsp;
	newp->lhsp(shift1p); newp->rhsp(shift2p);
	handle.relink(newp);
        iterate(newp);  // Further reduce, either node may have more reductions.
    }
    void replaceShiftShift(AstNodeBiop* nodep) {
	UINFO(4,"SHIFT(SHIFT(a,s1),s2)->SHIFT(a,ADD(s1,s2)) "<<nodep<<endl);
	if (debug()>=9) nodep->dumpTree(cout, "  repShiftShift_old: ");
        AstNodeBiop* lhsp = VN_CAST(nodep->lhsp(), NodeBiop); lhsp->unlinkFrBack();
	AstNode* ap = lhsp->lhsp()->unlinkFrBack();
	AstNode* shift1p = lhsp->rhsp()->unlinkFrBack();
	AstNode* shift2p = nodep->rhsp()->unlinkFrBack();
	// Shift1p and shift2p may have different sizes, both are self-determined so sum with infinite width
	if (nodep->type()==lhsp->type()) {
            int shift1 = VN_CAST(shift1p, Const)->toUInt();
            int shift2 = VN_CAST(shift2p, Const)->toUInt();
	    int newshift = shift1+shift2;
	    shift1p->deleteTree(); VL_DANGLING(shift1p);
	    shift2p->deleteTree(); VL_DANGLING(shift2p);
	    nodep->lhsp(ap);
	    nodep->rhsp(new AstConst(nodep->fileline(), newshift));
            iterate(nodep);  // Further reduce, either node may have more reductions.
	} else {
	    // We know shift amounts are constant, but might be a mixed left/right shift
            int shift1 = VN_CAST(shift1p, Const)->toUInt(); if (VN_IS(lhsp, ShiftR))  shift1=-shift1;
            int shift2 = VN_CAST(shift2p, Const)->toUInt(); if (VN_IS(nodep, ShiftR)) shift2=-shift2;
	    int newshift = shift1+shift2;
	    shift1p->deleteTree(); VL_DANGLING(shift1p);
	    shift2p->deleteTree(); VL_DANGLING(shift2p);
	    AstNode* newp;
	    V3Number mask1 (nodep->fileline(), nodep->width());
	    V3Number ones (nodep->fileline(), nodep->width());
	    ones.setMask(nodep->width());
	    if (shift1<0) {
		mask1.opShiftR(ones,V3Number(nodep->fileline(),VL_WORDSIZE,-shift1));
	    } else {
		mask1.opShiftL(ones,V3Number(nodep->fileline(),VL_WORDSIZE,shift1));
	    }
	    V3Number mask (nodep->fileline(), nodep->width());
	    if (shift2<0) {
		mask.opShiftR(mask1,V3Number(nodep->fileline(),VL_WORDSIZE,-shift2));
	    } else {
		mask.opShiftL(mask1,V3Number(nodep->fileline(),VL_WORDSIZE,shift2));
	    }
	    if (newshift<0) {
		newp = new AstShiftR(nodep->fileline(), ap,
				     new AstConst(nodep->fileline(), -newshift));
	    } else {
		newp = new AstShiftL(nodep->fileline(), ap,
				     new AstConst(nodep->fileline(), newshift));
	    }
	    newp->dtypeFrom(nodep);
            newp = new AstAnd(nodep->fileline(),
                              newp,
                              new AstConst(nodep->fileline(), mask));
	    newp->dtypeFrom(nodep);
	    nodep->replaceWith(newp); nodep->deleteTree(); VL_DANGLING(nodep);
	    //newp->dumpTree(cout, "  repShiftShift_new: ");
            iterate(newp);  // Further reduce, either node may have more reductions.
	}
	lhsp->deleteTree(); VL_DANGLING(lhsp);
    }

    bool replaceAssignMultiSel(AstNodeAssign* nodep) {
	// Multiple assignments to sequential bits can be concated
	// ASSIGN(SEL(a),aq), ASSIGN(SEL(a+1),bq) -> ASSIGN(SEL(a:b),CONCAT(aq,bq)
	// ie. assign var[2]=a, assign var[3]=b -> assign var[3:2]={b,a}
	if (!m_modp) return false;   // Skip if we're not const'ing an entire module (IE doing only one assign, etc)
        AstSel* sel1p = VN_CAST(nodep->lhsp(), Sel); if (!sel1p) return false;
        AstNodeAssign* nextp = VN_CAST(nodep->nextp(), NodeAssign); if (!nextp) return false;
	if (nodep->type() != nextp->type()) return false;
        AstSel* sel2p = VN_CAST(nextp->lhsp(), Sel); if (!sel2p) return false;
        AstVarRef* varref1p = VN_CAST(sel1p->fromp(), VarRef); if (!varref1p) return false;
        AstVarRef* varref2p = VN_CAST(sel2p->fromp(), VarRef); if (!varref2p) return false;
	if (!varref1p->sameGateTree(varref2p)) return false;
        AstConst* con1p = VN_CAST(sel1p->lsbp(), Const); if (!con1p) return false;
        AstConst* con2p = VN_CAST(sel2p->lsbp(), Const); if (!con2p) return false;
	// We need to make sure there's no self-references involved in either
	// assignment.  For speed, we only look 3 deep, then give up.
	if (!varNotReferenced(nodep->rhsp(), varref1p->varp())) return false;
	if (!varNotReferenced(nextp->rhsp(), varref2p->varp())) return false;
	// Swap?
	if ((  con1p->toSInt() != con2p->toSInt() + sel2p->width())
	    &&(con2p->toSInt() != con1p->toSInt() + sel1p->width())) return false;
	bool lsbFirstAssign = (con1p->toUInt() < con2p->toUInt());
	// If the user already has nice 32-bit divisions, keep them to aid later subdivision
	//if (VL_BITBIT_I(con1p->toUInt()) == 0) return false;
	UINFO(4,"replaceAssignMultiSel "<<nodep<<endl);
	UINFO(4,"                   && "<<nextp<<endl);
	//nodep->dumpTree(cout, "comb1: ");
	//nextp->dumpTree(cout, "comb2: ");
	AstNode* rhs1p = nodep->rhsp()->unlinkFrBack();
	AstNode* rhs2p = nextp->rhsp()->unlinkFrBack();
	AstNode* newp;
	if (lsbFirstAssign) {
            newp = nodep->cloneType(new AstSel(sel1p->fileline(), varref1p->unlinkFrBack(),
                                               sel1p->lsbConst(), sel1p->width() + sel2p->width()),
                                    new AstConcat(rhs1p->fileline(), rhs2p, rhs1p));
	} else {
            newp = nodep->cloneType(new AstSel(sel1p->fileline(), varref1p->unlinkFrBack(),
                                               sel2p->lsbConst(), sel1p->width() + sel2p->width()),
                                    new AstConcat(rhs1p->fileline(), rhs1p, rhs2p));
	}
	//pnewp->dumpTree(cout, "conew: ");
	nodep->replaceWith(newp); nodep->deleteTree();
	nextp->unlinkFrBack()->deleteTree();
	return true;
    }

    bool varNotReferenced(AstNode* nodep, AstVar* varp, int level=0) {
	// Return true if varp never referenced under node.
	// Return false if referenced, or tree too deep to be worth it, or side effects
	if (!nodep) return true;
	if (level>2) return false;
	if (nodep->isPure()) return false;  // For example a $fgetc can't be reordered
        if (VN_IS(nodep, NodeVarRef) && VN_CAST(nodep, NodeVarRef)->varp()==varp) return false;
	return (varNotReferenced  (nodep->nextp(),varp,level+1)
		&& varNotReferenced(nodep->op1p(),varp,level+1)
		&& varNotReferenced(nodep->op2p(),varp,level+1)
		&& varNotReferenced(nodep->op3p(),varp,level+1)
		&& varNotReferenced(nodep->op4p(),varp,level+1));
    }

    bool replaceNodeAssign(AstNodeAssign* nodep) {
        if (VN_IS(nodep->lhsp(), VarRef)
            && VN_IS(nodep->rhsp(), VarRef)
            && VN_CAST(nodep->lhsp(), VarRef)->sameNoLvalue(VN_CAST(nodep->rhsp(), VarRef))
            && !VN_IS(nodep, AssignDly)) {
	    // X = X.  Quite pointless, though X <= X may override another earlier assignment
            if (VN_IS(nodep, AssignW)) {
		nodep->v3error("Wire inputs its own output, creating circular logic (wire x=x)");
		return false;  // Don't delete the assign, or V3Gate will freak out
	    } else {
		nodep->unlinkFrBack()->deleteTree(); VL_DANGLING(nodep);
		return true;
	    }
	}
        else if (m_doV && VN_IS(nodep->lhsp(), Concat)) {
	    bool need_temp = false;
            if (m_warn && !VN_IS(nodep, AssignDly)) {  // Is same var on LHS and RHS?
		// Note only do this (need user4) when m_warn, which is
		// done as unique visitor
		AstUser4InUse	m_inuser4;
		ConstVarMarkVisitor mark(nodep->lhsp());
		ConstVarFindVisitor find(nodep->rhsp());
		if (find.found()) need_temp = true;
	    }
	    if (need_temp) {
		// The first time we constify, there may be the same variable on the LHS
		// and RHS.  In that case, we must use temporaries, or {a,b}={b,a} will break.
		UINFO(4,"  ASSITEMP "<<nodep<<endl);
		// ASSIGN(CONCAT(lc1,lc2),rhs) -> ASSIGN(temp1,SEL(rhs,{size})),
		//				  ASSIGN(temp2,SEL(newrhs,{size}))
		//                                ASSIGN(lc1,temp1),
		//				  ASSIGN(lc2,temp2)
	    } else {
		UINFO(4,"  ASSI "<<nodep<<endl);
		// ASSIGN(CONCAT(lc1,lc2),rhs) -> ASSIGN(lc1,SEL(rhs,{size})),
		//				  ASSIGN(lc2,SEL(newrhs,{size}))
	    }
	    if (debug()>=9) nodep->dumpTree(cout,"  Ass_old: ");
	    // Unlink the stuff
            AstNode* lc1p = VN_CAST(nodep->lhsp(), Concat)->lhsp()->unlinkFrBack();
            AstNode* lc2p = VN_CAST(nodep->lhsp(), Concat)->rhsp()->unlinkFrBack();
            AstNode* conp = VN_CAST(nodep->lhsp(), Concat)->unlinkFrBack();
	    AstNode* rhsp = nodep->rhsp()->unlinkFrBack();
	    AstNode*   rhs2p   = rhsp->cloneTree(false);
	    // Calc widths
	    int lsb2 = 0;
	    int msb2 = lsb2+lc2p->width()-1;
	    int lsb1 = msb2+1;
	    int msb1 = lsb1+lc1p->width()-1;
	    if (msb1!=(conp->width()-1)) nodep->v3fatalSrc("Width calc mismatch");
	    // Form ranges
	    AstSel*  sel1p = new AstSel(conp->fileline(), rhsp,  lsb1, msb1-lsb1+1);
	    AstSel*  sel2p = new AstSel(conp->fileline(), rhs2p, lsb2, msb2-lsb2+1);
	    // Make new assigns of same flavor as old one
	    //*** Not cloneTree; just one node.
	    AstNode* newp = NULL;
	    if (!need_temp) {
                AstNodeAssign* asn1ap = VN_CAST(nodep->cloneType(lc1p, sel1p), NodeAssign);
                AstNodeAssign* asn2ap = VN_CAST(nodep->cloneType(lc2p, sel2p), NodeAssign);
		asn1ap->dtypeFrom(sel1p);
		asn2ap->dtypeFrom(sel2p);
		newp = AstNode::addNext(newp, asn1ap);
		newp = AstNode::addNext(newp, asn2ap);
	    } else {
		if (!m_modp) nodep->v3fatalSrc("Not under module");
		// We could create just one temp variable, but we'll get better optimization
		// if we make one per term.
                string name1 = (string("__Vconcswap")+cvtToStr(m_modp->varNumGetInc()));
                string name2 = (string("__Vconcswap")+cvtToStr(m_modp->varNumGetInc()));
		AstVar* temp1p = new AstVar(sel1p->fileline(), AstVarType::BLOCKTEMP, name1,
					    VFlagLogicPacked(), msb1-lsb1+1);
		AstVar* temp2p = new AstVar(sel2p->fileline(), AstVarType::BLOCKTEMP, name2,
					    VFlagLogicPacked(), msb2-lsb2+1);
		m_modp->addStmtp(temp1p);
		m_modp->addStmtp(temp2p);
                AstNodeAssign* asn1ap = VN_CAST(nodep->cloneType
                                                (new AstVarRef(sel1p->fileline(), temp1p, true),
                                                 sel1p), NodeAssign);
                AstNodeAssign* asn2ap = VN_CAST(nodep->cloneType
                                                (new AstVarRef(sel2p->fileline(), temp2p, true),
                                                 sel2p), NodeAssign);
                AstNodeAssign* asn1bp = VN_CAST(nodep->cloneType
                                                (lc1p, new AstVarRef(sel1p->fileline(), temp1p, false)),
                                                NodeAssign);
                AstNodeAssign* asn2bp = VN_CAST(nodep->cloneType
                                                (lc2p, new AstVarRef(sel2p->fileline(), temp2p, false)),
                                                NodeAssign);
		asn1ap->dtypeFrom(temp1p);
		asn1bp->dtypeFrom(temp1p);
		asn2ap->dtypeFrom(temp2p);
		asn2bp->dtypeFrom(temp2p);
		// This order matters
		newp = AstNode::addNext(newp, asn1ap);
		newp = AstNode::addNext(newp, asn2ap);
		newp = AstNode::addNext(newp, asn1bp);
		newp = AstNode::addNext(newp, asn2bp);
	    }
	    if (debug()>=9 && newp) newp->dumpTreeAndNext(cout,"     _new: ");
	    nodep->addNextHere(newp);
	    // Cleanup
	    nodep->unlinkFrBack()->deleteTree(); VL_DANGLING(nodep);
	    conp->deleteTree(); VL_DANGLING(conp);
	    // Further reduce, either node may have more reductions.
	    return true;
	}
        else if (m_doV && VN_IS(nodep->rhsp(), StreamR)) {
	    // The right-streaming operator on rhs of assignment does not
	    // change the order of bits. Eliminate stream but keep its lhsp
	    // Unlink the stuff
            AstNode* srcp    = VN_CAST(nodep->rhsp(), StreamR)->lhsp()->unlinkFrBack();
            AstNode* sizep   = VN_CAST(nodep->rhsp(), StreamR)->rhsp()->unlinkFrBack();
            AstNode* streamp = VN_CAST(nodep->rhsp(), StreamR)->unlinkFrBack();
	    nodep->rhsp(srcp);
	    // Cleanup
	    sizep->deleteTree(); VL_DANGLING(sizep);
	    streamp->deleteTree(); VL_DANGLING(streamp);
	    // Further reduce, any of the nodes may have more reductions.
	    return true;
	}
        else if (m_doV && VN_IS(nodep->lhsp(), StreamL)) {
	    // Push the stream operator to the rhs of the assignment statement
            int dWidth = VN_CAST(nodep->lhsp(), StreamL)->lhsp()->width();
	    int sWidth = nodep->rhsp()->width();
	    // Unlink the stuff
            AstNode* dstp    = VN_CAST(nodep->lhsp(), StreamL)->lhsp()->unlinkFrBack();
            AstNode* streamp = VN_CAST(nodep->lhsp(), StreamL)->unlinkFrBack();
	    AstNode* srcp    = nodep->rhsp()->unlinkFrBack();
	    // Connect the rhs to the stream operator and update its width
            VN_CAST(streamp, StreamL)->lhsp(srcp);
	    streamp->dtypeSetLogicSized((srcp->width()),
					(srcp->widthMin()),
					AstNumeric::UNSIGNED);
	    // Shrink the RHS if necessary
	    if (sWidth > dWidth) {
		streamp = new AstSel(streamp->fileline(), streamp, sWidth-dWidth, dWidth);
	    }
	    // Link the nodes back in
	    nodep->lhsp(dstp);
	    nodep->rhsp(streamp);
	    return true;
	}
        else if (m_doV && VN_IS(nodep->lhsp(), StreamR)) {
	    // The right stream operator on lhs of assignment statement does
	    // not reorder bits. However, if the rhs is wider than the lhs,
	    // then we select bits from the left-most, not the right-most.
            int dWidth = VN_CAST(nodep->lhsp(), StreamR)->lhsp()->width();
	    int sWidth = nodep->rhsp()->width();
	    // Unlink the stuff
            AstNode* dstp    = VN_CAST(nodep->lhsp(), StreamR)->lhsp()->unlinkFrBack();
            AstNode* sizep   = VN_CAST(nodep->lhsp(), StreamR)->rhsp()->unlinkFrBack();
            AstNode* streamp = VN_CAST(nodep->lhsp(), StreamR)->unlinkFrBack();
	    AstNode* srcp    = nodep->rhsp()->unlinkFrBack();
	    if (sWidth > dWidth) {
		srcp = new AstSel(streamp->fileline(), srcp,  sWidth-dWidth, dWidth);
	    }
	    nodep->lhsp(dstp);
	    nodep->rhsp(srcp);
	    // Cleanup
	    sizep->deleteTree(); VL_DANGLING(sizep);
	    streamp->deleteTree(); VL_DANGLING(streamp);
	    // Further reduce, any of the nodes may have more reductions.
	    return true;
	}
	else if (replaceAssignMultiSel(nodep)) {
	    return true;
	}
	return false;
    }

    // Boolean replacements
    bool operandBoolShift(const AstNode* nodep) {
	// boolean test of AND(const,SHIFTR(x,const)) -> test of AND(SHIFTL(x,const), x)
        if (!VN_IS(nodep, And)) return false;
        if (!VN_IS(VN_CAST_CONST(nodep, And)->lhsp(), Const)) return false;
        if (!VN_IS(VN_CAST_CONST(nodep, And)->rhsp(), ShiftR)) return false;
        const AstShiftR* shiftp = VN_CAST(VN_CAST_CONST(nodep, And)->rhsp(), ShiftR);
        if (!VN_IS(shiftp->rhsp(), Const)) return false;
        if (static_cast<uint32_t>(nodep->width())
            <= VN_CAST_CONST(shiftp->rhsp(), Const)->toUInt()) return false;
	return true;
    }
    void replaceBoolShift(AstNode* nodep) {
	if (debug()>=9) nodep->dumpTree(cout,"  bshft_old: ");
        AstConst* andConstp = VN_CAST(VN_CAST(nodep, And)->lhsp(), Const);
        AstNode* fromp = VN_CAST(VN_CAST(nodep, And)->rhsp(), ShiftR)->lhsp()->unlinkFrBack();
        AstConst* shiftConstp = VN_CAST(VN_CAST(VN_CAST(nodep, And)->rhsp(), ShiftR)->rhsp(), Const);
	V3Number val (andConstp->fileline(), andConstp->width());
	val.opShiftL(andConstp->num(), shiftConstp->num());
	AstAnd* newp = new AstAnd(nodep->fileline(),
				  new AstConst(nodep->fileline(), val),
				  fromp);
        // widthMin no longer applicable if different C-expanded width
        newp->dtypeSetLogicSized(nodep->width(), nodep->width(), AstNumeric::UNSIGNED);
	nodep->replaceWith(newp);
	nodep->deleteTree(); VL_DANGLING(nodep);
	if (debug()>=9) newp->dumpTree(cout,"       _new: ");
    }

    void replaceWithSimulation(AstNode* nodep) {
	SimulateVisitor simvis;
	// Run it - may be unoptimizable due to large for loop, etc
	simvis.mainParamEmulate(nodep);
	if (!simvis.optimizable()) {
	    AstNode* errorp = simvis.whyNotNodep(); if (!errorp) errorp = nodep;
	    nodep->v3error("Expecting expression to be constant, but can't determine constant for "
			   <<nodep->prettyTypeName()<<endl
			   <<errorp->warnMore()<<"... Location of non-constant "
			   <<errorp->prettyTypeName()<<": "<<simvis.whyNotMessage());
	    replaceZero(nodep); VL_DANGLING(nodep);
	} else {
	    // Fetch the result
	    V3Number* outnump = simvis.fetchNumberNull(nodep);
	    if (!outnump) nodep->v3fatalSrc("No number returned from simulation");
	    // Replace it
	    replaceNum(nodep,*outnump); VL_DANGLING(nodep);
	}
    }

    //----------------------------------------

    // VISITORS
    virtual void visit(AstNetlist* nodep) {
	// Iterate modules backwards, in bottom-up order.  That's faster
        iterateChildrenBackwards(nodep);
    }
    virtual void visit(AstNodeModule* nodep) {
	m_modp = nodep;
        iterateChildren(nodep);
	m_modp = NULL;
    }
    virtual void visit(AstCFunc* nodep) {
	// No ASSIGNW removals under funcs, we've long eliminated INITIALs
	// (We should perhaps rename the assignw's to just assigns)
	m_wremove = false;
        iterateChildren(nodep);
	m_wremove = true;
    }
    virtual void visit(AstScope* nodep) {
	// No ASSIGNW removals under scope, we've long eliminated INITIALs
	m_scopep = nodep;
	m_wremove = false;
        iterateChildren(nodep);
	m_wremove = true;
	m_scopep = NULL;
    }

    void swapSides(AstNodeBiCom* nodep) {
	// COMMUNATIVE({a},CONST) -> COMMUNATIVE(CONST,{a})
	// This simplifies later optimizations
	AstNode* lhsp = nodep->lhsp()->unlinkFrBackWithNext();
	AstNode* rhsp = nodep->rhsp()->unlinkFrBackWithNext();
	nodep->lhsp(rhsp);
	nodep->rhsp(lhsp);
        iterate(nodep);  // Again?
    }

    int operandConcatMove(AstConcat* nodep) {
	//    CONCAT under concat  (See moveConcat)
	// Return value: true indicates to do it; 2 means move to LHS
        AstConcat* abConcp = VN_CAST(nodep->lhsp(), Concat);
        AstConcat* bcConcp = VN_CAST(nodep->rhsp(), Concat);
	if (!abConcp && !bcConcp) return 0;
	if (bcConcp) {
	    AstNode* ap = nodep->lhsp();
	    AstNode* bp = bcConcp->lhsp();
	    // If a+b == 32,64,96 etc, then we want to have a+b together on LHS
	    if (VL_BITBIT_I(ap->width()+bp->width())==0) return 2;  // Transform 2: to abConc
	}
	else { //abConcp
	    // Unless lhs is already 32 bits due to above, reorder it
	    if (VL_BITBIT_I(nodep->lhsp()->width())!=0) return 1;  // Transform 1: to bcConc
	}
	return 0;  // ok
    }
    void moveConcat(AstConcat* nodep) {
	//    1: CONCAT(CONCAT({a},{b}),{c})  -> CONCAT({a},CONCAT({b}, {c}))
	// or 2: CONCAT({a}, CONCAT({b},{c})) -> CONCAT(CONCAT({a},{b}),{c})
	// Because the lhs of a concat needs a shift but the rhs doesn't,
	// putting additional CONCATs on the RHS leads to fewer assembler operations.
	// However, we'll end up with lots of wide moves if we make huge trees
	// like that, so on 32 bit boundaries, we'll do the opposite form.
	UINFO(4,"Move concat: "<<nodep<<endl);
	if (operandConcatMove(nodep)>1) {
	    AstNode* ap = nodep->lhsp()->unlinkFrBack();
            AstConcat* bcConcp = VN_CAST(nodep->rhsp(), Concat); bcConcp->unlinkFrBack();
	    AstNode* bp = bcConcp->lhsp()->unlinkFrBack();
	    AstNode* cp = bcConcp->rhsp()->unlinkFrBack();
	    AstConcat* abConcp = new AstConcat(bcConcp->fileline(),
					       ap, bp);
	    nodep->lhsp(abConcp);
	    nodep->rhsp(cp);
	    // If bp was a concat, then we have this exact same form again!
	    // Recurse rather then calling node->iterate to prevent 2^n recursion!
	    if (operandConcatMove(abConcp)) moveConcat(abConcp);
	    bcConcp->deleteTree(); VL_DANGLING(bcConcp);
	} else {
            AstConcat* abConcp = VN_CAST(nodep->lhsp(), Concat); abConcp->unlinkFrBack();
	    AstNode* ap = abConcp->lhsp()->unlinkFrBack();
	    AstNode* bp = abConcp->rhsp()->unlinkFrBack();
	    AstNode* cp = nodep->rhsp()->unlinkFrBack();
	    AstConcat* bcConcp = new AstConcat(abConcp->fileline(),
					       bp, cp);
	    nodep->lhsp(ap);
	    nodep->rhsp(bcConcp);
	    if (operandConcatMove(bcConcp)) moveConcat(bcConcp);
	    abConcp->deleteTree(); VL_DANGLING(abConcp);
	}
    }

    // Special cases
    virtual void visit(AstConst* nodep) {}	// Already constant

    virtual void visit(AstCell* nodep) {
	if (m_params) {
            iterateAndNextNull(nodep->paramsp());
	} else {
            iterateChildren(nodep);
	}
    }
    virtual void visit(AstPin* nodep) {
        iterateChildren(nodep);
    }

    void replaceSelSel(AstSel* nodep) {
	// SEL(SEL({x},a,b),c,d) => SEL({x},a+c,d)
        AstSel* belowp = VN_CAST(nodep->fromp(), Sel);
	AstNode* fromp = belowp->fromp()->unlinkFrBack();
	AstNode* widthp = nodep->widthp()->unlinkFrBack();
	AstNode* lsb1p = nodep->lsbp()->unlinkFrBack();
	AstNode* lsb2p = belowp->lsbp()->unlinkFrBack();
	// Eliminate lower range
	UINFO(4,"Elim Lower range: "<<nodep<<endl);
	AstNode* newlsbp;
        if (VN_IS(lsb1p, Const) && VN_IS(lsb2p, Const)) {
	    newlsbp = new AstConst(lsb1p->fileline(),
                                   VN_CAST(lsb1p, Const)->toUInt()
                                   + VN_CAST(lsb2p, Const)->toUInt());
	    lsb1p->deleteTree(); VL_DANGLING(lsb1p);
	    lsb2p->deleteTree(); VL_DANGLING(lsb2p);
	} else {
	    // Width is important, we need the width of the fromp's
	    // expression, not the potentially smaller lsb1p's width
	    newlsbp = new AstAdd(lsb1p->fileline(),
				 lsb2p, new AstExtend(lsb1p->fileline(), lsb1p));
	    newlsbp->dtypeFrom(lsb2p); // Unsigned
            VN_CAST(newlsbp, Add)->rhsp()->dtypeFrom(lsb2p);
	}
	AstSel* newp = new AstSel(nodep->fileline(),
				  fromp,
				  newlsbp,
				  widthp);
	nodep->replaceWith(newp);
	nodep->deleteTree(); VL_DANGLING(nodep);
    }

    void replaceSelConcat(AstSel* nodep) {
	// SEL(CONCAT(a,b),c,d) => SEL(a or b, . .)
        AstConcat* conp = VN_CAST(nodep->fromp(), Concat);
	AstNode* conLhsp = conp->lhsp();
	AstNode* conRhsp = conp->rhsp();
        if (static_cast<int>(nodep->lsbConst()) >= conRhsp->width()) {
	    conLhsp->unlinkFrBack();
	    AstSel* newp = new AstSel(nodep->fileline(),
				      conLhsp,
				      nodep->lsbConst() - conRhsp->width(),
				      nodep->widthConst());
	    nodep->replaceWith(newp);
	}
        else if (static_cast<int>(nodep->msbConst()) < conRhsp->width()) {
	    conRhsp->unlinkFrBack();
	    AstSel* newp = new AstSel(nodep->fileline(),
				      conRhsp,
				      nodep->lsbConst(),
				      nodep->widthConst());
	    nodep->replaceWith(newp);
	}
	else {
	    // Yuk, split between the two
	    conRhsp->unlinkFrBack();
	    conLhsp->unlinkFrBack();
	    AstConcat* newp = new AstConcat
		(nodep->fileline(),
		 new AstSel(nodep->fileline(),
			    conLhsp,
			    0,
			    nodep->msbConst() - conRhsp->width() + 1),
		 new AstSel(nodep->fileline(),
			    conRhsp,
			    nodep->lsbConst(),
			    conRhsp->width()-nodep->lsbConst()));
	    nodep->replaceWith(newp);
	}
	nodep->deleteTree(); VL_DANGLING(nodep);
    }
    bool operandSelReplicate(AstSel* nodep) {
	// SEL(REPLICATE(from,rep),lsb,width) => SEL(from,0,width) as long as SEL's width <= b's width
        AstReplicate* repp = VN_CAST(nodep->fromp(), Replicate);
	AstNode* fromp = repp->lhsp();
        AstConst* lsbp = VN_CAST(nodep->lsbp(), Const); if (!lsbp) return false;
        AstNode* widthp = nodep->widthp(); if (!VN_IS(widthp, Const)) return false;
	if (!fromp->width()) nodep->v3fatalSrc("Not widthed");
	if ((lsbp->toUInt() / fromp->width())
	    != ((lsbp->toUInt()+nodep->width()-1) / fromp->width())) return false;
	//
	fromp->unlinkFrBack();
	widthp->unlinkFrBack();
	AstSel* newp = new AstSel(nodep->fileline(),
				  fromp,
				  new AstConst(lsbp->fileline(), lsbp->toUInt() % fromp->width()),
				  widthp);
	newp->dtypeFrom(nodep);
	nodep->replaceWith(newp); nodep->deleteTree(); VL_DANGLING(nodep);
	return true;
    }
    bool operandRepRep(AstReplicate* nodep) {
	// REPLICATE(REPLICATE2(from2,cnt2),cnt1) => REPLICATE(from2,(cnt1+cnt2))
        AstReplicate* rep2p = VN_CAST(nodep->lhsp(), Replicate);
	AstNode* from2p = rep2p->lhsp();
        AstConst* cnt1p = VN_CAST(nodep->rhsp(), Const); if (!cnt1p) return false;
        AstConst* cnt2p = VN_CAST(rep2p->rhsp(), Const); if (!cnt2p) return false;
	//
	from2p->unlinkFrBack();
	cnt1p->unlinkFrBack();
	cnt2p->unlinkFrBack();
	AstReplicate* newp = new AstReplicate(nodep->fileline(),
					      from2p, cnt1p->toUInt()*cnt2p->toUInt());
	newp->dtypeFrom(nodep);
	nodep->replaceWith(newp); nodep->deleteTree(); VL_DANGLING(nodep);
	return true;
    }
    bool operandConcatSame(AstConcat* nodep) {
	// CONCAT(fromp,fromp) -> REPLICATE(fromp,1+1)
	// CONCAT(REP(fromp,cnt1),fromp) -> REPLICATE(fromp,cnt1+1)
	// CONCAT(fromp,REP(fromp,cnt1)) -> REPLICATE(fromp,1+cnt1)
	// CONCAT(REP(fromp,cnt1),REP(fromp,cnt2)) -> REPLICATE(fromp,cnt1+cnt2)
	AstNode* from1p = nodep->lhsp(); uint32_t cnt1 = 1;
	AstNode* from2p = nodep->rhsp(); uint32_t cnt2 = 1;
        if (VN_IS(from1p, Replicate)) {
            AstConst* cnt1p = VN_CAST(VN_CAST(from1p, Replicate)->rhsp(), Const); if (!cnt1p) return false;
            from1p = VN_CAST(from1p, Replicate)->lhsp();
	    cnt1 = cnt1p->toUInt();
	}
        if (VN_IS(from2p, Replicate)) {
            AstConst* cnt2p = VN_CAST(VN_CAST(from2p, Replicate)->rhsp(), Const); if (!cnt2p) return false;
            from2p = VN_CAST(from2p, Replicate)->lhsp();
	    cnt2 = cnt2p->toUInt();
	}
	if (!operandsSame(from1p,from2p)) return false;
	//
	from1p->unlinkFrBack();
	AstReplicate* newp = new AstReplicate(nodep->fileline(), from1p, cnt1+cnt2);
	newp->dtypeFrom(nodep);
	nodep->replaceWith(newp); nodep->deleteTree(); VL_DANGLING(nodep);
	return true;
    }
    void replaceSelIntoBiop(AstSel* nodep) {
	// SEL(BUFIF1(a,b),1,bit) => BUFIF1(SEL(a,1,bit),SEL(b,1,bit))
        AstNodeBiop* fromp = VN_CAST(nodep->fromp()->unlinkFrBack(), NodeBiop);
	if (!fromp) nodep->v3fatalSrc("Called on non biop");
	AstNode* lsbp = nodep->lsbp()->unlinkFrBack();
	AstNode* widthp = nodep->widthp()->unlinkFrBack();
	//
	AstNode* bilhsp = fromp->lhsp()->unlinkFrBack();
	AstNode* birhsp = fromp->rhsp()->unlinkFrBack();
	//
	fromp->lhsp(new AstSel(nodep->fileline(),
			       bilhsp, lsbp->cloneTree(true), widthp->cloneTree(true)));
	fromp->rhsp(new AstSel(nodep->fileline(),
			       birhsp, lsbp, widthp));
	fromp->dtypeFrom(nodep);
	nodep->replaceWith(fromp); nodep->deleteTree(); VL_DANGLING(nodep);
    }
    void replaceSelIntoUniop(AstSel* nodep) {
	// SEL(NOT(a),1,bit) => NOT(SEL(a,bit))
        AstNodeUniop* fromp = VN_CAST(nodep->fromp()->unlinkFrBack(), NodeUniop);
	if (!fromp) nodep->v3fatalSrc("Called on non biop");
	AstNode* lsbp = nodep->lsbp()->unlinkFrBack();
	AstNode* widthp = nodep->widthp()->unlinkFrBack();
	//
	AstNode* bilhsp = fromp->lhsp()->unlinkFrBack();
	//
	fromp->lhsp(new AstSel(nodep->fileline(),
			       bilhsp, lsbp, widthp));
	fromp->dtypeFrom(nodep);
	nodep->replaceWith(fromp); nodep->deleteTree(); VL_DANGLING(nodep);
    }

    virtual void visit(AstAttrOf* nodep) {
	AstAttrOf* oldAttr = m_attrp;
	m_attrp = nodep;
        iterateChildren(nodep);
	m_attrp = oldAttr;
    }

    virtual void visit(AstArraySel* nodep) {
        iterateAndNextNull(nodep->bitp());
        if (VN_IS(nodep->bitp(), Const)
            && VN_IS(nodep->fromp(), VarRef)
	    // Need to make sure it's an array object so don't mis-allow a constant (bug509.)
            && VN_CAST(nodep->fromp(), VarRef)->varp()
            && VN_IS(VN_CAST(nodep->fromp(), VarRef)->varp()->valuep(), InitArray)) {
	    m_selp = nodep;  // Ask visit(AstVarRef) to replace varref with const
	}
        iterateAndNextNull(nodep->fromp());
        if (VN_IS(nodep->fromp(), Const)) {  // It did.
	    if (!m_selp) {
		nodep->v3error("Illegal assignment of constant to unpacked array");
	    } else {
		AstNode* fromp = nodep->fromp()->unlinkFrBack();
		nodep->replaceWith(fromp);
                if (VN_IS(fromp->dtypep()->skipRefp(), NodeArrayDType)) {
		    // Strip off array to find what array references
                    fromp->dtypeFrom(VN_CAST(fromp->dtypep()->skipRefp(), NodeArrayDType)->subDTypep());
		}
	    }
	}
	m_selp = NULL;
    }
    virtual void visit(AstNodeVarRef* nodep) {
        iterateChildren(nodep);
	if (!nodep->varp()) nodep->v3fatalSrc("Not linked");
	bool did=false;
	if (m_doV && nodep->varp()->valuep() && !m_attrp) {
	    //if (debug()) valuep->dumpTree(cout,"  visitvaref: ");
            iterateAndNextNull(nodep->varp()->valuep());  // May change nodep->varp()->valuep()
	    AstNode* valuep = nodep->varp()->valuep();
	    if (!nodep->lvalue()
		&& ((!m_params // Can reduce constant wires into equations
		     && m_doNConst
		     && v3Global.opt.oConst()
                     // Default value, not a "known" constant for this usage
                     && !(nodep->varp()->isFuncLocal()
                          && nodep->varp()->isNonOutput())
                     && !nodep->varp()->noSubst()
		     && !nodep->varp()->isSigPublic())
		    || nodep->varp()->isParam())) {
		if (operandConst(valuep)) {
                    const V3Number& num = VN_CAST(valuep, Const)->num();
                    //UINFO(2,"constVisit "<<cvtToHex(valuep)<<" "<<num<<endl);
		    replaceNum(nodep, num); VL_DANGLING(nodep);
		    did=true;
		}
                else if (m_selp && VN_IS(valuep, InitArray)) {
                    AstInitArray* initarp = VN_CAST(valuep, InitArray);
		    uint32_t bit = m_selp->bitConst();
		    int pos = 0;
		    AstNode* itemp = initarp->initsp();
		    for (; itemp; ++pos, itemp=itemp->nextp()) {
			uint32_t index = initarp->posIndex(pos);
			if (index == bit) break;
			if (index > bit) {
			    if (initarp->defaultp()) {
				itemp = initarp->defaultp();
			    } else {
				initarp->v3fatalSrc("Not enough values in array initalizement");
			    }
			}
		    }
                    if (VN_IS(itemp, Const)) {
                        const V3Number& num = VN_CAST(itemp, Const)->num();
                        //UINFO(2,"constVisit "<<cvtToHex(valuep)<<" "<<num<<endl);
			replaceNum(nodep, num); VL_DANGLING(nodep);
			did=true;
		    }
		}
                else if (m_params && VN_IS(valuep, InitArray) && VN_IS(nodep->backp(), Pin)) {
		    // Allow parameters to pass arrays
		    // Earlier recursion of InitArray made sure each array value is constant
		    // This exception is fairly fragile, i.e. doesn't support arrays of arrays or other stuff
		    AstNode* newp = valuep->cloneTree(false);
		    nodep->replaceWith(newp); nodep->deleteTree(); VL_DANGLING(nodep);
		    did = true;
		}
	    }
	}
	if (!did && m_required) {
	    nodep->v3error("Expecting expression to be constant, but variable isn't const: "<<nodep->varp()->prettyName());
	}
    }
    virtual void visit(AstEnumItemRef* nodep) {
        iterateChildren(nodep);
	if (!nodep->itemp()) nodep->v3fatalSrc("Not linked");
	bool did=false;
	if (nodep->itemp()->valuep()) {
	    //if (debug()) nodep->varp()->valuep()->dumpTree(cout,"  visitvaref: ");
            iterateAndNextNull(nodep->itemp()->valuep());
            if (AstConst* valuep = VN_CAST(nodep->itemp()->valuep(), Const)) {
		const V3Number& num = valuep->num();
		replaceNum(nodep, num); VL_DANGLING(nodep);
		did=true;
	    }
	}
	if (!did && m_required) {
	    nodep->v3error("Expecting expression to be constant, but variable isn't const: "<<nodep->itemp()->prettyName());
	}
    }

    // virtual void visit(AstCvtPackString* nodep) {
    // Not constant propagated (for today) because AstNodeMath::isOpaque is set
    // Someday if lower is constant, convert to quoted "string".

    bool onlySenItemInSenTree(AstNodeSenItem* nodep) {
	// Only one if it's not in a list
	return (!nodep->nextp() && nodep->backp()->nextp() != nodep);
    }
    virtual void visit(AstSenItem* nodep) {
        iterateChildren(nodep);
	if (m_doNConst
            && (VN_IS(nodep->sensp(), Const)
                || VN_IS(nodep->sensp(), EnumItemRef)
		|| (nodep->varrefp() && nodep->varrefp()->varp()->isParam()))) {
	    // Constants in sensitivity lists may be removed (we'll simplify later)
	    if (nodep->isClocked()) {  // A constant can never get a pos/negexge
		if (onlySenItemInSenTree(nodep)) {
		    nodep->replaceWith(new AstSenItem(nodep->fileline(), AstSenItem::Never()));
		    nodep->deleteTree(); VL_DANGLING(nodep);
		} else {
		    nodep->unlinkFrBack()->deleteTree(); VL_DANGLING(nodep);
		}
	    } else {  // Otherwise it may compute a result that needs to settle out
		nodep->replaceWith(new AstSenItem(nodep->fileline(), AstSenItem::Combo()));
		nodep->deleteTree(); VL_DANGLING(nodep);
	    }
        } else if (m_doNConst && VN_IS(nodep->sensp(), Not)) {
	    // V3Gate may propagate NOTs into clocks... Just deal with it
	    AstNode* sensp = nodep->sensp();
	    AstNode* lastSensp = sensp;
	    bool invert = false;
            while (VN_IS(lastSensp, Not)) {
                lastSensp = VN_CAST(lastSensp, Not)->lhsp();
		invert = !invert;
	    }
	    UINFO(8,"senItem(NOT...) "<<nodep<<" "<<invert<<endl);
	    if (invert) nodep->edgeType( nodep->edgeType().invert() );
            AstNodeVarRef* senvarp = VN_CAST(lastSensp->unlinkFrBack(), NodeVarRef);
	    if (!senvarp) sensp->v3fatalSrc("Non-varref sensitivity variable");
	    sensp->replaceWith(senvarp);
	    sensp->deleteTree(); VL_DANGLING(sensp);
	} else if (!m_doNConst  // Deal with later when doNConst missing
                   && (VN_IS(nodep->sensp(), EnumItemRef)
                       || VN_IS(nodep->sensp(), Const))) {
	} else if (nodep->isIllegal()) {  // Deal with later
	} else {
	    if (nodep->hasVar() && !nodep->varrefp()) nodep->v3fatalSrc("Null sensitivity variable");
	}
    }
    virtual void visit(AstSenGate* nodep) {
        iterateChildren(nodep);
        if (AstConst* constp = VN_CAST(nodep->rhsp(), Const)) {
	    if (constp->isZero()) {
		UINFO(4,"SENGATE(...,0)->NEVER"<<endl);
		if (onlySenItemInSenTree(nodep)) {
		    nodep->replaceWith(new AstSenItem(nodep->fileline(), AstSenItem::Never()));
		    nodep->deleteTree(); VL_DANGLING(nodep);
		} else {
		    nodep->unlinkFrBack()->deleteTree(); VL_DANGLING(nodep);
		}
	    } else {
		UINFO(4,"SENGATE(SENITEM,0)->ALWAYS SENITEM"<<endl);
		AstNode* senitemp = nodep->sensesp()->unlinkFrBack();
		nodep->replaceWith(senitemp);
		nodep->deleteTree(); VL_DANGLING(nodep);
	    }
	}
    }

    struct SenItemCmp {
        inline bool operator() (AstNodeSenItem* lhsp, AstNodeSenItem* rhsp) const {
	    if (lhsp->type() < rhsp->type()) return true;
	    if (lhsp->type() > rhsp->type()) return false;
            const AstSenItem* litemp = VN_CAST_CONST(lhsp, SenItem);
            const AstSenItem* ritemp = VN_CAST_CONST(rhsp, SenItem);
	    if (litemp && ritemp) {
		// Looks visually better if we keep sorted by name
		if (!litemp->varrefp() &&  ritemp->varrefp()) return true;
		if ( litemp->varrefp() && !ritemp->varrefp()) return false;
		if (litemp->varrefp() && ritemp->varrefp()) {
		    if (litemp->varrefp()->name() < ritemp->varrefp()->name()) return true;
		    if (litemp->varrefp()->name() > ritemp->varrefp()->name()) return false;
		    // But might be same name with different scopes
		    if (litemp->varrefp()->varScopep() < ritemp->varrefp()->varScopep()) return true;
		    if (litemp->varrefp()->varScopep() > ritemp->varrefp()->varScopep()) return false;
		    // Or rarely, different data types
		    if (litemp->varrefp()->dtypep() < ritemp->varrefp()->dtypep()) return true;
		    if (litemp->varrefp()->dtypep() > ritemp->varrefp()->dtypep()) return false;
		}
		// Sort by edge, AFTER variable, as we want multiple edges for same var adjacent
		// note the SenTree optimizer requires this order (more general first, less general last)
		if (litemp->edgeType() < ritemp->edgeType()) return true;
		if (litemp->edgeType() > ritemp->edgeType()) return false;
	    }
	    return false;
	}
    };

    virtual void visit(AstSenTree* nodep) {
        iterateChildren(nodep);
	if (m_doExpensive) {
	    //cout<<endl; nodep->dumpTree(cout,"ssin: ");
	    // Optimize ideas for the future:
	    //   SENTREE(... SENGATE(x,a), SENGATE(SENITEM(x),b) ...)  => SENGATE(x,OR(a,b))

	    //   SENTREE(... SENITEM(x),   SENGATE(SENITEM(x),*) ...)  => SENITEM(x)
	    // Do we need the SENITEM's to be identical?  No because we're
	    // ORing between them; we just need to insure that the result is at
	    // least as frequently activating.  So we simply
	    // SENGATE(SENITEM(x)) -> SENITEM(x), then let it collapse with the
	    // other SENITEM(x).
	    {
		AstUser4InUse	m_inuse4;
		// Mark x in SENITEM(x)
                for (AstNodeSenItem* senp = VN_CAST(nodep->sensesp(), NodeSenItem);
                     senp; senp=VN_CAST(senp->nextp(), NodeSenItem)) {
                    if (AstSenItem* itemp = VN_CAST(senp, SenItem)) {
			if (itemp->varrefp() && itemp->varrefp()->varScopep()) {
			    itemp->varrefp()->varScopep()->user4(1);
			}
		    }
		}
		// Find x in SENTREE(SENITEM(x))
                for (AstNodeSenItem* nextp, * senp = VN_CAST(nodep->sensesp(), NodeSenItem);
		     senp; senp=nextp) {
                    nextp=VN_CAST(senp->nextp(), NodeSenItem);
                    if (AstSenGate* gatep = VN_CAST(senp, SenGate)) {
                        if (AstSenItem* itemp = VN_CAST(gatep->sensesp(), SenItem)) {
			    if (itemp->varrefp() && itemp->varrefp()->varScopep()) {
				if (itemp->varrefp()->varScopep()->user4()) {
				    // Found, push this item up to the top
				    itemp->unlinkFrBack();
				    nodep->addSensesp(itemp);
				    gatep->unlinkFrBack()->deleteTree(); VL_DANGLING(gatep); VL_DANGLING(senp);
				}
			    }
			}
		    }
		}
	    }

	    // Sort the sensitivity names so "posedge a or b" and "posedge b or a" end up together.
	    // Also, remove duplicate assignments, and fold POS&NEGs into ANYEDGEs
	    // Make things a little faster; check first if we need a sort
            for (AstNodeSenItem* nextp, * senp = VN_CAST(nodep->sensesp(), NodeSenItem);
		 senp; senp=nextp) {
                nextp=VN_CAST(senp->nextp(), NodeSenItem);
		// cppcheck-suppress unassignedVariable  // cppcheck bug
		SenItemCmp cmp;
		if (nextp && !cmp(senp, nextp)) {
		    // Something's out of order, sort it
		    senp = NULL;
                    std::vector<AstNodeSenItem*> vec;
                    for (AstNodeSenItem* senp = VN_CAST(nodep->sensesp(), NodeSenItem);
                         senp; senp=VN_CAST(senp->nextp(), NodeSenItem)) {
			vec.push_back(senp);
		    }
		    stable_sort(vec.begin(), vec.end(), SenItemCmp());
                    for (std::vector<AstNodeSenItem*>::iterator it=vec.begin(); it!=vec.end(); ++it) {
			(*it)->unlinkFrBack();
		    }
                    for (std::vector<AstNodeSenItem*>::iterator it=vec.begin(); it!=vec.end(); ++it) {
			nodep->addSensesp(*it);
		    }
		    break;
		}
	    }

	    // Pass2, remove dup edges
            for (AstNodeSenItem* nextp, * senp = VN_CAST(nodep->sensesp(), NodeSenItem);
		 senp; senp=nextp) {
                nextp=VN_CAST(senp->nextp(), NodeSenItem);
		AstNodeSenItem* cmpp = nextp;
                AstSenItem* litemp = VN_CAST(senp, SenItem);
                AstSenItem* ritemp = VN_CAST(cmpp, SenItem);
		if (litemp && ritemp) {
		    if ((litemp->varrefp() && ritemp->varrefp() && litemp->varrefp()->sameGateTree(ritemp->varrefp()))
			|| (!litemp->varrefp() && !ritemp->varrefp())) {
			// We've sorted in the order ANY, BOTH, POS, NEG, so we don't need to try opposite orders
			if ((   litemp->edgeType()==AstEdgeType::ET_ANYEDGE)   // ANY  or {BOTH|POS|NEG} -> ANY
			    || (litemp->edgeType()==AstEdgeType::ET_BOTHEDGE)  // BOTH or {POS|NEG} -> BOTH
			    || (litemp->edgeType()==AstEdgeType::ET_POSEDGE    // POS  or NEG -> BOTH
				&& ritemp->edgeType()==AstEdgeType::ET_NEGEDGE)
			    || (litemp->edgeType()==ritemp->edgeType())	// Identical edges
			    ) {
			    // Fix edge of old node
			    if (litemp->edgeType()==AstEdgeType::ET_POSEDGE
				&& ritemp->edgeType()==AstEdgeType::ET_NEGEDGE)
				litemp->edgeType(AstEdgeType::ET_BOTHEDGE);
			    // Remove redundant node
			    ritemp->unlinkFrBack()->deleteTree(); VL_DANGLING(ritemp); VL_DANGLING(cmpp);
			    // Try to collapse again
			    nextp=litemp;
			}
		    }
		}
	    }
	    //nodep->dumpTree(cout,"ssou: ");
	}
    }

    //-----
    // Zero elimination
    virtual void visit(AstNodeAssign* nodep) {
        iterateChildren(nodep);
	if (m_doNConst && replaceNodeAssign(nodep)) return;
    }
    virtual void visit(AstAssignAlias* nodep) {
	// Don't perform any optimizations, keep the alias around
    }
    virtual void visit(AstAssignVarScope* nodep) {
	// Don't perform any optimizations, the node won't be linked yet
    }
    virtual void visit(AstAssignW* nodep) {
        iterateChildren(nodep);
	if (m_doNConst && replaceNodeAssign(nodep)) return;
        AstNodeVarRef* varrefp = VN_CAST(nodep->lhsp(), VarRef);  // Not VarXRef, as different refs may set different values to each hierarchy
	if (m_wremove && !m_params && m_doNConst
	    && m_modp && operandConst(nodep->rhsp())
            && !VN_CAST(nodep->rhsp(), Const)->num().isFourState()
	    && varrefp		// Don't do messes with BITREFs/ARRAYREFs
	    && !varrefp->varp()->valuep()  // Not already constified
	    && !varrefp->varScopep()) {	// Not scoped (or each scope may have different initial value)
	    // ASSIGNW (VARREF, const) -> INITIAL ( ASSIGN (VARREF, const) )
	    UINFO(4,"constAssignW "<<nodep<<endl);
	    // Make a initial assignment
	    AstNode* exprp = nodep->rhsp()->unlinkFrBack();
	    varrefp->unlinkFrBack();
	    AstInitial* newinitp
		= new AstInitial(nodep->fileline(),
				 new AstAssign(nodep->fileline(),
					       varrefp, exprp));
	    m_modp->addStmtp(newinitp);
	    nodep->unlinkFrBack()->deleteTree(); VL_DANGLING(nodep);
	    // Set the initial value right in the variable so we can constant propagate
	    AstNode* initvaluep = exprp->cloneTree(false);
	    varrefp->varp()->valuep(initvaluep);
	}
    }

    virtual void visit(AstNodeIf* nodep) {
        iterateChildren(nodep);
	if (m_doNConst) {
            if (const AstConst* constp = VN_CAST(nodep->condp(), Const)) {
		AstNode* keepp = NULL;
		if (constp->isZero()) {
		    UINFO(4,"IF(0,{any},{x}) => {x}: "<<nodep<<endl);
		    keepp = nodep->elsesp();
		} else {
		    UINFO(4,"IF(!0,{x},{any}) => {x}: "<<nodep<<endl);
		    keepp = nodep->ifsp();
		}
		if (keepp) {
		    keepp->unlinkFrBackWithNext();
		    nodep->replaceWith(keepp);
		} else {
		    nodep->unlinkFrBack();
		}
		nodep->deleteTree(); VL_DANGLING(nodep);
	    }
	    else if (!afterComment(nodep->ifsp()) && !afterComment(nodep->elsesp())) {
		// Empty block, remove it
		// Note if we support more C++ then there might be side effects in the condition itself
		nodep->unlinkFrBack()->deleteTree(); VL_DANGLING(nodep);
	    }
	    else if (!afterComment(nodep->ifsp())) {
		UINFO(4,"IF({x}) NULL {...} => IF(NOT{x}}: "<<nodep<<endl);
		AstNode* condp = nodep->condp();
		AstNode* elsesp = nodep->elsesp();
		condp->unlinkFrBackWithNext();
		elsesp->unlinkFrBackWithNext();
		if (nodep->ifsp()) { nodep->ifsp()->unlinkFrBackWithNext()->deleteTree(); }  // Must have been comment
		nodep->condp(new AstLogNot(condp->fileline(), condp));  // LogNot, as C++ optimization also possible
		nodep->addIfsp(elsesp);
	    }
            else if (((VN_IS(nodep->condp(), Not) && nodep->condp()->width()==1)
                      || VN_IS(nodep->condp(), LogNot))
		     && nodep->ifsp() && nodep->elsesp()) {
		UINFO(4,"IF(NOT {x})  => IF(x) swapped if/else"<<nodep<<endl);
                AstNode* condp = VN_CAST(nodep->condp(), Not)->lhsp()->unlinkFrBackWithNext();
		AstNode* ifsp = nodep->ifsp()->unlinkFrBackWithNext();
		AstNode* elsesp = nodep->elsesp()->unlinkFrBackWithNext();
		AstIf* ifp = new AstIf(nodep->fileline(), condp, elsesp, ifsp);
		ifp->branchPred(nodep->branchPred().invert());
		nodep->replaceWith(ifp);
		nodep->deleteTree(); VL_DANGLING(nodep);
	    }
	    else if (ifSameAssign(nodep)) {
		UINFO(4,"IF({a}) ASSIGN({b},{c}) else ASSIGN({b},{d}) => ASSIGN({b}, {a}?{c}:{d})"<<endl);
                AstNodeAssign* ifp   = VN_CAST(nodep->ifsp(), NodeAssign);
                AstNodeAssign* elsep = VN_CAST(nodep->elsesp(), NodeAssign);
		ifp->unlinkFrBack();
		AstNode* condp = nodep->condp()->unlinkFrBack();
		AstNode* truep = ifp->rhsp()->unlinkFrBack();
		AstNode* falsep = elsep->rhsp()->unlinkFrBack();
		ifp->rhsp(new AstCond(truep->fileline(),
				      condp, truep, falsep));
		nodep->replaceWith(ifp);
		nodep->deleteTree(); VL_DANGLING(nodep);
	    }
	    else if (0	// Disabled, as vpm assertions are faster without due to short-circuiting
		     && operandIfIf(nodep)) {
		UINFO(9,"IF({a}) IF({b}) => IF({a} && {b})"<<endl);
                AstNodeIf* lowerIfp = VN_CAST(nodep->ifsp(), NodeIf);
		AstNode* condp = nodep->condp()->unlinkFrBack();
		AstNode* lowerIfsp = lowerIfp->ifsp()->unlinkFrBackWithNext();
		AstNode* lowerCondp = lowerIfp->condp()->unlinkFrBackWithNext();
		nodep->condp(new AstLogAnd(lowerIfp->fileline(),
					   condp, lowerCondp));
		lowerIfp->replaceWith(lowerIfsp);
		lowerIfp->deleteTree(); VL_DANGLING(lowerIfp);
	    }
	    else if (operandBoolShift(nodep->condp())) {
		replaceBoolShift(nodep->condp());
	    }
	}
    }

    virtual void visit(AstDisplay* nodep) {
        // DISPLAY(SFORMAT(text1)),DISPLAY(SFORMAT(text2)) -> DISPLAY(SFORMAT(text1+text2))
        iterateChildren(nodep);
        if (stmtDisplayDisplay(nodep)) return;
    }
    bool stmtDisplayDisplay(AstDisplay* nodep) {
        // DISPLAY(SFORMAT(text1)),DISPLAY(SFORMAT(text2)) -> DISPLAY(SFORMAT(text1+text2))
        if (!m_modp) return false;  // Don't optimize under single statement
        if (!nodep->backp()) return false;
        AstDisplay* prevp = VN_CAST(nodep->backp(), Display);
        if (!prevp) return false;
        if (!((prevp->displayType() == nodep->displayType())
              || (prevp->displayType() == AstDisplayType::DT_WRITE
                  && nodep->displayType() == AstDisplayType::DT_DISPLAY)
              || (prevp->displayType() == AstDisplayType::DT_DISPLAY
                  && nodep->displayType() == AstDisplayType::DT_WRITE)))
            return false;
        if ((prevp->filep() && !nodep->filep())
            || (!prevp->filep() && nodep->filep())
            || !prevp->filep()->sameTree(nodep->filep())) return false;
        if (!prevp->fmtp() || prevp->fmtp()->nextp()
            || !nodep->fmtp() || nodep->fmtp()->nextp()) return false;
        // We don't merge scopeNames as might be different scopes (late in process)
        // We don't merge arguments as might need to later print warnings with right line numbers
        AstSFormatF* pformatp = prevp->fmtp();
        if (!pformatp || pformatp->exprsp() || pformatp->scopeNamep()) return false;
        AstSFormatF* nformatp = nodep->fmtp();
        if (!nformatp || nformatp->exprsp() || nformatp->scopeNamep()) return false;
        //
        UINFO(9,"DISPLAY(SF({a})) DISPLAY(SF({b})) -> DISPLAY(SF({a}+{b}))"<<endl);
        // Convert DT_DISPLAY to DT_WRITE as may allow later optimizations
        if (prevp->displayType() == AstDisplayType::DT_DISPLAY) {
            prevp->displayType(AstDisplayType::DT_WRITE);
            pformatp->text(pformatp->text()+"\n");
        }
        // We can't replace prev() as the edit tracking iterators will get confused.
        // So instead we edit the prev note itself.
        if (prevp->addNewline()) pformatp->text(pformatp->text()+"\n");
        pformatp->text(pformatp->text()+nformatp->text());
        if (!prevp->addNewline() && nodep->addNewline()) {
            pformatp->text(pformatp->text()+"\n");
        }
        nodep->unlinkFrBack()->deleteTree(); VL_DANGLING(nodep);
        return true;
    }
    virtual void visit(AstSFormatF* nodep) {
	// Substitute constants into displays.  The main point of this is to
	// simplify assertion methodologies which call functions with display's.
	// This eliminates a pile of wide temps, and makes the C a whole lot more readable.
        iterateChildren(nodep);
	bool anyconst = false;
	for (AstNode* argp = nodep->exprsp(); argp; argp=argp->nextp()) {
            if (VN_IS(argp, Const)) { anyconst=true; break; }
	}
	if (m_doNConst && anyconst) {
	    //UINFO(9,"  Display in  "<<nodep->text()<<endl);
            string newFormat;
            string fmt;
	    bool inPct = false;
	    AstNode* argp = nodep->exprsp();
	    string text = nodep->text();
	    for (string::const_iterator it = text.begin(); it!=text.end(); ++it) {
		char ch = *it;
		if (!inPct && ch=='%') {
		    inPct = true;
		    fmt = ch;
		} else if (inPct && (isdigit(ch) || ch=='.')) {
		    fmt += ch;
		} else if (inPct) {
		    inPct = false;
		    fmt += ch;
		    switch (tolower(ch)) {
		    case '%': break;  // %% - just output a %
		    case 'm': break;  // %m - auto insert "name"
		    case 'l': break;  // %l - auto insert "library"
		    default:  // Most operators, just move to next argument
			if (argp) {
			    AstNode* nextp=argp->nextp();
                            if (argp && VN_IS(argp, Const)) {  // Convert it
                                string out = VN_CAST(argp, Const)->num().displayed(nodep->fileline(), fmt);
				UINFO(9,"     DispConst: "<<fmt<<" -> "<<out<<"  for "<<argp<<endl);
				// fmt = out w/ replace % with %% as it must be literal.
				fmt = VString::quotePercent(out);
				argp->unlinkFrBack()->deleteTree(); VL_DANGLING(argp);
			    }
			    argp=nextp;
			}
			break;
		    } // switch
		    newFormat += fmt;
		} else {
		    newFormat += ch;
		}
	    }
	    if (newFormat != nodep->text()) {
		nodep->text(newFormat);
		UINFO(9,"  Display out "<<nodep<<endl);
	    }
	}
	if (!nodep->exprsp()
            && nodep->name().find('%') == string::npos
	    && !nodep->hidden()) {
	    // Just a simple constant string - the formatting is pointless
	    replaceConstString(nodep, nodep->name()); VL_DANGLING(nodep);
	}
    }

    virtual void visit(AstFuncRef* nodep) {
        iterateChildren(nodep);
	if (m_params) {  // Only parameters force us to do constant function call propagation
	    replaceWithSimulation(nodep);
	}
    }
    virtual void visit(AstArg* nodep) {
	// replaceWithSimulation on the Arg's parent FuncRef replaces these
        iterateChildren(nodep);
    }
    virtual void visit(AstWhile* nodep) {
        bool oldHasJumpGo = m_hasJumpGo;
        m_hasJumpGo = false;
        {
            iterateChildren(nodep);
        }
        bool thisWhileHasJumpGo = m_hasJumpGo;
        m_hasJumpGo = thisWhileHasJumpGo || oldHasJumpGo;
	if (m_doNConst) {
	    if (nodep->condp()->isZero()) {
		UINFO(4,"WHILE(0) => nop "<<nodep<<endl);
		if (nodep->precondsp()) nodep->replaceWith(nodep->precondsp());
		else nodep->unlinkFrBack();
		nodep->deleteTree(); VL_DANGLING(nodep);
	    }
            else if (nodep->condp()->isNeqZero()) {
                if (!thisWhileHasJumpGo) {
                    nodep->v3warn(INFINITELOOP, "Infinite loop (condition always true)");
                    nodep->fileline()->modifyWarnOff(V3ErrorCode::INFINITELOOP, true);  // Complain just once
                }
            }
	    else if (operandBoolShift(nodep->condp())) {
		replaceBoolShift(nodep->condp());
	    }
	}
    }
    virtual void visit(AstInitArray* nodep) {
	// Constant if all children are constant
        iterateChildren(nodep);
    }

    // These are converted by V3Param.  Don't constify as we don't want the from() VARREF to disappear, if any
    // If output of a presel didn't get consted, chances are V3Param didn't visit properly
    virtual void visit(AstNodePreSel* nodep) {}

    // Ignored, can eliminate early
    virtual void visit(AstSysIgnore* nodep) {
        iterateChildren(nodep);
	if (m_doNConst) {
	    nodep->unlinkFrBack()->deleteTree(); VL_DANGLING(nodep);
	}
    }

    // Simplify
    virtual void visit(AstBasicDType* nodep) {
        iterateChildren(nodep);
	nodep->cvtRangeConst();
    }

    //-----
    // Jump elimination

    virtual void visit(AstJumpGo* nodep) {
        iterateChildren(nodep);
        m_hasJumpGo = true;
	if (m_doExpensive) { nodep->labelp()->user4(true); }
    }

    virtual void visit(AstJumpLabel* nodep) {
	// Because JumpLabels disable many optimizations,
	// remove JumpLabels that are not pointed to by any AstJumpGos
	// Note this assumes all AstJumpGos are underneath the given label; V3Broken asserts this
        iterateChildren(nodep);
	// AstJumpGo's below here that point to this node will set user4
	if (m_doExpensive && !nodep->user4()) {
	    UINFO(4,"JUMPLABEL => unused "<<nodep<<endl);
	    AstNode* underp = NULL;
	    if (nodep->stmtsp()) underp = nodep->stmtsp()->unlinkFrBackWithNext();
	    if (underp) nodep->replaceWith(underp);
	    else nodep->unlinkFrBack();
	    nodep->deleteTree(); VL_DANGLING(nodep);
	}
    }

    //-----
    // Below lines are magic expressions processed by astgen
    //  TREE_SKIP_VISIT("AstNODETYPE")    # Rename normal visit to visitGen and don't iterate
    //-----

    TREE_SKIP_VISIT("ArraySel");

    //-----
    //  "AstNODETYPE {             # bracket not paren
    //                $accessor_name, ...
    //                             # .castFoo is the test VN_IS(object,Foo)
    //                             # ,, gets replaced with a , rather than &&
    //	             }" 	   # bracket not paren
    //    ,"what to call"
    //
    // Where "what_to_call" is:
    //		"function to call"
    //		"AstREPLACEMENT_TYPE{ $accessor }"
    //		"!   		# Print line number when matches, so can see operations
    //		"NEVER"		# Print error message
    //		"DONE"		# Process of matching did the transform already

    // In the future maybe support more complicated match & replace:
    //   ("AstOr  {%a, AstAnd{AstNot{%b}, %c}} if %a.width1 if %a==%b",	"AstOr{%a,%c}; %b.delete");
    // Lhs/rhs would be implied; for non math operations you'd need $lhsp etc.

    // Lint Checks
    //    v--- *1* These ops are always first, as we warn before replacing
    //    v--- *V* This op is a verilog op, only in m_doV mode
    //    v--- *C* This op works on all constant children, allowed in m_doConst mode
    //    v--- *S* This op specifies a type should use short-circuting of its lhs op

    TREEOP1("AstSel{warnSelect(nodep)}",	"NEVER");
    // Generic constants on both side.  Do this first to avoid other replacements
    TREEOPC("AstNodeBiop {$lhsp.castConst, $rhsp.castConst}",  "replaceConst(nodep)");
    TREEOPC("AstNodeUniop{$lhsp.castConst, !nodep->isOpaque()}",  "replaceConst(nodep)");
    // Zero on one side or the other
    TREEOP ("AstAdd   {$lhsp.isZero, $rhsp}",	"replaceWRhs(nodep)");
    TREEOP ("AstAnd   {$lhsp.isZero, $rhsp, isTPure($rhsp)}",	"replaceZero(nodep)");  // Can't use replaceZeroChkPure as we make this pattern in ChkPure
    // This visit function here must allow for short-circuiting.
    TREEOPS("AstLogAnd   {$lhsp.isZero}",	"replaceZero(nodep)");
    TREEOP ("AstLogAnd{$lhsp.isZero, $rhsp}",	"replaceZero(nodep)");
    // This visit function here must allow for short-circuiting.
    TREEOPS("AstLogOr   {$lhsp.isOne}",		"replaceNum(nodep, 1)");
    TREEOP ("AstLogOr {$lhsp.isZero, $rhsp}",	"replaceWRhs(nodep)");
    TREEOP ("AstDiv   {$lhsp.isZero, $rhsp}",	"replaceZeroChkPure(nodep,$rhsp)");
    TREEOP ("AstDivS  {$lhsp.isZero, $rhsp}",	"replaceZeroChkPure(nodep,$rhsp)");
    TREEOP ("AstMul   {$lhsp.isZero, $rhsp}",	"replaceZeroChkPure(nodep,$rhsp)");
    TREEOP ("AstMulS  {$lhsp.isZero, $rhsp}",	"replaceZeroChkPure(nodep,$rhsp)");
    TREEOP ("AstPow   {$rhsp.isZero}",		"replaceNum(nodep, 1)");  // Overrides lhs zero rule
    TREEOP ("AstPowSS {$rhsp.isZero}",		"replaceNum(nodep, 1)");  // Overrides lhs zero rule
    TREEOP ("AstPowSU {$rhsp.isZero}",		"replaceNum(nodep, 1)");  // Overrides lhs zero rule
    TREEOP ("AstPowUS {$rhsp.isZero}",		"replaceNum(nodep, 1)");  // Overrides lhs zero rule
    TREEOP ("AstPow   {$lhsp.isZero, !$rhsp.isZero}",	"replaceZeroChkPure(nodep,$rhsp)");
    TREEOP ("AstPowSU {$lhsp.isZero, !$rhsp.isZero}",	"replaceZeroChkPure(nodep,$rhsp)");
    TREEOP ("AstPowUS {$lhsp.isZero, !$rhsp.isZero}",	"replaceZeroChkPure(nodep,$rhsp)");
    TREEOP ("AstPowSU {$lhsp.isZero, !$rhsp.isZero}",	"replaceZeroChkPure(nodep,$rhsp)");
    TREEOP ("AstOr    {$lhsp.isZero, $rhsp}",	"replaceWRhs(nodep)");
    TREEOP ("AstShiftL{$lhsp.isZero, $rhsp}",	"replaceZeroChkPure(nodep,$rhsp)");
    TREEOP ("AstShiftR{$lhsp.isZero, $rhsp}",	"replaceZeroChkPure(nodep,$rhsp)");
    TREEOP ("AstShiftRS{$lhsp.isZero, $rhsp}",	"replaceZeroChkPure(nodep,$rhsp)");
    TREEOP ("AstXor   {$lhsp.isZero, $rhsp}",	"replaceWRhs(nodep)");
    TREEOP ("AstXnor  {$lhsp.isZero, $rhsp}",	"AstNot{$rhsp}");
    TREEOP ("AstSub   {$lhsp.isZero, $rhsp}",	"AstNegate{$rhsp}");
    TREEOP ("AstAdd   {$lhsp, $rhsp.isZero}",	"replaceWLhs(nodep)");
    TREEOP ("AstAnd   {$lhsp, $rhsp.isZero}",	"replaceZeroChkPure(nodep,$lhsp)");
    TREEOP ("AstLogAnd{$lhsp, $rhsp.isZero}",	"replaceZeroChkPure(nodep,$lhsp)");
    TREEOP ("AstLogOr {$lhsp, $rhsp.isZero}",	"replaceWLhs(nodep)");
    TREEOP ("AstMul   {$lhsp, $rhsp.isZero}",	"replaceZeroChkPure(nodep,$lhsp)");
    TREEOP ("AstMulS  {$lhsp, $rhsp.isZero}",	"replaceZeroChkPure(nodep,$lhsp)");
    TREEOP ("AstOr    {$lhsp, $rhsp.isZero}",	"replaceWLhs(nodep)");
    TREEOP ("AstShiftL{$lhsp, $rhsp.isZero}",	"replaceWLhs(nodep)");
    TREEOP ("AstShiftR{$lhsp, $rhsp.isZero}",	"replaceWLhs(nodep)");
    TREEOP ("AstShiftRS{$lhsp, $rhsp.isZero}",	"replaceWLhs(nodep)");
    TREEOP ("AstSub   {$lhsp, $rhsp.isZero}",	"replaceWLhs(nodep)");
    TREEOP ("AstXor   {$lhsp, $rhsp.isZero}",	"replaceWLhs(nodep)");
    TREEOP ("AstXnor  {$lhsp, $rhsp.isZero}",	"AstNot{$lhsp}");
    // Non-zero on one side or the other
    TREEOP ("AstAnd   {$lhsp.isAllOnes, $rhsp}",	"replaceWRhs(nodep)");
    TREEOP ("AstLogAnd{$lhsp.isNeqZero, $rhsp}",	"replaceWRhs(nodep)");
    TREEOP ("AstOr    {$lhsp.isAllOnes, $rhsp, isTPure($rhsp)}",	"replaceWLhs(nodep)"); //->allOnes
    TREEOP ("AstLogOr {$lhsp.isNeqZero, $rhsp}",	"replaceNum(nodep,1)");
    TREEOP ("AstAnd   {$lhsp, $rhsp.isAllOnes}",	"replaceWLhs(nodep)");
    TREEOP ("AstLogAnd{$lhsp, $rhsp.isNeqZero}",	"replaceWLhs(nodep)");
    TREEOP ("AstOr    {$lhsp, $rhsp.isAllOnes, isTPure($lhsp)}",	"replaceWRhs(nodep)"); //->allOnes
    TREEOP ("AstLogOr {$lhsp, $rhsp.isNeqZero, isTPure($lhsp)}",	"replaceNum(nodep,1)");
    TREEOP ("AstXor   {$lhsp.isAllOnes, $rhsp}",	"AstNot{$rhsp}");
    TREEOP ("AstXnor  {$lhsp.isAllOnes, $rhsp}",	"replaceWRhs(nodep)");
    TREEOP ("AstMul   {$lhsp.isOne, $rhsp}",	"replaceWRhs(nodep)");
    TREEOP ("AstMulS  {$lhsp.isOne, $rhsp}",	"replaceWRhs(nodep)");
    TREEOP ("AstDiv   {$lhsp, $rhsp.isOne}",	"replaceWLhs(nodep)");
    TREEOP ("AstDivS  {$lhsp, $rhsp.isOne}",	"replaceWLhs(nodep)");
    TREEOP ("AstMul   {operandIsPowTwo($lhsp), $rhsp}",	"replaceMulShift(nodep)");  // a*2^n -> a<<n
    TREEOP ("AstDiv   {$lhsp, operandIsPowTwo($rhsp)}",	"replaceDivShift(nodep)");  // a/2^n -> a>>n
    TREEOP ("AstPow   {operandIsTwo($lhsp), $rhsp}",	"replacePowShift(nodep)");  // 2**a == 1<<a
    TREEOP ("AstSub   {$lhsp.castAdd, operandSubAdd(nodep)}", "AstAdd{AstSub{$lhsp->castAdd()->lhsp(),$rhsp}, $lhsp->castAdd()->rhsp()}"); // ((a+x)-y) -> (a+(x-y))
    // Trinary ops
    // Note V3Case::Sel requires Cond to always be conditionally executed in C to prevent core dump!
    TREEOP ("AstNodeCond{$condp.isZero,       $expr1p, $expr2p}", "replaceWChild(nodep,$expr2p)");
    TREEOP ("AstNodeCond{$condp.isNeqZero,    $expr1p, $expr2p}", "replaceWChild(nodep,$expr1p)");
    TREEOPC("AstNodeCond{$condp.isZero,       $expr1p.castConst, $expr2p.castConst}", "replaceWChild(nodep,$expr2p)");
    TREEOPC("AstNodeCond{$condp.isNeqZero,    $expr1p.castConst, $expr2p.castConst}", "replaceWChild(nodep,$expr1p)");
    TREEOP ("AstNodeCond{$condp, operandsSame($expr1p,,$expr2p)}","replaceWChild(nodep,$expr1p)");
    // This visit function here must allow for short-circuiting.
    TREEOPS("AstCond {$lhsp.isZero}",		"replaceWIteratedThs(nodep)");
    TREEOPS("AstCond {$lhsp.isNeqZero}",	"replaceWIteratedRhs(nodep)");
    TREEOP ("AstCond{$condp.castNot,       $expr1p, $expr2p}", "AstCond{$condp->op1p(), $expr2p, $expr1p}");
    TREEOP ("AstNodeCond{$condp.width1, $expr1p.width1,   $expr1p.isAllOnes, $expr2p}", "AstLogOr {$condp, $expr2p}");  // a?1:b == a||b
    TREEOP ("AstNodeCond{$condp.width1, $expr1p.width1,   $expr1p,    $expr2p.isZero}", "AstLogAnd{$condp, $expr1p}");  // a?b:0 == a&&b
    TREEOP ("AstNodeCond{$condp.width1, $expr1p.width1,   $expr1p, $expr2p.isAllOnes}", "AstLogOr {AstNot{$condp}, $expr1p}");  // a?b:1 == ~a||b
    TREEOP ("AstNodeCond{$condp.width1, $expr1p.width1,   $expr1p.isZero,    $expr2p}", "AstLogAnd{AstNot{$condp}, $expr2p}");  // a?0:b == ~a&&b
    TREEOP ("AstNodeCond{!$condp.width1, operandBoolShift(nodep->condp())}", "replaceBoolShift(nodep->condp())");
    // Prefer constants on left, since that often needs a shift, it lets constant red remove the shift
    TREEOP ("AstNodeBiCom{!$lhsp.castConst, $rhsp.castConst}",	"swapSides(nodep)");
    TREEOP ("AstNodeBiComAsv{operandAsvConst(nodep)}",	"replaceAsv(nodep)");
    TREEOP ("AstNodeBiComAsv{operandAsvSame(nodep)}",	"replaceAsv(nodep)");
    TREEOP ("AstNodeBiComAsv{operandAsvLUp(nodep)}",	"replaceAsvLUp(nodep)");
    TREEOP ("AstNodeBiComAsv{operandAsvRUp(nodep)}",	"replaceAsvRUp(nodep)");
    TREEOP ("AstLt   {!$lhsp.castConst,$rhsp.castConst}",	"AstGt  {$rhsp,$lhsp}");
    TREEOP ("AstLtS  {!$lhsp.castConst,$rhsp.castConst}",	"AstGtS {$rhsp,$lhsp}");
    TREEOP ("AstLte  {!$lhsp.castConst,$rhsp.castConst}",	"AstGte {$rhsp,$lhsp}");
    TREEOP ("AstLteS {!$lhsp.castConst,$rhsp.castConst}",	"AstGteS{$rhsp,$lhsp}");
    TREEOP ("AstGt   {!$lhsp.castConst,$rhsp.castConst}",	"AstLt  {$rhsp,$lhsp}");
    TREEOP ("AstGtS  {!$lhsp.castConst,$rhsp.castConst}",	"AstLtS {$rhsp,$lhsp}");
    TREEOP ("AstGte  {!$lhsp.castConst,$rhsp.castConst}",	"AstLte {$rhsp,$lhsp}");
    TREEOP ("AstGteS {!$lhsp.castConst,$rhsp.castConst}",	"AstLteS{$rhsp,$lhsp}");
    //    v--- *1* as These ops are always first, as we warn before replacing
    TREEOP1("AstLt   {$lhsp, $rhsp.isZero}",		"replaceNumSigned(nodep,0)");
    TREEOP1("AstGte  {$lhsp, $rhsp.isZero}",		"replaceNumSigned(nodep,1)");
    TREEOP1("AstGt   {$lhsp.isZero, $rhsp}",		"replaceNumSigned(nodep,0)");
    TREEOP1("AstLte  {$lhsp.isZero, $rhsp}",		"replaceNumSigned(nodep,1)");
    TREEOP1("AstGt   {$lhsp, $rhsp.isAllOnes, $lhsp->width()==$rhsp->width()}",  "replaceNumLimited(nodep,0)");
    TREEOP1("AstLte  {$lhsp, $rhsp.isAllOnes, $lhsp->width()==$rhsp->width()}",  "replaceNumLimited(nodep,1)");
    TREEOP1("AstLt   {$lhsp.isAllOnes, $rhsp, $lhsp->width()==$rhsp->width()}",  "replaceNumLimited(nodep,0)");
    TREEOP1("AstGte  {$lhsp.isAllOnes, $rhsp, $lhsp->width()==$rhsp->width()}",  "replaceNumLimited(nodep,1)");
    // Two level bubble pushing
    TREEOP ("AstNot   {$lhsp.castNot,  $lhsp->width()==VN_CAST($lhsp,,Not)->lhsp()->width()}", "replaceWChild(nodep, $lhsp->op1p())");  // NOT(NOT(x))->x
    TREEOP ("AstLogNot{$lhsp.castLogNot}",		"replaceWChild(nodep, $lhsp->op1p())");  // LOGNOT(LOGNOT(x))->x
    TREEOPV("AstNot   {$lhsp.castEqCase, $lhsp.width1}","AstNeqCase{$lhsp->op1p(),$lhsp->op2p()}");
    TREEOP ("AstLogNot{$lhsp.castEqCase}",		"AstNeqCase{$lhsp->op1p(),$lhsp->op2p()}");
    TREEOPV("AstNot   {$lhsp.castNeqCase, $lhsp.width1}","AstEqCase {$lhsp->op1p(),$lhsp->op2p()}");
    TREEOP ("AstLogNot{$lhsp.castNeqCase}",		"AstEqCase {$lhsp->op1p(),$lhsp->op2p()}");
    TREEOPV("AstNot   {$lhsp.castEqWild, $lhsp.width1}","AstNeqWild{$lhsp->op1p(),$lhsp->op2p()}");
    TREEOP ("AstLogNot{$lhsp.castEqWild}",		"AstNeqWild{$lhsp->op1p(),$lhsp->op2p()}");
    TREEOPV("AstNot   {$lhsp.castNeqWild, $lhsp.width1}","AstEqWild {$lhsp->op1p(),$lhsp->op2p()}");
    TREEOP ("AstLogNot{$lhsp.castNeqWild}",		"AstEqWild {$lhsp->op1p(),$lhsp->op2p()}");
    TREEOPV("AstNot   {$lhsp.castEq, $lhsp.width1}",	"AstNeq {$lhsp->op1p(),$lhsp->op2p()}");
    TREEOP ("AstLogNot{$lhsp.castEq}",			"AstNeq {$lhsp->op1p(),$lhsp->op2p()}");
    TREEOPV("AstNot   {$lhsp.castNeq, $lhsp.width1}",	"AstEq  {$lhsp->op1p(),$lhsp->op2p()}");
    TREEOP ("AstLogNot{$lhsp.castNeq}",			"AstEq  {$lhsp->op1p(),$lhsp->op2p()}");
    TREEOPV("AstNot   {$lhsp.castLt, $lhsp.width1}",	"AstGte {$lhsp->op1p(),$lhsp->op2p()}");
    TREEOP ("AstLogNot{$lhsp.castLt}",			"AstGte {$lhsp->op1p(),$lhsp->op2p()}");
    TREEOPV("AstNot   {$lhsp.castLtS, $lhsp.width1}",	"AstGteS{$lhsp->op1p(),$lhsp->op2p()}");
    TREEOP ("AstLogNot{$lhsp.castLtS}",			"AstGteS{$lhsp->op1p(),$lhsp->op2p()}");
    TREEOPV("AstNot   {$lhsp.castLte, $lhsp.width1}",	"AstGt  {$lhsp->op1p(),$lhsp->op2p()}");
    TREEOP ("AstLogNot{$lhsp.castLte}",			"AstGt  {$lhsp->op1p(),$lhsp->op2p()}");
    TREEOPV("AstNot   {$lhsp.castLteS, $lhsp.width1}",	"AstGtS {$lhsp->op1p(),$lhsp->op2p()}");
    TREEOP ("AstLogNot{$lhsp.castLteS}",		"AstGtS {$lhsp->op1p(),$lhsp->op2p()}");
    TREEOPV("AstNot   {$lhsp.castGt, $lhsp.width1}",	"AstLte {$lhsp->op1p(),$lhsp->op2p()}");
    TREEOP ("AstLogNot{$lhsp.castGt}",			"AstLte {$lhsp->op1p(),$lhsp->op2p()}");
    TREEOPV("AstNot   {$lhsp.castGtS, $lhsp.width1}",	"AstLteS{$lhsp->op1p(),$lhsp->op2p()}");
    TREEOP ("AstLogNot{$lhsp.castGtS}",			"AstLteS{$lhsp->op1p(),$lhsp->op2p()}");
    TREEOPV("AstNot   {$lhsp.castGte, $lhsp.width1}",	"AstLt  {$lhsp->op1p(),$lhsp->op2p()}");
    TREEOP ("AstLogNot{$lhsp.castGte}",			"AstLt  {$lhsp->op1p(),$lhsp->op2p()}");
    TREEOPV("AstNot   {$lhsp.castGteS, $lhsp.width1}",	"AstLtS {$lhsp->op1p(),$lhsp->op2p()}");
    TREEOP ("AstLogNot{$lhsp.castGteS}",		"AstLtS {$lhsp->op1p(),$lhsp->op2p()}");
    // Not common, but avoids compiler warnings about over shifting
    TREEOP ("AstShiftL{operandHugeShiftL(nodep)}",	"replaceZero(nodep)");
    TREEOP ("AstShiftR{operandHugeShiftR(nodep)}",	"replaceZero(nodep)");
    TREEOP ("AstShiftL{operandShiftOp(nodep)}",		"replaceShiftOp(nodep)");
    TREEOP ("AstShiftR{operandShiftOp(nodep)}",		"replaceShiftOp(nodep)");
    TREEOP ("AstShiftL{operandShiftShift(nodep)}",	"replaceShiftShift(nodep)");
    TREEOP ("AstShiftR{operandShiftShift(nodep)}",	"replaceShiftShift(nodep)");
    TREEOP ("AstWordSel{operandWordOOB(nodep)}",	"replaceZero(nodep)");
    // Compress out EXTENDs to appease loop unroller
    TREEOPV("AstEq    {$rhsp.castExtend,operandBiExtendConstShrink(nodep)}",	"DONE");
    TREEOPV("AstNeq   {$rhsp.castExtend,operandBiExtendConstShrink(nodep)}",	"DONE");
    TREEOPV("AstGt    {$rhsp.castExtend,operandBiExtendConstShrink(nodep)}",	"DONE");
    TREEOPV("AstGte   {$rhsp.castExtend,operandBiExtendConstShrink(nodep)}",	"DONE");
    TREEOPV("AstLt    {$rhsp.castExtend,operandBiExtendConstShrink(nodep)}",	"DONE");
    TREEOPV("AstLte   {$rhsp.castExtend,operandBiExtendConstShrink(nodep)}",	"DONE");
    TREEOPV("AstEq    {$rhsp.castExtend,operandBiExtendConstOver(nodep)}",	"replaceZero(nodep)");
    TREEOPV("AstNeq   {$rhsp.castExtend,operandBiExtendConstOver(nodep)}",	"replaceNum(nodep,1)");
    TREEOPV("AstGt    {$rhsp.castExtend,operandBiExtendConstOver(nodep)}",	"replaceNum(nodep,1)");
    TREEOPV("AstGte   {$rhsp.castExtend,operandBiExtendConstOver(nodep)}",	"replaceNum(nodep,1)");
    TREEOPV("AstLt    {$rhsp.castExtend,operandBiExtendConstOver(nodep)}",	"replaceZero(nodep)");
    TREEOPV("AstLte   {$rhsp.castExtend,operandBiExtendConstOver(nodep)}",	"replaceZero(nodep)");
    // Identical operands on both sides
    // AstLogAnd/AstLogOr already converted to AstAnd/AstOr for these rules
    // AstAdd->ShiftL(#,1) but uncommon
    TREEOP ("AstAnd    {operandsSame($lhsp,,$rhsp)}",	"replaceWLhs(nodep)");
    TREEOP ("AstChangeXor{operandsSame($lhsp,,$rhsp)}",	"replaceZero(nodep)");
    TREEOP ("AstDiv    {operandsSame($lhsp,,$rhsp)}",	"replaceNum(nodep,1)");
    TREEOP ("AstDivS   {operandsSame($lhsp,,$rhsp)}",	"replaceNum(nodep,1)");
    TREEOP ("AstOr     {operandsSame($lhsp,,$rhsp)}",	"replaceWLhs(nodep)");
    TREEOP ("AstSub    {operandsSame($lhsp,,$rhsp)}",	"replaceZero(nodep)");
    TREEOP ("AstXnor   {operandsSame($lhsp,,$rhsp)}",	"replaceAllOnes(nodep)");
    TREEOP ("AstXor    {operandsSame($lhsp,,$rhsp)}",	"replaceZero(nodep)");
    TREEOP ("AstEq     {operandsSame($lhsp,,$rhsp)}",	"replaceNum(nodep,1)");  // We let X==X -> 1, although in a true 4-state sim it's X.
    TREEOP ("AstEqD    {operandsSame($lhsp,,$rhsp)}",	"replaceNum(nodep,1)");  // We let X==X -> 1, although in a true 4-state sim it's X.
    TREEOP ("AstEqN    {operandsSame($lhsp,,$rhsp)}",	"replaceNum(nodep,1)");  // We let X==X -> 1, although in a true 4-state sim it's X.
    TREEOP ("AstEqCase {operandsSame($lhsp,,$rhsp)}",	"replaceNum(nodep,1)");
    TREEOP ("AstEqWild {operandsSame($lhsp,,$rhsp)}",	"replaceNum(nodep,1)");
    TREEOP ("AstGt     {operandsSame($lhsp,,$rhsp)}",	"replaceZero(nodep)");
    TREEOP ("AstGtD    {operandsSame($lhsp,,$rhsp)}",	"replaceZero(nodep)");
    TREEOP ("AstGtN    {operandsSame($lhsp,,$rhsp)}",	"replaceZero(nodep)");
    TREEOP ("AstGtS    {operandsSame($lhsp,,$rhsp)}",	"replaceZero(nodep)");
    TREEOP ("AstGte    {operandsSame($lhsp,,$rhsp)}",	"replaceNum(nodep,1)");
    TREEOP ("AstGteD   {operandsSame($lhsp,,$rhsp)}",	"replaceNum(nodep,1)");
    TREEOP ("AstGteN   {operandsSame($lhsp,,$rhsp)}",	"replaceNum(nodep,1)");
    TREEOP ("AstGteS   {operandsSame($lhsp,,$rhsp)}",	"replaceNum(nodep,1)");
    TREEOP ("AstLt     {operandsSame($lhsp,,$rhsp)}",	"replaceZero(nodep)");
    TREEOP ("AstLtD    {operandsSame($lhsp,,$rhsp)}",	"replaceZero(nodep)");
    TREEOP ("AstLtN    {operandsSame($lhsp,,$rhsp)}",	"replaceZero(nodep)");
    TREEOP ("AstLtS    {operandsSame($lhsp,,$rhsp)}",	"replaceZero(nodep)");
    TREEOP ("AstLte    {operandsSame($lhsp,,$rhsp)}",	"replaceNum(nodep,1)");
    TREEOP ("AstLteD   {operandsSame($lhsp,,$rhsp)}",	"replaceNum(nodep,1)");
    TREEOP ("AstLteN   {operandsSame($lhsp,,$rhsp)}",	"replaceNum(nodep,1)");
    TREEOP ("AstLteS   {operandsSame($lhsp,,$rhsp)}",	"replaceNum(nodep,1)");
    TREEOP ("AstNeq    {operandsSame($lhsp,,$rhsp)}",	"replaceZero(nodep)");
    TREEOP ("AstNeqD   {operandsSame($lhsp,,$rhsp)}",	"replaceZero(nodep)");
    TREEOP ("AstNeqN   {operandsSame($lhsp,,$rhsp)}",	"replaceZero(nodep)");
    TREEOP ("AstNeqCase{operandsSame($lhsp,,$rhsp)}",	"replaceZero(nodep)");
    TREEOP ("AstNeqWild{operandsSame($lhsp,,$rhsp)}",	"replaceZero(nodep)");
    TREEOP ("AstLogAnd {operandsSame($lhsp,,$rhsp), $lhsp.width1}",	"replaceWLhs(nodep)");
    TREEOP ("AstLogOr  {operandsSame($lhsp,,$rhsp), $lhsp.width1}",	"replaceWLhs(nodep)");
    ///=== Verilog operators
    // Comparison against 1'b0/1'b1; must be careful about widths.
    // These use Not, so must be Verilog only
    TREEOPV("AstEq    {$rhsp.width1, $lhsp.isZero,    $rhsp}",	"AstNot{$rhsp}");
    TREEOPV("AstEq    {$lhsp.width1, $lhsp, $rhsp.isZero}",	"AstNot{$lhsp}");
    TREEOPV("AstEq    {$rhsp.width1, $lhsp.isAllOnes, $rhsp}",	"replaceWRhs(nodep)");
    TREEOPV("AstEq    {$lhsp.width1, $lhsp, $rhsp.isAllOnes}",	"replaceWLhs(nodep)");
    TREEOPV("AstNeq   {$rhsp.width1, $lhsp.isZero,    $rhsp}",	"replaceWRhs(nodep)");
    TREEOPV("AstNeq   {$lhsp.width1, $lhsp, $rhsp.isZero}",	"replaceWLhs(nodep)");
    TREEOPV("AstNeq   {$rhsp.width1, $lhsp.isAllOnes, $rhsp}",	"AstNot{$rhsp}");
    TREEOPV("AstNeq   {$lhsp.width1, $lhsp, $rhsp.isAllOnes}",	"AstNot{$lhsp}");
    TREEOPV("AstLt    {$rhsp.width1, $lhsp.isZero,    $rhsp}",	"replaceWRhs(nodep)");  // Because not signed #s
    TREEOPV("AstGt    {$lhsp.width1, $lhsp, $rhsp.isZero}",	"replaceWLhs(nodep)");  // Because not signed #s
    // Useful for CONDs added around ARRAYSEL's in V3Case step
    TREEOPV("AstLte   {$lhsp->width()==$rhsp->width(), $rhsp.isAllOnes}", "replaceNum(nodep,1)");
    // Simplify reduction operators
    // This also gets &{...,0,....} => const 0  (Common for unused_ok signals)
    TREEOPV("AstRedAnd{$lhsp, $lhsp.width1}",	"replaceWLhs(nodep)");
    TREEOPV("AstRedOr {$lhsp, $lhsp.width1}",	"replaceWLhs(nodep)");
    TREEOPV("AstRedXor{$lhsp, $lhsp.width1}",	"replaceWLhs(nodep)");
    TREEOPV("AstRedAnd{$lhsp.castConcat}",	"AstAnd{AstRedAnd{$lhsp->castConcat()->lhsp()}, AstRedAnd{$lhsp->castConcat()->rhsp()}}");    // &{a,b} => {&a}&{&b}
    TREEOPV("AstRedOr {$lhsp.castConcat}",	"AstOr {AstRedOr {$lhsp->castConcat()->lhsp()}, AstRedOr {$lhsp->castConcat()->rhsp()}}");    // |{a,b} => {|a}|{|b}
    TREEOPV("AstRedXor{$lhsp.castConcat}",	"AstXor{AstRedXor{$lhsp->castConcat()->lhsp()}, AstRedXor{$lhsp->castConcat()->rhsp()}}");    // ^{a,b} => {^a}^{^b}
    TREEOPV("AstRedAnd{$lhsp.castExtend, $lhsp->width() > VN_CAST($lhsp,,Extend)->lhsp()->width()}", "replaceZero(nodep)");  // &{0,...} => 0  Prevents compiler limited range error
    TREEOPV("AstRedOr {$lhsp.castExtend}",	"AstRedOr {$lhsp->castExtend()->lhsp()}");
    TREEOPV("AstRedXor{$lhsp.castExtend}",	"AstRedXor{$lhsp->castExtend()->lhsp()}");
    TREEOPV("AstOneHot{$lhsp.width1}",		"replaceWLhs(nodep)");
    TREEOPV("AstOneHot0{$lhsp.width1}",		"replaceNum(nodep,1)");
    // Binary AND/OR is faster than logical and/or (usually)
    TREEOPV("AstLogAnd{$lhsp.width1, $rhsp.width1, isTPure($lhsp), isTPure($rhsp)}", "AstAnd{$lhsp,$rhsp}");
    TREEOPV("AstLogOr {$lhsp.width1, $rhsp.width1, isTPure($lhsp), isTPure($rhsp)}", "AstOr{$lhsp,$rhsp}");
    TREEOPV("AstLogNot{$lhsp.width1, isTPure($lhsp)}",	"AstNot{$lhsp}");
    // CONCAT(CONCAT({a},{b}),{c}) -> CONCAT({a},CONCAT({b},{c}))
    // CONCAT({const},CONCAT({const},{c})) -> CONCAT((constifiedCONC{const|const},{c}))
    TREEOPV("AstConcat{operandConcatMove(nodep)}",	"moveConcat(nodep)");
    TREEOPV("AstConcat{$lhsp.isZero, $rhsp}",		"replaceExtend(nodep, nodep->rhsp())");
    // CONCAT(a[1],a[0]) -> a[1:0]
    TREEOPV("AstConcat{$lhsp.castSel, $rhsp.castSel, ifAdjacentSel(VN_CAST($lhsp,,Sel),,VN_CAST($rhsp,,Sel))}",  "replaceConcatSel(nodep)");
    TREEOPV("AstConcat{ifConcatMergeableBiop($lhsp), concatMergeable($lhsp,,$rhsp)}", "replaceConcatMerge(nodep)");
    // Common two-level operations that can be simplified
    TREEOP ("AstAnd {$lhsp.castOr, $rhsp.castOr, operandAndOrSame(nodep)}",	"replaceAndOr(nodep)");
    TREEOP ("AstOr  {$lhsp.castAnd,$rhsp.castAnd,operandAndOrSame(nodep)}",	"replaceAndOr(nodep)");
    TREEOP ("AstOr  {matchOrAndNot(nodep)}",		"DONE");
    TREEOP ("AstAnd {operandShiftSame(nodep)}",		"replaceShiftSame(nodep)");
    TREEOP ("AstOr  {operandShiftSame(nodep)}",		"replaceShiftSame(nodep)");
    TREEOP ("AstXor {operandShiftSame(nodep)}",		"replaceShiftSame(nodep)");
    //      "AstXnor{operandShiftSame(nodep)}",		// Cannot ShiftSame as the shifted-in zeros might create a one
    // Note can't simplify a extend{extends}, extends{extend}, as the sign bits end up in the wrong places
    TREEOPV("AstExtend {$lhsp.castExtend}",  "replaceExtend(nodep, VN_CAST(nodep->lhsp(), Extend)->lhsp())");
    TREEOPV("AstExtendS{$lhsp.castExtendS}", "replaceExtend(nodep, VN_CAST(nodep->lhsp(), ExtendS)->lhsp())");
    TREEOPV("AstReplicate{$lhsp, $rhsp.isOne, $lhsp->width()==nodep->width()}",	"replaceWLhs(nodep)");  // {1{lhs}}->lhs
    TREEOPV("AstReplicateN{$lhsp, $rhsp.isOne, $lhsp->width()==nodep->width()}", "replaceWLhs(nodep)");  // {1{lhs}}->lhs
    TREEOPV("AstReplicate{$lhsp.castReplicate, operandRepRep(nodep)}", "DONE");  // {2{3{lhs}}}->{6{lhs}}
    TREEOPV("AstConcat{operandConcatSame(nodep)}", "DONE");  // {a,a}->{2{a}}, {a,2{a}}->{3{a}, etc
    // Next rule because AUTOINST puts the width of bits in
    // to pins, even when the widths are exactly the same across the hierarchy.
    TREEOPV("AstSel{operandSelExtend(nodep)}",	"DONE");
    TREEOPV("AstSel{operandSelFull(nodep)}",	"replaceWChild(nodep, nodep->fromp())");
    TREEOPV("AstSel{$fromp.castSel}",		"replaceSelSel(nodep)");
    TREEOPV("AstSel{$fromp.castAdd, operandSelBiLower(nodep)}",	"DONE");
    TREEOPV("AstSel{$fromp.castAnd, operandSelBiLower(nodep)}",	"DONE");
    TREEOPV("AstSel{$fromp.castOr,  operandSelBiLower(nodep)}",	"DONE");
    TREEOPV("AstSel{$fromp.castSub, operandSelBiLower(nodep)}",	"DONE");
    TREEOPV("AstSel{$fromp.castXnor,operandSelBiLower(nodep)}",	"DONE");
    TREEOPV("AstSel{$fromp.castXor, operandSelBiLower(nodep)}",	"DONE");
    TREEOPV("AstSel{$fromp.castShiftR, operandSelShiftLower(nodep)}",	"DONE");
    TREEOPC("AstSel{$fromp.castConst, $lsbp.castConst, $widthp.castConst, }",	"replaceConst(nodep)");
    TREEOPV("AstSel{$fromp.castConcat, $lsbp.castConst, $widthp.castConst, }",	"replaceSelConcat(nodep)");
    TREEOPV("AstSel{$fromp.castReplicate, $lsbp.castConst, $widthp.castConst, operandSelReplicate(nodep) }",	"DONE");
    // V3Tristate requires selects below BufIf1.
    // Also do additional operators that are bit-independent, but only definite
    // win if bit select is a constant (otherwise we may need to compute bit index several times)
    TREEOPV("AstSel{$fromp.castBufIf1}",		"replaceSelIntoBiop(nodep)");
    TREEOPV("AstSel{$fromp.castNot}",			"replaceSelIntoUniop(nodep)");
    TREEOPV("AstSel{$fromp.castAnd,$lhsp.castConst}",	"replaceSelIntoUniop(nodep)");
    TREEOPV("AstSel{$fromp.castOr,$lhsp.castConst}",	"replaceSelIntoUniop(nodep)");
    TREEOPV("AstSel{$fromp.castXor,$lhsp.castConst}",	"replaceSelIntoUniop(nodep)");
    TREEOPV("AstSel{$fromp.castXnor,$lhsp.castConst}",	"replaceSelIntoUniop(nodep)");
    // Conversions
    TREEOPV("AstRedXnor{$lhsp}",		"AstNot{AstRedXor{$lhsp}}");  // Just eliminate XNOR's
    // This visit function here must allow for short-circuiting.
    TREEOPS("AstLogIf {$lhsp.isZero}",		"replaceNum(nodep, 1)");
    TREEOPV("AstLogIf {$lhsp, $rhsp}",		"AstLogOr{AstLogNot{$lhsp},$rhsp}");
    TREEOPV("AstLogIff{$lhsp, $rhsp}",		"AstLogNot{AstXor{$lhsp,$rhsp}}");
    // Strings
    TREEOPC("AstCvtPackString{$lhsp.castConst}", "replaceConstString(nodep, VN_CAST(nodep->lhsp(), Const)->num().toString())");


    // Possible futures:
    // (a?(b?y:x):y) -> (a&&!b)?x:y
    // (a?(b?x:y):y) -> (a&&b)?x:y
    // (a?x:(b?x:y)) -> (a||b)?x:y
    // (a?x:(b?y:x)) -> (a||!b)?x:y

    // Note we can't convert EqCase/NeqCase to Eq/Neq here because that would break 3'b1x1==3'b101

    //-----
    virtual void visit(AstNode* nodep) {
	// Default: Just iterate
	if (m_required) {
            if (VN_IS(nodep, NodeDType) || VN_IS(nodep, Range)) {
		// Ignore dtypes for parameter type pins
	    } else {
		nodep->v3error("Expecting expression to be constant, but can't convert a "
			       <<nodep->prettyTypeName()<<" to constant.");
	    }
	} else {
	    // Calculate the width of this operation
	    if (m_params && !nodep->width()) {
		nodep = V3Width::widthParamsEdit(nodep);
	    }
            iterateChildren(nodep);
	}
    }

public:
    // Processing Mode Enum
    enum ProcMode {
	PROC_PARAMS,
	PROC_GENERATE,
	PROC_LIVE,
	PROC_V_WARN,
	PROC_V_NOWARN,
	PROC_V_EXPENSIVE,
	PROC_CPP
    };

    // CONSTUCTORS
    explicit ConstVisitor(ProcMode pmode) {
	m_params = false;
	m_required = false;
	m_doExpensive = false;
	m_doNConst = false;
	m_doShort = true;	// Presently always done
	m_doV = false;
	m_doGenerate = false;	// Inside generate conditionals
        m_hasJumpGo = false;
	m_warn = false;
	m_wremove = true;  // Overridden in visitors
	m_modp = NULL;
	m_selp = NULL;
	m_scopep = NULL;
	m_attrp = NULL;
	//
	switch (pmode) {
	case PROC_PARAMS:	m_doV = true;  m_doNConst = true; m_params = true; m_required = true; break;
	case PROC_GENERATE:	m_doV = true;  m_doNConst = true; m_params = true; m_required = true; m_doGenerate = true; break;
	case PROC_LIVE:		break;
	case PROC_V_WARN:	m_doV = true;  m_doNConst = true; m_warn = true; break;
	case PROC_V_NOWARN:	m_doV = true;  m_doNConst = true; break;
	case PROC_V_EXPENSIVE:	m_doV = true;  m_doNConst = true; m_doExpensive = true; break;
	case PROC_CPP:		m_doV = false; m_doNConst = true; break;
	default:		v3fatalSrc("Bad case"); break;
	}
    }
    virtual ~ConstVisitor() {}
    AstNode* mainAcceptEdit(AstNode* nodep) {
	// Operate starting at a random place
        return iterateSubtreeReturnEdits(nodep);
    }
};

//######################################################################
// Const class functions

//! Force this cell node's parameter list to become a constant
//! @return  Pointer to the edited node.
AstNode* V3Const::constifyParamsEdit(AstNode* nodep) {
    //if (debug()>0) nodep->dumpTree(cout,"  forceConPRE : ");
    // Resize even if the node already has a width, because buried in the tree
    // we may have a node we just created with signing, etc, that isn't sized yet.

    // Make sure we've sized everything first
    nodep = V3Width::widthParamsEdit(nodep);
    ConstVisitor visitor(ConstVisitor::PROC_PARAMS);
    if (AstVar* varp=VN_CAST(nodep, Var)) {
	// If a var wants to be constified, it's really a param, and
	// we want the value to be constant.  We aren't passed just the
	// init value because we need widthing above to handle the var's type.
	if (varp->valuep()) visitor.mainAcceptEdit(varp->valuep());
    } else {
	nodep = visitor.mainAcceptEdit(nodep);
    }
    // Because we do edits, nodep links may get trashed and core dump this.
    //if (debug()>0) nodep->dumpTree(cout,"  forceConDONE: ");
    return nodep;
}

//! Force this cell node's parameter list to become a constant inside generate.
//! If we are inside a generated "if", "case" or "for", we don't want to
//! trigger warnings when we deal with the width. It is possible that these
//! are spurious, existing within sub-expressions that will not actually be
//! generated. Since such occurrences, must be constant, in order to be
//! someting a generate block can depend on, we can wait until later to do the
//! width check.
//! @return  Pointer to the edited node.
AstNode* V3Const::constifyGenerateParamsEdit(AstNode* nodep) {
    //if (debug()>0) nodep->dumpTree(cout,"  forceConPRE : ");
    // Resize even if the node already has a width, because buried in the tree
    // we may have a node we just created with signing, etc, that isn't sized
    // yet.

    // Make sure we've sized everything first
    nodep = V3Width::widthGenerateParamsEdit(nodep);
    ConstVisitor visitor(ConstVisitor::PROC_GENERATE);
    if (AstVar* varp=VN_CAST(nodep, Var)) {
	// If a var wants to be constified, it's really a param, and
	// we want the value to be constant.  We aren't passed just the
	// init value because we need widthing above to handle the var's type.
	if (varp->valuep()) visitor.mainAcceptEdit(varp->valuep());
    } else {
	nodep = visitor.mainAcceptEdit(nodep);
    }
    // Because we do edits, nodep links may get trashed and core dump this.
    //if (debug()>0) nodep->dumpTree(cout,"  forceConDONE: ");
    return nodep;
}

void V3Const::constifyAllLint(AstNetlist* nodep) {
    // Only call from Verilator.cpp, as it uses user#'s
    UINFO(2,__FUNCTION__<<": "<<endl);
    {
        ConstVisitor visitor (ConstVisitor::PROC_V_WARN);
        (void)visitor.mainAcceptEdit(nodep);
    }  // Destruct before checking
    V3Global::dumpCheckGlobalTree("const", 0, v3Global.opt.dumpTreeLevel(__FILE__) >= 3);
}

void V3Const::constifyCpp(AstNetlist* nodep) {
    UINFO(2,__FUNCTION__<<": "<<endl);
    {
        ConstVisitor visitor (ConstVisitor::PROC_CPP);
        (void)visitor.mainAcceptEdit(nodep);
    }  // Destruct before checking
    V3Global::dumpCheckGlobalTree("const_cpp", 0, v3Global.opt.dumpTreeLevel(__FILE__) >= 3);
}

AstNode* V3Const::constifyEdit(AstNode* nodep) {
    ConstVisitor visitor (ConstVisitor::PROC_V_NOWARN);
    nodep = visitor.mainAcceptEdit(nodep);
    return nodep;
}

void V3Const::constifyAllLive(AstNetlist* nodep) {
    // Only call from Verilator.cpp, as it uses user#'s
    // This only pushes constants up, doesn't make any other edits
    // IE doesn't prune dead statements, as we need to do some usability checks after this
    UINFO(2,__FUNCTION__<<": "<<endl);
    {
        ConstVisitor visitor (ConstVisitor::PROC_LIVE);
        (void)visitor.mainAcceptEdit(nodep);
    }  // Destruct before checking
    V3Global::dumpCheckGlobalTree("const", 0, v3Global.opt.dumpTreeLevel(__FILE__) >= 3);
}

void V3Const::constifyAll(AstNetlist* nodep) {
    // Only call from Verilator.cpp, as it uses user#'s
    UINFO(2,__FUNCTION__<<": "<<endl);
    {
        ConstVisitor visitor (ConstVisitor::PROC_V_EXPENSIVE);
        (void)visitor.mainAcceptEdit(nodep);
    }  // Destruct before checking
    V3Global::dumpCheckGlobalTree("const", 0, v3Global.opt.dumpTreeLevel(__FILE__) >= 3);
}

AstNode* V3Const::constifyExpensiveEdit(AstNode* nodep) {
    ConstVisitor visitor (ConstVisitor::PROC_V_EXPENSIVE);
    nodep = visitor.mainAcceptEdit(nodep);
    return nodep;
}
