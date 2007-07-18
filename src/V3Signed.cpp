// $Id$
//*************************************************************************
// DESCRIPTION: Verilator: Signed/unsigned resolution
//
// Code available from: http://www.veripool.com/verilator
//
// AUTHORS: Wilson Snyder with Paul Wasson, Duane Gabli
//
//*************************************************************************
//
// Copyright 2005-2007 by Wilson Snyder.  This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// General Public License or the Perl Artistic License.
//
// Verilator is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
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
//*************************************************************************

#include "config_build.h"
#include "verilatedos.h"
#include <stdio.h>
#include <stdarg.h>
#include <unistd.h>
#include <map>
#include <iomanip>

#include "V3Global.h"
#include "V3Signed.h"
#include "V3Ast.h"

//######################################################################
// Signed class functions

class SignedVisitor : public AstNVisitor {
private:
    // NODE STATE/TYPES
    // STATE
    int		m_taskDepth;	// Recursion check
    bool	m_paramsOnly;	// Computing parameter value; limit operation

    // METHODS - special type detection
    bool backRequiresUnsigned(AstNode* nodep) {
	// The spec doesn't state this, but if you have an array select where the selection
	// index is NOT wide enough, you do not sign extend, but always zero extend.
	return (nodep->castArraySel()
		|| nodep->castSel());
    }

    // VISITORS
    //========
    // Signed: Output explicit by user, Lhs either
    virtual void visit(AstSigned* nodep, AstNUser*) {		signed_Os_Ix(nodep); }
    virtual void visit(AstUnsigned* nodep, AstNUser*) {		signed_Ou_Ix(nodep); }

    //========
    // Signed: Output unsigned, Operands either
    virtual void visit(AstArraySel* nodep, AstNUser*) {		signed_Ou_Ix(nodep); } //See backRequiresUnsigned
    virtual void visit(AstSel* nodep, AstNUser*) {		signed_Ou_Ix(nodep); } //See backRequiresUnsigned
    virtual void visit(AstAttrOf* nodep, AstNUser*) {		signed_Ou_Ix(nodep); }
    virtual void visit(AstCountOnes* nodep, AstNUser*) {	signed_Ou_Ix(nodep); }
    virtual void visit(AstPslBool* nodep, AstNUser*) {		signed_Ou_Ix(nodep); }
    virtual void visit(AstTime* nodep, AstNUser*) {		signed_Ou_Ix(nodep); }
    //
    virtual void visit(AstRedAnd* nodep, AstNUser*) {		signed_Ou_Ix(nodep); }
    virtual void visit(AstRedOr* nodep, AstNUser*) {		signed_Ou_Ix(nodep); }
    virtual void visit(AstRedXnor* nodep, AstNUser*){		signed_Ou_Ix(nodep); }
    virtual void visit(AstRedXor* nodep,AstNUser*) {		signed_Ou_Ix(nodep); }
    virtual void visit(AstIsUnknown* nodep,AstNUser*) {		signed_Ou_Ix(nodep); }
    virtual void visit(AstOneHot* nodep,AstNUser*) {		signed_Ou_Ix(nodep); }
    virtual void visit(AstOneHot0* nodep,AstNUser*) {		signed_Ou_Ix(nodep); }
    //
    virtual void visit(AstConcat* nodep, AstNUser*) {		signed_Ou_Ix(nodep); }
    virtual void visit(AstReplicate* nodep, AstNUser*) {	signed_Ou_Ix(nodep); }
    virtual void visit(AstRange* nodep, AstNUser*) {		signed_Ou_Ix(nodep); }
    // ...    One presumes these are unsigned out, though the spec doesn't say
    virtual void visit(AstLogNot* nodep, AstNUser*) {		signed_Ou_Ix(nodep); }
    virtual void visit(AstLogAnd* nodep, AstNUser*) {		signed_Ou_Ix(nodep); }
    virtual void visit(AstLogOr* nodep, AstNUser*) {		signed_Ou_Ix(nodep); }
    virtual void visit(AstLogIf* nodep, AstNUser*) {		signed_Ou_Ix(nodep); }
    virtual void visit(AstLogIff* nodep, AstNUser*) {		signed_Ou_Ix(nodep); }
    // ...    These shouldn't matter, just make unsigned
    virtual void visit(AstUCFunc* nodep, AstNUser*) {		signed_Ou_Ix(nodep); }
    virtual void visit(AstText* nodep, AstNUser*) {		signed_Ou_Ix(nodep); }
    // ...    These comparisons don't care about inbound types
    // ...    (Though they should match.  We don't check.)
    virtual void visit(AstEq* nodep, AstNUser*) {		signed_Ou_Ix(nodep); }
    virtual void visit(AstEqCase* nodep, AstNUser*) {		signed_Ou_Ix(nodep); }
    virtual void visit(AstEqWild* nodep, AstNUser*) {		signed_Ou_Ix(nodep); }
    virtual void visit(AstNeq* nodep, AstNUser*) {		signed_Ou_Ix(nodep); }
    virtual void visit(AstNeqCase* nodep, AstNUser*){		signed_Ou_Ix(nodep); }
    virtual void visit(AstNeqWild* nodep, AstNUser*){		signed_Ou_Ix(nodep); }

    //=======
    // Signed: Output signed iff LHS signed; unary operator
    virtual void visit(AstNot* nodep, AstNUser*) {		signed_Olhs(nodep); }
    virtual void visit(AstUnaryMin* nodep, AstNUser*) {		signed_Olhs(nodep); }
    virtual void visit(AstShiftL* nodep, AstNUser*) {		signed_Olhs(nodep); }
    virtual void visit(AstShiftR* nodep, AstNUser*) {		signed_Olhs(nodep); }

    //=======
    // Signed: Output signed iff LHS & RHS signed; binary operator
    virtual void visit(AstAnd* nodep, AstNUser*) {		signed_OlhsAndRhs(nodep); }
    virtual void visit(AstOr* nodep, AstNUser*) {		signed_OlhsAndRhs(nodep); }
    virtual void visit(AstXnor* nodep, AstNUser*) {		signed_OlhsAndRhs(nodep); }
    virtual void visit(AstXor* nodep, AstNUser*) {		signed_OlhsAndRhs(nodep); }
    virtual void visit(AstSub* nodep, AstNUser*) {		signed_OlhsAndRhs(nodep); }
    virtual void visit(AstAdd* nodep, AstNUser*) {		signed_OlhsAndRhs(nodep); }

    //=======
    // Signed: Output signed iff RHS & THS signed
    virtual void visit(AstNodeCond* nodep, AstNUser*) {		signed_OrhsAndThs(nodep); }

    //=======
    // These have proper signedness set when they were created.
    virtual void visit(AstFunc* nodep, AstNUser*) {		nodep->iterateChildren(*this); }
    virtual void visit(AstVar* nodep, AstNUser*) {		nodep->iterateChildren(*this); }

    // Inherit from others
    virtual void visit(AstNodeVarRef* nodep, AstNUser*) {
	nodep->varp()->iterate(*this);
	nodep->signedFrom(nodep->varp());
    }
    virtual void visit(AstFuncRef* nodep, AstNUser* vup) {
	visit(nodep->castNodeFTaskRef(), vup);  // Deal with as if was task
	nodep->signedFrom(nodep->taskp());
    }
    virtual void visit(AstConst* nodep, AstNUser*) {
	// The node got setup with the signed state of the node.
	// However a later operation may have changed the node->signed w/o changing
	// the number's sign.  So we don't: nodep->isSigned(nodep->num().isSigned());
    }
    virtual void visit(AstNodeFTaskRef* nodep, AstNUser*) {
	// Fortunately, the input variables to the task keep whatever sign they are given
	// And we already did the function's output signedness above in visit(AstFuncRef,
	// so, it's just
	nodep->iterateChildren(*this);
    }
    virtual void visit(AstPin* nodep, AstNUser*) {
	// Same as above taskref argument.
	nodep->iterateChildren(*this);
    }

    // VISITORS - Special
    virtual void visit(AstDisplay* nodep, AstNUser*) {
	nodep->iterateChildren(*this);
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
	    } else if (inPct) {
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
		default:  // Most operators, just move to next argument
		    if (argp) argp=argp->nextp();
		    break;
		} // switch
	    }
	    dispout += ch;
	}
	nodep->text(dispout);
	UINFO(9,"  Display out "<<nodep->text()<<endl);
    }

    // VISITORS - These need to be changed to different op types
    // Uniop
    virtual void visit(AstExtend* nodep, AstNUser*) {
	signed_Olhs(nodep);
	if (nodep->isSigned() && !backRequiresUnsigned(nodep->backp())) {
	    replaceWithSignedVersion(nodep, new AstExtendS	(nodep->fileline(), nodep->lhsp()->unlinkFrBack())); nodep=NULL;
	}
    }
    virtual void visit(AstExtendS* nodep, AstNUser*) {
	signed_Olhs(nodep);
	if (!(nodep->isSigned() && !backRequiresUnsigned(nodep->backp()))) {
	    replaceWithSignedVersion(nodep, new AstExtend	(nodep->fileline(), nodep->lhsp()->unlinkFrBack())); nodep=NULL;
	}
    }

    // Biop
    virtual void visit(AstPow* nodep, AstNUser*) {
	// Pow is special, output sign only depends on LHS sign
	signed_Olhs(nodep);
	if (nodep->isSigned()) {
	    replaceWithSignedVersion(nodep, new AstPowS	(nodep->fileline(), nodep->lhsp()->unlinkFrBack(), nodep->rhsp()->unlinkFrBack())); nodep=NULL;
	}
    }
    virtual void visit(AstPowS* nodep, AstNUser*) {
	// Pow is special, output sign only depends on LHS sign
	signed_Olhs(nodep);
	if (!nodep->isSigned()) {
	    replaceWithSignedVersion(nodep, new AstPow	(nodep->fileline(), nodep->lhsp()->unlinkFrBack(), nodep->rhsp()->unlinkFrBack())); nodep=NULL;
	}
    }

    // These have different node types, as they operate differently
    // Must add to case statement below, 
    virtual void visit(AstGt* nodep, AstNUser*) {	checkReplace_Ou_FlavLhsAndRhs(nodep); }
    virtual void visit(AstGtS* nodep, AstNUser*) {	checkReplace_Ou_FlavLhsAndRhs(nodep); }
    virtual void visit(AstGte* nodep, AstNUser*) {	checkReplace_Ou_FlavLhsAndRhs(nodep); }
    virtual void visit(AstGteS* nodep, AstNUser*) {	checkReplace_Ou_FlavLhsAndRhs(nodep); }
    virtual void visit(AstLt* nodep, AstNUser*) {	checkReplace_Ou_FlavLhsAndRhs(nodep); }
    virtual void visit(AstLtS* nodep, AstNUser*) {	checkReplace_Ou_FlavLhsAndRhs(nodep); }
    virtual void visit(AstLte* nodep, AstNUser*) {	checkReplace_Ou_FlavLhsAndRhs(nodep); }
    virtual void visit(AstLteS* nodep, AstNUser*) {	checkReplace_Ou_FlavLhsAndRhs(nodep); }
    // Need replacements; output matches input sign
    virtual void visit(AstDiv* nodep, AstNUser*) {	checkReplace_OlhsAndRhs(nodep); }
    virtual void visit(AstDivS* nodep, AstNUser*) {	checkReplace_OlhsAndRhs(nodep); }
    virtual void visit(AstModDiv* nodep, AstNUser*) {	checkReplace_OlhsAndRhs(nodep); }
    virtual void visit(AstModDivS* nodep, AstNUser*) {	checkReplace_OlhsAndRhs(nodep); }
    virtual void visit(AstMul* nodep, AstNUser*) {	checkReplace_OlhsAndRhs(nodep); }
    virtual void visit(AstMulS* nodep, AstNUser*) {	checkReplace_OlhsAndRhs(nodep); }
    // ShiftRS converts to ShiftR, but not vice-versa
    virtual void visit(AstShiftRS* nodep, AstNUser*) {	checkReplace_Olhs(nodep); }

    void checkReplace_Ou_FlavLhsAndRhs(AstNodeBiop* nodep) {
	// For compares, the output of the comparison is unsigned.
	// However, we need the appropriate type of compare selected by RHS & LHS
	signed_Ou_Ix(nodep);
	checkReplace(nodep, nodep->lhsp()->isSigned() && nodep->rhsp()->isSigned());
    }
    void checkReplace_Olhs(AstNodeBiop* nodep) {
	signed_Olhs(nodep);
	checkReplace(nodep, nodep->isSigned());
    }
    void checkReplace_OlhsAndRhs(AstNodeBiop* nodep) {
	signed_OlhsAndRhs(nodep);
	checkReplace(nodep, nodep->isSigned());
    }

    void checkReplace(AstNodeBiop* nodep, bool signedFlavorNeeded) {
	if (signedFlavorNeeded != nodep->signedFlavor()) {
	    AstNode* lhsp = nodep->lhsp()->unlinkFrBack();
	    AstNode* rhsp = nodep->rhsp()->unlinkFrBack();
	    AstNode* newp = NULL;
	    // Given a signed/unsigned node type, create the opposite type
	    switch (nodep->type()) {
	    case AstType::GT:	   newp = new AstGtS	(nodep->fileline(), lhsp, rhsp); break;
	    case AstType::GTS:	   newp = new AstGt	(nodep->fileline(), lhsp, rhsp); break;
	    case AstType::GTE:	   newp = new AstGteS	(nodep->fileline(), lhsp, rhsp); break;
	    case AstType::GTES:	   newp = new AstGte	(nodep->fileline(), lhsp, rhsp); break;
	    case AstType::LT:	   newp = new AstLtS	(nodep->fileline(), lhsp, rhsp); break;
	    case AstType::LTS:	   newp = new AstLt	(nodep->fileline(), lhsp, rhsp); break;
	    case AstType::LTE:	   newp = new AstLteS	(nodep->fileline(), lhsp, rhsp); break;
	    case AstType::LTES:	   newp = new AstLte	(nodep->fileline(), lhsp, rhsp); break;
	    case AstType::DIV:	   newp = new AstDivS	(nodep->fileline(), lhsp, rhsp); break;
	    case AstType::DIVS:	   newp = new AstDiv	(nodep->fileline(), lhsp, rhsp); break;
	    case AstType::MODDIV:  newp = new AstModDivS(nodep->fileline(), lhsp, rhsp); break;
	    case AstType::MODDIVS: newp = new AstModDiv (nodep->fileline(), lhsp, rhsp); break;
	    case AstType::MUL:	   newp = new AstMulS	(nodep->fileline(), lhsp, rhsp); break;
	    case AstType::MULS:	   newp = new AstMul	(nodep->fileline(), lhsp, rhsp); break;
	    case AstType::SHIFTRS: newp = new AstShiftR	(nodep->fileline(), lhsp, rhsp); break;
	    default:
		nodep->v3fatalSrc("Node needs sign change, but bad case: "<<nodep<<endl);
		break;
	    }
	    replaceWithSignedVersion(nodep,newp);
	}
    }

    // VISITORS - defaults
    virtual void visit(AstNodeMath* nodep, AstNUser*) {
	nodep->v3fatalSrc("Visit function missing? Signedness unknown for this node: "<<nodep);
	nodep->iterateChildren(*this);
    }
    virtual void visit(AstNode* nodep, AstNUser*) {
	nodep->iterateChildren(*this);
    }

    // COMMON SCHEMES
    // Signed: Output signed, Lhs/Rhs/etc either
    void signed_Os_Ix(AstNode* nodep) {
	nodep->iterateChildren(*this);
	nodep->isSigned(true);
    }
    // Signed: Output unsigned, Lhs/Rhs/etx either
    void signed_Ou_Ix(AstNode* nodep) {
	nodep->iterateChildren(*this);
	nodep->isSigned(false);
    }
    // Signed: Output signed iff LHS signed; unary operator
    void signed_Olhs(AstNodeUniop* nodep) {
	nodep->iterateChildren(*this);
	nodep->isSigned(nodep->lhsp()->isSigned());
    }
    // Signed: Output signed iff LHS signed; binary operator
    void signed_Olhs(AstNodeBiop* nodep) {
	nodep->iterateChildren(*this);
	nodep->isSigned(nodep->lhsp()->isSigned());
    }
    // Signed: Output signed iff LHS & RHS signed; binary operator
    void signed_OlhsAndRhs(AstNodeBiop* nodep) {
	nodep->iterateChildren(*this);
	nodep->isSigned(nodep->lhsp()->isSigned() && nodep->rhsp()->isSigned());
    }
    // Signed: Output signed iff RHS & THS signed
    void signed_OrhsAndThs(AstNodeTriop* nodep) {
	nodep->iterateChildren(*this);
	nodep->isSigned(nodep->rhsp()->isSigned() && nodep->thsp()->isSigned());
    }
    void replaceWithSignedVersion(AstNode* nodep, AstNode* newp) {
	UINFO(6," Replace "<<nodep<<" w/ "<<newp<<endl);
	nodep->replaceWith(newp);
	newp->widthSignedFrom(nodep);
	pushDeletep(nodep); nodep=NULL;
    }

public:
    // CONSTRUCTORS
    SignedVisitor(AstNode* nodep, bool paramsOnly) {
	m_paramsOnly = paramsOnly;
	m_taskDepth = 0;
	nodep->accept(*this);
    }
    virtual ~SignedVisitor() {}
};

//######################################################################
// Signed class functions
/// Remove all $signed, $unsigned, we're done with them.

class SignedRemoveVisitor : public AstNVisitor {
private:
    // VISITORS
    virtual void visit(AstSigned* nodep, AstNUser*) {
	replaceWithSignedVersion(nodep, nodep->lhsp()->unlinkFrBack()); nodep=NULL;
    }
    virtual void visit(AstUnsigned* nodep, AstNUser*) {
	replaceWithSignedVersion(nodep, nodep->lhsp()->unlinkFrBack()); nodep=NULL;
    }
    virtual void visit(AstNode* nodep, AstNUser*) {
	nodep->iterateChildren(*this);
    }
    void replaceWithSignedVersion(AstNode* nodep, AstNode* newp) {
	UINFO(6," Replace "<<nodep<<" w/ "<<newp<<endl);
	nodep->replaceWith(newp);
	newp->widthSignedFrom(nodep);
	pushDeletep(nodep); nodep=NULL;
    }
public:
    // CONSTRUCTORS
    SignedRemoveVisitor(AstNode* nodep) {
	nodep->accept(*this);
    }
    virtual ~SignedRemoveVisitor() {}
};

//######################################################################
// Top Signed class

void V3Signed::signedAll(AstNetlist* nodep) {
    UINFO(2,__FUNCTION__<<": "<<endl);
    SignedVisitor visitor (nodep, false);
    SignedRemoveVisitor rvisitor (nodep);
}

void V3Signed::signedParams(AstNode* nodep) {
    UINFO(4,__FUNCTION__<<": "<<endl);
    SignedVisitor visitor (nodep, true);
    SignedRemoveVisitor rvisitor (nodep);
}
