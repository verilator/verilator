// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Add temporaries, such as for clean nodes
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
// V3Clean's Transformations:
//
// Each module:
//	For each math operator, if it requires a clean operand,
//	and the operand is dirty, insert a CLEAN node.
//	Resize operands to C++ 32/64/wide types.
//	Copy all width() values to widthMin() so RANGE, etc can still see orig widths
//
//*************************************************************************

#include "config_build.h"
#include "verilatedos.h"
#include <cstdio>
#include <cstdarg>
#include <unistd.h>
#include <algorithm>

#include "V3Global.h"
#include "V3Clean.h"
#include "V3Ast.h"

//######################################################################
// Clean state, as a visitor of each AstNode

class CleanVisitor : public AstNVisitor {
private:
    // NODE STATE
    // Entire netlist:
    //  AstNode::user()		-> CleanState.  For this node, 0==UNKNOWN
    //  AstNode::user2()	-> bool.  True indicates widthMin has been propagated
    //  AstNodeDType::user3()	-> AstNodeDType*.  Alternative node with C size
    AstUser1InUse	m_inuser1;
    AstUser2InUse	m_inuser2;
    AstUser3InUse	m_inuser3;

    // TYPES
    enum CleanState { CS_UNKNOWN, CS_CLEAN, CS_DIRTY };

    // STATE
    AstNodeModule* m_modp;

    // METHODS
    static int debug() {
	static int level = -1;
	if (VL_UNLIKELY(level < 0)) level = v3Global.opt.debugSrcLevel(__FILE__);
	return level;
    }

    // Width resetting
    int  cppWidth(AstNode* nodep) {
	if (nodep->width()<=VL_WORDSIZE) return VL_WORDSIZE;
	else if (nodep->width()<=VL_QUADSIZE) return VL_QUADSIZE;
	else return nodep->widthWords()*VL_WORDSIZE;
    }
    void setCppWidth (AstNode* nodep) {
	nodep->user2(true);  // Don't resize it again
	AstNodeDType* old_dtypep = nodep->dtypep();
	int width=cppWidth(nodep);  // widthMin is unchanged
	if (old_dtypep->width() != width) {
	    // Since any given dtype's cppWidth() is the same, we can just
	    // remember one convertion for each, and reuse it
	    if (AstNodeDType* new_dtypep = old_dtypep->user3p()->castNode()->castNodeDType()) {
		nodep->dtypep(new_dtypep);
	    } else {
		nodep->dtypeChgWidth(width, nodep->widthMin());
		AstNodeDType* new_dtypep2 = nodep->dtypep();
		if (new_dtypep2 == old_dtypep) nodep->v3fatalSrc("Dtype didn't change when width changed");
		old_dtypep->user3p(new_dtypep2);  // Remember for next time
	    }
	}
    }
    void computeCppWidth (AstNode* nodep) {
	if (!nodep->user2() && nodep->hasDType()) {
	    if (nodep->castVar() || nodep->castNodeDType()) {  // Don't want to change variable widths!
	    } else {
		setCppWidth(nodep);
	    }
	}
    }

    // Store the clean state in the userp on each node
    void setCleanState(AstNode* nodep, CleanState clean) {
	nodep->user1(clean);
    }
    CleanState getCleanState(AstNode* nodep) {
	return ((CleanState)nodep->user1());
    }
    bool isClean(AstNode* nodep) {
	CleanState clstate = getCleanState(nodep);
	if (clstate==CS_CLEAN) return true;
	if (clstate==CS_DIRTY) return false;
	nodep->v3fatalSrc("Unknown clean state on node: "+nodep->prettyTypeName());
	return false;
    }
    void setClean(AstNode* nodep, bool isClean) {
	computeCppWidth (nodep);  // Just to be sure it's in widthMin
	bool wholeUint = ((nodep->widthMin() % VL_WORDSIZE) == 0);  //32,64,...
	setCleanState(nodep, ((isClean||wholeUint) ? CS_CLEAN:CS_DIRTY));
    }

    // Operate on nodes
    void insertClean(AstNode* nodep) {  // We'll insert ABOVE passed node
	UINFO(4,"  NeedClean "<<nodep<<endl);
	AstNRelinker relinkHandle;
	nodep->unlinkFrBack(&relinkHandle);
	//
	computeCppWidth(nodep);
	V3Number mask (nodep->fileline(), cppWidth(nodep));
	mask.setMask(nodep->widthMin());
	AstNode* cleanp = new AstAnd (nodep->fileline(),
				      new AstConst (nodep->fileline(), mask),
				      nodep);
	cleanp->dtypeFrom(nodep);  // Otherwise the AND normally picks LHS
	relinkHandle.relink(cleanp);
    }
    void insureClean(AstNode* nodep) {
	computeCppWidth(nodep);
	if (!isClean(nodep)) insertClean(nodep);
    }
    void insureCleanAndNext(AstNode* nodep) {
	// Editing list, careful looping!
	for (AstNode* exprp = nodep; exprp; ) {
	    AstNode* nextp = exprp->nextp();
	    insureClean(exprp);
	    exprp = nextp;
	}
    }

    // Base type handling methods
    void operandBiop(AstNodeBiop* nodep) {
	nodep->iterateChildren(*this);
	computeCppWidth(nodep);
	if (nodep->cleanLhs()) {
	    insureClean(nodep->lhsp());
	}
	if (nodep->cleanRhs()) {
	    insureClean(nodep->rhsp());
	}
	//no setClean.. must do it in each user routine.
    }
    void operandTriop(AstNodeTriop* nodep) {
	nodep->iterateChildren(*this);
	computeCppWidth(nodep);
	if (nodep->cleanLhs()) {
	    insureClean(nodep->lhsp());
	}
	if (nodep->cleanRhs()) {
	    insureClean(nodep->rhsp());
	}
	if (nodep->cleanThs()) {
	    insureClean(nodep->thsp());
	}
	//no setClean.. must do it in each user routine.
    }

    // VISITORS
    virtual void visit(AstNodeModule* nodep, AstNUser*) {
	m_modp = nodep;
	nodep->iterateChildren(*this);
	m_modp = NULL;
    }
    virtual void visit(AstNodeUniop* nodep, AstNUser*) {
	nodep->iterateChildren(*this);
	computeCppWidth(nodep);
	if (nodep->cleanLhs()) {
	    insureClean(nodep->lhsp());
	}
	setClean (nodep, nodep->cleanOut());
    }
    virtual void visit(AstNodeBiop* nodep, AstNUser*) {
	operandBiop(nodep);
	setClean (nodep, nodep->cleanOut());
    }
    virtual void visit(AstAnd* nodep, AstNUser*) {
	operandBiop(nodep);
	setClean (nodep, isClean(nodep->lhsp()) || isClean(nodep->rhsp()));
    }
    virtual void visit(AstXor* nodep, AstNUser*) {
	operandBiop(nodep);
	setClean (nodep, isClean(nodep->lhsp()) && isClean(nodep->rhsp()));
    }
    virtual void visit(AstOr* nodep, AstNUser*) {
	operandBiop(nodep);
	setClean (nodep, isClean(nodep->lhsp()) && isClean(nodep->rhsp()));
    }
    virtual void visit(AstNodeMath* nodep, AstNUser*) {
	nodep->iterateChildren(*this);
	computeCppWidth(nodep);
        setClean (nodep, nodep->cleanOut());
    }
    virtual void visit(AstNodeAssign* nodep, AstNUser*) {
	nodep->iterateChildren(*this);
	computeCppWidth(nodep);
	if (nodep->cleanRhs()) {
	    insureClean(nodep->rhsp());
	}
    }
    virtual void visit(AstText* nodep, AstNUser*) {
	setClean (nodep, true);
    }
    virtual void visit(AstScopeName* nodep, AstNUser*) {
	setClean (nodep, true);
    }
    virtual void visit(AstSel* nodep, AstNUser*) {
	operandTriop(nodep);
        setClean (nodep, nodep->cleanOut());
    }
    virtual void visit(AstUCFunc* nodep, AstNUser*) {
	nodep->iterateChildren(*this);
	computeCppWidth(nodep);
        setClean (nodep, false);
	// We always clean, as we don't trust those pesky users.
	if (!nodep->backp()->castAnd()) {
	    insertClean(nodep);
	}
	insureCleanAndNext (nodep->bodysp());
    }
    virtual void visit(AstTraceInc* nodep, AstNUser*) {
	nodep->iterateChildren(*this);
	insureCleanAndNext (nodep->valuep());
    }
    virtual void visit(AstTypedef* nodep, AstNUser*) {
	// No cleaning, or would loose pointer to enum
	nodep->iterateChildren(*this);
    }

    // Control flow operators
    virtual void visit(AstNodeCond* nodep, AstNUser*) {
	nodep->iterateChildren(*this);
	insureClean(nodep->condp());
	setClean(nodep, isClean(nodep->expr1p()) && isClean(nodep->expr2p()));
    }
    virtual void visit(AstWhile* nodep, AstNUser*) {
	nodep->iterateChildren(*this);
	insureClean(nodep->condp());
    }
    virtual void visit(AstNodeIf* nodep, AstNUser*) {
	nodep->iterateChildren(*this);
	insureClean(nodep->condp());
    }
    virtual void visit(AstSFormatF* nodep, AstNUser*) {
	nodep->iterateChildren(*this);
	insureCleanAndNext (nodep->exprsp());
	setClean(nodep, true);  // generates a string, so not relevant
    }
    virtual void visit(AstUCStmt* nodep, AstNUser*) {
	nodep->iterateChildren(*this);
	insureCleanAndNext (nodep->bodysp());
    }
    virtual void visit(AstCCall* nodep, AstNUser*) {
	nodep->iterateChildren(*this);
	insureCleanAndNext (nodep->argsp());
    }

    //--------------------
    // Default: Just iterate
    virtual void visit(AstNode* nodep, AstNUser*) {
	nodep->iterateChildren(*this);
	computeCppWidth(nodep);
    }

public:
    // CONSTUCTORS
    CleanVisitor(AstNetlist* nodep) {
	nodep->accept(*this);
    }
    virtual ~CleanVisitor() {}
};

//######################################################################
// Clean class functions

void V3Clean::cleanAll(AstNetlist* nodep) {
    UINFO(2,__FUNCTION__<<": "<<endl);
    CleanVisitor visitor (nodep);
    V3Global::dumpCheckGlobalTree("clean.tree", 0, v3Global.opt.dumpTreeLevel(__FILE__) >= 3);
}
