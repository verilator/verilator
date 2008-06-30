//*************************************************************************
// DESCRIPTION: Verilator: Add temporaries, such as for clean nodes
//
// Code available from: http://www.veripool.org/verilator
//
// AUTHORS: Wilson Snyder with Paul Wasson, Duane Gabli
//
//*************************************************************************
//
// Copyright 2003-2008 by Wilson Snyder.  This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// General Public License or the Perl Artistic License.
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
//	Copy all width() values to minWidth() so RANGE, etc can still see orig widths
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
    //  AstNode::user2()	-> bool.  True indicates minWidth has been propagated

    // STATE
    AstModule* m_modp;
    //int debug() { return 9; }

    // ENUMS
    enum CleanState { UNKNOWN, CLEAN, DIRTY };

    // METHODS
    // Width resetting
    int  cppWidth(AstNode* nodep) {
	if (nodep->width()<=VL_WORDSIZE) return VL_WORDSIZE;
	else if (nodep->width()<=VL_QUADSIZE) return VL_QUADSIZE;
	else return nodep->widthWords()*VL_WORDSIZE;
    }
    void setCppWidth (AstNode* nodep, int width, int widthMin) {
	nodep->user2(true);  // Don't resize it again
	nodep->width(width, widthMin);
    }
    void computeCppWidth (AstNode* nodep) {
	if (!nodep->user2()) {
	    if (nodep->castVar()) {  // Don't want to change variable widths!
		setCppWidth(nodep, nodep->width(), nodep->width());  // set widthMin anyways so can see it later
	    } else {
		setCppWidth(nodep, cppWidth(nodep), nodep->widthMin());
	    }
	}
    }

    // Store the clean state in the userp on each node
    void setCleanState(AstNode* nodep, CleanState clean) {
	nodep->user(clean);
    }
    CleanState getCleanState(AstNode* nodep) {
	return ((CleanState)nodep->user());
    }
    bool isClean(AstNode* nodep) {
	CleanState clstate = getCleanState(nodep);
	if (clstate==CLEAN) return true;
	if (clstate==DIRTY) return false;
	nodep->v3fatalSrc("Unknown clean state on node.");
	return false;
    }
    void setClean(AstNode* nodep, bool isClean) {
	computeCppWidth (nodep);  // Just to be sure it's in widthMin
	bool wholeUint = ((nodep->widthMin() % VL_WORDSIZE) == 0);  //32,64,...
	setCleanState(nodep, ((isClean||wholeUint) ? CLEAN:DIRTY));
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
	setCppWidth (cleanp, cppWidth(nodep), nodep->widthMin());
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
    virtual void visit(AstModule* nodep, AstNUser*) {
	m_modp = nodep;
	nodep->iterateChildren(*this);
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
    virtual void visit(AstNodePli* nodep, AstNUser*) {
	nodep->iterateChildren(*this);
	insureCleanAndNext (nodep->exprsp());
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
    CleanVisitor() {}
    virtual ~CleanVisitor() {}
    void main(AstNetlist* nodep) {
	AstNode::userClearTree();	// userp() used on entire tree
	AstNode::user2ClearTree();	// userp() used on entire tree
	nodep->accept(*this);
    }
};

//######################################################################
// Clean class functions

void V3Clean::cleanAll(AstNetlist* nodep) {
    UINFO(2,__FUNCTION__<<": "<<endl);
    CleanVisitor visitor;
    visitor.main(nodep);
}
