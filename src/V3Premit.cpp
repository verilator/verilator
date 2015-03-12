// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Add temporaries, such as for premit nodes
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
// V3Premit's Transformations:
//
// Each module:
//	For each wide OP, make a a temporary variable with the wide value
//	For each deep expression, assign expression to temporary.
//
// Each display (independant transformation; here as Premit is a good point)
//	If autoflush, insert a flush
//
//*************************************************************************

#include "config_build.h"
#include "verilatedos.h"
#include <cstdio>
#include <cstdarg>
#include <unistd.h>
#include <algorithm>
#include <list>

#include "V3Global.h"
#include "V3Premit.h"
#include "V3Ast.h"


//######################################################################
// Structure for global state

class PremitAssignVisitor : public AstNVisitor {
private:
    // NODE STATE
    //  AstVar::user4()		// bool; occurs on LHS of current assignment
    AstUser4InUse	m_inuser4;

    // STATE
    bool	m_noopt;	// Disable optimization of variables in this block

    // METHODS
    static int debug() {
	static int level = -1;
	if (VL_UNLIKELY(level < 0)) level = v3Global.opt.debugSrcLevel(__FILE__);
	return level;
    }

    // VISITORS
    virtual void visit(AstNodeAssign* nodep, AstNUser*) {
        //AstNode::user4ClearTree();  // Implied by AstUser4InUse
	// LHS first as fewer varrefs
	nodep->lhsp()->iterateAndNext(*this);
	// Now find vars marked as lhs
	nodep->rhsp()->iterateAndNext(*this);
    }
    virtual void visit(AstVarRef* nodep, AstNUser*) {
	// it's LHS var is used so need a deep temporary
	if (nodep->lvalue()) {
	    nodep->varp()->user4(true);
	} else {
	    if (nodep->varp()->user4()) {
		if (!m_noopt) UINFO(4, "Block has LHS+RHS var: "<<nodep<<endl);
		m_noopt = true;
	    }
	}
    }
    virtual void visit(AstNode* nodep, AstNUser*) {
	nodep->iterateChildren(*this);
    }

public:
    // CONSTRUCTORS
    PremitAssignVisitor(AstNodeAssign* nodep) {
	UINFO(4,"  PremitAssignVisitor on "<<nodep<<endl);
	m_noopt = false;
	nodep->accept(*this);
    }
    virtual ~PremitAssignVisitor() {}
    bool noOpt() const { return m_noopt; }
};

//######################################################################
// Premit state, as a visitor of each AstNode

class PremitVisitor : public AstNVisitor {
private:
    // NODE STATE
    //  AstNodeMath::user()	-> bool.  True if iterated already
    //  AstShiftL::user2()	-> bool.  True if converted to conditional
    //  AstShiftR::user2()	-> bool.  True if converted to conditional
    //  *::user4()		-> See PremitAssignVisitor
    AstUser1InUse	m_inuser1;
    AstUser2InUse	m_inuser2;

    // STATE
    AstNodeModule*	m_modp;		// Current module
    AstCFunc*		m_funcp;	// Current block
    AstNode*		m_stmtp;	// Current statement
    AstWhile*		m_inWhilep;	// Inside while loop, special statement additions
    AstTraceInc*	m_inTracep;	// Inside while loop, special statement additions
    bool		m_assignLhs;	// Inside assignment lhs, don't breakup extracts

    // METHODS
    static int debug() {
	static int level = -1;
	if (VL_UNLIKELY(level < 0)) level = v3Global.opt.debugSrcLevel(__FILE__);
	return level;
    }

    bool assignNoTemp(AstNodeAssign* nodep) {
	return (nodep->lhsp()->castVarRef()
		&& !AstVar::scVarRecurse(nodep->lhsp())
		&& nodep->rhsp()->castConst());
    }
    void checkNode(AstNode* nodep) {
	// Consider adding a temp for this expression.
	// We need to avoid adding temps to the following:
	//   ASSIGN(x, *here*)
	//   ASSIGN(CONST*here*, VARREF(!sc))
	//   ARRAYSEL(*here*, ...)   (No wides can be in any argument but first, so we don't check which arg is wide)
	//   ASSIGN(x, SEL*HERE*(ARRAYSEL()...)   (m_assignLhs==true handles this.)
	//UINFO(9, "   Check: "<<nodep<<endl);
	//UINFO(9, "     Detail stmtp="<<(m_stmtp?"Y":"N")<<" U="<<(nodep->user1()?"Y":"N")<<" IW "<<(nodep->isWide()?"Y":"N")<<endl);
	if (m_stmtp
	    && !nodep->user1()) {	// Not already done
	    if (nodep->isWide()) {
		if (m_assignLhs) {
		} else if (nodep->firstAbovep()
			   && nodep->firstAbovep()->castNodeAssign()
			   && assignNoTemp(nodep->firstAbovep()->castNodeAssign())) {
		    // Not much point if it's just a direct assignment to a constant
		} else if (nodep->firstAbovep()
			   && nodep->firstAbovep()->castArraySel()) {  // ArraySel's are pointer refs, ignore
		} else {
		    UINFO(4,"Cre Temp: "<<nodep<<endl);
		    createDeepTemp(nodep, false);
		}
	    }
	}
    }

    AstVar* getBlockTemp(AstNode* nodep) {
	string newvarname = ((string)"__Vtemp"+cvtToStr(m_modp->varNumGetInc()));
	AstVar* varp = new AstVar (nodep->fileline(), AstVarType::STMTTEMP, newvarname,
				   nodep->dtypep());
	m_funcp->addInitsp(varp);
	return varp;
    }

    void insertBeforeStmt(AstNode* newp) {
	// Insert newp before m_stmtp
	if (m_inWhilep) {
	    // Statements that are needed for the 'condition' in a while actually have to
	    // be put before & after the loop, since we can't do any statements in a while's (cond).
	    m_inWhilep->addPrecondsp(newp);
	} else if (m_inTracep) {
	    m_inTracep->addPrecondsp(newp);
	} else if (m_stmtp) {
	    AstNRelinker linker;
	    m_stmtp->unlinkFrBack(&linker);
	    newp->addNext(m_stmtp);
	    linker.relink(newp);
	} else {
	    newp->v3fatalSrc("No statement insertion point.");
	}
    }

    void createDeepTemp(AstNode* nodep, bool noSubst) {
	if (debug()>8) nodep->dumpTree(cout,"deepin:");

	AstNRelinker linker;
	nodep->unlinkFrBack(&linker);

	AstVar* varp = getBlockTemp(nodep);
	if (noSubst) varp->noSubst(true); // Do not remove varrefs to this in V3Const
	// Replace node tree with reference to var
	AstVarRef* newp = new AstVarRef (nodep->fileline(), varp, false);
	linker.relink(newp);
	// Put assignment before the referencing statement
	AstAssign* assp = new AstAssign (nodep->fileline(),
					 new AstVarRef(nodep->fileline(), varp, true),
					 nodep);
	insertBeforeStmt(assp);
	if (debug()>8) assp->dumpTree(cout,"deepou:");
	nodep->user1(true);  // Don't add another assignment
    }

    // VISITORS
    virtual void visit(AstNodeModule* nodep, AstNUser*) {
	UINFO(4," MOD   "<<nodep<<endl);
	m_modp = nodep;
	m_funcp = NULL;
	nodep->iterateChildren(*this);
	m_modp = NULL;
    }
    virtual void visit(AstCFunc* nodep, AstNUser*) {
	m_funcp = nodep;
	nodep->iterateChildren(*this);
	m_funcp = NULL;
    }
    void startStatement(AstNode* nodep) {
	m_assignLhs = false;
	if (m_funcp) m_stmtp = nodep;
    }
    virtual void visit(AstWhile* nodep, AstNUser*) {
	UINFO(4,"  WHILE  "<<nodep<<endl);
	startStatement(nodep);
	nodep->precondsp()->iterateAndNext(*this);
	startStatement(nodep);
	m_inWhilep = nodep;
	nodep->condp()->iterateAndNext(*this);
	m_inWhilep = NULL;
	startStatement(nodep);
	nodep->bodysp()->iterateAndNext(*this);
	nodep->incsp()->iterateAndNext(*this);
	m_stmtp = NULL;
    }
    virtual void visit(AstNodeAssign* nodep, AstNUser*) {
	startStatement(nodep);
	{
	    bool noopt = PremitAssignVisitor(nodep).noOpt();
	    if (noopt && !nodep->user1()) {
		// Need to do this even if not wide, as e.g. a select may be on a wide operator
		UINFO(4,"Deep temp for LHS/RHS\n");
		createDeepTemp(nodep->rhsp(), false);
	    }
	}
	nodep->rhsp()->iterateAndNext(*this);
	m_assignLhs = true;
	nodep->lhsp()->iterateAndNext(*this);
	m_assignLhs = false;
	m_stmtp = NULL;
    }
    virtual void visit(AstNodeStmt* nodep, AstNUser*) {
	UINFO(4,"  STMT  "<<nodep<<endl);
	startStatement(nodep);
	nodep->iterateChildren(*this);
	m_stmtp = NULL;
    }
    virtual void visit(AstTraceInc* nodep, AstNUser*) {
	startStatement(nodep);
	m_inTracep = nodep;
	nodep->iterateChildren(*this);
	m_inTracep = NULL;
	m_stmtp = NULL;
    }
    void visitShift (AstNodeBiop* nodep) {
	// Shifts of > 32/64 bits in C++ will wrap-around and generate non-0s
	if (!nodep->user2SetOnce()) {
	    UINFO(4,"  ShiftFix  "<<nodep<<endl);
	    if (nodep->widthMin()<=64  // Else we'll use large operators which work right
		// C operator's width must be < maximum shift which is based on Verilog width
		&& nodep->width() < (1LL<<nodep->rhsp()->widthMin())) {
		AstNRelinker replaceHandle;
		nodep->unlinkFrBack(&replaceHandle);
		AstNode* constzerop;
		int m1value = nodep->widthMin()-1; // Constant of width-1; not changing dtype width
		if (nodep->signedFlavor()) {
		    // Then over shifting gives the sign bit, not all zeros
		    // Note *NOT* clean output -- just like normal shift!
		    // Create equivalent of VL_SIGNONES_(node_width)
		    constzerop = new AstNegate (nodep->fileline(),
						new AstShiftR(nodep->fileline(),
							      nodep->lhsp()->cloneTree(false),
							      new AstConst(nodep->fileline(),
									   m1value),
							      nodep->width()));
		} else {
		    V3Number zeronum  (nodep->fileline(), nodep->width(), 0);
		    constzerop = new AstConst(nodep->fileline(), zeronum);
		}
		constzerop->dtypeFrom (nodep);  // unsigned

		V3Number widthnum (nodep->fileline(), nodep->rhsp()->widthMin(), m1value);
		AstNode* constwidthp = new AstConst(nodep->fileline(), widthnum);
		constwidthp->dtypeFrom (nodep->rhsp());  // unsigned
		AstCond* newp =
		    new AstCond (nodep->fileline(),
				 new AstGte (nodep->fileline(),
					     constwidthp,
					     nodep->rhsp()->cloneTree(false)),
				 nodep,
				 constzerop);
		replaceHandle.relink(newp);
	    }
	}
	nodep->iterateChildren(*this); checkNode(nodep);
    }
    virtual void visit(AstShiftL* nodep, AstNUser*) {
	visitShift(nodep);
    }
    virtual void visit(AstShiftR* nodep, AstNUser*) {
	visitShift(nodep);
    }
    virtual void visit(AstShiftRS* nodep, AstNUser*) {
	visitShift(nodep);
    }
    // Operators
    virtual void visit(AstNodeTermop* nodep, AstNUser*) {
	nodep->iterateChildren(*this); checkNode(nodep); }
    virtual void visit(AstNodeUniop* nodep, AstNUser*) {
	nodep->iterateChildren(*this); checkNode(nodep); }
    virtual void visit(AstNodeBiop* nodep, AstNUser*) {
	nodep->iterateChildren(*this); checkNode(nodep); }
    virtual void visit(AstUCFunc* nodep, AstNUser*) {
	nodep->iterateChildren(*this); checkNode(nodep); }
    virtual void visit(AstSel* nodep, AstNUser*) {
	nodep->fromp()->iterateAndNext(*this);
	{   // Only the 'from' is part of the assignment LHS
	    bool prevAssign = m_assignLhs;
	    m_assignLhs = false;
	    nodep->lsbp()->iterateAndNext(*this);
	    nodep->widthp()->iterateAndNext(*this);
	    m_assignLhs = prevAssign;
	}
	checkNode(nodep); }
    virtual void visit(AstConst* nodep, AstNUser*) {
	nodep->iterateChildren(*this); checkNode(nodep); }
    virtual void visit(AstNodeCond* nodep, AstNUser*) {
	nodep->iterateChildren(*this);
	if (nodep->expr1p()->isWide()
	    && !nodep->condp()->castConst()
	    && !nodep->condp()->castVarRef()) {
	    // We're going to need the expression several times in the expanded code,
	    // so might as well make it a common expression
	    createDeepTemp(nodep->condp(), false);
	}
	checkNode(nodep);
    }

    // Autoflush
    virtual void visit(AstDisplay* nodep, AstNUser*) {
	startStatement(nodep);
	nodep->iterateChildren(*this);
	m_stmtp = NULL;
	if (v3Global.opt.autoflush()) {
	    AstNode* searchp = nodep->nextp();
	    while (searchp && searchp->castComment()) searchp = searchp->nextp();
	    if (searchp
		&& searchp->castDisplay()
		&& nodep->filep()->sameGateTree(searchp->castDisplay()->filep())) {
		// There's another display next; we can just wait to flush
	    } else {
		UINFO(4,"Autoflush "<<nodep<<endl);
		nodep->addNextHere(new AstFFlush(nodep->fileline(),
						 nodep->filep()->cloneTree(true)));
	    }
	}
    }
    virtual void visit(AstSFormatF* nodep, AstNUser*) {
	nodep->iterateChildren(*this);
	// Any strings sent to a display must be var of string data type,
	// to avoid passing a pointer to a temporary.
	for (AstNode* expp=nodep->exprsp(); expp; expp = expp->nextp()) {
	    if (expp->dtypep()->basicp()->isString()
		&& !expp->castVarRef()) {
		createDeepTemp(expp, true);
	    }
	}
    }

    //--------------------
    // Default: Just iterate
    virtual void visit(AstVar* nodep, AstNUser*) {}	// Don't hit varrefs under vars
    virtual void visit(AstNode* nodep, AstNUser*) {
	nodep->iterateChildren(*this);
    }

public:
    // CONSTUCTORS
    PremitVisitor(AstNetlist* nodep) {
	m_modp = NULL;
	m_funcp = NULL;
	m_stmtp = NULL;
	m_inWhilep = NULL;
	m_inTracep = NULL;
	nodep->accept(*this);
    }
    virtual ~PremitVisitor() {}
};

//----------------------------------------------------------------------
// Top loop

//######################################################################
// Premit class functions

void V3Premit::premitAll(AstNetlist* nodep) {
    UINFO(2,__FUNCTION__<<": "<<endl);
    PremitVisitor visitor (nodep);
    V3Global::dumpCheckGlobalTree("premit.tree", 0, v3Global.opt.dumpTreeLevel(__FILE__) >= 3);
}
