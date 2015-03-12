// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Replace return/continue with jumps
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
// V3LinkJump's Transformations:
//
// Each module:
//	Look for BEGINs
//	    BEGIN(VAR...) -> VAR ... {renamed}
//	FOR -> WHILEs
//
//*************************************************************************

#include "config_build.h"
#include "verilatedos.h"
#include <cstdio>
#include <cstdarg>
#include <unistd.h>
#include <algorithm>
#include <vector>

#include "V3Global.h"
#include "V3LinkJump.h"
#include "V3Ast.h"

//######################################################################

class LinkJumpVisitor : public AstNVisitor {
private:
    // TYPES
    typedef vector<AstBegin*> BeginStack;

    // STATE
    AstNodeModule*	m_modp;		// Current module
    AstNodeFTask* 	m_ftaskp;	// Current function/task
    AstWhile*	 	m_loopp;	// Current loop
    bool		m_loopInc;	// In loop increment
    int			m_repeatNum;	// Repeat counter
    BeginStack		m_beginStack;	// All begin blocks above current node

    // METHODS
    static int debug() {
	static int level = -1;
	if (VL_UNLIKELY(level < 0)) level = v3Global.opt.debugSrcLevel(__FILE__);
	return level;
    }

    AstJumpLabel* findAddLabel(AstNode* nodep, bool endOfIter) {
	// Put label under given node, and if WHILE optionally at end of iteration
	UINFO(4,"Create label for "<<nodep<<endl);
	if (nodep->castJumpLabel()) return nodep->castJumpLabel(); // Done

	AstNode* underp = NULL;
	bool     under_and_next = true;
	if (nodep->castBegin()) underp = nodep->castBegin()->stmtsp();
	else if (nodep->castNodeFTask()) underp = nodep->castNodeFTask()->stmtsp();
	else if (nodep->castWhile()) {
	    if (endOfIter) {
		// Note we jump to end of bodysp; a FOR loop has its increment under incsp() which we don't skip
		underp = nodep->castWhile()->bodysp();
	    } else {
		underp = nodep; under_and_next=false; // IE we skip the entire while
	    }
	}
	else {
	    nodep->v3fatalSrc("Unknown jump point for break/disable/continue");
	    return NULL;
	}
	// Skip over variables as we'll just move them in a momement
	// Also this would otherwise prevent us from using a label twice
	// see t_func_return test.
	while (underp && underp->castVar()) underp = underp->nextp();
	if (underp) UINFO(5,"  Underpoint is "<<underp<<endl);

	if (!underp) {
	    nodep->v3fatalSrc("Break/disable/continue not under expected statement");
	    return NULL;
	} else if (underp->castJumpLabel()) {
	    return underp->castJumpLabel();
	} else { // Move underp stuff to be under a new label
	    AstJumpLabel* labelp = new AstJumpLabel(nodep->fileline(), NULL);

	    AstNRelinker repHandle;
	    if (under_and_next) underp->unlinkFrBackWithNext(&repHandle);
	    else underp->unlinkFrBack(&repHandle);
	    repHandle.relink(labelp);

	    labelp->addStmtsp(underp);
	    // Keep any AstVars under the function not under the new JumpLabel
	    for (AstNode* nextp, *varp=underp; varp; varp = nextp) {
		nextp = varp->nextp();
		if (varp->castVar()) {
		    labelp->addPrev(varp->unlinkFrBack());
		}
	    }
	    return labelp;
	}
    }

    // VISITORS
    virtual void visit(AstNodeModule* nodep, AstNUser*) {
	if (nodep->dead()) return;
	m_modp = nodep;
	m_repeatNum = 0;
	nodep->iterateChildren(*this);
	m_modp = NULL;
    }
    virtual void visit(AstNodeFTask* nodep, AstNUser*) {
	m_ftaskp = nodep;
	nodep->iterateChildren(*this);
	m_ftaskp = NULL;
    }
    virtual void visit(AstBegin* nodep, AstNUser*) {
	UINFO(8,"  "<<nodep<<endl);
	m_beginStack.push_back(nodep);
	nodep->iterateChildren(*this);
	m_beginStack.pop_back();
    }
    virtual void visit(AstRepeat* nodep, AstNUser*) {
	// So later optimizations don't need to deal with them,
	//    REPEAT(count,body) -> loop=count,WHILE(loop>0) { body, loop-- }
	// Note var can be signed or unsigned based on original number.
	AstNode* countp = nodep->countp()->unlinkFrBackWithNext();
   	string name = string("__Vrepeat")+cvtToStr(m_repeatNum++);
	// Spec says value is integral, if negative is ignored
	AstVar* varp = new AstVar(nodep->fileline(), AstVarType::BLOCKTEMP, name,
				  nodep->findSigned32DType());
	varp->usedLoopIdx(true);
	m_modp->addStmtp(varp);
	AstNode* initsp = new AstAssign(nodep->fileline(), new AstVarRef(nodep->fileline(), varp, true),
					countp);
	AstNode* decp = new AstAssign(nodep->fileline(), new AstVarRef(nodep->fileline(), varp, true),
				      new AstSub(nodep->fileline(), new AstVarRef(nodep->fileline(), varp, false),
						 new AstConst(nodep->fileline(), 1)));
	V3Number zero (nodep->fileline(), 32, 0);  zero.isSigned(true);
	AstNode* zerosp = new AstConst(nodep->fileline(), zero);
	AstNode* condp = new AstGtS(nodep->fileline(), new AstVarRef(nodep->fileline(), varp, false),
				    zerosp);
	AstNode* bodysp = nodep->bodysp(); if (bodysp) bodysp->unlinkFrBackWithNext();
	AstNode* newp = new AstWhile(nodep->fileline(),
				     condp,
				     bodysp,
				     decp);
	initsp = initsp->addNext(newp);
	newp = initsp;
	nodep->replaceWith(newp);
	nodep->deleteTree(); nodep=NULL;
    }
    virtual void visit(AstWhile* nodep, AstNUser*) {
	// Don't need to track AstRepeat/AstFor as they have already been converted
	AstWhile* lastLoopp = m_loopp;
	bool lastInc = m_loopInc;
	m_loopp = nodep;
	m_loopInc = false;
	nodep->precondsp()->iterateAndNext(*this);
	nodep->condp()->iterateAndNext(*this);
	nodep->bodysp()->iterateAndNext(*this);
	m_loopInc = true;
	nodep->incsp()->iterateAndNext(*this);
	m_loopInc = lastInc;
	m_loopp = lastLoopp;
    }
    virtual void visit(AstReturn* nodep, AstNUser*) {
	nodep->iterateChildren(*this);
	AstFunc* funcp = m_ftaskp->castFunc();
	if (!m_ftaskp) { nodep->v3error("Return isn't underneath a task or function"); }
	else if (funcp  && !nodep->lhsp()) { nodep->v3error("Return underneath a function should have return value"); }
	else if (!funcp &&  nodep->lhsp()) { nodep->v3error("Return underneath a task shouldn't have return value"); }
	else {
	    if (funcp && nodep->lhsp()) {
		// Set output variable to return value
		nodep->addPrev(new AstAssign(nodep->fileline(),
					     new AstVarRef(nodep->fileline(), funcp->fvarp()->castVar(), true),
					     nodep->lhsp()->unlinkFrBackWithNext()));
	    }
	    // Jump to the end of the function call
	    AstJumpLabel* labelp = findAddLabel(m_ftaskp, false);
	    nodep->addPrev(new AstJumpGo(nodep->fileline(), labelp));
	}
	nodep->unlinkFrBack(); pushDeletep(nodep); nodep=NULL;
    }
    virtual void visit(AstBreak* nodep, AstNUser*) {
	nodep->iterateChildren(*this);
	if (!m_loopp) { nodep->v3error("break isn't underneath a loop"); }
	else {
	    // Jump to the end of the loop
	    AstJumpLabel* labelp = findAddLabel(m_loopp, false);
	    nodep->addNextHere(new AstJumpGo(nodep->fileline(), labelp));
	}
	nodep->unlinkFrBack(); pushDeletep(nodep); nodep=NULL;
    }
    virtual void visit(AstContinue* nodep, AstNUser*) {
	nodep->iterateChildren(*this);
	if (!m_loopp) { nodep->v3error("continue isn't underneath a loop"); }
	else {
	    // Jump to the end of this iteration
	    // If a "for" loop then need to still do the post-loop increment
	    AstJumpLabel* labelp = findAddLabel(m_loopp, true);
	    nodep->addNextHere(new AstJumpGo(nodep->fileline(), labelp));
	}
	nodep->unlinkFrBack(); pushDeletep(nodep); nodep=NULL;
    }
    virtual void visit(AstDisable* nodep, AstNUser*) {
	UINFO(8,"   DISABLE "<<nodep<<endl);
	nodep->iterateChildren(*this);
	AstBegin* beginp = NULL;
	for (BeginStack::reverse_iterator it = m_beginStack.rbegin(); it != m_beginStack.rend(); ++it) {
	    UINFO(9,"    UNDERBLK  "<<*it<<endl);
	    if ((*it)->name() == nodep->name()) {
		beginp = *it;
		break;
	    }
	}
	//if (debug()>=9) { UINFO(0,"\n"); beginp->dumpTree(cout,"  labeli: "); }
	if (!beginp) { nodep->v3error("disable isn't underneath a begin with name: "<<nodep->prettyName()); }
	else {
	    // Jump to the end of the named begin
	    AstJumpLabel* labelp = findAddLabel(beginp, false);
	    nodep->addNextHere(new AstJumpGo(nodep->fileline(), labelp));
	}
	nodep->unlinkFrBack(); pushDeletep(nodep); nodep=NULL;
	//if (debug()>=9) { UINFO(0,"\n"); beginp->dumpTree(cout,"  labelo: "); }
    }
    virtual void visit(AstVarRef* nodep, AstNUser*) {
	if (m_loopInc && nodep->varp()) nodep->varp()->usedLoopIdx(true);
    }

    virtual void visit(AstConst* nodep, AstNUser*) {}
    virtual void visit(AstNode* nodep, AstNUser*) {
	nodep->iterateChildren(*this);
    }
public:
    // CONSTUCTORS
    LinkJumpVisitor(AstNetlist* nodep) {
	m_modp = NULL;
	m_ftaskp = NULL;
	m_loopp = NULL;
	m_loopInc = false;
	m_repeatNum = 0;
	nodep->accept(*this);
    }
    virtual ~LinkJumpVisitor() {}
};

//######################################################################
// Task class functions

void V3LinkJump::linkJump(AstNetlist* nodep) {
    UINFO(2,__FUNCTION__<<": "<<endl);
    LinkJumpVisitor bvisitor (nodep);
    V3Global::dumpCheckGlobalTree("link.tree", 0, v3Global.opt.dumpTreeLevel(__FILE__) >= 3);
}
