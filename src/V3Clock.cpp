// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Clocking POS/NEGEDGE insertion
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
// V3Clock's Transformations:
//
// Top Scope:
//   Check created ACTIVEs
//      Compress adjacent ACTIVEs with same sensitivity list
//	Form master _eval function
//		Add around the SENTREE a (IF POSEDGE(..))
//			Add a __Vlast_{clock} for the comparison
//			Set the __Vlast_{clock} at the end of the block
//		Replace UNTILSTABLEs with loops until specified signals become const.
//   Create global calling function for any per-scope functions.  (For FINALs).
//
//*************************************************************************

#include "config_build.h"
#include "verilatedos.h"
#include <cstdio>
#include <cstdarg>
#include <unistd.h>
#include <algorithm>

#include "V3Global.h"
#include "V3Clock.h"
#include "V3Ast.h"
#include "V3EmitCBase.h"

//######################################################################
// Clock state, as a visitor of each AstNode

class ClockVisitor : public AstNVisitor {
private:
    // NODE STATE
    // Cleared each Module:
    //  AstVarScope::user1p()	-> AstVarScope*.  Temporary signal that was created.
    //  AstVarScope::user2p()	-> AstVarScope*.  Temporary signal for change detects
    AstUser1InUse	m_inuser1;
    AstUser2InUse	m_inuser2;

    // TYPES
    enum {  DOUBLE_OR_RATE = 10 };	// How many | per ||, Determined experimentally as best

    // STATE
    AstNodeModule*	m_modp;		// Current module
    AstTopScope*	m_topScopep;	// Current top scope
    AstScope*		m_scopep;	// Current scope
    AstActive*		m_activep;	// Current block
    AstUntilStable*	m_untilp;	// Current until
    AstCFunc*		m_evalFuncp;	// Top eval function we are creating
    AstCFunc*		m_initFuncp;	// Top initial function we are creating
    AstCFunc*		m_finalFuncp;	// Top final function we are creating
    AstCFunc*		m_settleFuncp;	// Top settlement function we are creating
    AstSenTree*		m_lastSenp;	// Last sensitivity match, so we can detect duplicates.
    AstIf*		m_lastIfp;	// Last sensitivity if active to add more under
    int			m_stableNum;	// Number of each untilstable

    // METHODS
    static int debug() {
	static int level = -1;
	if (VL_UNLIKELY(level < 0)) level = v3Global.opt.debugSrcLevel(__FILE__);
	return level;
    }

    AstVarScope* getCreateLastClk(AstVarScope* vscp) {
	if (vscp->user1p()) return ((AstVarScope*)vscp->user1p());
	AstVar* varp = vscp->varp();
	if (!varp->width1()) varp->v3error("Unsupported: Clock edge on non-single bit signal: "<<varp->prettyName());
	string newvarname = ((string)"__Vclklast__"+vscp->scopep()->nameDotless()+"__"+varp->name());
	AstVar* newvarp = new AstVar (vscp->fileline(), AstVarType::MODULETEMP, newvarname, VFlagLogicPacked(), 1);
	m_modp->addStmtp(newvarp);
	AstVarScope* newvscp = new AstVarScope(vscp->fileline(), m_scopep, newvarp);
	vscp->user1p(newvscp);
	m_scopep->addVarp(newvscp);
	// At bottom, assign them
	AstAssign* finalp
	    = new AstAssign (vscp->fileline(),
			     new AstVarRef(vscp->fileline(), newvscp, true),
			     new AstVarRef(vscp->fileline(), vscp, false));
	m_evalFuncp->addFinalsp(finalp);
	//
	UINFO(4,"New Last: "<<newvscp<<endl);
	return newvscp;
    }
    AstNode* createSenItemEquation(AstSenItem* nodep) {
	// We know the var is clean, and one bit, so we use binary ops
	// for speed instead of logical ops.
	// POSEDGE:  var & ~var_last
	// NEGEDGE:  ~var & var_last
	// BOTHEDGE:  var ^ var_last
	// HIGHEDGE:  var
	// LOWEDGE:  ~var
	AstNode* newp = NULL;
	AstVarScope* clkvscp = nodep->varrefp()->varScopep();
	if (nodep->edgeType()==AstEdgeType::ET_POSEDGE) {
	    AstVarScope* lastVscp = getCreateLastClk(clkvscp);
	    newp = new AstAnd(nodep->fileline(),
			      new AstVarRef(nodep->fileline(),
					    nodep->varrefp()->varScopep(), false),
			      new AstNot(nodep->fileline(),
					 new AstVarRef(nodep->fileline(),
						       lastVscp, false)));
	} else if (nodep->edgeType()==AstEdgeType::ET_NEGEDGE) {
	    AstVarScope* lastVscp = getCreateLastClk(clkvscp);
	    newp = new AstAnd(nodep->fileline(),
			      new AstNot(nodep->fileline(),
					 new AstVarRef(nodep->fileline(),
						       nodep->varrefp()->varScopep(), false)),
			      new AstVarRef(nodep->fileline(), lastVscp, false));
	} else if (nodep->edgeType()==AstEdgeType::ET_BOTHEDGE) {
	    AstVarScope* lastVscp = getCreateLastClk(clkvscp);
	    newp = new AstXor(nodep->fileline(),
			      new AstVarRef(nodep->fileline(),
					    nodep->varrefp()->varScopep(), false),
			      new AstVarRef(nodep->fileline(), lastVscp, false));
	} else if (nodep->edgeType()==AstEdgeType::ET_HIGHEDGE) {
	    newp = new AstVarRef(nodep->fileline(),
				 clkvscp, false);
	} else if (nodep->edgeType()==AstEdgeType::ET_LOWEDGE) {
	    newp = new AstNot(nodep->fileline(),
			      new AstVarRef(nodep->fileline(),
					    clkvscp, false));
	} else {
	    nodep->v3fatalSrc("Bad edge type");
	}
	return newp;
    }
    AstNode* createSenGateEquation(AstSenGate* nodep) {
	AstNode* newp = new AstAnd(nodep->fileline(),
				   createSenseEquation(nodep->sensesp()),
				   nodep->rhsp()->cloneTree(true));
	return newp;
    }
    AstNode* createSenseEquation(AstNodeSenItem* nodesp) {
	// Nodep may be a list of elements; we need to walk it
	AstNode* senEqnp = NULL;
	for (AstNodeSenItem* senp = nodesp; senp; senp=senp->nextp()->castNodeSenItem()) {
	    AstNode* senOnep = NULL;
	    if (AstSenItem* itemp = senp->castSenItem()) {
		senOnep = createSenItemEquation(itemp);
	    } else if (AstSenGate* itemp = senp->castSenGate()) {
		senOnep = createSenGateEquation(itemp);
	    } else {
		senp->v3fatalSrc("Strange node under sentree");
	    }
	    if (senEqnp) {
		// Add new OR to the sensitivity list equation
		senEqnp = new AstOr(senp->fileline(), senEqnp, senOnep);
	    } else {
		senEqnp = senOnep;
	    }
	}
	return senEqnp;
    }
    AstIf* makeActiveIf(AstSenTree* sensesp) {
	AstNode* senEqnp = createSenseEquation(sensesp->sensesp());
	if (!senEqnp) sensesp->v3fatalSrc("No sense equation, shouldn't be in sequent activation.");
	AstIf* newifp = new AstIf (sensesp->fileline(),
				   senEqnp, NULL, NULL);
	return (newifp);
    }
    void clearLastSen() {
	m_lastSenp = NULL;
	m_lastIfp = NULL;
    }

    // VISITORS
    virtual void visit(AstTopScope* nodep, AstNUser*) {
	UINFO(4," TOPSCOPE   "<<nodep<<endl);
	m_topScopep=nodep;
	m_scopep = nodep->scopep();
	if (!m_scopep) nodep->v3fatalSrc("No scope found on top level, perhaps you have no statements?\n");
	//VV*****  We reset all user1p()
	AstNode::user1ClearTree();
	// Make top functions
	{
	    AstCFunc* funcp = new AstCFunc(nodep->fileline(), "_eval", m_scopep);
	    funcp->argTypes(EmitCBaseVisitor::symClassVar());
	    funcp->dontCombine(true);
	    funcp->symProlog(true);
	    funcp->isStatic(true);
	    funcp->entryPoint(true);
	    m_scopep->addActivep(funcp);
	    m_evalFuncp = funcp;
	}
	{
	    AstCFunc* funcp = new AstCFunc(nodep->fileline(), "_eval_initial", m_scopep);
	    funcp->argTypes(EmitCBaseVisitor::symClassVar());
	    funcp->dontCombine(true);
	    funcp->slow(true);
	    funcp->symProlog(true);
	    funcp->isStatic(true);
	    funcp->entryPoint(true);
	    m_scopep->addActivep(funcp);
	    m_initFuncp = funcp;
	}
	{
	    AstCFunc* funcp = new AstCFunc(nodep->fileline(), "final", m_scopep);
	    funcp->skipDecl(true);
	    funcp->dontCombine(true);
	    funcp->slow(true);
	    funcp->isStatic(false);
	    funcp->entryPoint(true);
	    funcp->addInitsp(new AstCStmt(nodep->fileline(),
					  EmitCBaseVisitor::symClassVar()+" = this->__VlSymsp;\n"));
	    funcp->addInitsp(new AstCStmt(nodep->fileline(), EmitCBaseVisitor::symTopAssign()+"\n"));
	    m_scopep->addActivep(funcp);
	    m_finalFuncp = funcp;
	}
	{
	    AstCFunc* funcp = new AstCFunc(nodep->fileline(), "_eval_settle", m_scopep);
	    funcp->argTypes(EmitCBaseVisitor::symClassVar());
	    funcp->dontCombine(true);
	    funcp->slow(true);
	    funcp->isStatic(true);
	    funcp->symProlog(true);
	    funcp->entryPoint(true);
	    m_scopep->addActivep(funcp);
	    m_settleFuncp = funcp;
	}
	// Process the activates
	nodep->iterateChildren(*this);
	// Done, clear so we can detect errors
	UINFO(4," TOPSCOPEDONE "<<nodep<<endl);
	clearLastSen();
	m_topScopep=NULL;
	m_scopep = NULL;
    }
    virtual void visit(AstNodeModule* nodep, AstNUser*) {
	//UINFO(4," MOD   "<<nodep<<endl);
	m_modp = nodep;
	m_stableNum = 0;
	nodep->iterateChildren(*this);
	m_modp= NULL;
    }
    virtual void visit(AstScope* nodep, AstNUser*) {
	//UINFO(4," SCOPE   "<<nodep<<endl);
	m_scopep = nodep;
	nodep->iterateChildren(*this);
	if (AstNode* movep = nodep->finalClksp()) {
	    if (!m_topScopep) nodep->v3fatalSrc("Final clocks under non-top scope");
	    movep->unlinkFrBackWithNext();
	    m_evalFuncp->addFinalsp(movep);
	}
	m_scopep = NULL;
    }
    virtual void visit(AstAlways* nodep, AstNUser*) {
	AstNode* cmtp = new AstComment(nodep->fileline(), nodep->typeName());
	nodep->replaceWith(cmtp);
	if (AstNode* stmtsp = nodep->bodysp()) {
	    stmtsp->unlinkFrBackWithNext();
	    cmtp->addNextHere(stmtsp);
	}
	nodep->deleteTree(); nodep = NULL;
    }
    virtual void visit(AstAlwaysPost* nodep, AstNUser*) {
	AstNode* cmtp = new AstComment(nodep->fileline(), nodep->typeName());
	nodep->replaceWith(cmtp);
	if (AstNode* stmtsp = nodep->bodysp()) {
	    stmtsp->unlinkFrBackWithNext();
	    cmtp->addNextHere(stmtsp);
	}
	nodep->deleteTree(); nodep = NULL;
    }
    virtual void visit(AstCoverToggle* nodep, AstNUser*) {
	//nodep->dumpTree(cout,"ct:");
	//COVERTOGGLE(INC, ORIG, CHANGE) ->
	//   IF(ORIG ^ CHANGE) { INC; CHANGE = ORIG; }
	AstNode* incp = nodep->incp()->unlinkFrBack();
	AstNode* origp = nodep->origp()->unlinkFrBack();
	AstNode* changep = nodep->changep()->unlinkFrBack();
	AstIf* newp = new AstIf(nodep->fileline(),
				new AstXor(nodep->fileline(),
					   origp,
					   changep),
				incp, NULL);
	// We could add another IF to detect posedges, and only increment if so.
	// It's another whole branch though verus a potential memory miss.
	// We'll go with the miss.
	newp->addIfsp(new AstAssign(nodep->fileline(),
				    changep->cloneTree(false),
				    origp->cloneTree(false)));
	nodep->replaceWith(newp); nodep->deleteTree(); nodep=NULL;
    }
    virtual void visit(AstInitial* nodep, AstNUser*) {
	AstNode* cmtp = new AstComment(nodep->fileline(), nodep->typeName());
	nodep->replaceWith(cmtp);
	if (AstNode* stmtsp = nodep->bodysp()) {
	    stmtsp->unlinkFrBackWithNext();
	    cmtp->addNextHere(stmtsp);
	}
	nodep->deleteTree(); nodep = NULL;
    }
    virtual void visit(AstCFunc* nodep, AstNUser*) {
	nodep->iterateChildren(*this);
	// Link to global function
	if (nodep->formCallTree()) {
	    UINFO(4, "    formCallTree "<<nodep<<endl);
	    AstCCall* callp = new AstCCall(nodep->fileline(), nodep);
	    callp->argTypes("vlSymsp");
	    m_finalFuncp->addStmtsp(callp);
	}
    }
    virtual void visit(AstSenTree* nodep, AstNUser*) {
	// Delete it later; Actives still pointing to it
	nodep->unlinkFrBack();
	pushDeletep(nodep);
    }
    void addToEvalLoop(AstNode* stmtsp) {
	if (m_untilp) m_untilp->addBodysp(stmtsp);  // In a until loop, add to body
	else m_evalFuncp->addStmtsp(stmtsp);  // else add to top level function
    }
    void addToSettleLoop(AstNode* stmtsp) {
	if (m_untilp) m_untilp->addBodysp(stmtsp);  // In a until loop, add to body
	else m_settleFuncp->addStmtsp(stmtsp);  // else add to top level function
    }
    void addToInitial(AstNode* stmtsp) {
	if (m_untilp) m_untilp->addBodysp(stmtsp);  // In a until loop, add to body
	else m_initFuncp->addStmtsp(stmtsp);  // else add to top level function
    }
    virtual void visit(AstActive* nodep, AstNUser*) {
	// Careful if adding variables here, ACTIVES can be under other ACTIVES
	// Need to save and restore any member state in AstUntilStable block
	if (!m_topScopep || !nodep->stmtsp()) {
	    // Not at the top or empty block...
	    // Only empty blocks should be leftover on the non-top.  Killem.
	    if (nodep->stmtsp()) nodep->v3fatalSrc("Non-empty lower active");
	    nodep->unlinkFrBack()->deleteTree(); nodep=NULL;
	} else {
	    UINFO(4,"  ACTIVE  "<<nodep<<endl);
	    AstNode* stmtsp = nodep->stmtsp()->unlinkFrBackWithNext();
	    if (nodep->hasClocked()) {
		// Remember the latest sensitivity so we can compare it next time
		if (nodep->hasInitial()) nodep->v3fatalSrc("Initial block should not have clock sensitivity");
		if (m_lastSenp && nodep->sensesp()->sameTree(m_lastSenp)) {
		    UINFO(4,"    sameSenseTree\n");
		} else {
		    clearLastSen();
		    m_lastSenp = nodep->sensesp();
		    // Make a new if statement
		    m_lastIfp = makeActiveIf(m_lastSenp);
		    addToEvalLoop(m_lastIfp);
		}
		// Move statements to if
		m_lastIfp->addIfsp(stmtsp);
	    } else if (nodep->hasInitial()) {
		// Don't need to: clearLastSen();, as we're adding it to different cfunc
		// Move statements to function
		addToInitial(stmtsp);
	    } else if (nodep->hasSettle()) {
		// Don't need to: clearLastSen();, as we're adding it to different cfunc
		// Move statements to function
		addToSettleLoop(stmtsp);
	    } else {
		// Combo
		clearLastSen();
		// Move statements to function
		addToEvalLoop(stmtsp);
	    }
	    nodep->unlinkFrBack()->deleteTree(); nodep = NULL;
	}
    }

    //--------------------
    // Default: Just iterate
    virtual void visit(AstNode* nodep, AstNUser*) {
	nodep->iterateChildren(*this);
    }

public:
    // CONSTUCTORS
    ClockVisitor(AstNetlist* nodep) {
	m_modp=NULL; m_activep=NULL;
	m_evalFuncp = NULL;
	m_topScopep=NULL;
	m_lastSenp=NULL;
	m_lastIfp = NULL;
	m_scopep = NULL;
	m_stableNum = 0;
	m_untilp = NULL;
	//
	nodep->accept(*this);
    }
    virtual ~ClockVisitor() {}
};

//######################################################################
// Clock class functions

void V3Clock::clockAll(AstNetlist* nodep) {
    UINFO(2,__FUNCTION__<<": "<<endl);
    ClockVisitor visitor (nodep);
    V3Global::dumpCheckGlobalTree("clock.tree", 0, v3Global.opt.dumpTreeLevel(__FILE__) >= 3);
}
