// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Collect and print statistics
//
// Code available from: http://www.veripool.org/verilator
//
//*************************************************************************
//
// Copyright 2005-2015 by Wilson Snyder.  This program is free software; you can
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

#include "config_build.h"
#include "verilatedos.h"
#include <cstdio>
#include <cstdarg>
#include <unistd.h>
#include <map>
#include <iomanip>

#include "V3Global.h"
#include "V3Assert.h"
#include "V3Ast.h"
#include "V3GraphDfa.h"
#include "V3Stats.h"

//######################################################################
// Assert class functions

class AssertVisitor : public AstNVisitor {
private:
    // NODE STATE/TYPES
    // Cleared on netlist
    //  AstNode::user()		-> bool.  True if processed
    AstUser1InUse	m_inuser1;

    // STATE
    AstNodeModule*	m_modp;		// Last module
    AstBegin*	m_beginp;	// Last begin
    V3Double0	m_statAsCover;	// Statistic tracking
    V3Double0	m_statAsPsl;	// Statistic tracking
    V3Double0	m_statAsFull;	// Statistic tracking
    V3Double0	m_statAsSV;	// Statistic tracking

    // METHODS
    string assertDisplayMessage(AstNode* nodep, const string& prefix, const string& message) {
	return (string("[%0t] "+prefix+": ")+nodep->fileline()->filebasename()
		+":"+cvtToStr(nodep->fileline()->lineno())
		+": Assertion failed in %m"
		+((message != "")?": ":"")+message
		+"\n");
    }
    void replaceDisplay(AstDisplay* nodep, const string& prefix) {
	nodep->displayType(AstDisplayType::DT_WRITE);
	nodep->fmtp()->text(assertDisplayMessage(nodep, prefix, nodep->fmtp()->text()));
	// cppcheck-suppress nullPointer
	AstNode* timenewp = new AstTime(nodep->fileline());
	if (AstNode* timesp = nodep->fmtp()->exprsp()) {
	    timesp->unlinkFrBackWithNext();
	    timenewp->addNext(timesp);
	}
	nodep->fmtp()->exprsp(timenewp);
	if (!nodep->fmtp()->scopeNamep() && nodep->fmtp()->formatScopeTracking()) {
	    nodep->fmtp()->scopeNamep(new AstScopeName(nodep->fileline()));
	}
    }

    AstNode* newIfAssertOn(AstNode* nodep) {
	// Add a internal if to check assertions are on.
	// Don't make this a AND term, as it's unlikely to need to test this.
	AstNode* newp
	    = new AstIf (nodep->fileline(),
			 // If assertions are off, have constant propagation rip them out later
			 // This allows syntax errors and such to be detected normally.
			 (v3Global.opt.assertOn()
			  ? (AstNode*)(new AstCMath(nodep->fileline(), "Verilated::assertOn()", 1))
			  : (AstNode*)(new AstConst(nodep->fileline(), AstConst::LogicFalse()))),
			 nodep, NULL);
	newp->user1(true); // Don't assert/cover this if
	return newp;
    }

    AstNode* newFireAssert(AstNode* nodep, const string& message) {
	AstDisplay* dispp = new AstDisplay (nodep->fileline(), AstDisplayType::DT_ERROR, message, NULL, NULL);
	AstNode* bodysp = dispp;
	replaceDisplay(dispp, "%%Error");   // Convert to standard DISPLAY format
	bodysp->addNext(new AstStop (nodep->fileline()));
	bodysp = newIfAssertOn(bodysp);
	return bodysp;
    }

    void newPslAssertion(AstNode* nodep, AstNode* propp, AstSenTree* sentreep,
			 AstNode* stmtsp, const string& message) {
	propp->unlinkFrBack();
	sentreep->unlinkFrBack();
	if (stmtsp) stmtsp->unlinkFrBack();
	//
	AstNode* bodysp = NULL;
	bool selfDestruct = false;
	if (AstPslCover* snodep = nodep->castPslCover()) {
	    if (!v3Global.opt.coverageUser()) {
		selfDestruct = true;
	    } else {
		// V3Coverage assigned us a bucket to increment.
		AstCoverInc* covincp = snodep->coverincp()->castCoverInc();
		if (!covincp) snodep->v3fatalSrc("Missing AstCoverInc under assertion");
		covincp->unlinkFrBack();
		if (message!="") covincp->declp()->comment(message);
		bodysp = covincp;
	    }
	} else {
	    nodep->v3fatalSrc("Unknown node type");
	}
	if (stmtsp) bodysp = bodysp->addNext(stmtsp);
	AstIf* ifp = new AstIf (nodep->fileline(), propp, bodysp, NULL);
	bodysp = ifp;
	if (nodep->castVAssert()) ifp->branchPred(AstBranchPred::BP_UNLIKELY);
	//
	AstNode* newp = new AstAlways (nodep->fileline(),
				       VAlwaysKwd::ALWAYS,
				       sentreep,
				       bodysp);
	// Install it
	if (selfDestruct) {
	    // Delete it after making the tree.  This way we can tell the user
	    // if it wasn't constructed nicely or has other errors without needing --coverage.
	    newp->deleteTree();
	    nodep->unlinkFrBack();
	} else {
	    nodep->replaceWith(newp);
	}
	// Bye
	pushDeletep(nodep); nodep=NULL;
    }

    void newVAssertion(AstVAssert* nodep, AstNode* propp) {
	propp->unlinkFrBackWithNext();
	AstNode* passsp = nodep->passsp(); if (passsp) passsp->unlinkFrBackWithNext();
	AstNode* failsp = nodep->failsp(); if (failsp) failsp->unlinkFrBackWithNext();
	//
	if (nodep->castVAssert()) {
	    if (passsp) passsp = newIfAssertOn(passsp);
	    if (failsp) failsp = newIfAssertOn(failsp);
	} else {
	    nodep->v3fatalSrc("Unknown node type");
	}

	AstIf* ifp = new AstIf (nodep->fileline(), propp, passsp, failsp);
	AstNode* newp = ifp;
	if (nodep->castVAssert()) ifp->branchPred(AstBranchPred::BP_UNLIKELY);
	//
	// Install it
	nodep->replaceWith(newp);
	// Bye
	pushDeletep(nodep); nodep=NULL;
    }
    
    virtual void visit(AstIf* nodep, AstNUser*) {
	if (nodep->user1SetOnce()) return;
	if (nodep->uniquePragma() || nodep->unique0Pragma()) {
	    AstNodeIf* ifp = nodep;
	    AstNode* propp = NULL;
	    bool hasDefaultElse = false;
	    do {
		// If this statement ends with 'else if', then nextIf will point to the
		// nextIf statement.  Otherwise it will be null.
		AstNodeIf* nextifp = dynamic_cast<AstNodeIf*>(ifp->elsesp());
		ifp->condp()->iterateAndNext(*this);

		// Recurse into the true case.
		ifp->ifsp()->iterateAndNext(*this);
		
		// If the last else is not an else if, recurse into that too.
		if (ifp->elsesp() && !nextifp) {
		    ifp->elsesp()->iterateAndNext(*this);
		}
		
		// Build a bitmask of the true predicates
	        AstNode* predp = ifp->condp()->cloneTree(false);
	        if (propp) {
		    propp = new AstConcat(nodep->fileline(), predp, propp);
		} else {
		    propp = predp;
		}

		// Record if this ends with an 'else' that does not have an if
		if (ifp->elsesp() && !nextifp) {
		    hasDefaultElse = true;
		}
		
		ifp = nextifp;
	    } while (ifp);

	    AstNode *newifp = nodep->cloneTree(false);
	    bool allow_none = nodep->unique0Pragma();
	    
	    // Note: if this ends with an 'else', then we don't need to validate that one of the
	    // predicates evaluates to true.
	    AstNode* ohot = ((allow_none || hasDefaultElse)
			     ? (new AstOneHot0(nodep->fileline(), propp))->castNode()
			     : (new AstOneHot (nodep->fileline(), propp))->castNode());
	    AstIf* checkifp = new AstIf (nodep->fileline(),
					 new AstLogNot (nodep->fileline(), ohot),
					 newFireAssert(nodep, "'unique if' statement violated"),
					 newifp);
	    checkifp->branchPred(AstBranchPred::BP_UNLIKELY);
	    nodep->replaceWith(checkifp);
	    pushDeletep(nodep);
	} else {
	    nodep->iterateChildren(*this);
	}
    }

    // VISITORS  //========== Case assertions
    virtual void visit(AstCase* nodep, AstNUser*) {
	nodep->iterateChildren(*this);
	if (!nodep->user1SetOnce()) {
	    bool has_default=false;
	    for (AstCaseItem* itemp = nodep->itemsp(); itemp; itemp=itemp->nextp()->castCaseItem()) {
		if (itemp->isDefault()) has_default=true;
	    }
	    if (nodep->fullPragma() || nodep->priorityPragma()) {
		// Simply need to add a default if there isn't one already
		++m_statAsFull;
		if (!has_default) {
		    nodep->addItemsp(new AstCaseItem(nodep->fileline(), NULL/*DEFAULT*/,
						     newFireAssert(nodep, "synthesis full_case, but non-match found")));
		}
	    }
	    if (nodep->parallelPragma() || nodep->uniquePragma() || nodep->unique0Pragma()) {
		// Need to check that one, and only one of the case items match at any moment
		// If there's a default, we allow none to match, else exactly one must match
		++m_statAsFull;
		if (!has_default && !nodep->itemsp()) {
		    // Not parallel, but harmlessly so.
		} else {
		    AstNode* propp = NULL;
		    for (AstCaseItem* itemp = nodep->itemsp(); itemp; itemp=itemp->nextp()->castCaseItem()) {
			for (AstNode* icondp = itemp->condsp(); icondp!=NULL; icondp=icondp->nextp()) {
			    AstNode* onep = new AstEq(icondp->fileline(),
						      nodep->exprp()->cloneTree(false),
						      icondp->cloneTree(false));
			    if (propp) propp = new AstConcat(icondp->fileline(), onep, propp);
			    else propp = onep;
			}
		    }
		    bool allow_none = has_default || nodep->unique0Pragma();
		    AstNode* ohot = (allow_none
				     ? (new AstOneHot0(nodep->fileline(), propp))->castNode()
				     : (new AstOneHot (nodep->fileline(), propp))->castNode());
		    AstIf* ifp = new AstIf (nodep->fileline(),
					    new AstLogNot (nodep->fileline(), ohot),
					    newFireAssert(nodep, "synthesis parallel_case, but multiple matches found"),
					    NULL);
		    ifp->branchPred(AstBranchPred::BP_UNLIKELY);
		    nodep->addNotParallelp(ifp);
		}
	    }
	}
    }

    // VISITORS  //========== Statements
    virtual void visit(AstDisplay* nodep, AstNUser*) {
	nodep->iterateChildren(*this);
	// Replace the special types with standard text
	if (nodep->displayType()==AstDisplayType::DT_INFO) {
	    replaceDisplay(nodep, "-Info");
	} else if (nodep->displayType()==AstDisplayType::DT_WARNING) {
	    replaceDisplay(nodep, "%%Warning");
	} else if (nodep->displayType()==AstDisplayType::DT_ERROR
		   || nodep->displayType()==AstDisplayType::DT_FATAL) {
	    replaceDisplay(nodep, "%%Error");
	}
    }

    virtual void visit(AstPslCover* nodep, AstNUser*) {
	nodep->iterateChildren(*this);
	if (m_beginp && nodep->name() == "") nodep->name(m_beginp->name());
	newPslAssertion(nodep, nodep->propp(), nodep->sentreep(),
			nodep->stmtsp(), nodep->name()); nodep=NULL;
	++m_statAsCover;
    }
    virtual void visit(AstVAssert* nodep, AstNUser*) {
	nodep->iterateChildren(*this);
	newVAssertion(nodep, nodep->propp()); nodep=NULL;
	++m_statAsSV;
    }

    virtual void visit(AstNodeModule* nodep, AstNUser*) {
	m_modp = nodep;
	//
	nodep->iterateChildren(*this);
	// Reset defaults
	m_modp = NULL;
    }
    virtual void visit(AstBegin* nodep, AstNUser*) {
	// This code is needed rather than a visitor in V3Begin,
	// because V3Assert is called before V3Begin
	AstBegin* lastp = m_beginp;
	{
	    m_beginp = nodep;
	    nodep->iterateChildren(*this);
	}
	m_beginp = lastp;
    }

    virtual void visit(AstNode* nodep, AstNUser*) {
	nodep->iterateChildren(*this);
    }
public:
    // CONSTRUCTORS
    AssertVisitor(AstNetlist* nodep) {
	m_beginp = NULL;
	m_modp = NULL;
	// Process
	nodep->accept(*this);
    }
    virtual ~AssertVisitor() {
	V3Stats::addStat("Assertions, PSL asserts", m_statAsPsl);
	V3Stats::addStat("Assertions, SystemVerilog asserts", m_statAsSV);
	V3Stats::addStat("Assertions, cover statements", m_statAsCover);
	V3Stats::addStat("Assertions, full/parallel case", m_statAsFull);
    }
};

//######################################################################
// Top Assert class

void V3Assert::assertAll(AstNetlist* nodep) {
    UINFO(2,__FUNCTION__<<": "<<endl);
    AssertVisitor visitor (nodep);
    V3Global::dumpCheckGlobalTree("assert.tree", 0, v3Global.opt.dumpTreeLevel(__FILE__) >= 3);
}
