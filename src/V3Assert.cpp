// $Id$
//*************************************************************************
// DESCRIPTION: Verilator: Collect and print statistics
//
// Code available from: http://www.veripool.com/verilator
//
// AUTHORS: Wilson Snyder with Paul Wasson, Duane Gabli
//
//*************************************************************************
//
// Copyright 2005-2006 by Wilson Snyder.  This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// General Public License or the Perl Artistic License.
//
// Verilator is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
//*************************************************************************

#include "config.h"
#include <stdio.h>
#include <stdarg.h>
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

    // STATE
    AstModule*	m_modp;		// Last module
    V3Double0	m_statAsCover;	// Statistic tracking
    V3Double0	m_statAsPsl;	// Statistic tracking
    V3Double0	m_statAsFull;	// Statistic tracking

    // METHODS
    AstNode* newFireAssert(AstNode* nodep, const string& message) {
	AstNode* bodysp = new AstDisplay
	    (nodep->fileline(), '\0',
	     (string("[%0t] %%Error: ")+nodep->fileline()->filebasename()
	      +":"+cvtToStr(nodep->fileline()->lineno())
	      +": Assertion failed in %m"
	      +((message != "")?": ":"")+message
	      +"\\n"),
	     NULL,
	     new AstTime(nodep->fileline()));
	bodysp->addNext(new AstStop (nodep->fileline()));
	// Add a internal if to check assertions are on.
	// Don't make this a AND term, as it's unlikely to need to test this.
	bodysp = new AstIf (nodep->fileline(),
			    new AstCMath(nodep->fileline(), "Verilated::assertOn()", 1),
			    bodysp, NULL);
	return bodysp;
    }

    void newAssertion(AstNode* nodep, AstNode* propp, AstSenTree* sentreep, const string& message) {
	propp->unlinkFrBack();
	sentreep->unlinkFrBack();
	//
	AstNode* bodysp = NULL;
	bool selfDestruct = false;	
	if (AstPslCover* snodep = nodep->castPslCover()) {
	    if (!v3Global.opt.coverageUser()) {
		selfDestruct = true;
	    } else {
		// V3Coverage assigned us a bucket to increment.
		AstCoverInc* covincp = snodep->coverincp()->castCoverInc();
		if (!covincp) snodep->v3fatalSrc("Missing coverage in PSL");
		covincp->unlinkFrBack();
		if (message!="") covincp->declp()->comment(message);
		bodysp = covincp;
	    }
	} else if (nodep->castPslAssert()) {
	    bodysp = newFireAssert(nodep,message);
	    // We assert the property is always true... so report when it fails
	    // (Note this is opposite the behavior of coverage statements.)
	    // Need: 'never' operator: not hold in current or any future cycle
	    propp = new AstLogNot (nodep->fileline(), propp);
	} else {
	    nodep->v3fatalSrc("Unknown node type");
	}
	AstIf* ifp = new AstIf (nodep->fileline(), propp, bodysp, NULL);
	bodysp = ifp;
	if (nodep->castPslAssert()) ifp->branchPred(AstBranchPred::UNLIKELY);
	//
	AstNode* newp = new AstAlways (nodep->fileline(),
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

    // VISITORS  //========== Case assertions
    virtual void visit(AstCase* nodep, AstNUser*) {
	nodep->iterateChildren(*this);
	if (!nodep->user()) {
	    nodep->user(true);
	    bool has_default=false;
	    for (AstCaseItem* itemp = nodep->itemsp(); itemp; itemp=itemp->nextp()->castCaseItem()) {
		if (itemp->isDefault()) has_default=true;
	    }
	    if (nodep->fullPragma()) {
		// Simply need to add a default if there isn't one already
		m_statAsFull++;
		if (!has_default) {
		    nodep->addItemsp(new AstCaseItem(nodep->fileline(), NULL/*DEFAULT*/,
						     newFireAssert(nodep, "synthesis full_case, but non-match found")));
		}
	    }
	    if (nodep->parallelPragma()) {
		// Need to check that one, and only one of the case items match at any moment
		// If there's a default, we allow none to match, else exactly one must match
		m_statAsFull++;
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
		    AstNode* ohot = (has_default
				     ? (new AstOneHot0(nodep->fileline(), propp))->castNode()
				     : (new AstOneHot (nodep->fileline(), propp))->castNode());
		    AstIf* ifp = new AstIf (nodep->fileline(),
					    new AstLogNot (nodep->fileline(), ohot),
					    newFireAssert(nodep, "synthesis parallel_case, but multiple matches found"),
					    NULL);
		    ifp->branchPred(AstBranchPred::UNLIKELY);
		    nodep->addNotParallelp(ifp);
		}
	    }
	}
    }

    // VISITORS  //========== Statements
    virtual void visit(AstPslCover* nodep, AstNUser*) {
	nodep->iterateChildren(*this);
	newAssertion(nodep, nodep->propp(), nodep->sentreep(), nodep->name()); nodep=NULL;
	m_statAsCover++;
    }
    virtual void visit(AstPslAssert* nodep, AstNUser*) {
	nodep->iterateChildren(*this);
	newAssertion(nodep, nodep->propp(), nodep->sentreep(), nodep->name()); nodep=NULL;
	m_statAsPsl++;
    }

    virtual void visit(AstModule* nodep, AstNUser*) {
	m_modp = nodep;
	//
	nodep->iterateChildren(*this);
	// Reset defaults
	m_modp = NULL;
    }

    // VISITORS  //========== Temporal Layer

    // VISITORS  //========== Boolean Layer
    virtual void visit(AstPslBool* nodep, AstNUser*) {
	nodep->replaceWith(nodep->exprp()->unlinkFrBack());
	pushDeletep(nodep); nodep=NULL;
    }

    virtual void visit(AstNode* nodep, AstNUser*) {
	nodep->iterateChildren(*this);
    }
public:
    // CONSTRUCTORS
    AssertVisitor(AstNetlist* nodep) {
	m_modp = NULL;
	// Process
	AstNode::userClearTree();	// userp() used on entire tree
	nodep->accept(*this);
    }
    virtual ~AssertVisitor() {
	V3Stats::addStat("Assertions, PSL asserts", m_statAsPsl);
	V3Stats::addStat("Assertions, cover statements", m_statAsCover);
	V3Stats::addStat("Assertions, full/parallel case", m_statAsFull);
    }
};

//######################################################################
// Top Assert class

void V3Assert::assertAll(AstNetlist* nodep) {
    UINFO(2,__FUNCTION__<<": "<<endl);
    AssertVisitor visitor (nodep);
}
