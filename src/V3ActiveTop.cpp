// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Break always into sensitivity active domains
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
// V3Active's Transformations:
//
// Note this can be called multiple times.
//   Across all ACTIVES
//	SenTrees are now under each ACTIVE statement, we want them global:
//	    Find SenTree in under global TopScope, or create it there
//	    Move SenTree the global SenTree
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
#include "V3ActiveTop.h"
#include "V3Ast.h"
#include "V3SenTree.h"
#include "V3Const.h"

//######################################################################
// Active class functions

class ActiveTopVisitor : public AstNVisitor {
private:
    // NODE STATE
    //  Entire netlist
    //   AstNode::user()		bool. True if processed
    //  Each call to V3Const::constify
    //   AstNode::user4()		Used by V3Const::constify, called below
    AstUser1InUse	m_inuser1;

    // STATE
    AstTopScope*	m_topscopep;	// Top scope for adding sentrees under
    SenTreeFinder	m_finder;	// Find global sentree's and add them

    // METHODS
    static int debug() {
	static int level = -1;
	if (VL_UNLIKELY(level < 0)) level = v3Global.opt.debugSrcLevel(__FILE__);
	return level;
    }

    // VISITORS
    virtual void visit(AstTopScope* nodep, AstNUser*) {
	m_topscopep = nodep;
	m_finder.main(m_topscopep);
	nodep->iterateChildren(*this);
	m_topscopep = NULL;
    }
    virtual void visit(AstNodeModule* nodep, AstNUser*) {
	// Create required actives and add to module
	// We can start ordering at a module, or a scope
	UINFO(4," MOD   "<<nodep<<endl);
	nodep->iterateChildren(*this);
    }
    virtual void visit(AstActive* nodep, AstNUser*) {
	UINFO(4,"   ACTIVE "<<nodep<<endl);
	V3Const::constifyExpensiveEdit(nodep); // Remove duplicate clocks and such; sensesp() may change!
	AstSenTree* sensesp = nodep->sensesp();
	if (!sensesp) nodep->v3fatalSrc("NULL");
	if (sensesp->sensesp()
	    && sensesp->sensesp()->castSenItem()
	    && sensesp->sensesp()->castSenItem()->isNever()) {
	    // Never executing.  Kill it.
	    if (sensesp->sensesp()->nextp()) nodep->v3fatalSrc("Never senitem should be alone, else the never should be eliminated.");
	    nodep->unlinkFrBack()->deleteTree(); nodep=NULL;
	    return;
	}
	// Copy combo tree to settlement tree with duplicated statements
	if (sensesp->hasCombo()) {
	    AstSenTree* newsentreep
		= new AstSenTree (nodep->fileline(),
				  new AstSenItem (nodep->fileline(), AstSenItem::Settle()));
	    AstActive* newp = new AstActive(nodep->fileline(),"settle", newsentreep);
	    newp->sensesStorep(newsentreep);
	    if (nodep->stmtsp()) newp->addStmtsp(nodep->stmtsp()->cloneTree(true));
	    nodep->addNextHere(newp);
	}
	// Move the SENTREE for each active up to the global level.
	// This way we'll easily see what clock domains are identical
	AstSenTree* wantp = m_finder.getSenTree(nodep->fileline(), sensesp);
	UINFO(4,"   lookdone\n");
	if (wantp != sensesp) {
	    // Move the active's contents to the other active
	    UINFO(4,"   merge active "<<sensesp<<" into "<<wantp<<endl);
	    if (nodep->sensesStorep()) {
		if (sensesp != nodep->sensesStorep()) nodep->v3fatalSrc("sensesStore should have been deleted earlier if different\n");
		sensesp->unlinkFrBack();
		// There may be other references to same sense tree,
		// we'll be removing all references when we get to them,
		// but don't dangle our pointer yet!
		pushDeletep(sensesp);
	    }
	    nodep->sensesp(wantp);
	}
	// No need to do statements under it, they're already moved.
	//nodep->iterateChildren(*this);
    }
    virtual void visit(AstInitial* nodep, AstNUser*) {
	nodep->v3fatalSrc("Node should have been under ACTIVE");
    }
    virtual void visit(AstAssignAlias* nodep, AstNUser*) {
	nodep->v3fatalSrc("Node should have been under ACTIVE");
    }
    virtual void visit(AstAssignW* nodep, AstNUser*) {
	nodep->v3fatalSrc("Node should have been under ACTIVE");
    }
    virtual void visit(AstAlways* nodep, AstNUser*) {
	nodep->v3fatalSrc("Node should have been under ACTIVE");
    }
    virtual void visit(AstAlwaysPublic* nodep, AstNUser*) {
	nodep->v3fatalSrc("Node should have been under ACTIVE");
    }
    virtual void visit(AstFinal* nodep, AstNUser*) {
	nodep->v3fatalSrc("Node should have been deleted");
    }
    // Empty visitors, speed things up
    virtual void visit(AstNodeMath* nodep, AstNUser*) {}
    virtual void visit(AstVarScope* nodep, AstNUser*) {}
    //--------------------
    virtual void visit(AstNode* nodep, AstNUser*) {
	nodep->iterateChildren(*this);
    }
public:
    // CONSTUCTORS
    ActiveTopVisitor(AstNetlist* nodep) {
	m_topscopep = NULL;
	nodep->accept(*this);
    }
    virtual ~ActiveTopVisitor() {}
};

//######################################################################
// Active class functions

void V3ActiveTop::activeTopAll(AstNetlist* nodep) {
    UINFO(2,__FUNCTION__<<": "<<endl);
    ActiveTopVisitor visitor (nodep);
    V3Global::dumpCheckGlobalTree("activetop.tree", 0, v3Global.opt.dumpTreeLevel(__FILE__) >= 3);
}
