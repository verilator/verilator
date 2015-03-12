// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: AssignPost Variable assignment elimination
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
// LIFE TRANSFORMATIONS:
//	Build control-flow graph with assignments and var usages
//	All modules:
//	    Delete these
//		ASSIGN(Vdly, a)
//	    	... {no reads or writes of a after the first write to Vdly}
//	 	... {no reads of a after the first write to Vdly}
//		ASSIGNPOST(Vdly,tmp)
//
//*************************************************************************

#include "config_build.h"
#include "verilatedos.h"
#include <cstdio>
#include <cstdarg>
#include <unistd.h>

#include "V3Global.h"
#include "V3LifePost.h"
#include "V3Stats.h"
#include "V3Ast.h"

//######################################################################
// LifePost state, as a visitor of each AstNode

class LifePostBaseVisitor : public AstNVisitor {
protected:
    static int debug() {
	static int level = -1;
	if (VL_UNLIKELY(level < 0)) level = v3Global.opt.debugSrcLevel(__FILE__);
	return level;
    }
};

//######################################################################
// LifePost class functions

class LifePostElimVisitor : public LifePostBaseVisitor {
private:
    // NODE STATE
    // INPUT:
    //  AstVarScope::user4p()	-> AstVarScope*, If set, replace this varscope with specified new one
    // STATE
    // VISITORS
    virtual void visit(AstVarRef* nodep, AstNUser*) {
	AstVarScope* vscp = nodep->varScopep();
	if (!vscp) nodep->v3fatalSrc("Scope not assigned");
	if (AstVarScope* newvscp = (AstVarScope*)vscp->user4p()) {
	    UINFO(9, "  Replace "<<nodep<<" to "<<newvscp<<endl);
	    AstVarRef* newrefp = new AstVarRef(nodep->fileline(), newvscp, nodep->lvalue());
	    nodep->replaceWith(newrefp);
	    nodep->deleteTree(); nodep=NULL;
	}
    }
    virtual void visit(AstNodeModule* nodep, AstNUser*) {
	// Only track the top scopes, not lower level functions
	if (nodep->isTop()) nodep->iterateChildren(*this);
    }
    virtual void visit(AstCCall* nodep, AstNUser*) {
	nodep->iterateChildren(*this);
	// Enter the function and trace it
	nodep->funcp()->accept(*this);
    }
    virtual void visit(AstVar*, AstNUser*) {}	// Don't want varrefs under it
    virtual void visit(AstNode* nodep, AstNUser*) {
	nodep->iterateChildren(*this);
    }
public:
    // CONSTRUCTORS
    LifePostElimVisitor(AstTopScope* nodep) {
	nodep->accept(*this);
    }
    virtual ~LifePostElimVisitor() {}
};

//######################################################################
// LifePostlicate delay elimination

class LifePostDlyVisitor : public LifePostBaseVisitor {
private:
    // NODE STATE
    // Cleared on entire tree
    //  AstVarScope::user()	-> Sequence # of first virtex setting this var.
    //  AstVarScope::user2()	-> Sequence # of last consumption of this var
    //  AstVarScope::user4()	-> AstVarScope*: Passed to LifePostElim to substitute this var
    AstUser1InUse	m_inuser1;
    AstUser2InUse	m_inuser2;
    AstUser4InUse	m_inuser4;

    // STATE
    uint32_t		m_sequence;	// Sequence number of assignments/varrefs
    V3Double0		m_statAssnDel;	// Statistic tracking

    // VISITORS
    virtual void visit(AstTopScope* nodep, AstNUser*) {
	AstNode::user1ClearTree();	// user1p() used on entire tree
	AstNode::user2ClearTree();	// user2p() used on entire tree
	AstNode::user4ClearTree();	// user4p() used on entire tree
	m_sequence = 0;
	nodep->iterateChildren(*this);

	// Replace any node4p varscopes with the new scope
	LifePostElimVisitor visitor (nodep);
    }

    virtual void visit(AstVarRef* nodep, AstNUser*) {
	// Consumption/generation of a variable,
	AstVarScope* vscp = nodep->varScopep();
	if (!vscp) nodep->v3fatalSrc("Scope not assigned");
	m_sequence++;
	if (nodep->lvalue()) {
	    // First generator
	    if (!vscp->user1()) vscp->user1(m_sequence);
	} else {
	    // Last consumer
	    vscp->user2(m_sequence);
	}
    }
    virtual void visit(AstAssignPost* nodep, AstNUser*) {
	if (AstVarRef* lhsp = nodep->lhsp()->castVarRef()) {
	    if (AstVarRef* rhsp = nodep->rhsp()->castVarRef()) {
		// Scrunch these:
		//    __Vdly__q = __PVT__clk_clocks;
		//    ... {no reads or writes of __PVT__q after the first write to __Vdly__q}
		//    ... {no reads of __Vdly__q after the first write to __Vdly__q}
		//    __PVT__q = __Vdly__q;
		UINFO(9,"   POST "<<nodep<<endl);
		UINFO(9,"     lhs "<<lhsp<<endl);
		UINFO(9,"     rhs "<<rhsp<<endl);
		uint32_t firstWrite = rhsp->varScopep()->user1();
		uint32_t lastRead   = rhsp->varScopep()->user2();
		uint32_t lastRead2  = lhsp->varScopep()->user2();
		UINFO(9,"     first "<<firstWrite<<" last "<<lastRead<<" "<<lastRead2<<endl);
		if (lastRead < firstWrite
		    && lastRead2 < firstWrite) {
		    UINFO(4,"    DELETE "<<nodep<<endl);
		    // Mark so LifePostElimVisitor will get it
		    rhsp->varScopep()->user4p(lhsp->varScopep());
		    nodep->unlinkFrBack()->deleteTree(); nodep=NULL;
		    ++m_statAssnDel;
		}
	    }
	}
    }
    virtual void visit(AstNodeModule* nodep, AstNUser*) {
	// Only track the top scopes, not lower level functions
	if (nodep->isTop()) nodep->iterateChildren(*this);
    }
    virtual void visit(AstCCall* nodep, AstNUser*) {
	nodep->iterateChildren(*this);
	// Enter the function and trace it
	nodep->funcp()->accept(*this);
    }

    //-----
    virtual void visit(AstVar*, AstNUser*) {}	// Don't want varrefs under it
    virtual void visit(AstNode* nodep, AstNUser*) {
	nodep->iterateChildren(*this);
    }
public:
    // CONSTRUCTORS
    LifePostDlyVisitor(AstNetlist* nodep) {
	nodep->accept(*this);
    }
    virtual ~LifePostDlyVisitor() {
	V3Stats::addStat("Optimizations, Lifetime postassign deletions", m_statAssnDel);
    }
};

//######################################################################
// LifePost class functions

void V3LifePost::lifepostAll(AstNetlist* nodep) {
    UINFO(2,__FUNCTION__<<": "<<endl);
    // Mark redundant AssignPost
    LifePostDlyVisitor visitor (nodep);
    V3Global::dumpCheckGlobalTree("life_post.tree", 0, v3Global.opt.dumpTreeLevel(__FILE__) >= 3);
}
