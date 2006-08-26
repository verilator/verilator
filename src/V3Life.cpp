// $Id$
//*************************************************************************
// DESCRIPTION: Verilator: Lifelicate variable assignment elimination
//
// Code available from: http://www.veripool.com/verilator
//
// AUTHORS: Wilson Snyder with Paul Wasson, Duane Gabli
//
//*************************************************************************
//
// Copyright 2003-2006 by Wilson Snyder.  This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// General Public License or the Perl Artistic License.
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
//	    ASSIGN(x,...), ASSIGN(x,...) => delete first one
//	    We also track across if statements:
//	    ASSIGN(X,...) IF( ..., ASSIGN(X,...), ASSIGN(X,...)) => deletes first
//	    We don't do the opposite yet though (remove assigns in if followed by outside if)
//	    
//*************************************************************************

#include "config.h"
#include <stdio.h>
#include <stdarg.h>
#include <unistd.h>
#include <map>

#include "V3Global.h"
#include "V3Life.h"
#include "V3Stats.h"
#include "V3Ast.h"

//######################################################################
// Life state, as a visitor of each AstNode

class LifeVarEntry {
    AstNode*	m_assignp;	// Last assignment to this varscope
    bool	m_firstSet;	// True if creation was a set (and thus block above may have a set that can be deleted
public:
    LifeVarEntry() {	// Construction for when a var is used
	clearAssign();
	m_firstSet = false;
    }
    LifeVarEntry(AstNode* assp) {	// Construction for when a var is set
	m_assignp = assp;
	m_firstSet = true;
    }
    LifeVarEntry(bool) {	// Construction for when a var is set, but ass isn't
	m_assignp = NULL;
	m_firstSet = true;
    }
    AstNode* assignp() const { return m_assignp; }
    bool firstSet() const { return m_firstSet; }
    void clearAssign() { m_assignp = NULL; }
    void newerAssign(AstNode* assp) { m_assignp = assp; }
};

class LifeVisitor : public AstNVisitor {
private:
    // NODE STATE
    //  AstVarScope::user()	-> int.       Used in combining to detect duplicates

    // STATE
    //static int debug() { return 9; }
    int		m_ifCount;	// If counter
    V3Double0	m_statAssnDel;	// Statistic tracking

    // LIFE MAP
    //  For each basic block, we'll make a new map of what variables that if/else is changing
    typedef std::map<AstVarScope*, LifeVarEntry> LifeMap;
    LifeMap	*m_lifep;	// Current active lifetime map for current scope

    // METHODS
    void checkRemoveAssign(LifeVarEntry* entp) {
	// Check the var entry, and remove if appropriate
	if (AstNode* oldassp = entp->assignp()) {
	    UINFO(7,"       PREV: "<<oldassp<<endl);
	    // Redundant assignment, in same level block
	    if (debug()>4) oldassp->dumpTree(cout, "       REMOVE/SAMEBLK ");
	    entp->clearAssign();
	    oldassp->unlinkFrBack();
	    pushDeletep(oldassp);
	    m_statAssnDel++;
	}
    }
    void setLast(AstVarScope* nodep, AstNode* assp) {
	// Do we have a old assignment we can nuke?
	UINFO(4,"     ASSIGNof: "<<nodep<<endl);
	UINFO(7,"       new: "<<assp<<endl);
	LifeMap::iterator iter = m_lifep->find(nodep);
	if (iter != m_lifep->end()) {
	    checkRemoveAssign(&(iter->second));
	    iter->second.newerAssign(assp);
	} else {
	    m_lifep->insert(make_pair(nodep,LifeVarEntry(assp)));
	}
	//lifeDump();
    }
    void clearLastAssign(AstVarScope* nodep) {
	UINFO(4,"     clearof: "<<nodep<<endl);
	LifeMap::iterator iter = m_lifep->find(nodep);
	if (iter != m_lifep->end()) {
	    iter->second.clearAssign();
	} else {
	    m_lifep->insert(make_pair(nodep,LifeVarEntry()));
	}
    }
    void lifeDump(LifeMap* lifep) {
	UINFO(5, "  LifeMap:"<<endl);
	for (LifeMap::iterator it = lifep->begin(); it!=lifep->end(); ++it) {
	    UINFO(5, "     Ent:  "
		  <<(it->second.firstSet()?"[F]  ":"     ")
		  <<it->first<<endl);
	    if (it->second.assignp()) {
		UINFO(5, "       Ass: "<<it->second.assignp()<<endl);
	    }
	}
    }
    void clearLifeFromSublife (LifeMap* sublifep) {
	// Any varrefs under a if/else branch affect statements outside and after the if/else
	for (LifeMap::iterator it = sublifep->begin(); it!=sublifep->end(); ++it) {
	    clearLastAssign(it->first);
	}
    }
    void dualBranch (LifeMap* life1p, LifeMap* life2p) {
	// Find any common sets on both branches of IF and propagate upwards
	//lifeDump(life1p);
	//lifeDump(life2p);
	m_ifCount++;
	for (LifeMap::iterator it = life1p->begin(); it!=life1p->end(); ++it) {
	    // When the if branch sets a var before it's used, mark that variable
	    if (it->second.firstSet()) it->first->user(m_ifCount);
	}
	for (LifeMap::iterator it = life2p->begin(); it!=life2p->end(); ++it) {
	    // When the else branch sets a var before it's used
	    AstVarScope* nodep = it->first;
	    if (it->second.firstSet()
		&& nodep->user()==m_ifCount) {	// And the if hit the same var
		UINFO(4,"DUALBRANCH "<<nodep<<endl);
		LifeMap::iterator iter = m_lifep->find(nodep);
		if (iter != m_lifep->end()) {
		    checkRemoveAssign(&(iter->second));
		    iter->second.clearAssign();
		} else {
		    m_lifep->insert(make_pair(nodep,LifeVarEntry(true)));
		}
	    }
	}
	//lifeDump(m_lifep);
    }

    // VISITORS
    virtual void visit(AstModule* nodep, AstNUser*) {
	// Only track the top scopes, not lower level functions
	if (nodep->isTop()) nodep->iterateChildren(*this);
    }
    virtual void visit(AstTopScope* nodep, AstNUser*) {
	AstNode::userClearTree();	// userp() used on entire tree
	AstNode::user2ClearTree();	// userp() used on entire tree
	AstNode::user3ClearTree();	// userp() used on entire tree
	AstNode::user4ClearTree();	// userp() used on entire tree

	AstScope* scopep = nodep->scopep()->castScope();
	if (!scopep) nodep->v3fatalSrc("TopScope has no scope\n");
	AstCFunc* evalp = NULL;
	for (AstNode* searchp = scopep->blocksp(); searchp; searchp=searchp->nextp()) {
	    if (AstCFunc* funcp = searchp->castCFunc()) {
		if (funcp->name() == "_eval") {
		    evalp = funcp;
		    break;
		}
	    }
	}
	if (!evalp) nodep->v3fatalSrc("Top _eval entry function not found\n");
	evalp->iterateChildren(*this);
    }

    virtual void visit(AstVarRef* nodep, AstNUser*) {
	// Consumption/generation of a variable, 
	// it's used so can't elim assignment before this use.
	if (!nodep->varScopep()) nodep->v3fatalSrc("NULL");
	//
	AstVarScope* vscp = nodep->varScopep();
	if (!vscp) nodep->v3fatalSrc("Scope not assigned");
	clearLastAssign(vscp);
    }
    virtual void visit(AstNodeAssign* nodep, AstNUser*) {
	// Collect any used variables first, as lhs may also be on rhs
	nodep->rhsp()->iterateAndNext(*this);
	// Has to be direct assignment without any EXTRACTing.
	if (nodep->lhsp()->castVarRef()) {
	    AstVarScope* vscp = nodep->lhsp()->castVarRef()->varScopep();
	    if (!vscp) vscp->v3fatalSrc("Scope lost on variable");
	    setLast(vscp, nodep);
	} else {
	    nodep->lhsp()->iterateAndNext(*this);
	}
    }

    //---- Track control flow changes 
    virtual void visit(AstNodeIf* nodep, AstNUser*) {
    	UINFO(4,"   IF "<<nodep<<endl);
	// Condition is part of PREVIOUS block
	nodep->condp()->iterateAndNext(*this);
	LifeMap* prevLifeMapp = m_lifep;
	LifeMap* ifLifep = new LifeMap;
	LifeMap* elseLifep = new LifeMap;
	{
	    m_lifep = ifLifep;
	    nodep->ifsp()->iterateAndNext(*this);
	}
	{
	    m_lifep = elseLifep;
	    nodep->elsesp()->iterateAndNext(*this);
	}
    	UINFO(4,"   join "<<endl);
	m_lifep = prevLifeMapp;
	// Find sets on both flows
	dualBranch (ifLifep, elseLifep);
	// For the next assignments, clear any variables that were read or written in the block
	clearLifeFromSublife(ifLifep);
	clearLifeFromSublife(elseLifep);
	delete ifLifep;
	delete elseLifep;
    }

    virtual void visit(AstWhile* nodep, AstNUser*) {
	// While's are a problem, as we don't allow loops in the graph.  We
	// may go around the cond/body multiple times.  Thus a
	// lifelication just in the body is ok, but we can't delete an
	// assignment in the body that's used in the cond.  (And otherwise
	// would because it only appears used after-the-fact.  So, we model
	// it as a IF statement, and just don't allow elimination of
	// variables in the body.
	LifeMap* prevLifeMapp = m_lifep;
	LifeMap* condLifep = new LifeMap;
	LifeMap* bodyLifep = new LifeMap;
	{
	    m_lifep = condLifep;
	    nodep->precondsp()->iterateAndNext(*this);
	    nodep->condp()->iterateAndNext(*this);
	}
	{
	    m_lifep = bodyLifep;
	    nodep->bodysp()->iterateAndNext(*this);
	}
    	UINFO(4,"   joinfor"<<endl);
	m_lifep = prevLifeMapp;
	// For the next assignments, clear any variables that were read or written in the block
	clearLifeFromSublife(condLifep);
	clearLifeFromSublife(bodyLifep);
	delete condLifep;
	delete bodyLifep;
    }
    virtual void visit(AstCCall* nodep, AstNUser*) {
    	//UINFO(4,"  CCALL "<<nodep<<endl);
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
    LifeVisitor(AstNetlist* nodep) {
	m_ifCount = 1;
	m_lifep = new LifeMap;
	nodep->accept(*this);
	delete m_lifep;
    }
    virtual ~LifeVisitor() {
	V3Stats::addStat("Optimizations, Lifetime assign deletions", m_statAssnDel);
    }
};

//######################################################################
// Life class functions

void V3Life::lifeAll(AstNetlist* nodep) {
    UINFO(2,__FUNCTION__<<": "<<endl);
    // Delete lifelicate assignments
    LifeVisitor visitor (nodep);
}
