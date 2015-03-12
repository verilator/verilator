// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Generated Clock repairs
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
// GENCLK TRANSFORMATIONS:
//	Follow control-flow graph with assignments and var usages
//	    ASSIGNDLY to variable later used as clock requires change detect
//
//*************************************************************************

#include "config_build.h"
#include "verilatedos.h"
#include <cstdio>
#include <cstdarg>
#include <unistd.h>

#include "V3Global.h"
#include "V3GenClk.h"
#include "V3Ast.h"

//######################################################################
// GenClk state, as a visitor of each AstNode

class GenClkBaseVisitor : public AstNVisitor {
protected:
    static int debug() {
	static int level = -1;
	if (VL_UNLIKELY(level < 0)) level = v3Global.opt.debugSrcLevel(__FILE__);
	return level;
    }
};

//######################################################################
// GenClk Read

class GenClkRenameVisitor : public GenClkBaseVisitor {
private:
    // NODE STATE
    // Cleared on top scope
    //  AstVarScope::user2()	-> AstVarScope*.  Signal replacing activation with
    //  AstVarRef::user3()	-> bool.  Signal is replaced activation (already done)
    AstUser2InUse	m_inuser2;
    AstUser3InUse	m_inuser3;

    // STATE
    AstActive*		m_activep;	// Inside activate statement
    AstNodeModule*	m_topModp;	// Top module
    AstScope*		m_scopetopp;	// Scope under TOPSCOPE

    // METHODS
    AstVarScope* genInpClk(AstVarScope* vscp) {
	if (vscp->user2p()) {
	    return vscp->user2p()->castNode()->castVarScope();
	} else {
	    AstVar* varp = vscp->varp();
	    string newvarname = "__VinpClk__"+vscp->scopep()->nameDotless()+"__"+varp->name();
	    // Create:  VARREF(inpclk)
	    //          ...
	    //          ASSIGN(VARREF(inpclk), VARREF(var))
	    AstVar* newvarp = new AstVar (varp->fileline(), AstVarType::MODULETEMP, newvarname, varp);
	    m_topModp->addStmtp(newvarp);
	    AstVarScope* newvscp = new AstVarScope(vscp->fileline(), m_scopetopp, newvarp);
	    m_scopetopp->addVarp(newvscp);
	    AstAssign* asninitp = new AstAssign (vscp->fileline(),
						 new AstVarRef(vscp->fileline(), newvscp, true),
						 new AstVarRef(vscp->fileline(), vscp, false));
	    m_scopetopp->addFinalClkp(asninitp);
	    //
	    vscp->user2p(newvscp);
	    return newvscp;
	}
    }

    // VISITORS
    virtual void visit(AstTopScope* nodep, AstNUser*) {
	AstNode::user2ClearTree();	// user2p() used on entire tree

	AstScope* scopep = nodep->scopep();
	if (!scopep) nodep->v3fatalSrc("No scope found on top level");
	m_scopetopp = scopep;

	nodep->iterateChildren(*this);
    }
    //----
    virtual void visit(AstVarRef* nodep, AstNUser*) {
	// Consumption/generation of a variable,
	AstVarScope* vscp = nodep->varScopep();
	if (!vscp) nodep->v3fatalSrc("Scope not assigned");
	if (m_activep && !nodep->user3()) {
	    nodep->user3(true);
	    if (vscp->isCircular()) {
		UINFO(8,"  VarActReplace "<<nodep<<endl);
		// Replace with the new variable
		AstVarScope* newvscp = genInpClk(vscp);
		AstVarRef* newrefp = new AstVarRef(nodep->fileline(), newvscp, nodep->lvalue());
		nodep->replaceWith(newrefp);
		pushDeletep(nodep); nodep=NULL;
	    }
	}
    }
    virtual void visit(AstActive* nodep, AstNUser*) {
	m_activep = nodep;
	nodep->sensesp()->iterateChildren(*this);  // iterateAndNext?
	m_activep = NULL;
	nodep->iterateChildren(*this);
    }
    virtual void visit(AstCFunc* nodep, AstNUser*) {
	nodep->iterateChildren(*this);
    }

    //-----
    virtual void visit(AstNode* nodep, AstNUser*) {
	nodep->iterateChildren(*this);
    }
public:
    // CONSTRUCTORS
    GenClkRenameVisitor(AstTopScope* nodep, AstNodeModule* topModp) {
	m_topModp = topModp;
	m_scopetopp = NULL;
	m_activep = NULL;
	nodep->accept(*this);
    }
    virtual ~GenClkRenameVisitor() {}
};

//######################################################################
// GenClk Read

class GenClkReadVisitor : public GenClkBaseVisitor {
private:
    // NODE STATE
    // Cleared on top scope
    //  AstVarScope::user()	-> bool.  Set when the var has been used as clock
    AstUser1InUse	m_inuser1;

    // STATE
    AstActive*	m_activep;		// Inside activate statement
    AstNodeAssign* m_assignp;		// Inside assigndly statement
    AstNodeModule*	m_topModp;	// Top module

    // VISITORS
    virtual void visit(AstTopScope* nodep, AstNUser*) {
	AstNode::user1ClearTree();	// user1p() used on entire tree
	nodep->iterateChildren(*this);
	{
	    // Make the new clock signals and replace any activate references
	    // See rename, it does some AstNode::userClearTree()'s
	    GenClkRenameVisitor visitor (nodep, m_topModp);
	}
    }
    virtual void visit(AstNodeModule* nodep, AstNUser*) {
	// Only track the top scopes, not lower level functions
	if (nodep->isTop()) {
	    m_topModp = nodep;
	    nodep->iterateChildren(*this);
	}
    }
    virtual void visit(AstCCall* nodep, AstNUser*) {
	nodep->iterateChildren(*this);
	// Enter the function and trace it
	nodep->funcp()->accept(*this);
    }
    //----

    virtual void visit(AstVarRef* nodep, AstNUser*) {
	// Consumption/generation of a variable,
	AstVarScope* vscp = nodep->varScopep();
	if (!vscp) nodep->v3fatalSrc("Scope not assigned");
	if (m_activep) {
	    UINFO(8,"  VarAct "<<nodep<<endl);
	    vscp->user1(true);
	}
	if (m_assignp && nodep->lvalue() && vscp->user1()) {
	    // Variable was previously used as a clock, and is now being set
	    // Thus a unordered generated clock...
	    UINFO(8,"  VarSetAct "<<nodep<<endl);
	    vscp->circular(true);
	}
    }
    virtual void visit(AstNodeAssign* nodep, AstNUser*) {
	//UINFO(8,"ASS "<<nodep<<endl);
	m_assignp = nodep;
	nodep->iterateChildren(*this);
	m_assignp = NULL;
    }
    virtual void visit(AstActive* nodep, AstNUser*) {
	UINFO(8,"ACTIVE "<<nodep<<endl);
	m_activep = nodep;
	nodep->sensesp()->iterateChildren(*this);  // iterateAndNext?
	m_activep = NULL;
	nodep->iterateChildren(*this);
    }

    //-----
    virtual void visit(AstVar*, AstNUser*) {}	// Don't want varrefs under it
    virtual void visit(AstNode* nodep, AstNUser*) {
	nodep->iterateChildren(*this);
    }
public:
    // CONSTRUCTORS
    GenClkReadVisitor(AstNetlist* nodep) {
	m_activep = NULL;
	m_assignp = NULL;
	m_topModp = NULL;
	nodep->accept(*this);
    }
    virtual ~GenClkReadVisitor() {}
};

//######################################################################
// GenClk class functions

void V3GenClk::genClkAll(AstNetlist* nodep) {
    UINFO(2,__FUNCTION__<<": "<<endl);
    GenClkReadVisitor visitor (nodep);
    V3Global::dumpCheckGlobalTree("genclk.tree", 0, v3Global.opt.dumpTreeLevel(__FILE__) >= 3);
}
