// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Add temporaries, such as for changed nodes
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
// V3Changed's Transformations:
//
// Each module:
//	Each combo block
//	    For each variable that comes from combo block and is generated AFTER a usage
//		Add __Vlast_{var} to local section, init to current value (just use array?)
//		Change = if any var != last.
//	    If a signal is used as a clock in this module or any
//	    module *below*, and it isn't a input to this module,
//	    we need to indicate a new clock has been created.
//
//*************************************************************************

#include "config_build.h"
#include "verilatedos.h"
#include <cstdio>
#include <cstdarg>
#include <unistd.h>
#include <algorithm>
#include <set>

#include "V3Global.h"
#include "V3Ast.h"
#include "V3Changed.h"
#include "V3EmitCBase.h"

//######################################################################

class ChangedState {
public:
    // STATE
    AstNodeModule*	m_topModp;	// Top module
    AstScope*		m_scopetopp;	// Scope under TOPSCOPE
    AstCFunc*		m_chgFuncp;	// Change function we're building
    ChangedState() {
	m_topModp = NULL;
	m_chgFuncp = NULL;
	m_scopetopp = NULL;
    }
    ~ChangedState() {}
};

//######################################################################
// Utility visitor to find elements to be compared

class ChangedInsertVisitor : public AstNVisitor {
private:
    // STATE
    ChangedState*	m_statep;	// Shared state across visitors
    AstVarScope*	m_vscp;		// Original (non-change) variable we're change-detecting
    AstVarScope*	m_newvscp;	// New (change detect) variable we're change-detecting
    AstNode*		m_varEqnp;	// Original var's equation to get var value
    AstNode*		m_newLvEqnp;	// New var's equation to read value 
    AstNode*		m_newRvEqnp;	// New var's equation to set value 
    uint32_t		m_detects;	// # detects created

    // CONSTANTS
    enum MiscConsts {
	DETECTARRAY_MAX_INDEXES = 256	// How many indexes before error
	// Ok to increase this, but may result in much slower model
    };

    void newChangeDet() {
	if (++m_detects > DETECTARRAY_MAX_INDEXES) {
	    m_vscp->v3warn(E_DETECTARRAY, "Unsupported: Can't detect more than "<<cvtToStr(DETECTARRAY_MAX_INDEXES)
			   <<" array indexes (probably with UNOPTFLAT warning suppressed): "<<m_vscp->prettyName()<<endl
			   <<m_vscp->warnMore()
			   <<"... Could recompile with DETECTARRAY_MAX_INDEXES increased"<<endl);
	    return;
	}
	AstChangeDet* changep = new AstChangeDet (m_vscp->fileline(),
						  m_varEqnp->cloneTree(true),
						  m_newRvEqnp->cloneTree(true), false);
	m_statep->m_chgFuncp->addStmtsp(changep);
	AstAssign* initp = new AstAssign (m_vscp->fileline(),
					  m_newLvEqnp->cloneTree(true),
					  m_varEqnp->cloneTree(true));
	m_statep->m_chgFuncp->addFinalsp(initp);
    }

    virtual void visit(AstBasicDType* nodep, AstNUser*) {
	newChangeDet();
    }
    virtual void visit(AstPackArrayDType* nodep, AstNUser*) {
	newChangeDet();
    }
    virtual void visit(AstUnpackArrayDType* nodep, AstNUser*) {
	for (int index=0; index < nodep->elementsConst(); ++index) {
	    AstNode* origVEp = m_varEqnp;
	    AstNode* origNLEp = m_newLvEqnp;
	    AstNode* origNREp = m_newRvEqnp;

	    m_varEqnp   = new AstArraySel(nodep->fileline(), m_varEqnp->cloneTree(true), index);
	    m_newLvEqnp = new AstArraySel(nodep->fileline(), m_newLvEqnp->cloneTree(true), index);
	    m_newRvEqnp = new AstArraySel(nodep->fileline(), m_newRvEqnp->cloneTree(true), index);

	    nodep->subDTypep()->skipRefp()->accept(*this);

	    m_varEqnp->deleteTree();
	    m_newLvEqnp->deleteTree();
	    m_newRvEqnp->deleteTree();

	    m_varEqnp   = origVEp;
	    m_newLvEqnp = origNLEp;
	    m_newRvEqnp = origNREp;
	}
    }
    virtual void visit(AstNodeClassDType* nodep, AstNUser*) {
	if (nodep->packedUnsup()) {
	    newChangeDet();
	} else {
	    if (debug()) nodep->dumpTree(cout,"-DETECTARRAY-class-");
	    m_vscp->v3warn(E_DETECTARRAY, "Unsupported: Can't detect changes on complex variable (probably with UNOPTFLAT warning suppressed): "<<m_vscp->varp()->prettyName());
	}
    }
    virtual void visit(AstNode* nodep, AstNUser*) {
	nodep->iterateChildren(*this);
	if (debug()) nodep->dumpTree(cout,"-DETECTARRAY-general-");
	m_vscp->v3warn(E_DETECTARRAY, "Unsupported: Can't detect changes on complex variable (probably with UNOPTFLAT warning suppressed): "<<m_vscp->varp()->prettyName());
    }
public:
    // CONSTUCTORS
    ChangedInsertVisitor(AstVarScope* vscp, ChangedState* statep) {
	m_statep = statep;
	m_vscp = vscp;
	m_detects = 0;
	{
	    AstVar* varp = m_vscp->varp();
	    string newvarname = "__Vchglast__"+m_vscp->scopep()->nameDotless()+"__"+varp->shortName();
	    // Create:  VARREF(_last)
	    //          ASSIGN(VARREF(_last), VARREF(var))
	    //          ...
	    //          CHANGEDET(VARREF(_last), VARREF(var))
	    AstVar* newvarp = new AstVar (varp->fileline(), AstVarType::MODULETEMP, newvarname, varp);
	    m_statep->m_topModp->addStmtp(newvarp);
	    m_newvscp = new AstVarScope(m_vscp->fileline(), m_statep->m_scopetopp, newvarp);
	    m_statep->m_scopetopp->addVarp(m_newvscp);

	    m_varEqnp   = new AstVarRef(m_vscp->fileline(), m_vscp, false);
	    m_newLvEqnp = new AstVarRef(m_vscp->fileline(), m_newvscp, true);
	    m_newRvEqnp = new AstVarRef(m_vscp->fileline(), m_newvscp, false);
	}
	vscp->dtypep()->skipRefp()->accept(*this);
	m_varEqnp->deleteTree();
	m_newLvEqnp->deleteTree();
	m_newRvEqnp->deleteTree();
    }
    virtual ~ChangedInsertVisitor() {}
};

//######################################################################
// Changed state, as a visitor of each AstNode

class ChangedVisitor : public AstNVisitor {
private:
    // NODE STATE
    // Entire netlist:
    //  AstVarScope::user1()		-> bool.  True indicates processed
    AstUser1InUse	m_inuser1;

    // STATE
    ChangedState*	m_statep;	// Shared state across visitors

    // METHODS
    static int debug() {
	static int level = -1;
	if (VL_UNLIKELY(level < 0)) level = v3Global.opt.debugSrcLevel(__FILE__);
	return level;
    }

    void genChangeDet(AstVarScope* vscp) {
	vscp->v3warn(IMPERFECTSCH,"Imperfect scheduling of variable: "<<vscp);
	ChangedInsertVisitor visitor (vscp, m_statep);
    }

    // VISITORS
    virtual void visit(AstNodeModule* nodep, AstNUser*) {
	UINFO(4," MOD   "<<nodep<<endl);
	if (nodep->isTop()) {
	    m_statep->m_topModp = nodep;
	}
	nodep->iterateChildren(*this);
    }
    virtual void visit(AstTopScope* nodep, AstNUser*) {
	UINFO(4," TS "<<nodep<<endl);
	// Clearing
	AstNode::user1ClearTree();
	// Create the change detection function
	AstScope* scopep = nodep->scopep();
	if (!scopep) nodep->v3fatalSrc("No scope found on top level, perhaps you have no statements?\n");
	m_statep->m_scopetopp = scopep;
	// Create change detection function
	m_statep->m_chgFuncp = new AstCFunc(nodep->fileline(), "_change_request", scopep, "QData");
	m_statep->m_chgFuncp->argTypes(EmitCBaseVisitor::symClassVar());
	m_statep->m_chgFuncp->symProlog(true);
	m_statep->m_chgFuncp->declPrivate(true);
	m_statep->m_scopetopp->addActivep(m_statep->m_chgFuncp);
	// We need at least one change detect so we know to emit the correct code
	m_statep->m_chgFuncp->addStmtsp(new AstChangeDet(nodep->fileline(), NULL, NULL, false));
	//
	nodep->iterateChildren(*this);
    }
    virtual void visit(AstVarScope* nodep, AstNUser*) {
	if (nodep->isCircular()) {
	    UINFO(8,"  CIRC "<<nodep<<endl);
	    if (!nodep->user1SetOnce()) {
		genChangeDet(nodep);
	    }
	}
    }
    virtual void visit(AstNodeMath* nodep, AstNUser*) {
	// Short-circuit 
    }
    //--------------------
    // Default: Just iterate
    virtual void visit(AstNode* nodep, AstNUser*) {
	nodep->iterateChildren(*this);
    }

public:
    // CONSTUCTORS
    ChangedVisitor(AstNetlist* nodep, ChangedState* statep) {
	m_statep = statep;
	nodep->accept(*this);
    }
    virtual ~ChangedVisitor() {}
};

//######################################################################
// Changed class functions

void V3Changed::changedAll(AstNetlist* nodep) {
    UINFO(2,__FUNCTION__<<": "<<endl);
    ChangedState state;
    ChangedVisitor visitor (nodep, &state);
    V3Global::dumpCheckGlobalTree("changed.tree", 0, v3Global.opt.dumpTreeLevel(__FILE__) >= 3);
}
