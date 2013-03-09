// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Add temporaries, such as for changed nodes
//
// Code available from: http://www.veripool.org/verilator
//
//*************************************************************************
//
// Copyright 2003-2013 by Wilson Snyder.  This program is free software; you can
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
// Changed state, as a visitor of each AstNode

class ChangedVisitor : public AstNVisitor {
private:
    // NODE STATE
    // Entire netlist:
    //  AstVarScope::user1()		-> bool.  True indicates processed
    AstUser1InUse	m_inuser1;

    // STATE
    AstNodeModule*	m_topModp;	// Top module
    AstScope*		m_scopetopp;	// Scope under TOPSCOPE
    AstCFunc*		m_chgFuncp;	// Change function we're building

    // CONSTANTS
    enum MiscConsts {
	DETECTARRAY_MAX_INDEXES = 256	// How many indexes before error
	// Ok to increase this, but may result in much slower model
    };

    // METHODS
    static int debug() {
	static int level = -1;
	if (VL_UNLIKELY(level < 0)) level = v3Global.opt.debugSrcLevel(__FILE__);
	return level;
    }

    AstNode* aselIfNeeded(bool isArray, int index, AstNode* childp) {
	if (isArray) {
	    return new AstArraySel(childp->fileline(), childp,
				   new AstConst(childp->fileline(), index));
	} else {
	    return childp;
	}
    }

    void genChangeDet(AstVarScope* vscp) {
#ifdef NEW_ORDERING
	vscp->v3fatalSrc("Not applicable\n");
#endif
	AstVar* varp = vscp->varp();
	vscp->v3warn(IMPERFECTSCH,"Imperfect scheduling of variable: "<<vscp);
	AstUnpackArrayDType* arrayp = varp->dtypeSkipRefp()->castUnpackArrayDType();
	AstStructDType *structp = varp->dtypeSkipRefp()->castStructDType();
	bool isArray = arrayp;
	bool isStruct = structp && structp->packed();
	int elements = isArray ? arrayp->elementsConst() : 1;
	if (isArray && (elements > DETECTARRAY_MAX_INDEXES)) {
	    vscp->v3warn(E_DETECTARRAY, "Unsupported: Can't detect more than "<<cvtToStr(DETECTARRAY_MAX_INDEXES)
			 <<" array indexes (probably with UNOPTFLAT warning suppressed): "<<varp->prettyName()<<endl
			 <<vscp->warnMore()
			 <<"... Could recompile with DETECTARRAY_MAX_INDEXES increased to at least "<<cvtToStr(elements));
	} else if (!isArray && !isStruct
		   && !varp->dtypeSkipRefp()->castBasicDType()) {
	    if (debug()) varp->dumpTree(cout,"-DETECTARRAY-");
	    vscp->v3warn(E_DETECTARRAY, "Unsupported: Can't detect changes on complex variable (probably with UNOPTFLAT warning suppressed): "<<varp->prettyName());
	} else {
	    string newvarname = "__Vchglast__"+vscp->scopep()->nameDotless()+"__"+varp->shortName();
	    // Create:  VARREF(_last)
	    //          ASSIGN(VARREF(_last), VARREF(var))
	    //          ...
	    //          CHANGEDET(VARREF(_last), VARREF(var))
	    AstVar* newvarp = new AstVar (varp->fileline(), AstVarType::MODULETEMP, newvarname, varp);
	    m_topModp->addStmtp(newvarp);
	    AstVarScope* newvscp = new AstVarScope(vscp->fileline(), m_scopetopp, newvarp);
	    m_scopetopp->addVarp(newvscp);
	    for (int index=0; index<elements; ++index) {
		AstChangeDet* changep
		    = new AstChangeDet (vscp->fileline(),
					aselIfNeeded(isArray, index,
						     new AstVarRef(vscp->fileline(), vscp, false)),
					aselIfNeeded(isArray, index,
						     new AstVarRef(vscp->fileline(), newvscp, false)),
					false);
		m_chgFuncp->addStmtsp(changep);
		AstAssign* initp
		    = new AstAssign (vscp->fileline(),
				     aselIfNeeded(isArray, index,
						  new AstVarRef(vscp->fileline(), newvscp, true)),
				     aselIfNeeded(isArray, index,
						  new AstVarRef(vscp->fileline(), vscp, false)));
		m_chgFuncp->addFinalsp(initp);
	    }
	}
    }

    // VISITORS
    virtual void visit(AstNodeModule* nodep, AstNUser*) {
	UINFO(4," MOD   "<<nodep<<endl);
	if (nodep->isTop()) {
	    m_topModp = nodep;
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
	m_scopetopp = scopep;
	// Create change detection function
	m_chgFuncp = new AstCFunc(nodep->fileline(), "_change_request", scopep, "IData");
	m_chgFuncp->argTypes(EmitCBaseVisitor::symClassVar());
	m_chgFuncp->symProlog(true);
	m_chgFuncp->declPrivate(true);
	m_scopetopp->addActivep(m_chgFuncp);
	// We need at least one change detect so we know to emit the correct code
	m_chgFuncp->addStmtsp(new AstChangeDet(nodep->fileline(), NULL, NULL, false));
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
    //--------------------
    // Default: Just iterate
    virtual void visit(AstNode* nodep, AstNUser*) {
	nodep->iterateChildren(*this);
    }

public:
    // CONSTUCTORS
    ChangedVisitor(AstNetlist* nodep) {
	m_topModp = NULL;
	m_chgFuncp = NULL;
	m_scopetopp = NULL;
	nodep->accept(*this);
    }
    virtual ~ChangedVisitor() {}
};

//######################################################################
// Changed class functions

void V3Changed::changedAll(AstNetlist* nodep) {
    UINFO(2,__FUNCTION__<<": "<<endl);
    ChangedVisitor visitor (nodep);
}
