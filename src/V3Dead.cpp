// $Id$
//*************************************************************************
// DESCRIPTION: Verilator: Dead code elimination
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
// DEAD TRANSFORMATIONS:
//	Remove any unreferenced modules
//	Remove any unreferenced variables
//	    
//*************************************************************************

#include "config.h"
#include <stdio.h>
#include <stdarg.h>
#include <unistd.h>
#include <vector>

#include "V3Global.h"
#include "V3Dead.h"
#include "V3Ast.h"

//######################################################################

class DeadModVisitor : public AstNVisitor {
    // In a module that is dead, cleanup the in-use counts of the modules
private:
    // NODE STATE
    // ** Shared with DeadVisitor **
    // VISITORS
    virtual void visit(AstCell* nodep, AstNUser*) {
	nodep->iterateChildren(*this);
	nodep->modp()->user(nodep->modp()->user() - 1);
    }
    //-----
    virtual void visit(AstNodeMath* nodep, AstNUser*) {}  // Accelerate
    virtual void visit(AstNode* nodep, AstNUser*) {
	nodep->iterateChildren(*this);
    }
public:
    // CONSTRUCTORS
    DeadModVisitor(AstModule* nodep) {
	nodep->accept(*this);
    }
    virtual ~DeadModVisitor() {}
};

//######################################################################
// Dead state, as a visitor of each AstNode

class DeadVisitor : public AstNVisitor {
private:
    // NODE STATE
    // Entire Netlist:
    //  AstModule::user()	-> int. Count of number of cells referencing this module.
    //  AstVar::user()		-> int. Count of number of references
    //  AstVarScope::user()	-> int. Count of number of references

    // STATE
    vector<AstVar*>		m_varsp;	// List of all encountered to avoid another loop through tree
    vector<AstVarScope*>	m_vscsp;	// List of all encountered to avoid another loop through tree
    bool			m_elimUserVars;	// Allow removal of user's vars
    //int debug() { return 9; }

    // METHODS

    // VISITORS
    virtual void visit(AstCell* nodep, AstNUser*) {
	nodep->iterateChildren(*this);
	nodep->modp()->user(nodep->modp()->user() + 1);
    }
    virtual void visit(AstNodeVarRef* nodep, AstNUser*) {
	nodep->iterateChildren(*this);
	if (nodep->varScopep()) {
	    nodep->varScopep()->user(nodep->varScopep()->user() + 1);
	    nodep->varScopep()->varp()->user(nodep->varScopep()->varp()->user() + 1);
	}
	if (nodep->varp()) {
	    nodep->varp()->user(nodep->varp()->user() + 1);
	}
    }
    virtual void visit(AstVarScope* nodep, AstNUser*) {
	nodep->iterateChildren(*this);
	m_vscsp.push_back(nodep);
    }
    virtual void visit(AstVar* nodep, AstNUser*) {
	nodep->iterateChildren(*this);
	m_varsp.push_back(nodep);
    }

    //-----
    virtual void visit(AstNode* nodep, AstNUser*) {
	nodep->iterateChildren(*this);
    }

    // METHODS
    void deadCheckMod() {
	// Kill any unused modules
	// V3LinkCells has a graph that is capable of this too, but we need to do it
	// after we've done all the generate blocks
	for (bool retry=true; retry; ) {
	    retry=false;
	    AstModule* nextmodp;
	    for (AstModule* modp = v3Global.rootp()->modulesp(); modp; modp=nextmodp) {
		nextmodp = modp->nextp()->castModule();
		if (modp->level()>2	&& modp->user()==0) {
		    // > 2 because L1 is the wrapper, L2 is the top user module
		    UINFO(4,"  Dead module "<<modp<<endl);
		    // And its children may now be killable too; correct counts
		    // Recurse, as cells may not be directly under the module but in a generate
		    DeadModVisitor visitor(modp);
		    modp->unlinkFrBack()->deleteTree(); modp=NULL;
		    retry = true;
		}
	    }
	}
    }
    bool canElim(AstVar* nodep) {
	return (!nodep->isSigPublic()	// Can't elim publics!
		&& (nodep->isTemp() || nodep->isParam() || m_elimUserVars));
    }
    void deadCheckVar() {
	// Delete any unused varscopes
	for (vector<AstVarScope*>::iterator it = m_vscsp.begin(); it!=m_vscsp.end(); ++it) {
	    if ((*it)->user() == 0 && canElim((*it)->varp())) {
		UINFO(4,"  Dead "<<(*it)<<endl);
		(*it)->unlinkFrBack()->deleteTree(); (*it)=NULL;
	    }
	}
	for (vector<AstVar*>::iterator it = m_varsp.begin(); it!=m_varsp.end(); ++it) {
	    if ((*it)->user() == 0 && canElim((*it))) {
		UINFO(4,"  Dead "<<(*it)<<endl);
		(*it)->unlinkFrBack()->deleteTree(); (*it)=NULL;
	    }
	}
    }

public:
    // CONSTRUCTORS
    DeadVisitor(AstNetlist* nodep, bool elimUserVars) {
	m_elimUserVars = elimUserVars;
	// Operate on whole netlist
	AstNode::userClearTree();	// userp() used on entire tree
	nodep->accept(*this);
	deadCheckVar();
	// Modules after vars, because might be vars we delete inside a mod we delete
	deadCheckMod();
    }
    virtual ~DeadVisitor() {}
};

//######################################################################
// Dead class functions

void V3Dead::deadifyAll(AstNetlist* nodep, bool elimUserVars) {
    UINFO(2,__FUNCTION__<<": "<<endl);
    DeadVisitor visitor (nodep, elimUserVars);
}
