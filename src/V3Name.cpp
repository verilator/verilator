// $Id$
//*************************************************************************
// DESCRIPTION: Verilator: Change names for __PVT__'s
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
// V3Name's Transformations:
//		
//	Cell/Var's
//		Prepend __PVT__ to variable names
//*************************************************************************

#include "config.h"
#include <stdio.h>
#include <stdarg.h>
#include <unistd.h>
#include <algorithm>

#include "V3Global.h"
#include "V3Name.h"
#include "V3Ast.h"

//######################################################################
// Name state, as a visitor of each AstNode

class NameVisitor : public AstNVisitor {
private:
    // NODE STATE
    // Cleared on Netlist
    //  AstCell::user()		-> bool.  Set true if already processed
    //  AstScope::user()	-> bool.  Set true if already processed
    //  AstVar::user()		-> bool.  Set true if already processed
    //
    //  AstCell::user2()	-> bool.  Set true if was privitized
    //  AstVar::user2()		-> bool.  Set true if was privitized

    // STATE
    AstModule*	m_modp;

    //int debug() { return 9; }

    // VISITORS
    virtual void visit(AstNetlist* nodep, AstNUser*) {
	AstNode::userClearTree();
	AstNode::user2ClearTree();
	nodep->iterateChildren(*this);
    }
    virtual void visit(AstModule* nodep, AstNUser*) {
	m_modp = nodep;
	nodep->iterateChildren(*this);
	m_modp = NULL;
    }
    // Add __PVT__ to names of local signals
    virtual void visit(AstVar* nodep, AstNUser*) {
	// Don't iterate... Don't need temps for RANGES under the Var.
	if (!nodep->user()
	    && !m_modp->isTop()
	    && !nodep->isSigPublic()
	    && !nodep->isTemp()) {	// Don't bother to rename internal signals
	    // Change the name to something private...
	    string newname = (string)"__PVT__"+nodep->name();
	    nodep->name(newname);
	    nodep->user(1);
	    nodep->user2(1);
	}
    }
    virtual void visit(AstVarRef* nodep, AstNUser*) {
	if (nodep->varp()) {
	    nodep->varp()->iterateChildren(*this);
	    nodep->name(nodep->varp()->name());
	}
    }
    virtual void visit(AstCell* nodep, AstNUser*) {
	if (!nodep->user()
	    && !nodep->modp()->modPublic()) {
	    // Change the name to something private...
	    string newname = (string)"__PVT__"+nodep->name();
	    nodep->name(newname);
	    nodep->user(1);
	    nodep->user2(1);
	}
	nodep->iterateChildren(*this);
    }
    virtual void visit(AstScope* nodep, AstNUser*) {
	if (!nodep->user()) {
	    if (nodep->aboveScopep()) nodep->aboveScopep()->iterateChildren(*this);
	    nodep->aboveCellp()->iterateChildren(*this);
	    // Always recompute name (as many level above scope may have changed)
	    // Same formula as V3Scope
	    nodep->name(nodep->isTop() ? "TOP"
			: (nodep->aboveScopep()->name()+"."+nodep->aboveCellp()->name()));
	    nodep->user(1);
	}
	nodep->iterateChildren(*this);
    }

    //--------------------
    virtual void visit(AstNode* nodep, AstNUser*) {
	nodep->iterateChildren(*this);
    }
public:
    // CONSTUCTORS
    NameVisitor(AstNode* nodep) {
	nodep->accept(*this);
    }
    virtual ~NameVisitor() {}
};

//######################################################################
// Name class functions

void V3Name::nameAll(AstNetlist* nodep) {
    UINFO(2,__FUNCTION__<<": "<<endl);
    NameVisitor visitor (nodep);
}
