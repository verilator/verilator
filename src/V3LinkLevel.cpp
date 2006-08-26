// $Id$
//*************************************************************************
// DESCRIPTION: Verilator: Resolve module/signal name references
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
// LINKTOP TRANSFORMATIONS:
//	Utility functions
//	    Sort cells by depth
//	    Create new MODULE TOP with connections to below signals
//*************************************************************************

#include "config.h"
#include <stdio.h>
#include <stdarg.h>
#include <unistd.h>
#include <map>
#include <algorithm>
#include <vector>

#include "V3Global.h"
#include "V3LinkLevel.h"
#include "V3Ast.h"

//######################################################################
// Levelizing class functions

class LinkLevelVisitor : public AstNVisitor {
private:
    // STATE
    AstModule* m_modp;
    // VISITs
    virtual void visit(AstModule* nodep, AstNUser*) {
	m_modp = nodep;
	nodep->iterateChildren(*this);
    }
    virtual void visit(AstCell* nodep, AstNUser*) {
	// Track module depths, so can sort list from parent down to children
	nodep->modp()->level(max(nodep->modp()->level(), (1+m_modp->level())));
	UINFO(5," Under "<<m_modp<<"  IS  "<<nodep->modp()<<endl);
	if (nodep->modp()->level()>99) nodep->v3error("Over 99 levels of cell hierarchy.  Probably cell instantiates itself.");
	// Recurse in, preserving state
	AstModule* holdmodp = m_modp;
	nodep->modp()->accept(*this);
	m_modp = holdmodp;
    }
    // For speed, don't recurse things that can't have cells
    virtual void visit(AstNodeStmt*, AstNUser*) {}
    virtual void visit(AstNode* nodep, AstNUser*) {
	// Default: Just iterate
	nodep->iterateChildren(*this);
    }

public:
    // CONSTUCTORS
    LinkLevelVisitor() {}
    virtual ~LinkLevelVisitor() {}
    void main(AstNetlist* rootp) {
	rootp->accept(*this);
    }
};

struct CmpLevel {
    inline bool operator () (const AstModule* lhsp, const AstModule* rhsp) const {
	return lhsp->level() < rhsp->level();
    }
};

void V3LinkLevel::modSortByLevel() {
    // Sort modules by levels, root down to lowest children
    // Calculate levels again in case we added modules
    UINFO(2,"modSortByLevel()\n");
    LinkLevelVisitor visitor;
    visitor.main(v3Global.rootp());

    vector<AstModule*> vec;
    AstModule* topp = NULL;
    for (AstModule* nodep = v3Global.rootp()->modulesp(); nodep; nodep=nodep->nextp()->castModule()) {
	if (nodep->level()<=2) {
	    if (topp) nodep->v3error("Unsupported: Multiple top level modules: "
				     <<nodep->prettyName()<<" and "<<topp->prettyName());
	    topp = nodep;
	}
	vec.push_back(nodep);
    }
    sort(vec.begin(), vec.end(), CmpLevel()); // Sort the vector
    for (vector<AstModule*>::iterator it = vec.begin(); it != vec.end(); ++it) {
	AstModule* nodep = *it;
	nodep->unlinkFrBack();
    }
    if (v3Global.rootp()->modulesp()) v3Global.rootp()->v3fatalSrc("Unlink didn't work");
    for (vector<AstModule*>::iterator it = vec.begin(); it != vec.end(); ++it) {
	AstModule* nodep = *it;
	v3Global.rootp()->addModulep(nodep);
    }
}

//######################################################################
// Wrapping

void V3LinkLevel::wrapTop(AstNetlist* netlistp) {
    UINFO(2,__FUNCTION__<<": "<<endl);
    // We do ONLY the top module
    AstModule* oldmodp = netlistp->modulesp();
    AstModule* newmodp = new AstModule(oldmodp->fileline(), (string)"TOP_"+oldmodp->name());
    // Make the new module first in the list
    oldmodp->unlinkFrBackWithNext();
    newmodp->addNext(oldmodp);
    newmodp->level(1);
    newmodp->modPublic(true);
    netlistp->addModulep(newmodp);

    // Add instance
    AstCell* cellp = new AstCell(newmodp->fileline(),
				 (v3Global.opt.l2Name() ? "v" : oldmodp->name()),
				 oldmodp->name(),
				 NULL, NULL, NULL);
    cellp->modp(oldmodp);
    newmodp->addStmtp(cellp);

    // Add pins
    for (AstNode* subnodep=oldmodp->stmtsp(); subnodep; subnodep = subnodep->nextp()) {
	if (AstVar* oldvarp=subnodep->castVar()) {
	    UINFO(8,"VARWRAP "<<oldvarp<<endl);
	    if (oldvarp->isIO()) {
		AstVar* varp = oldvarp->cloneTree(false)->castVar();
		newmodp->addStmtp(varp);
		varp->sigPublic(true);	// User needs to be able to get to it...
		if (oldvarp->isInput() || oldvarp->isOutput()) {
		    oldvarp->primaryIO(true);
		    varp->primaryIO(true);
		}
		if (varp->isIO() && v3Global.opt.systemC()) varp->sc(true);

		AstPin* pinp = new AstPin(oldvarp->fileline(),0,oldvarp->name(),
					  new AstVarRef(varp->fileline(),
							varp, oldvarp->isOutput()));
		// Skip length and width comp; we know it's a direct assignment
		pinp->modVarp(oldvarp);
		pinp->widthSignedFrom(oldvarp);
		cellp->addPinsp(pinp);
	    }
	}
    }
}
