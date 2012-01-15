//*************************************************************************
// DESCRIPTION: Verilator: Resolve module/signal name references
//
// Code available from: http://www.veripool.org/verilator
//
// AUTHORS: Wilson Snyder with Paul Wasson, Duane Gabli
//
//*************************************************************************
//
// Copyright 2003-2012 by Wilson Snyder.  This program is free software; you can
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
// LINKTOP TRANSFORMATIONS:
//	Utility functions
//	    Sort cells by depth
//	    Create new MODULE TOP with connections to below signals
//*************************************************************************

#include "config_build.h"
#include "verilatedos.h"
#include <cstdio>
#include <cstdarg>
#include <unistd.h>
#include <map>
#include <algorithm>
#include <vector>

#include "V3Global.h"
#include "V3LinkLevel.h"
#include "V3Ast.h"

//######################################################################
// Levelizing class functions

struct CmpLevel {
    inline bool operator () (const AstNodeModule* lhsp, const AstNodeModule* rhsp) const {
	return lhsp->level() < rhsp->level();
    }
};

void V3LinkLevel::modSortByLevel() {
    // Sort modules by levels, root down to lowest children
    // Calculate levels again in case we added modules
    UINFO(2,"modSortByLevel()\n");

    // level() was computed for us in V3LinkCells

    typedef vector<AstNodeModule*> ModVec;

    ModVec vec;
    AstNodeModule* topp = NULL;
    for (AstNodeModule* nodep = v3Global.rootp()->modulesp(); nodep; nodep=nodep->nextp()->castNodeModule()) {
	if (nodep->level()<=2) {
	    if (topp) {
		nodep->v3warn(E_MULTITOP, "Unsupported: Multiple top level modules: "
			      <<nodep->prettyName()<<" and "<<topp->prettyName());
		nodep->v3warn(E_MULTITOP, "Fix, or use --top-module option to select which you want.");
	    }
	    topp = nodep;
	}
	vec.push_back(nodep);
    }
    sort(vec.begin(), vec.end(), CmpLevel()); // Sort the vector
    for (ModVec::iterator it = vec.begin(); it != vec.end(); ++it) {
	AstNodeModule* nodep = *it;
	nodep->unlinkFrBack();
    }
    if (v3Global.rootp()->modulesp()) v3Global.rootp()->v3fatalSrc("Unlink didn't work");
    for (ModVec::iterator it = vec.begin(); it != vec.end(); ++it) {
	AstNodeModule* nodep = *it;
	v3Global.rootp()->addModulep(nodep);
    }
}

//######################################################################
// Wrapping

void V3LinkLevel::wrapTop(AstNetlist* netlistp) {
    UINFO(2,__FUNCTION__<<": "<<endl);
    // We do ONLY the top module
    AstNodeModule* oldmodp = netlistp->modulesp();
    if (!oldmodp) netlistp->v3fatalSrc("No module found to process");
    AstNodeModule* newmodp = new AstModule(oldmodp->fileline(), (string)"TOP_"+oldmodp->name());
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
		AstVar* varp = oldvarp->cloneTree(false);
		newmodp->addStmtp(varp);
		varp->sigPublic(true);	// User needs to be able to get to it...
		if (oldvarp->isIO()) {
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

    wrapTopPackages(netlistp, newmodp);
}

void V3LinkLevel::wrapTopPackages(AstNetlist* netlistp, AstNodeModule* newmodp) {
    // Instantiate all packages under the top wrapper
    // This way all later SCOPE based optimizations can ignore packages
    for (AstNodeModule* modp = netlistp->modulesp(); modp; modp=modp->nextp()->castNodeModule()) {
	if (modp->castPackage()) {
	    AstCell* cellp = new AstCell(modp->fileline(),
					 // Could add __03a__03a="::" to prevent conflict
					 // with module names/"v"
					 modp->name(),
					 modp->name(),
					 NULL, NULL, NULL);
	    cellp->modp(modp);
	    newmodp->addStmtp(cellp);
	}
    }
}
