// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Netlist (top level) functions
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
// COVERAGEJOIN TRANSFORMATIONS:
//	If two COVERTOGGLEs have same VARSCOPE, combine them
//*************************************************************************


#include "config_build.h"
#include "verilatedos.h"
#include <cstdio>
#include <cstdarg>
#include <unistd.h>
#include <vector>

#include "V3Global.h"
#include "V3CoverageJoin.h"
#include "V3Hashed.h"
#include "V3Stats.h"

//######################################################################
// CoverageJoin state, as a visitor of each AstNode

class CoverageJoinVisitor : public AstNVisitor {
private:
    // NODE STATE
    // V3Hashed
    //  AstCoverToggle->VarRef::user4()	// V3Hashed calculation

    //AstUser4InUse	In V3Hashed

    // TYPES
    typedef vector<AstCoverToggle*> ToggleList;

    // STATE
    ToggleList		m_toggleps;	// List of of all AstCoverToggle's

    V3Double0		m_statToggleJoins;	// Statistic tracking

    // METHODS
    static int debug() {
	static int level = -1;
	if (VL_UNLIKELY(level < 0)) level = v3Global.opt.debugSrcLevel(__FILE__);
	return level;
    }

    void detectDuplicates() {
	UINFO(9,"Finding duplicates\n");
	// Note uses user4
	V3Hashed  hashed;	// Duplicate code detection
	// Hash all of the original signals we toggle cover
	for (ToggleList::iterator it = m_toggleps.begin(); it != m_toggleps.end(); ++it) {
	    AstCoverToggle* nodep = *it;
	    hashed.hashAndInsert(nodep->origp());
	}
	// Find if there are any duplicates
	for (ToggleList::iterator it = m_toggleps.begin(); it != m_toggleps.end(); ++it) {
	    AstCoverToggle* nodep = *it;
	    if (nodep->backp()) {   // nodep->backp() is null if we already detected it's a duplicate and unlinked it
		// Want to choose a base node, and keep finding duplicates that are identical
		// This prevents making chains where a->b, then c->d, then b->c, as we'll find a->b, a->c, a->d directly.
		while (1) {
		    V3Hashed::iterator dupit = hashed.findDuplicate(nodep->origp());
		    if (dupit == hashed.end()) break;
		    //
		    AstNode* duporigp = hashed.iteratorNodep(dupit);
		    // Note hashed will point to the original variable (what's duplicated), not the covertoggle,
		    // but we need to get back to the covertoggle which is immediately above, so:
		    AstCoverToggle* removep = duporigp->backp()->castCoverToggle();
		    if (!removep) nodep->v3fatalSrc("CoverageJoin duplicate of wrong type");
		    UINFO(8,"  Orig "<<nodep<<" -->> "<<nodep->incp()->declp()<<endl);
		    UINFO(8,"   dup "<<removep<<" -->> "<<removep->incp()->declp()<<endl);
		    // The CoverDecl the duplicate pointed to now needs to point to the original's data
		    // IE the duplicate will get the coverage number from the non-duplicate
		    AstCoverDecl* datadeclp = nodep->incp()->declp()->dataDeclThisp();
		    removep->incp()->declp()->dataDeclp (datadeclp);
		    UINFO(8,"   new "<<removep->incp()->declp()<<endl);
		    // Mark the found node as a duplicate of the first node
		    // (Not vice-versa as we have the iterator for the found node)
		    removep->unlinkFrBack();  pushDeletep(removep); removep=NULL;
		    // Remove node from comparison so don't hit it again
		    hashed.erase(dupit);
		    ++m_statToggleJoins;
		}
	    }
	}
    }

    // VISITORS
    virtual void visit(AstNetlist* nodep, AstNUser*) {
	// Find all Coverage's
	nodep->iterateChildren(*this);
	// Simplify
	detectDuplicates();
    }
    virtual void visit(AstCoverToggle* nodep, AstNUser*) {
	m_toggleps.push_back(nodep);
	nodep->iterateChildren(*this);
    }
    //--------------------
    virtual void visit(AstNodeMath* nodep, AstNUser*) {}  // Accelerate
    virtual void visit(AstNode* nodep, AstNUser*) {
	nodep->iterateChildren(*this);
    }

public:
    // CONSTUCTORS
    CoverageJoinVisitor(AstNetlist* nodep) {
	nodep->accept(*this);
    }
    virtual ~CoverageJoinVisitor() {
	V3Stats::addStat("Coverage, Toggle points joined", m_statToggleJoins);
    }
};

//######################################################################
// Coverage class functions

void V3CoverageJoin::coverageJoin(AstNetlist* rootp) {
    UINFO(2,__FUNCTION__<<": "<<endl);
    CoverageJoinVisitor visitor (rootp);
    V3Global::dumpCheckGlobalTree("coveragejoin.tree", 0, v3Global.opt.dumpTreeLevel(__FILE__) >= 3);
}
