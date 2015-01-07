// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Break always into sensitivity block domains
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
// V3Block's Transformations:
//
// Note this can be called multiple times.
//   Create a IBLOCK(initial), SBLOCK(combo)
//	ALWAYS: Remove any-edges from sense list
//	    If no POS/NEG in senselist, Fold into SBLOCK(combo)
//	    Else fold into SBLOCK(sequent).
//	    OPTIMIZE: When support async clocks, fold into that block if possible
//	INITIAL: Move into IBLOCK
//	WIRE: Move into SBLOCK(combo)
//
//*************************************************************************

#ifndef _V3SENTREE_H_
#define _V3SENTREE_H_

#include "config_build.h"
#include "verilatedos.h"
#include <cstdio>
#include <cstdarg>
#include <unistd.h>
#include <map>
#include <algorithm>
#include <vector>

#include "V3Global.h"
#include "V3Ast.h"

//######################################################################
// Collect SenTrees under the entire scope
// And provide functions to find/add a new one

class SenTreeFinder : public AstNVisitor {
private:
    // STATE
    AstTopScope*	m_topscopep;		// Top scope to add statement to
    vector<AstSenTree*>	m_treesp;	// List of sensitive blocks, for folding

    // VISITORS
    static int debug() {
	static int level = -1;
	if (VL_UNLIKELY(level < 0)) level = v3Global.opt.debugSrcLevel(__FILE__);
	return level;
    }

    virtual void visit(AstNodeModule* nodep, AstNUser*) {
	// Only do the top
	if (nodep->isTop()) {
	    nodep->iterateChildren(*this);
	}
    }
    virtual void visit(AstTopScope* nodep, AstNUser*) {
	m_topscopep = nodep;
	nodep->iterateChildren(*this);
	// Don't clear topscopep, the namer persists beyond this visit
    }
    virtual void visit(AstScope* nodep, AstNUser*) {
	// But no SenTrees under TopScope's scope
    }
    // Memorize existing block names
    virtual void visit(AstActive* nodep, AstNUser*) {
	// Don't grab SenTrees under Actives, only those that are global (under Scope directly)
	nodep->iterateChildren(*this);
    }
    virtual void visit(AstSenTree* nodep, AstNUser*) {
	m_treesp.push_back(nodep);
    }
    // Empty visitors, speed things up
    virtual void visit(AstNodeStmt* nodep, AstNUser*) { }
    virtual void visit(AstNode* nodep, AstNUser*) {
	nodep->iterateChildren(*this);
    }
    // METHODS
public:
    void clear() {
	m_topscopep = NULL;
	m_treesp.clear();
    }
    AstSenTree* getSenTree(FileLine* fl, AstSenTree* sensesp) {
	// Return a global sentree that matches given sense list.
	// Not the fastest, but there tend to be few clocks
	AstSenTree* treep = NULL;
	//sensesp->dumpTree(cout,"  Lookingfor: ");
	for (vector<AstSenTree*>::iterator it = m_treesp.begin(); it!=m_treesp.end(); ++it) {
	    treep = *it;
	    if (treep) {  // Not deleted
		if (treep->sameTree(sensesp)) {
		    UINFO(8,"    Found SBLOCK "<<treep<<endl);
		    goto found;
		}
	    }
	    treep = NULL;
	}
      found:
	// Not found, form a new one
	if (!treep) {
	    UASSERT(m_topscopep,"Never called main()");
	    treep = sensesp->cloneTree(false);
	    m_topscopep->addStmtsp(treep);
	    UINFO(8,"    New SENTREE "<<treep<<endl);
	    m_treesp.push_back(treep);
	    // Note blocks may have also been added above in the Active visitor
	}
	return treep;
    }
public:
    // CONSTUCTORS
    SenTreeFinder() {
	clear();
    }
    virtual ~SenTreeFinder() {}
    void main(AstTopScope* nodep) {
	nodep->accept(*this);
    }
};

#endif // Guard
