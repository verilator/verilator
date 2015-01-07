// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Branch prediction
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
// BRANCH TRANSFORMATIONS:
//	At each IF/(IF else).
//	   Count underneath $display/$stop statements.
//	   If more on if than else, this branch is unlikely, or vice-versa.
//	At each FTASKREF,
//	   Count calls into the function
//	Then, if FTASK is called only once, add inline attribute
//
//*************************************************************************

#include "config_build.h"
#include "verilatedos.h"
#include <cstdio>
#include <cstdarg>
#include <unistd.h>
#include <map>

#include "V3Global.h"
#include "V3Branch.h"
#include "V3Ast.h"

//######################################################################
// Branch state, as a visitor of each AstNode

class BranchVisitor : public AstNVisitor {
private:
    // NODE STATE
    // Entire netlist:
    //  AstFTask::user1()	-> int.  Number of references
    AstUser1InUse	m_inuser1;

    // TYPES
    typedef vector<AstCFunc*> CFuncVec;

    // STATE
    int		m_likely;	// Excuses for branch likely taken
    int		m_unlikely;	// Excuses for branch likely not taken
    CFuncVec	m_cfuncsp;	// List of all tasks

    // METHODS
    static int debug() {
	static int level = -1;
	if (VL_UNLIKELY(level < 0)) level = v3Global.opt.debugSrcLevel(__FILE__);
	return level;
    }

    void reset() {
	m_likely = false;
	m_unlikely = false;
    }
    void checkUnlikely(AstNode* nodep) {
	if (nodep->isUnlikely()) {
	    UINFO(4,"  UNLIKELY: "<<nodep<<endl);
	    m_unlikely++;
	}
    }

    // VISITORS
    virtual void visit(AstNodeIf* nodep, AstNUser*) {
	UINFO(4," IF: "<<nodep<<endl);
	int lastLikely = m_likely;
	int lastUnlikely = m_unlikely;
	{
	    // Do if
	    reset();
	    nodep->ifsp()->iterateAndNext(*this);
	    int ifLikely = m_likely;
	    int ifUnlikely = m_unlikely;
	    // Do else
	    reset();
	    nodep->elsesp()->iterateAndNext(*this);
	    int elseLikely = m_likely;
	    int elseUnlikely = m_unlikely;
	    // Compute
	    int likeness = ifLikely - ifUnlikely - (elseLikely - elseUnlikely);
	    if (likeness>0) {
		nodep->branchPred(AstBranchPred::BP_LIKELY);
	    } else if (likeness<0) {
		nodep->branchPred(AstBranchPred::BP_UNLIKELY);
	    } // else leave unknown
	}
	m_likely = lastLikely;
	m_unlikely = lastUnlikely;
    }
    virtual void visit(AstCCall* nodep, AstNUser*) {
	checkUnlikely(nodep);
	nodep->funcp()->user1Inc();
	nodep->iterateChildren(*this);
    }
    virtual void visit(AstCFunc* nodep, AstNUser*) {
	checkUnlikely(nodep);
	m_cfuncsp.push_back(nodep);
	nodep->iterateChildren(*this);
    }
    virtual void visit(AstNode* nodep, AstNUser*) {
	checkUnlikely(nodep);
	nodep->iterateChildren(*this);
    }

    // METHODS
    void calc_tasks() {
	for (CFuncVec::iterator it=m_cfuncsp.begin(); it!=m_cfuncsp.end(); ++it) {
	    AstCFunc* nodep = *it;
	    if (!nodep->dontInline()) {
		nodep->isInline(true);
	    }
	}
    }

public:
    // CONSTUCTORS
    BranchVisitor(AstNetlist* nodep) {
	reset();
	nodep->iterateChildren(*this);
	calc_tasks();
    }
    virtual ~BranchVisitor() {}
};

//######################################################################
// Branch class functions

void V3Branch::branchAll(AstNetlist* rootp) {
    UINFO(2,__FUNCTION__<<": "<<endl);
    BranchVisitor visitor (rootp);
}
