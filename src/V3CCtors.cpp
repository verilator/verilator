// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Generate C language constructors and AstCReset nodes.
//
// Code available from: http://www.veripool.org/verilator
//
//*************************************************************************
//
// Copyright 2003-2017 by Wilson Snyder.  This program is free software; you can
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
// V3CCtors's Transformations:
//	Iterates over all modules and
// 	for all AstVar, create a creates a AstCReset node in an _ctor_var_reset AstCFunc.
//	for all AstCoverDecl, move the declaration into a _configure_coverage AstCFunc.
//	For each variable that needs reset, add a AstCReset node.
//
//	This transformation honors outputSplitCFuncs.
//*************************************************************************
#include "config_build.h"
#include "verilatedos.h"
#include <cstdio>
#include <cstdarg>
#include <unistd.h>
#include <cmath>
#include <map>
#include <vector>
#include <algorithm>

#include "V3Global.h"
#include "V3EmitCBase.h"
#include "V3CCtors.h"

class V3CCtorsVisitor {
private:
    string 		m_basename;
    string 		m_argsp;
    string 		m_callargsp;
    AstNodeModule*	m_modp;		// Current module
    AstCFunc*		m_tlFuncp;	// Top level function being built
    AstCFunc*		m_funcp;	// Current function
    int			m_numStmts;	// Number of statements output
    int			m_funcNum;	// Function number being built

public:
    void add(AstNode* nodep) {
	if (v3Global.opt.outputSplitCFuncs()
	    && v3Global.opt.outputSplitCFuncs() < m_numStmts) {
	    m_funcp = NULL;
	}
	if (!m_funcp) {
	    m_funcp = new AstCFunc(m_modp->fileline(), m_basename + "_" + cvtToStr(++m_funcNum), NULL, "void");
	    m_funcp->isStatic(false);
	    m_funcp->declPrivate(true);
	    m_funcp->slow(true);
	    m_funcp->argTypes(m_argsp);
	    m_modp->addStmtp(m_funcp);

	    // Add a top call to it
	    AstCCall* callp = new AstCCall(m_modp->fileline(), m_funcp);
	    callp->argTypes(m_callargsp);

	    m_tlFuncp->addStmtsp(callp);
	    m_numStmts = 0;
	}
	m_funcp->addStmtsp(nodep);
	m_numStmts += 1;
    }

    V3CCtorsVisitor(AstNodeModule* nodep, string basename, string argsp="", string callargsp="",
		    const string& stmt="") {
	m_basename = basename;
	m_argsp = argsp;
	m_callargsp = callargsp;
	m_modp = nodep;
	m_numStmts = 0;
	m_funcNum = 0;
	m_tlFuncp = new AstCFunc(nodep->fileline(), basename, NULL, "void");
	m_tlFuncp->declPrivate(true);
	m_tlFuncp->isStatic(false);
	m_tlFuncp->slow(true);
	m_tlFuncp->argTypes(m_argsp);
	if (stmt != "") {
	    m_tlFuncp->addStmtsp(new AstCStmt(nodep->fileline(), stmt));
	}
	m_funcp = m_tlFuncp;
	m_modp->addStmtp(m_tlFuncp);
    }
    ~V3CCtorsVisitor() {}
};

//######################################################################

void V3CCtors::cctorsAll() {
    UINFO(2,__FUNCTION__<<": "<<endl);
    for (AstNodeModule* modp = v3Global.rootp()->modulesp(); modp; modp=modp->nextp()->castNodeModule()) {
	// Process each module in turn
	V3CCtorsVisitor var_reset (modp, "_ctor_var_reset");
	V3CCtorsVisitor configure_coverage (modp, "_configure_coverage",
					    EmitCBaseVisitor::symClassVar()+ ", bool first", "vlSymsp, first",
					    "if (0 && vlSymsp && first) {} // Prevent unused\n");

	for (AstNode* np = modp->stmtsp(); np; np = np->nextp()) {
	    AstVar* varp = np->castVar();
	    if (varp) var_reset.add(new AstCReset(varp->fileline(), new AstVarRef(varp->fileline(), varp, true)));
	    AstCoverDecl* coverp = np->castCoverDecl();
	    if (coverp) {
		AstNode* backp = coverp->backp();
		coverp->unlinkFrBack();
		configure_coverage.add(coverp);
		np = backp;
	    }
	}
    }
}
