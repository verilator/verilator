// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Generate AstCReset nodes.
//
// Code available from: http://www.veripool.org/verilator
//
//*************************************************************************
//
// Copyright 2003-2016 by Wilson Snyder.  This program is free software; you can
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
// V3VarReset's Transformations:
//	Iterates over all modules and creates a _ctor_var_reset AstCFunc
//	For each variable that needs reset, add a AstCReset node.
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
#include "V3VarResets.h"

class V3VarReset {
private:
    AstNodeModule*	m_modp;		// Current module
    AstCFunc*		m_tlFuncp;	// Top level function being built
    AstCFunc*		m_funcp;	// Current function
    int			m_numStmts;	// Number of statements output
    int			m_funcNum;	// Function number being built

    void initializeVar(AstVar* nodep) {
	if (v3Global.opt.outputSplitCFuncs()
	    && v3Global.opt.outputSplitCFuncs() < m_numStmts) {
	    m_funcp = NULL;
	}
	if (!m_funcp) {
	    m_funcp = new AstCFunc(m_modp->fileline(), "_ctor_var_reset_" + cvtToStr(++m_funcNum), NULL, "void");
	    m_funcp->isStatic(false);
	    m_funcp->declPrivate(true);
	    m_funcp->slow(true);
	    m_modp->addStmtp(m_funcp);

	    // Add a top call to it
	    AstCCall* callp = new AstCCall(m_modp->fileline(), m_funcp);

	    m_tlFuncp->addStmtsp(callp);
	    m_numStmts = 0;
	}
	m_funcp->addStmtsp(new AstCReset(nodep->fileline(), new AstVarRef(nodep->fileline(), nodep, true)));
	m_numStmts += 1;
    }

public:
    V3VarReset(AstNodeModule* nodep) {
	m_modp = nodep;
	m_numStmts = 0;
	m_funcNum = 0;
	m_tlFuncp = new AstCFunc(nodep->fileline(), "_ctor_var_reset", NULL, "void");
	m_tlFuncp->declPrivate(true);
	m_tlFuncp->isStatic(false);
	m_tlFuncp->slow(true);
	m_funcp = m_tlFuncp;
	m_modp->addStmtp(m_tlFuncp);
	for (AstNode* np = m_modp->stmtsp(); np; np = np->nextp()) {
	    AstVar* varp = np->castVar();
	    if (varp) initializeVar(varp); 
	}
    }
};

//######################################################################

void V3VarResets::emitResets() {
    UINFO(2,__FUNCTION__<<": "<<endl);
    for (AstNodeModule* nodep = v3Global.rootp()->modulesp(); nodep; nodep=nodep->nextp()->castNodeModule()) {
    	// Process each module in turn
	V3VarReset v(nodep);
    }
}
