// $Id$
//*************************************************************************
// DESCRIPTION: Verilator: Waves tracing
//
// Code available from: http://www.veripool.com/verilator
//
// AUTHORS: Wilson Snyder with Paul Wasson, Duane Gabli
//
//*************************************************************************
//
// Copyright 2003-2008 by Wilson Snyder.  This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// General Public License or the Perl Artistic License.
//
// Verilator is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
//*************************************************************************
// V3TraceDecl's Transformations:
//	Create trace CFUNCs
//	For each VARSCOPE
//	    If appropriate type of signal, create a TRACE
//		
//*************************************************************************

#include "config_build.h"
#include "verilatedos.h"
#include <stdio.h>
#include <stdarg.h>
#include <unistd.h>

#include "V3Global.h"
#include "V3TraceDecl.h"
#include "V3EmitCBase.h"
#include "V3Stats.h"

//######################################################################
// TraceDecl state, as a visitor of each AstNode

class TraceDeclVisitor : public EmitCBaseVisitor {
private:
    // NODE STATE
    // Cleared entire netlist	

    // STATE
    AstModule*		m_modp;		// Current module
    AstScope*		m_scopetopp;	// Current top scope
    AstCFunc*		m_initFuncp;	// Trace function being built
    AstCFunc*		m_fullFuncp;	// Trace function being built
    AstCFunc*		m_chgFuncp;	// Trace function being built
    V3Double0		m_statSigs;	// Statistic tracking
    V3Double0		m_statIgnSigs;	// Statistic tracking
    //int debug() { return 9; }

    // METHODS
    const char* varIgnoreTrace(AstVar* nodep) {
	// Return true if this shouldn't be traced
	string prettyName = nodep->prettyName();
	if (!nodep->isTrace())
	    return "Verilator trace_off";
	if (prettyName.c_str()[0] == '_')
	    return "Leading underscore";
	if (prettyName.find("._") != string::npos)
	    return "Inlined leading underscore";
	if (nodep->width() > 256) return "Wide bus > 256 bits";
	if (nodep->arrayElements() > 32) return "Wide memory > 32 ents";
	if (nodep->arrayp(1)) return "Unsupported: Multi-dimensional array";
	return NULL;
    }

    // VISITORS
    virtual void visit(AstTopScope* nodep, AstNUser*) {
	m_scopetopp = nodep->scopep();
	// The container for m_traceFuncp must be made first
	{
	    AstCFunc* funcp = new AstCFunc(nodep->fileline(), "traceInitThis", m_scopetopp);
	    funcp->slow(true);
	    funcp->argTypes(EmitCBaseVisitor::symClassVar()+", SpTraceVcd* vcdp, uint32_t code");
	    funcp->funcType(AstCFuncType::TRACE_INIT);
	    funcp->symProlog(true);
	    m_scopetopp->addActivep(funcp);
	    m_initFuncp = funcp;
	    UINFO(5,"  Newfunc "<<funcp<<endl);
	}
	{
	    AstCFunc* funcp = new AstCFunc(nodep->fileline(), "traceFullThis", m_scopetopp);
	    funcp->slow(true);
	    funcp->argTypes(EmitCBaseVisitor::symClassVar()+", SpTraceVcd* vcdp, uint32_t code");
	    funcp->funcType(AstCFuncType::TRACE_FULL);
	    funcp->symProlog(true);
	    m_scopetopp->addActivep(funcp);
	    m_fullFuncp = funcp;
	}
	{
	    AstCFunc* funcp = new AstCFunc(nodep->fileline(), "traceChgThis", m_scopetopp);
	    funcp->argTypes(EmitCBaseVisitor::symClassVar()+", SpTraceVcd* vcdp, uint32_t code");
	    funcp->funcType(AstCFuncType::TRACE_CHANGE);
	    funcp->symProlog(true);
	    m_scopetopp->addActivep(funcp);
	    m_chgFuncp = funcp;
	}
	nodep->iterateChildren(*this);
    }
    virtual void visit(AstVarScope* nodep, AstNUser*) {
	nodep->iterateChildren(*this);
	if (!nodep->varp()->isTemp() && !nodep->varp()->isParam() && !nodep->varp()->isFuncLocal()) {
	    UINFO(5, "    vsc "<<nodep<<endl);
	    AstVar* varp = nodep->varp();
	    AstScope* scopep = nodep->scopep();
	    // Compute show name
	    string showname = scopep->prettyName() + "." + varp->prettyName();
	    if (showname.substr(0,4) == "TOP.") showname.replace(0,4,"");
	    if (!m_initFuncp) nodep->v3fatalSrc("NULL");
	    if (varIgnoreTrace(varp)) {
		m_statIgnSigs++;
		m_initFuncp->addStmtsp(
		    new AstComment(nodep->fileline(),
				   "Tracing: "+showname+" // Ignored: "+varIgnoreTrace(varp)));
	    } else {
		m_statSigs++;
		AstNode* valuep = NULL;
		if (nodep->valuep()) valuep=nodep->valuep()->cloneTree(true);
		else valuep = new AstVarRef(nodep->fileline(), nodep, false);
		AstTraceDecl* declp = new AstTraceDecl(nodep->fileline(), showname, varp);
		m_initFuncp->addStmtsp(declp);
		m_chgFuncp->addStmtsp(new AstTraceInc(nodep->fileline(), declp, valuep));
		// The full version will get constructed in V3Trace
	    }
	}
    }
    //--------------------
    virtual void visit(AstNode* nodep, AstNUser*) {
	nodep->iterateChildren(*this);
    }

public:
    // CONSTUCTORS
    TraceDeclVisitor(AstNetlist* nodep) {
	m_scopetopp = NULL;
	m_initFuncp = NULL;
	m_fullFuncp = NULL;
	m_chgFuncp = NULL;
	nodep->accept(*this);
    }
    virtual ~TraceDeclVisitor() {
	V3Stats::addStat("Tracing, Traced signals", m_statSigs);
	V3Stats::addStat("Tracing, Ignored signals", m_statIgnSigs);
    }
};

//######################################################################
// Trace class functions

void V3TraceDecl::traceDeclAll(AstNetlist* nodep) {
    UINFO(2,__FUNCTION__<<": "<<endl);
    TraceDeclVisitor visitor (nodep);
}
