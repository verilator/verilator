//*************************************************************************
// DESCRIPTION: Verilator: Waves tracing
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
// V3TraceDecl's Transformations:
//	Create trace CFUNCs
//	For each VARSCOPE
//	    If appropriate type of signal, create a TRACE
//
//*************************************************************************

#include "config_build.h"
#include "verilatedos.h"
#include <cstdio>
#include <cstdarg>
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

    // STATE
    AstNodeModule*	m_modp;		// Current module
    AstScope*		m_scopetopp;	// Current top scope
    AstCFunc*		m_initFuncp;	// Trace function being built
    AstCFunc*		m_initSubFuncp;	// Trace function being built (under m_init)
    int			m_initSubStmts;	// Number of statements in function
    AstCFunc*		m_fullFuncp;	// Trace function being built
    AstCFunc*		m_chgFuncp;	// Trace function being built
    int			m_funcNum;	// Function number being built

    V3Double0		m_statSigs;	// Statistic tracking
    V3Double0		m_statIgnSigs;	// Statistic tracking

    // METHODS
    static int debug() {
	static int level = -1;
	if (VL_UNLIKELY(level < 0)) level = v3Global.opt.debugSrcLevel(__FILE__);
	return level;
    }

    const char* varIgnoreTrace(AstVar* nodep) {
	// Return true if this shouldn't be traced
	// See also similar rule in V3Coverage::varIgnoreToggle
	string prettyName = nodep->prettyName();
	if (!nodep->isTrace())
	    return "Verilator trace_off";
	if (!v3Global.opt.traceUnderscore()) {
	    if (prettyName.c_str()[0] == '_')
	        return "Leading underscore";
	    if (prettyName.find("._") != string::npos)
	        return "Inlined leading underscore";
        }
	if ((int)nodep->width() > v3Global.opt.traceMaxWidth()) return "Wide bus > --trace-max-width bits";
	if ((int)nodep->dtypep()->arrayElements() > v3Global.opt.traceMaxArray()) return "Wide memory > --trace-max-array ents";
	if (!(nodep->dtypeSkipRefp()->castBasicDType()
	      || (nodep->dtypeSkipRefp()->castArrayDType()
		  && nodep->dtypeSkipRefp()->castArrayDType()->dtypeSkipRefp()->castBasicDType()))) {
	    return "Unsupported: Multi-dimensional array";
	}
	return NULL;
    }

    AstCFunc* newCFunc(AstCFuncType type, const string& name, bool slow) {
	AstCFunc* funcp = new AstCFunc(m_scopetopp->fileline(), name, m_scopetopp);
	funcp->slow(slow);
	funcp->argTypes(EmitCBaseVisitor::symClassVar()+", "+v3Global.opt.traceClassBase()+"* vcdp, uint32_t code");
	funcp->funcType(type);
	funcp->symProlog(true);
	m_scopetopp->addActivep(funcp);
	UINFO(5,"  Newfunc "<<funcp<<endl);
	return funcp;
    }
    AstCFunc* newCFuncSub(AstCFunc* basep) {
	string name = basep->name()+"__"+cvtToStr(++m_funcNum);
	AstCFunc* funcp = NULL;
	if (basep->funcType()==AstCFuncType::TRACE_INIT) {
	    funcp = newCFunc(AstCFuncType::TRACE_INIT_SUB, name, basep->slow());
	} else {
	    basep->v3fatalSrc("Strange base function type");
	}
	// cppcheck-suppress nullPointer  // above fatal prevents it
	AstCCall* callp = new AstCCall(funcp->fileline(), funcp);
	callp->argTypes("vlSymsp, vcdp, code");
	basep->addStmtsp(callp);
	return funcp;
    }
    void addCFuncStmt(AstCFunc* basep, AstNode* nodep) {
	basep->addStmtsp(nodep);
    }

    // VISITORS
    virtual void visit(AstTopScope* nodep, AstNUser*) {
	m_scopetopp = nodep->scopep();
	// Make containers for TRACEDECLs first
	m_initFuncp = newCFunc(AstCFuncType::TRACE_INIT, "traceInitThis", true);
	m_fullFuncp = newCFunc(AstCFuncType::TRACE_FULL, "traceFullThis", true);
	m_chgFuncp  = newCFunc(AstCFuncType::TRACE_CHANGE, "traceChgThis", false);
	//
	m_initSubFuncp = newCFuncSub(m_initFuncp);
	// And find variables
	nodep->iterateChildren(*this);
    }
    virtual void visit(AstVarScope* nodep, AstNUser*) {
	nodep->iterateChildren(*this);
	if (!nodep->varp()->isTemp() && !nodep->varp()->isParam() && !nodep->varp()->isFuncLocal()) {
	    UINFO(5, "    vsc "<<nodep<<endl);
	    AstVar* varp = nodep->varp();
	    AstScope* scopep = nodep->scopep();
	    // Compute show name
	    // This code assumes SPTRACEVCDC_VERSION >= 1330;
	    // it uses spaces to separate hierarchy components.
	    string showname = AstNode::vcdName(scopep->name() + " " + varp->name());
	    if (showname.substr(0,4) == "TOP ") showname.replace(0,4,"");
	    if (!m_initSubFuncp) nodep->v3fatalSrc("NULL");
	    if (varIgnoreTrace(varp)) {
		++m_statIgnSigs;
		m_initSubFuncp->addStmtsp(
		    new AstComment(nodep->fileline(),
				   "Tracing: "+showname+" // Ignored: "+varIgnoreTrace(varp)));
	    } else {
		++m_statSigs;
		AstNode* valuep = NULL;
		if (nodep->valuep()) valuep=nodep->valuep()->cloneTree(true);
		else valuep = new AstVarRef(nodep->fileline(), nodep, false);
		AstTraceDecl* declp = new AstTraceDecl(nodep->fileline(), showname, varp);

		if (m_initSubStmts && v3Global.opt.outputSplitCTrace()
		    && m_initSubStmts > v3Global.opt.outputSplitCTrace()) {
		    m_initSubFuncp = newCFuncSub(m_initFuncp);
		    m_initSubStmts = 0;
		}

		m_initSubFuncp->addStmtsp(declp);
		m_initSubStmts += EmitCBaseCounterVisitor(declp).count();

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
	m_initSubFuncp = NULL;
	m_initSubStmts = 0;
	m_fullFuncp = NULL;
	m_chgFuncp = NULL;
	m_funcNum = 0;
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
