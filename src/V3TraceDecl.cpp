// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Waves tracing
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
    AstScope*		m_scopetopp;	// Current top scope
    AstCFunc*		m_initFuncp;	// Trace function being built
    AstCFunc*		m_initSubFuncp;	// Trace function being built (under m_init)
    int			m_initSubStmts;	// Number of statements in function
    AstCFunc*		m_fullFuncp;	// Trace function being built
    AstCFunc*		m_chgFuncp;	// Trace function being built
    int			m_funcNum;	// Function number being built
    AstVarScope*	m_traVscp;	// Signal being trace constructed
    AstNode*		m_traValuep;	// Signal being traced's value to trace in it
    string		m_traShowname;	// Signal being traced's component name

    V3Double0		m_statSigs;	// Statistic tracking
    V3Double0		m_statIgnSigs;	// Statistic tracking

    // METHODS
    static int debug() {
	static int level = -1;
	if (VL_UNLIKELY(level < 0)) level = v3Global.opt.debugSrcLevel(__FILE__);
	return level;
    }

    const char* vscIgnoreTrace(AstVarScope* nodep) {
	// Return true if this shouldn't be traced
	// See also similar rule in V3Coverage::varIgnoreToggle
	AstVar* varp = nodep->varp();
	string prettyName = varp->prettyName();
	if (!varp->isTrace()) {
	    return "Verilator trace_off";
	}
	else if (!nodep->isTrace()) {
	    return "Verilator cell trace_off";
	}
	else if (!v3Global.opt.traceUnderscore()) {
	    if (prettyName.size()>=1 && prettyName[0] == '_')
	        return "Leading underscore";
	    if (prettyName.find("._") != string::npos)
	        return "Inlined leading underscore";
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
    void addCFuncStmt(AstCFunc* basep, AstNode* nodep, VNumRange arrayRange) {
	basep->addStmtsp(nodep);
    }
    void addTraceDecl(const VNumRange& arrayRange,
		      int widthOverride) {  // If !=0, is packed struct/array where basicp size misreflects one element
	VNumRange bitRange;
	AstBasicDType* bdtypep = m_traValuep->dtypep()->basicp();
	if (widthOverride) bitRange = VNumRange(widthOverride-1,0,false);
	else if (bdtypep) bitRange = bdtypep->nrange();
	AstTraceDecl* declp = new AstTraceDecl(m_traVscp->fileline(), m_traShowname, m_traValuep,
					       bitRange, arrayRange);
	UINFO(9,"Decl "<<declp<<endl);

	if (m_initSubStmts && v3Global.opt.outputSplitCTrace()
	    && m_initSubStmts > v3Global.opt.outputSplitCTrace()) {
	    m_initSubFuncp = newCFuncSub(m_initFuncp);
	    m_initSubStmts = 0;
	}

	m_initSubFuncp->addStmtsp(declp);
	m_initSubStmts += EmitCBaseCounterVisitor(declp).count();

	m_chgFuncp->addStmtsp(new AstTraceInc(m_traVscp->fileline(), declp, m_traValuep->cloneTree(true)));
	// The full version will get constructed in V3Trace
    }
    void addIgnore(const char* why) {
	++m_statIgnSigs;
	m_initSubFuncp->addStmtsp(
	    new AstComment(m_traVscp->fileline(), "Tracing: "+m_traShowname+" // Ignored: "+why));
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
	// Avoid updating this if (), instead see varp->isTrace()
	if (!nodep->varp()->isTemp() && !nodep->varp()->isFuncLocal()) {
	    UINFO(5, "    vsc "<<nodep<<endl);
	    AstVar* varp = nodep->varp();
	    AstScope* scopep = nodep->scopep();
	    // Compute show name
	    // This code assumes SPTRACEVCDC_VERSION >= 1330;
	    // it uses spaces to separate hierarchy components.
	    m_traShowname = AstNode::vcdName(scopep->name() + " " + varp->name());
	    if (m_traShowname.substr(0,4) == "TOP ") m_traShowname.replace(0,4,"");
	    if (!m_initSubFuncp) nodep->v3fatalSrc("NULL");

	    m_traVscp = nodep;
	    m_traValuep = NULL;
	    if (vscIgnoreTrace(nodep)) {
		addIgnore(vscIgnoreTrace(nodep));
	    } else {
		++m_statSigs;
		if (nodep->valuep()) m_traValuep = nodep->valuep()->cloneTree(true);
		else m_traValuep = new AstVarRef(nodep->fileline(), nodep, false);
		{
		    // Recurse into data type of the signal; the visitors will call addTraceDecl()
		    varp->dtypeSkipRefp()->accept(*this);
		}
		// Cleanup
		if (m_traValuep) { m_traValuep->deleteTree(); m_traValuep=NULL; }
	    }
	    m_traVscp = NULL;
	    m_traValuep = NULL;
	    m_traShowname = "";
	}
    }
    // VISITORS - Data types when tracing
    virtual void visit(AstConstDType* nodep, AstNUser*) {
	if (m_traVscp) {
	    nodep->subDTypep()->skipRefp()->accept(*this);
	}
    }
    virtual void visit(AstRefDType* nodep, AstNUser*) {
	if (m_traVscp) {
	    nodep->subDTypep()->skipRefp()->accept(*this);
	}
    }
    virtual void visit(AstUnpackArrayDType* nodep, AstNUser*) {
	// Note more specific dtypes above
	if (m_traVscp) {
	    if ((int)nodep->arrayUnpackedElements() > v3Global.opt.traceMaxArray()) {
		addIgnore("Wide memory > --trace-max-array ents");
	    } else if (nodep->subDTypep()->skipRefp()->castBasicDType()  // Nothing lower than this array
		       && m_traVscp->dtypep()->skipRefp() == nodep) {  // Nothing above this array
		// Simple 1-D array, use exising V3EmitC runtime loop rather than unrolling
		// This will put "(index)" at end of signal name for us
		addTraceDecl(nodep->declRange(), 0);
	    } else {
		// Unroll now, as have no other method to get right signal names
		AstNodeDType* subtypep = nodep->subDTypep()->skipRefp();
		for (int i=nodep->lsb(); i<=nodep->msb(); ++i) {
		    string oldShowname = m_traShowname;
		    AstNode* oldValuep = m_traValuep;
		    {
			m_traShowname += string("(")+cvtToStr(i)+string(")");
			m_traValuep = new AstArraySel(nodep->fileline(), m_traValuep->cloneTree(true),
						      i - nodep->lsb());

			subtypep->accept(*this);
			m_traValuep->deleteTree(); m_traValuep = NULL;
		    }
		    m_traShowname = oldShowname;
		    m_traValuep = oldValuep;
		}
	    }
	}
    }
    virtual void visit(AstPackArrayDType* nodep, AstNUser*) {
	if (m_traVscp) {
	    if (!v3Global.opt.traceStructs()) {
		// Everything downstream is packed, so deal with as one trace unit
		// This may not be the nicest for user presentation, but is a much faster way to trace
		addTraceDecl(VNumRange(), nodep->width());
	    } else {
		AstNodeDType* subtypep = nodep->subDTypep()->skipRefp();
		for (int i=nodep->lsb(); i<=nodep->msb(); ++i) {
		    string oldShowname = m_traShowname;
		    AstNode* oldValuep = m_traValuep;
		    {
			m_traShowname += string("(")+cvtToStr(i)+string(")");
			m_traValuep = new AstSel(nodep->fileline(), m_traValuep->cloneTree(true),
						 (i - nodep->lsb())*subtypep->width(),
						 subtypep->width());
			subtypep->accept(*this);
			m_traValuep->deleteTree(); m_traValuep = NULL;
		    }
		    m_traShowname = oldShowname;
		    m_traValuep = oldValuep;
		}
	    }
	}
    }
    virtual void visit(AstNodeClassDType* nodep, AstNUser*) {
	if (m_traVscp) {
	    if (nodep->packed() && !v3Global.opt.traceStructs()) {
		// Everything downstream is packed, so deal with as one trace unit
		// This may not be the nicest for user presentation, but is a much faster way to trace
		addTraceDecl(VNumRange(), nodep->width());
	    } else {
		if (!nodep->packed()) {
		    addIgnore("Unsupported: Unpacked struct/union");
		} else {
		    for (AstMemberDType* itemp = nodep->membersp(); itemp; itemp=itemp->nextp()->castMemberDType()) {
			AstNodeDType* subtypep = itemp->subDTypep()->skipRefp();
			string oldShowname = m_traShowname;
			AstNode* oldValuep = m_traValuep;
			{
			    m_traShowname += string(" ")+itemp->prettyName();
			    if (nodep->castStructDType()) {
				m_traValuep = new AstSel(nodep->fileline(), m_traValuep->cloneTree(true),
							 itemp->lsb(), subtypep->width());
				subtypep->accept(*this);
				m_traValuep->deleteTree(); m_traValuep = NULL;
			    } else { // Else union, replicate fields
				subtypep->accept(*this);
			    }
			}
			m_traShowname = oldShowname;
			m_traValuep = oldValuep;
		    }
		}
	    }
	}
    }
    virtual void visit(AstBasicDType* nodep, AstNUser*) {
	if (m_traVscp) {
	    if (nodep->keyword()==AstBasicDTypeKwd::STRING) {
		addIgnore("Unsupported: strings");
	    } else {
		addTraceDecl(VNumRange(), 0);
	    }
	}
    }
    virtual void visit(AstNodeDType* nodep, AstNUser*) {
	// Note more specific dtypes above
	if (!m_traVscp) return;
	addIgnore("Unsupported: data type");
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
	m_traVscp = NULL;
	m_traValuep = NULL;
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
    V3Global::dumpCheckGlobalTree("tracedecl.tree", 0, v3Global.opt.dumpTreeLevel(__FILE__) >= 3);
}
