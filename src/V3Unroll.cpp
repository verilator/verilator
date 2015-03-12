// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Add temporaries, such as for unroll nodes
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
// V3Unroll's Transformations:
//	Note is called twice.  Once on modules for GenFor unrolling,
//	Again after V3Scope for normal for loop unrolling.
//
// Each module:
//	Look for "FOR" loops and unroll them if <= 32 loops.
//	(Eventually, a better way would be to simulate the entire loop; ala V3Table.)
//	Convert remaining FORs to WHILEs
//
//*************************************************************************

#include "config_build.h"
#include "verilatedos.h"
#include <cstdio>
#include <cstdarg>
#include <unistd.h>
#include <algorithm>

#include "V3Global.h"
#include "V3Unroll.h"
#include "V3Stats.h"
#include "V3Const.h"
#include "V3Ast.h"

//######################################################################
// Unroll state, as a visitor of each AstNode

class UnrollVisitor : public AstNVisitor {
private:
    // STATE
    AstVar*		m_forVarp;		// Iterator variable
    AstVarScope*	m_forVscp;		// Iterator variable scope (NULL for generate pass)
    AstConst*		m_varValuep;		// Current value of loop
    AstNode*		m_ignoreIncp;		// Increment node to ignore
    AstAttrOf*		m_attrp;		// Current attribute
    bool		m_varModeCheck;		// Just checking RHS assignments
    bool		m_varModeReplace;	// Replacing varrefs
    bool		m_varAssignHit;		// Assign var hit
    bool		m_generate;		// Expand single generate For loop
    string		m_beginName;		// What name to give begin iterations
    V3Double0		m_statLoops;		// Statistic tracking
    V3Double0		m_statIters;		// Statistic tracking

    // METHODS
    static int debug() {
	static int level = -1;
	if (VL_UNLIKELY(level < 0)) level = v3Global.opt.debugSrcLevel(__FILE__);
	return level;
    }

    // VISITORS
    bool cantUnroll(AstNode* nodep, const char* reason) {
	if (m_generate) {
	    nodep->v3error("Unsupported: Can't unroll generate for; "<<reason);
	}
	UINFO(3,"   Can't Unroll: "<<reason<<" :"<<nodep<<endl);
	//if (debug()>=9) nodep->dumpTree(cout,"-cant-");
	V3Stats::addStatSum(string("Unrolling gave up, ")+reason, 1);
	return false;
    }

    int unrollCount() {
	return m_generate ? v3Global.opt.unrollCount()*16
	    : v3Global.opt.unrollCount();
    }

    bool bodySizeOverRecurse(AstNode* nodep, int& bodySize, int bodyLimit) {
	if (!nodep) return false;
	bodySize++;
	// Exit once exceeds limits, rather than always total
	// so don't go O(n^2) when can't unroll
	if (bodySize > bodyLimit) return true;
	if (bodySizeOverRecurse(nodep->op1p(), bodySize, bodyLimit)) return true;
	if (bodySizeOverRecurse(nodep->op2p(), bodySize, bodyLimit)) return true;
	if (bodySizeOverRecurse(nodep->op3p(), bodySize, bodyLimit)) return true;
	if (bodySizeOverRecurse(nodep->op4p(), bodySize, bodyLimit)) return true;
	// Tail recurse.
	return bodySizeOverRecurse(nodep->nextp(), bodySize, bodyLimit);
    }

    bool forUnrollCheck(AstNode* nodep,
			AstNode* initp,	// Maybe under nodep (no nextp), or standalone (ignore nextp)
			AstNode* precondsp, AstNode* condp,
			AstNode* incp,		// Maybe under nodep or in bodysp
			AstNode* bodysp) {
	// To keep the IF levels low, we return as each test fails.
	UINFO(4, " FOR Check "<<nodep<<endl);
	if (initp)	UINFO(6, "    Init "<<initp<<endl);
	if (precondsp)	UINFO(6, "    Pcon "<<precondsp<<endl);
	if (condp)	UINFO(6, "    Cond "<<condp<<endl);
	if (incp)	UINFO(6, "    Inc  "<<incp<<endl);
	// Initial value check
	AstAssign* initAssp = initp->castAssign();
	if (!initAssp) return cantUnroll(nodep, "no initial assignment");
	if (initp->nextp() && initp->nextp()!=nodep) nodep->v3fatalSrc("initial assignment shouldn't be a list");
	if (!initAssp->lhsp()->castVarRef()) return cantUnroll(nodep, "no initial assignment to simple variable");
	m_forVarp = initAssp->lhsp()->castVarRef()->varp();
	m_forVscp = initAssp->lhsp()->castVarRef()->varScopep();
	if (nodep->castGenFor() && !m_forVarp->isGenVar()) {
	    nodep->v3error("Non-genvar used in generate for: "<<m_forVarp->prettyName()<<endl);
	}
	if (m_generate) V3Const::constifyParamsEdit(initAssp->rhsp());  // rhsp may change
	AstConst* constInitp = initAssp->rhsp()->castConst();
	if (!constInitp) return cantUnroll(nodep, "non-constant initializer");
	//
	// Condition check
	if (condp->nextp()) nodep->v3fatalSrc("conditional shouldn't be a list");
	//
	// Assignment of next value check
	AstAssign* incAssp = incp->castAssign();
	if (!incAssp) return cantUnroll(nodep, "no increment assignment");
	if (incAssp->nextp()) nodep->v3fatalSrc("increment shouldn't be a list");
	AstNodeBiop* incInstrp = incAssp->rhsp()->castNodeBiop();
	//
	if (m_forVscp) { UINFO(8, "   Loop Variable: "<<m_forVscp<<endl); }
	else	       { UINFO(8, "   Loop Variable: "<<m_forVarp<<endl); }
	if (debug()>=9) nodep->dumpTree(cout,"-   for: ");
	//
	// Extract the constant loop bounds
	bool subtract = incInstrp->castSub();
	{
	    if (!subtract && !incInstrp->castAdd()) return cantUnroll(nodep, "missing add/sub for incrementer");
	    AstVarRef* incVarrp   = (subtract ? incInstrp->lhsp()->castVarRef()
				     : incInstrp->rhsp()->castVarRef());
	    if (!incVarrp) return cantUnroll(nodep, "missing variable in incrementer");
	    if (incVarrp->varp() != m_forVarp
		|| incVarrp->varScopep() != m_forVscp) {
		return cantUnroll(nodep, "different variables in incrementer");
	    }
	}
	//
	// Adds have the # on the lhsp because V3Const pushes rhs consts over to the lhs
	// Subtracts have it on the rhs, because you write i=i-1; i=1-i is non-sensible.
	AstConst* preconstIncp = (subtract ? incInstrp->rhsp()->castConst()
				  : incInstrp->lhsp()->castConst());
	if (m_generate) preconstIncp = V3Const::constifyParamsEdit(preconstIncp)->castConst();
	AstConst* constIncp = (subtract ? incInstrp->rhsp()->castConst()
			       : incInstrp->lhsp()->castConst());
	UINFO(8, "   Inc expr ok:  "<<constIncp<<endl);
	if (!constIncp) return cantUnroll(nodep, "non-constant increment");
	if (constIncp->isZero()) return cantUnroll(nodep, "zero increment");  // Or we could loop forever below...

        bool lt  = condp->castLt()  || condp->castLtS();
        bool lte = condp->castLte() || condp->castLteS();
	bool gt  = condp->castGt()  || condp->castGtS();
	bool gte = condp->castGte() || condp->castGteS();
	if (!lt && !lte && !gt && !gte)
	    return cantUnroll(nodep, "condition not <=, <, >= or >");
	AstNodeBiop* cmpInstrp = condp->castNodeBiop();
	bool cmpVarLhs;
	if (cmpInstrp->lhsp()->castVarRef()
	    && cmpInstrp->lhsp()->castVarRef()->varp() == m_forVarp
	    && cmpInstrp->lhsp()->castVarRef()->varScopep() == m_forVscp) {
	    cmpVarLhs = true;
	} else if (cmpInstrp->rhsp()->castVarRef()
		   && cmpInstrp->rhsp()->castVarRef()->varp() == m_forVarp
		   && cmpInstrp->rhsp()->castVarRef()->varScopep() == m_forVscp) {
	    cmpVarLhs = false;
	} else if (!cmpInstrp->rhsp()->castVarRef()) {
	    return cantUnroll(nodep, "no variable on rhs of condition");
	} else {
	    return cantUnroll(nodep, "different variable in condition");
	}

	if (m_generate) V3Const::constifyParamsEdit(cmpVarLhs ? cmpInstrp->rhsp()
						    : cmpInstrp->lhsp());  // rhsp/lhsp may change
	AstConst* constStopp = (cmpVarLhs ? cmpInstrp->rhsp()->castConst()
				: cmpInstrp->lhsp()->castConst());
	if (!constStopp) return cantUnroll(nodep, "non-constant final value");
	UINFO(8, "   Stop expr ok: "<<constStopp<<endl);
	//
	if (constInitp->width()>32 || constInitp->num().isFourState()
	    || constStopp->width()>32 || constStopp->num().isFourState()
	    || constIncp->width()>32  || constIncp->num().isFourState())
	    return cantUnroll(nodep, "init/final/increment too large or four state");
	vlsint32_t valInit = constInitp->num().toSInt();
	vlsint32_t valStop = constStopp->num().toSInt();
	if (gte) valStop++;  if (lte) valStop--;   // 23 >= a, handle as if 24 > a
	vlsint32_t valInc  = constIncp->num().toSInt();
	if (subtract) valInc = -valInc;
	UINFO(8,"     In Numbers: for (v="<<valInit<<"; v<"<<valStop<<"; v=v+"<<valInc<<")\n");
	//
	if (!m_generate) {
	    int loops = ((valStop - valInit)/valInc);
	    if (loops < 0) { loops += (1ULL<<constStopp->width()); } // Will roll around
	    UINFO(8, "         ~Iters: "<<loops<<" c="<<unrollCount()<<endl);
	    if (loops > unrollCount())
		return cantUnroll(nodep, "too many iterations");

	    // Less than 10 statements in the body?
	    int bodySize = 0;
	    int bodyLimit = v3Global.opt.unrollStmts();
	    if (loops>0) bodyLimit = v3Global.opt.unrollStmts() / loops;
	    if (bodySizeOverRecurse(precondsp, bodySize/*ref*/, bodyLimit)
		|| bodySizeOverRecurse(bodysp, bodySize/*ref*/, bodyLimit)
		|| bodySizeOverRecurse(incp, bodySize/*ref*/, bodyLimit)) {
		return cantUnroll(nodep, "too many statements");
	    }
	}
	//
	// Now, make sure there's no assignment to this variable in the loop
	m_varModeCheck = true;
	m_varAssignHit = false;
	m_ignoreIncp = incp;
	precondsp->iterateAndNext(*this);
	bodysp->iterateAndNext(*this);
	incp->iterateAndNext(*this);
	m_varModeCheck = false;
	m_ignoreIncp = NULL;
	if (m_varAssignHit) return cantUnroll(nodep, "genvar assigned *inside* loop");
	//
	// Finally, we can do it
	forUnroller(nodep, initp, precondsp, incp, bodysp,
		    constInitp->num(),
		    cmpInstrp, constStopp->num(), cmpVarLhs,
		    incInstrp, constIncp->num()); nodep = NULL;
	// Cleanup
	return true;
    }

    void forUnroller(AstNode* nodep,
		     AstNode* initp,
		     AstNode* precondsp,
		     AstNode* incp, AstNode* bodysp,
		     const V3Number& numInit,
		     AstNodeBiop* cmpInstrp, const V3Number& numStop, bool cmpVarLhs,
		     AstNodeBiop* incInstrp, const V3Number& numInc) {
	UINFO(4, "   Unroll for var="<<numInit<<"; var<"<<numStop<<"; var+="<<numInc<<endl);
	UINFO(6, "    cmpI "<<cmpInstrp<<endl);
	UINFO(6, "    IncI "<<incInstrp<<endl);
	AstNode* stmtsp = NULL;
	if (initp) {
	    initp->unlinkFrBack();	// Always a single statement; nextp() may be nodep
	    // Don't add to list, we do it once, and setting loop index isn't needed as we're constant propagating it
	}
	if (precondsp) {
	    precondsp->unlinkFrBackWithNext();
	    // cppcheck-suppress nullPointer  // addNextNull deals with it
	    stmtsp = stmtsp->addNextNull(precondsp);
	}
	if (bodysp) {
	    bodysp->unlinkFrBackWithNext();
	    // cppcheck-suppress nullPointer  // addNextNull deals with it
	    stmtsp = stmtsp->addNextNull(bodysp);  // Maybe null if no body
	}
	if (incp && !nodep->castGenFor()) {  // Generates don't need to increment loop index
	    incp->unlinkFrBackWithNext();
	    // cppcheck-suppress nullPointer  // addNextNull deals with it
	    stmtsp = stmtsp->addNextNull(incp);  // Maybe null if no body
	}
	// Mark variable to disable some later warnings
	m_forVarp->usedLoopIdx(true);

	// If it's a While, then incp is already part of bodysp.
	V3Number loopValue(nodep->fileline(), m_forVarp->width());  // May differ in size from numInitp
	loopValue.opAssign(numInit);

	AstNode* newbodysp = NULL;
	++m_statLoops;
	if (stmtsp) {
	    int times = 0;
	    while (1) {
		UINFO(8,"      Looping "<<loopValue<<endl);
		// if loopValue<valStop
		V3Number contin (nodep->fileline(), 1);
		if (cmpVarLhs) {
		    cmpInstrp->numberOperate(contin, loopValue, numStop);
		} else {
		    cmpInstrp->numberOperate(contin, numStop, loopValue);
		}
		if (contin.isEqZero()) {
		    break;  // Done with the loop
		} else {
		    // Replace iterator values with constant.
		    AstNode* oneloopp = stmtsp->cloneTree(true);

		    m_varValuep = new AstConst(nodep->fileline(), loopValue);

		    // Iteration requires a back, so put under temporary node
		    if (oneloopp) {
			AstBegin* tempp = new AstBegin(oneloopp->fileline(),"[EditWrapper]",oneloopp);
			m_varModeReplace = true;
			tempp->stmtsp()->iterateAndNext(*this);
			m_varModeReplace = false;
			oneloopp = tempp->stmtsp()->unlinkFrBackWithNext(); tempp->deleteTree(); tempp=NULL;
		    }
		    if (m_generate) {
			string index = AstNode::encodeNumber(m_varValuep->toSInt());
			string nname = m_beginName + "__BRA__" + index + "__KET__";
			oneloopp = new AstBegin(oneloopp->fileline(),nname,oneloopp,true);
		    }

		    if (newbodysp) newbodysp->addNext(oneloopp);
		    else newbodysp = oneloopp;

		    ++m_statIters;
		    if (++times > unrollCount()*3) {
			nodep->v3error("Loop unrolling took too long; probably this is an infinite loop, or set --unroll-count above "<<unrollCount());
			break;
		    }

		    //loopValue += valInc
		    V3Number newnum(nodep->fileline(), m_forVarp->width());  // Can't increment in-place
		    incInstrp->numberOperate(newnum, loopValue, numInc);
		    loopValue.opAssign(newnum);

		    pushDeletep(m_varValuep); m_varValuep=NULL;
		}
	    }
	}
	// Replace the FOR()
	if (newbodysp) nodep->replaceWith(newbodysp);
	else nodep->unlinkFrBack();
	if (bodysp) { pushDeletep(bodysp); bodysp=NULL; }
	if (precondsp) { pushDeletep(precondsp); precondsp=NULL; }
	if (initp) { pushDeletep(initp); initp=NULL; }
	if (incp && !incp->backp()) { pushDeletep(incp); incp=NULL; }
	if (debug()>=9) newbodysp->dumpTree(cout,"-  _new: ");
    }

    virtual void visit(AstWhile* nodep, AstNUser*) {
	nodep->iterateChildren(*this);
	if (m_varModeCheck || m_varModeReplace) {
	} else {
	    // Constify before unroll call, as it may change what is underneath.
	    if (nodep->precondsp()) V3Const::constifyEdit(nodep->precondsp());  // precondsp may change
	    if (nodep->condp()) V3Const::constifyEdit(nodep->condp()); //condp may change
	    // Grab initial value
	    AstNode* initp = NULL;  // Should be statement before the while.
	    if (nodep->backp()->nextp() == nodep) initp=nodep->backp();
	    if (initp) { V3Const::constifyEdit(initp); initp=NULL; }
	    if (nodep->backp()->nextp() == nodep) initp=nodep->backp();
	    // Grab assignment
	    AstNode* incp = NULL;  // Should be last statement
	    if (nodep->incsp()) V3Const::constifyEdit(nodep->incsp());
	    if (nodep->incsp()) incp = nodep->incsp();
	    else {
		for (incp = nodep->bodysp(); incp && incp->nextp(); incp = incp->nextp()) {}
		if (incp) { V3Const::constifyEdit(incp); incp=NULL; }
		for (incp = nodep->bodysp(); incp && incp->nextp(); incp = incp->nextp()) {}  // Again, as may have changed
	    }
	    // And check it
	    if (forUnrollCheck(nodep, initp,
			       nodep->precondsp(), nodep->condp(),
			       incp, nodep->bodysp())) {
		pushDeletep(nodep); nodep=NULL; // Did replacement
	    }
	}
    }
    virtual void visit(AstGenFor* nodep, AstNUser*) {
	if (!m_generate || m_varModeReplace) {
	    nodep->iterateChildren(*this);
	}  // else V3Param will recursively call each for loop to be unrolled for us
	if (m_varModeCheck || m_varModeReplace) {
	} else {
	    // Constify before unroll call, as it may change what is underneath.
	    if (nodep->initsp()) V3Const::constifyEdit(nodep->initsp());  // initsp may change
	    if (nodep->condp()) V3Const::constifyEdit(nodep->condp());  // condp may change
	    if (nodep->incsp()) V3Const::constifyEdit(nodep->incsp());  // incsp may change
	    if (nodep->condp()->isZero()) {
		// We don't need to do any loops.  Remove the GenFor,
		// Genvar's don't care about any initial assignments.
		//
		// Note normal For's can't do exactly this deletion, as
		// we'd need to initialize the variable to the initial
		// condition, but they'll become while's which can be
		// deleted by V3Const.
		nodep->unlinkFrBack()->deleteTree(); nodep=NULL;
	    } else if (forUnrollCheck(nodep, nodep->initsp(),
				      NULL, nodep->condp(),
				      nodep->incsp(), nodep->bodysp())) {
		pushDeletep(nodep); nodep=NULL; // Did replacement
	    } else {
		nodep->v3error("For loop doesn't have genvar index, or is malformed");
	    }
	}
    }
    virtual void visit(AstNodeFor* nodep, AstNUser*) {
	if (m_generate) {  // Ignore for's when expanding genfor's
	    nodep->iterateChildren(*this);
	} else {
	    nodep->v3error("V3Begin should have removed standard FORs");
	}
    }
    virtual void visit(AstAttrOf* nodep, AstNUser*) {
	AstAttrOf* oldAttr = m_attrp;
	m_attrp = nodep;
	nodep->iterateChildren(*this);
	m_attrp = oldAttr;
    }

    virtual void visit(AstVarRef* nodep, AstNUser*) {
	if (m_varModeCheck
	    && nodep->varp() == m_forVarp
	    && nodep->varScopep() == m_forVscp
	    && nodep->lvalue()) {
	    UINFO(8,"   Itervar assigned to: "<<nodep<<endl);
	    m_varAssignHit = true;
	}
	if (m_varModeReplace
	    && nodep->varp() == m_forVarp
	    && nodep->varScopep() == m_forVscp
	    && !nodep->lvalue()
	    && !m_attrp) {  // Most likely under a select
	    AstNode* newconstp = m_varValuep->cloneTree(false);
	    nodep->replaceWith(newconstp);
	    pushDeletep(nodep);
	}
    }

    //--------------------
    // Default: Just iterate
    virtual void visit(AstNode* nodep, AstNUser*) {
	if (m_varModeCheck && nodep == m_ignoreIncp) {
	    // Ignore subtree that is the increment
	} else {
	    nodep->iterateChildren(*this);
	}
    }

public:
    // CONSTUCTORS
    UnrollVisitor(AstNode* nodep, bool generate, string beginName) {
	m_forVarp = NULL;
	m_forVscp = NULL;
	m_ignoreIncp = NULL;
	m_varModeCheck = false;
	m_varModeReplace = false;
	m_generate = generate;
	m_beginName = beginName;
	m_attrp = NULL;
	//
	nodep->accept(*this);
    }
    virtual ~UnrollVisitor() {
	V3Stats::addStat("Optimizations, Unrolled Loops", m_statLoops);
	V3Stats::addStat("Optimizations, Unrolled Iterations", m_statIters);
    }
};

//######################################################################
// Unroll class functions

void V3Unroll::unrollAll(AstNetlist* nodep) {
    UINFO(2,__FUNCTION__<<": "<<endl);
    UnrollVisitor visitor (nodep, false, "");
    V3Global::dumpCheckGlobalTree("unroll.tree", 0, v3Global.opt.dumpTreeLevel(__FILE__) >= 3);
}

void V3Unroll::unrollGen(AstNodeFor* nodep, string beginName) {
    UINFO(2,__FUNCTION__<<": "<<endl);
    UnrollVisitor visitor (nodep, true, beginName);
}
