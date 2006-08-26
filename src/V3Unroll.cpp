// $Id$
//*************************************************************************
// DESCRIPTION: Verilator: Add temporaries, such as for unroll nodes
//
// Code available from: http://www.veripool.com/verilator
//
// AUTHORS: Wilson Snyder with Paul Wasson, Duane Gabli
//
//*************************************************************************
//
// Copyright 2003-2006 by Wilson Snyder.  This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// General Public License or the Perl Artistic License.
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

#include "config.h"
#include <stdio.h>
#include <stdarg.h>
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
    bool		m_varModeCheck;		// Just checking RHS assignments
    bool		m_varModeReplace;	// Replacing varrefs
    bool		m_varAssignHit;		// Assign var hit
    bool		m_inBegin;		// Inside a begin/end loop
    bool		m_generate;		// Expand single generate For loop
    V3Double0		m_statLoops;		// Statistic tracking
    V3Double0		m_statIters;		// Statistic tracking

    //int debug() { return 9; }

    // VISITORS
    virtual void visit(AstModule* nodep, AstNUser*) {
	UINFO(4," MOD   "<<nodep<<endl);
	nodep->iterateChildren(*this);
    }

    bool cantUnroll(AstNodeFor* nodep, const char* reason) {
	if (m_generate) {
	    nodep->v3error("Unsupported: Can't unroll generate for; "<<reason);
	}
	UINFO(3,"   Can't Unroll: "<<reason<<" :"<<nodep<<endl);
	V3Stats::addStatSum(string("Unrolling gave up, ")+reason, 1);
	return false;
    }

    bool forUnrollCheck(AstNodeFor* nodep) {
	// Do only the body; ignore the loop variable as a dependency.
	// Return if we did the replacement or not
	if (m_varModeCheck || m_varModeReplace) return false;
	// See if we can make it simple enough to process
	if (nodep->initsp()) V3Const::constifyTree(nodep->initsp());  // May change what is under init, leave here
	V3Const::constifyTree(nodep->condp());
	if (nodep->assignsp()) V3Const::constifyTree(nodep->assignsp());

	AstAssign* initp = nodep->initsp()->castAssign();
	if (!initp) nodep->v3fatalSrc("no initial assignment");
	m_forVarp = initp->lhsp()->castVarRef()->varp();
	m_forVscp = initp->lhsp()->castVarRef()->varScopep();
	if (nodep->castGenFor() && !m_forVarp->isGenVar()) {
	    nodep->v3error("Non-genvar used in generate for: "<<m_forVarp->name()<<endl);
	}
	AstNodeBiop* condp = nodep->condp()->castNodeBiop();
	AstAssign* assignp = nodep->assignsp()->castAssign();
	AstNodeBiop* incInstrp = assignp->rhsp()->castNodeBiop();
	if (!assignp) nodep->v3fatalSrc("no increment assignment");
	UINFO(4, " FOR Check "<<nodep<<endl);
	if (m_forVscp) { UINFO(8, "   Loop Variable: "<<m_forVscp<<endl); }
	else	       { UINFO(8, "   Loop Variable: "<<m_forVarp<<endl); }
	if (debug()>=9) nodep->dumpTree(cout,"   for: ");
	//
	// Extract the constant loop bounds
	// To keep the IF levels low, we return as each test fails.
	if (m_generate) V3Const::constifyParam(initp->rhsp());
	AstConst* constInitp = initp->rhsp()->castConst();
	if (!constInitp) return cantUnroll(nodep, "non-constant initializer");
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
	if (m_generate) V3Const::constifyParam(preconstIncp);
	AstConst* constIncp = (subtract ? incInstrp->rhsp()->castConst()
			       : incInstrp->lhsp()->castConst());
	UINFO(8, "   Inc expr ok:  "<<constIncp<<endl);
	if (!constIncp) return cantUnroll(nodep, "non-constant increment");
	if (constIncp->isZero()) return cantUnroll(nodep, "zero increment");  // Or we could loop forever below...

        bool lt  = condp->castLt() || condp->castLtS();
        bool lte = condp->castLte() || condp->castLteS();
	bool gt  = condp->castGt() || condp->castGtS();
	bool gte = condp->castGte() || condp->castGteS();
	if (!lt && !lte && !gt && !gte)
	    return cantUnroll(nodep, "condition not <= or <");
	if (!condp->lhsp()->castVarRef())
	    return cantUnroll(nodep, "no variable on lhs of condition");
	if (condp->lhsp()->castVarRef()->varp() != m_forVarp
	    || condp->lhsp()->castVarRef()->varScopep() != m_forVscp)
	    return cantUnroll(nodep, "different variable in condition");
	if (m_generate) V3Const::constifyParam(condp->rhsp());
	AstConst* constStopp = condp->rhsp()->castConst();
	if (!constStopp) return cantUnroll(nodep, "non-constant final value");
	UINFO(8, "   Stop expr ok: "<<constStopp<<endl);
	//
	if (constInitp->width()>32 || constInitp->num().isFourState()
	    || constStopp->width()>32 || constStopp->num().isFourState()
	    || constIncp->width()>32  || constIncp->num().isFourState())
	    return cantUnroll(nodep, "init/final/increment too large or four state");
	vlsint32_t valInit = constInitp->num().asInt();  // Extract as unsigned, then make signed
	vlsint32_t valStop = constStopp->num().asInt();  // Extract as unsigned, then make signed
	if (lte) valStop++;  if (gte) valStop--;
	vlsint32_t valInc  = constIncp->num().asSInt();
	if (subtract) valInc = -valInc;
	UINFO(8,"     In Numbers: for (v="<<valInit<<"; v<"<<valStop<<"; v=v+"<<valInc<<")\n");
	//
	if (!m_generate) {
	    UINFO(8, "         ~Iters: "<<((valStop - valInit)/valInc)<<" c="<<v3Global.opt.unrollCount()<<endl);
	    if (((valStop - valInit)/valInc) > v3Global.opt.unrollCount())
		return cantUnroll(nodep, "too many iterations");

	    // Less then 10 statements in the body?
	    int bodySize = 0;
	    for (AstNode* bodp = nodep->bodysp(); bodp; bodp=bodp->nextp()) {
		bodySize++;
	    }
	    if (bodySize > v3Global.opt.unrollStmts())
		return cantUnroll(nodep, "too many statements");
	}
	//
	// Now, make sure there's no assignment to this variable in the loop
	m_varModeCheck = true;
	m_varAssignHit = false;
	nodep->bodysp()->iterateAndNext(*this);
	m_varModeCheck = false;
	if (m_varAssignHit) return cantUnroll(nodep, "genvar assigned *inside* loop");
	//
	// Finally, we can do it
	forUnroller(nodep, constInitp->num(),
		    condp, constStopp->num(),
		    incInstrp, constIncp->num()); nodep = NULL;
	return true;
    }

    void forUnroller(AstNodeFor* nodep, const V3Number& numInit,
		     AstNodeBiop* cmpInstrp, const V3Number& numStop,
		     AstNodeBiop* incInstrp, const V3Number& numInc) {
	UINFO(4, "   Unroll for var="<<numInit<<"; var<"<<numStop<<"; var+="<<numInc<<endl);
	AstNode* bodysp = nodep->bodysp();  // Maybe null if no body
	if (bodysp) bodysp->unlinkFrBackWithNext();

	AstNode* newbodysp = NULL;
	V3Number loopValue(nodep->fileline(), m_forVarp->width());  // May differ in size from numInitp
	loopValue.opAssign(numInit);

	m_statLoops++;
	if (bodysp) {
	    int times = 0;
	    while (1) {
		UINFO(8,"      Looping "<<loopValue<<endl);
		// if loopValue<valStop
		V3Number contin (nodep->fileline(), 1);
		cmpInstrp->numberOperate(contin, loopValue, numStop);
		if (contin.isEqZero()) {
		    break;  // Done with the loop
		} else {
		    AstNode* oneloopp = bodysp->cloneTree(true);

		    m_varValuep = new AstConst(nodep->fileline(), loopValue);
		    m_varModeReplace = true;
		    oneloopp->iterateAndNext(*this);
		    m_varModeReplace = false;

		    if (newbodysp) newbodysp->addNext(oneloopp);
		    else newbodysp = oneloopp;

		    m_statIters++;
		    if (++times > v3Global.opt.unrollCount()*3) {
			nodep->v3error("Loop unrolling took too long; probably this is an infinite loop.");
			break;
		    }

		    //loopValue += valInc
		    V3Number newnum(nodep->fileline(), m_forVarp->width());  // Can't increment in-place
		    incInstrp->numberOperate(newnum, loopValue, numInc);
		    loopValue.opAssign(newnum);
		}
	    }
	}

	// And, leave the iterator at the right final value.
	if (!nodep->castGenFor()) {
	    AstVarRef* newrefp = (m_forVscp
				  ? new AstVarRef(nodep->fileline(), m_forVscp, true)
				  : new AstVarRef(nodep->fileline(), m_forVarp, true));
	    AstAssign* finalAssignp = new AstAssign
		(nodep->fileline(),
		 newrefp,
		 new AstConst(nodep->fileline(), loopValue));
	    if (newbodysp) newbodysp->addNext(finalAssignp);
	    else newbodysp = finalAssignp;
	}

	// Replace the FOR()
	if (newbodysp) nodep->replaceWith(newbodysp);
	else nodep->unlinkFrBack();
	if (debug()>=9) newbodysp->dumpTree(cout,"  _new: ");
    }

    virtual void visit(AstNodeFor* nodep, AstNUser*) {
	if (!m_generate || m_varModeReplace) {
	    nodep->iterateChildren(*this);
	}
	if (m_varModeCheck || m_varModeReplace) {
	} else {
	    if (forUnrollCheck(nodep)) {
		nodep=NULL; // Did replacement
	    } else if (m_generate || nodep->castGenFor()) {
		nodep->v3error("For loop doesn't have genvar index, or is misformed");
	    } else {
		// So later optimizations don't need to deal with them,
		// convert leftover FOR's:
		//    FOR(init,cond,assign,body) -> init,WHILE(cond) { body, assign }
		AstNode* initsp = nodep->initsp(); if (initsp) initsp->unlinkFrBackWithNext();
		AstNode* condp = nodep->condp(); if (condp) condp->unlinkFrBackWithNext();
		AstNode* assignsp = nodep->assignsp(); if (assignsp) assignsp->unlinkFrBackWithNext();
		AstNode* bodysp = nodep->bodysp(); if (bodysp) bodysp->unlinkFrBackWithNext();
		bodysp = bodysp->addNext(assignsp);
		AstNode* newp = new AstWhile(nodep->fileline(),
					     condp,
					     bodysp);
		initsp = initsp->addNext(newp);
		newp = initsp;
		nodep->replaceWith(newp);
		nodep->deleteTree(); nodep=NULL;
	    }
	}
    }

    virtual void visit(AstBegin* nodep, AstNUser*) {
	// Naming inside loop body; must have been a generate for.
	// We need to only rename the 'upper' begin,
	// anything lower will be renamed "uppernewname.lowerbegin"
	bool lastBegin = m_inBegin;
	m_inBegin = true;
	nodep->iterateChildren(*this);
	m_inBegin = lastBegin;

	if (m_varModeReplace && !m_inBegin // above begin, not this one
	    ) {
	    // Rename it, as otherwise we may get a conflict
	    // V3Begin sees these DOTs and makes CellInlines for us.
	    string nname = (string)"genfor"+cvtToStr(m_varValuep->asInt())+"__DOT__"+nodep->name();
	    //UINFO(8,"   Rename begin "<<nname<<" "<<nodep<<endl);
	    nodep->name(nname);
	}
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
	    && nodep->varScopep() == m_forVscp) {
	    AstNode* newconstp = m_varValuep->cloneTree(false);
	    nodep->replaceWith(newconstp);
	}
    }

    //--------------------
    // Default: Just iterate
    virtual void visit(AstNode* nodep, AstNUser*) {
	nodep->iterateChildren(*this);
    }

public:
    // CONSTUCTORS
    UnrollVisitor(AstNode* nodep, bool generate) {
	m_forVarp = NULL;
	m_forVscp = NULL;
	m_varModeCheck = false;
	m_varModeReplace = false;
	m_inBegin = false;
	m_generate = generate;
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
    UnrollVisitor visitor (nodep, false);
}

void V3Unroll::unrollGen(AstNodeFor* nodep) {
    UINFO(2,__FUNCTION__<<": "<<endl);
    UnrollVisitor visitor (nodep, true);
}
