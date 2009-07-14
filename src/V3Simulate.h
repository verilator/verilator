// -*- C++ -*-
//*************************************************************************
// DESCRIPTION: Verilator: Simulate code to determine output values/variables
//
// Code available from: http://www.veripool.org/verilator
//
// AUTHORS: Wilson Snyder with Paul Wasson, Duane Gabli
//
//*************************************************************************
//
// Copyright 2003-2009 by Wilson Snyder.  This program is free software; you can
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
//
// void example_usage() {
//	SimulateVisitor simvis (false);
//	simvis.clear();
//	// Set all inputs to the constant
//	for (deque<AstVarScope*>::iterator it = m_inVarps.begin(); it!=m_inVarps.end(); ++it) {
//	    simvis.newNumber(invscp, #);
//	}
//	// Simulate
//	simvis.main(nodep);
//	// Read outputs
//	for (deque<AstVarScope*>::iterator it = m_outVarps.begin(); it!=m_outVarps.end(); ++it) {
//	    V3Number* outnump = simvis.fetchOutNumberNull(outvscp);
//
//*************************************************************************


#ifndef _V3SIMULATE_H_
#define _V3SIMULATE_H_ 1
#include "config_build.h"
#include "verilatedos.h"
#include "V3Error.h"
#include "V3Ast.h"

//============================================================================

//######################################################################
// Simulate class functions

class SimulateVisitor : public AstNVisitor {
    // Simulate a node tree, returning value of variables
    // Two major operating modes:
    //   Test the tree to see if it is conformant
    //   Given a set of input values, find the output values
    // Both are done in this same visitor to reduce risk; if a visitor
    // is missing, we will simply not apply the optimization, rather then bomb.

private:
    // NODE STATE
    // Cleared on each always/assignw
    AstUser1InUse	m_inuser1;
    AstUser3InUse	m_inuser3;
    AstUser4InUse	m_inuser4;

    // Checking:
    //  AstVarScope::user1()	-> VarUsage.  Set true to indicate tracking as lvalue/rvalue
    // Simulating:
    //  AstVarScope::user3()	-> V3Number*. Input value of variable or node (and output for non-delayed assignments)
    //  AstVarScope::user4()	-> V3Number*. Output value of variable (delayed assignments)

    enum VarUsage { VU_NONE=0, VU_LV=1, VU_RV=2, VU_LVDLY=4 };

    // STATE
    bool	m_checking;		///< Checking vs. simulation mode
    // Checking:
    const char*	m_whyNotOptimizable;	///< String explaining why not optimizable or NULL to optimize
    bool	m_anyAssignDly;		///< True if found a delayed assignment
    bool	m_anyAssignComb;	///< True if found a non-delayed assignment
    bool	m_inDlyAssign;		///< Under delayed assignment
    int		m_instrCount;		///< Number of nodes
    int		m_dataCount;		///< Bytes of data
    // Simulating:
    deque<V3Number*>	m_numFreeps;	///< List of all numbers free and not in use
    deque<V3Number*>	m_numAllps; 	///< List of all numbers free and in use

    // Note level 8&9 include debugging each simulation value
    static int debug() {
	static int level = -1;
	if (VL_UNLIKELY(level < 0)) level = v3Global.opt.debugSrcLevel(__FILE__);
	return level;
    }

    // Checking METHODS
public:
    /// Call other-this function on all new var references
    virtual void varRefCb(AstVarRef* nodep) {}

    void clearOptimizable(AstNode* nodep/*null ok*/, const char* why) {
	if (!m_whyNotOptimizable) {
	    if (debug()>=5) {
		UINFO(0,"Clear optimizable: "<<why);
		if (nodep) cout<<": "<<nodep;
		cout<<endl;
	    }
	    m_whyNotOptimizable = why;
	}
    }
    bool optimizable() const { return m_whyNotOptimizable==NULL; }
    bool isAssignDly() const { return m_anyAssignDly; }
    int instrCount() const { return m_instrCount; }
    int dataCount() const { return m_dataCount; }

    // Simulation METHODS
private:
    V3Number* allocNumber(AstNode* nodep, uint32_t value) {
	// Save time - kept a list of allocated but unused V3Numbers
	// It would be more efficient to do this by size, but the extra accounting
	// slows things down more than we gain.
	V3Number* nump;
	if (!m_numFreeps.empty()) {
	    //UINFO(7,"Num Reuse "<<nodep->width()<<endl);
	    nump = m_numFreeps.back(); m_numFreeps.pop_back();
	    nump->width(nodep->width());
	    nump->fileline(nodep->fileline());
	    nump->setLong(value);  // We do support more than 32 bit numbers, just valuep=0 in that case
	} else {
	    //UINFO(7,"Num New "<<nodep->width()<<endl);
	    nump = new V3Number (nodep->fileline(), nodep->width(), value);
	    m_numAllps.push_back(nump);
	}
	return nump;
    }
public:
    V3Number* newNumber(AstNode* nodep, uint32_t value=0) {
	// Set a constant value for this node
	if (!nodep->user3p()) {
	    V3Number* nump = allocNumber(nodep, value);
	    setNumber(nodep, nump);
	}
	return (fetchNumber(nodep));
    }
    V3Number* newOutNumber(AstNode* nodep, uint32_t value=0) {
	// Set a constant value for this node
	if (!nodep->user4p()) {
	    V3Number* nump = allocNumber(nodep, value);
	    setOutNumber(nodep, nump);
	}
	return (fetchOutNumber(nodep));
    }
    V3Number* fetchNumberNull(AstNode* nodep) {
	return ((V3Number*)nodep->user3p());
    }
    V3Number* fetchOutNumberNull(AstNode* nodep) {
	return ((V3Number*)nodep->user4p());
    }
    V3Number* fetchNumber(AstNode* nodep) {
	V3Number* nump = fetchNumberNull(nodep);
	if (!nump) nodep->v3fatalSrc("No value found for node.");
	return nump;
    }
    V3Number* fetchOutNumber(AstNode* nodep) {
	V3Number* nump = fetchOutNumberNull(nodep);
	if (!nump) nodep->v3fatalSrc("No value found for node.");
	return nump;
    }
private:
    void setNumber(AstNode* nodep, const V3Number* nump) {
	UINFO(9,"     set num "<<*nump<<" on "<<nodep<<endl);
	nodep->user3p((AstNUser*)nump);
    }
    void setOutNumber(AstNode* nodep, const V3Number* nump) {
	UINFO(9,"     set num "<<*nump<<" on "<<nodep<<endl);
	nodep->user4p((AstNUser*)nump);
    }

    void checkNodeInfo(AstNode* nodep) {
	m_instrCount += nodep->instrCount();
	m_dataCount += nodep->width();
	if (!nodep->isPredictOptimizable()) {
	    //UINFO(9,"     !predictopt "<<nodep<<endl);
	    clearOptimizable(nodep,"!predictOptimzable");
	}
    }

    // VISITORS
    virtual void visit(AstAlways* nodep, AstNUser*) {
	if (m_checking) checkNodeInfo(nodep);
	nodep->iterateChildren(*this);
    }
    virtual void visit(AstSenTree* nodep, AstNUser*) {
	// Sensitivities aren't inputs per se; we'll keep our tree under the same sens.
    }
    virtual void visit(AstVarRef* nodep, AstNUser*) {
	AstVarScope* vscp = nodep->varScopep();
	if (!vscp) nodep->v3fatalSrc("Not linked");
	if (m_checking) {
	    if (m_checking && !optimizable()) return;  // Accelerate
	    // We can't have non-delayed assignments with same value on LHS and RHS
	    // as we don't figure out variable ordering.
	    // Delayed is OK though, as we'll decode the next state separately.
	    if (nodep->varp()->arraysp()) clearOptimizable(nodep,"Array references");
	    if (nodep->lvalue()) {
		if (m_inDlyAssign) {
		    if (!(vscp->user1() & VU_LVDLY)) {
			vscp->user1( vscp->user1() | VU_LVDLY);
			varRefCb (nodep);
		    }
		} else { // nondly asn
		    if (!(vscp->user1() & VU_LV)) {
			if (vscp->user1() & VU_RV) clearOptimizable(nodep,"Var read & write");
			vscp->user1( vscp->user1() | VU_LV);
			varRefCb (nodep);
		    }
		}
	    } else {
		if (!(vscp->user1() & VU_RV)) {
		    if (vscp->user1() & VU_LV) clearOptimizable(nodep,"Var write & read");
		    vscp->user1( vscp->user1() | VU_RV);
		    varRefCb (nodep);
		}
	    }
	}
	else { // simulating
	    if (nodep->lvalue()) {
		nodep->v3fatalSrc("LHS varref should be handled in AstAssign visitor.");
	    } else {
		// Return simulation value
		V3Number* nump = fetchNumberNull(vscp);
		if (!nump) nodep->v3fatalSrc("Variable value should have been set before any visitor called.");
		setNumber(nodep, nump);
	    }
	}
    }
    virtual void visit(AstNodeIf* nodep, AstNUser*) {
	if (m_checking) {
	    checkNodeInfo(nodep);
	    nodep->iterateChildren(*this);
	} else {
	    nodep->condp()->iterateAndNext(*this);
	    if (fetchNumber(nodep->condp())->isNeqZero()) {
		nodep->ifsp()->iterateAndNext(*this);
	    } else {
		nodep->elsesp()->iterateAndNext(*this);
	    }
	}
    }
    virtual void visit(AstConst* nodep, AstNUser*) {
	if (m_checking) {
	    checkNodeInfo(nodep);
	} else {
	    setNumber(nodep, &(nodep->num()));
	}
    }
    virtual void visit(AstNodeUniop* nodep, AstNUser*) {
	if (m_checking) {
	    if (!optimizable()) return;  // Accelerate
	    checkNodeInfo(nodep);
	    nodep->iterateChildren(*this);
	} else {
	    nodep->iterateChildren(*this);
	    nodep->numberOperate(*newNumber(nodep), *fetchNumber(nodep->lhsp()));
	}
    }
    virtual void visit(AstNodeBiop* nodep, AstNUser*) {
	if (m_checking) {
	    if (!optimizable()) return;  // Accelerate
	    checkNodeInfo(nodep);
	    nodep->iterateChildren(*this);
	} else {
	    nodep->iterateChildren(*this);
	    nodep->numberOperate(*newNumber(nodep), *fetchNumber(nodep->lhsp()), *fetchNumber(nodep->rhsp()));
	}
    }
    virtual void visit(AstNodeTriop* nodep, AstNUser*) {
	if (m_checking) {
	    if (!optimizable()) return;  // Accelerate
	    checkNodeInfo(nodep);
	    nodep->iterateChildren(*this);
	} else {
	    nodep->iterateChildren(*this);
	    nodep->numberOperate(*newNumber(nodep),
				 *fetchNumber(nodep->lhsp()),
				 *fetchNumber(nodep->rhsp()),
				 *fetchNumber(nodep->thsp()));
	}
    }
    virtual void visit(AstNodeCond* nodep, AstNUser*) {
	// We could use above visit(AstNodeTriop), but it's slower even O(n^2) to evaluate
	// both sides when we really only need to evaluate one side.
	if (m_checking) {
	    if (!optimizable()) return;  // Accelerate
	    checkNodeInfo(nodep);
	    nodep->iterateChildren(*this);
	} else {
	    nodep->condp()->accept(*this);
	    if (fetchNumber(nodep->condp())->isNeqZero()) {
		nodep->expr1p()->accept(*this);
		newNumber(nodep)->opAssign(*fetchNumber(nodep->expr1p()));
	    } else {
		nodep->expr2p()->accept(*this);
		newNumber(nodep)->opAssign(*fetchNumber(nodep->expr2p()));
	    }
	}
    }
    virtual void visit(AstNodeAssign* nodep, AstNUser*) {
	if (m_checking) {
	    if (!optimizable()) return;  // Accelerate
	    if (nodep->castAssignDly()) {
		if (m_anyAssignComb) clearOptimizable(nodep, "Mix of dly/non dly assigns");
		m_anyAssignDly = true;
		m_inDlyAssign = true;
	    } else {
		if (m_anyAssignDly) clearOptimizable(nodep, "Mix of dly/non dly assigns");
		m_anyAssignComb = true;
	    }
	    nodep->iterateChildren(*this);
	}
	if (!nodep->lhsp()->castVarRef()) {
	    clearOptimizable(nodep, "LHS isn't simple variable");
	}
	else if (!m_checking) {
	    nodep->rhsp()->iterateAndNext(*this);
	    AstVarScope* vscp = nodep->lhsp()->castVarRef()->varScopep();
	    if (nodep->castAssignDly()) {
		// Don't do setNumber, as value isn't yet visible to following statements
		setOutNumber(vscp, fetchNumber(nodep->rhsp()));
	    } else {
		setNumber(vscp, fetchNumber(nodep->rhsp()));
		setOutNumber(vscp, fetchNumber(nodep->rhsp()));
	    }
	}
	m_inDlyAssign = false;
    }

    virtual void visit(AstComment*, AstNUser*) {}
    // default
    // These types are definately not reducable
    //   AstCoverInc, AstNodePli, AstArraySel, AstStop, AstFinish,
    //   AstRand, AstTime, AstUCFunc, AstCCall, AstCStmt, AstUCStmt
    // In theory, we could follow the loop, but might be slow
    //   AstFor, AstWhile
    virtual void visit(AstNode* nodep, AstNUser*) {
	if (m_checking) {
	    checkNodeInfo(nodep);
	    if (optimizable()) {
		// Hmm, what is this then?
		// In production code, we'll just not optimize.  It should be fixed though.
		clearOptimizable(nodep, "Unknown node type, perhaps missing visitor in SimulateVisitor");
#ifdef VL_DEBUG
		UINFO(0,"Unknown node type in SimulateVisitor: "<<nodep->prettyTypeName()<<endl);
#endif
	    }
	} else { // simulating
	    nodep->v3fatalSrc("Optimizable should have been cleared in check step, and never reach simulation.");
	}
    }

public:
    // CONSTRUCTORS
    SimulateVisitor(bool checking) {
	m_checking = checking;
	clear(); // We reuse this structure in the main loop, so put initializers inside clear()
    }
    void clear() {
	m_whyNotOptimizable = NULL;
	m_anyAssignComb = false;
	m_anyAssignDly = false;
	m_inDlyAssign = false;
	m_instrCount = 0;
	m_dataCount = 0;

	AstNode::user1ClearTree();	// user1p() used on entire tree
	AstNode::user3ClearTree();	// user3p() used on entire tree
	AstNode::user4ClearTree();	// user4p() used on entire tree

	// Move all allocated numbers to the free pool
	m_numFreeps = m_numAllps;
    }
    void main (AstNode* nodep) {
	nodep->accept(*this);
    }
    virtual ~SimulateVisitor() {
	for (deque<V3Number*>::iterator it = m_numAllps.begin(); it != m_numAllps.end(); ++it) {
	    delete (*it);
	}
	m_numFreeps.clear();
	m_numAllps.clear();
    }
};

#endif // Guard
