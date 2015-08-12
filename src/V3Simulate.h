// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Simulate code to determine output values/variables
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
//
// void example_usage() {
//	SimulateVisitor simvis (false, false);
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
#include "V3Width.h"
#include "V3Task.h"

#include <deque>

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
    AstUser2InUse	m_inuser2;
    AstUser3InUse	m_inuser3;

    // Checking:
    //  AstVar(Scope)::user1()	-> VarUsage.  Set true to indicate tracking as lvalue/rvalue
    // Simulating:
    //  AstVar(Scope)::user3()	-> V3Number*. Input value of variable or node (and output for non-delayed assignments)
    //  AstVar(Scope)::user2()	-> V3Number*. Output value of variable (delayed assignments)

    enum VarUsage { VU_NONE=0, VU_LV=1, VU_RV=2, VU_LVDLY=4 };

    // STATE
    // Major mode
    bool	m_checkOnly;		///< Checking only (no simulation) mode
    bool	m_scoped;		///< Running with AstVarScopes instead of AstVars
    bool	m_params;		///< Doing parameter propagation
    // Checking:
    string	m_whyNotOptimizable;	///< String explaining why not optimizable or NULL to optimize
    AstNode*	m_whyNotNodep;		///< First node not optimizable
    bool	m_anyAssignDly;		///< True if found a delayed assignment
    bool	m_anyAssignComb;	///< True if found a non-delayed assignment
    bool	m_inDlyAssign;		///< Under delayed assignment
    int		m_instrCount;		///< Number of nodes
    int		m_dataCount;		///< Bytes of data
    AstJumpGo*	m_jumpp;		///< Jump label we're branching from
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
    /// Call other-this function on all new *non-constant* var references
    virtual void varRefCb(AstVarRef* nodep) {}

    void clearOptimizable(AstNode* nodep/*null ok*/, const string& why) {
	//  Something bad found.  optimizable() will return false,
	//  and fetchNumber should not be called or it may assert.
	if (!m_whyNotNodep) {
	    m_whyNotNodep = nodep;
	    if (debug()>=5) {
		UINFO(0,"Clear optimizable: "<<why);
		if (nodep) cout<<": "<<nodep;
		cout<<endl;
	    }
	    m_whyNotOptimizable = why;
	}
    }
    inline bool optimizable() const { return m_whyNotNodep==NULL; }
    string whyNotMessage() const { return m_whyNotOptimizable; }
    AstNode* whyNotNodep() const { return m_whyNotNodep; }

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
	nump->isDouble(nodep->isDouble());
	return nump;
    }
public:
    V3Number* newNumber(AstNode* nodep, uint32_t value=0) {
	// Set a constant value for this node
	if (!nodep->user3p()) {
	    V3Number* nump = allocNumber(nodep, value);
	    setNumber(nodep, nump);
	    return nump;
	} else {
	    return (fetchNumber(nodep));
	}
    }
    V3Number* newOutNumber(AstNode* nodep, uint32_t value=0) {
	// Set a constant value for this node
	if (!nodep->user2p()) {
	    V3Number* nump = allocNumber(nodep, value);
	    setOutNumber(nodep, nump);
	    return nump;
	} else {
	    return (fetchOutNumber(nodep));
	}
    }
    V3Number* fetchNumberNull(AstNode* nodep) {
	return ((V3Number*)nodep->user3p());
    }
    V3Number* fetchOutNumberNull(AstNode* nodep) {
	return ((V3Number*)nodep->user2p());
    }
    V3Number* fetchNumber(AstNode* nodep) {
	V3Number* nump = fetchNumberNull(nodep);
	if (!nump) nodep->v3fatalSrc("No value found for node.");
	//UINFO(9,"     fetch num "<<*nump<<" on "<<nodep<<endl);
	return nump;
    }
    V3Number* fetchOutNumber(AstNode* nodep) {
	V3Number* nump = fetchOutNumberNull(nodep);
	if (!nump) nodep->v3fatalSrc("No value found for node.");
	return nump;
    }
private:
    inline void setNumber(AstNode* nodep, const V3Number* nump) {
	UINFO(9,"     set num "<<*nump<<" on "<<nodep<<endl);
	nodep->user3p((AstNUser*)nump);
    }
    inline void setOutNumber(AstNode* nodep, const V3Number* nump) {
	UINFO(9,"     set num "<<*nump<<" on "<<nodep<<endl);
	nodep->user2p((AstNUser*)nump);
    }

    void checkNodeInfo(AstNode* nodep) {
	if (m_checkOnly) {
	    m_instrCount += nodep->instrCount();
	    m_dataCount += nodep->width();
	}
	if (!nodep->isPredictOptimizable()) {
	    //UINFO(9,"     !predictopt "<<nodep<<endl);
	    clearOptimizable(nodep,"Isn't predictable");
	}
    }

    void badNodeType(AstNode* nodep) {
	// Call for default node types, or other node types we don't know how to handle
	checkNodeInfo(nodep);
	if (optimizable()) {
	    // Hmm, what is this then?
	    // In production code, we'll just not optimize.  It should be fixed though.
	    clearOptimizable(nodep, "Unknown node type, perhaps missing visitor in SimulateVisitor");
#ifdef VL_DEBUG
	    UINFO(0,"Unknown node type in SimulateVisitor: "<<nodep->prettyTypeName()<<endl);
#endif
	}
    }

    AstNode* varOrScope(AstVarRef* nodep) {
	AstNode* vscp;
	if (m_scoped) vscp = nodep->varScopep();
	else vscp = nodep->varp();
	if (!vscp) nodep->v3fatalSrc("Not linked");
	return vscp;
    }
    int unrollCount() {
	return m_params ? v3Global.opt.unrollCount()*16
	    : v3Global.opt.unrollCount();
    }
    bool jumpingOver(AstNode* nodep) {
	// True to jump over this node - all visitors must call this up front
	return (m_jumpp && m_jumpp->labelp()!=nodep);
    }
    void assignOutNumber(AstNodeAssign* nodep, AstNode* vscp, const V3Number* nump) {
	// Don't do setNumber, as value isn't yet visible to following statements
	if (nodep->castAssignDly()) {
	    // Don't do setNumber, as value isn't yet visible to following statements
	    newOutNumber(vscp)->opAssign(*nump);
	} else {
	    newNumber(vscp)->opAssign(*nump);
	    newOutNumber(vscp)->opAssign(*nump);
	}
    }

    // VISITORS
    virtual void visit(AstAlways* nodep, AstNUser*) {
	if (jumpingOver(nodep)) return;
	checkNodeInfo(nodep);
	nodep->iterateChildren(*this);
    }
    virtual void visit(AstSenTree* nodep, AstNUser*) {
	// Sensitivities aren't inputs per se; we'll keep our tree under the same sens.
    }
    virtual void visit(AstVarRef* nodep, AstNUser*) {
	if (jumpingOver(nodep)) return;
	if (!optimizable()) return;  // Accelerate
	AstNode* vscp = varOrScope(nodep);

	// We can't have non-delayed assignments with same value on LHS and RHS
	// as we don't figure out variable ordering.
	// Delayed is OK though, as we'll decode the next state separately.
	if (!nodep->varp()->dtypeSkipRefp()->castBasicDType()
            && !nodep->varp()->dtypeSkipRefp()->castPackArrayDType())
            clearOptimizable(nodep,"Array references/not basic");
	if (nodep->lvalue()) {
	    if (m_inDlyAssign) {
		if (!(vscp->user1() & VU_LVDLY)) {
		    vscp->user1( vscp->user1() | VU_LVDLY);
		    if (m_checkOnly) varRefCb (nodep);
		}
	    } else { // nondly asn
		if (!(vscp->user1() & VU_LV)) {
		    if (!m_params && (vscp->user1() & VU_RV)) clearOptimizable(nodep,"Var read & write");
		    vscp->user1( vscp->user1() | VU_LV);
		    if (m_checkOnly) varRefCb (nodep);
		}
	    }
	} else {
	    if (!(vscp->user1() & VU_RV)) {
		if (!m_params && (vscp->user1() & VU_LV)) clearOptimizable(nodep,"Var write & read");
		vscp->user1( vscp->user1() | VU_RV);
		bool isConst = nodep->varp()->isParam();
		AstConst* constp = (isConst ? nodep->varp()->valuep()->castConst() : NULL);
		if (isConst && constp) { // Propagate PARAM constants for constant function analysis
		    if (!m_checkOnly && optimizable()) {
			newNumber(vscp)->opAssign(constp->num());
		    }
		} else {
		    if (m_checkOnly) varRefCb (nodep);
		}
	    }
	}
	if (!m_checkOnly && optimizable()) { // simulating
	    if (nodep->lvalue()) {
		nodep->v3fatalSrc("LHS varref should be handled in AstAssign visitor.");
	    } else {
		// Return simulation value - copy by reference instead of value for speed
		V3Number* nump = fetchNumberNull(vscp);
		if (!nump) {
		    if (m_params) {
			clearOptimizable(nodep,"Language violation: reference to non-function-local variable");
		    } else {
			nodep->v3fatalSrc("Variable value should have been set before any visitor called.");
		    }
		    nump = allocNumber(nodep, 0);  // Any value; just so recover from error
		}
		setNumber(nodep, nump);
	    }
	}
    }
    virtual void visit(AstVarXRef* nodep, AstNUser*) {
	if (jumpingOver(nodep)) return;
	if (m_scoped) {  badNodeType(nodep); return; }
	else { clearOptimizable(nodep,"Language violation: Dotted hierarchical references not allowed in constant functions"); }
    }
    virtual void visit(AstNodeFTask* nodep, AstNUser*) {
	if (jumpingOver(nodep)) return;
	if (!m_params) { badNodeType(nodep); return; }
	if (nodep->dpiImport()) { clearOptimizable(nodep,"DPI import functions aren't simulatable"); }
	checkNodeInfo(nodep);
	nodep->iterateChildren(*this);
    }
    virtual void visit(AstNodeIf* nodep, AstNUser*) {
	if (jumpingOver(nodep)) return;
	UINFO(5,"   IF "<<nodep<<endl);
	checkNodeInfo(nodep);
	if (m_checkOnly) {
	    nodep->iterateChildren(*this);
	} else {
	    nodep->condp()->iterateAndNext(*this);
	    if (optimizable()) {
		if (fetchNumber(nodep->condp())->isNeqZero()) {
		    nodep->ifsp()->iterateAndNext(*this);
		} else {
		    nodep->elsesp()->iterateAndNext(*this);
		}
	    }
	}
    }
    virtual void visit(AstConst* nodep, AstNUser*) {
	checkNodeInfo(nodep);
	if (!m_checkOnly && optimizable()) {
	    setNumber(nodep, &(nodep->num()));
	}
    }
    virtual void visit(AstNodeUniop* nodep, AstNUser*) {
	if (!optimizable()) return;  // Accelerate
	checkNodeInfo(nodep);
	nodep->iterateChildren(*this);
	if (!m_checkOnly && optimizable()) {
	    nodep->numberOperate(*newNumber(nodep), *fetchNumber(nodep->lhsp()));
	}
    }
    virtual void visit(AstNodeBiop* nodep, AstNUser*) {
	if (!optimizable()) return;  // Accelerate
	checkNodeInfo(nodep);
	nodep->iterateChildren(*this);
	if (!m_checkOnly && optimizable()) {
	    nodep->numberOperate(*newNumber(nodep), *fetchNumber(nodep->lhsp()), *fetchNumber(nodep->rhsp()));
	}
    }
    virtual void visit(AstNodeTriop* nodep, AstNUser*) {
	if (!optimizable()) return;  // Accelerate
	checkNodeInfo(nodep);
	nodep->iterateChildren(*this);
	if (!m_checkOnly && optimizable()) {
	    nodep->numberOperate(*newNumber(nodep),
				 *fetchNumber(nodep->lhsp()),
				 *fetchNumber(nodep->rhsp()),
				 *fetchNumber(nodep->thsp()));
	}
    }
    virtual void visit(AstLogAnd* nodep, AstNUser*) {
	// Need to short circuit
	if (!optimizable()) return;  // Accelerate
	checkNodeInfo(nodep);
	if (m_checkOnly) {
	    nodep->iterateChildren(*this);
	} else {
	    nodep->lhsp()->accept(*this);
	    if (fetchNumber(nodep->lhsp())->isNeqZero()) {
		nodep->rhsp()->accept(*this);
		newNumber(nodep)->opAssign(*fetchNumber(nodep->rhsp()));
	    } else {
		newNumber(nodep)->opAssign(*fetchNumber(nodep->lhsp()));  // a zero
	    }
	}
    }
    virtual void visit(AstLogOr* nodep, AstNUser*) {
	// Need to short circuit
	if (!optimizable()) return;  // Accelerate
	checkNodeInfo(nodep);
	if (m_checkOnly) {
	    nodep->iterateChildren(*this);
	} else {
	    nodep->lhsp()->accept(*this);
	    if (fetchNumber(nodep->lhsp())->isNeqZero()) {
		newNumber(nodep)->opAssign(*fetchNumber(nodep->lhsp()));  // a one
	    } else {
		nodep->rhsp()->accept(*this);
		newNumber(nodep)->opAssign(*fetchNumber(nodep->rhsp()));
	    }
	}
    }
    virtual void visit(AstLogIf* nodep, AstNUser*) {
	// Need to short circuit, same as (!A || B)
	if (!optimizable()) return;  // Accelerate
	checkNodeInfo(nodep);
	if (m_checkOnly) {
	    nodep->iterateChildren(*this);
	} else {
	    nodep->lhsp()->accept(*this);
	    if (fetchNumber(nodep->lhsp())->isEqZero()) {
		newNumber(nodep)->opAssign(V3Number(nodep->fileline(), 1, 1));  // a one
	    } else {
		nodep->rhsp()->accept(*this);
		newNumber(nodep)->opAssign(*fetchNumber(nodep->rhsp()));
	    }
	}
    }
    virtual void visit(AstNodeCond* nodep, AstNUser*) {
	// We could use above visit(AstNodeTriop), but need to do short circuiting.
	// It's also slower even O(n^2) to evaluate both sides when we really only need to evaluate one side.
	if (!optimizable()) return;  // Accelerate
	checkNodeInfo(nodep);
	if (m_checkOnly) {
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
	if (jumpingOver(nodep)) return;
	if (!optimizable()) return;  // Accelerate
	if (nodep->castAssignDly()) {
	    if (m_anyAssignComb) clearOptimizable(nodep, "Mix of dly/non-dly assigns");
	    m_anyAssignDly = true;
	    m_inDlyAssign = true;
	} else {
	    if (m_anyAssignDly) clearOptimizable(nodep, "Mix of dly/non-dly assigns");
	    m_anyAssignComb = true;
	}
	if (AstSel* selp = nodep->lhsp()->castSel()) {
	    if (!m_params) { clearOptimizable(nodep, "LHS has select"); return; }
	    checkNodeInfo(selp);
	    AstVarRef* varrefp = selp->fromp()->castVarRef();
	    if (!varrefp) {
		clearOptimizable(nodep, "Select LHS isn't simple variable");
		return;
	    }
	    if (m_checkOnly) {
		nodep->iterateChildren(*this);
	    } else {
		selp->lsbp()->iterateAndNext(*this);
		nodep->rhsp()->iterateAndNext(*this);
		if (optimizable()) {
		    AstNode* vscp = varOrScope(varrefp);
		    if (optimizable()) {
			V3Number outnum (nodep->fileline(), varrefp->varp()->widthMin());
			if (V3Number* outnump = fetchOutNumberNull(vscp)) {
			    outnum = *outnump;
			} else if (V3Number* outnump = fetchNumberNull(vscp)) {
			    outnum = *outnump;
			} else {  // Assignment to unassigned variable, all bits are X or 0
			    if (varrefp->varp()->basicp() && varrefp->varp()->basicp()->isZeroInit()) {
				outnum.setAllBits0();
			    } else {
				outnum.setAllBitsX();
			    }
			}
			outnum.opSelInto(*fetchNumber(nodep->rhsp()),
					 *fetchNumber(selp->lsbp()),
					 selp->widthConst());
			assignOutNumber(nodep, vscp, &outnum);
		    }
		}
	    }
	}
	else if (!nodep->lhsp()->castVarRef()) {
	    clearOptimizable(nodep, "LHS isn't simple variable");
	}
	else if (m_checkOnly) {
	    nodep->iterateChildren(*this);
	}
	else if (optimizable()) {
	    nodep->rhsp()->iterateAndNext(*this);
	    if (optimizable()) {
		AstNode* vscp = varOrScope(nodep->lhsp()->castVarRef());
		assignOutNumber(nodep, vscp, fetchNumber(nodep->rhsp()));
	    }
	}
	m_inDlyAssign = false;
    }
    virtual void visit(AstBegin* nodep, AstNUser*) {
	checkNodeInfo(nodep);
	nodep->iterateChildren(*this);
    }
    virtual void visit(AstNodeCase* nodep, AstNUser*) {
	if (jumpingOver(nodep)) return;
	UINFO(5,"   CASE "<<nodep<<endl);
	checkNodeInfo(nodep);
	if (m_checkOnly) {
	    nodep->iterateChildren(*this);
	} else if (optimizable()) {
	    nodep->exprp()->iterateAndNext(*this);
	    bool hit = false;
	    for (AstCaseItem* itemp = nodep->itemsp(); itemp; itemp=itemp->nextp()->castCaseItem()) {
		if (!itemp->isDefault()) {
		    for (AstNode* ep = itemp->condsp(); ep; ep=ep->nextp()) {
			if (hit) break;
			ep->iterateAndNext(*this);
			if (optimizable()) {
			    V3Number match (nodep->fileline(), 1);
			    match.opEq(*fetchNumber(nodep->exprp()), *fetchNumber(ep));
			    if (match.isNeqZero()) {
				itemp->bodysp()->iterateAndNext(*this);
				hit = true;
			    }
			}
		    }
		}
	    }
	    // Else default match
	    for (AstCaseItem* itemp = nodep->itemsp(); itemp; itemp=itemp->nextp()->castCaseItem()) {
		if (hit) break;
		if (!hit && itemp->isDefault()) {
		    itemp->bodysp()->iterateAndNext(*this);
		    hit = true;
		}
	    }
	}
    }

    virtual void visit(AstCaseItem* nodep, AstNUser*) {
	// Real handling is in AstNodeCase
	if (jumpingOver(nodep)) return;
	checkNodeInfo(nodep);
	nodep->iterateChildren(*this);
    }

    virtual void visit(AstComment*, AstNUser*) {}

    virtual void visit(AstJumpGo* nodep, AstNUser*) {
	if (jumpingOver(nodep)) return;
	checkNodeInfo(nodep);
	if (!m_checkOnly) {
	    UINFO(5,"   JUMP GO "<<nodep<<endl);
	    m_jumpp = nodep;
	}
    }
    virtual void visit(AstJumpLabel* nodep, AstNUser*) {
	if (jumpingOver(nodep)) return;
	checkNodeInfo(nodep);
	nodep->iterateChildren(*this);
	if (m_jumpp && m_jumpp->labelp() == nodep) {
	    UINFO(5,"   JUMP DONE "<<nodep<<endl);
	    m_jumpp = NULL;
	}
    }
    virtual void visit(AstStop* nodep, AstNUser*) {
	if (m_params) {  // This message seems better than an obscure $stop
	    // The spec says $stop is just ignored, it seems evil to ignore assertions
	    clearOptimizable(nodep,"$stop executed during function constification; maybe indicates assertion firing");
	}
	checkNodeInfo(nodep);
    }

    virtual void visit(AstNodeFor* nodep, AstNUser*) {
	// Doing lots of Whiles is slow, so only for parameters
	UINFO(5,"   FOR "<<nodep<<endl);
	if (!m_params) { badNodeType(nodep); return; }
	checkNodeInfo(nodep);
	if (m_checkOnly) {
	    nodep->iterateChildren(*this);
	} else if (optimizable()) {
	    int loops = 0;
	    nodep->initsp()->iterateAndNext(*this);
	    while (1) {
		UINFO(5,"    FOR-ITER "<<nodep<<endl);
		nodep->condp()->iterateAndNext(*this);
		if (!optimizable()) break;
		if (!fetchNumber(nodep->condp())->isNeqZero()) {
		    break;
		}
		nodep->bodysp()->iterateAndNext(*this);
		nodep->incsp()->iterateAndNext(*this);
		if (loops++ > unrollCount()*16) {
		    clearOptimizable(nodep, "Loop unrolling took too long; probably this is an infinite loop, or set --unroll-count above "+cvtToStr(unrollCount()));
		    break;
		}
	    }
	}
    }

    virtual void visit(AstWhile* nodep, AstNUser*) {
	// Doing lots of Whiles is slow, so only for parameters
	if (jumpingOver(nodep)) return;
	UINFO(5,"   WHILE "<<nodep<<endl);
	if (!m_params) { badNodeType(nodep); return; }
	checkNodeInfo(nodep);
	if (m_checkOnly) {
	    nodep->iterateChildren(*this);
	} else if (optimizable()) {
	    int loops = 0;
	    while (1) {
		UINFO(5,"    WHILE-ITER "<<nodep<<endl);
		nodep->precondsp()->iterateAndNext(*this);
		if (jumpingOver(nodep)) break;
		nodep->condp()->iterateAndNext(*this);
		if (jumpingOver(nodep)) break;
		if (!optimizable()) break;
		if (!fetchNumber(nodep->condp())->isNeqZero()) {
		    break;
		}
		nodep->bodysp()->iterateAndNext(*this);
		if (jumpingOver(nodep)) break;
		nodep->incsp()->iterateAndNext(*this);
		if (jumpingOver(nodep)) break;

		// Prep for next loop
		if (loops++ > unrollCount()*16) {
		    clearOptimizable(nodep, "Loop unrolling took too long; probably this is an infinite loop, or set --unroll-count above "+cvtToStr(unrollCount()));
		    break;
		}
	    }
	}
    }

    virtual void visit(AstFuncRef* nodep, AstNUser*) {
	if (jumpingOver(nodep)) return;
	UINFO(5,"   FUNCREF "<<nodep<<endl);
	if (!m_params) { badNodeType(nodep); return; }
	AstNodeFTask* funcp = nodep->taskp()->castNodeFTask(); if (!funcp) nodep->v3fatalSrc("Not linked");
	// cppcheck-suppress redundantAssignment
	if (m_params) { V3Width::widthParamsEdit(funcp); } funcp=NULL; // Make sure we've sized the function
	funcp = nodep->taskp()->castNodeFTask(); if (!funcp) nodep->v3fatalSrc("Not linked");
	// Apply function call values to function
	V3TaskConnects tconnects = V3Task::taskConnects(nodep, nodep->taskp()->stmtsp());
	// Must do this in two steps, eval all params, then apply them
	// Otherwise chained functions may have the wrong results
	for (V3TaskConnects::iterator it=tconnects.begin(); it!=tconnects.end(); ++it) {
	    AstVar* portp = it->first;
	    AstNode* pinp = it->second->exprp();
	    if (pinp) {  // Else too few arguments in function call - ignore it
		if (portp->isOutput()) {
		    clearOptimizable(portp,"Language violation: Outputs not allowed in constant functions");
		    return;
		}
		// Evaluate pin value
		pinp->accept(*this);
	    }
	}
	for (V3TaskConnects::iterator it=tconnects.begin(); it!=tconnects.end(); ++it) {
	    AstVar* portp = it->first;
	    AstNode* pinp = it->second->exprp();
	    if (pinp) {  // Else too few arguments in function call - ignore it
		// Apply value to the function
		if (!m_checkOnly && optimizable()) {
		    newNumber(portp)->opAssign(*fetchNumber(pinp));
		}
	    }
	}
	// Evaluate the function
	funcp->accept(*this);
	if (!m_checkOnly && optimizable()) {
	    // Grab return value from output variable (if it's a function)
	    if (!funcp->fvarp()) nodep->v3fatalSrc("Function reference points at non-function");
	    newNumber(nodep)->opAssign(*fetchNumber(funcp->fvarp()));
	}
    }

    virtual void visit(AstVar* nodep, AstNUser*) {
	if (jumpingOver(nodep)) return;
	if (!m_params) { badNodeType(nodep); return; }
    }

    // default
    // These types are definately not reducable
    //   AstCoverInc, AstDisplay, AstArraySel, AstStop, AstFinish,
    //   AstRand, AstTime, AstUCFunc, AstCCall, AstCStmt, AstUCStmt
    virtual void visit(AstNode* nodep, AstNUser*) {
	if (jumpingOver(nodep)) return;
	badNodeType(nodep);
    }

private:
    // MEMBERS - called by constructor
    void setMode(bool scoped, bool checkOnly, bool params) {
	m_checkOnly = checkOnly;
	m_scoped = scoped;
	m_params = params;
    }
    void mainGuts(AstNode* nodep) {
	nodep->accept(*this);
	if (m_jumpp) {
	    m_jumpp->v3fatalSrc("JumpGo branched to label that wasn't found");
	    m_jumpp = NULL;
	}
    }
public:
    // CONSTRUCTORS
    SimulateVisitor() {
	setMode(false,false,false);
	clear(); // We reuse this structure in the main loop, so put initializers inside clear()
    }
    void clear() {
	m_whyNotOptimizable = "";
	m_whyNotNodep = NULL;
	m_anyAssignComb = false;
	m_anyAssignDly = false;
	m_inDlyAssign = false;
	m_instrCount = 0;
	m_dataCount = 0;
	m_jumpp = NULL;

	AstNode::user1ClearTree();	// user1p() used on entire tree
	AstNode::user2ClearTree();	// user2p() used on entire tree
	AstNode::user3ClearTree();	// user3p() used on entire tree

	// Move all allocated numbers to the free pool
	m_numFreeps = m_numAllps;
    }
    void mainTableCheck   (AstNode* nodep) {
	setMode(true/*scoped*/,true/*checking*/, false/*params*/);
	mainGuts(nodep);
    }
    void mainTableEmulate (AstNode* nodep) {
	setMode(true/*scoped*/,false/*checking*/, false/*params*/);
	mainGuts(nodep);
    }
    void mainParamEmulate (AstNode* nodep) {
	setMode(false/*scoped*/,false/*checking*/, true/*params*/);
	mainGuts(nodep);
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
