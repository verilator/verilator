// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Simulate code to determine output values/variables
//
// Code available from: http://www.veripool.org/verilator
//
//*************************************************************************
//
// Copyright 2003-2019 by Wilson Snyder.  This program is free software; you can
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
#include <sstream>

//============================================================================

//######################################################################
// Simulate class functions

class SimStackNode {
public:
    // MEMBERS
    AstFuncRef*		m_funcp;
    V3TaskConnects*	m_tconnects;
    // CONSTRUCTORS
    SimStackNode(AstFuncRef* funcp, V3TaskConnects* tconnects):
	m_funcp(funcp),
	m_tconnects(tconnects) {}
    ~SimStackNode() {}
};

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
    std::deque<V3Number*>               m_numFreeps;    ///< List of all numbers free and not in use
    std::deque<V3Number*>               m_numAllps;     ///< List of all numbers free and in use
    std::deque<SimStackNode*>      m_callStack;    ///< Call stack for verbose error messages

    // Cleanup
    // V3Numbers that represents strings are a bit special and the API for V3Number does not allow changing them.
    std::deque<V3Number*>  m_stringNumbersp;  // List of allocated string numbers


    // Note level 8&9 include debugging each simulation value
    VL_DEBUG_FUNC;  // Declare debug()

    // Potentially very slow, intended for debugging
    string prettyNumber(V3Number* nump, AstNodeDType* dtypep) {
        if (AstRefDType* refdtypep = VN_CAST(dtypep, RefDType)) {
	    dtypep = refdtypep->skipRefp();
	}
        if (AstStructDType* stp = VN_CAST(dtypep, StructDType)) {
	    if (stp->packed()) {
                std::ostringstream out;
		out<<"'{";
                for (AstMemberDType* itemp = stp->membersp(); itemp; itemp=VN_CAST(itemp->nextp(), MemberDType)) {
		    int width = itemp->width();
		    int lsb = itemp->lsb();
		    int msb = lsb + width - 1;
		    V3Number fieldNum = V3Number(nump->fileline(), width);
		    fieldNum.opSel(*nump, msb, lsb);
		    out<<itemp->name()<<": ";
		    if (AstNodeDType * childTypep = itemp->subDTypep()) {
			out<<prettyNumber(&fieldNum, childTypep);
		    } else {
			out<<fieldNum;
		    }
		    if (itemp->nextp()) out<<", ";
		}
		out<<"}";
		return out.str();
	    }
        } else if (AstPackArrayDType * arrayp = VN_CAST(dtypep, PackArrayDType)) {
	    if (AstNodeDType * childTypep = arrayp->subDTypep()) {
                std::ostringstream out;
		out<<"[";
		int arrayElements = arrayp->elementsConst();
		for (int element = 0; element < arrayElements; ++element) {
		    int width = childTypep->width();
		    int lsb = width * element;
		    int msb = lsb + width - 1;
		    V3Number fieldNum = V3Number(nump->fileline(), width);
		    fieldNum.opSel(*nump, msb, lsb);
		    int arrayElem = arrayp->lsb() + element;
		    out<<arrayElem<<" = "<<prettyNumber(&fieldNum, childTypep);
		    if (element < arrayElements - 1) out<<", ";
		}
		out<<"]";
		return out.str();
	    }
	}
	return nump->ascii();
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
            std::ostringstream stack;
            for (std::deque<SimStackNode*>::iterator it=m_callStack.begin(); it !=m_callStack.end(); ++it) {
		AstFuncRef* funcp = (*it)->m_funcp;
		stack<<"\nCalled from:\n"<<funcp->fileline()<<" "<<funcp->prettyName()<<"() with parameters:";
		V3TaskConnects* tconnects = (*it)->m_tconnects;
		for (V3TaskConnects::iterator conIt = tconnects->begin(); conIt != tconnects->end(); ++conIt) {
		    AstVar* portp = conIt->first;
		    AstNode* pinp = conIt->second->exprp();
		    AstNodeDType* dtypep = pinp->dtypep();
		    stack<<"\n    "<<portp->prettyName()<<" = "<<prettyNumber(fetchNumber(pinp), dtypep);
		}
	    }
	    m_whyNotOptimizable += stack.str();
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
            nump = new V3Number(nodep->fileline(), nodep->width(), value);
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
    void newNumber(AstNode* nodep, const V3Number& numr) {
        newNumber(nodep)->opAssign(numr);
    }
    void newOutNumber(AstNode* nodep, const V3Number& numr) {
        newOutNumber(nodep)->opAssign(numr);
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
	nodep->user3p((void*)nump);
    }
    inline void setOutNumber(AstNode* nodep, const V3Number* nump) {
	UINFO(9,"     set num "<<*nump<<" on "<<nodep<<endl);
	nodep->user2p((void*)nump);
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
        if (VN_IS(nodep, AssignDly)) {
	    // Don't do setNumber, as value isn't yet visible to following statements
            newOutNumber(vscp, *nump);
	} else {
            newNumber(vscp, *nump);
            newOutNumber(vscp, *nump);
	}
    }

    // VISITORS
    virtual void visit(AstAlways* nodep) {
	if (jumpingOver(nodep)) return;
	checkNodeInfo(nodep);
        iterateChildren(nodep);
    }
    virtual void visit(AstSenTree* nodep) {
	// Sensitivities aren't inputs per se; we'll keep our tree under the same sens.
    }
    virtual void visit(AstVarRef* nodep) {
	if (jumpingOver(nodep)) return;
	if (!optimizable()) return;  // Accelerate
        if (!nodep->varp()) nodep->v3fatalSrc("Unlinked");
        iterateChildren(nodep->varp());
	AstNode* vscp = varOrScope(nodep);

	// We can't have non-delayed assignments with same value on LHS and RHS
	// as we don't figure out variable ordering.
	// Delayed is OK though, as we'll decode the next state separately.
        if (!VN_IS(nodep->varp()->dtypeSkipRefp(), BasicDType)
            && !VN_IS(nodep->varp()->dtypeSkipRefp(), PackArrayDType)
            && !VN_IS(nodep->varp()->dtypeSkipRefp(), StructDType))
            clearOptimizable(nodep,"Array references/not basic");
	if (nodep->lvalue()) {
	    if (m_inDlyAssign) {
		if (!(vscp->user1() & VU_LVDLY)) {
		    vscp->user1( vscp->user1() | VU_LVDLY);
		    if (m_checkOnly) varRefCb (nodep);
		}
            } else {  // nondly asn
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
		V3Number* nump = isConst ? fetchNumberNull(nodep->varp()->valuep()) : NULL;
                if (isConst && nump) {  // Propagate PARAM constants for constant function analysis
		    if (!m_checkOnly && optimizable()) {
                        newNumber(vscp, *nump);
		    }
		} else {
		    if (m_checkOnly) varRefCb (nodep);
		}
	    }
	}
        if (!m_checkOnly && optimizable()) {  // simulating
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
    virtual void visit(AstVarXRef* nodep) {
	if (jumpingOver(nodep)) return;
        if (m_scoped) { badNodeType(nodep); return; }
	else { clearOptimizable(nodep,"Language violation: Dotted hierarchical references not allowed in constant functions"); }
    }
    virtual void visit(AstNodeFTask* nodep) {
	if (jumpingOver(nodep)) return;
	if (!m_params) { badNodeType(nodep); return; }
	if (nodep->dpiImport()) { clearOptimizable(nodep,"DPI import functions aren't simulatable"); }
	checkNodeInfo(nodep);
        iterateChildren(nodep);
    }
    virtual void visit(AstNodeIf* nodep) {
	if (jumpingOver(nodep)) return;
	UINFO(5,"   IF "<<nodep<<endl);
	checkNodeInfo(nodep);
	if (m_checkOnly) {
            iterateChildren(nodep);
	} else {
            iterateAndNextNull(nodep->condp());
	    if (optimizable()) {
		if (fetchNumber(nodep->condp())->isNeqZero()) {
                    iterateAndNextNull(nodep->ifsp());
		} else {
                    iterateAndNextNull(nodep->elsesp());
		}
	    }
	}
    }
    virtual void visit(AstConst* nodep) {
	checkNodeInfo(nodep);
	if (!m_checkOnly && optimizable()) {
	    setNumber(nodep, &(nodep->num()));
	}
    }
    virtual void visit(AstEnumItemRef* nodep) {
	checkNodeInfo(nodep);
	if (!nodep->itemp()) nodep->v3fatalSrc("Not linked");
	if (!m_checkOnly && optimizable()) {
            AstNode* valuep = nodep->itemp()->valuep();
	    if (valuep) {
                iterateAndNextNull(valuep);
		if (optimizable()) {
                    newNumber(nodep, *fetchNumber(valuep));
		}
            } else {
                clearOptimizable(nodep, "No value found for enum item");
            }
        }
    }
    virtual void visit(AstNodeUniop* nodep) {
	if (!optimizable()) return;  // Accelerate
	checkNodeInfo(nodep);
        iterateChildren(nodep);
	if (!m_checkOnly && optimizable()) {
            nodep->numberOperate(*newNumber(nodep),
                                 *fetchNumber(nodep->lhsp()));
	}
    }
    virtual void visit(AstNodeBiop* nodep) {
	if (!optimizable()) return;  // Accelerate
	checkNodeInfo(nodep);
        iterateChildren(nodep);
	if (!m_checkOnly && optimizable()) {
            nodep->numberOperate(*newNumber(nodep),
                                 *fetchNumber(nodep->lhsp()),
                                 *fetchNumber(nodep->rhsp()));
	}
    }
    virtual void visit(AstNodeTriop* nodep) {
	if (!optimizable()) return;  // Accelerate
	checkNodeInfo(nodep);
        iterateChildren(nodep);
	if (!m_checkOnly && optimizable()) {
	    nodep->numberOperate(*newNumber(nodep),
				 *fetchNumber(nodep->lhsp()),
				 *fetchNumber(nodep->rhsp()),
				 *fetchNumber(nodep->thsp()));
	}
    }
    virtual void visit(AstLogAnd* nodep) {
	// Need to short circuit
	if (!optimizable()) return;  // Accelerate
	checkNodeInfo(nodep);
	if (m_checkOnly) {
            iterateChildren(nodep);
	} else {
            iterate(nodep->lhsp());
	    if (optimizable()) {
		if (fetchNumber(nodep->lhsp())->isNeqZero()) {
                    iterate(nodep->rhsp());
                    newNumber(nodep, *fetchNumber(nodep->rhsp()));
		} else {
                    newNumber(nodep, *fetchNumber(nodep->lhsp()));  // a zero
		}
	    }
	}
    }
    virtual void visit(AstLogOr* nodep) {
	// Need to short circuit
	if (!optimizable()) return;  // Accelerate
	checkNodeInfo(nodep);
	if (m_checkOnly) {
            iterateChildren(nodep);
	} else {
            iterate(nodep->lhsp());
	    if (optimizable()) {
		if (fetchNumber(nodep->lhsp())->isNeqZero()) {
                    newNumber(nodep, *fetchNumber(nodep->lhsp()));  // a one
		} else {
                    iterate(nodep->rhsp());
                    newNumber(nodep, *fetchNumber(nodep->rhsp()));
		}
	    }
	}
    }
    virtual void visit(AstLogIf* nodep) {
	// Need to short circuit, same as (!A || B)
	if (!optimizable()) return;  // Accelerate
	checkNodeInfo(nodep);
	if (m_checkOnly) {
            iterateChildren(nodep);
	} else {
            iterate(nodep->lhsp());
	    if (optimizable()) {
		if (fetchNumber(nodep->lhsp())->isEqZero()) {
                    newNumber(nodep, V3Number(nodep->fileline(), 1, 1));  // a one
		} else {
                    iterate(nodep->rhsp());
                    newNumber(nodep, *fetchNumber(nodep->rhsp()));
		}
	    }
	}
    }
    virtual void visit(AstNodeCond* nodep) {
	// We could use above visit(AstNodeTriop), but need to do short circuiting.
	// It's also slower even O(n^2) to evaluate both sides when we really only need to evaluate one side.
	if (!optimizable()) return;  // Accelerate
	checkNodeInfo(nodep);
	if (m_checkOnly) {
            iterateChildren(nodep);
	} else {
            iterate(nodep->condp());
	    if (optimizable()) {
		if (fetchNumber(nodep->condp())->isNeqZero()) {
                    iterate(nodep->expr1p());
                    newNumber(nodep, *fetchNumber(nodep->expr1p()));
		} else {
                    iterate(nodep->expr2p());
                    newNumber(nodep, *fetchNumber(nodep->expr2p()));
		}
	    }
	}
    }

    void handleAssignSel(AstNodeAssign* nodep, AstSel* selp) {
	AstVarRef* varrefp = NULL;
	V3Number lsb = V3Number(nodep->fileline());
        iterateAndNextNull(nodep->rhsp());  // Value to assign
	handleAssignSelRecurse(nodep, selp, varrefp/*ref*/, lsb/*ref*/, 0);
	if (!m_checkOnly && optimizable()) {
	    if (!varrefp) nodep->v3fatalSrc("Indicated optimizable, but no variable found on RHS of select");
	    AstNode* vscp = varOrScope(varrefp);
	    V3Number outnum = V3Number(nodep->fileline());
	    if (V3Number* vscpnump = fetchOutNumberNull(vscp)) {
		outnum = *vscpnump;
	    } else if (V3Number* vscpnump = fetchNumberNull(vscp)) {
		outnum = *vscpnump;
	    } else {  // Assignment to unassigned variable, all bits are X or 0
		outnum = V3Number(nodep->fileline(), varrefp->varp()->widthMin());
		if (varrefp->varp()->basicp() && varrefp->varp()->basicp()->isZeroInit()) {
		    outnum.setAllBits0();
		} else {
		    outnum.setAllBitsX();
		}
	    }
	    outnum.opSelInto(*fetchNumber(nodep->rhsp()),
			     lsb,
			     selp->widthConst());
	    assignOutNumber(nodep, vscp, &outnum);
	}
    }
    void handleAssignSelRecurse(AstNodeAssign* nodep, AstSel* selp,
                                AstVarRef*& outVarrefpRef, V3Number& lsbRef,
                                int depth) {
	// Recurse down to find final variable being set (outVarrefp), with value to write on nodep->rhsp()
	checkNodeInfo(selp);
        iterateAndNextNull(selp->lsbp());  // Bit index
        if (AstVarRef* varrefp = VN_CAST(selp->fromp(), VarRef)) {
	    outVarrefpRef = varrefp;
	    lsbRef = *fetchNumber(selp->lsbp());
	    return;  // And presumably still optimizable()
        } else if (AstSel* subselp = VN_CAST(selp->lhsp(), Sel)) {
	    V3Number sublsb = V3Number(nodep->fileline());
	    handleAssignSelRecurse(nodep, subselp, outVarrefpRef, sublsb/*ref*/, depth+1);
	    if (optimizable()) {
		lsbRef = sublsb;
		lsbRef.opAdd(sublsb, *fetchNumber(selp->lsbp()));
	    }
	} else {
	    clearOptimizable(nodep, "Select LHS isn't simple variable");
	}
    }

    virtual void visit(AstNodeAssign* nodep) {
	if (jumpingOver(nodep)) return;
	if (!optimizable()) return;  // Accelerate
        if (VN_IS(nodep, AssignDly)) {
	    if (m_anyAssignComb) clearOptimizable(nodep, "Mix of dly/non-dly assigns");
	    m_anyAssignDly = true;
	    m_inDlyAssign = true;
	} else {
	    if (m_anyAssignDly) clearOptimizable(nodep, "Mix of dly/non-dly assigns");
	    m_anyAssignComb = true;
	}

        if (AstSel* selp = VN_CAST(nodep->lhsp(), Sel)) {
	    if (!m_params) { clearOptimizable(nodep, "LHS has select"); return; }
	    handleAssignSel(nodep, selp);
	}
        else if (!VN_IS(nodep->lhsp(), VarRef)) {
	    clearOptimizable(nodep, "LHS isn't simple variable");
	}
	else if (m_checkOnly) {
            iterateChildren(nodep);
	}
	else if (optimizable()) {
            iterateAndNextNull(nodep->rhsp());
	    if (optimizable()) {
                AstNode* vscp = varOrScope(VN_CAST(nodep->lhsp(), VarRef));
		assignOutNumber(nodep, vscp, fetchNumber(nodep->rhsp()));
	    }
	}
	m_inDlyAssign = false;
    }
    virtual void visit(AstBegin* nodep) {
	checkNodeInfo(nodep);
        iterateChildren(nodep);
    }
    virtual void visit(AstNodeCase* nodep) {
	if (jumpingOver(nodep)) return;
	UINFO(5,"   CASE "<<nodep<<endl);
	checkNodeInfo(nodep);
	if (m_checkOnly) {
            iterateChildren(nodep);
	} else if (optimizable()) {
            iterateAndNextNull(nodep->exprp());
	    bool hit = false;
            for (AstCaseItem* itemp = nodep->itemsp(); itemp; itemp=VN_CAST(itemp->nextp(), CaseItem)) {
		if (!itemp->isDefault()) {
		    for (AstNode* ep = itemp->condsp(); ep; ep=ep->nextp()) {
			if (hit) break;
                        iterateAndNextNull(ep);
			if (optimizable()) {
			    V3Number match (nodep->fileline(), 1);
			    match.opEq(*fetchNumber(nodep->exprp()), *fetchNumber(ep));
			    if (match.isNeqZero()) {
                                iterateAndNextNull(itemp->bodysp());
				hit = true;
			    }
			}
		    }
		}
	    }
	    // Else default match
            for (AstCaseItem* itemp = nodep->itemsp(); itemp; itemp=VN_CAST(itemp->nextp(), CaseItem)) {
		if (hit) break;
		if (!hit && itemp->isDefault()) {
                    iterateAndNextNull(itemp->bodysp());
		    hit = true;
		}
	    }
	}
    }

    virtual void visit(AstCaseItem* nodep) {
	// Real handling is in AstNodeCase
	if (jumpingOver(nodep)) return;
	checkNodeInfo(nodep);
        iterateChildren(nodep);
    }

    virtual void visit(AstComment*) {}

    virtual void visit(AstJumpGo* nodep) {
	if (jumpingOver(nodep)) return;
	checkNodeInfo(nodep);
	if (!m_checkOnly) {
	    UINFO(5,"   JUMP GO "<<nodep<<endl);
	    m_jumpp = nodep;
	}
    }
    virtual void visit(AstJumpLabel* nodep) {
	if (jumpingOver(nodep)) return;
	checkNodeInfo(nodep);
        iterateChildren(nodep);
	if (m_jumpp && m_jumpp->labelp() == nodep) {
	    UINFO(5,"   JUMP DONE "<<nodep<<endl);
	    m_jumpp = NULL;
	}
    }
    virtual void visit(AstStop* nodep) {
	if (jumpingOver(nodep)) return;
	if (m_params) {  // This message seems better than an obscure $stop
	    // The spec says $stop is just ignored, it seems evil to ignore assertions
	    clearOptimizable(nodep,"$stop executed during function constification; maybe indicates assertion firing");
	}
	checkNodeInfo(nodep);
    }

    virtual void visit(AstNodeFor* nodep) {
	// Doing lots of Whiles is slow, so only for parameters
	UINFO(5,"   FOR "<<nodep<<endl);
	if (!m_params) { badNodeType(nodep); return; }
	checkNodeInfo(nodep);
	if (m_checkOnly) {
            iterateChildren(nodep);
	} else if (optimizable()) {
	    int loops = 0;
            iterateAndNextNull(nodep->initsp());
	    while (1) {
		UINFO(5,"    FOR-ITER "<<nodep<<endl);
                iterateAndNextNull(nodep->condp());
		if (!optimizable()) break;
		if (!fetchNumber(nodep->condp())->isNeqZero()) {
		    break;
		}
                iterateAndNextNull(nodep->bodysp());
                iterateAndNextNull(nodep->incsp());
		if (loops++ > unrollCount()*16) {
                    clearOptimizable(nodep, "Loop unrolling took too long; probably this is an"
                                     "infinite loop, or set --unroll-count above "
                                     + cvtToStr(unrollCount()));
		    break;
		}
	    }
	}
    }

    virtual void visit(AstWhile* nodep) {
	// Doing lots of Whiles is slow, so only for parameters
	if (jumpingOver(nodep)) return;
	UINFO(5,"   WHILE "<<nodep<<endl);
	if (!m_params) { badNodeType(nodep); return; }
	checkNodeInfo(nodep);
	if (m_checkOnly) {
            iterateChildren(nodep);
	} else if (optimizable()) {
	    int loops = 0;
	    while (1) {
		UINFO(5,"    WHILE-ITER "<<nodep<<endl);
                iterateAndNextNull(nodep->precondsp());
		if (jumpingOver(nodep)) break;
                iterateAndNextNull(nodep->condp());
		if (jumpingOver(nodep)) break;
		if (!optimizable()) break;
		if (!fetchNumber(nodep->condp())->isNeqZero()) {
		    break;
		}
                iterateAndNextNull(nodep->bodysp());
		if (jumpingOver(nodep)) break;
                iterateAndNextNull(nodep->incsp());
		if (jumpingOver(nodep)) break;

		// Prep for next loop
		if (loops++ > unrollCount()*16) {
                    clearOptimizable(nodep, "Loop unrolling took too long; probably this is an infinite"
                                     " loop, or set --unroll-count above "+cvtToStr(unrollCount()));
		    break;
		}
	    }
	}
    }

    virtual void visit(AstFuncRef* nodep) {
	if (jumpingOver(nodep)) return;
	if (!optimizable()) return;  // Accelerate
	UINFO(5,"   FUNCREF "<<nodep<<endl);
	if (!m_params) { badNodeType(nodep); return; }
        AstNodeFTask* funcp = VN_CAST(nodep->taskp(), NodeFTask); if (!funcp) nodep->v3fatalSrc("Not linked");
        if (m_params) { V3Width::widthParamsEdit(funcp); } VL_DANGLING(funcp);  // Make sure we've sized the function
        funcp = VN_CAST(nodep->taskp(), NodeFTask); if (!funcp) nodep->v3fatalSrc("Not linked");
	// Apply function call values to function
	V3TaskConnects tconnects = V3Task::taskConnects(nodep, nodep->taskp()->stmtsp());
	// Must do this in two steps, eval all params, then apply them
	// Otherwise chained functions may have the wrong results
	for (V3TaskConnects::iterator it=tconnects.begin(); it!=tconnects.end(); ++it) {
	    AstVar* portp = it->first;
	    AstNode* pinp = it->second->exprp();
	    if (pinp) {  // Else too few arguments in function call - ignore it
                if (portp->isWritable()) {
                    clearOptimizable(portp, "Language violation: Outputs/refs not allowed in constant functions");
                    return;
                }
                // Evaluate pin value
                iterate(pinp);
	    }
	}
	for (V3TaskConnects::iterator it=tconnects.begin(); it!=tconnects.end(); ++it) {
	    AstVar* portp = it->first;
	    AstNode* pinp = it->second->exprp();
	    if (pinp) {  // Else too few arguments in function call - ignore it
		// Apply value to the function
		if (!m_checkOnly && optimizable()) {
                    newNumber(portp, *fetchNumber(pinp));
		}
	    }
	}
        SimStackNode stackNode(nodep, &tconnects);
	m_callStack.push_front(&stackNode);
	// Evaluate the function
        iterate(funcp);
	m_callStack.pop_front();
	if (!m_checkOnly && optimizable()) {
	    // Grab return value from output variable (if it's a function)
	    if (!funcp->fvarp()) nodep->v3fatalSrc("Function reference points at non-function");
            newNumber(nodep, *fetchNumber(funcp->fvarp()));
	}
    }

    virtual void visit(AstVar* nodep) {
	if (jumpingOver(nodep)) return;
	if (!m_params) { badNodeType(nodep); return; }
    }

    virtual void visit(AstScopeName *nodep) {
	if (jumpingOver(nodep)) return;
	if (!m_params) { badNodeType(nodep); return; }
	// Ignore
    }

    virtual void visit(AstSFormatF *nodep) {
	if (jumpingOver(nodep)) return;
	if (!optimizable()) return;  // Accelerate
        iterateChildren(nodep);
	if (m_params) {
	    AstNode* nextArgp = nodep->exprsp();

            string result;
	    string format = nodep->text();
	    string::const_iterator pos = format.begin();
	    bool inPct = false;
	    for (; pos != format.end(); ++pos) {
		if (!inPct && pos[0] == '%') {
		    inPct = true;
                } else if (!inPct) {  // Normal text
		    result += *pos;
                } else {  // Format character
		    inPct = false;

		    if (V3Number::displayedFmtLegal(tolower(pos[0]))) {
			AstNode* argp = nextArgp;
			nextArgp = nextArgp->nextp();
			V3Number* nump = fetchNumberNull(argp);
			if (!nump) {
			    clearOptimizable(nodep, "Argument for $display like statement is not constant");
			    break;
			}
			string format = string("%") + pos[0];
			result += nump->displayed(nodep->fileline(), format);
		    } else {
			switch (tolower(pos[0])) {
			case '%':
			    result += "%";
			    break;
			case 'm':
			    // This happens prior to AstScope so we don't know the scope name. Leave the %m in place.
			    result += "%m";
			    break;
			default:
			    clearOptimizable(nodep, "Unknown $display-like format code.");
			    break;
			}
		    }
		}
	    }

	    V3Number* resultNump = new V3Number(V3Number::String(), nodep->fileline(), result);
	    setNumber(nodep, resultNump);
	    m_stringNumbersp.push_back(resultNump);

	}
    }

    virtual void visit(AstDisplay *nodep) {
	if (jumpingOver(nodep)) return;
	if (!optimizable()) return;  // Accelerate
        iterateChildren(nodep);
	if (m_params) {
	    V3Number* textp = fetchNumber(nodep->fmtp());
	    switch (nodep->displayType()) {
	    case AstDisplayType::DT_DISPLAY:  // FALLTHRU
	    case AstDisplayType::DT_INFO:
		v3warn(USERINFO, textp->toString());
		break;
	    case AstDisplayType::DT_ERROR:
		v3warn(USERERROR, textp->toString());
		break;
	    case AstDisplayType::DT_WARNING:
		v3warn(USERWARN, textp->toString());
		break;
	    case AstDisplayType::DT_FATAL:
		v3warn(USERFATAL, textp->toString());
		break;
	    case AstDisplayType::DT_WRITE:  // FALLTHRU
	    default:
		clearOptimizable(nodep, "Unexpected display type");
	    }
	}
    }

    // default
    // These types are definately not reducable
    //   AstCoverInc, AstArraySel, AstFinish,
    //   AstRand, AstTime, AstUCFunc, AstCCall, AstCStmt, AstUCStmt
    virtual void visit(AstNode* nodep) {
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
        iterate(nodep);
	if (m_jumpp) {
	    m_jumpp->v3fatalSrc("JumpGo branched to label that wasn't found");
	    m_jumpp = NULL;
	}
    }
public:
    // CONSTRUCTORS
    SimulateVisitor() {
        // Note AstUser#InUse ensures only one invocation exists at once
	setMode(false,false,false);
        clear();  // We reuse this structure in the main loop, so put initializers inside clear()
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

        AstNode::user1ClearTree();
        AstNode::user2ClearTree();
        AstNode::user3ClearTree();

	// Move all allocated numbers to the free pool
	m_numFreeps = m_numAllps;
    }
    void mainTableCheck(AstNode* nodep) {
	setMode(true/*scoped*/,true/*checking*/, false/*params*/);
	mainGuts(nodep);
    }
    void mainTableEmulate(AstNode* nodep) {
	setMode(true/*scoped*/,false/*checking*/, false/*params*/);
	mainGuts(nodep);
    }
    void mainCheckTree(AstNode* nodep) {
	setMode(false/*scoped*/,true/*checking*/, false/*params*/);
	mainGuts(nodep);
    }
    void mainParamEmulate(AstNode* nodep) {
	setMode(false/*scoped*/,false/*checking*/, true/*params*/);
	mainGuts(nodep);
    }
    virtual ~SimulateVisitor() {
        for (std::deque<V3Number*>::iterator it = m_numAllps.begin(); it != m_numAllps.end(); ++it) {
	    delete (*it);
	}
        for (std::deque<V3Number*>::iterator it = m_stringNumbersp.begin(); it != m_stringNumbersp.end(); ++it) {
	    delete (*it);
	}
	m_stringNumbersp.clear();
	m_numFreeps.clear();
	m_numAllps.clear();
    }
};

#endif  // Guard
