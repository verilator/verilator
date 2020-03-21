// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Simulate code to determine output values/variables
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2020 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************
//
// void example_usage() {
//      SimulateVisitor simvis (false, false);
//      simvis.clear();
//      // Set all inputs to the constant
//      for (deque<AstVarScope*>::iterator it = m_inVarps.begin(); it!=m_inVarps.end(); ++it) {
//          simvis.newValue(invscp, #);
//      }
//      // Simulate
//      simvis.main(nodep);
//      // Read outputs
//      for (deque<AstVarScope*>::iterator it = m_outVarps.begin(); it!=m_outVarps.end(); ++it) {
//          AstConst* outconstp = simvis.fetchOutNumberNull(outvscp);
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
    AstFuncRef* m_funcp;
    V3TaskConnects* m_tconnects;
    // CONSTRUCTORS
    SimStackNode(AstFuncRef* funcp, V3TaskConnects* tconnects)
        : m_funcp(funcp)
        , m_tconnects(tconnects) {}
    ~SimStackNode() {}
};

typedef std::deque<AstConst*> ConstDeque;
typedef std::map<AstNodeDType*, ConstDeque> ConstPile;

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
    AstUser1InUse m_inuser1;
    AstUser2InUse m_inuser2;
    AstUser3InUse m_inuser3;

    // Checking:
    //  AstVar(Scope)::user1()  -> VarUsage.  Set true to indicate tracking as lvalue/rvalue
    // Simulating:
    //  AstVar(Scope)::user3()  -> AstConst*. Input value of variable or node
    //    (and output for non-delayed assignments)
    //  AstVar(Scope)::user2()  -> AstCont*. Output value of variable (delayed assignments)

    enum VarUsage { VU_NONE = 0, VU_LV = 1, VU_RV = 2, VU_LVDLY = 4 };

    // STATE
    // Major mode
    bool        m_checkOnly;            ///< Checking only (no simulation) mode
    bool        m_scoped;               ///< Running with AstVarScopes instead of AstVars
    bool        m_params;               ///< Doing parameter propagation
    // Checking:
    string      m_whyNotOptimizable;    ///< String explaining why not optimizable or NULL to optimize
    AstNode*    m_whyNotNodep;          ///< First node not optimizable
    bool        m_anyAssignDly;         ///< True if found a delayed assignment
    bool        m_anyAssignComb;        ///< True if found a non-delayed assignment
    bool        m_inDlyAssign;          ///< Under delayed assignment
    int         m_instrCount;           ///< Number of nodes
    int         m_dataCount;            ///< Bytes of data
    AstJumpGo*  m_jumpp;                ///< Jump label we're branching from
    // Simulating:
    ConstPile   m_constFreeps;          ///< List of all AstConst* free and not in use
    ConstPile   m_constAllps;           ///< List of all AstConst* free and in use
    std::deque<SimStackNode*> m_callStack;  ///< Call stack for verbose error messages

    // Cleanup
    // V3Numbers that represents strings are a bit special and the API for
    // V3Number does not allow changing them.
    std::deque<AstNode*> m_reclaimValuesp;  // List of allocated string numbers

    // Note level 8&9 include debugging each simulation value
    VL_DEBUG_FUNC;  // Declare debug()

    // Potentially very slow, intended for debugging
    string prettyNumber(const V3Number* nump, AstNodeDType* dtypep) {
        if (AstRefDType* refdtypep = VN_CAST(dtypep, RefDType)) {
            dtypep = refdtypep->skipRefp();
        }
        if (AstStructDType* stp = VN_CAST(dtypep, StructDType)) {
            if (stp->packed()) {
                std::ostringstream out;
                out<<"'{";
                for (AstMemberDType* itemp = stp->membersp();
                     itemp; itemp = VN_CAST(itemp->nextp(), MemberDType)) {
                    int width = itemp->width();
                    int lsb = itemp->lsb();
                    int msb = lsb + width - 1;
                    V3Number fieldNum(nump, width);
                    fieldNum.opSel(*nump, msb, lsb);
                    out<<itemp->name()<<": ";
                    if (AstNodeDType* childTypep = itemp->subDTypep()) {
                        out<<prettyNumber(&fieldNum, childTypep);
                    } else {
                        out<<fieldNum;
                    }
                    if (itemp->nextp()) out<<", ";
                }
                out<<"}";
                return out.str();
            }
        } else if (AstPackArrayDType* arrayp = VN_CAST(dtypep, PackArrayDType)) {
            if (AstNodeDType* childTypep = arrayp->subDTypep()) {
                std::ostringstream out;
                out<<"[";
                int arrayElements = arrayp->elementsConst();
                for (int element = 0; element < arrayElements; ++element) {
                    int width = childTypep->width();
                    int lsb = width * element;
                    int msb = lsb + width - 1;
                    V3Number fieldNum(nump, width);
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
        //  and fetchConst should not be called or it may assert.
        if (!m_whyNotNodep) {
            m_whyNotNodep = nodep;
            if (debug() >= 5) {
                UINFO(0, "Clear optimizable: "<<why);
                if (nodep) cout<<": "<<nodep;
                cout<<endl;
            }
            m_whyNotOptimizable = why;
            std::ostringstream stack;
            for (std::deque<SimStackNode*>::iterator it = m_callStack.begin();
                 it != m_callStack.end(); ++it) {
                AstFuncRef* funcp = (*it)->m_funcp;
                stack<<"\n        "<<funcp->fileline()
                     <<"... Called from "
                     <<funcp->prettyName()<<"() with parameters:";
                V3TaskConnects* tconnects = (*it)->m_tconnects;
                for (V3TaskConnects::iterator conIt = tconnects->begin();
                     conIt != tconnects->end(); ++conIt) {
                    AstVar* portp = conIt->first;
                    AstNode* pinp = conIt->second->exprp();
                    AstNodeDType* dtypep = pinp->dtypep();
                    stack<<"\n           "<<portp->prettyName(
                        )<<" = "<<prettyNumber(&fetchConst(pinp)->num(), dtypep);
                }
            }
            m_whyNotOptimizable += stack.str();
        }
    }
    bool optimizable() const { return m_whyNotNodep == NULL; }
    string whyNotMessage() const { return m_whyNotOptimizable; }
    AstNode* whyNotNodep() const { return m_whyNotNodep; }

    bool isAssignDly() const { return m_anyAssignDly; }
    int instrCount() const { return m_instrCount; }
    int dataCount() const { return m_dataCount; }

    // Simulation METHODS
private:
    AstConst* allocConst(AstNode* nodep) {
        // Save time - kept a list of allocated but unused values
        // It would be more efficient to do this by size, but the extra accounting
        // slows things down more than we gain.
        AstConst* constp;
        AstNodeDType* dtypep = nodep->dtypep();
        if (!m_constFreeps[dtypep].empty()) {
            //UINFO(7, "Num Reuse "<<nodep->width()<<endl);
            constp = m_constFreeps[dtypep].back(); m_constFreeps[dtypep].pop_back();
            constp->num().nodep(nodep);
        } else {
            //UINFO(7, "Num New "<<nodep->width()<<endl);
            constp = new AstConst(nodep->fileline(), AstConst::DtypedValue(), nodep->dtypep(), 0);
            m_constAllps[constp->dtypep()].push_back(constp);
        }
        constp->num().isDouble(nodep->isDouble());
        constp->num().isString(nodep->isString());
        return constp;
    }
public:
    void newValue(AstNode* nodep, const AstNode* valuep) {
        if (const AstConst* constp = VN_CAST_CONST(valuep, Const)) {
            newConst(nodep)->num().opAssign(constp->num());
        } else if (fetchValueNull(nodep) != valuep) {
            // const_cast, as clonep() is set on valuep, but nothing should care
            setValue(nodep, newTrackedClone(const_cast<AstNode*>(valuep)));
        }
    }
    void newOutValue(AstNode* nodep, const AstNode* valuep) {
        if (const AstConst* constp = VN_CAST_CONST(valuep, Const)) {
            newOutConst(nodep)->num().opAssign(constp->num());
        } else if (fetchOutValueNull(nodep) != valuep) {
            // const_cast, as clonep() is set on valuep, but nothing should care
            setOutValue(nodep, newTrackedClone(const_cast<AstNode*>(valuep)));
        }
    }
private:
    AstNode* newTrackedClone(AstNode* nodep) {
        AstNode* newp = nodep->cloneTree(false);
        m_reclaimValuesp.push_back(newp);
        return newp;
    }
    AstConst* newConst(AstNode* nodep) {
        // Set a constant value for this node
        if (!VN_IS(nodep->user3p(), Const)) {
            AstConst* constp = allocConst(nodep);
            setValue(nodep, constp);
            return constp;
        } else {
            return fetchConst(nodep);
        }
    }
    AstConst* newOutConst(AstNode* nodep) {
        // Set a var-output constant value for this node
        if (!VN_IS(nodep->user2p(), Const)) {
            AstConst* constp = allocConst(nodep);
            setOutValue(nodep, constp);
            return constp;
        } else {
            return fetchOutConst(nodep);
        }
    }
public:
    AstNode* fetchValueNull(AstNode* nodep) {
        return (AstNode*)(nodep->user3p());
    }
private:
    AstNode* fetchOutValueNull(AstNode* nodep) {
        return (AstNode*)(nodep->user2p());
    }
    AstConst* fetchConstNull(AstNode* nodep) {
        return VN_CAST(fetchValueNull(nodep), Const);
    }
    AstConst* fetchOutConstNull(AstNode* nodep) {
        return VN_CAST(fetchOutValueNull(nodep), Const);
    }
    AstNode* fetchValue(AstNode* nodep) {
        AstNode* valuep = fetchValueNull(nodep);
        UASSERT_OBJ(valuep, nodep, "No value found for node.");
        //UINFO(9, "     fetch val "<<*valuep<<" on "<<nodep<<endl);
        return valuep;
    }
    AstConst* fetchConst(AstNode* nodep) {
        AstConst* constp = fetchConstNull(nodep);
        UASSERT_OBJ(constp, nodep, "No value found for node.");
        //UINFO(9, "     fetch num "<<*constp<<" on "<<nodep<<endl);
        return constp;
    }
    AstConst* fetchOutConst(AstNode* nodep) {
        AstConst* constp = fetchOutConstNull(nodep);
        UASSERT_OBJ(constp, nodep, "No value found for node.");
        return constp;
    }
public:
    V3Number* fetchNumberNull(AstNode* nodep) {
        AstConst* constp = fetchConstNull(nodep);
        if (constp) return &constp->num();
        return NULL;
    }
    V3Number* fetchOutNumberNull(AstNode* nodep) {
        AstConst* constp = fetchOutConstNull(nodep);
        if (constp) return &constp->num();
        return NULL;
    }
private:
    void setValue(AstNode* nodep, const AstNode* valuep) {
        UASSERT_OBJ(valuep, nodep, "Simulate setting null value");
        UINFO(9, "     set val "<<valuep->name()<<" on "<<nodep<<endl);
        nodep->user3p((void*)valuep);
    }
    void setOutValue(AstNode* nodep, const AstNode* valuep) {
        UASSERT_OBJ(valuep, nodep, "Simulate setting null value");
        UINFO(9, "     set oval "<<valuep->name()<<" on "<<nodep<<endl);
        nodep->user2p((void*)valuep);
    }

    void checkNodeInfo(AstNode* nodep) {
        if (m_checkOnly) {
            m_instrCount += nodep->instrCount();
            m_dataCount += nodep->width();
        }
        if (!nodep->isPredictOptimizable()) {
            //UINFO(9, "     !predictopt "<<nodep<<endl);
            clearOptimizable(nodep, "Isn't predictable");
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
            UINFO(0, "Unknown node type in SimulateVisitor: "<<nodep->prettyTypeName()<<endl);
#endif
        }
    }

    AstNode* varOrScope(AstVarRef* nodep) {
        AstNode* vscp;
        if (m_scoped) vscp = nodep->varScopep();
        else vscp = nodep->varp();
        UASSERT_OBJ(vscp, nodep, "Not linked");
        return vscp;
    }
    int unrollCount() {
        return m_params ? v3Global.opt.unrollCount() * 16 : v3Global.opt.unrollCount();
    }
    bool jumpingOver(AstNode* nodep) {
        // True to jump over this node - all visitors must call this up front
        return (m_jumpp && m_jumpp->labelp() != nodep);
    }
    void assignOutValue(AstNodeAssign* nodep, AstNode* vscp, const AstNode* valuep) {
        if (VN_IS(nodep, AssignDly)) {
            // Don't do setValue, as value isn't yet visible to following statements
            newOutValue(vscp, valuep);
        } else {
            newValue(vscp, valuep);
            newOutValue(vscp, valuep);
        }
    }

    // VISITORS
    virtual void visit(AstAlways* nodep) VL_OVERRIDE {
        if (jumpingOver(nodep)) return;
        checkNodeInfo(nodep);
        iterateChildren(nodep);
    }
    virtual void visit(AstSenTree* nodep) VL_OVERRIDE {
        // Sensitivities aren't inputs per se; we'll keep our tree under the same sens.
    }
    virtual void visit(AstVarRef* nodep) VL_OVERRIDE {
        if (jumpingOver(nodep)) return;
        if (!optimizable()) return;  // Accelerate
        UASSERT_OBJ(nodep->varp(), nodep, "Unlinked");
        iterateChildren(nodep->varp());
        AstNode* vscp = varOrScope(nodep);

        // We can't have non-delayed assignments with same value on LHS and RHS
        // as we don't figure out variable ordering.
        // Delayed is OK though, as we'll decode the next state separately.
        if (!VN_IS(nodep->varp()->dtypeSkipRefp(), BasicDType)
            && !VN_IS(nodep->varp()->dtypeSkipRefp(), PackArrayDType)
            && !VN_IS(nodep->varp()->dtypeSkipRefp(), UnpackArrayDType)
            && !VN_IS(nodep->varp()->dtypeSkipRefp(), StructDType))
            clearOptimizable(nodep, "Array references/not basic");
        if (nodep->lvalue()) {
            if (m_inDlyAssign) {
                if (!(vscp->user1() & VU_LVDLY)) {
                    vscp->user1(vscp->user1() | VU_LVDLY);
                    if (m_checkOnly) varRefCb(nodep);
                }
            } else {  // nondly asn
                if (!(vscp->user1() & VU_LV)) {
                    if (!m_params && (vscp->user1() & VU_RV)) {
                        clearOptimizable(nodep, "Var read & write");
                    }
                    vscp->user1(vscp->user1() | VU_LV);
                    if (m_checkOnly) varRefCb(nodep);
                }
            }
        } else {
            if (!(vscp->user1() & VU_RV)) {
                if (!m_params && (vscp->user1() & VU_LV)) {
                    clearOptimizable(nodep, "Var write & read");
                }
                vscp->user1(vscp->user1() | VU_RV);
                bool isConst = nodep->varp()->isParam() && nodep->varp()->valuep();
                AstNode* valuep = isConst ? fetchValueNull(nodep->varp()->valuep()) : NULL;
                if (isConst && valuep) {  // Propagate PARAM constants for constant function analysis
                    if (!m_checkOnly && optimizable()) {
                        newValue(vscp, valuep);
                    }
                } else {
                    if (m_checkOnly) varRefCb(nodep);
                }
            }
        }
        if (!m_checkOnly && optimizable()) {  // simulating
            UASSERT_OBJ(!nodep->lvalue(), nodep,
                        "LHS varref should be handled in AstAssign visitor.");
            {
                // Return simulation value - copy by reference instead of value for speed
                AstNode* valuep = fetchValueNull(vscp);
                if (!valuep) {
                    if (m_params) {
                        clearOptimizable(nodep, "Language violation: reference to non-function-local variable");
                    } else {
                        nodep->v3fatalSrc("Variable value should have been set before any visitor called.");
                    }
                    valuep = allocConst(nodep);  // Any value; just so recover from error
                }
                setValue(nodep, valuep);
            }
        }
    }
    virtual void visit(AstVarXRef* nodep) VL_OVERRIDE {
        if (jumpingOver(nodep)) return;
        if (m_scoped) { badNodeType(nodep); return; }
        else { clearOptimizable(nodep, "Language violation: Dotted hierarchical references not allowed in constant functions"); }
    }
    virtual void visit(AstNodeFTask* nodep) VL_OVERRIDE {
        if (jumpingOver(nodep)) return;
        if (!m_params) { badNodeType(nodep); return; }
        if (nodep->dpiImport()) {
            clearOptimizable(nodep, "DPI import functions aren't simulatable");
        }
        checkNodeInfo(nodep);
        iterateChildren(nodep);
    }
    virtual void visit(AstNodeIf* nodep) VL_OVERRIDE {
        if (jumpingOver(nodep)) return;
        UINFO(5, "   IF "<<nodep<<endl);
        checkNodeInfo(nodep);
        if (m_checkOnly) {
            iterateChildren(nodep);
        } else {
            iterateAndNextNull(nodep->condp());
            if (optimizable()) {
                if (fetchConst(nodep->condp())->num().isNeqZero()) {
                    iterateAndNextNull(nodep->ifsp());
                } else {
                    iterateAndNextNull(nodep->elsesp());
                }
            }
        }
    }
    virtual void visit(AstConst* nodep) VL_OVERRIDE {
        checkNodeInfo(nodep);
        if (!m_checkOnly && optimizable()) {
            newValue(nodep, nodep);
        }
    }
    virtual void visit(AstInitArray* nodep) VL_OVERRIDE {
        checkNodeInfo(nodep);
        if (!m_checkOnly && optimizable()) {
            newValue(nodep, nodep);
        }
    }
    virtual void visit(AstEnumItemRef* nodep) VL_OVERRIDE {
        checkNodeInfo(nodep);
        UASSERT_OBJ(nodep->itemp(), nodep, "Not linked");
        if (!m_checkOnly && optimizable()) {
            AstNode* valuep = nodep->itemp()->valuep();
            if (valuep) {
                iterateAndNextNull(valuep);
                if (optimizable()) {
                    newValue(nodep, fetchValue(valuep));
                }
            } else {
                clearOptimizable(nodep, "No value found for enum item");
            }
        }
    }
    virtual void visit(AstNodeUniop* nodep) VL_OVERRIDE {
        if (!optimizable()) return;  // Accelerate
        checkNodeInfo(nodep);
        iterateChildren(nodep);
        if (!m_checkOnly && optimizable()) {
            nodep->numberOperate(newConst(nodep)->num(),
                                 fetchConst(nodep->lhsp())->num());
        }
    }
    virtual void visit(AstNodeBiop* nodep) VL_OVERRIDE {
        if (!optimizable()) return;  // Accelerate
        checkNodeInfo(nodep);
        iterateChildren(nodep);
        if (!m_checkOnly && optimizable()) {
            nodep->numberOperate(newConst(nodep)->num(),
                                 fetchConst(nodep->lhsp())->num(),
                                 fetchConst(nodep->rhsp())->num());
        }
    }
    virtual void visit(AstNodeTriop* nodep) VL_OVERRIDE {
        if (!optimizable()) return;  // Accelerate
        checkNodeInfo(nodep);
        iterateChildren(nodep);
        if (!m_checkOnly && optimizable()) {
            nodep->numberOperate(newConst(nodep)->num(),
                                 fetchConst(nodep->lhsp())->num(),
                                 fetchConst(nodep->rhsp())->num(),
                                 fetchConst(nodep->thsp())->num());
        }
    }
    virtual void visit(AstLogAnd* nodep) VL_OVERRIDE {
        // Need to short circuit
        if (!optimizable()) return;  // Accelerate
        checkNodeInfo(nodep);
        if (m_checkOnly) {
            iterateChildren(nodep);
        } else {
            iterate(nodep->lhsp());
            if (optimizable()) {
                if (fetchConst(nodep->lhsp())->num().isNeqZero()) {
                    iterate(nodep->rhsp());
                    newValue(nodep, fetchValue(nodep->rhsp()));
                } else {
                    newValue(nodep, fetchValue(nodep->lhsp()));  // a zero
                }
            }
        }
    }
    virtual void visit(AstLogOr* nodep) VL_OVERRIDE {
        // Need to short circuit
        if (!optimizable()) return;  // Accelerate
        checkNodeInfo(nodep);
        if (m_checkOnly) {
            iterateChildren(nodep);
        } else {
            iterate(nodep->lhsp());
            if (optimizable()) {
                if (fetchConst(nodep->lhsp())->num().isNeqZero()) {
                    newValue(nodep, fetchValue(nodep->lhsp()));  // a one
                } else {
                    iterate(nodep->rhsp());
                    newValue(nodep, fetchValue(nodep->rhsp()));
                }
            }
        }
    }
    virtual void visit(AstLogIf* nodep) VL_OVERRIDE {
        // Need to short circuit, same as (!A || B)
        if (!optimizable()) return;  // Accelerate
        checkNodeInfo(nodep);
        if (m_checkOnly) {
            iterateChildren(nodep);
        } else {
            iterate(nodep->lhsp());
            if (optimizable()) {
                if (fetchConst(nodep->lhsp())->num().isEqZero()) {
                    AstConst cnst(nodep->fileline(), AstConst::WidthedValue(), 1, 1);  // a one
                    newValue(nodep, &cnst);  // a one
                } else {
                    iterate(nodep->rhsp());
                    newValue(nodep, fetchValue(nodep->rhsp()));
                }
            }
        }
    }
    virtual void visit(AstNodeCond* nodep) VL_OVERRIDE {
        // We could use above visit(AstNodeTriop), but need to do short circuiting.
        // It's also slower even O(n^2) to evaluate both sides when we
        // really only need to evaluate one side.
        if (!optimizable()) return;  // Accelerate
        checkNodeInfo(nodep);
        if (m_checkOnly) {
            iterateChildren(nodep);
        } else {
            iterate(nodep->condp());
            if (optimizable()) {
                if (fetchConst(nodep->condp())->num().isNeqZero()) {
                    iterate(nodep->expr1p());
                    newValue(nodep, fetchValue(nodep->expr1p()));
                } else {
                    iterate(nodep->expr2p());
                    newValue(nodep, fetchValue(nodep->expr2p()));
                }
            }
        }
    }

    void handleAssignArray(AstNodeAssign* nodep, AstArraySel* selp) {
        iterateAndNextNull(nodep->rhsp());  // Value to assign
        // At present we only handle single dimensional assignments
        // To do better, we need the concept of lvalues, or similar, to know where/how to insert
        checkNodeInfo(selp);
        iterateAndNextNull(selp->bitp());  // Bit index
        AstVarRef* varrefp = VN_CAST(selp->fromp(), VarRef);
        if (!varrefp) {
            clearOptimizable(nodep, "Array select LHS isn't simple variable");
            return;
        }
        AstUnpackArrayDType* arrayp = VN_CAST(varrefp->varp()->dtypeSkipRefp(), UnpackArrayDType);
        UASSERT_OBJ(arrayp, nodep, "Array select of non-array dtype");
        AstBasicDType* basicp = VN_CAST(arrayp->subDTypep()->skipRefp(), BasicDType);
        if (!basicp) {
            clearOptimizable(nodep, "Array of non-basic dtype (e.g. array-of-array)");
            return;
        }
        if (!m_checkOnly && optimizable()) {
            AstNode* vscp = varOrScope(varrefp);
            AstInitArray* initp = NULL;
            if (AstInitArray* vscpnump = VN_CAST(fetchOutValueNull(vscp), InitArray)) {
                initp = vscpnump;
            } else if (AstInitArray* vscpnump = VN_CAST(fetchValueNull(vscp), InitArray)) {
                initp = vscpnump;
            } else {  // Assignment to unassigned variable, all bits are X
                // TODO generic initialization which builds X/arrays by recursion
                AstConst* outconstp = new AstConst(nodep->fileline(), AstConst::WidthedValue(),
                                                   basicp->widthMin(), 0);
                if (basicp->isZeroInit()) {
                    outconstp->num().setAllBits0();
                } else {
                    outconstp->num().setAllBitsX();
                }

                initp = new AstInitArray(nodep->fileline(), arrayp, outconstp);
                m_reclaimValuesp.push_back(initp);
            }
            uint32_t index = fetchConst(selp->bitp())->toUInt();
            AstNode* valuep = newTrackedClone(fetchValue(nodep->rhsp()));
            UINFO(9, "     set val["<<index<<"] = "<<valuep<<endl);
            // Values are in the "real" tree under the InitArray so can eventually extract it,
            // Not in the usual setValue (pointed to by user2/3p)
            initp->addIndexValuep(index, valuep);
            if (debug() >= 9) initp->dumpTree(cout, "-array-");
            assignOutValue(nodep, vscp, initp);
        }
    }
    void handleAssignSel(AstNodeAssign* nodep, AstSel* selp) {
        AstVarRef* varrefp = NULL;
        V3Number lsb(nodep);
        iterateAndNextNull(nodep->rhsp());  // Value to assign
        handleAssignSelRecurse(nodep, selp, varrefp/*ref*/, lsb/*ref*/, 0);
        if (!m_checkOnly && optimizable()) {
            UASSERT_OBJ(varrefp, nodep,
                        "Indicated optimizable, but no variable found on RHS of select");
            AstNode* vscp = varOrScope(varrefp);
            AstConst* outconstp = NULL;
            if (AstConst* vscpnump = fetchOutConstNull(vscp)) {
                outconstp = vscpnump;
            } else if (AstConst* vscpnump = fetchConstNull(vscp)) {
                outconstp = vscpnump;
            } else {  // Assignment to unassigned variable, all bits are X or 0
                outconstp = new AstConst(nodep->fileline(), AstConst::WidthedValue(),
                                         varrefp->varp()->widthMin(), 0);
                if (varrefp->varp()->basicp() && varrefp->varp()->basicp()->isZeroInit()) {
                    outconstp->num().setAllBits0();
                } else {
                    outconstp->num().setAllBitsX();
                }
            }
            outconstp->num().opSelInto(fetchConst(nodep->rhsp())->num(),
                                       lsb,
                                       selp->widthConst());
            assignOutValue(nodep, vscp, outconstp);
        }
    }
    void handleAssignSelRecurse(AstNodeAssign* nodep, AstSel* selp,
                                AstVarRef*& outVarrefpRef, V3Number& lsbRef,
                                int depth) {
        // Recurse down to find final variable being set (outVarrefp), with
        // lsb to be eventually set on lsbRef
        checkNodeInfo(selp);
        iterateAndNextNull(selp->lsbp());  // Bit index
        if (AstVarRef* varrefp = VN_CAST(selp->fromp(), VarRef)) {
            outVarrefpRef = varrefp;
            lsbRef = fetchConst(selp->lsbp())->num();
            return;  // And presumably still optimizable()
        } else if (AstSel* subselp = VN_CAST(selp->lhsp(), Sel)) {
            V3Number sublsb(nodep);
            handleAssignSelRecurse(nodep, subselp, outVarrefpRef, sublsb/*ref*/, depth+1);
            if (optimizable()) {
                lsbRef = sublsb;
                lsbRef.opAdd(sublsb, fetchConst(selp->lsbp())->num());
            }
        } else {
            clearOptimizable(nodep, "Select LHS isn't simple variable");
        }
    }

    virtual void visit(AstNodeAssign* nodep) VL_OVERRIDE {
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
        else if (AstArraySel* selp = VN_CAST(nodep->lhsp(), ArraySel)) {
            if (!m_params) { clearOptimizable(nodep, "LHS has select"); return; }
            handleAssignArray(nodep, selp);
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
                assignOutValue(nodep, vscp, fetchValue(nodep->rhsp()));
            }
        }
        m_inDlyAssign = false;
    }
    virtual void visit(AstArraySel* nodep) VL_OVERRIDE {
        checkNodeInfo(nodep);
        iterateChildren(nodep);
        if (AstInitArray* initp = VN_CAST(fetchValueNull(nodep->fromp()), InitArray)) {
            AstConst* indexp = fetchConst(nodep->bitp());
            uint32_t offset = indexp->num().toUInt();
            AstNode* itemp = initp->getIndexDefaultedValuep(offset);
            if (!itemp) {
                clearOptimizable(nodep, "Array initialization has too few elements, need element "
                                 +cvtToStr(offset));
            } else {
                setValue(nodep, itemp);
            }
        } else {
            clearOptimizable(nodep, "Array select of non-array");
        }
    }
    virtual void visit(AstBegin* nodep) VL_OVERRIDE {
        checkNodeInfo(nodep);
        iterateChildren(nodep);
    }
    virtual void visit(AstNodeCase* nodep) VL_OVERRIDE {
        if (jumpingOver(nodep)) return;
        UINFO(5, "   CASE "<<nodep<<endl);
        checkNodeInfo(nodep);
        if (m_checkOnly) {
            iterateChildren(nodep);
        } else if (optimizable()) {
            iterateAndNextNull(nodep->exprp());
            bool hit = false;
            for (AstCaseItem* itemp = nodep->itemsp();
                 itemp; itemp=VN_CAST(itemp->nextp(), CaseItem)) {
                if (!itemp->isDefault()) {
                    for (AstNode* ep = itemp->condsp(); ep; ep = ep->nextp()) {
                        if (hit) break;
                        iterateAndNextNull(ep);
                        if (optimizable()) {
                            V3Number match(nodep, 1);
                            match.opEq(fetchConst(nodep->exprp())->num(), fetchConst(ep)->num());
                            if (match.isNeqZero()) {
                                iterateAndNextNull(itemp->bodysp());
                                hit = true;
                            }
                        }
                    }
                }
            }
            // Else default match
            for (AstCaseItem* itemp = nodep->itemsp();
                 itemp; itemp = VN_CAST(itemp->nextp(), CaseItem)) {
                if (hit) break;
                if (!hit && itemp->isDefault()) {
                    iterateAndNextNull(itemp->bodysp());
                    hit = true;
                }
            }
        }
    }

    virtual void visit(AstCaseItem* nodep) VL_OVERRIDE {
        // Real handling is in AstNodeCase
        if (jumpingOver(nodep)) return;
        checkNodeInfo(nodep);
        iterateChildren(nodep);
    }

    virtual void visit(AstComment*) VL_OVERRIDE {}

    virtual void visit(AstJumpGo* nodep) VL_OVERRIDE {
        if (jumpingOver(nodep)) return;
        checkNodeInfo(nodep);
        if (!m_checkOnly) {
            UINFO(5, "   JUMP GO "<<nodep<<endl);
            m_jumpp = nodep;
        }
    }
    virtual void visit(AstJumpLabel* nodep) VL_OVERRIDE {
        if (jumpingOver(nodep)) return;
        checkNodeInfo(nodep);
        iterateChildren(nodep);
        if (m_jumpp && m_jumpp->labelp() == nodep) {
            UINFO(5, "   JUMP DONE "<<nodep<<endl);
            m_jumpp = NULL;
        }
    }
    virtual void visit(AstStop* nodep) VL_OVERRIDE {
        if (jumpingOver(nodep)) return;
        if (m_params) {  // This message seems better than an obscure $stop
            // The spec says $stop is just ignored, it seems evil to ignore assertions
            clearOptimizable(nodep, "$stop executed during function constification; maybe indicates assertion firing");
        }
        checkNodeInfo(nodep);
    }

    virtual void visit(AstNodeFor* nodep) VL_OVERRIDE {
        // Doing lots of Whiles is slow, so only for parameters
        UINFO(5, "   FOR "<<nodep<<endl);
        if (!m_params) { badNodeType(nodep); return; }
        checkNodeInfo(nodep);
        if (m_checkOnly) {
            iterateChildren(nodep);
        } else if (optimizable()) {
            int loops = 0;
            iterateAndNextNull(nodep->initsp());
            while (1) {
                UINFO(5, "    FOR-ITER "<<nodep<<endl);
                iterateAndNextNull(nodep->condp());
                if (!optimizable()) break;
                if (!fetchConst(nodep->condp())->num().isNeqZero()) {
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

    virtual void visit(AstWhile* nodep) VL_OVERRIDE {
        // Doing lots of Whiles is slow, so only for parameters
        if (jumpingOver(nodep)) return;
        UINFO(5, "   WHILE "<<nodep<<endl);
        if (!m_params) { badNodeType(nodep); return; }
        checkNodeInfo(nodep);
        if (m_checkOnly) {
            iterateChildren(nodep);
        } else if (optimizable()) {
            int loops = 0;
            while (1) {
                UINFO(5, "    WHILE-ITER "<<nodep<<endl);
                iterateAndNextNull(nodep->precondsp());
                if (jumpingOver(nodep)) break;
                iterateAndNextNull(nodep->condp());
                if (jumpingOver(nodep)) break;
                if (!optimizable()) break;
                if (!fetchConst(nodep->condp())->num().isNeqZero()) {
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

    virtual void visit(AstFuncRef* nodep) VL_OVERRIDE {
        if (jumpingOver(nodep)) return;
        if (!optimizable()) return;  // Accelerate
        UINFO(5, "   FUNCREF "<<nodep<<endl);
        if (!m_params) { badNodeType(nodep); return; }
        AstNodeFTask* funcp = VN_CAST(nodep->taskp(), NodeFTask);
        UASSERT_OBJ(funcp, nodep, "Not linked");
        if (m_params) { V3Width::widthParamsEdit(funcp); } VL_DANGLING(funcp);  // Make sure we've sized the function
        funcp = VN_CAST(nodep->taskp(), NodeFTask); UASSERT_OBJ(funcp, nodep, "Not linked");
        // Apply function call values to function
        V3TaskConnects tconnects = V3Task::taskConnects(nodep, nodep->taskp()->stmtsp());
        // Must do this in two steps, eval all params, then apply them
        // Otherwise chained functions may have the wrong results
        for (V3TaskConnects::iterator it = tconnects.begin(); it != tconnects.end(); ++it) {
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
        for (V3TaskConnects::iterator it = tconnects.begin(); it != tconnects.end(); ++it) {
            AstVar* portp = it->first;
            AstNode* pinp = it->second->exprp();
            if (pinp) {  // Else too few arguments in function call - ignore it
                // Apply value to the function
                if (!m_checkOnly && optimizable()) {
                    newValue(portp, fetchValue(pinp));
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
            UASSERT_OBJ(funcp->fvarp(), nodep, "Function reference points at non-function");
            newValue(nodep, fetchValue(funcp->fvarp()));
        }
    }

    virtual void visit(AstVar* nodep) VL_OVERRIDE {
        if (jumpingOver(nodep)) return;
        if (!m_params) { badNodeType(nodep); return; }
    }

    virtual void visit(AstScopeName* nodep) VL_OVERRIDE {
        if (jumpingOver(nodep)) return;
        // Ignore
    }

    virtual void visit(AstSFormatF* nodep) VL_OVERRIDE {
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
                        AstConst* constp = fetchConstNull(argp);
                        if (!constp) {
                            clearOptimizable(nodep, "Argument for $display like statement is not constant");
                            break;
                        }
                        string pformat = string("%") + pos[0];
                        result += constp->num().displayed(nodep, pformat);
                    } else {
                        switch (tolower(pos[0])) {
                        case '%': result += "%"; break;
                        case 'm':
                            // This happens prior to AstScope so we don't
                            // know the scope name. Leave the %m in place.
                            result += "%m";
                            break;
                        default:
                            clearOptimizable(nodep, "Unknown $display-like format code.");
                            break;
                        }
                    }
                }
            }

            AstConst* resultConstp = new AstConst(nodep->fileline(), AstConst::String(), result);
            setValue(nodep, resultConstp);
            m_reclaimValuesp.push_back(resultConstp);
        }
    }

    virtual void visit(AstDisplay* nodep) VL_OVERRIDE {
        if (jumpingOver(nodep)) return;
        if (!optimizable()) return;  // Accelerate
        iterateChildren(nodep);
        if (m_params) {
            AstConst* textp = fetchConst(nodep->fmtp());
            switch (nodep->displayType()) {
            case AstDisplayType::DT_DISPLAY:  // FALLTHRU
            case AstDisplayType::DT_INFO: v3warn(USERINFO, textp->name()); break;
            case AstDisplayType::DT_ERROR: v3warn(USERERROR, textp->name()); break;
            case AstDisplayType::DT_WARNING: v3warn(USERWARN, textp->name()); break;
            case AstDisplayType::DT_FATAL: v3warn(USERFATAL, textp->name()); break;
            case AstDisplayType::DT_WRITE:  // FALLTHRU
            default: clearOptimizable(nodep, "Unexpected display type");
            }
        }
    }

    // default
    // These types are definitely not reducible
    //   AstCoverInc, AstFinish,
    //   AstRand, AstTime, AstUCFunc, AstCCall, AstCStmt, AstUCStmt
    virtual void visit(AstNode* nodep) VL_OVERRIDE {
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
        UASSERT_OBJ(!m_jumpp, m_jumpp, "JumpGo branched to label that wasn't found");
    }
public:
    // CONSTRUCTORS
    SimulateVisitor() {
        // Note AstUser#InUse ensures only one invocation exists at once
        setMode(false, false, false);
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
        m_constFreeps = m_constAllps;
    }
    void mainTableCheck(AstNode* nodep) {
        setMode(true/*scoped*/, true/*checking*/, false/*params*/);
        mainGuts(nodep);
    }
    void mainTableEmulate(AstNode* nodep) {
        setMode(true/*scoped*/, false/*checking*/, false/*params*/);
        mainGuts(nodep);
    }
    void mainCheckTree(AstNode* nodep) {
        setMode(false/*scoped*/, true/*checking*/, false/*params*/);
        mainGuts(nodep);
    }
    void mainParamEmulate(AstNode* nodep) {
        setMode(false/*scoped*/, false/*checking*/, true/*params*/);
        mainGuts(nodep);
    }
    virtual ~SimulateVisitor() {
        for (ConstPile::iterator it = m_constAllps.begin();
             it != m_constAllps.end(); ++it) {
            for (ConstDeque::iterator it2 = it->second.begin();
                 it2 != it->second.end(); ++it2) {
                delete (*it2);
            }
        }
        for (std::deque<AstNode*>::iterator it = m_reclaimValuesp.begin();
             it != m_reclaimValuesp.end(); ++it) {
            delete (*it);
        }
        m_reclaimValuesp.clear();
        m_constFreeps.clear();
        m_constAllps.clear();
    }
};

#endif  // Guard
