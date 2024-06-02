// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Simulate code to determine output values/variables
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2024 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************
//
// void example_usage() {
//      SimulateVisitor simvis{false, false};
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

#ifndef VERILATOR_V3SIMULATE_H_
#define VERILATOR_V3SIMULATE_H_

#include "config_build.h"
#include "verilatedos.h"

#include "V3Ast.h"
#include "V3AstUserAllocator.h"
#include "V3Error.h"
#include "V3Task.h"
#include "V3Width.h"

#include <deque>
#include <sstream>
#include <stack>
#include <string>
#include <unordered_map>
#include <vector>

//============================================================================

//######################################################################
// Simulate class functions

class SimStackNode final {
public:
    // MEMBERS
    AstFuncRef* const m_funcp;
    V3TaskConnects* const m_tconnects;
    // CONSTRUCTORS
    SimStackNode(AstFuncRef* funcp, V3TaskConnects* tconnects)
        : m_funcp{funcp}
        , m_tconnects{tconnects} {}
    ~SimStackNode() = default;
};

class SimulateVisitor VL_NOT_FINAL : public VNVisitorConst {
    // Simulate a node tree, returning value of variables
    // Two major operating modes:
    //   Test the tree to see if it is conformant
    //   Given a set of input values, find the output values
    // Both are done in this same visitor to reduce risk; if a visitor
    // is missing, we will not apply the optimization, rather then bomb.

private:
    // NODE STATE
    // Cleared on each always/assignw
    const VNUser1InUse m_inuser1;

    // AstVar/AstVarScope::user1p()     -> See AuxAstVar via m_varAux
    // AstConst::user1()    -> bool. This AstConst (allocated by this class) is in use

    enum VarUsage : uint8_t { VU_NONE = 0, VU_LV = 1, VU_RV = 2, VU_LVDLY = 4 };

    struct AuxVariable final {
        // Checking:
        //  Set true to indicate tracking as lvalue/rvalue
        uint8_t usage = VU_NONE;
        // Simulating:
        //  Output value of variable (delayed assignments)
        AstNodeExpr* outValuep = nullptr;
        //  Input value of variable or node (and output for non-delayed assignments)
        AstNodeExpr* valuep = nullptr;
    };

    AstUser1Allocator<AstNode, AuxVariable> m_varAux;

    // STATE
    // Major mode
    bool m_checkOnly;  ///< Checking only (no simulation) mode
    bool m_scoped;  ///< Running with AstVarScopes instead of AstVars
    bool m_params;  ///< Doing parameter propagation
    // Checking:
    string m_whyNotOptimizable;  ///< String explaining why not optimizable or nullptr to optimize
    AstNode* m_whyNotNodep;  ///< First node not optimizable
    bool m_anyAssignDly;  ///< True if found a delayed assignment
    bool m_anyAssignComb;  ///< True if found a non-delayed assignment
    bool m_inDlyAssign;  ///< Under delayed assignment
    bool m_isOutputter;  // Creates output
    int m_instrCount;  ///< Number of nodes
    int m_dataCount;  ///< Bytes of data
    AstJumpGo* m_jumpp = nullptr;  ///< Jump label we're branching from
    // Simulating:
    std::unordered_map<const AstNodeDType*, std::deque<AstConst*>>
        m_constps;  ///< Lists of all AstConst* allocated per dtype
    std::vector<SimStackNode*> m_callStack;  ///< Call stack for verbose error messages

    // Cleanup
    // V3Numbers that represents strings are a bit special and the API for
    // V3Number does not allow changing them.
    std::vector<AstNode*> m_reclaimValuesp;  // List of allocated string numbers

    // Note level 8&9 include debugging each simulation value
    VL_DEFINE_DEBUG_FUNCTIONS;

    // Potentially very slow, intended for debugging
    string prettyNumber(const V3Number* nump, AstNodeDType* dtypep) {
        if (AstRefDType* const refdtypep = VN_CAST(dtypep, RefDType)) {  //
            dtypep = refdtypep->skipRefp();
        }
        if (AstNodeUOrStructDType* const stp = VN_CAST(dtypep, NodeUOrStructDType)) {
            if (stp->packed()) {
                std::ostringstream out;
                out << "'{";
                for (AstMemberDType* itemp = stp->membersp(); itemp;
                     itemp = VN_AS(itemp->nextp(), MemberDType)) {
                    const int width = itemp->width();
                    const int lsb = itemp->lsb();
                    const int msb = lsb + width - 1;
                    V3Number fieldNum{nump, width};
                    fieldNum.opSel(*nump, msb, lsb);
                    out << itemp->name() << ": ";
                    if (AstNodeDType* const childTypep = itemp->subDTypep()) {
                        out << prettyNumber(&fieldNum, childTypep);
                    } else {
                        out << fieldNum;
                    }
                    if (itemp->nextp()) out << ", ";
                }
                out << "}";
                return out.str();
            }
        } else if (const AstPackArrayDType* const arrayp = VN_CAST(dtypep, PackArrayDType)) {
            if (AstNodeDType* const childTypep = arrayp->subDTypep()) {
                std::ostringstream out;
                out << "[";
                const int arrayElements = arrayp->elementsConst();
                for (int element = 0; element < arrayElements; ++element) {
                    const int width = childTypep->width();
                    const int lsb = width * element;
                    const int msb = lsb + width - 1;
                    V3Number fieldNum{nump, width};
                    fieldNum.opSel(*nump, msb, lsb);
                    const int arrayElem = arrayp->lo() + element;
                    out << arrayElem << " = " << prettyNumber(&fieldNum, childTypep);
                    if (element < arrayElements - 1) out << ", ";
                }
                out << "]";
                return out.str();
            }
        }
        return nump->ascii();
    }

    // Checking METHODS
public:
    /// Call other-this function on all new *non-constant* var references
    virtual void varRefCb(AstVarRef* nodep) {}

    void clearOptimizable(AstNode* nodep /*null ok*/, const string& why) {
        //  Something bad found.  optimizable() will return false,
        //  and fetchConst should not be called or it may assert.
        if (!m_whyNotNodep) {
            m_whyNotNodep = nodep;
            if (debug() >= 5) {
                UINFO(0, "Clear optimizable: " << why);
                if (nodep) std::cout << ": " << nodep;
                std::cout << std::endl;
            }
            m_whyNotOptimizable = why;
            std::ostringstream stack;
            for (const auto& callstack : vlstd::reverse_view(m_callStack)) {
                AstFuncRef* const funcp = callstack->m_funcp;
                stack << "\n        " << funcp->fileline() << "... Called from '"
                      << funcp->prettyName() << "()' with parameters:";
                V3TaskConnects* tconnects = callstack->m_tconnects;
                for (V3TaskConnects::iterator conIt = tconnects->begin();
                     conIt != tconnects->end(); ++conIt) {
                    AstVar* const portp = conIt->first;
                    AstNodeExpr* const pinp = conIt->second->exprp();
                    AstNodeDType* const dtypep = pinp->dtypep();
                    if (AstConst* const valp = fetchConstNull(pinp)) {
                        stack << "\n           " << portp->prettyName() << " = "
                              << prettyNumber(&valp->num(), dtypep);
                    }
                }
            }
            m_whyNotOptimizable += stack.str();
        }
    }
    bool optimizable() const { return m_whyNotNodep == nullptr; }
    string whyNotMessage() const { return m_whyNotOptimizable; }
    AstNode* whyNotNodep() const { return m_whyNotNodep; }

    bool isAssignDly() const { return m_anyAssignDly; }
    bool isOutputter() const { return m_isOutputter; }
    int instrCount() const { return m_instrCount; }
    int dataCount() const { return m_dataCount; }

    // Simulation METHODS
private:
    AstConst* allocConst(AstNode* nodep) {
        // Save time - kept a list of allocated but unused values
        // It would be more efficient to do this by size, but the extra accounting
        // slows things down more than we gain.
        AstConst* constp;
        // Grab free list corresponding to this dtype
        std::deque<AstConst*>& freeList = m_constps[nodep->dtypep()];
        bool allocNewConst = true;
        if (!freeList.empty()) {
            constp = freeList.front();
            if (!constp->user1()) {
                // Front of free list is free, reuse it (otherwise allocate new node)
                allocNewConst = false;  // No need to allocate
                // Mark the AstConst node as used, and move it to the back of the free list. This
                // ensures that when all AstConst instances within the list are used, then the
                // front of the list will be marked as used, in which case the enclosing 'if' will
                // fail and we fall back to allocation.
                constp->user1(1);
                freeList.pop_front();
                freeList.push_back(constp);
                // configure const
                constp->num().nodep(nodep);
            }
        }
        if (allocNewConst) {
            // Need to allocate new constant
            constp = new AstConst{nodep->fileline(), AstConst::DTyped{}, nodep->dtypep()};
            // Mark as in use, add to free list for later reuse
            constp->user1(1);
            freeList.push_back(constp);
        }
        return constp;
    }

public:
    void newValue(AstNode* nodep, const AstNodeExpr* valuep) {
        if (const AstConst* const constp = VN_CAST(valuep, Const)) {
            newConst(nodep)->num().opAssign(constp->num());
        } else if (fetchValueNull(nodep) != valuep) {
            // const_cast, as clonep() is set on valuep, but nothing should care
            setValue(nodep, newTrackedClone(const_cast<AstNodeExpr*>(valuep)));
        }
    }
    void newOutValue(AstNode* nodep, const AstNodeExpr* valuep) {
        if (const AstConst* const constp = VN_CAST(valuep, Const)) {
            newOutConst(nodep)->num().opAssign(constp->num());
        } else if (fetchOutValueNull(nodep) != valuep) {
            // const_cast, as clonep() is set on valuep, but nothing should care
            setOutValue(nodep, newTrackedClone(const_cast<AstNodeExpr*>(valuep)));
        }
    }

private:
    AstNodeExpr* newTrackedClone(AstNodeExpr* nodep) {
        AstNodeExpr* const newp = nodep->cloneTree(false);
        m_reclaimValuesp.push_back(newp);
        return newp;
    }
    AstConst* newConst(AstNode* nodep) {
        // Set a constant value for this node
        if (!VN_IS(m_varAux(nodep).valuep, Const)) {
            AstConst* const constp = allocConst(nodep);
            setValue(nodep, constp);
            return constp;
        } else {
            return fetchConst(nodep);
        }
    }
    AstConst* newOutConst(AstNode* nodep) {
        // Set a var-output constant value for this node
        if (!VN_IS(m_varAux(nodep).outValuep, Const)) {
            AstConst* const constp = allocConst(nodep);
            setOutValue(nodep, constp);
            return constp;
        } else {
            return fetchOutConst(nodep);
        }
    }

public:
    AstNodeExpr* fetchValueNull(AstNode* nodep) { return m_varAux(nodep).valuep; }

private:
    AstNodeExpr* fetchOutValueNull(AstNode* nodep) { return m_varAux(nodep).outValuep; }
    AstConst* fetchConstNull(AstNode* nodep) { return VN_CAST(fetchValueNull(nodep), Const); }
    AstConst* fetchOutConstNull(AstNode* nodep) {
        return VN_CAST(fetchOutValueNull(nodep), Const);
    }
    AstNodeExpr* fetchValue(AstNode* nodep) {
        AstNodeExpr* const valuep = fetchValueNull(nodep);
        UASSERT_OBJ(valuep, nodep, "No value found for node.");
        // UINFO(9, "     fetch val " << *valuep << " on " << nodep << endl);
        return valuep;
    }
    AstConst* fetchConst(AstNode* nodep) {
        AstConst* const constp = fetchConstNull(nodep);
        UASSERT_OBJ(constp, nodep, "No value found for node.");
        // UINFO(9, "     fetch num " << *constp << " on " << nodep << endl);
        return constp;
    }
    AstConst* fetchOutConst(AstNode* nodep) {
        AstConst* const constp = fetchOutConstNull(nodep);
        UASSERT_OBJ(constp, nodep, "No value found for node.");
        return constp;
    }

public:
    V3Number* fetchNumberNull(AstNode* nodep) {
        AstConst* const constp = fetchConstNull(nodep);
        if (constp) return &constp->num();
        return nullptr;
    }
    V3Number* fetchOutNumberNull(AstNode* nodep) {
        AstConst* const constp = fetchOutConstNull(nodep);
        if (constp) return &constp->num();
        return nullptr;
    }

private:
    void setValue(AstNode* nodep, AstNodeExpr* valuep) {
        UASSERT_OBJ(valuep, nodep, "Simulate setting null value");
        UINFO(9, "     set val " << valuep->name() << " on " << nodep << endl);
        m_varAux(nodep).valuep = valuep;
    }
    void setOutValue(AstNode* nodep, AstNodeExpr* valuep) {
        UASSERT_OBJ(valuep, nodep, "Simulate setting null value");
        UINFO(9, "     set oval " << valuep->name() << " on " << nodep << endl);
        m_varAux(nodep).outValuep = valuep;
    }

    void checkNodeInfo(AstNode* nodep, bool ignorePredict = false) {
        if (m_checkOnly) {
            m_instrCount += nodep->instrCount();
            m_dataCount += nodep->width();
        }
        if (!ignorePredict && !nodep->isPredictOptimizable()) {
            // UINFO(9, "     !predictopt " << nodep << endl);
            clearOptimizable(nodep, "Isn't predictable");
        }
        if (nodep->isOutputter()) m_isOutputter = true;
    }

    void knownBadNodeType(AstNode* nodep) {
        // Call for node types we know we can't handle
        checkNodeInfo(nodep);
        if (optimizable()) {
            clearOptimizable(nodep, "Known unhandled node type "s + nodep->typeName());
        }
    }
    void badNodeType(AstNode* nodep) {
        // Call for default node types, or other node types we don't know how to handle
        checkNodeInfo(nodep);
        if (optimizable()) {
            // Hmm, what is this then?
            // In production code, we'll just not optimize.  It should be fixed though.
            clearOptimizable(nodep,
                             "Unknown node type, perhaps missing visitor in SimulateVisitor");
#ifdef VL_DEBUG
            static std::set<VNType> s_typePrinted;
            const auto pair = s_typePrinted.emplace(nodep->type());
            if (pair.second)
                UINFO(0,
                      "Unknown node type in SimulateVisitor: " << nodep->prettyTypeName() << endl);
#endif
        }
    }

    AstNode* varOrScope(AstVarRef* nodep) const {
        AstNode* vscp;
        if (m_scoped) {
            vscp = nodep->varScopep();
        } else {
            vscp = nodep->varp();
        }
        UASSERT_OBJ(vscp, nodep, "Not linked");
        return vscp;
    }
    bool jumpingOver(const AstNode* nodep) const {
        // True to jump over this node - all visitors must call this up front
        return (m_jumpp && m_jumpp->labelp() != nodep);
    }
    void assignOutValue(AstNodeAssign* nodep, AstNode* vscp, const AstNodeExpr* valuep) {
        if (VN_IS(nodep, AssignDly)) {
            // Don't do setValue, as value isn't yet visible to following statements
            newOutValue(vscp, valuep);
        } else {
            newValue(vscp, valuep);
            newOutValue(vscp, valuep);
        }
    }

    // VISITORS
    void visit(AstAlways* nodep) override {
        if (jumpingOver(nodep)) return;
        checkNodeInfo(nodep);
        iterateChildrenConst(nodep);
    }
    void visit(AstSenTree* nodep) override {
        // Sensitivities aren't inputs per se; we'll keep our tree under the same sens.
    }
    void visit(AstVarRef* nodep) override {
        if (jumpingOver(nodep)) return;
        if (!optimizable()) return;  // Accelerate
        UASSERT_OBJ(nodep->varp(), nodep, "Unlinked");
        iterateChildrenConst(nodep->varp());
        AstNode* const vscp = varOrScope(nodep);

        // We can't have non-delayed assignments with same value on LHS and RHS
        // as we don't figure out variable ordering.
        // Delayed is OK though, as we'll decode the next state separately.
        if (!VN_IS(nodep->varp()->dtypeSkipRefp(), BasicDType)
            && !VN_IS(nodep->varp()->dtypeSkipRefp(), PackArrayDType)
            && !VN_IS(nodep->varp()->dtypeSkipRefp(), UnpackArrayDType)
            && !VN_IS(nodep->varp()->dtypeSkipRefp(), NodeUOrStructDType))
            clearOptimizable(nodep, "Array references/not basic");
        if (nodep->access().isWriteOrRW()) {
            if (m_inDlyAssign) {
                if (!(m_varAux(vscp).usage & VU_LVDLY)) {
                    m_varAux(vscp).usage |= VU_LVDLY;
                    if (m_checkOnly) varRefCb(nodep);
                }
            } else {  // nondly asn
                if (!(m_varAux(vscp).usage & VU_LV)) {
                    if (!m_params && (m_varAux(vscp).usage & VU_RV)) {
                        clearOptimizable(nodep, "Var read & write");
                    }
                    m_varAux(vscp).usage |= VarUsage::VU_LV;
                    if (m_checkOnly) varRefCb(nodep);
                }
            }
        }
        if (nodep->access().isReadOrRW()) {
            if (!(m_varAux(vscp).usage & VU_RV)) {
                if (!m_params && (m_varAux(vscp).usage & VU_LV)) {
                    clearOptimizable(nodep, "Var write & read");
                }
                m_varAux(vscp).usage |= VU_RV;
                const bool varIsConst = (nodep->varp()->isConst() || nodep->varp()->isParam())
                                        && nodep->varp()->valuep();
                AstNodeExpr* const valuep
                    = varIsConst ? fetchValueNull(nodep->varp()->valuep()) : nullptr;
                // Propagate PARAM constants for constant function analysis
                if (varIsConst && valuep) {
                    if (!m_checkOnly && optimizable()) newValue(vscp, valuep);
                } else {
                    if (m_checkOnly) varRefCb(nodep);
                }
            }
        }
        if (!m_checkOnly && optimizable()) {  // simulating
            UASSERT_OBJ(nodep->access().isReadOnly(), nodep,
                        "LHS varref should be handled in AstAssign visitor.");
            {
                // Return simulation value - copy by reference instead of value for speed
                AstNodeExpr* valuep = fetchValueNull(vscp);
                if (!valuep) {
                    if (m_params) {
                        clearOptimizable(
                            nodep, "Language violation: reference to non-function-local variable");
                    } else {
                        nodep->v3fatalSrc(
                            "Variable value should have been set before any visitor called.");
                    }
                    valuep = allocConst(nodep);  // Any value; just so recover from error
                }
                setValue(nodep, valuep);
            }
        }
    }
    void visit(AstVarXRef* nodep) override {
        if (jumpingOver(nodep)) return;
        if (m_scoped) {
            badNodeType(nodep);
            return;
        } else {
            clearOptimizable(nodep, "Language violation: Dotted hierarchical references not "
                                    "allowed in constant functions");
        }
    }
    void visit(AstNodeFTask* nodep) override {
        if (jumpingOver(nodep)) return;
        if (!m_params) {
            badNodeType(nodep);
            return;
        }
        if (nodep->dpiImport()) {
            if (m_params) {
                nodep->v3error("Constant function may not be DPI import (IEEE 1800-2023 13.4.3)");
            }
            clearOptimizable(nodep, "DPI import functions aren't simulatable");
        }
        if (nodep->underGenerate()) {
            nodep->v3error(
                "Constant function may not be declared under generate (IEEE 1800-2023 13.4.3)");
            clearOptimizable(nodep, "Constant function called under generate");
        }
        checkNodeInfo(nodep);
        iterateChildrenConst(nodep);
    }
    void visit(AstInitialStatic* nodep) override {
        if (jumpingOver(nodep)) return;
        if (!m_params) {
            badNodeType(nodep);
            return;
        }
        checkNodeInfo(nodep);
        iterateChildrenConst(nodep);
    }
    void visit(AstNodeIf* nodep) override {
        if (jumpingOver(nodep)) return;
        UINFO(5, "   IF " << nodep << endl);
        checkNodeInfo(nodep);
        if (m_checkOnly) {
            iterateChildrenConst(nodep);
        } else {
            iterateAndNextConstNull(nodep->condp());
            if (optimizable()) {
                if (fetchConst(nodep->condp())->num().isNeqZero()) {
                    iterateAndNextConstNull(nodep->thensp());
                } else {
                    iterateAndNextConstNull(nodep->elsesp());
                }
            }
        }
    }
    void visit(AstConst* nodep) override {
        checkNodeInfo(nodep);
        if (!m_checkOnly && optimizable()) newValue(nodep, nodep);
    }
    void visit(AstInitArray* nodep) override {
        checkNodeInfo(nodep);
        if (!m_checkOnly && optimizable()) newValue(nodep, nodep);
    }
    void visit(AstEnumItemRef* nodep) override {
        checkNodeInfo(nodep);
        UASSERT_OBJ(nodep->itemp(), nodep, "Not linked");
        if (!m_checkOnly && optimizable()) {
            AstNode* const valuep = nodep->itemp()->valuep();
            if (valuep) {
                iterateAndNextConstNull(valuep);
                if (!optimizable()) return;
                newValue(nodep, fetchValue(valuep));
            } else {
                clearOptimizable(nodep, "No value found for enum item");  // LCOV_EXCL_LINE
            }
        }
    }
    void visit(AstNodeUniop* nodep) override {
        if (!optimizable()) return;  // Accelerate
        checkNodeInfo(nodep);
        iterateChildrenConst(nodep);
        if (!m_checkOnly && optimizable()) {
            nodep->numberOperate(newConst(nodep)->num(), fetchConst(nodep->lhsp())->num());
        }
    }
    void visit(AstNodeBiop* nodep) override {
        if (!optimizable()) return;  // Accelerate
        checkNodeInfo(nodep);
        iterateChildrenConst(nodep);
        if (!m_checkOnly && optimizable()) {
            nodep->numberOperate(newConst(nodep)->num(), fetchConst(nodep->lhsp())->num(),
                                 fetchConst(nodep->rhsp())->num());
        }
    }
    void visit(AstNodeTriop* nodep) override {
        if (!optimizable()) return;  // Accelerate
        checkNodeInfo(nodep);
        iterateChildrenConst(nodep);
        if (!m_checkOnly && optimizable()) {
            nodep->numberOperate(newConst(nodep)->num(), fetchConst(nodep->lhsp())->num(),
                                 fetchConst(nodep->rhsp())->num(),
                                 fetchConst(nodep->thsp())->num());
        }
    }
    void visit(AstNodeQuadop* nodep) override {
        if (!optimizable()) return;  // Accelerate
        checkNodeInfo(nodep);
        iterateChildrenConst(nodep);
        if (!m_checkOnly && optimizable()) {
            nodep->numberOperate(newConst(nodep)->num(), fetchConst(nodep->lhsp())->num(),
                                 fetchConst(nodep->rhsp())->num(),
                                 fetchConst(nodep->thsp())->num(),
                                 fetchConst(nodep->fhsp())->num());
        }
    }
    void visit(AstLogAnd* nodep) override {
        // Need to short circuit
        if (!optimizable()) return;  // Accelerate
        checkNodeInfo(nodep);
        if (m_checkOnly) {
            iterateChildrenConst(nodep);
        } else {
            iterateConst(nodep->lhsp());
            if (!optimizable()) return;
            if (fetchConst(nodep->lhsp())->num().isNeqZero()) {
                iterateConst(nodep->rhsp());
                if (!optimizable()) return;
                newValue(nodep, fetchValue(nodep->rhsp()));
            } else {
                newValue(nodep, fetchValue(nodep->lhsp()));  // a zero
            }
        }
    }
    void visit(AstLogOr* nodep) override {
        // Need to short circuit
        if (!optimizable()) return;  // Accelerate
        checkNodeInfo(nodep);
        if (m_checkOnly) {
            iterateChildrenConst(nodep);
        } else {
            iterateConst(nodep->lhsp());
            if (!optimizable()) return;
            if (fetchConst(nodep->lhsp())->num().isNeqZero()) {
                newValue(nodep, fetchValue(nodep->lhsp()));  // a one
            } else {
                iterateConst(nodep->rhsp());
                if (!optimizable()) return;
                newValue(nodep, fetchValue(nodep->rhsp()));
            }
        }
    }
    void visit(AstLogIf* nodep) override {
        // Need to short circuit, same as (!A || B)
        if (!optimizable()) return;  // Accelerate
        checkNodeInfo(nodep);
        if (m_checkOnly) {
            iterateChildrenConst(nodep);
        } else {
            iterateConst(nodep->lhsp());
            if (!optimizable()) return;
            if (fetchConst(nodep->lhsp())->num().isEqZero()) {
                const AstConst cnst{nodep->fileline(), AstConst::WidthedValue{}, 1, 1};  // a one
                newValue(nodep, &cnst);  // a one
            } else {
                iterateConst(nodep->rhsp());
                if (!optimizable()) return;
                newValue(nodep, fetchValue(nodep->rhsp()));
            }
        }
    }
    void visit(AstNodeCond* nodep) override {
        // We could use above visit(AstNodeTriop), but need to do short circuiting.
        // It's also slower even O(n^2) to evaluate both sides when we
        // really only need to evaluate one side.
        if (!optimizable()) return;  // Accelerate
        checkNodeInfo(nodep);
        if (m_checkOnly) {
            iterateChildrenConst(nodep);
        } else {
            iterateConst(nodep->condp());
            if (!optimizable()) return;
            if (fetchConst(nodep->condp())->num().isNeqZero()) {
                iterateConst(nodep->thenp());
                if (!optimizable()) return;
                newValue(nodep, fetchValue(nodep->thenp()));
            } else {
                iterateConst(nodep->elsep());
                if (!optimizable()) return;
                newValue(nodep, fetchValue(nodep->elsep()));
            }
        }
    }

    void handleAssignArray(AstNodeAssign* nodep, AstArraySel* selp) {
        iterateAndNextConstNull(nodep->rhsp());  // Value to assign
        // At present we only handle single dimensional assignments
        // To do better, we need the concept of lvalues, or similar, to know where/how to insert
        checkNodeInfo(selp);
        iterateAndNextConstNull(selp->bitp());  // Bit index
        AstVarRef* const varrefp = VN_CAST(selp->fromp(), VarRef);
        if (!varrefp) {
            clearOptimizable(nodep, "Array select LHS isn't simple variable");
            return;
        }
        AstUnpackArrayDType* const arrayp
            = VN_AS(varrefp->varp()->dtypeSkipRefp(), UnpackArrayDType);
        UASSERT_OBJ(arrayp, nodep, "Array select of non-array dtype");
        AstBasicDType* const basicp = VN_CAST(arrayp->subDTypep()->skipRefp(), BasicDType);
        if (!basicp) {
            clearOptimizable(nodep, "Array of non-basic dtype (e.g. array-of-array)");
            return;
        }
        if (!m_checkOnly && optimizable()) {
            AstNode* const vscp = varOrScope(varrefp);
            AstInitArray* initp = nullptr;
            if (AstInitArray* const vscpnump = VN_CAST(fetchOutValueNull(vscp), InitArray)) {
                initp = vscpnump;
            } else if (AstInitArray* const vscpnump = VN_CAST(fetchValueNull(vscp), InitArray)) {
                initp = vscpnump;
            } else {  // Assignment to unassigned variable, all bits are X
                // TODO generic initialization which builds X/arrays by recursion
                AstConst* const outconstp = new AstConst{
                    nodep->fileline(), AstConst::WidthedValue{}, basicp->widthMin(), 0};
                if (basicp->isZeroInit()) {
                    outconstp->num().setAllBits0();
                } else {
                    outconstp->num().setAllBitsX();
                }

                initp = new AstInitArray{nodep->fileline(), arrayp, outconstp};
                m_reclaimValuesp.push_back(initp);
            }
            const uint32_t index = fetchConst(selp->bitp())->toUInt();
            AstNodeExpr* const valuep = newTrackedClone(fetchValue(nodep->rhsp()));
            UINFO(9, "     set val[" << index << "] = " << valuep << endl);
            // Values are in the "real" tree under the InitArray so can eventually extract it,
            // Not in the usual setValue (via m_varAux)
            initp->addIndexValuep(index, valuep);
            if (debug() >= 9) initp->dumpTree("-  array: ");
            assignOutValue(nodep, vscp, initp);
        }
    }
    void handleAssignSel(AstNodeAssign* nodep, AstSel* selp) {
        AstVarRef* varrefp = nullptr;
        V3Number lsb{nodep};
        iterateAndNextConstNull(nodep->rhsp());  // Value to assign
        handleAssignSelRecurse(nodep, selp, varrefp /*ref*/, lsb /*ref*/, 0);
        if (!m_checkOnly && optimizable()) {
            UASSERT_OBJ(varrefp, nodep,
                        "Indicated optimizable, but no variable found on RHS of select");
            AstNode* const vscp = varOrScope(varrefp);
            AstConst* outconstp = nullptr;
            if (AstConst* const vscpnump = fetchOutConstNull(vscp)) {
                outconstp = vscpnump;
            } else if (AstConst* const vscpnump = fetchConstNull(vscp)) {
                outconstp = vscpnump;
            } else {  // Assignment to unassigned variable, all bits are X or 0
                outconstp = new AstConst{nodep->fileline(), AstConst::WidthedValue{},
                                         varrefp->varp()->widthMin(), 0};
                if (varrefp->varp()->basicp() && varrefp->varp()->basicp()->isZeroInit()) {
                    outconstp->num().setAllBits0();
                } else {
                    outconstp->num().setAllBitsX();
                }
            }
            outconstp->num().opSelInto(fetchConst(nodep->rhsp())->num(), lsb, selp->widthConst());
            assignOutValue(nodep, vscp, outconstp);
        }
    }
    void handleAssignSelRecurse(AstNodeAssign* nodep, AstSel* selp, AstVarRef*& outVarrefpRef,
                                V3Number& lsbRef, int depth) {
        // Recurse down to find final variable being set (outVarrefp), with
        // lsb to be eventually set on lsbRef
        checkNodeInfo(selp);
        iterateAndNextConstNull(selp->lsbp());  // Bit index
        if (AstVarRef* const varrefp = VN_CAST(selp->fromp(), VarRef)) {
            outVarrefpRef = varrefp;
            lsbRef = fetchConst(selp->lsbp())->num();
            return;  // And presumably still optimizable()
        } else if (AstSel* const subselp = VN_CAST(selp->fromp(), Sel)) {
            V3Number sublsb{nodep};
            handleAssignSelRecurse(nodep, subselp, outVarrefpRef, sublsb /*ref*/, depth + 1);
            if (optimizable()) {
                lsbRef = sublsb;
                lsbRef.opAdd(sublsb, fetchConst(selp->lsbp())->num());
            }
        } else {
            clearOptimizable(nodep, "Select LHS isn't simple variable");
        }
    }

    void visit(AstNodeAssign* nodep) override {
        if (jumpingOver(nodep)) return;
        if (!optimizable()) return;  // Accelerate
        checkNodeInfo(nodep);

        VL_RESTORER(m_inDlyAssign);

        if (VN_IS(nodep, AssignForce)) {
            clearOptimizable(nodep, "Force");
        } else if (VN_IS(nodep, AssignDly)) {
            if (m_anyAssignComb) clearOptimizable(nodep, "Mix of dly/non-dly assigns");
            m_anyAssignDly = true;
            m_inDlyAssign = true;
        } else {
            if (m_anyAssignDly) clearOptimizable(nodep, "Mix of dly/non-dly assigns");
            m_anyAssignComb = true;
        }

        if (AstSel* const selp = VN_CAST(nodep->lhsp(), Sel)) {
            if (!m_params) {
                clearOptimizable(nodep, "LHS has select");
                return;
            }
            handleAssignSel(nodep, selp);
        } else if (AstArraySel* const selp = VN_CAST(nodep->lhsp(), ArraySel)) {
            if (!m_params) {
                clearOptimizable(nodep, "LHS has select");
                return;
            }
            handleAssignArray(nodep, selp);
        } else if (!VN_IS(nodep->lhsp(), VarRef)) {
            clearOptimizable(nodep, "LHS isn't simple variable");
        } else if (m_checkOnly) {
            iterateChildrenConst(nodep);
        } else if (optimizable()) {
            iterateAndNextConstNull(nodep->rhsp());
            if (!optimizable()) return;
            AstNode* const vscp = varOrScope(VN_CAST(nodep->lhsp(), VarRef));
            assignOutValue(nodep, vscp, fetchValue(nodep->rhsp()));
        }
    }
    void visit(AstArraySel* nodep) override {
        checkNodeInfo(nodep);
        iterateChildrenConst(nodep);
        if (AstInitArray* const initp = VN_CAST(fetchValueNull(nodep->fromp()), InitArray)) {
            AstConst* const indexp = fetchConst(nodep->bitp());
            const uint32_t offset = indexp->num().toUInt();
            AstNodeExpr* const itemp = initp->getIndexDefaultedValuep(offset);
            if (!itemp) {
                clearOptimizable(nodep, "Array initialization has too few elements, need element "
                                            + cvtToStr(offset));
            } else {
                setValue(nodep, itemp);
            }
        } else {
            clearOptimizable(nodep, "Array select of non-array");
        }
    }
    void visit(AstBegin* nodep) override {
        checkNodeInfo(nodep);
        iterateChildrenConst(nodep);
    }
    void visit(AstNodeCase* nodep) override {
        if (jumpingOver(nodep)) return;
        UINFO(5, "   CASE " << nodep << endl);
        checkNodeInfo(nodep);
        if (m_checkOnly) {
            iterateChildrenConst(nodep);
        } else if (optimizable()) {
            iterateAndNextConstNull(nodep->exprp());
            bool hit = false;
            for (AstCaseItem* itemp = nodep->itemsp(); itemp;
                 itemp = VN_AS(itemp->nextp(), CaseItem)) {
                if (!itemp->isDefault()) {
                    for (AstNode* ep = itemp->condsp(); ep; ep = ep->nextp()) {
                        if (hit) break;
                        iterateAndNextConstNull(ep);
                        if (optimizable()) {
                            V3Number match{nodep, 1};
                            match.opEq(fetchConst(nodep->exprp())->num(), fetchConst(ep)->num());
                            if (match.isNeqZero()) {
                                iterateAndNextConstNull(itemp->stmtsp());
                                hit = true;
                            }
                        }
                    }
                }
            }
            // Else default match
            for (AstCaseItem* itemp = nodep->itemsp(); itemp;
                 itemp = VN_AS(itemp->nextp(), CaseItem)) {
                if (hit) break;
                if (!hit && itemp->isDefault()) {
                    iterateAndNextConstNull(itemp->stmtsp());
                    hit = true;
                }
            }
        }
    }

    void visit(AstCaseItem* nodep) override {
        // Real handling is in AstNodeCase
        if (jumpingOver(nodep)) return;
        checkNodeInfo(nodep);
        iterateChildrenConst(nodep);
    }

    void visit(AstComment*) override {}

    void visit(AstStmtExpr* nodep) override {
        if (jumpingOver(nodep)) return;
        checkNodeInfo(nodep);
        iterateChildrenConst(nodep);
    }
    void visit(AstExprStmt* nodep) override {
        if (jumpingOver(nodep)) return;
        checkNodeInfo(nodep);
        iterateAndNextConstNull(nodep->stmtsp());
        if (!optimizable()) return;
        iterateAndNextConstNull(nodep->resultp());
        if (!optimizable()) return;
        if (!m_checkOnly) newValue(nodep, fetchValue(nodep->resultp()));
    }

    void visit(AstJumpBlock* nodep) override {
        if (jumpingOver(nodep)) return;
        iterateChildrenConst(nodep);
    }
    void visit(AstJumpGo* nodep) override {
        if (jumpingOver(nodep)) return;
        checkNodeInfo(nodep);
        if (!m_checkOnly) {
            UINFO(5, "   JUMP GO " << nodep << endl);
            m_jumpp = nodep;
        }
    }
    void visit(AstJumpLabel* nodep) override {
        // This only supports forward jumps. That's all we make at present,
        // AstJumpGo::broken uses brokeExistsBelow() to check this.
        if (jumpingOver(nodep)) return;
        checkNodeInfo(nodep);
        iterateChildrenConst(nodep);
        if (m_jumpp && m_jumpp->labelp() == nodep) {
            UINFO(5, "   JUMP DONE " << nodep << endl);
            m_jumpp = nullptr;
        }
    }
    void visit(AstStop* nodep) override {
        if (jumpingOver(nodep)) return;
        if (m_params) {  // This message seems better than an obscure $stop
            // The spec says $stop is just ignored, it seems evil to ignore assertions
            clearOptimizable(
                nodep,
                "$stop executed during function constification; maybe indicates assertion firing");
        }
        checkNodeInfo(nodep);
    }

    void visit(AstNodeFor* nodep) override {
        // Doing lots of Whiles is slow, so only for parameters
        UINFO(5, "   FOR " << nodep << endl);
        if (!m_params) {
            badNodeType(nodep);
            return;
        }
        checkNodeInfo(nodep);
        if (m_checkOnly) {
            iterateChildrenConst(nodep);
        } else if (optimizable()) {
            int loops = 0;
            iterateAndNextConstNull(nodep->initsp());
            while (true) {
                UINFO(5, "    FOR-ITER " << nodep << endl);
                iterateAndNextConstNull(nodep->condp());
                if (!optimizable()) break;
                if (!fetchConst(nodep->condp())->num().isNeqZero()) {  //
                    break;
                }
                iterateAndNextConstNull(nodep->stmtsp());
                iterateAndNextConstNull(nodep->incsp());
                if (loops++ > v3Global.opt.unrollCountAdjusted(VOptionBool{}, m_params, true)) {
                    clearOptimizable(nodep, "Loop unrolling took too long; probably this is an"
                                            "infinite loop, or use /*verilator unroll_full*/, or "
                                            "set --unroll-count above "
                                                + cvtToStr(loops));
                    break;
                }
            }
        }
    }

    void visit(AstWhile* nodep) override {
        // Doing lots of Whiles is slow, so only for parameters
        if (jumpingOver(nodep)) return;
        UINFO(5, "   WHILE " << nodep << endl);
        if (!m_params) {
            badNodeType(nodep);
            return;
        }
        checkNodeInfo(nodep);
        if (m_checkOnly) {
            iterateChildrenConst(nodep);
        } else if (optimizable()) {
            int loops = 0;
            while (true) {
                UINFO(5, "    WHILE-ITER " << nodep << endl);
                iterateAndNextConstNull(nodep->precondsp());
                if (jumpingOver(nodep)) break;
                iterateAndNextConstNull(nodep->condp());
                if (jumpingOver(nodep)) break;
                if (!optimizable()) break;
                if (!fetchConst(nodep->condp())->num().isNeqZero()) {  //
                    break;
                }
                iterateAndNextConstNull(nodep->stmtsp());
                if (jumpingOver(nodep)) break;
                iterateAndNextConstNull(nodep->incsp());
                if (jumpingOver(nodep)) break;

                // Prep for next loop
                if (loops++
                    > v3Global.opt.unrollCountAdjusted(nodep->unrollFull(), m_params, true)) {
                    clearOptimizable(nodep, "Loop unrolling took too long; probably this is an"
                                            "infinite loop, or use /*verilator unroll_full*/, or "
                                            "set --unroll-count above "
                                                + cvtToStr(loops));
                    break;
                }
            }
        }
    }

    void visit(AstFuncRef* nodep) override {
        if (jumpingOver(nodep)) return;
        if (!optimizable()) return;  // Accelerate
        UINFO(5, "   FUNCREF " << nodep << endl);
        checkNodeInfo(nodep);
        if (!m_params) {
            badNodeType(nodep);
            return;
        }
        AstNodeFTask* funcp = nodep->taskp();
        UASSERT_OBJ(funcp, nodep, "Not linked");
        if (m_params) V3Width::widthParamsEdit(funcp);
        VL_DANGLING(funcp);  // Make sure we've sized the function
        funcp = nodep->taskp();
        UASSERT_OBJ(funcp, nodep, "Not linked");
        if (funcp->recursive()) {
            // Because we attach values to nodes rather then making a stack, this is a mess
            // When we do support this, we need a stack depth limit of 1K or something,
            // and the t_func_recurse_param_bad.v test should check that limit's error message
            clearOptimizable(funcp, "Unsupported: Recursive constant functions");
            return;
        }
        // Apply function call values to function
        V3TaskConnects tconnects = V3Task::taskConnects(nodep, nodep->taskp()->stmtsp());
        // Must do this in two steps, eval all params, then apply them
        // Otherwise chained functions may have the wrong results
        for (V3TaskConnects::iterator it = tconnects.begin(); it != tconnects.end(); ++it) {
            AstVar* const portp = it->first;
            AstNode* const pinp = it->second->exprp();
            if (pinp) {  // Else too few arguments in function call - ignore it
                if (portp->isWritable()) {
                    clearOptimizable(
                        portp,
                        "Language violation: Outputs/refs not allowed in constant functions");
                    return;
                }
                // Evaluate pin value
                iterateConst(pinp);
            }
        }
        for (V3TaskConnects::iterator it = tconnects.begin(); it != tconnects.end(); ++it) {
            AstVar* const portp = it->first;
            AstNode* const pinp = it->second->exprp();
            if (pinp) {  // Else too few arguments in function call - ignore it
                // Apply value to the function
                if (!m_checkOnly && optimizable()) newValue(portp, fetchValue(pinp));
            }
        }
        SimStackNode stackNode{nodep, &tconnects};
        // cppcheck-suppress danglingLifetime
        m_callStack.push_back(&stackNode);
        // Clear output variable
        if (const auto* const basicp = VN_CAST(funcp->fvarp(), Var)->basicp()) {
            AstConst cnst{funcp->fvarp()->fileline(), AstConst::WidthedValue{}, basicp->widthMin(),
                          0};
            if (basicp->isZeroInit()) {
                cnst.num().setAllBits0();
            } else {
                cnst.num().setAllBitsX();
            }
            newValue(funcp->fvarp(), &cnst);
        }
        // Evaluate the function
        iterateConst(funcp);
        m_callStack.pop_back();
        if (!m_checkOnly && optimizable()) {
            // Grab return value from output variable (if it's a function)
            UASSERT_OBJ(funcp->fvarp(), nodep, "Function reference points at non-function");
            newValue(nodep, fetchValue(funcp->fvarp()));
        }
    }

    void visit(AstVar* nodep) override {
        if (jumpingOver(nodep)) return;
        if (!m_params) {
            badNodeType(nodep);
            return;
        }
    }

    void visit(AstScopeName* nodep) override {
        if (jumpingOver(nodep)) return;
        // Ignore
    }

    void visit(AstSFormatF* nodep) override {
        if (jumpingOver(nodep)) return;
        if (!optimizable()) return;  // Accelerate
        checkNodeInfo(nodep);
        iterateChildrenConst(nodep);
        if (m_params) {
            AstNode* nextArgp = nodep->exprsp();

            string result;
            const string format = nodep->text();
            auto pos = format.cbegin();
            bool inPct = false;
            string width;
            for (; pos != format.cend(); ++pos) {
                if (!inPct && pos[0] == '%') {
                    inPct = true;
                    width = "";
                } else if (!inPct) {  // Normal text
                    result += *pos;
                } else {  // Format character
                    if (std::isdigit(pos[0])) {
                        width += pos[0];
                        continue;
                    }

                    inPct = false;

                    if (V3Number::displayedFmtLegal(std::tolower(pos[0]), false)) {
                        AstNode* const argp = nextArgp;
                        nextArgp = nextArgp->nextp();
                        AstConst* const constp = fetchConstNull(argp);
                        if (!constp) {
                            clearOptimizable(
                                nodep, "Argument for $display like statement is not constant");
                            break;
                        }
                        const string pformat = "%"s + width + pos[0];
                        result += constp->num().displayed(nodep, pformat);
                    } else {
                        switch (std::tolower(pos[0])) {
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

            AstConst* const resultConstp
                = new AstConst{nodep->fileline(), AstConst::String{}, result};
            setValue(nodep, resultConstp);
            m_reclaimValuesp.push_back(resultConstp);
        }
    }

    void visit(AstDisplay* nodep) override {
        if (jumpingOver(nodep)) return;
        if (!optimizable()) return;  // Accelerate
        // We ignore isPredictOptimizable as $display is often in constant
        // functions and we want them to work if used with parameters
        checkNodeInfo(nodep, /*display:*/ true);
        iterateChildrenConst(nodep);
        if (m_params) {
            AstConst* const textp = fetchConst(nodep->fmtp());
            switch (nodep->displayType()) {
            case VDisplayType::DT_DISPLAY:  // FALLTHRU
            case VDisplayType::DT_INFO: v3warn(USERINFO, textp->name()); break;
            case VDisplayType::DT_ERROR: v3warn(USERERROR, textp->name()); break;
            case VDisplayType::DT_WARNING: v3warn(USERWARN, textp->name()); break;
            case VDisplayType::DT_FATAL: v3warn(USERFATAL, textp->name()); break;
            case VDisplayType::DT_WRITE:  // FALLTHRU
            default: clearOptimizable(nodep, "Unexpected display type");
            }
        }
    }

    // Ignore coverage - from a function we're inlining
    void visit(AstCoverInc* nodep) override {}

    // ====
    // Known Bad
    void visit(AstCMethodHard* nodep) override {
        // Some CMethods such as size() on queues could be supported, but
        // instead we should change those methods to new Ast types so we can
        // properly dispatch them
        if (jumpingOver(nodep)) return;
        knownBadNodeType(nodep);
    }
    void visit(AstMemberSel* nodep) override {
        if (jumpingOver(nodep)) return;
        knownBadNodeType(nodep);
    }
    // ====
    // default
    // These types are definitely not reducible
    //   AstCoverInc, AstFinish,
    //   AstRand, AstTime, AstUCFunc, AstCCall, AstCStmt, AstUCStmt
    void visit(AstNode* nodep) override {
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
        iterateConst(nodep);
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
        m_whyNotNodep = nullptr;
        m_anyAssignComb = false;
        m_anyAssignDly = false;
        m_inDlyAssign = false;
        m_isOutputter = false;
        m_instrCount = 0;
        m_dataCount = 0;
        m_jumpp = nullptr;

        AstNode::user1ClearTree();
        m_varAux.clear();
    }
    void mainTableCheck(AstNode* nodep) {
        setMode(true /*scoped*/, true /*checking*/, false /*params*/);
        mainGuts(nodep);
    }
    void mainTableEmulate(AstNode* nodep) {
        setMode(true /*scoped*/, false /*checking*/, false /*params*/);
        mainGuts(nodep);
    }
    void mainCheckTree(AstNode* nodep) {
        setMode(false /*scoped*/, true /*checking*/, false /*params*/);
        mainGuts(nodep);
    }
    void mainParamEmulate(AstNode* nodep) {
        setMode(false /*scoped*/, false /*checking*/, true /*params*/);
        mainGuts(nodep);
    }
    ~SimulateVisitor() override {
        for (const auto& pair : m_constps) {
            for (AstConst* const constp : pair.second) delete constp;
        }
        m_constps.clear();
        for (AstNode* ip : m_reclaimValuesp) delete ip;
        m_reclaimValuesp.clear();
    }
};

#endif  // Guard
