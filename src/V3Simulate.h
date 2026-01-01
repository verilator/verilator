// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Simulate code to determine output values/variables
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2026 by Wilson Snyder. This program is free software; you
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
    // CONSTANTS
    static constexpr int CONST_FUNC_RECURSION_MAX = 1000;
    static constexpr int CALL_STACK_MAX = 100;

    // NODE STATE
    // Cleared on each always/assignw
    const VNUser1InUse m_inuser1;

    // AstNode::user1p()     -> See AuxAstVar via m_varAux

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

    // We want to re-use allocated constants across calls to clear(), but we want to be able
    // to 'clear()' fast, so we use a generation number based allocator.
    struct ConstAllocator final {
        size_t m_generation = 0;
        size_t m_nextFree = 0;
        std::deque<AstConst*> m_constps;
        AstConst* allocate(size_t currentGeneration, AstNode* nodep) {
            if (m_generation != currentGeneration) {
                m_generation = currentGeneration;
                m_nextFree = 0;
            }
            UASSERT_OBJ(m_nextFree <= m_constps.size(), nodep, "Should only allocate at end");
            if (m_nextFree == m_constps.size()) {
                m_constps.push_back(
                    new AstConst{nodep->fileline(), AstConst::DTyped{}, nodep->dtypep()});
            }
            AstConst* const constp = m_constps[m_nextFree++];
            constp->num().nodep(nodep);
            return constp;
        }

        ~ConstAllocator() {
            for (AstConst* const constp : m_constps) VL_DO_DANGLING(delete constp, constp);
        }
    };

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
    bool m_isImpure;  // Not pure
    bool m_isCoverage;  // Has coverage
    int m_instrCount;  ///< Number of nodes
    int m_dataCount;  ///< Bytes of data
    int m_recurseCount = 0;  // Now deep in current recursion
    AstNode* m_jumptargetp = nullptr;  // AstJumpBlock/AstLoop we are branching over
    // Simulating:
    // Allocators for constants of various data types
    std::unordered_map<const AstNodeDType*, ConstAllocator> m_constps;
    size_t m_constGeneration = 0;
    std::vector<SimStackNode*> m_callStack;  // Call stack for verbose error messages

    // Cleanup
    // V3Numbers that represents strings are a bit special and the API for
    // V3Number does not allow changing them.
    std::vector<AstNode*> m_reclaimValuesp;  // List of allocated string numbers

    // Note level 8&9 include debugging each simulation value
    VL_DEFINE_DEBUG_FUNCTIONS;

    // Potentially very slow, intended for debugging
    string prettyNumber(const V3Number* nump, const AstNodeDType* dtypep) {
        if (const AstRefDType* const refdtypep = VN_CAST(dtypep, RefDType)) {  //
            dtypep = refdtypep->skipRefp();
        }
        if (const AstNodeUOrStructDType* const stp = VN_CAST(dtypep, NodeUOrStructDType)) {
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
                    if (const AstNodeDType* const childTypep = itemp->subDTypep()) {
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
            if (const AstNodeDType* const childTypep = arrayp->subDTypep()) {
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
            if (debug() >= 5) {  // LCOV_EXCL_START
                UINFO_PREFIX("Clear optimizable: " << why);
                if (nodep) std::cout << ": " << nodep;
                std::cout << std::endl;
            }  // LCOV_EXCL_STOP
            m_whyNotOptimizable = why;
            std::ostringstream stack;
            int n = 0;
            for (const auto& callstack : vlstd::reverse_view(m_callStack)) {
                const AstFuncRef* const funcp = callstack->m_funcp;
                stack << "\n        " << funcp->fileline() << "... Called from '"
                      << funcp->prettyName() << "()' with parameters:";
                V3TaskConnects* tconnects = callstack->m_tconnects;
                for (V3TaskConnects::iterator conIt = tconnects->begin();
                     conIt != tconnects->end(); ++conIt) {
                    const AstVar* const portp = conIt->first;
                    AstNodeExpr* const pinp = conIt->second->exprp();
                    const AstNodeDType* const dtypep = pinp->dtypep();
                    if (AstConst* const valp = fetchConstNull(pinp)) {
                        stack << "\n           " << portp->prettyName() << " = "
                              << prettyNumber(&valp->num(), dtypep);
                    }
                }
                if (++n > CALL_STACK_MAX) {
                    stack << "\n           ... stack truncated";
                    break;
                }
            }
            m_whyNotOptimizable += stack.str();
        }
    }
    bool optimizable() const { return m_whyNotNodep == nullptr; }
    string whyNotMessage() const { return m_whyNotOptimizable; }
    AstNode* whyNotNodep() const { return m_whyNotNodep; }

    bool isAssignDly() const { return m_anyAssignDly; }
    bool isImpure() const { return m_isImpure; }
    bool isCoverage() const { return m_isCoverage; }
    int instrCount() const { return m_instrCount; }
    int dataCount() const { return m_dataCount; }

    // Simulation METHODS
private:
    AstConst* allocConst(AstNode* nodep) {
        // Allocate a constant with this dtype. Reuse them across a 'clear()' call for efficiency.
        return m_constps[nodep->dtypep()].allocate(m_constGeneration, nodep);
    }

public:
    void newValue(AstNode* nodep, const AstNodeExpr* valuep) {
        if (const AstConst* const constp = VN_CAST(valuep, Const)) {
            newConst(nodep)->num().opAssign(constp->num());
            UINFO(9, "     new val " << valuep->name() << " on " << nodep);
        } else if (fetchValueNull(nodep) != valuep) {
            // const_cast, as clonep() is set on valuep, but nothing should care
            setValue(nodep, newTrackedClone(const_cast<AstNodeExpr*>(valuep)));
        }
    }
    void newOutValue(AstNode* nodep, const AstNodeExpr* valuep) {
        if (const AstConst* const constp = VN_CAST(valuep, Const)) {
            newOutConst(nodep)->num().opAssign(constp->num());
            UINFO(9, "     new oval " << valuep->name() << " on " << nodep);
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
            m_varAux(nodep).valuep = constp;
            return constp;
        } else {
            return fetchConst(nodep);
        }
    }
    AstConst* newOutConst(AstNode* nodep) {
        // Set a var-output constant value for this node
        if (!VN_IS(m_varAux(nodep).outValuep, Const)) {
            AstConst* const constp = allocConst(nodep);
            m_varAux(nodep).outValuep = constp;
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
        // UINFO(9, "     fetch val " << *valuep << " on " << nodep);
        return valuep;
    }
    AstConst* fetchConst(AstNode* nodep) {
        AstConst* const constp = fetchConstNull(nodep);
        UASSERT_OBJ(constp, nodep, "No value found for node.");
        // UINFO(9, "     fetch num " << *constp << " on " << nodep);
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
        UINFO(9, "     set val " << valuep->name() << " on " << nodep);
        m_varAux(nodep).valuep = valuep;
    }
    void setOutValue(AstNode* nodep, AstNodeExpr* valuep) {
        UASSERT_OBJ(valuep, nodep, "Simulate setting null value");
        UINFO(9, "     set oval " << valuep->name() << " on " << nodep);
        m_varAux(nodep).outValuep = valuep;
    }

    void checkNodeInfo(AstNode* nodep, bool ignorePredict = false) {
        if (m_checkOnly) {
            m_instrCount += nodep->instrCount();
            m_dataCount += nodep->width();
        }
        if (!ignorePredict && !nodep->isPredictOptimizable()) {
            // UINFO(9, "     !predictopt " << nodep);
            clearOptimizable(nodep, "Isn't predictable");
        }
        if (!nodep->isPure()) m_isImpure = true;
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
                UINFO(0, "Unknown node type in SimulateVisitor: " << nodep->prettyTypeName());
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

    // True if current node might be jumped over - all visitors must call this up front
    bool jumpingOver() const { return m_jumptargetp; }
    void assignOutValue(const AstNodeAssign* nodep, AstNode* vscp, const AstNodeExpr* valuep) {
        if (VN_IS(nodep, AssignDly)) {
            // Don't do setValue, as value isn't yet visible to following statements
            newOutValue(vscp, valuep);
        } else {
            newValue(vscp, valuep);
            newOutValue(vscp, valuep);
        }
    }

    string toStringRecurse(AstNodeExpr* nodep) {
        // Return string representation, or clearOptimizable
        const AstNodeExpr* const valuep = fetchValue(nodep);
        if (const AstConst* const avaluep = VN_CAST(valuep, Const)) {
            return "'h"s + avaluep->num().displayed(nodep, "%0x");
        }
        if (const AstInitArray* const avaluep = VN_CAST(valuep, InitArray)) {
            string result = "'{";
            string comma;
            if (VN_IS(nodep->dtypep(), AssocArrayDType)) {
                if (avaluep->defaultp()) {
                    result += comma + "default:" + toStringRecurse(avaluep->defaultp());
                    comma = ", ";
                }
                const auto& mapr = avaluep->map();
                for (const auto& itr : mapr) {
                    result += comma + cvtToStr(itr.first) + ":"
                              + toStringRecurse(itr.second->valuep());
                    comma = ", ";
                }
            } else if (const AstUnpackArrayDType* const dtypep
                       = VN_CAST(nodep->dtypep(), UnpackArrayDType)) {
                for (int n = 0; n < dtypep->elementsConst(); ++n) {
                    result += comma + toStringRecurse(avaluep->getIndexDefaultedValuep(n));
                    comma = ", ";
                }
            }
            result += "}";
            return result;
        }
        clearOptimizable(nodep, "Cannot convert to string");  // LCOV_EXCL_LINE
        return "";
    }

    void initVar(AstVar* nodep) {
        if (const AstBasicDType* const basicp = nodep->dtypeSkipRefp()->basicp()) {
            AstConst cnst{nodep->fileline(), AstConst::WidthedValue{}, basicp->widthMin(), 0};
            if (basicp->isZeroInit()) {
                cnst.num().setAllBits0();
            } else {
                cnst.num().setAllBitsX();
            }
            newValue(nodep, &cnst);
        }
    }

    // VISITORS
    void visit(AstAlways* nodep) override {
        if (jumpingOver()) return;
        checkNodeInfo(nodep);
        iterateChildrenConst(nodep);
    }
    void visit(AstSenTree* nodep) override {
        // Sensitivities aren't inputs per se; we'll keep our tree under the same sens.
    }
    void visit(AstVarRef* nodep) override {
        if (jumpingOver()) return;
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
                const AstNodeExpr* const valuep
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
        if (jumpingOver()) return;
        if (m_scoped) {
            badNodeType(nodep);
            return;
        } else {
            clearOptimizable(nodep, "Language violation: Dotted hierarchical references not "
                                    "allowed in constant functions");
        }
    }
    void visit(AstNodeFTask* nodep) override {
        if (jumpingOver()) return;
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
        if (jumpingOver()) return;
        if (!m_params) {
            badNodeType(nodep);
            return;
        }
        checkNodeInfo(nodep);
        iterateChildrenConst(nodep);
    }
    void visit(AstNodeIf* nodep) override {
        if (jumpingOver()) return;
        UINFO(5, "   IF " << nodep);
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
        iterateChildrenConst(nodep);
        if (!m_checkOnly && optimizable()) newValue(nodep, nodep);
    }
    void visit(AstInitItem* nodep) override {
        checkNodeInfo(nodep);
        iterateChildrenConst(nodep);
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
            AstConst* const valuep = newConst(nodep);
            nodep->numberOperate(newConst(nodep)->num(), fetchConst(nodep->lhsp())->num(),
                                 fetchConst(nodep->rhsp())->num());
            // See #5490. 'numberOperate' on partially out of range select yields 'x' bits,
            // but in reality it would yield '0's without V3Table, so force 'x' bits to '0',
            // to ensure the result is the same with and without V3Table.
            if (!m_params && VN_IS(nodep, Sel) && valuep->num().isAnyX()) {
                V3Number num{valuep, valuep->width(), valuep->num()};
                valuep->num().opBitsOne(num);
            }
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
    void visit(AstCond* nodep) override {
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

    void handleAssignArray(AstNodeAssign* nodep, AstArraySel* selp, AstNodeExpr* valueFromp) {
        // At present we only handle single dimensional assignments
        // To do better, we need the concept of lvalues, or similar, to know where/how to insert
        checkNodeInfo(selp);
        iterateAndNextConstNull(selp->bitp());  // Bit index
        AstVarRef* const varrefp = VN_CAST(selp->fromp(), VarRef);
        if (!varrefp) {
            clearOptimizable(selp->fromp(), "Array select LHS isn't simple variable");
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
            AstNodeExpr* const valuep = newTrackedClone(fetchValue(valueFromp));
            UINFO(9, "     set val[" << index << "] = " << valuep);
            // Values are in the "real" tree under the InitArray so can eventually extract it,
            // Not in the usual setValue (via m_varAux)
            initp->addIndexValuep(index, valuep);
            UINFOTREE(9, initp, "", "array");
            assignOutValue(nodep, vscp, initp);
        }
    }
    void handleAssignSel(AstNodeAssign* nodep, AstSel* selp, AstNodeExpr* valueFromp) {
        AstVarRef* varrefp = nullptr;
        V3Number lsb{nodep};
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
                m_reclaimValuesp.emplace_back(outconstp);
            }
            outconstp->num().opSelInto(fetchConst(valueFromp)->num(), lsb, selp->widthConst());
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
            clearOptimizable(selp->fromp(), "Select LHS isn't simple variable");
        }
    }
    void handleAssignRecurse(AstNodeAssign* nodep, AstNodeExpr* lhsp, AstNodeExpr* valueFromp) {
        if (!optimizable()) return;
        if (AstArraySel* const selp = VN_CAST(lhsp, ArraySel)) {
            if (!m_params) {
                clearOptimizable(lhsp, "Assign LHS has select");
                return;
            }
            handleAssignArray(nodep, selp, valueFromp);
        } else if (AstConcat* const selp = VN_CAST(lhsp, Concat)) {
            checkNodeInfo(selp);
            if (!VN_IS(selp->rhsp()->dtypep()->skipRefp(), BasicDType)) {
                clearOptimizable(lhsp, "Assign LHS concat of non-basic type");
                return;
            }
            // Split value into left and right concat values
            if (!m_checkOnly) {
                {
                    AstConst* const outconstp
                        = new AstConst{selp->lhsp()->fileline(), AstConst::WidthedValue{},
                                       selp->lhsp()->width(), 0};
                    outconstp->num().opSel(fetchConst(valueFromp)->num(),
                                           selp->lhsp()->width() + selp->rhsp()->width() + 1,
                                           selp->rhsp()->width());
                    newValue(selp->lhsp(), outconstp);
                    VL_DO_DANGLING(outconstp->deleteTree(), outconstp);
                }
                {
                    AstConst* const outconstp
                        = new AstConst{selp->rhsp()->fileline(), AstConst::WidthedValue{},
                                       selp->rhsp()->widthMin(), 0};
                    outconstp->num().opSel(fetchConst(valueFromp)->num(),
                                           selp->rhsp()->width() - 1, 0);
                    newValue(selp->rhsp(), outconstp);
                    VL_DO_DANGLING(outconstp->deleteTree(), outconstp);
                }
            }
            handleAssignRecurse(nodep, selp->lhsp(), selp->lhsp());
            handleAssignRecurse(nodep, selp->rhsp(), selp->rhsp());
        } else if (AstReplicate* const selp = VN_CAST(lhsp, Replicate)) {
            checkNodeInfo(selp);
            iterateAndNextConstNull(selp->countp());
            AstConst* const countp = VN_CAST(selp->countp(), Const);
            if (!countp || !countp->num().isEqOne()) {
                clearOptimizable(selp, "Replicate LHS count isn't one");
                return;
            }
            handleAssignRecurse(nodep, selp->srcp(), valueFromp);
        } else if (AstSel* const selp = VN_CAST(lhsp, Sel)) {
            if (!m_params) {
                clearOptimizable(lhsp, "Assign LHS has select");
                return;
            }
            handleAssignSel(nodep, selp, valueFromp);
        } else if (VN_IS(lhsp, VarRef)) {
            if (m_checkOnly) {
                iterateAndNextConstNull(lhsp);
            } else {
                AstNode* const vscp = varOrScope(VN_CAST(lhsp, VarRef));
                assignOutValue(nodep, vscp, fetchValue(valueFromp));
            }
        } else {
            clearOptimizable(lhsp, "Assign LHS isn't simple variable");
        }
    }
    void visit(AstNodeAssign* nodep) override {
        if (jumpingOver()) return;
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

        iterateAndNextConstNull(nodep->rhsp());  // Value to assign
        handleAssignRecurse(nodep, nodep->lhsp(), nodep->rhsp());
        // UINFO(9, "set " << fetchConst(nodep->rhsp())->num().ascii() << " for assign "
        //  << nodep->lhsp()->name());
    }
    void visit(AstArraySel* nodep) override {
        checkNodeInfo(nodep);
        iterateChildrenConst(nodep);
        if (const AstInitArray* const initp = VN_CAST(fetchValueNull(nodep->fromp()), InitArray)) {
            const AstConst* const indexp = fetchConst(nodep->bitp());
            const uint32_t offset = indexp->num().toUInt();
            AstNodeExpr* const itemp = initp->getIndexDefaultedValuep(offset);
            if (!itemp) {
                clearOptimizable(nodep, "Array initialization has too few elements, need element "
                                            + cvtToStr(offset));
            } else if (AstConst* const constp = VN_CAST(itemp, Const)) {
                setValue(nodep, constp);
            } else {
                setValue(nodep, fetchValue(itemp));
            }
        } else {
            clearOptimizable(nodep, "Array select of non-array");
        }
    }

    // Evaluate a slice of an unpacked array.  If the base value is a constant
    // AstInitArray, build a new AstInitArray representing the slice and assign
    // it as this node's value.  New index 0 corresponds to the lowest index of
    // the slice.  Otherwise, mark this node as unoptimizable.
    void visit(AstSliceSel* nodep) override {
        checkNodeInfo(nodep);
        iterateChildrenConst(nodep);
        if (m_checkOnly || !optimizable()) return;
        // Fetch the base constant array
        if (const AstInitArray* const initp = VN_CAST(fetchValueNull(nodep->fromp()), InitArray)) {
            const VNumRange& sliceRange = nodep->declRange();
            const uint32_t sliceElements = sliceRange.elements();
            const int sliceLo = sliceRange.lo();
            // Use this node's dtype for the slice array
            AstNodeDType* const dtypep = nodep->dtypep()->skipRefp();
            // Clone the default value from the base array, if present
            AstNodeExpr* defaultp = nullptr;
            if (initp->defaultp()) defaultp = initp->defaultp()->cloneTree(false);
            AstInitArray* const newInitp = new AstInitArray{nodep->fileline(), dtypep, defaultp};
            // Copy slice elements in ascending order
            for (uint32_t idx = 0; idx < sliceElements; ++idx) {
                const uint32_t baseIdx = sliceLo + idx;
                AstNodeExpr* const itemp = initp->getIndexDefaultedValuep(baseIdx);
                if (itemp) newInitp->addIndexValuep(idx, itemp->cloneTree(false));
            }
            // Assign the new constant array and track it for later deletion
            setValue(nodep, newInitp);
            m_reclaimValuesp.push_back(newInitp);
        } else {
            clearOptimizable(nodep, "Slice select of non-array");
        }
    }

    void visit(AstBegin* nodep) override {
        checkNodeInfo(nodep);
        iterateChildrenConst(nodep);
    }
    void visit(AstCase* nodep) override {
        if (jumpingOver()) return;
        UINFO(5, "   CASE " << nodep);
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
                if (itemp->isDefault()) {
                    iterateAndNextConstNull(itemp->stmtsp());
                    hit = true;
                }
            }
        }
    }

    void visit(AstCaseItem* nodep) override {
        // Real handling is in AstNodeCase
        if (jumpingOver()) return;
        checkNodeInfo(nodep);
        iterateChildrenConst(nodep);
    }

    void visit(AstComment*) override {}

    void visit(AstStmtExpr* nodep) override {
        if (jumpingOver()) return;
        checkNodeInfo(nodep);
        iterateChildrenConst(nodep);
    }
    void visit(AstExprStmt* nodep) override {
        if (jumpingOver()) return;
        checkNodeInfo(nodep);
        iterateAndNextConstNull(nodep->stmtsp());
        if (!optimizable()) return;
        iterateAndNextConstNull(nodep->resultp());
        if (!optimizable()) return;
        if (!m_checkOnly) newValue(nodep, fetchValue(nodep->resultp()));
    }

    void visit(AstJumpBlock* nodep) override {
        if (jumpingOver()) return;
        iterateChildrenConst(nodep);
        if (m_jumptargetp == nodep) {
            UINFO(5, "   JUMP DONE " << nodep);
            m_jumptargetp = nullptr;
        }
    }
    void visit(AstJumpGo* nodep) override {
        if (jumpingOver()) return;
        checkNodeInfo(nodep);
        if (!m_checkOnly) {
            UINFO(5, "   JUMP GO " << nodep);
            UASSERT_OBJ(!m_jumptargetp, nodep, "Jump inside jump");
            m_jumptargetp = nodep->blockp();
        }
    }
    void visit(AstLoop* nodep) override {
        UASSERT_OBJ(!nodep->contsp(), nodep, "'contsp' only used before LinkJump");
        if (jumpingOver()) return;
        UINFO(5, "   LOOP " << nodep);
        // Doing lots of loops is slow, so only for parameters
        if (!m_params) {
            badNodeType(nodep);
            return;
        }
        checkNodeInfo(nodep);
        if (m_checkOnly) {
            iterateChildrenConst(nodep);
            return;
        }
        if (!optimizable()) return;

        size_t iterCount = 0;
        const size_t iterLimit = v3Global.opt.unrollLimit();
        while (true) {
            if (iterCount > iterLimit) {
                clearOptimizable(nodep, "Loop simulation took too long; probably this is an "
                                        "infinite loop, otherwise set '--unroll-limit' above "
                                            + std::to_string(iterLimit));
                break;
            }
            ++iterCount;

            UINFO(5, "    LOOP-ITER " << nodep);
            iterateAndNextConstNull(nodep->stmtsp());
            if (jumpingOver()) break;
        }

        if (m_jumptargetp == nodep) {
            UINFO(5, "   LOOP TEST DONE " << nodep);
            m_jumptargetp = nullptr;
        }
    }
    void visit(AstLoopTest* nodep) override {
        if (jumpingOver()) return;
        checkNodeInfo(nodep);
        iterateConst(nodep->condp());
        if (!m_checkOnly && optimizable() && fetchConst(nodep->condp())->num().isEqZero()) {
            UINFO(5, "   LOOP TEST GO " << nodep);
            UASSERT_OBJ(!m_jumptargetp, nodep, "Jump inside jump");
            m_jumptargetp = nodep->loopp();
        }
    }

    void visit(AstStop* nodep) override {
        if (jumpingOver()) return;
        if (m_params) {  // This message seems better than an obscure $stop
            // The spec says $stop is just ignored, it seems evil to ignore assertions
            clearOptimizable(
                nodep,
                "$stop executed during function constification; maybe indicates assertion firing");
        }
        checkNodeInfo(nodep);
    }
    void visit(AstFuncRef* nodep) override {
        if (jumpingOver()) return;
        if (!optimizable()) return;  // Accelerate
        UINFO(5, "   FUNCREF " << nodep);
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
            if (m_recurseCount >= CONST_FUNC_RECURSION_MAX) {
                clearOptimizable(funcp, "Constant function recursed more than "s
                                            + std::to_string(CONST_FUNC_RECURSION_MAX) + " times");
                return;
            }
            ++m_recurseCount;
        }

        // Values from previous call, so can save to stack
        // The "stack" is this visit function's local stack, as this visit is itself recursing
        std::map<AstNode*, AstNodeExpr*> oldValues;

        if (funcp->recursive() && !m_checkOnly) {
            // Save local automatics
            funcp->foreach([this, &oldValues](AstVar* varp) {
                if (varp->lifetime().isAutomatic()) {  // This also does function's I/O
                    if (AstNodeExpr* const valuep = fetchValueNull(varp)) {
                        AstNodeExpr* const nvaluep = newTrackedClone(valuep);
                        oldValues.emplace(varp, nvaluep);
                    }
                }
            });
            // Save every expression value, as might be in middle of expression
            // that calls recursively back to this same function.
            // This is much heavier-weight then likely is needed, in theory
            // we could look at the visit stack to determine what nodes
            // need save-restore, but that is difficult to get right, and
            // recursion is rare.
            funcp->foreach([this, &oldValues](AstNodeExpr* exprp) {
                if (VN_IS(exprp, Const)) return;  // Speed up as won't change
                if (AstNodeExpr* const valuep = fetchValueNull(exprp)) {
                    AstNodeExpr* const nvaluep = newTrackedClone(valuep);
                    oldValues.emplace(exprp, nvaluep);
                }
            });
        }
        // Apply function call values to function
        V3TaskConnects tconnects = V3Task::taskConnects(nodep, nodep->taskp()->stmtsp());
        // Must do this in two steps, eval all params, then apply them
        // Otherwise chained functions may have the wrong results
        std::vector<std::pair<AstVar*, AstNodeExpr*>> portValues;
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
                // Clone in case are recursing
                portValues.push_back(std::make_pair(portp, newTrackedClone(fetchValue(pinp))));
            }
        }
        // Apply value to the function
        if (!m_checkOnly && optimizable())
            for (const auto& it : portValues) {
                if (!m_checkOnly && optimizable()) newValue(it.first, it.second);
            }
        SimStackNode stackNode{nodep, &tconnects};
        // cppcheck-suppress danglingLifetime
        m_callStack.push_back(&stackNode);
        if (!m_checkOnly) {
            // Clear output variable
            initVar(VN_CAST(funcp->fvarp(), Var));
            // Clear other automatic variables
            funcp->foreach([this](AstVar* varp) {
                if (varp->lifetime().isAutomatic() && !varp->isIO()) initVar(varp);
            });
        }

        // Evaluate the function
        iterateConst(funcp);
        m_callStack.pop_back();
        const AstNodeExpr* returnp = nullptr;
        if (!m_checkOnly && optimizable()) {
            // Grab return value from output variable
            UASSERT_OBJ(funcp->fvarp(), nodep, "Function reference points at non-function");
            returnp = newTrackedClone(fetchValue(funcp->fvarp()));
            UINFO(5, "func " << nodep->name() << " return = " << returnp);
        }
        // Restore local automatics (none unless recursed)
        for (const auto& it : oldValues) {
            if (it.second) newValue(it.first, it.second);
        }
        if (returnp) newValue(nodep, returnp);
        if (funcp->recursive()) {
            UASSERT_OBJ(m_recurseCount > 0, nodep, "recurse underflow");
            --m_recurseCount;
        }
    }

    void visit(AstVar* nodep) override {
        if (jumpingOver()) return;
        if (!m_params) {
            badNodeType(nodep);
            return;
        }
    }

    void visit(AstScopeName* nodep) override {
        if (jumpingOver()) return;
        // Ignore
    }

    void visit(AstSFormatF* nodep) override {
        if (jumpingOver()) return;
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
        if (jumpingOver()) return;
        if (!optimizable()) return;  // Accelerate
        // We ignore isPredictOptimizable as $display is often in constant
        // functions and we want them to work if used with parameters
        checkNodeInfo(nodep, /*display:*/ true);
        iterateChildrenConst(nodep);
        if (m_params) {
            const AstConst* const textp = fetchConst(nodep->fmtp());
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
    void visit(AstToStringN* nodep) override {
        if (jumpingOver()) return;
        if (!optimizable()) return;  // Accelerate
        checkNodeInfo(nodep);
        iterateChildrenConst(nodep);
        if (!optimizable()) return;
        std::string result = toStringRecurse(nodep->lhsp());
        if (!optimizable()) return;
        AstConst* const resultConstp = new AstConst{nodep->fileline(), AstConst::String{}, result};
        setValue(nodep, resultConstp);
        m_reclaimValuesp.push_back(resultConstp);
    }

    void visit(AstCoverInc* nodep) override { m_isCoverage = true; }

    // ====
    // Known Bad
    void visit(AstCMethodHard* nodep) override {
        // Some CMethods such as size() on queues could be supported, but
        // instead we should change those methods to new Ast types so we can
        // properly dispatch them
        if (jumpingOver()) return;
        knownBadNodeType(nodep);
    }
    void visit(AstMemberSel* nodep) override {
        if (jumpingOver()) return;
        knownBadNodeType(nodep);
    }
    // ====
    // default
    // These types are definitely not reducible
    //   AstCoverInc, AstFinish,
    //   AstRand, AstTime, AstCCall, AstCStmt*, AstCExpr*
    void visit(AstNode* nodep) override {
        if (jumpingOver()) return;
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
        UASSERT_OBJ(!m_jumptargetp, m_jumptargetp, "Jump target was not found");
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
        m_isImpure = false;
        m_isCoverage = false;
        m_instrCount = 0;
        m_dataCount = 0;
        m_jumptargetp = nullptr;

        AstNode::user1ClearTree();
        m_varAux.clear();
        ++m_constGeneration;
    }
    void mainTableCheck(AstNode* nodep) {
        setMode(true /*scoped*/, true /*checking*/, false /*params*/);
        mainGuts(nodep);
    }
    void mainTableEmulate(AstNode* nodep) {
        setMode(true /*scoped*/, false /*checking*/, false /*params*/);
        mainGuts(nodep);
    }
    void mainParamEmulate(AstNode* nodep) {
        setMode(false /*scoped*/, false /*checking*/, true /*params*/);
        mainGuts(nodep);
    }
    ~SimulateVisitor() override {
        m_constps.clear();
        std::vector<AstNode*> unusedRootps;
        unusedRootps.reserve(m_reclaimValuesp.size());
        for (AstNode* const nodep : m_reclaimValuesp) {
            if (!nodep->backp()) unusedRootps.emplace_back(nodep);
        }
        m_reclaimValuesp.clear();
        for (AstNode* const nodep : unusedRootps) VL_DO_DANGLING(nodep->deleteTree(), nodep);
    }
};

#endif  // Guard
