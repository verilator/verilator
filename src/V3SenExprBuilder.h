// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Builder for sensitivity checking expressions.
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2003-2026 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#ifndef VERILATOR_V3SENEXPRBUILDER_H_
#define VERILATOR_V3SENEXPRBUILDER_H_

#include "config_build.h"
#include "verilatedos.h"

#include "V3Ast.h"
#include "V3UniqueNames.h"

//######################################################################
// SenExprBuilder constructs the expressions used to compute if an
// AstSenTree have triggered

class SenExprBuilder final {
public:
    // TYPES
    struct Results final {
        std::vector<AstNodeStmt*> m_inits;  // Initialization statements for previous values
        std::vector<AstNodeStmt*> m_preUpdates;  // Pre update assignments
        std::vector<AstNodeStmt*> m_postUpdates;  // Post update assignments
        // Aliases of destructive post updates (for example event clearFired) that may need
        // to run once before entering a fresh dynamic wait loop.
        std::vector<AstNodeStmt*> m_destructivePostUpdates;
        std::vector<AstVar*> m_vars;  // Created temporary variables
    };

private:
    // STATE
    AstScope* const m_scopep;  // The scope

    Results m_results;  // The builder result

    std::unordered_map<VNRef<AstNode>, AstVarScope*> m_prev;  // The 'previous value' signals
    std::unordered_map<VNRef<AstNode>, AstVarScope*> m_curr;  // The 'current value' signals
    std::unordered_set<VNRef<AstNode>> m_hasPreUpdate;  // Whether the given sen expression already
                                                        // has an update statement in m_preUpdates
    std::unordered_set<VNRef<AstNode>> m_hasPostUpdate;  // Likewise for m_postUpdates

    V3UniqueNames m_prevNames{"__Vtrigprevexpr"};  // For generating unique temporary names

    static bool isSupportedDType(AstNodeDType* dtypep) {
        dtypep = dtypep->skipRefp();
        if (VN_IS(dtypep, BasicDType)) return true;
        if (VN_IS(dtypep, PackArrayDType)) return true;
        if (VN_IS(dtypep, UnpackArrayDType)) return isSupportedDType(dtypep->subDTypep());
        if (VN_IS(dtypep, NodeUOrStructDType)) return true;  // All are packed at the moment
        // Per IEEE, detects reference object pointer changes, not contents of the class changes
        if (VN_IS(dtypep, ClassRefDType)) return true;
        return false;
    }

    static bool isSimpleExpr(const AstNode* const exprp) {
        return exprp->forall([](const AstNode* const nodep) {
            return VN_IS(nodep, Const) || VN_IS(nodep, NodeVarRef) || VN_IS(nodep, Sel)
                   || VN_IS(nodep, NodeSel) || VN_IS(nodep, MemberRef)
                   || VN_IS(nodep, CMethodHard);
        });
    }

    // Whether a reference may be null: a class reference or a virtual interface
    static bool isNullableRef(const AstNodeExpr* const refp) {
        if (!refp->dtypep()) return false;
        const AstNodeDType* const dtypep = refp->dtypep()->skipRefp();
        const AstIfaceRefDType* const ifaceDtypep = VN_CAST(dtypep, IfaceRefDType);
        return VN_IS(dtypep, ClassRefDType) || (ifaceDtypep && ifaceDtypep->isVirtual());
    }

    // Collect nullable bases for member accesses through nullable references; bases
    // are ordered innermost first, so each guard is evaluated before its dependents.
    static void collectNullableBases(const AstNodeExpr* exprp,
                                     std::vector<const AstNodeExpr*>& bases,
                                     std::unordered_set<const AstNodeExpr*>& seen) {
        if (!exprp) return;
        exprp->foreach([&](const AstNode* nodep) {
            const AstMemberRef* const memberRefp = VN_CAST(nodep, MemberRef);
            if (!memberRefp) return;
            const AstNodeExpr* const fromp = memberRefp->fromp();
            if (!isNullableRef(fromp)) return;
            if (!seen.insert(fromp).second) return;
            bases.push_back(fromp);
            collectNullableBases(fromp, bases, seen);
        });
    }

    static void collectNullableBases(const AstNodeExpr* exprp,
                                     std::vector<const AstNodeExpr*>& bases) {
        std::unordered_set<const AstNodeExpr*> seen;
        collectNullableBases(exprp, bases, seen);
    }

    // METHODS
    AstVarScope* crateTemp(AstNodeExpr* exprp) {
        // For readability, use the scoped signal name if the trigger is a simple AstVarRef
        string name;
        if (AstVarRef* const refp = VN_CAST(exprp, VarRef)) {
            AstVarScope* const vscp = refp->varScopep();
            name = "__" + vscp->scopep()->nameDotless() + "__" + vscp->varp()->name();
            name = m_prevNames.get(name);
        } else {
            name = m_prevNames.get(exprp);
        }
        // Not shared between instances, as the users might move the variables into processes
        FileLine* const flp = m_scopep->fileline();
        AstVar* const varp = new AstVar{flp, VVarType::MODULETEMP, name, exprp->dtypep()};
        varp->isInternal(true);
        m_scopep->modp()->addStmtsp(varp);
        AstVarScope* const vscp = new AstVarScope{flp, m_scopep, varp};
        m_scopep->addVarsp(vscp);
        m_results.m_vars.push_back(varp);
        return vscp;
    }

    // Helper to wrap a statement with null checks: if (base1 != null) if (base2 != null) stmt
    AstNodeStmt* wrapStmtWithNullChecks(FileLine* flp, AstNodeStmt* stmtp,
                                        const std::vector<const AstNodeExpr*>& bases) {
        AstNodeStmt* resultp = stmtp;
        for (const AstNodeExpr* const basep : bases) {
            AstNodeExpr* const nullp = new AstConst{flp, AstConst::Null{}};
            // const_cast safe: cloneTree doesn't modify the source
            AstNodeExpr* const checkp
                = new AstNeq{flp, const_cast<AstNodeExpr*>(basep)->cloneTree(false), nullp};
            resultp = new AstIf{flp, checkp, resultp};
        }
        return resultp;
    }

    // Helper to wrap a trigger expression with null checks
    // Returns the expression wrapped in: (base1 != null) ? ((base2 != null) ? expr : 0) : 0
    AstNodeExpr* wrapExprWithNullChecks(FileLine* flp, AstNodeExpr* exprp,
                                        const std::vector<const AstNodeExpr*>& bases) {
        AstNodeExpr* resultp = exprp;
        for (const AstNodeExpr* const basep : bases) {
            AstNodeExpr* const nullp = new AstConst{flp, AstConst::Null{}};
            // const_cast safe: cloneTree doesn't modify the source
            AstNodeExpr* const checkp
                = new AstNeq{flp, const_cast<AstNodeExpr*>(basep)->cloneTree(false), nullp};
            AstNodeExpr* const falsep = new AstConst{flp, AstConst::BitFalse{}};
            // Don't use AstNullCheck here: it reports a null pointer error, while a
            // trigger with a null base must not fire.
            AstNodeExpr* const condp = new AstCond{flp, checkp, resultp, falsep};
            condp->dtypeSetBit();
            resultp = condp;
        }
        return resultp;
    }

    AstNodeExpr* getCurr(AstNodeExpr* exprp) {
        // For simple expressions like varrefs or selects, just use them directly
        if (isSimpleExpr(exprp)) return exprp->cloneTree(false);

        // Create the 'current value' variable
        FileLine* const flp = exprp->fileline();
        auto result = m_curr.emplace(*exprp, nullptr);
        if (result.second) result.first->second = crateTemp(exprp);
        AstVarScope* const currp = result.first->second;

        // Collect null guards for member accesses through nullable references
        std::vector<const AstNodeExpr*> bases;
        collectNullableBases(exprp, bases);

        // Add pre update if it does not exist yet in this round
        if (m_hasPreUpdate.emplace(*currp).second) {
            m_results.m_preUpdates.push_back(wrapStmtWithNullChecks(
                flp,
                new AstAssign{flp, new AstVarRef{flp, currp, VAccess::WRITE},
                              exprp->cloneTree(false)},
                bases));
        }
        return new AstVarRef{flp, currp, VAccess::READ};
    }

    AstVarScope* getPrev(AstNodeExpr* exprp) {
        FileLine* const flp = exprp->fileline();
        const auto rdCurr = [this, exprp]() { return getCurr(exprp); };

        // Collect null guards for member accesses through nullable references
        std::vector<const AstNodeExpr*> bases;
        collectNullableBases(exprp, bases);

        AstNode* scopeExprp = exprp;
        if (AstVarRef* const refp = VN_CAST(exprp, VarRef)) scopeExprp = refp->varScopep();
        // Create the 'previous value' variable
        const auto pair = m_prev.emplace(*scopeExprp, nullptr);
        if (pair.second) {
            AstVarScope* const prevp = crateTemp(exprp);
            pair.first->second = prevp;
            // Add the initializer init (guarded if through a nullable reference)
            AstAssign* const initp = new AstAssign{flp, new AstVarRef{flp, prevp, VAccess::WRITE},
                                                   exprp->cloneTree(false)};
            m_results.m_inits.push_back(wrapStmtWithNullChecks(flp, initp, bases));
        }

        AstVarScope* const prevp = pair.first->second;

        const auto wrPrev = [=]() { return new AstVarRef{flp, prevp, VAccess::WRITE}; };

        // Add post update if it does not exist yet
        if (m_hasPostUpdate.emplace(*exprp).second) {
            AstNodeDType* const exprDtp = exprp->dtypep()->skipRefp();
            if (!isSupportedDType(exprDtp)) {
                exprp->v3warn(
                    E_UNSUPPORTED,
                    "Unsupported: Cannot detect changes on expression of complex type "
                        << exprDtp->prettyDTypeNameQ() << "\n"
                        << exprp->warnMore()
                        << "... May be caused by combinational cycles reported with UNOPTFLAT");
                return prevp;
            }
            if (VN_IS(exprDtp, UnpackArrayDType)) {
                AstCMethodHard* const cmhp
                    = new AstCMethodHard{flp, wrPrev(), VCMethod::UNPACKED_ASSIGN, rdCurr()};
                cmhp->dtypeSetVoid();
                m_results.m_postUpdates.push_back(
                    wrapStmtWithNullChecks(flp, cmhp->makeStmt(), bases));
            } else {
                m_results.m_postUpdates.push_back(
                    wrapStmtWithNullChecks(flp, new AstAssign{flp, wrPrev(), rdCurr()}, bases));
            }
        }

        return prevp;
    }

    std::pair<AstNodeExpr*, bool> createTerm(const AstSenItem* senItemp) {
        FileLine* const flp = senItemp->fileline();
        AstNodeExpr* const senp = senItemp->sensp();

        // Collect null guards for member accesses through class or dynamic-scope handles
        // that may be null (for example, before the creating process has started).
        std::vector<const AstNodeExpr*> bases;
        collectNullableBases(senp, bases);

        const auto currp = [this, senp]() { return getCurr(senp); };
        const auto prevp
            = [this, flp, senp]() { return new AstVarRef{flp, getPrev(senp), VAccess::READ}; };
        const auto lsb = [=](AstNodeExpr* opp) { return new AstSel{flp, opp, 0, 1}; };

        // All event signals should be 1-bit at this point
        switch (senItemp->edgeType()) {
        case VEdgeType::ET_CHANGED:
        case VEdgeType::ET_HYBRID: {
            // If a change sense folded to a constant, run it once at time 0 only
            if (VN_IS(senp, Const)) return {new AstConst{flp, AstConst::BitFalse{}}, true};
            // Hybrid needs to run on startup
            const bool fireAtInit = senItemp->edgeType() == VEdgeType::ET_HYBRID;
            if (VN_IS(senp->dtypep()->skipRefp(), UnpackArrayDType)) {
                // operand order reversed to avoid calling neq() method on non-VlUnpacked type, see
                // issue #5125
                AstCMethodHard* const resultp
                    = new AstCMethodHard{flp, prevp(), VCMethod::UNPACKED_NEQ, currp()};
                resultp->dtypeSetBit();
                return {wrapExprWithNullChecks(flp, resultp, bases), fireAtInit};
            }
            return {wrapExprWithNullChecks(flp, new AstNeq{flp, currp(), prevp()}, bases),
                    fireAtInit};
        }
        case VEdgeType::ET_BOTHEDGE:  //
            return {wrapExprWithNullChecks(flp, lsb(new AstXor{flp, currp(), prevp()}), bases),
                    false};
        case VEdgeType::ET_POSEDGE:  //
            return {wrapExprWithNullChecks(
                        flp, lsb(new AstAnd{flp, currp(), new AstNot{flp, prevp()}}), bases),
                    false};
        case VEdgeType::ET_NEGEDGE:  //
            return {wrapExprWithNullChecks(
                        flp, lsb(new AstAnd{flp, new AstNot{flp, currp()}, prevp()}), bases),
                    false};
        case VEdgeType::ET_EVENT: {
            UASSERT_OBJ(v3Global.hasEvents(), senItemp, "Inconsistent");

            // Clear 'fired' state when done (guarded if through a nullable reference)
            // The event is modified, so the select (e.g. assoc array) must be an lvalue
            AstNodeExpr* const clearFromp = currp();
            if (AstNodeVarRef* const refp
                = VN_CAST(clearFromp->getVAccessTargetRecurse(), NodeVarRef)) {
                refp->access(VAccess::WRITE);
            }
            // Dynamic array and queue selects were already made as read-only 'at'
            for (AstNodeExpr* selp = clearFromp;;) {
                if (AstCMethodHard* const cmethodp = VN_CAST(selp, CMethodHard)) {
                    if (cmethodp->method() == VCMethod::ARRAY_AT) {
                        cmethodp->method(VCMethod::ARRAY_AT_WRITE);
                    } else if (cmethodp->method() == VCMethod::ARRAY_AT_BACK) {
                        cmethodp->method(VCMethod::DYN_AT_WRITE_APPEND_BACK);
                    }
                    selp = cmethodp->fromp();
                } else if (const AstNodeSel* const nodeSelp = VN_CAST(selp, NodeSel)) {
                    selp = nodeSelp->fromp();
                } else {
                    break;
                }
            }
            AstCMethodHard* const clearp
                = new AstCMethodHard{flp, clearFromp, VCMethod::EVENT_CLEAR_FIRED};
            clearp->dtypeSetVoid();
            AstNodeStmt* const clearStmtp = wrapStmtWithNullChecks(flp, clearp->makeStmt(), bases);
            m_results.m_postUpdates.push_back(clearStmtp);
            m_results.m_destructivePostUpdates.push_back(clearStmtp);

            // Get 'fired' state
            AstCMethodHard* const callp
                = new AstCMethodHard{flp, currp(), VCMethod::EVENT_IS_FIRED};
            callp->dtypeSetBit();
            AstNodeExpr* const firedp = wrapExprWithNullChecks(flp, callp, bases);
            // Do not trigger user named-event processes after $finish.
            AstNodeExpr* const notFinishp
                = new AstCExpr{flp,
                               "VL_LIKELY(!vlSymsp->_vm_contextp__->gotFinish() && "
                               "!vlSymsp->_vm_contextp__->finishPending())",
                               1};
            return {new AstLogAnd{flp, notFinishp, firedp}, false};
        }
        case VEdgeType::ET_TRUE:  //
            return {currp(), false};
        default:  // LCOV_EXCL_START
            senItemp->v3fatalSrc("Unknown edge type");
            return {nullptr, false};
        }  // LCOV_EXCL_STOP
    }

public:
    // Returns the expression computing the trigger, and a bool indicating that
    // this trigger should be fired on the first evaluation (at initialization)
    std::pair<AstNodeExpr*, bool> build(const AstSenItem* senItemp) {
        auto term = createTerm(senItemp);
        if (AstNodeExpr* const condp = senItemp->condp()) {
            term.first = new AstAnd{senItemp->fileline(), condp->cloneTreePure(false), term.first};
        }
        return term;
    }

    // Like above, but for a whole SenTree
    std::pair<AstNodeExpr*, bool> build(const AstSenTree* senTreep) {
        FileLine* const flp = senTreep->fileline();
        AstNodeExpr* resultp = nullptr;
        bool firedAtInitialization = false;
        for (AstSenItem* const senItemp : senTreep->sensespList()) {
            const auto& pair = build(senItemp);
            if (AstNodeExpr* termp = pair.first) {
                resultp = resultp ? new AstOr{flp, resultp, termp} : termp;
                firedAtInitialization |= pair.second;
            }
        }
        return {resultp, firedAtInitialization};
    }

    Results getResultsAndClearUpdates() {
        m_hasPreUpdate.clear();
        m_hasPostUpdate.clear();
        Results ans = std::move(m_results);
        m_results = {};
        return ans;
    }

    Results getAndClearResults() {
        m_curr.clear();
        m_prev.clear();
        m_hasPreUpdate.clear();
        m_hasPostUpdate.clear();
        return std::move(m_results);
    }

    // CONSTRUCTOR
    explicit SenExprBuilder(AstScope* scopep)
        : m_scopep{scopep} {}
};

#endif  // Guard
