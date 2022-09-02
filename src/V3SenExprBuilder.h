// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Builder for sensitivity checking expressions.
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2022 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
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
    // STATE
    AstScope* const m_scopep;  // The scope

    std::vector<AstVar*> m_locals;  // Trigger eval local variables
    std::vector<AstNodeStmt*> m_inits;  // Initialization statements for prevoius values
    std::vector<AstNodeStmt*> m_preUpdates;  // Pre update assignments
    std::vector<AstNodeStmt*> m_postUpdates;  // Post update assignments

    std::unordered_map<VNRef<AstNode>, AstVarScope*> m_prev;  // The 'previous value' signals
    std::unordered_map<VNRef<AstNode>, AstVarScope*> m_curr;  // The 'current value' signals
    std::unordered_set<VNRef<AstNode>> m_hasPreUpdate;  // Whether the given sen expression already
                                                        // has an update statement in m_preUpdates
    std::unordered_set<VNRef<AstNode>> m_hasPostUpdate;  // Likewis for m_postUpdates

    V3UniqueNames m_currNames{"__Vtrigcurrexpr"};  // For generating unique current value
                                                   // signal names
    V3UniqueNames m_prevNames{"__Vtrigprevexpr"};  // Likewise for previous values

    static bool isSupportedDType(AstNodeDType* dtypep) {
        dtypep = dtypep->skipRefp();
        if (VN_IS(dtypep, BasicDType)) return true;
        if (VN_IS(dtypep, PackArrayDType)) return true;
        if (VN_IS(dtypep, UnpackArrayDType)) return isSupportedDType(dtypep->subDTypep());
        if (VN_IS(dtypep, NodeUOrStructDType)) return true;  // All are packed at the moment
        return false;
    }

    static bool isSimpleExpr(const AstNode* const exprp) {
        return exprp->forall([](const AstNode* const nodep) {
            return VN_IS(nodep, Const) || VN_IS(nodep, NodeVarRef) || VN_IS(nodep, Sel)
                   || VN_IS(nodep, NodeSel) || VN_IS(nodep, MemberSel)
                   || VN_IS(nodep, CMethodHard);
        });
    }

    // METHODS
    AstNode* getCurr(AstNode* exprp) {
        // For simple expressions like varrefs or selects, just use them directly
        if (isSimpleExpr(exprp)) return exprp->cloneTree(false);

        // Create the 'current value' variable
        FileLine* const flp = exprp->fileline();
        auto result = m_curr.emplace(*exprp, nullptr);
        if (result.second) {
            AstVar* const varp
                = new AstVar{flp, VVarType::BLOCKTEMP, m_currNames.get(exprp), exprp->dtypep()};
            varp->funcLocal(true);
            m_locals.push_back(varp);
            AstVarScope* vscp = new AstVarScope{flp, m_scopep, varp};
            m_scopep->addVarsp(vscp);
            result.first->second = vscp;
        }
        AstVarScope* const currp = result.first->second;

        // Add pre update if it does not exist yet in this round
        if (m_hasPreUpdate.emplace(*currp).second) {
            m_preUpdates.push_back(new AstAssign{flp, new AstVarRef{flp, currp, VAccess::WRITE},
                                                 exprp->cloneTree(false)});
        }
        return new AstVarRef{flp, currp, VAccess::READ};
    }
    AstVarScope* getPrev(AstNode* exprp) {
        FileLine* const flp = exprp->fileline();
        const auto rdCurr = [=]() { return getCurr(exprp); };

        // Create the 'previous value' variable
        auto it = m_prev.find(*exprp);
        if (it == m_prev.end()) {
            // For readability, use the scoped signal name if the trigger is a simple AstVarRef
            string name;
            if (AstVarRef* const refp = VN_CAST(exprp, VarRef)) {
                AstVarScope* vscp = refp->varScopep();
                name = "__Vtrigrprev__" + vscp->scopep()->nameDotless() + "__"
                       + vscp->varp()->name();
            } else {
                name = m_prevNames.get(exprp);
            }

            AstVarScope* prevp;
            if (m_scopep->isTop()) {
                prevp = m_scopep->createTemp(name, exprp->dtypep());
            } else {
                AstVar* const varp = new AstVar{flp, VVarType::BLOCKTEMP, m_prevNames.get(exprp),
                                                exprp->dtypep()};
                varp->funcLocal(true);
                m_locals.push_back(varp);
                prevp = new AstVarScope{flp, m_scopep, varp};
                m_scopep->addVarsp(prevp);
            }
            it = m_prev.emplace(*exprp, prevp).first;

            // Add the initializer init
            AstAssign* const initp = new AstAssign{flp, new AstVarRef{flp, prevp, VAccess::WRITE},
                                                   exprp->cloneTree(false)};
            m_inits.push_back(initp);
        }

        AstVarScope* const prevp = it->second;

        const auto wrPrev = [=]() { return new AstVarRef{flp, prevp, VAccess::WRITE}; };

        // Add post update if it does not exist yet
        if (m_hasPostUpdate.emplace(*exprp).second) {
            if (!isSupportedDType(exprp->dtypep())) {
                exprp->v3warn(E_UNSUPPORTED,
                              "Unsupported: Cannot detect changes on expression of complex type"
                              " (see combinational cycles reported by UNOPTFLAT)");
                return prevp;
            }

            if (AstUnpackArrayDType* const dtypep = VN_CAST(exprp->dtypep(), UnpackArrayDType)) {
                AstCMethodHard* const cmhp = new AstCMethodHard{flp, wrPrev(), "assign", rdCurr()};
                cmhp->dtypeSetVoid();
                cmhp->statement(true);
                m_postUpdates.push_back(cmhp);
            } else {
                m_postUpdates.push_back(new AstAssign{flp, wrPrev(), rdCurr()});
            }
        }

        return prevp;
    }

    std::pair<AstNode*, bool> createTerm(AstSenItem* senItemp) {
        FileLine* const flp = senItemp->fileline();
        AstNode* const senp = senItemp->sensp();

        const auto currp = [=]() { return getCurr(senp); };
        const auto prevp = [=]() { return new AstVarRef{flp, getPrev(senp), VAccess::READ}; };
        const auto lsb = [=](AstNodeMath* opp) { return new AstSel{flp, opp, 0, 1}; };

        // All event signals should be 1-bit at this point
        switch (senItemp->edgeType()) {
        case VEdgeType::ET_ILLEGAL:
            return {nullptr, false};  // We already warn for this in V3LinkResolve
        case VEdgeType::ET_CHANGED:
        case VEdgeType::ET_HYBRID:  //
            if (VN_IS(senp->dtypep(), UnpackArrayDType)) {
                AstCMethodHard* const resultp = new AstCMethodHard{flp, currp(), "neq", prevp()};
                resultp->dtypeSetBit();
                return {resultp, true};
            }
            return {new AstNeq{flp, currp(), prevp()}, true};
        case VEdgeType::ET_BOTHEDGE:  //
            return {lsb(new AstXor{flp, currp(), prevp()}), false};
        case VEdgeType::ET_POSEDGE:  //
            return {lsb(new AstAnd{flp, currp(), new AstNot{flp, prevp()}}), false};
        case VEdgeType::ET_NEGEDGE:  //
            return {lsb(new AstAnd{flp, new AstNot{flp, currp()}, prevp()}), false};
        case VEdgeType::ET_EVENT: {
            UASSERT_OBJ(v3Global.hasEvents(), senItemp, "Inconsistent");
            {
                // If the event is fired, set up the clearing process
                AstCMethodHard* const callp = new AstCMethodHard{flp, currp(), "isFired"};
                callp->dtypeSetBit();
                AstIf* const ifp = new AstIf{flp, callp};
                m_postUpdates.push_back(ifp);

                // Clear 'fired' state when done
                AstCMethodHard* const clearp = new AstCMethodHard{flp, currp(), "clearFired"};
                ifp->addThensp(clearp);
                clearp->dtypeSetVoid();
                clearp->statement(true);

                // Enqueue for clearing 'triggered' state on next eval
                AstTextBlock* const blockp = new AstTextBlock{flp};
                ifp->addThensp(blockp);
                const auto add = [&](const string& text) { blockp->addText(flp, text, true); };
                add("vlSymsp->enqueueTriggeredEventForClearing(");
                blockp->addNodesp(currp());
                add(");\n");
            }

            // Get 'fired' state
            AstCMethodHard* const callp = new AstCMethodHard{flp, currp(), "isFired"};
            callp->dtypeSetBit();
            return {callp, false};
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
    std::pair<AstNode*, bool> build(const AstSenTree* senTreep) {
        FileLine* const flp = senTreep->fileline();
        AstNode* resultp = nullptr;
        bool firedAtInitialization = false;
        for (AstSenItem* senItemp = senTreep->sensesp(); senItemp;
             senItemp = VN_AS(senItemp->nextp(), SenItem)) {
            const auto& pair = createTerm(senItemp);
            if (AstNode* const termp = pair.first) {
                resultp = resultp ? new AstOr{flp, resultp, termp} : termp;
                firedAtInitialization |= pair.second;
            }
        }
        return {resultp, firedAtInitialization};
    }

    std::vector<AstNodeStmt*> getAndClearInits() { return std::move(m_inits); }
    std::vector<AstVar*> getAndClearLocals() { return std::move(m_locals); }

    std::vector<AstNodeStmt*> getAndClearPreUpdates() {
        m_hasPreUpdate.clear();
        return std::move(m_preUpdates);
    }

    std::vector<AstNodeStmt*> getAndClearPostUpdates() {
        m_hasPostUpdate.clear();
        return std::move(m_postUpdates);
    }

    // CONSTRUCTOR
    SenExprBuilder(AstScope* scopep)
        : m_scopep{scopep} {}
};

#endif  // Guard
