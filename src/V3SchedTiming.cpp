// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Code scheduling
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
//
// Functions defined in this file are used by V3Sched.cpp to properly integrate
// static scheduling with timing features. They remap the external domains of
// variables (see V3SchedTimingPrep.cpp) to trigger vectors, and create timing
// resume/ready calls for the global eval loop. There is also a function that
// transforms forks into emittable constructs.
//
// See the internals documentation docs/internals.rst for more details.
//
//*************************************************************************

#include "V3PchAstNoMT.h"  // VL_MT_DISABLED_CODE_UNIT

#include "V3EmitCBase.h"
#include "V3Sched.h"

VL_DEFINE_DEBUG_FUNCTIONS;

namespace V3Sched {

//============================================================================
// Trigger indices of the external domains of each variable

std::map<const AstVarScope*, std::vector<uint32_t>>
TimingKit::externalTriggerIndices(const TriggerKit& trigKit) const {
    std::map<const AstVarScope*, std::vector<uint32_t>> result;
    for (const auto& vscpDomains : m_externalDomains) {
        std::vector<uint32_t>& indices = result[vscpDomains.first];
        for (const AstSenTree* const domainp : vscpDomains.second) {
            for (const AstSenItem* const itemp : domainp->sensespList()) {
                indices.push_back(trigKit.senItem2TrigIdx(itemp));
            }
        }
    }
    return result;
}

//============================================================================
// Creates a timing resume call (if needed, else returns null)

AstCCall* TimingKit::createResume(AstVarScope* trigVscp) {
    if (!m_resumeFuncp) {
        if (m_lbs.empty()) return nullptr;
        // Create global resume function
        AstNetlist* const netlistp = v3Global.rootp();
        AstScope* const scopeTopp = netlistp->topScopep()->scopep();
        m_resumeFuncp = new AstCFunc{netlistp->fileline(), "_timing_resume", scopeTopp, ""};
        m_resumeFuncp->dontCombine(true);
        m_resumeFuncp->isLoose(true);
        m_resumeFuncp->isConst(false);
        m_resumeFuncp->declPrivate(true);
        scopeTopp->addBlocksp(m_resumeFuncp);

        for (const auto& entry : m_lbs) {
            AstActive* const activep = entry.m_activep;
            activep->foreach([this](AstCMethodHard* const exprp) {
                if (exprp->method() != VCMethod::SCHED_RESUME) return;
                AstNodeExpr* const fromp = exprp->fromp();
                if (VN_AS(fromp->dtypep(), BasicDType)->keyword()
                    != VBasicDTypeKwd::TRIGGER_SCHEDULER) {
                    return;
                }
                AstCMethodHard* const moveToResumep = new AstCMethodHard{
                    fromp->fileline(), fromp->cloneTree(false),
                    VCMethod::SCHED_MOVE_TO_RESUME_QUEUE,
                    exprp->pinsp() ? exprp->pinsp()->cloneTree(true) : nullptr};
                moveToResumep->dtypeSetVoid();
                m_resumeFuncp->addStmtsp(moveToResumep->makeStmt());
            });
        }

        // Put all the timing actives in the resume function
        AstIf* dlyShedIfp = nullptr;
        for (const auto& entry : m_lbs) {
            AstActive* const activep = entry.m_activep;
            // Resume time delays last. For no particular reason other than
            // that's what we used to do prior to proper #0 support.
            AstVarRef* const schedrefp = VN_AS(
                VN_AS(VN_AS(activep->stmtsp(), StmtExpr)->exprp(), CMethodHard)->fromp(), VarRef);

            AstNode* const actionp = activep->stmtsp()->unlinkFrBackWithNext();
            if (schedrefp->varScopep()->dtypep()->basicp()->isDelayScheduler()) {
                FileLine* const flp = trigVscp->fileline();
                const std::set<uint32_t>& triggers = entry.m_triggers;
                AstTriggered* const condp
                    = new AstTriggered{flp, trigVscp, {triggers.begin(), triggers.end()}};
                dlyShedIfp = new AstIf{flp, condp};
                dlyShedIfp->addThensp(actionp);
            } else {
                m_resumeFuncp->addStmtsp(actionp);
            }
        }
        if (dlyShedIfp) m_resumeFuncp->addStmtsp(dlyShedIfp);

        // These are now spent, oispose of now empty AstActive instances
        m_lbs.deleteActives();
    }
    AstCCall* const callp = new AstCCall{m_resumeFuncp->fileline(), m_resumeFuncp};
    callp->dtypeSetVoid();
    return callp;
}

AstVarScope* TimingKit::getDelayScheduler(AstNetlist* const /*netlistp*/) {
    for (const auto& entry : m_lbs) {
        AstActive* const ap = entry.m_activep;
        // TODO: this triple VN_AS expression is ridiculous
        AstVarRef* const schedrefp
            = VN_AS(VN_AS(VN_AS(ap->stmtsp(), StmtExpr)->exprp(), CMethodHard)->fromp(), VarRef);
        AstVarScope* const vscp = schedrefp->varScopep();
        if (vscp->dtypep()->basicp()->isDelayScheduler()) return vscp;
    }
    // None found. Design doesn't use any time delays
    return nullptr;
}

//============================================================================
// Creates a timing ready call (if needed, else returns null)

AstCCall* TimingKit::createReady(AstVarScope* trigVscp) {
    if (!m_readyFuncp) {
        for (const auto& entry : m_lbs) {
            AstActive* const activep = entry.m_activep;
            auto* const resumep = VN_AS(VN_AS(activep->stmtsp(), StmtExpr)->exprp(), CMethodHard);
            UASSERT_OBJ(!resumep->nextp(), resumep, "Should be the only statement here");
            AstVarScope* const schedulerp = VN_AS(resumep->fromp(), VarRef)->varScopep();
            UASSERT_OBJ(schedulerp->dtypep()->basicp()->isDelayScheduler()
                            || schedulerp->dtypep()->basicp()->isTriggerScheduler()
                            || schedulerp->dtypep()->basicp()->isDynamicTriggerScheduler(),
                        schedulerp, "Unexpected type");
            if (!schedulerp->dtypep()->basicp()->isTriggerScheduler()) continue;
            // Create the global ready function only if we have trigger schedulers
            if (!m_readyFuncp) {
                AstNetlist* const netlistp = v3Global.rootp();
                AstScope* const scopeTopp = netlistp->topScopep()->scopep();
                m_readyFuncp = new AstCFunc{netlistp->fileline(), "_timing_ready", scopeTopp, ""};
                m_readyFuncp->dontCombine(true);
                m_readyFuncp->isLoose(true);
                m_readyFuncp->isConst(false);
                m_readyFuncp->declPrivate(true);
                scopeTopp->addBlocksp(m_readyFuncp);
            }

            FileLine* const flp = activep->sentreep()->fileline();

            // Create an 'AstIf' sensitive to the suspending triggers
            const std::set<uint32_t>& triggers = entry.m_triggers;
            AstTriggered* const condp
                = new AstTriggered{flp, trigVscp, {triggers.begin(), triggers.end()}};
            AstIf* const ifp = new AstIf{flp, condp};
            m_readyFuncp->addStmtsp(ifp);

            // Mark as ready the processes resumed on this sensitivity expression
            AstVarRef* const refp = new AstVarRef{flp, schedulerp, VAccess::READWRITE};
            AstCMethodHard* const callp = new AstCMethodHard{flp, refp, VCMethod::SCHED_READY};
            callp->dtypeSetVoid();
            if (resumep->pinsp()) callp->addPinsp(resumep->pinsp()->cloneTree(false));
            ifp->addThensp(callp->makeStmt());
        }
        // We still haven't created a ready function (no trigger schedulers), return null
        if (!m_readyFuncp) return nullptr;
    }
    AstCCall* const callp = new AstCCall{m_readyFuncp->fileline(), m_readyFuncp};
    callp->dtypeSetVoid();
    return callp;
}

//============================================================================
// Visits all forks and transforms their sub-statements into separate functions.

// Transform all forked processes into functions
class TransformForksVisitor final : public VNVisitor {
    // NODE STATE
    //  AstVar::user1()  -> bool.  Set true if the variable was declared before the current fork.
    const VNUser1InUse m_inuser1;

    // STATE
    bool m_inClass = false;  // Are we in a class?
    bool m_beginHasAwaits = false;  // Does the current begin have awaits?
    AstFork* m_forkp = nullptr;  // Current fork
    AstCFunc* m_funcp = nullptr;  // Current function

    // METHODS
    // Remap local vars referenced by the given fork function
    // TODO: We should only pass variables to the fork that are
    // live in the fork body, but for that we need a proper data
    // flow analysis framework which we don't have at the moment
    void remapLocals(AstCFunc* const funcp, AstCCall* const callp) {
        const VNUser2InUse user2InUse;  // AstVarScope -> AstVarScope: var to remap to
        funcp->foreach([&](AstNodeVarRef* refp) {
            AstVar* const varp = refp->varp();
            AstVarScope* const vscp = refp->varScopep();
            AstBasicDType* const dtypep = varp->dtypep()->basicp();
            // If not a fork..join, copy. All write refs should've been handled by V3Fork
            bool passByValue = !m_forkp->joinType().join();
            if (vscp->forkByValue()) {
                // Set just before the fork, for its processes to get by value
                passByValue = true;
            } else if (!varp->isFuncLocal()) {
                // Not func local. Its lifetime is longer than the forked process. Skip
                return;
            } else if (!varp->user1()) {
                // Not declared before the fork. It cannot outlive the forked process
                return;
            } else if (dtypep && dtypep->isForkSync()) {
                // We can just pass it by value to the new function
                passByValue = true;
            }
            // Remap the reference
            if (!vscp->user2p()) {
                // Clone the var to the new function
                AstVar* const newvarp
                    = new AstVar{varp->fileline(), VVarType::BLOCKTEMP, varp->name(), varp};
                newvarp->funcLocal(true);
                newvarp->direction(passByValue ? VDirection::INPUT : VDirection::REF);
                funcp->addArgsp(newvarp);
                AstVarScope* const newvscp
                    = new AstVarScope{newvarp->fileline(), funcp->scopep(), newvarp};
                funcp->scopep()->addVarsp(newvscp);
                vscp->user2p(newvscp);
                callp->addArgsp(new AstVarRef{refp->fileline(), vscp,
                                              passByValue ? VAccess::READ : VAccess::READWRITE});
            }
            AstVarScope* const newvscp = VN_AS(vscp->user2p(), VarScope);
            refp->varScopep(newvscp);
            refp->varp(newvscp->varp());
        });
    }

    // VISITORS
    void visit(AstNodeModule* nodep) override {
        VL_RESTORER(m_inClass);
        m_inClass = VN_IS(nodep, Class);
        iterateChildren(nodep);
    }
    void visit(AstCFunc* nodep) override {
        VL_RESTORER(m_funcp);
        m_funcp = nodep;
        iterateChildren(nodep);
    }
    void visit(AstVar* nodep) override {
        if (!m_forkp) nodep->user1(true);
    }
    void visit(AstFork* nodep) override {
        if (m_forkp) return;  // Handle forks in forks after moving them to new functions
        VL_RESTORER(m_forkp);
        m_forkp = nodep;
        iterateChildrenConst(nodep);  // Const, so we don't iterate the calls twice
        // Replace self with the function calls (no co_await, as we don't want the main
        // process to suspend whenever any of the children do)
        // V3Dead could have removed all statements from the fork, so guard against it
        // Inline begins now that they are not needed
        AstNode* resp = nullptr;
        if (AstNode* const declsp = nodep->declsp()) {
            resp = AstNode::addNext(resp, declsp->unlinkFrBackWithNext());
        }
        if (AstNode* const stmtsp = nodep->stmtsp()) {
            resp = AstNode::addNext(resp, stmtsp->unlinkFrBackWithNext());
        }
        while (AstBegin* const beginp = nodep->forksp()) {
            if (AstNode* const declsp = beginp->declsp()) {
                resp = AstNode::addNext(resp, declsp->unlinkFrBackWithNext());
            }
            if (AstNode* const stmtsp = beginp->stmtsp()) {
                resp = AstNode::addNext(resp, stmtsp->unlinkFrBackWithNext());
            }
            VL_DO_DANGLING(pushDeletep(beginp->unlinkFrBack()), beginp);
        }
        if (resp) {
            nodep->replaceWith(resp);
        } else {
            nodep->unlinkFrBack();
        }
        VL_DO_DANGLING(pushDeletep(nodep), nodep);
    }
    void visit(AstBegin* nodep) override {
        UASSERT_OBJ(m_forkp, nodep, "Begin outside of a fork");
        // Start with children, so later we only find awaits that are actually in this begin
        m_beginHasAwaits = false;
        iterateChildrenConst(nodep);
        if (!nodep->stmtsp()) return;
        if (!m_beginHasAwaits && !nodep->needProcess()) return;

        UASSERT_OBJ(!nodep->name().empty(), nodep, "Begin needs a name");
        // Create a function to put this begin's statements in
        FileLine* const flp = nodep->fileline();
        AstCFunc* const newfuncp = new AstCFunc{flp, m_funcp->name() + "__" + nodep->name(),
                                                m_funcp->scopep(), "VlCoroutine"};

        m_funcp->addNextHere(newfuncp);
        newfuncp->isLoose(m_funcp->isLoose());
        newfuncp->slow(m_funcp->slow());
        newfuncp->isConst(m_funcp->isConst());
        newfuncp->declPrivate(true);
        // Create the call to the function
        AstCCall* const callp = new AstCCall{flp, newfuncp};
        callp->dtypeSetVoid();
        // If we're in a class, add a vlSymsp arg
        if (m_inClass) {
            newfuncp->addStmtsp(new AstCStmt{flp, "VL_KEEP_THIS;"});
            newfuncp->argTypes(EmitCUtil::symClassVar());
            callp->argTypes("vlSymsp");
        }
        // Put the begin's statements in the function
        if (AstNode* const declsp = nodep->declsp()) {
            newfuncp->addStmtsp(declsp->unlinkFrBackWithNext());
        }
        if (AstNode* const stmtsp = nodep->stmtsp()) {
            newfuncp->addStmtsp(stmtsp->unlinkFrBackWithNext());
        }
        // Replace the body of the begin with a call to the newly created function
        nodep->addStmtsp(callp->makeStmt());
        // Propagate if needs process
        if (nodep->needProcess()) newfuncp->setNeedProcess();
        remapLocals(newfuncp, callp);
    }
    void visit(AstCAwait* nodep) override {
        m_beginHasAwaits = true;
        iterateChildrenConst(nodep);
    }

    //--------------------
    void visit(AstNode* nodep) override { iterateChildren(nodep); }

public:
    // CONSTRUCTORS
    explicit TransformForksVisitor(AstNetlist* nodep) { iterate(nodep); }
    ~TransformForksVisitor() override = default;
};

void transformForks(AstNetlist* const netlistp) {
    if (!v3Global.usesTiming()) return;
    { TransformForksVisitor{netlistp}; }
    V3Global::dumpCheckGlobalTree("transform_forks", 0, dumpTreeEitherLevel() >= 3);
}

}  // namespace V3Sched
