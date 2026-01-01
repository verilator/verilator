// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Code scheduling
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
// Functions defined in this file are used by V3Sched.cpp to properly integrate
// static scheduling with timing features. They create external domains for
// variables, remap them to trigger vectors, and create timing resume/commit
// calls for the global eval loop. There is also a function that transforms
// forks into emittable constructs.
//
// See the internals documentation docs/internals.rst for more details.
//
//*************************************************************************

#include "V3PchAstNoMT.h"  // VL_MT_DISABLED_CODE_UNIT

#include "V3EmitCBase.h"
#include "V3Sched.h"

#include <unordered_map>

VL_DEFINE_DEBUG_FUNCTIONS;

namespace V3Sched {

//============================================================================
// Remaps external domains using the specified trigger map

std::map<const AstVarScope*, std::vector<AstSenTree*>>
TimingKit::remapDomains(const std::unordered_map<const AstSenTree*, AstSenTree*>& trigMap) const {
    std::map<const AstVarScope*, std::vector<AstSenTree*>> remappedDomainMap;
    for (const auto& vscpDomains : m_externalDomains) {
        const AstVarScope* const vscp = vscpDomains.first;
        const auto& domains = vscpDomains.second;
        auto& remappedDomains = remappedDomainMap[vscp];
        remappedDomains.reserve(domains.size());
        for (AstSenTree* const domainp : domains) {
            remappedDomains.push_back(trigMap.at(domainp));
        }
    }
    return remappedDomainMap;
}

//============================================================================
// Creates a timing resume call (if needed, else returns null)

AstCCall* TimingKit::createResume(AstNetlist* const netlistp) {
    if (!m_resumeFuncp) {
        if (m_lbs.empty()) return nullptr;
        // Create global resume function
        AstScope* const scopeTopp = netlistp->topScopep()->scopep();
        m_resumeFuncp = new AstCFunc{netlistp->fileline(), "_timing_resume", scopeTopp, ""};
        m_resumeFuncp->dontCombine(true);
        m_resumeFuncp->isLoose(true);
        m_resumeFuncp->isConst(false);
        m_resumeFuncp->declPrivate(true);
        scopeTopp->addBlocksp(m_resumeFuncp);

        // Put all the timing actives in the resume function
        AstIf* dlyShedIfp = nullptr;
        for (auto& p : m_lbs) {
            AstActive* const activep = p.second;
            // Hack to ensure that #0 delays will be executed after any other `act` events.
            // Just handle delayed coroutines last.
            AstVarRef* const schedrefp = VN_AS(
                VN_AS(VN_AS(activep->stmtsp(), StmtExpr)->exprp(), CMethodHard)->fromp(), VarRef);

            AstIf* const ifp = V3Sched::util::createIfFromSenTree(activep->sentreep());
            ifp->addThensp(activep->stmtsp()->unlinkFrBackWithNext());

            if (schedrefp->varScopep()->dtypep()->basicp()->isDelayScheduler()) {
                dlyShedIfp = ifp;
            } else {
                m_resumeFuncp->addStmtsp(ifp);
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

//============================================================================
// Creates a timing commit call (if needed, else returns null)

AstCCall* TimingKit::createCommit(AstNetlist* const netlistp) {
    if (!m_commitFuncp) {
        for (auto& p : m_lbs) {
            AstActive* const activep = p.second;
            auto* const resumep = VN_AS(VN_AS(activep->stmtsp(), StmtExpr)->exprp(), CMethodHard);
            UASSERT_OBJ(!resumep->nextp(), resumep, "Should be the only statement here");
            AstVarScope* const schedulerp = VN_AS(resumep->fromp(), VarRef)->varScopep();
            UASSERT_OBJ(schedulerp->dtypep()->basicp()->isDelayScheduler()
                            || schedulerp->dtypep()->basicp()->isTriggerScheduler()
                            || schedulerp->dtypep()->basicp()->isDynamicTriggerScheduler(),
                        schedulerp, "Unexpected type");
            if (!schedulerp->dtypep()->basicp()->isTriggerScheduler()) continue;
            // Create the global commit function only if we have trigger schedulers
            if (!m_commitFuncp) {
                AstScope* const scopeTopp = netlistp->topScopep()->scopep();
                m_commitFuncp
                    = new AstCFunc{netlistp->fileline(), "_timing_commit", scopeTopp, ""};
                m_commitFuncp->dontCombine(true);
                m_commitFuncp->isLoose(true);
                m_commitFuncp->isConst(false);
                m_commitFuncp->declPrivate(true);
                scopeTopp->addBlocksp(m_commitFuncp);
            }

            // There is a somewhat complicate dance here. Given a suspendable
            // process of the form:
            //    ->evntA;
            //    $display("Fired evntA");
            //    @(evntA or evntB);
            // The firing of the event cannot trigger the event control
            // following it, as the process is not yet sensitive to the event
            // when it fires (same applies for change detects). The way the
            // scheduling works, the @evnt will suspend the process before
            // the firing of the event is recognized on the next iteration of
            // the 'act' loop, and hence could incorrectly resume the @evnt
            // statement. To make this work, whenever a process suspends, it
            // goes into an "uncommitted" state, so it cannot be resumed
            // immediately on the next iteration of the 'act' loop, which is
            // what we want. The question then is, when should the suspended
            // process be "committed" and hence possible to be resumed. This is
            // done when it is know for sure the suspending expression was not
            // triggered on the current iteration of the 'act' loop. With
            // multiple events in the suspending expression, all events need
            // to be not triggered to safely commit the suspended process.
            //
            // This is is consistent with IEEE scheduling semantics, and
            // behaves as if the above was executed as:
            //    ->evntA;
            //    $display("Fired evnt");
            //    ... all other statements in the 'act' loop that might fire evntA or evntB ...
            //    @(evntA or evntB);
            // which is a valid execution. Race conditions be fun to debug,
            // but they are a responsibility of the user.

            AstSenTree* const senTreep = activep->sentreep();
            FileLine* const flp = senTreep->fileline();

            // Create an 'AstIf' sensitive to the suspending triggers
            AstIf* const ifp = V3Sched::util::createIfFromSenTree(senTreep);
            m_commitFuncp->addStmtsp(ifp);

            // Commit the processes suspended on this sensitivity expression
            //  in the **else** branch, when the event is known to be not fired.
            AstVarRef* const refp = new AstVarRef{flp, schedulerp, VAccess::READWRITE};
            AstCMethodHard* const callp = new AstCMethodHard{flp, refp, VCMethod::SCHED_COMMIT};
            callp->dtypeSetVoid();
            if (resumep->pinsp()) callp->addPinsp(resumep->pinsp()->cloneTree(false));
            ifp->addElsesp(callp->makeStmt());
        }
        // We still haven't created a commit function (no trigger schedulers), return null
        if (!m_commitFuncp) return nullptr;
    }
    AstCCall* const callp = new AstCCall{m_commitFuncp->fileline(), m_commitFuncp};
    callp->dtypeSetVoid();
    return callp;
}

//============================================================================
// Creates the timing kit and marks variables written by suspendables

class AwaitVisitor final : public VNVisitor {
    // NODE STATE
    //  AstSenTree::user1()  -> bool.  Set true if the sentree has been visited.
    const VNUser1InUse m_inuser1;

    // STATE
    bool m_inProcess = false;  // Are we in a process?
    bool m_gatherVars = false;  // Should we gather vars in m_writtenBySuspendable?
    AstScope* const m_scopeTopp;  // Scope at the top
    LogicByScope& m_lbs;  // Timing resume actives
    AstNodeStmt*& m_postUpdatesr;  // Post updates for the trigger eval function
    // Additional var sensitivities
    std::map<const AstVarScope*, std::set<AstSenTree*>>& m_externalDomains;
    std::set<AstSenTree*> m_processDomains;  // Sentrees from the current process
    // Variables written by suspendable processes
    std::vector<AstVarScope*> m_writtenBySuspendable;

    // METHODS
    // Add arguments to a resume() call based on arguments in the suspending call
    void addResumePins(AstCMethodHard* const resumep, AstNodeExpr* pinsp) {
        AstCExpr* const exprp = VN_CAST(pinsp, CExpr);
        AstText* const textp = VN_CAST(exprp->nodesp(), Text);
        if (textp) {
            // The first argument, vlProcess, isn't used by any of resume() methods, skip it
            if ((pinsp = VN_CAST(pinsp->nextp(), NodeExpr))) {
                resumep->addPinsp(pinsp->cloneTree(false));
            }
        } else {
            resumep->addPinsp(pinsp->cloneTree(false));
        }
    }
    // Create an active with a timing scheduler resume() call
    void createResumeActive(AstCAwait* const awaitp) {
        auto* const methodp = VN_AS(awaitp->exprp(), CMethodHard);
        AstVarScope* const schedulerp = VN_AS(methodp->fromp(), VarRef)->varScopep();
        AstSenTree* const sentreep = awaitp->sentreep();
        FileLine* const flp = sentreep->fileline();
        // Create a resume() call on the timing scheduler
        auto* const resumep = new AstCMethodHard{
            flp, new AstVarRef{flp, schedulerp, VAccess::READWRITE}, VCMethod::SCHED_RESUME};
        resumep->dtypeSetVoid();
        if (schedulerp->dtypep()->basicp()->isTriggerScheduler()) {
            UASSERT_OBJ(methodp->pinsp(), methodp,
                        "Trigger method should have pins from V3Timing");
            // The first pin is the commit boolean, the rest (if any) should be debug info
            // See V3Timing for details
            if (AstNode* const dbginfop = methodp->pinsp()->nextp()) {
                if (methodp->pinsp()) addResumePins(resumep, static_cast<AstNodeExpr*>(dbginfop));
            }
        } else if (schedulerp->dtypep()->basicp()->isDynamicTriggerScheduler()) {
            auto* const postp = resumep->cloneTree(false);
            postp->method(VCMethod::SCHED_DO_POST_UPDATES);
            m_postUpdatesr = AstNode::addNext(m_postUpdatesr, postp->makeStmt());
        }
        // Put it in an active
        AstActive* const activep = new AstActive{flp, "_timing", sentreep};
        activep->addStmtsp(resumep->makeStmt());
        m_lbs.emplace_back(m_scopeTopp, activep);
    }

    // VISITORS
    void visit(AstNodeProcedure* const nodep) override {
        UASSERT_OBJ(!m_inProcess && !m_gatherVars && m_processDomains.empty()
                        && m_writtenBySuspendable.empty(),
                    nodep, "Process in process?");
        m_inProcess = true;
        m_gatherVars = nodep->isSuspendable();  // Only gather vars in a suspendable
        const VNUser2InUse user2InUse;  // AstVarScope -> bool: Set true if var has been added
                                        // to m_writtenBySuspendable
        iterateChildren(nodep);
        for (AstVarScope* const vscp : m_writtenBySuspendable) {
            m_externalDomains[vscp].insert(m_processDomains.begin(), m_processDomains.end());
            vscp->varp()->setWrittenBySuspendable();
        }
        m_processDomains.clear();
        m_writtenBySuspendable.clear();
        m_inProcess = false;
        m_gatherVars = false;
    }
    void visit(AstFork* nodep) override {
        VL_RESTORER(m_gatherVars);
        if (m_inProcess) m_gatherVars = true;
        // If not in a process, we don't need to gather variables or domains
        iterateChildren(nodep);
    }
    void visit(AstCAwait* nodep) override {
        if (AstSenTree* const sentreep = nodep->sentreep()) {
            if (!sentreep->user1SetOnce()) createResumeActive(nodep);
            nodep->clearSentreep();  // Clear as these sentrees will get deleted later
            if (m_inProcess) m_processDomains.insert(sentreep);
        }
    }
    void visit(AstNodeVarRef* nodep) override {
        if (m_gatherVars && nodep->access().isWriteOrRW() && !nodep->varp()->ignoreSchedWrite()
            && !nodep->varScopep()->user2SetOnce()) {
            m_writtenBySuspendable.push_back(nodep->varScopep());
        }
    }
    void visit(AstExprStmt* nodep) override { iterateChildren(nodep); }

    //--------------------
    void visit(AstNode* nodep) override { iterateChildren(nodep); }

public:
    // CONSTRUCTORS
    explicit AwaitVisitor(AstNetlist* nodep, LogicByScope& lbs, AstNodeStmt*& postUpdatesr,
                          std::map<const AstVarScope*, std::set<AstSenTree*>>& externalDomains)
        : m_scopeTopp{nodep->topScopep()->scopep()}
        , m_lbs{lbs}
        , m_postUpdatesr{postUpdatesr}
        , m_externalDomains{externalDomains} {
        iterate(nodep);
    }
    ~AwaitVisitor() override = default;
};

TimingKit prepareTiming(AstNetlist* const netlistp) {
    if (!v3Global.usesTiming()) return {};
    LogicByScope lbs;
    AstNodeStmt* postUpdates = nullptr;
    std::map<const AstVarScope*, std::set<AstSenTree*>> externalDomains;
    AwaitVisitor{netlistp, lbs, postUpdates, externalDomains};
    return {std::move(lbs), postUpdates, std::move(externalDomains)};
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
            AstBasicDType* const dtypep = varp->dtypep()->basicp();
            // If not a fork..join, copy. All write refs should've been handled by V3Fork
            bool passByValue = !m_forkp->joinType().join();
            if (!varp->isFuncLocal()) {
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
            AstVarScope* const vscp = refp->varScopep();
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
        if (nodep->needProcess()) {
            newfuncp->setNeedProcess();
            newfuncp->addStmtsp(new AstCStmt{flp, "vlProcess->state(VlProcess::FINISHED);"});
        }
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
    TransformForksVisitor{netlistp};
    V3Global::dumpCheckGlobalTree("transform_forks", 0, dumpTreeEitherLevel() >= 3);
}

}  // namespace V3Sched
