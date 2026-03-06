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
// V3Sched::schedule is the top level entry-point to the scheduling algorithm
// at a high level, the process is:
//
//  - Gather and classify all logic in the design based on what triggers its execution
//  - Schedule static, initial and final logic classes in source order
//  - Break combinational cycles by introducing hybrid logic
//  - Create 'settle' region that restores the combinational invariant
//  - Partition the clocked and combinational (including hybrid) logic into pre/act/nba.
//    All clocks (signals referenced in an AstSenTree) generated via a blocking assignment
//    (including combinationally generated signals) are computed within the act region.
//  - Replicate combinational logic
//  - Create input combinational logic loop
//  - Create the pre/act/nba triggers
//  - Create the 'act' region evaluation function
//  - Create the 'nba' region evaluation function
//  - Bolt it all together to create the '_eval' function
//
// Details of the algorithm are described in the internals documentation docs/internals.rst
//
//*************************************************************************

#include "V3PchAstNoMT.h"  // VL_MT_DISABLED_CODE_UNIT

#include "V3Sched.h"

#include "V3Const.h"
#include "V3EmitCBase.h"
#include "V3EmitV.h"
#include "V3Graph.h"
#include "V3GraphStream.h"
#include "V3Order.h"
#include "V3SenExprBuilder.h"
#include "V3Stats.h"

VL_DEFINE_DEBUG_FUNCTIONS;

namespace V3Sched {

namespace {

//============================================================================
// Utility functions

AstCFunc* createScopeSubFunc(AstCFunc* topFuncp, AstScope* scopep,
                             const string& suffix = string{}) {
    const string subName{topFuncp->name() + "__" + scopep->nameDotless() + suffix};
    AstCFunc* const subFuncp = new AstCFunc{scopep->fileline(), subName, scopep};
    subFuncp->isLoose(true);
    subFuncp->isConst(false);
    subFuncp->declPrivate(true);
    subFuncp->slow(topFuncp->slow());
    scopep->addBlocksp(subFuncp);
    topFuncp->addStmtsp(util::callVoidFunc(subFuncp));
    return subFuncp;
}

struct StaticUnit final {
    AstScope* m_scopep = nullptr;
    AstNode* m_nodep = nullptr;
    size_t m_seq = 0;
};

struct StaticUnitSummary final {
    std::unordered_set<AstVarScope*> m_reads;
    std::unordered_set<AstVarScope*> m_writes;
    std::unordered_set<AstCFunc*> m_callees;
    std::unordered_set<AstNodeFTask*> m_taskCallees;
    std::vector<std::pair<AstClass*, std::string>> m_unresolvedMethods;
};

using ScopeVarMap = std::unordered_map<AstVar*, AstVarScope*>;
using ScopeVarListMap = std::unordered_map<AstVar*, std::vector<AstVarScope*>>;

class StaticDepCollector final : public VNVisitorConst {
    const ScopeVarListMap& m_allVarMap;
    const ScopeVarMap& m_varMap;
    StaticUnitSummary& m_summary;

    AstVarScope* resolveVarScope(const AstNodeVarRef* refp) const {
        if (AstVarScope* const vscp = refp->varScopep()) return vscp;
        const auto it = m_allVarMap.find(refp->varp());
        if (it != m_allVarMap.end() && it->second.size() == 1) return it->second.front();
        return nullptr;
    }

    void noteRead(const AstNodeVarRef* refp) {
        if (AstVarScope* const vscp = resolveVarScope(refp)) m_summary.m_reads.insert(vscp);
    }

    void noteReadConservative(const AstNodeVarRef* refp) {
        if (AstVarScope* const vscp = refp->varScopep()) {
            m_summary.m_reads.insert(vscp);
            return;
        }
        const auto it = m_allVarMap.find(refp->varp());
        if (it == m_allVarMap.end()) return;
        for (AstVarScope* const vscp : it->second) m_summary.m_reads.insert(vscp);
    }

    static AstClass* receiverClassFrom(const AstMethodCall* methodp) {
        if (!methodp) return nullptr;
        if (AstNodeExpr* const fromp = methodp->fromp()) {
            if (!fromp->dtypep()) return nullptr;
            if (AstClassRefDType* const classRefp
                = VN_CAST(fromp->dtypep()->skipRefp(), ClassRefDType)) {
                return classRefp->classp();
            }
        }
        if (AstClassPackage* const classPkgp = VN_CAST(methodp->classOrPackagep(), ClassPackage)) {
            return classPkgp->classp();
        }
        return nullptr;
    }

    void visit(AstNodeVarRef* nodep) override {
        AstVarScope* const vscp = resolveVarScope(nodep);
        if (!vscp) return;
        if (nodep->access().isReadOrRW()) m_summary.m_reads.insert(vscp);
        if (nodep->access().isWriteOrRW()
            && (!nodep->varp()->ignoreSchedWrite() || nodep->varp()->isConst())) {
            m_summary.m_writes.insert(vscp);
        }
    }
    void visit(AstNodeFTaskRef* nodep) override {
        AstNodeFTask* const taskp = nodep->taskp();
        if (taskp) m_summary.m_taskCallees.insert(taskp);
        if (const AstMethodCall* const methodp = VN_CAST(nodep, MethodCall)) {
            if (AstNodeExpr* const fromp = methodp->fromp()) {
                fromp->foreach([&](const AstNodeVarRef* refp) {
                    if (taskp) {
                        noteRead(refp);
                    } else {
                        noteReadConservative(refp);
                    }
                });
            }
            if (!taskp) {
                if (AstClass* const classp = receiverClassFrom(methodp)) {
                    m_summary.m_unresolvedMethods.emplace_back(classp, methodp->name());
                }
            }
        }
        iterateChildrenConst(nodep);
    }
    void visit(AstNodeCCall* nodep) override {
        if (AstCFunc* const funcp = nodep->funcp()) m_summary.m_callees.insert(funcp);
        iterateChildrenConst(nodep);
    }
    void visit(AstVar* nodep) override {
        if (nodep->valuep()) {
            const auto it = m_varMap.find(nodep);
            if (it != m_varMap.end()) m_summary.m_writes.insert(it->second);
        }
        iterateChildrenConst(nodep);
    }
    void visit(AstNode* nodep) override { iterateChildrenConst(nodep); }

public:
    StaticDepCollector(AstNode* nodep, const ScopeVarListMap& allVarMap, const ScopeVarMap& varMap,
                       StaticUnitSummary& summary)
        : m_allVarMap{allVarMap}
        , m_varMap{varMap}
        , m_summary{summary} {
        iterateConst(nodep);
    }
};

class StaticUnitVertex final : public V3GraphVertex {
    size_t m_idx = 0;
    size_t m_seq = 0;

public:
    StaticUnitVertex(V3Graph* graphp, size_t idx, size_t seq)
        : V3GraphVertex{graphp}
        , m_idx{idx}
        , m_seq{seq} {}
    size_t idx() const { return m_idx; }
    size_t seq() const { return m_seq; }
};

struct StaticUnitSeqLess final {  // Tie-break unordered ready vertices by source order.
    bool operator()(const V3GraphVertex* a, const V3GraphVertex* b) const {
        return static_cast<const StaticUnitVertex*>(a)->seq()
               < static_cast<const StaticUnitVertex*>(b)->seq();
    }
};

std::vector<const AstSenTree*> getSenTreesUsedBy(const std::vector<const LogicByScope*>& lbsps) {
    const VNUser1InUse user1InUse;
    std::vector<const AstSenTree*> result;
    for (const LogicByScope* const lbsp : lbsps) {
        for (const auto& pair : *lbsp) {
            AstActive* const activep = pair.second;
            AstSenTree* const senTreep = activep->sentreep();
            if (senTreep->user1SetOnce()) continue;
            if (senTreep->hasClocked() || senTreep->hasHybrid()) result.push_back(senTreep);
        }
    }
    return result;
}

void remapSensitivities(const LogicByScope& lbs,
                        const std::unordered_map<const AstSenTree*, AstSenTree*>& senTreeMap) {
    for (const auto& pair : lbs) {
        AstActive* const activep = pair.second;
        AstSenTree* const senTreep = activep->sentreep();
        if (senTreep->hasCombo()) continue;
        activep->sentreep(senTreeMap.at(senTreep));
    }
}

void invertAndMergeSenTreeMap(
    V3Order::TrigToSenMap& result,
    const std::unordered_map<const AstSenTree*, AstSenTree*>& senTreeMap) {
    for (const auto& pair : senTreeMap) result.emplace(pair.second, pair.first);
}

std::vector<AstSenTree*>
findTriggeredIface(const AstVarScope* vscp,
                   const VirtIfaceTriggers::IfaceMemberSensMap& vifMemberTriggered) {
    const AstIface* ifacep;
    if (vscp->varp()->isVirtIface()) {
        // If `vscp->varp()->isVirtIface()` is true then the interface type that viface is pointing
        // to is under `VN_AS(vscp->varp()->dtypep(), IfaceRefDType)->ifacep()`

        ifacep = VN_AS(vscp->varp()->dtypep(), IfaceRefDType)->ifacep();

        // Virtual interface is sensitive to a different interface type than it is a virtual type
        // of - this may be a valid behaviour but this function does not expects that
        UASSERT_OBJ(vscp->varp()->sensIfacep() == nullptr, vscp,
                    "Virtual interface has an ambiguous type - "
                        << vscp->varp()->sensIfacep()->prettyTypeName()
                        << " != " << ifacep->prettyTypeName());
    } else {
        // If `vscp->varp()` is of a non-virtual interface type it has `sensIfacep()` set to
        // interface it is sensitive to
        ifacep = vscp->varp()->sensIfacep();
    }
    UASSERT_OBJ(ifacep, vscp, "Variable is not sensitive for any interface");
    std::vector<AstSenTree*> result;
    for (const auto& memberIt : vifMemberTriggered) {
        if (memberIt.first.m_ifacep == ifacep) result.push_back(memberIt.second);
    }
    UASSERT_OBJ(!result.empty(), vscp, "Did not find virtual interface trigger");
    return result;
}

//============================================================================
// Eval loop builder

struct EvalLoop final {
    // Flag set to true on entry to the first iteration of the loop
    AstVarScope* firstIterp;
    // The loop itself and statements around it
    AstNodeStmt* stmtsp;
};

// Create an eval loop with all the trimmings.
EvalLoop createEvalLoop(
    AstNetlist* netlistp,  //
    const std::string& tag,  // Tag for current phase
    const string& name,  // Name of current phase
    bool slow,  // Should create slow functions
    const TriggerKit& trigKit,  // The trigger kit
    AstVarScope* trigp,  // The trigger vector - may be nullptr if no triggers or using 'condp'
    AstNodeExpr* condp,  // Explicit condition that must be true to run 'phaseWorkp'
    AstNodeStmt* innerp,  // The inner loop, if any
    AstNodeStmt* phasePrepp,  // Prep statements run before checking triggers
    AstNodeStmt* phaseWorkp,  // The work to do if anything triggered
    // Extra statements to run after the work, even if no triggers fired. This function is
    // passed a variable, which must be set to true if we must continue and loop again,
    // and must be unmodified otherwise.
    std::function<AstNodeStmt*(AstVarScope*)> phaseExtra = [](AstVarScope*) { return nullptr; }  //
) {
    UASSERT(!trigp || !condp, "Cannot use both 'trigp' and 'condp' in 'createEvalLoop'");

    // All work is under a trigger or condition, so if there are none,
    // there is nothing to do besides executing the inner loop.
    if (!trigp && !condp) return {nullptr, innerp};

    const std::string varPrefix = "__V" + tag;
    AstScope* const scopeTopp = netlistp->topScopep()->scopep();
    FileLine* const flp = netlistp->fileline();

    // We wrap the prep/cond/work in a function for readability
    AstCFunc* const phaseFuncp = util::makeTopFunction(netlistp, "_eval_phase__" + tag, slow);
    {
        // Add the preparatory statements
        phaseFuncp->addStmtsp(phasePrepp);

        // The execute flag
        AstVarScope* const executeFlagp = scopeTopp->createTemp(varPrefix + "Execute", 1);
        executeFlagp->varp()->noReset(true);

        // If there is work in this phase, execute it if any triggers fired
        if (phaseWorkp) {
            AstNodeExpr* const lhsp = new AstVarRef{flp, executeFlagp, VAccess::WRITE};
            // If using explicit condition, that directly determines whether to execute,
            // otherwise check if any triggers are fired
            AstNodeExpr* const rhsp = condp ? condp : trigKit.newAnySetCall(trigp);
            phaseFuncp->addStmtsp(new AstAssign{flp, lhsp, rhsp});

            // Add the work
            AstIf* const ifp = new AstIf{flp, new AstVarRef{flp, executeFlagp, VAccess::READ}};
            ifp->addThensp(phaseWorkp);
            phaseFuncp->addStmtsp(ifp);
        }

        // Construct the extra statements
        AstNodeStmt* const extraWorkp = phaseExtra(executeFlagp);
        if (extraWorkp) phaseFuncp->addStmtsp(extraWorkp);

        // The function returns ture iff it did run work
        phaseFuncp->rtnType("bool");
        AstNodeExpr* const retp
            = phaseWorkp || extraWorkp
                  ? static_cast<AstNodeExpr*>(new AstVarRef{flp, executeFlagp, VAccess::READ})
                  : static_cast<AstNodeExpr*>(new AstConst{flp, AstConst::BitFalse{}});
        phaseFuncp->addStmtsp(new AstCReturn{flp, retp});
    }

    // The result statements
    AstNodeStmt* stmtps = nullptr;

    // Prof-exec section push
    if (v3Global.opt.profExec()) {  //
        stmtps = AstCStmt::profExecSectionPush(flp, "loop " + tag);
    }

    const auto addVar = [&](const std::string& name, int width, uint32_t initVal, bool init) {
        const string tempName{"__V" + tag + name};
        AstVarScope* const vscp = tempName == "__VstlFirstIteration"
                                      ? netlistp->stlFirstIterationp()
                                      : scopeTopp->createTemp(tempName, width);
        vscp->varp()->noReset(true);
        vscp->varp()->isInternal(true);
        if (init) stmtps = AstNode::addNext(stmtps, util::setVar(vscp, initVal));
        return vscp;
    };

    // The iteration counter
    AstVarScope* const counterp = addVar("IterCount", 32, 0, true);
    // The first iteration flag - cleared in 'phasePrepp' if used
    AstVarScope* const firstIterFlagp = addVar("FirstIteration", 1, 1, true);
    // Phase function result
    AstVarScope* const phaseResultp = addVar("PhaseResult", 1, 0, false);

    // The loop
    {
        AstLoop* const loopp = new AstLoop{flp};
        stmtps->addNext(loopp);

        // Check the iteration limit (aborts if exceeded). Dump triggers if using triggers.
        AstNodeStmt* dumpCallp = trigp ? trigKit.newDumpCall(trigp, tag, false) : nullptr;
        loopp->addStmtsp(util::checkIterationLimit(netlistp, name, counterp, dumpCallp));
        // Increment the iteration counter
        loopp->addStmtsp(util::incrementVar(counterp));

        // Execute the inner loop
        loopp->addStmtsp(innerp);

        // Call the phase function to execute the current work. If we did
        // work, then need to loop again, so set the continuation flag.
        // If used, the first iteration flag is cleared when consumed, no
        // need to reset it
        AstCCall* const callp = new AstCCall{flp, phaseFuncp};
        callp->dtypeSetBit();
        AstAssign* const resultAssignp
            = new AstAssign{flp, new AstVarRef{flp, phaseResultp, VAccess::WRITE}, callp};
        loopp->addStmtsp(resultAssignp);
        // Clear FirstIteration flag
        AstAssign* const firstClearp
            = new AstAssign{flp, new AstVarRef{flp, firstIterFlagp, VAccess::WRITE},
                            new AstConst{flp, AstConst::BitFalse()}};
        loopp->addStmtsp(firstClearp);
        // Continues until the continuation flag is clear
        loopp->addStmtsp(
            new AstLoopTest{flp, loopp, new AstVarRef{flp, phaseResultp, VAccess::READ}});
    }

    // Prof-exec section pop
    if (v3Global.opt.profExec()) {
        stmtps->addNext(AstCStmt::profExecSectionPop(flp, "loop " + tag));
    }

    return {firstIterFlagp, stmtps};
}

//============================================================================
// Collect and classify all logic in the design

LogicClasses gatherLogicClasses(AstNetlist* netlistp) {
    LogicClasses result;

    netlistp->foreach([&](AstScope* scopep) {
        scopep->foreach([&](AstActive* activep) {
            AstSenTree* const senTreep = activep->sentreep();
            if (senTreep->hasStatic()) {
                UASSERT_OBJ(!senTreep->sensesp()->nextp(), activep,
                            "static initializer with additional sensitivities");
                result.m_static.emplace_back(scopep, activep);
            } else if (senTreep->hasInitial()) {
                UASSERT_OBJ(!senTreep->sensesp()->nextp(), activep,
                            "'initial' logic with additional sensitivities");
                result.m_initial.emplace_back(scopep, activep);
            } else if (senTreep->hasFinal()) {
                UASSERT_OBJ(!senTreep->sensesp()->nextp(), activep,
                            "'final' logic with additional sensitivities");
                result.m_final.emplace_back(scopep, activep);
            } else if (senTreep->hasCombo()) {
                UASSERT_OBJ(!senTreep->sensesp()->nextp(), activep,
                            "combinational logic with additional sensitivities");
                if (VN_IS(activep->stmtsp(), AlwaysPostponed)) {
                    result.m_postponed.emplace_back(scopep, activep);
                } else {
                    result.m_comb.emplace_back(scopep, activep);
                }
            } else {
                UASSERT_OBJ(senTreep->hasClocked(), activep, "What else could it be?");
                if (VN_IS(activep->stmtsp(), AlwaysObserved)) {
                    result.m_observed.emplace_back(scopep, activep);
                } else if (VN_IS(activep->stmtsp(), AlwaysReactive)) {
                    result.m_reactive.emplace_back(scopep, activep);
                } else {
                    result.m_clocked.emplace_back(scopep, activep);
                }
            }
        });
    });

    return result;
}

//============================================================================
// Simple ordering in source order

void orderSequentially(AstCFunc* funcp, const LogicByScope& lbs) {
    const VNUser1InUse user1InUse;  // AstScope -> AstCFunc: the sub-function for the scope
    const VNUser2InUse user2InUse;  // AstScope -> int: sub-function counter used for names
    for (const auto& pair : lbs) {
        AstScope* const scopep = pair.first;
        AstActive* const activep = pair.second;
        // Create a sub-function per scope so we can V3Combine them later
        if (!scopep->user1p()) scopep->user1p(createScopeSubFunc(funcp, scopep));
        // Add statements to sub-function
        for (AstNode *logicp = activep->stmtsp(), *nextp; logicp; logicp = nextp) {
            auto* subFuncp = VN_AS(scopep->user1p(), CFunc);
            nextp = logicp->nextp();
            if (AstNodeProcedure* const procp = VN_CAST(logicp, NodeProcedure)) {
                if (AstNode* bodyp = procp->stmtsp()) {
                    bodyp->unlinkFrBackWithNext();
                    // If the process is suspendable, we need a separate function (a coroutine)
                    if (procp->isSuspendable()) {
                        funcp->slow(false);
                        subFuncp = createScopeSubFunc(funcp, scopep,
                                                      "__Vtiming__" + cvtToStr(scopep->user2Inc()));
                        subFuncp->rtnType("VlCoroutine");
                        if (VN_IS(procp, Always)) {
                            subFuncp->slow(false);
                            FileLine* const flp = procp->fileline();
                            AstNodeExpr* const condp = new AstCExpr{
                                flp, "VL_LIKELY(!vlSymsp->_vm_contextp__->gotFinish())", 1};
                            AstLoop* const loopp = new AstLoop{flp};
                            loopp->addStmtsp(new AstLoopTest{flp, loopp, condp});
                            loopp->addStmtsp(bodyp);
                            bodyp = loopp;
                        }
                    }
                    subFuncp->addStmtsp(bodyp);
                    if (procp->needProcess()) subFuncp->setNeedProcess();
                    util::splitCheck(subFuncp);
                }
            } else {
                logicp->unlinkFrBack();
                subFuncp->addStmtsp(logicp);
            }
        }
        if (activep->backp()) activep->unlinkFrBack();
        VL_DO_DANGLING(activep->deleteTree(), activep);
    }
}

// For static initializers, prefer ordering by data dependencies across scopes.
// If there are cycles, preserve source order within the unresolved remainder.
void orderStaticByDependencies(AstCFunc* funcp, const LogicByScope& lbs) {
    std::vector<StaticUnit> units;
    std::vector<StaticUnitSummary> summaries;
    units.reserve(lbs.size() * 2);
    summaries.reserve(lbs.size() * 2);
    ScopeVarListMap allVarMap;

    for (const auto& pair : lbs) {
        AstScope* const scopep = pair.first;
        for (AstVarScope* vscp = scopep->varsp(); vscp; vscp = VN_AS(vscp->nextp(), VarScope)) {
            allVarMap[vscp->varp()].push_back(vscp);
        }
    }

    size_t seq = 0;
    for (const auto& pair : lbs) {
        AstScope* const scopep = pair.first;
        AstActive* const activep = pair.second;
        ScopeVarMap varMap;
        for (AstVarScope* vscp = scopep->varsp(); vscp; vscp = VN_AS(vscp->nextp(), VarScope)) {
            varMap.emplace(vscp->varp(), vscp);
        }
        for (AstNode *logicp = activep->stmtsp(), *logicNextp; logicp; logicp = logicNextp) {
            logicNextp = logicp->nextp();
            if (AstNodeProcedure* const procp = VN_CAST(logicp, NodeProcedure)) {
                for (AstNode *stmtp = procp->stmtsp(), *stmtNextp; stmtp; stmtp = stmtNextp) {
                    stmtNextp = stmtp->nextp();
                    stmtp->unlinkFrBack();
                    units.emplace_back();
                    summaries.emplace_back();
                    StaticUnit& unit = units.back();
                    StaticUnitSummary& summary = summaries.back();
                    unit.m_scopep = scopep;
                    unit.m_nodep = stmtp;
                    unit.m_seq = seq++;
                    StaticDepCollector{stmtp, allVarMap, varMap, summary};
                }
                if (procp->backp()) procp->unlinkFrBack();
                VL_DO_DANGLING(procp->deleteTree(), procp);
            } else {
                logicp->unlinkFrBack();
                units.emplace_back();
                summaries.emplace_back();
                StaticUnit& unit = units.back();
                StaticUnitSummary& summary = summaries.back();
                unit.m_scopep = scopep;
                unit.m_nodep = logicp;
                unit.m_seq = seq++;
                StaticDepCollector{logicp, allVarMap, varMap, summary};
            }
        }
        if (activep->backp()) activep->unlinkFrBack();
        VL_DO_DANGLING(activep->deleteTree(), activep);
    }

    const size_t n = units.size();
    UASSERT_OBJ(summaries.size() == n, funcp, "Static summaries out of sync with units");

    // Calls in static units may hide reads in outlined helper CFuncs / class tasks.
    // Pull transitive callee reads into the calling unit so data-dependency edges can be formed.
    using ReadSet = std::unordered_set<AstVarScope*>;
    std::map<std::pair<AstClass*, std::string>, std::vector<AstNodeFTask*>> unresolvedMethodTargets;
    std::unordered_map<AstNode*, size_t> callableIndex;
    std::vector<AstNode*> callableNodes;
    std::vector<StaticUnitSummary> callableDirect;
    std::vector<std::unordered_set<size_t>> callSucc;
    std::vector<ReadSet> callableReads;

    auto collectDirectSummary = [&](AstNode* stmtsp) {
        StaticUnitSummary direct;
        const ScopeVarMap emptyVarMap;
        for (AstNode* stmtp = stmtsp; stmtp; stmtp = stmtp->nextp()) {
            StaticDepCollector{stmtp, allVarMap, emptyVarMap, direct};
        }
        return direct;
    };
    auto findUnresolvedTargets = [&](AstClass* classp, const std::string& methodName)
        -> const std::vector<AstNodeFTask*>& {
        static const std::vector<AstNodeFTask*> empty;
        if (!classp) return empty;
        const auto key = std::make_pair(classp, methodName);
        const auto it = unresolvedMethodTargets.find(key);
        if (it != unresolvedMethodTargets.end()) return it->second;
        std::vector<AstNodeFTask*> targets;
        std::function<void(AstClass*)> scanClass = [&](AstClass* currentp) {
            if (!currentp) return;
            if (const AstClassExtends* const cextendsp = currentp->extendsp()) {
                scanClass(cextendsp->classp());
            }
            for (AstNode* stmtp = currentp->stmtsp(); stmtp; stmtp = stmtp->nextp()) {
                if (AstNodeFTask* const memberp = VN_CAST(stmtp, NodeFTask)) {
                    if (memberp->name() == methodName) targets.push_back(memberp);
                } else if (AstScope* const scopep = VN_CAST(stmtp, Scope)) {
                    for (AstNode* blockp = scopep->blocksp(); blockp; blockp = blockp->nextp()) {
                        if (AstNodeFTask* const memberp = VN_CAST(blockp, NodeFTask)) {
                            if (memberp->name() == methodName) targets.push_back(memberp);
                        }
                    }
                }
            }
        };
        scanClass(classp);
        return unresolvedMethodTargets.emplace(key, std::move(targets)).first->second;
    };

    auto ensureCallable = [&](AstNode* callablep) {
        UASSERT_OBJ(callablep, funcp, "Null callable");
        const auto it = callableIndex.find(callablep);
        if (it != callableIndex.end()) return it->second;
        const size_t idx = callableNodes.size();
        callableIndex.emplace(callablep, idx);
        callableNodes.push_back(callablep);
        callableDirect.emplace_back();
        callSucc.emplace_back();
        return idx;
    };

    auto callableStmtsp = [&](AstNode* callablep) -> AstNode* {
        if (AstCFunc* const cfuncp = VN_CAST(callablep, CFunc)) return cfuncp->stmtsp();
        if (AstNodeFTask* const taskp = VN_CAST(callablep, NodeFTask)) return taskp->stmtsp();
        callablep->v3fatalSrc("Unexpected callable node type");
        return nullptr;  // LCOV_EXCL_LINE
    };

    for (const StaticUnitSummary& summary : summaries) {
        for (AstCFunc* const calleep : summary.m_callees) ensureCallable(calleep);
        for (AstNodeFTask* const taskp : summary.m_taskCallees) ensureCallable(taskp);
        for (const auto& unresolved : summary.m_unresolvedMethods) {
            for (AstNodeFTask* const targetp : findUnresolvedTargets(unresolved.first, unresolved.second)) {
                ensureCallable(targetp);
            }
        }
    }

    for (size_t idx = 0; idx < callableNodes.size(); ++idx) {
        const StaticUnitSummary direct = collectDirectSummary(callableStmtsp(callableNodes[idx]));
        callableDirect[idx] = direct;
        for (AstCFunc* const calleep : direct.m_callees) {
            const size_t to = ensureCallable(calleep);
            callSucc[idx].insert(to);
        }
        for (AstNodeFTask* const taskp : direct.m_taskCallees) {
            const size_t to = ensureCallable(taskp);
            callSucc[idx].insert(to);
        }
        for (const auto& unresolved : direct.m_unresolvedMethods) {
            for (AstNodeFTask* const targetp : findUnresolvedTargets(unresolved.first, unresolved.second)) {
                const size_t to = ensureCallable(targetp);
                callSucc[idx].insert(to);
            }
        }
    }

    if (!callableNodes.empty()) {
        const size_t callN = callableNodes.size();
        std::vector<int> index(callN, -1);
        std::vector<int> lowlink(callN, 0);
        std::vector<int> compOf(callN, -1);
        std::vector<size_t> stack;
        std::vector<bool> onStack(callN, false);
        int nextIndex = 0;
        int compCount = 0;

        std::function<void(size_t)> strongConnect = [&](size_t v) {
            index[v] = nextIndex;
            lowlink[v] = nextIndex;
            ++nextIndex;
            stack.push_back(v);
            onStack[v] = true;

            for (const size_t w : callSucc[v]) {
                if (index[w] == -1) {
                    strongConnect(w);
                    lowlink[v] = std::min(lowlink[v], lowlink[w]);
                } else if (onStack[w]) {
                    lowlink[v] = std::min(lowlink[v], index[w]);
                }
            }

            if (lowlink[v] == index[v]) {
                while (true) {
                    const size_t w = stack.back();
                    stack.pop_back();
                    onStack[w] = false;
                    compOf[w] = compCount;
                    if (w == v) break;
                }
                ++compCount;
            }
        };

        for (size_t v = 0; v < callN; ++v) {
            if (index[v] == -1) strongConnect(v);
        }

        std::vector<ReadSet> compReads(compCount);
        std::vector<std::unordered_set<int>> compSucc(compCount);
        for (size_t v = 0; v < callN; ++v) {
            ReadSet& reads = compReads[compOf[v]];
            reads.insert(callableDirect[v].m_reads.begin(), callableDirect[v].m_reads.end());
            for (const size_t w : callSucc[v]) {
                const int fromComp = compOf[v];
                const int toComp = compOf[w];
                if (fromComp != toComp) compSucc[fromComp].insert(toComp);
            }
        }

        std::vector<int> indegree(compCount, 0);
        for (int fromComp = 0; fromComp < compCount; ++fromComp) {
            for (const int toComp : compSucc[fromComp]) ++indegree[toComp];
        }
        std::vector<int> topo;
        topo.reserve(compCount);
        std::vector<int> queue;
        queue.reserve(compCount);
        for (int comp = 0; comp < compCount; ++comp) {
            if (indegree[comp] == 0) queue.push_back(comp);
        }
        for (size_t qi = 0; qi < queue.size(); ++qi) {
            const int comp = queue[qi];
            topo.push_back(comp);
            for (const int toComp : compSucc[comp]) {
                if (--indegree[toComp] == 0) queue.push_back(toComp);
            }
        }
        UASSERT_OBJ(topo.size() == static_cast<size_t>(compCount), funcp,
                    "Callable SCC condensation graph should be acyclic");

        for (auto it = topo.rbegin(); it != topo.rend(); ++it) {
            ReadSet& reads = compReads[*it];
            for (const int toComp : compSucc[*it]) {
                const ReadSet& calleeReads = compReads[toComp];
                reads.insert(calleeReads.begin(), calleeReads.end());
            }
        }

        callableReads.resize(callN);
        for (size_t v = 0; v < callN; ++v) callableReads[v] = compReads[compOf[v]];
    }

    auto mergeCallableReads = [&](ReadSet& reads, AstNode* callablep) {
        if (!callablep) return;
        const auto it = callableIndex.find(callablep);
        if (it == callableIndex.end()) return;
        const ReadSet& closure = callableReads[it->second];
        reads.insert(closure.begin(), closure.end());
    };

    for (size_t i = 0; i < n; ++i) {
        for (AstCFunc* const calleep : summaries[i].m_callees) mergeCallableReads(summaries[i].m_reads, calleep);
        for (AstNodeFTask* const taskp : summaries[i].m_taskCallees) {
            mergeCallableReads(summaries[i].m_reads, taskp);
        }
        for (const auto& unresolved : summaries[i].m_unresolvedMethods) {
            for (AstNodeFTask* const targetp : findUnresolvedTargets(unresolved.first, unresolved.second)) {
                mergeCallableReads(summaries[i].m_reads, targetp);
            }
        }
    }

    if (n <= 1) {
        if (!units.empty()) {
            AstCFunc* const subFuncp = createScopeSubFunc(funcp, units[0].m_scopep);
            subFuncp->addStmtsp(units[0].m_nodep);
            util::splitCheck(subFuncp);
        }
        return;
    }

    std::vector<std::unordered_set<size_t>> depSucc(n);

    std::unordered_map<AstVarScope*, std::vector<size_t>> writers;
    writers.reserve(n * 4);
    for (size_t i = 0; i < n; ++i) {
        for (AstVarScope* const vscp : summaries[i].m_writes) writers[vscp].push_back(i);
    }

    // Data dependencies: a reader must run after all writers of any read variable.
    for (size_t readerIdx = 0; readerIdx < n; ++readerIdx) {
        for (AstVarScope* const vscp : summaries[readerIdx].m_reads) {
            const auto it = writers.find(vscp);
            if (it == writers.end()) continue;
            for (const size_t writerIdx : it->second) {
                if (writerIdx == readerIdx) continue;
                depSucc[writerIdx].insert(readerIdx);
            }
        }
    }

    V3Graph depGraph;
    std::vector<StaticUnitVertex*> unitVtxps;
    unitVtxps.reserve(n);
    for (size_t i = 0; i < n; ++i) {
        StaticUnitVertex* const vxp = new StaticUnitVertex{&depGraph, i, units[i].m_seq};
        unitVtxps.push_back(vxp);
    }
    for (size_t from = 0; from < n; ++from) {
        for (const size_t to : depSucc[from]) {
            new V3GraphEdge{&depGraph, unitVtxps[from], unitVtxps[to], 1, V3GraphEdge::CUTABLE};
        }
    }
    depGraph.acyclic(&V3GraphEdge::followAlwaysTrue);
    for (V3GraphVertex& vtx : depGraph.vertices()) {
        for (V3GraphEdge* const edgep : vtx.outEdges().unlinkable()) {
            if (edgep->weight() != 0) continue;
            VL_DO_DANGLING(edgep->unlinkDelete(), edgep);
        }
    }

    std::vector<size_t> ordered;
    ordered.reserve(n);
    GraphStream<StaticUnitSeqLess> depOrder{&depGraph, GraphWay::FORWARD, StaticUnitSeqLess{}};
    while (const V3GraphVertex* const vxp = depOrder.nextp()) {
        ordered.push_back(static_cast<const StaticUnitVertex*>(vxp)->idx());
    }
    UASSERT_OBJ(ordered.size() == n, funcp, "Static ordering dropped vertices");

    size_t subFuncNum = 0;
    AstScope* currentScopep = nullptr;
    AstCFunc* currentSubFuncp = nullptr;
    for (const size_t idx : ordered) {
        StaticUnit& unit = units[idx];
        if (unit.m_scopep != currentScopep) {
            if (currentSubFuncp) util::splitCheck(currentSubFuncp);
            currentScopep = unit.m_scopep;
            currentSubFuncp
                = createScopeSubFunc(funcp, currentScopep, "__Vstatic" + cvtToStr(subFuncNum++));
        }
        currentSubFuncp->addStmtsp(unit.m_nodep);
    }
    if (currentSubFuncp) util::splitCheck(currentSubFuncp);
}

//============================================================================
// Create simply ordered functions

AstCFunc* createStatic(AstNetlist* netlistp, const LogicClasses& logicClasses) {
    AstCFunc* const funcp = util::makeTopFunction(netlistp, "_eval_static", /* slow: */ true);
    orderStaticByDependencies(funcp, logicClasses.m_static);
    return funcp;  // Not splitting yet as it is not final
}

void createInitial(AstNetlist* netlistp, const LogicClasses& logicClasses) {
    AstCFunc* const funcp = util::makeTopFunction(netlistp, "_eval_initial", /* slow: */ true);
    orderSequentially(funcp, logicClasses.m_initial);
    util::splitCheck(funcp);
}

AstCFunc* createPostponed(AstNetlist* netlistp, const LogicClasses& logicClasses) {
    if (logicClasses.m_postponed.empty()) return nullptr;
    AstCFunc* const funcp = util::makeTopFunction(netlistp, "_eval_postponed", /* slow: */ true);
    orderSequentially(funcp, logicClasses.m_postponed);
    util::splitCheck(funcp);
    return funcp;
}

void createFinal(AstNetlist* netlistp, const LogicClasses& logicClasses) {
    AstCFunc* const funcp = util::makeTopFunction(netlistp, "_eval_final", /* slow: */ true);
    orderSequentially(funcp, logicClasses.m_final);
    util::splitCheck(funcp);
}

//============================================================================
// Helper that creates virtual interface trigger resets

void addVirtIfaceTriggerAssignments(const VirtIfaceTriggers& virtIfaceTriggers,
                                    uint32_t vifTriggerIndex, uint32_t vifMemberTriggerIndex,
                                    const TriggerKit& trigKit) {
    for (const auto& p : virtIfaceTriggers.m_memberTriggers) {
        trigKit.addExtraTriggerAssignment(p.second, vifMemberTriggerIndex);
        ++vifMemberTriggerIndex;
    }
}

// Order the combinational logic to create the settle loop
void createSettle(AstNetlist* netlistp, AstCFunc* const initFuncp, SenExprBuilder& senExprBulider,
                  LogicClasses& logicClasses) {
    AstCFunc* const funcp = util::makeTopFunction(netlistp, "_eval_settle", true);

    // Clone, because ordering is destructive, but we still need them for "_eval"
    LogicByScope comb = logicClasses.m_comb.clone();
    LogicByScope hybrid = logicClasses.m_hybrid.clone();

    // Nothing to do if there is no logic.
    // While this is rare in real designs, it reduces noise in small tests.
    if (comb.empty() && hybrid.empty()) return;

    // We have an extra trigger denoting this is the first iteration of the settle loop
    TriggerKit::ExtraTriggers extraTriggers;
    const uint32_t firstIterationTrigger = extraTriggers.allocate("first iteration");

    // Gather the relevant sensitivity expressions and create the trigger kit
    const auto& senTreeps = getSenTreesUsedBy({&comb, &hybrid});
    const TriggerKit trigKit = TriggerKit::create(netlistp, initFuncp, senExprBulider, {},
                                                  senTreeps, "stl", extraTriggers, true, false);

    // Remap sensitivities (comb has none, so only do the hybrid)
    remapSensitivities(hybrid, trigKit.mapVec());

    // Create the inverse map from trigger ref AstSenTree to original AstSenTree
    V3Order::TrigToSenMap trigToSen;
    invertAndMergeSenTreeMap(trigToSen, trigKit.mapVec());

    // First trigger is for pure combinational triggers (first iteration)
    AstSenTree* const inputChanged
        = trigKit.newExtraTriggerSenTree(trigKit.vscp(), firstIterationTrigger);

    // Create and the body function
    AstCFunc* const stlFuncp = V3Order::order(
        netlistp, {&comb, &hybrid}, trigToSen, "stl", false, true,
        [=](const AstVarScope*, std::vector<AstSenTree*>& out) { out.push_back(inputChanged); });
    util::splitCheck(stlFuncp);

    // Create the eval loop
    const EvalLoop stlLoop = createEvalLoop(  //
        netlistp, "stl", "Settle", /* slow: */ true, trigKit,
        // Use trigger
        trigKit.vscp(), nullptr,
        // Explicit condition
        // Inner loop statements
        nullptr,
        // Prep statements: Compute the current 'stl' triggers
        [&trigKit] {
            AstNodeStmt* const stmtp = trigKit.newCompBaseCall();
            if (stmtp) stmtp->addNext(trigKit.newDumpCall(trigKit.vscp(), trigKit.name(), true));
            return stmtp;
        }(),
        // Work statements: Invoke the 'stl' function
        util::callVoidFunc(stlFuncp));

    // Add the first iteration trigger to the trigger computation function
    trigKit.addExtraTriggerAssignment(stlLoop.firstIterp, firstIterationTrigger, false);

    // Add the eval loop to the top function
    funcp->addStmtsp(stlLoop.stmtsp);
}

//============================================================================
// Order the replicated combinational logic to create the 'ico' region

AstNode* createInputCombLoop(AstNetlist* netlistp, AstCFunc* const initFuncp,
                             SenExprBuilder& senExprBuilder, LogicByScope& logic,
                             const VirtIfaceTriggers& virtIfaceTriggers) {
    // Nothing to do if no combinational logic is sensitive to top level inputs
    if (logic.empty()) return nullptr;

    // SystemC only: Any top level inputs feeding a combinational logic must be marked,
    // so we can make them sc_sensitive
    if (v3Global.opt.systemC()) {
        logic.foreachLogic([](AstNode* logicp) {
            logicp->foreach([](AstVarRef* refp) {
                if (refp->access().isWriteOnly()) return;
                AstVarScope* const vscp = refp->varScopep();
                if (vscp->scopep()->isTop() && vscp->varp()->isNonOutput()) {
                    vscp->varp()->scSensitive(true);
                }
            });
        });
    }

    // We have some extra trigger denoting external conditions
    AstVarScope* const dpiExportTriggerVscp = netlistp->dpiExportTriggerp();

    TriggerKit::ExtraTriggers extraTriggers;
    const uint32_t firstIterationTrigger = extraTriggers.allocate("first iteration");
    const uint32_t dpiExportTriggerIndex = dpiExportTriggerVscp
                                               ? extraTriggers.allocate("DPI export trigger")
                                               : std::numeric_limits<uint32_t>::max();
    const size_t firstVifTriggerIndex = extraTriggers.size();
    const size_t firstVifMemberTriggerIndex = extraTriggers.size();
    for (const auto& p : virtIfaceTriggers.m_memberTriggers) {
        const auto& item = p.first;
        extraTriggers.allocate("virtual interface member: " + item.m_ifacep->name() + "."
                               + item.m_memberp->name());
    }

    // Gather the relevant sensitivity expressions and create the trigger kit
    const auto& senTreeps = getSenTreesUsedBy({&logic});
    const TriggerKit trigKit = TriggerKit::create(netlistp, initFuncp, senExprBuilder, {},
                                                  senTreeps, "ico", extraTriggers, false, false);
    std::ignore = senExprBuilder.getAndClearResults();

    if (dpiExportTriggerVscp) {
        trigKit.addExtraTriggerAssignment(dpiExportTriggerVscp, dpiExportTriggerIndex);
    }
    addVirtIfaceTriggerAssignments(virtIfaceTriggers, firstVifTriggerIndex,
                                   firstVifMemberTriggerIndex, trigKit);

    // Remap sensitivities
    remapSensitivities(logic, trigKit.mapVec());

    // Create the inverse map from trigger ref AstSenTree to original AstSenTree
    V3Order::TrigToSenMap trigToSen;
    invertAndMergeSenTreeMap(trigToSen, trigKit.mapVec());

    // The trigger top level inputs (first iteration)
    AstSenTree* const inputChanged
        = trigKit.newExtraTriggerSenTree(trigKit.vscp(), firstIterationTrigger);

    // The DPI Export trigger
    AstSenTree* const dpiExportTriggered
        = dpiExportTriggerVscp
              ? trigKit.newExtraTriggerSenTree(trigKit.vscp(), dpiExportTriggerIndex)
              : nullptr;
    const auto& vifMemberTriggeredIco = virtIfaceTriggers.makeMemberToSensMap(
        trigKit, firstVifMemberTriggerIndex, trigKit.vscp());

    // Create and Order the body function
    AstCFunc* const icoFuncp = V3Order::order(
        netlistp, {&logic}, trigToSen, "ico", false, false,
        [=](const AstVarScope* vscp, std::vector<AstSenTree*>& out) {
            AstVar* const varp = vscp->varp();
            if (varp->isPrimaryInish() || varp->isSigUserRWPublic()) {
                out.push_back(inputChanged);
            }
            if (varp->isWrittenByDpi()) out.push_back(dpiExportTriggered);
            if (vscp->varp()->isVirtIface()) {
                std::vector<AstSenTree*> ifaceTriggered
                    = findTriggeredIface(vscp, vifMemberTriggeredIco);
                out.insert(out.end(), ifaceTriggered.begin(), ifaceTriggered.end());
            }
        });
    util::splitCheck(icoFuncp);

    // Create the eval loop
    const EvalLoop icoLoop = createEvalLoop(  //
        netlistp, "ico", "Input combinational", /* slow: */ false, trigKit,
        // Use trigger
        trigKit.vscp(), nullptr,
        // Inner loop statements
        nullptr,
        // Prep statements: Compute the current 'ico' triggers
        [&trigKit] {
            AstNodeStmt* const stmtp = trigKit.newCompBaseCall();
            if (stmtp) stmtp->addNext(trigKit.newDumpCall(trigKit.vscp(), trigKit.name(), true));
            return stmtp;
        }(),
        // Work statements: Invoke the 'ico' function
        util::callVoidFunc(icoFuncp));

    // Add the first iteration trigger to the trigger computation function
    trigKit.addExtraTriggerAssignment(icoLoop.firstIterp, firstIterationTrigger, false);

    return icoLoop.stmtsp;
}

//============================================================================
// EvalKit groups items that have to be passed to createEval() for a given eval region

struct EvalKit final {
    // The AstVarScope representing the region's trigger vector
    AstVarScope* const m_vscp = nullptr;
    // The AstCFunc that evaluates the region's logic
    AstCFunc* const m_funcp = nullptr;
    // Is this kit used/required?
    bool empty() const { return !m_funcp; }
};

//============================================================================
// Bolt together parts to create the top level _eval function

void createEval(AstNetlist* netlistp,  //
                AstNode* icoLoop,  //
                const TriggerKit& trigKit,  //
                const EvalKit& actKit,  //
                const EvalKit& nbaKit,  //
                const EvalKit& obsKit,  //
                const EvalKit& reactKit,  //
                AstCFunc* postponedFuncp,  //
                TimingKit& timingKit  //
) {
    FileLine* const flp = netlistp->fileline();

    // Grab the delay scheduler variable, if any
    AstVarScope* const delaySchedVscp = timingKit.getDelayScheduler(netlistp);

    // 'createResume' consumes the contents that 'createReady' needs, so do the right order
    AstCCall* const timingReadyp = timingKit.createReady(netlistp);
    AstCCall* const timingResumep = timingKit.createResume(netlistp);

    // Create the active eval loop
    EvalLoop topLoop = createEvalLoop(  //
        netlistp, "act", "Active", /* slow: */ false, trigKit,
        // Use trigger
        actKit.m_vscp, nullptr,
        // Inner loop statements
        nullptr,
        // Prep statements
        [&]() {
            // Compute the current 'act' triggers - the NBA triggers are the latched value
            AstNodeStmt* stmtsp = trigKit.newCompBaseCall();
            AstNodeStmt* const dumpp
                = stmtsp ? trigKit.newDumpCall(trigKit.vscp(), trigKit.name(), true) : nullptr;
            // Mark as ready for triggered awaits
            if (timingReadyp) stmtsp = AstNode::addNext(stmtsp, timingReadyp->makeStmt());
            if (AstVarScope* const vscAccp = trigKit.vscAccp()) {
                stmtsp = AstNode::addNext(stmtsp, trigKit.newOrIntoCall(actKit.m_vscp, vscAccp));
            }
            stmtsp = AstNode::addNext(stmtsp, trigKit.newCompExtCall(nbaKit.m_vscp));
            stmtsp = AstNode::addNext(stmtsp, dumpp);
            // Latch the 'act' triggers under the 'nba' triggers
            stmtsp = AstNode::addNext(stmtsp, trigKit.newOrIntoCall(nbaKit.m_vscp, actKit.m_vscp));
            //
            return stmtsp;
        }(),
        // Work statements
        [&]() {
            AstNodeStmt* workp = nullptr;
            if (AstVarScope* const actAccp = trigKit.vscAccp()) {
                AstCMethodHard* const cCallp = new AstCMethodHard{
                    flp, new AstVarRef{flp, actAccp, VAccess::WRITE}, VCMethod::UNPACKED_FILL,
                    new AstConst{flp, AstConst::Unsized64{}, 0}};
                cCallp->dtypeSetVoid();
                workp = AstNode::addNext(workp, cCallp->makeStmt());
            }
            // Resume triggered timing schedulers
            if (timingResumep) workp = AstNode::addNext(workp, timingResumep->makeStmt());
            // Invoke the 'act' function
            workp = AstNode::addNext(workp, util::callVoidFunc(actKit.m_funcp));
            //
            return workp;
        }());

    // Create if there are any delays, so we can check at runtime if a #0 is unexpected
    if (delaySchedVscp) {
        topLoop = createEvalLoop(  //
            netlistp, "inact", "Inactive", /* slow: */ false, trigKit,
            // Use explicit condition
            nullptr,
            [&]() {
                // Run if any zero delays are pending
                AstNodeExpr* const callp
                    = new AstCMethodHard{flp, new AstVarRef{flp, delaySchedVscp, VAccess::READ},
                                         VCMethod::SCHED_AWAITING_ZERO_DELAY};
                callp->dtypeSetBit();
                return callp;
            }(),
            // Inner loop statements
            topLoop.stmtsp,
            // Prep statements
            nullptr,
            // Work statements
            [&]() -> AstNodeStmt* {
                if (v3Global.usesZeroDelay()) {
                    // Resume processes watiting for #0 delay
                    AstCMethodHard* const callp = new AstCMethodHard{
                        flp, new AstVarRef{flp, delaySchedVscp, VAccess::READWRITE},
                        VCMethod::SCHED_RESUME_ZERO_DELAY};
                    callp->dtypeSetVoid();
                    return callp->makeStmt();
                } else {
                    // Assumption was that the design doesn't use #0 delays.
                    // Die at run-time if it does.
                    AstCStmt* const stmtp = new AstCStmt{flp};
                    const FileLine* const locp = netlistp->topModulep()->fileline();
                    const std::string& file = VIdProtect::protect(locp->filename());
                    const std::string& line = std::to_string(locp->lineno());
                    stmtp->add(
                        "VL_FATAL_MT(\"" + V3OutFormatter::quoteNameControls(file) + "\", " + line
                        + ", \"\", \"ZERODLY: Design Verilated with '--no-sched-zero-delay', "
                        + "but #0 delay executed at runtime\");");
                    return stmtp;
                }
            }());
    }

    // Create the NBA eval loop, which is the default top level loop.
    topLoop = createEvalLoop(  //
        netlistp, "nba", "NBA", /* slow: */ false, trigKit,
        // Use trigger
        nbaKit.m_vscp, nullptr,
        // Inner loop statements
        topLoop.stmtsp,
        // Prep statements
        nullptr,
        // Work statements
        [&]() {
            AstNodeStmt* workp = nullptr;
            // Latch the 'nba' trigger flags under the following region's trigger flags
            if (!obsKit.empty()) {
                workp = trigKit.newOrIntoCall(obsKit.m_vscp, nbaKit.m_vscp);
            } else if (!reactKit.empty()) {
                workp = trigKit.newOrIntoCall(reactKit.m_vscp, nbaKit.m_vscp);
            }
            // Invoke the 'nba' function
            workp = AstNode::addNext(workp, util::callVoidFunc(nbaKit.m_funcp));
            // Clear the 'nba' triggers
            workp = AstNode::addNext(workp, trigKit.newClearCall(nbaKit.m_vscp));
            //
            return workp;
        }(),
        // Extra work (not conditional on having had a fired trigger)
        [&](AstVarScope* continuep) -> AstNodeStmt* {
            // Check if any dynamic NBAs are pending, if there are any in the design
            if (!netlistp->nbaEventp()) return nullptr;
            AstVarScope* const nbaEventp = netlistp->nbaEventp();
            AstVarScope* const nbaEventTriggerp = netlistp->nbaEventTriggerp();
            UASSERT(nbaEventTriggerp, "NBA event trigger var should exist");
            netlistp->nbaEventp(nullptr);
            netlistp->nbaEventTriggerp(nullptr);

            // If a dynamic NBA is pending, clear the pending flag and fire the ready event
            AstIf* const ifp = new AstIf{flp, new AstVarRef{flp, nbaEventTriggerp, VAccess::READ}};
            ifp->addThensp(util::setVar(continuep, 1));
            ifp->addThensp(util::setVar(nbaEventTriggerp, 0));
            AstCMethodHard* const firep = new AstCMethodHard{
                flp, new AstVarRef{flp, nbaEventp, VAccess::WRITE}, VCMethod::EVENT_FIRE};
            firep->dtypeSetVoid();
            ifp->addThensp(firep->makeStmt());
            return ifp;
        });

    if (!obsKit.empty()) {
        // Create the Observed eval loop, which becomes the top level loop.
        topLoop = createEvalLoop(  //
            netlistp, "obs", "Observed", /* slow: */ false, trigKit,
            // Use trigger
            obsKit.m_vscp, nullptr,
            // Inner loop statements
            topLoop.stmtsp,
            // Prep statements
            nullptr,
            // Work statements
            [&]() {
                AstNodeStmt* workp = nullptr;
                // Latch the Observed trigger flags under the Reactive trigger flags
                if (!reactKit.empty()) {
                    workp = trigKit.newOrIntoCall(reactKit.m_vscp, obsKit.m_vscp);
                }
                // Invoke the 'obs' function
                workp = AstNode::addNext(workp, util::callVoidFunc(obsKit.m_funcp));
                // Clear the 'obs' triggers
                workp = AstNode::addNext(workp, trigKit.newClearCall(obsKit.m_vscp));
                //
                return workp;
            }());
    }

    if (!reactKit.empty()) {
        // Create the Reactive eval loop, which becomes the top level loop.
        topLoop = createEvalLoop(  //
            netlistp, "react", "Reactive", /* slow: */ false, trigKit,
            // Use trigger
            reactKit.m_vscp, nullptr,
            // Inner loop statements
            topLoop.stmtsp,
            // Prep statements
            nullptr,
            // Work statements
            [&]() {
                // Invoke the 'react' function
                AstNodeStmt* workp = util::callVoidFunc(reactKit.m_funcp);
                // Clear the 'react' triggers
                workp = AstNode::addNext(workp, trigKit.newClearCall(reactKit.m_vscp));
                return workp;
            }());
    }

    // Now that we have build the loops, create the main 'eval' function
    AstCFunc* const funcp = util::makeTopFunction(netlistp, "_eval", false);
    netlistp->evalp(funcp);

    if (v3Global.opt.profExec()) funcp->addStmtsp(AstCStmt::profExecSectionPush(flp, "eval"));

    // Start with the ico loop, if any
    if (icoLoop) funcp->addStmtsp(icoLoop);

    // Execute the top level eval loop
    funcp->addStmtsp(topLoop.stmtsp);

    // Add the Postponed eval call
    if (postponedFuncp) funcp->addStmtsp(util::callVoidFunc(postponedFuncp));

    if (v3Global.opt.profExec()) funcp->addStmtsp(AstCStmt::profExecSectionPop(flp, "eval"));
}

}  // namespace

//============================================================================
// Helper that builds virtual interface trigger sentrees

VirtIfaceTriggers::IfaceMemberSensMap
VirtIfaceTriggers::makeMemberToSensMap(const TriggerKit& trigKit, uint32_t vifTriggerIndex,
                                       AstVarScope* trigVscp) const {
    IfaceMemberSensMap map;
    for (const auto& p : m_memberTriggers) {
        map.emplace(p.first, trigKit.newExtraTriggerSenTree(trigVscp, vifTriggerIndex));
        ++vifTriggerIndex;
    }
    return map;
}

std::unordered_map<const AstSenTree*, AstSenTree*>
cloneMapWithNewTriggerReferences(const std::unordered_map<const AstSenTree*, AstSenTree*>& map,
                                 AstVarScope* vscp) {
    AstTopScope* const topScopep = v3Global.rootp()->topScopep();
    // Label global SenTrees by the order they are in the Ast
    const VNUser1InUse user1InUse;
    int n = 0;
    for (AstNode* nodep = topScopep->senTreesp(); nodep; nodep = nodep->nextp()) nodep->user1(++n);
    // Sort map by key order for determinism
    using Pair = std::pair<const AstSenTree*, AstSenTree*>;
    std::vector<Pair> pairs{map.begin(), map.end()};
    std::sort(pairs.begin(), pairs.end(), [](const Pair& a, const Pair& b) {  //
        return a.first->user1() < b.first->user1();
    });
    // Replace references in each mapped value with a reference to the given vscp
    for (Pair& pair : pairs) {
        pair.second = pair.second->cloneTree(false);
        pair.second->foreach([&](AstVarRef* refp) {
            UASSERT_OBJ(refp->access() == VAccess::READ, refp, "Should be read ref");
            refp->replaceWith(new AstVarRef{refp->fileline(), vscp, VAccess::READ});
            VL_DO_DANGLING(refp->deleteTree(), refp);
        });
        topScopep->addSenTreesp(pair.second);
    }
    // Convert back to map
    return std::unordered_map<const AstSenTree*, AstSenTree*>{pairs.begin(), pairs.end()};
}

//============================================================================
// Top level entry-point to scheduling

void schedule(AstNetlist* netlistp) {
    const auto addSizeStat = [](const string& name, const LogicByScope& lbs) {
        uint64_t size = 0;
        lbs.foreachLogic([&](AstNode* nodep) { size += nodep->nodeCount(); });
        V3Stats::addStat("Scheduling, " + name, size);
    };

    // Step 0. Prepare external domains for timing and virtual interfaces
    // Create extra triggers for virtual interfaces
    const auto& virtIfaceTriggers = makeVirtIfaceTriggers(netlistp);
    // Prepare timing-related logic and external domains
    TimingKit timingKit = prepareTiming(netlistp);

    // Step 1. Gather and classify all logic in the design
    LogicClasses logicClasses = gatherLogicClasses(netlistp);

    if (v3Global.opt.stats()) {
        V3Stats::statsStage("sched-gather");
        addSizeStat("size of class: static", logicClasses.m_static);
        addSizeStat("size of class: initial", logicClasses.m_initial);
        addSizeStat("size of class: final", logicClasses.m_final);
    }

    // Step 2. Schedule static, initial and final logic classes in source order
    AstCFunc* const staticp = createStatic(netlistp, logicClasses);
    if (v3Global.opt.stats()) V3Stats::statsStage("sched-static");

    createInitial(netlistp, logicClasses);
    if (v3Global.opt.stats()) V3Stats::statsStage("sched-initial");

    createFinal(netlistp, logicClasses);
    if (v3Global.opt.stats()) V3Stats::statsStage("sched-final");

    // Step 3: Break combinational cycles by introducing hybrid logic
    // Note: breakCycles also removes corresponding logic from logicClasses.m_comb;
    logicClasses.m_hybrid = breakCycles(netlistp, logicClasses.m_comb);
    if (v3Global.opt.stats()) {
        addSizeStat("size of class: clocked", logicClasses.m_clocked);
        addSizeStat("size of class: combinational", logicClasses.m_comb);
        addSizeStat("size of class: hybrid", logicClasses.m_hybrid);
        V3Stats::statsStage("sched-break-cycles");
    }

    // We pass around a single SenExprBuilder instance, as we only need one set of 'prev' variables
    // for edge/change detection in sensitivity expressions, which this keeps track of.
    AstTopScope* const topScopep = netlistp->topScopep();
    AstScope* const scopeTopp = topScopep->scopep();
    SenExprBuilder senExprBuilder{scopeTopp};

    // Step 4: Create 'settle' region that restores the combinational invariant
    createSettle(netlistp, staticp, senExprBuilder, logicClasses);
    if (v3Global.opt.stats()) V3Stats::statsStage("sched-settle");

    // Step 5: Partition the clocked and combinational (including hybrid) logic into pre/act/nba.
    // All clocks (signals referenced in an AstSenTree) generated via a blocking assignment
    // (including combinationally generated signals) are computed within the act region.
    LogicRegions logicRegions
        = partition(logicClasses.m_clocked, logicClasses.m_comb, logicClasses.m_hybrid);
    logicRegions.m_obs = logicClasses.m_observed;
    logicRegions.m_react = logicClasses.m_reactive;
    if (v3Global.opt.stats()) {
        addSizeStat("size of region: Active Pre", logicRegions.m_pre);
        addSizeStat("size of region: Active", logicRegions.m_act);
        addSizeStat("size of region: NBA", logicRegions.m_nba);
        addSizeStat("size of region: Observed", logicRegions.m_obs);
        addSizeStat("size of region: Reactive", logicRegions.m_react);
        V3Stats::statsStage("sched-partition");
    }

    // Step 6: Replicate combinational logic
    LogicReplicas logicReplicas = replicateLogic(logicRegions);
    if (v3Global.opt.stats()) {
        addSizeStat("size of replicated logic: Input", logicReplicas.m_ico);
        addSizeStat("size of replicated logic: Active", logicReplicas.m_act);
        addSizeStat("size of replicated logic: NBA", logicReplicas.m_nba);
        addSizeStat("size of replicated logic: Observed", logicReplicas.m_obs);
        addSizeStat("size of replicated logic: Reactive", logicReplicas.m_react);
        V3Stats::statsStage("sched-replicate");
    }

    // Step 7: Create input combinational logic loop
    AstNode* const icoLoopp = createInputCombLoop(netlistp, staticp, senExprBuilder,
                                                  logicReplicas.m_ico, virtIfaceTriggers);
    if (v3Global.opt.stats()) V3Stats::statsStage("sched-create-ico");

    // Step 8: Create the triggers
    AstVarScope* const dpiExportTriggerVscp = netlistp->dpiExportTriggerp();
    netlistp->dpiExportTriggerp(nullptr);  // Finished with this here

    // We may have an extra trigger for variable updated in DPI exports
    TriggerKit::ExtraTriggers extraTriggers;
    const uint32_t dpiExportTriggerIndex = dpiExportTriggerVscp
                                               ? extraTriggers.allocate("DPI export trigger")
                                               : std::numeric_limits<uint32_t>::max();
    const uint32_t firstVifTriggerIndex = extraTriggers.size();
    const uint32_t firstVifMemberTriggerIndex = extraTriggers.size();
    for (const auto& p : virtIfaceTriggers.m_memberTriggers) {
        const auto& item = p.first;
        extraTriggers.allocate("virtual interface member: " + item.m_ifacep->name() + "."
                               + item.m_memberp->name());
    }

    const auto& preTreeps = getSenTreesUsedBy({&logicRegions.m_pre});
    const auto& senTreeps = getSenTreesUsedBy({&logicRegions.m_act,  //
                                               &logicRegions.m_nba,  //
                                               &logicRegions.m_obs,  //
                                               &logicRegions.m_react,  //
                                               &timingKit.m_lbs});
    const TriggerKit trigKit
        = TriggerKit::create(netlistp, staticp, senExprBuilder, preTreeps, senTreeps, "act",
                             extraTriggers, false, v3Global.usesTiming());

    // Add post updates from the timing kit
    if (timingKit.m_postUpdates) trigKit.compBasep()->addStmtsp(timingKit.m_postUpdates);

    if (dpiExportTriggerVscp) {
        trigKit.addExtraTriggerAssignment(dpiExportTriggerVscp, dpiExportTriggerIndex);
    }
    addVirtIfaceTriggerAssignments(virtIfaceTriggers, firstVifTriggerIndex,
                                   firstVifMemberTriggerIndex, trigKit);
    if (v3Global.opt.stats()) V3Stats::statsStage("sched-create-triggers");

    // Note: Experiments so far show that running the Act (or Ico) regions on
    // multiple threads is always a net loss, so only use multi-threading for
    // NBA for now. This can be revised if evidence is available that it would
    // be beneficial

    // Step 9: Create the 'act' region evaluation function

    // Remap sensitivities of the input logic to the triggers
    remapSensitivities(logicRegions.m_pre, trigKit.mapPre());
    remapSensitivities(logicRegions.m_act, trigKit.mapVec());
    remapSensitivities(logicReplicas.m_act, trigKit.mapVec());
    remapSensitivities(timingKit.m_lbs, trigKit.mapVec());
    const std::map<const AstVarScope*, std::vector<AstSenTree*>> actTimingDomains
        = timingKit.remapDomains(trigKit.mapVec());

    // Create the inverse map from trigger ref AstSenTree to original AstSenTree
    V3Order::TrigToSenMap trigToSenAct;
    invertAndMergeSenTreeMap(trigToSenAct, trigKit.mapPre());
    invertAndMergeSenTreeMap(trigToSenAct, trigKit.mapVec());

    // The DPI Export trigger AstSenTree
    AstSenTree* const dpiExportTriggeredAct
        = dpiExportTriggerVscp
              ? trigKit.newExtraTriggerSenTree(trigKit.vscp(), dpiExportTriggerIndex)
              : nullptr;

    const auto& vifMemberTriggeredAct = virtIfaceTriggers.makeMemberToSensMap(
        trigKit, firstVifMemberTriggerIndex, trigKit.vscp());

    AstCFunc* const actFuncp = V3Order::order(
        netlistp, {&logicRegions.m_pre, &logicRegions.m_act, &logicReplicas.m_act}, trigToSenAct,
        "act", false, false, [&](const AstVarScope* vscp, std::vector<AstSenTree*>& out) {
            auto it = actTimingDomains.find(vscp);
            if (it != actTimingDomains.end()) out = it->second;
            if (vscp->varp()->isWrittenByDpi()) out.push_back(dpiExportTriggeredAct);
            if (vscp->varp()->isVirtIface()) {
                std::vector<AstSenTree*> ifaceTriggered
                    = findTriggeredIface(vscp, vifMemberTriggeredAct);
                out.insert(out.end(), ifaceTriggered.begin(), ifaceTriggered.end());
            }
        });
    util::splitCheck(actFuncp);
    if (v3Global.opt.stats()) V3Stats::statsStage("sched-create-act");

    const EvalKit actKit{trigKit.vscp(), actFuncp};

    // Orders a region's logic and creates the region eval function
    const auto order = [&](const std::string& name,
                           const std::vector<V3Sched::LogicByScope*>& logic) -> EvalKit {
        UINFO(2, "Scheduling " << name << " #logic = " << logic.size());
        AstVarScope* const trigVscp = trigKit.newTrigVec(name);
        const auto trigMap = cloneMapWithNewTriggerReferences(trigKit.mapVec(), trigVscp);
        // Remap sensitivities of the input logic to the triggers
        for (LogicByScope* lbs : logic) remapSensitivities(*lbs, trigMap);

        // Create the inverse map from trigger ref AstSenTree to original AstSenTree
        V3Order::TrigToSenMap trigToSen;
        invertAndMergeSenTreeMap(trigToSen, trigMap);

        AstSenTree* const dpiExportTriggered
            = dpiExportTriggerVscp
                  ? trigKit.newExtraTriggerSenTree(trigVscp, dpiExportTriggerIndex)
                  : nullptr;
        const auto& vifMemberTriggered
            = virtIfaceTriggers.makeMemberToSensMap(trigKit, firstVifMemberTriggerIndex, trigVscp);

        const auto& timingDomains = timingKit.remapDomains(trigMap);
        AstCFunc* const funcp = V3Order::order(
            netlistp, logic, trigToSen, name, name == "nba" && v3Global.opt.mtasks(), false,
            [&](const AstVarScope* vscp, std::vector<AstSenTree*>& out) {
                auto it = timingDomains.find(vscp);
                if (it != timingDomains.end()) out = it->second;
                if (vscp->varp()->isWrittenByDpi()) out.push_back(dpiExportTriggered);
                // Sometimes virtual interfaces mix with non-virtual one so, here both have to be
                // detected - look `t_virtual_interface_nba_assign`
                if (vscp->varp()->sensIfacep() || vscp->varp()->isVirtIface()) {
                    std::vector<AstSenTree*> ifaceTriggered
                        = findTriggeredIface(vscp, vifMemberTriggered);
                    out.insert(out.end(), ifaceTriggered.begin(), ifaceTriggered.end());
                }
            });

        return {trigVscp, funcp};
    };

    // Step 10: Create the 'nba' region evaluation function
    const EvalKit nbaKit = order("nba", {&logicRegions.m_nba, &logicReplicas.m_nba});
    util::splitCheck(nbaKit.m_funcp);
    netlistp->evalNbap(nbaKit.m_funcp);  // Remember for V3LifePost
    if (v3Global.opt.stats()) V3Stats::statsStage("sched-create-nba");

    // Orders a region's logic and creates the region eval function (only if there is any logic in
    // the region)
    const auto orderIfNonEmpty
        = [&](const std::string& name, const std::vector<LogicByScope*>& logic) -> EvalKit {
        if (logic[0]->empty())
            return {};  // if region is empty, replica is supposed to be empty as well
        const auto& kit = order(name, logic);
        if (v3Global.opt.stats()) V3Stats::statsStage("sched-create-" + name);
        return kit;
    };

    // Step 11: Create the 'obs' region evaluation function
    const EvalKit obsKit = orderIfNonEmpty("obs", {&logicRegions.m_obs, &logicReplicas.m_obs});

    // Step 12: Create the 're' region evaluation function
    const EvalKit reactKit
        = orderIfNonEmpty("react", {&logicRegions.m_react, &logicReplicas.m_react});

    // Step 13: Create the 'postponed' region evaluation function
    auto* const postponedFuncp = createPostponed(netlistp, logicClasses);

    // Step 14: Bolt it all together to create the '_eval' function
    createEval(netlistp, icoLoopp, trigKit, actKit, nbaKit, obsKit, reactKit, postponedFuncp,
               timingKit);

    // Step 15: Add neccessary evaluation before awaits
    if (AstCCall* const readyp = timingKit.createReady(netlistp)) {
        staticp->addStmtsp(readyp->makeStmt());
        beforeTrigVisitor(netlistp, senExprBuilder, trigKit);
    } else {
        // beforeTrigVisitor clears Sentree pointers in AstCAwaits (as these sentrees will get
        // deleted later) if there was no need to call it, SenTrees have to be cleaned manually
        netlistp->foreach([](AstCAwait* const cAwaitp) { cAwaitp->clearSentreep(); });
    }
    if (AstVarScope* const trigAccp = trigKit.vscAccp()) {
        // Copy trigger vector to accumulator at the end of static initialziation so,
        // triggers fired during initialization persist to the first resume.
        const AstUnpackArrayDType* const trigAccDTypep
            = VN_AS(trigAccp->dtypep(), UnpackArrayDType);
        UASSERT_OBJ(
            trigAccDTypep->right() == 0, trigAccp,
            "Expected that trigger vector and accumulator start elements enumeration from 0");
        UASSERT_OBJ(trigAccDTypep->left() >= 0, trigAccp,
                    "Expected that trigger vector and accumulator has no negative indexes");
        FileLine* const flp = trigAccp->fileline();
        AstVarScope* const vscp = netlistp->topScopep()->scopep()->createTemp("__Vi", 32);
        AstLoop* const loopp = new AstLoop{flp};
        loopp->addStmtsp(
            new AstAssign{flp,
                          new AstArraySel{flp, new AstVarRef{flp, trigAccp, VAccess::WRITE},
                                          new AstVarRef{flp, vscp, VAccess::READ}},
                          new AstArraySel{flp, new AstVarRef{flp, actKit.m_vscp, VAccess::READ},
                                          new AstVarRef{flp, vscp, VAccess::READ}}});
        loopp->addStmtsp(util::incrementVar(vscp));
        loopp->addStmtsp(new AstLoopTest{
            flp, loopp,
            new AstLte{flp, new AstVarRef{flp, vscp, VAccess::READ},
                       new AstConst{flp, AstConst::WidthedValue{}, 32,
                                    static_cast<uint32_t>(trigAccDTypep->left())}}});
        staticp->addStmtsp(loopp);
    }

    // Step 16: Clean up
    netlistp->clearStlFirstIterationp();

    // Haven't split static initializer yet
    util::splitCheck(staticp);

    // Dump
    V3Global::dumpCheckGlobalTree("sched", 0, dumpTreeEitherLevel() >= 3);
}

}  // namespace V3Sched
