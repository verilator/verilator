// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Code scheduling
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2025 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
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
#include "V3Order.h"
#include "V3SenExprBuilder.h"
#include "V3Stats.h"

VL_DEFINE_DEBUG_FUNCTIONS;

namespace V3Sched {

namespace {

//============================================================================
// Utility functions

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
findTriggeredIface(const AstVarScope* vscp, const VirtIfaceTriggers::IfaceSensMap& vifTrigged,
                   const VirtIfaceTriggers::IfaceMemberSensMap& vifMemberTriggered) {
    UASSERT_OBJ(vscp->varp()->sensIfacep(), vscp, "Not an virtual interface trigger");
    std::vector<AstSenTree*> result;
    const auto ifaceIt = vifTrigged.find(vscp->varp()->sensIfacep());
    if (ifaceIt != vifTrigged.end()) result.push_back(ifaceIt->second);
    for (const auto& memberIt : vifMemberTriggered) {
        if (vscp->varp()->sensIfacep() == memberIt.first.m_ifacep) {
            result.push_back(memberIt.second);
        }
    }
    if (result.empty()) vscp->v3fatalSrc("Did not find virtual interface trigger");
    return result;
}

//============================================================================
// Eval loop builder

struct EvalLoop final {
    // Flag set to true during the first iteration of the loop
    AstVarScope* firstIterp;
    // The loop itself and statements around it
    AstNodeStmt* stmtsp = nullptr;
};

// Create an eval loop with all the trimmings.
EvalLoop createEvalLoop(
    AstNetlist* netlistp,  //
    const std::string& tag,  // Tag for current phase
    const string& name,  // Name of current phase
    bool slow,  // Should create slow functions
    AstVarScope* trigp,  // The trigger vector
    AstCFunc* dumpFuncp,  // Trigger dump function for debugging only
    AstNodeStmt* innerp,  // The inner loop, if any
    AstNodeStmt* phasePrepp,  // Prep statements run before checking triggers
    AstNodeStmt* phaseWorkp,  // The work to do if anything triggered
    // Extra statements to run after the work, even if no triggers fired. This function is
    // passed a variable, which must be set to true if we must continue and loop again,
    // and must be unmodified otherwise.
    std::function<AstNodeStmt*(AstVarScope*)> phaseExtra = [](AstVarScope*) { return nullptr; }  //
) {
    const std::string varPrefix = "__V" + tag;
    AstScope* const scopeTopp = netlistp->topScopep()->scopep();
    FileLine* const flp = netlistp->fileline();

    // We wrap the prep/cond/work in a function for readability
    AstCFunc* const phaseFuncp = util::makeTopFunction(netlistp, "_eval_phase__" + tag, slow);
    {
        // The execute flag
        AstVarScope* const executeFlagp = scopeTopp->createTemp(varPrefix + "Execute", 1);
        executeFlagp->varp()->noReset(true);

        // Add the preparatory statements
        phaseFuncp->addStmtsp(phasePrepp);

        // Check if any triggers are fired, save the result
        AstCMethodHard* const callp = new AstCMethodHard{
            flp, new AstVarRef{flp, trigp, VAccess::READ}, VCMethod::TRIGGER_ANY};
        callp->dtypeSetBit();
        phaseFuncp->addStmtsp(
            new AstAssign{flp, new AstVarRef{flp, executeFlagp, VAccess::WRITE}, callp});

        // Add the work
        AstIf* const ifp = new AstIf{flp, new AstVarRef{flp, executeFlagp, VAccess::READ}};
        ifp->addThensp(phaseWorkp);
        phaseFuncp->addStmtsp(ifp);

        // Construct the extra statements
        if (AstNodeStmt* const extrap = phaseExtra(executeFlagp)) phaseFuncp->addStmtsp(extrap);

        // The function returns ture iff it did run the work
        phaseFuncp->rtnType("bool");
        phaseFuncp->addStmtsp(
            new AstCReturn{flp, new AstVarRef{flp, executeFlagp, VAccess::READ}});
    }

    // The result statements
    AstNodeStmt* stmtps = nullptr;

    // Prof-exec section push
    if (v3Global.opt.profExec()) stmtps = util::profExecSectionPush(flp, "loop " + tag);

    const auto addVar = [&](const std::string& name, int width, uint32_t initVal) {
        AstVarScope* const vscp = scopeTopp->createTemp("__V" + tag + name, width);
        vscp->varp()->noReset(true);
        stmtps = AstNode::addNext(stmtps, util::setVar(vscp, initVal));
        return vscp;
    };

    // The iteration counter
    AstVarScope* const counterp = addVar("IterCount", 32, 0);
    // The first iteration flag
    AstVarScope* const firstIterFlagp = addVar("FirstIteration", 1, 1);
    // The continuation flag
    AstVarScope* const continueFlagp = addVar("Continue", 1, 1);

    // The loop
    {
        AstNodeExpr* const condp = new AstVarRef{flp, continueFlagp, VAccess::READ};
        AstLoop* const loopp = new AstLoop{flp};
        loopp->addStmtsp(new AstLoopTest{flp, loopp, condp});

        // Check the iteration limit (aborts if exceeded)
        loopp->addStmtsp(util::checkIterationLimit(netlistp, name, counterp, dumpFuncp));
        // Increment the iteration counter
        loopp->addStmtsp(util::incrementVar(counterp));

        // Reset continuation flag
        loopp->addStmtsp(util::setVar(continueFlagp, 0));

        // Execute the inner loop
        loopp->addStmtsp(innerp);

        // Call the phase function to execute the current work. If we did
        // work, then need to loop again, so set the continuation flag
        AstCCall* const callp = new AstCCall{flp, phaseFuncp};
        callp->dtypeSetBit();
        AstIf* const ifp = new AstIf{flp, callp};
        ifp->addThensp(util::setVar(continueFlagp, 1));
        loopp->addStmtsp(ifp);

        // Clear the first iteration flag
        loopp->addStmtsp(util::setVar(firstIterFlagp, 0));

        stmtps->addNext(loopp);
    }

    // Prof-exec section pop
    if (v3Global.opt.profExec()) stmtps->addNext(util::profExecSectionPop(flp));

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
    // Create new subfunc for scope
    const auto createNewSubFuncp = [&](AstScope* const scopep) {
        const string subName{funcp->name() + "__" + scopep->nameDotless()};
        AstCFunc* const subFuncp = new AstCFunc{scopep->fileline(), subName, scopep};
        subFuncp->isLoose(true);
        subFuncp->isConst(false);
        subFuncp->declPrivate(true);
        subFuncp->slow(funcp->slow());
        scopep->addBlocksp(subFuncp);
        // Call it from the top function
        funcp->addStmtsp(util::callVoidFunc(subFuncp));
        return subFuncp;
    };
    const VNUser1InUse user1InUse;  // AstScope -> AstCFunc: the sub-function for the scope
    const VNUser2InUse user2InUse;  // AstScope -> int: sub-function counter used for names
    for (const auto& pair : lbs) {
        AstScope* const scopep = pair.first;
        AstActive* const activep = pair.second;
        // Create a sub-function per scope so we can V3Combine them later
        if (!scopep->user1p()) scopep->user1p(createNewSubFuncp(scopep));
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
                        subFuncp = createNewSubFuncp(scopep);
                        subFuncp->name(subFuncp->name() + "__Vtiming__"
                                       + cvtToStr(scopep->user2Inc()));
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

//============================================================================
// Create simply ordered functions

AstCFunc* createStatic(AstNetlist* netlistp, const LogicClasses& logicClasses) {
    AstCFunc* const funcp = util::makeTopFunction(netlistp, "_eval_static", /* slow: */ true);
    orderSequentially(funcp, logicClasses.m_static);
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
// EvalKit groups items that have to be passed to createEval() for a given eval region

struct EvalKit final {
    // The TRIGGERVEC AstVarScope representing the region's trigger flags
    AstVarScope* const m_vscp = nullptr;
    // The AstCFunc that computes the region's active triggers
    AstCFunc* const m_triggerComputep = nullptr;
    // The AstCFunc that dumps the region's active triggers
    AstCFunc* const m_dumpp = nullptr;
    // The AstCFunc that evaluates the region's logic
    AstCFunc* const m_funcp = nullptr;
    // Is this kit used/required?
    bool empty() const { return !m_funcp; }
};

// Create an AstSenTree that is sensitive to the given trigger index. Must not exist yet!
AstSenTree* createTriggerSenTree(AstNetlist* netlistp, AstVarScope* const vscp, uint32_t index) {
    UASSERT_OBJ(index != std::numeric_limits<unsigned>::max(), netlistp, "Invalid trigger index");
    AstTopScope* const topScopep = netlistp->topScopep();
    FileLine* const flp = topScopep->fileline();
    AstVarRef* const vrefp = new AstVarRef{flp, vscp, VAccess::READ};
    const uint32_t wordIndex = index / 64;
    const uint32_t bitIndex = index % 64;
    AstCMethodHard* const callp
        = new AstCMethodHard{flp, vrefp, VCMethod::TRIGGER_WORD, new AstConst{flp, wordIndex}};
    callp->dtypeSetUInt64();
    AstNodeExpr* const termp
        = new AstAnd{flp, new AstConst{flp, AstConst::Unsized64{}, 1ULL << bitIndex}, callp};
    AstSenItem* const senItemp = new AstSenItem{flp, VEdgeType::ET_TRUE, termp};
    AstSenTree* const resultp = new AstSenTree{flp, senItemp};
    topScopep->addSenTreesp(resultp);
    return resultp;
}

//============================================================================
// Helper that creates virtual interface trigger resets

void addVirtIfaceTriggerAssignments(const VirtIfaceTriggers& virtIfaceTriggers,
                                    size_t vifTriggerIndex, size_t vifMemberTriggerIndex,
                                    const TriggerKit& actTrig) {
    for (const auto& p : virtIfaceTriggers.m_ifaceTriggers) {
        actTrig.addExtraTriggerAssignment(p.second, vifTriggerIndex);
        ++vifTriggerIndex;
    }
    for (const auto& p : virtIfaceTriggers.m_memberTriggers) {
        actTrig.addExtraTriggerAssignment(p.second, vifMemberTriggerIndex);
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
    ExtraTriggers extraTriggers;
    const size_t firstIterationTrigger = extraTriggers.allocate("first iteration");

    // Gather the relevant sensitivity expressions and create the trigger kit
    const auto& senTreeps = getSenTreesUsedBy({&comb, &hybrid});
    const TriggerKit trig = TriggerKit::create(netlistp, initFuncp, senExprBulider, senTreeps,
                                               "stl", extraTriggers, true);

    // Remap sensitivities (comb has none, so only do the hybrid)
    remapSensitivities(hybrid, trig.m_map);

    // Create the inverse map from trigger ref AstSenTree to original AstSenTree
    V3Order::TrigToSenMap trigToSen;
    invertAndMergeSenTreeMap(trigToSen, trig.m_map);

    // First trigger is for pure combinational triggers (first iteration)
    AstSenTree* const inputChanged
        = createTriggerSenTree(netlistp, trig.m_vscp, firstIterationTrigger);

    // Create and the body function
    AstCFunc* const stlFuncp = V3Order::order(
        netlistp, {&comb, &hybrid}, trigToSen, "stl", false, true,
        [=](const AstVarScope*, std::vector<AstSenTree*>& out) { out.push_back(inputChanged); });
    util::splitCheck(stlFuncp);

    // Create the eval loop
    const EvalLoop stlLoop = createEvalLoop(  //
        netlistp, "stl", "Settle", /* slow: */ true, trig.m_vscp, trig.m_dumpp,
        // Inner loop statements
        nullptr,
        // Prep statements: Compute the current 'stl' triggers
        util::callVoidFunc(trig.m_funcp),
        // Work statements: Invoke the 'stl' function
        util::callVoidFunc(stlFuncp));

    // Add the first iteration trigger to the trigger computation function
    trig.addFirstIterationTriggerAssignment(stlLoop.firstIterp, firstIterationTrigger);

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

    ExtraTriggers extraTriggers;
    const size_t firstIterationTrigger = extraTriggers.allocate("first iteration");
    const size_t dpiExportTriggerIndex = dpiExportTriggerVscp
                                             ? extraTriggers.allocate("DPI export trigger")
                                             : std::numeric_limits<unsigned>::max();
    const size_t firstVifTriggerIndex = extraTriggers.size();
    for (const auto& p : virtIfaceTriggers.m_ifaceTriggers) {
        extraTriggers.allocate("virtual interface: " + p.first->name());
    }
    const size_t firstVifMemberTriggerIndex = extraTriggers.size();
    for (const auto& p : virtIfaceTriggers.m_memberTriggers) {
        const auto& item = p.first;
        extraTriggers.allocate("virtual interface member: " + item.m_ifacep->name() + "."
                               + item.m_memberp->name());
    }

    // Gather the relevant sensitivity expressions and create the trigger kit
    const auto& senTreeps = getSenTreesUsedBy({&logic});
    const TriggerKit trig = TriggerKit::create(netlistp, initFuncp, senExprBuilder, senTreeps,
                                               "ico", extraTriggers, false);

    if (dpiExportTriggerVscp) {
        trig.addExtraTriggerAssignment(dpiExportTriggerVscp, dpiExportTriggerIndex);
    }
    addVirtIfaceTriggerAssignments(virtIfaceTriggers, firstVifTriggerIndex,
                                   firstVifMemberTriggerIndex, trig);

    // Remap sensitivities
    remapSensitivities(logic, trig.m_map);

    // Create the inverse map from trigger ref AstSenTree to original AstSenTree
    V3Order::TrigToSenMap trigToSen;
    invertAndMergeSenTreeMap(trigToSen, trig.m_map);

    // The trigger top level inputs (first iteration)
    AstSenTree* const inputChanged
        = createTriggerSenTree(netlistp, trig.m_vscp, firstIterationTrigger);

    // The DPI Export trigger
    AstSenTree* const dpiExportTriggered
        = dpiExportTriggerVscp ? createTriggerSenTree(netlistp, trig.m_vscp, dpiExportTriggerIndex)
                               : nullptr;
    const auto& vifTriggeredIco
        = virtIfaceTriggers.makeIfaceToSensMap(netlistp, firstVifTriggerIndex, trig.m_vscp);
    const auto& vifMemberTriggeredIco
        = virtIfaceTriggers.makeMemberToSensMap(netlistp, firstVifMemberTriggerIndex, trig.m_vscp);

    // Create and Order the body function
    AstCFunc* const icoFuncp = V3Order::order(
        netlistp, {&logic}, trigToSen, "ico", false, false,
        [=](const AstVarScope* vscp, std::vector<AstSenTree*>& out) {
            AstVar* const varp = vscp->varp();
            if (varp->isPrimaryInish() || varp->isSigUserRWPublic()) {
                out.push_back(inputChanged);
            }
            if (varp->isWrittenByDpi()) out.push_back(dpiExportTriggered);
            if (vscp->varp()->sensIfacep()) {
                std::vector<AstSenTree*> ifaceTriggered
                    = findTriggeredIface(vscp, vifTriggeredIco, vifMemberTriggeredIco);
                out.insert(out.end(), ifaceTriggered.begin(), ifaceTriggered.end());
            }
        });
    util::splitCheck(icoFuncp);

    // Create the eval loop
    const EvalLoop icoLoop = createEvalLoop(  //
        netlistp, "ico", "Input combinational", /* slow: */ false, trig.m_vscp, trig.m_dumpp,
        // Inner loop statements
        nullptr,
        // Prep statements: Compute the current 'ico' triggers
        util::callVoidFunc(trig.m_funcp),
        // Work statements: Invoke the 'ico' function
        util::callVoidFunc(icoFuncp));

    // Add the first iteration trigger to the trigger computation function
    trig.addFirstIterationTriggerAssignment(icoLoop.firstIterp, firstIterationTrigger);

    return icoLoop.stmtsp;
}

//============================================================================
// Helpers for 'createEval'

AstStmtExpr* createTriggerClearCall(FileLine* const flp, AstVarScope* const vscp) {  // Trigger
    AstVarRef* const refp = new AstVarRef{flp, vscp, VAccess::WRITE};
    AstCMethodHard* const callp = new AstCMethodHard{flp, refp, VCMethod::TRIGGER_CLEAR};
    callp->dtypeSetVoid();
    return callp->makeStmt();
}

AstStmtExpr* createTriggerSetCall(FileLine* const flp, AstVarScope* const toVscp,
                                  AstVarScope* const fromVscp) {
    AstVarRef* const lhsp = new AstVarRef{flp, toVscp, VAccess::WRITE};
    AstVarRef* const argp = new AstVarRef{flp, fromVscp, VAccess::READ};
    AstCMethodHard* const callp = new AstCMethodHard{flp, lhsp, VCMethod::TRIGGER_THIS_OR, argp};
    callp->dtypeSetVoid();
    return callp->makeStmt();
}

AstStmtExpr* createTriggerAndNotCall(FileLine* const flp, AstVarScope* const lhsVscp,
                                     AstVarScope* const aVscp, AstVarScope* const bVscp) {
    AstVarRef* const lhsp = new AstVarRef{flp, lhsVscp, VAccess::WRITE};
    AstVarRef* const opap = new AstVarRef{flp, aVscp, VAccess::READ};
    AstVarRef* const opbp = new AstVarRef{flp, bVscp, VAccess::READ};
    opap->addNext(opbp);
    AstCMethodHard* const callp = new AstCMethodHard{flp, lhsp, VCMethod::TRIGGER_AND_NOT, opap};
    callp->dtypeSetVoid();
    return callp->makeStmt();
}

//============================================================================
// Bolt together parts to create the top level _eval function

void createEval(AstNetlist* netlistp,  //
                AstNode* icoLoop,  //
                const EvalKit& actKit,  //
                AstVarScope* preTrigsp,  //
                const EvalKit& nbaKit,  //
                const EvalKit& obsKit,  //
                const EvalKit& reactKit,  //
                AstCFunc* postponedFuncp,  //
                TimingKit& timingKit  //
) {
    FileLine* const flp = netlistp->fileline();

    // 'createResume' consumes the contents that 'createCommit' needs, so do the right order
    AstCCall* const timingCommitp = timingKit.createCommit(netlistp);
    AstCCall* const timingResumep = timingKit.createResume(netlistp);

    // Create the active eval loop
    const EvalLoop actLoop = createEvalLoop(  //
        netlistp, "act", "Active", /* slow: */ false, actKit.m_vscp, actKit.m_dumpp,
        // Inner loop statements
        nullptr,
        // Prep statements
        [&]() {
            // Compute the current 'act' triggers
            AstNodeStmt* const stmtsp = util::callVoidFunc(actKit.m_triggerComputep);
            // Commit trigger awaits from the previous iteration
            if (timingCommitp) stmtsp->addNext(timingCommitp->makeStmt());
            //
            return stmtsp;
        }(),
        // Work statements
        [&]() {
            // Compute the 'pre' triggers
            AstNodeStmt* const workp
                = createTriggerAndNotCall(flp, preTrigsp, actKit.m_vscp, nbaKit.m_vscp);
            // Latch the 'act' triggers under the 'nba' triggers
            workp->addNext(createTriggerSetCall(flp, nbaKit.m_vscp, actKit.m_vscp));
            // Resume triggered timing schedulers
            if (timingResumep) workp->addNext(timingResumep->makeStmt());
            // Invoke the 'act' function
            workp->addNext(util::callVoidFunc(actKit.m_funcp));
            //
            return workp;
        }());

    // Create the NBA eval loop, which is the default top level loop.
    EvalLoop topLoop = createEvalLoop(  //
        netlistp, "nba", "NBA", /* slow: */ false, nbaKit.m_vscp, nbaKit.m_dumpp,
        // Inner loop statements
        actLoop.stmtsp,
        // Prep statements
        nullptr,
        // Work statements
        [&]() {
            AstNodeStmt* workp = nullptr;
            // Latch the 'nba' trigger flags under the following region's trigger flags
            if (!obsKit.empty()) {
                workp = createTriggerSetCall(flp, obsKit.m_vscp, nbaKit.m_vscp);
            } else if (!reactKit.empty()) {
                workp = createTriggerSetCall(flp, reactKit.m_vscp, nbaKit.m_vscp);
            }
            // Invoke the 'nba' function
            workp = AstNode::addNext(workp, util::callVoidFunc(nbaKit.m_funcp));
            // Clear the 'nba' triggers
            workp->addNext(createTriggerClearCall(flp, nbaKit.m_vscp));
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

            // If a dynamic NBA is pending, clear the pending flag and fire the commit event
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
            netlistp, "obs", "Observed", /* slow: */ false, obsKit.m_vscp, obsKit.m_dumpp,
            // Inner loop statements
            topLoop.stmtsp,
            // Prep statements
            nullptr,
            // Work statements
            [&]() {
                AstNodeStmt* workp = nullptr;
                // Latch the Observed trigger flags under the Reactive trigger flags
                if (!reactKit.empty()) {
                    workp = createTriggerSetCall(flp, reactKit.m_vscp, obsKit.m_vscp);
                }
                // Invoke the 'obs' function
                workp = AstNode::addNext(workp, util::callVoidFunc(obsKit.m_funcp));
                // Clear the 'obs' triggers
                workp->addNext(createTriggerClearCall(flp, obsKit.m_vscp));
                //
                return workp;
            }());
    }

    if (!reactKit.empty()) {
        // Create the Reactive eval loop, which becomes the top level loop.
        topLoop = createEvalLoop(  //
            netlistp, "react", "Reactive", /* slow: */ false, reactKit.m_vscp, reactKit.m_dumpp,
            // Inner loop statements
            topLoop.stmtsp,
            // Prep statements
            nullptr,
            // Work statements
            [&]() {
                // Invoke the 'react' function
                AstNodeStmt* const workp = util::callVoidFunc(reactKit.m_funcp);
                // Clear the 'react' triggers
                workp->addNext(createTriggerClearCall(flp, reactKit.m_vscp));
                return workp;
            }());
    }

    // Now that we have build the loops, create the main 'eval' function
    AstCFunc* const funcp = util::makeTopFunction(netlistp, "_eval", false);
    netlistp->evalp(funcp);

    if (v3Global.opt.profExec()) funcp->addStmtsp(util::profExecSectionPush(flp, "eval"));

    // Start with the ico loop, if any
    if (icoLoop) funcp->addStmtsp(icoLoop);

    // Execute the top level eval loop
    funcp->addStmtsp(topLoop.stmtsp);

    // Add the Postponed eval call
    if (postponedFuncp) funcp->addStmtsp(util::callVoidFunc(postponedFuncp));

    if (v3Global.opt.profExec()) funcp->addStmtsp(util::profExecSectionPop(flp));
}

}  // namespace

//============================================================================
// Helper that builds virtual interface trigger sentrees

VirtIfaceTriggers::IfaceSensMap
VirtIfaceTriggers::makeIfaceToSensMap(AstNetlist* const netlistp, size_t vifTriggerIndex,
                                      AstVarScope* trigVscp) const {
    std::map<const AstIface*, AstSenTree*> map;
    for (const auto& p : m_ifaceTriggers) {
        map.emplace(p.first, createTriggerSenTree(netlistp, trigVscp, vifTriggerIndex));
        ++vifTriggerIndex;
    }
    return map;
}

VirtIfaceTriggers::IfaceMemberSensMap
VirtIfaceTriggers::makeMemberToSensMap(AstNetlist* const netlistp, size_t vifTriggerIndex,
                                       AstVarScope* trigVscp) const {
    IfaceMemberSensMap map;
    for (const auto& p : m_memberTriggers) {
        map.emplace(p.first, createTriggerSenTree(netlistp, trigVscp, vifTriggerIndex));
        ++vifTriggerIndex;
    }
    return map;
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

    // Step 8: Create the pre/act/nba triggers
    AstVarScope* const dpiExportTriggerVscp = netlistp->dpiExportTriggerp();
    netlistp->dpiExportTriggerp(nullptr);  // Finished with this here

    // We may have an extra trigger for variable updated in DPI exports
    ExtraTriggers extraTriggers;
    const size_t dpiExportTriggerIndex = dpiExportTriggerVscp
                                             ? extraTriggers.allocate("DPI export trigger")
                                             : std::numeric_limits<unsigned>::max();
    const size_t firstVifTriggerIndex = extraTriggers.size();
    for (const auto& p : virtIfaceTriggers.m_ifaceTriggers) {
        extraTriggers.allocate("virtual interface: " + p.first->name());
    }
    const size_t firstVifMemberTriggerIndex = extraTriggers.size();
    for (const auto& p : virtIfaceTriggers.m_memberTriggers) {
        const auto& item = p.first;
        extraTriggers.allocate("virtual interface member: " + item.m_ifacep->name() + "."
                               + item.m_memberp->name());
    }

    const auto& senTreeps = getSenTreesUsedBy({&logicRegions.m_pre,  //
                                               &logicRegions.m_act,  //
                                               &logicRegions.m_nba,  //
                                               &logicRegions.m_obs,  //
                                               &logicRegions.m_react,  //
                                               &timingKit.m_lbs});
    const TriggerKit actTrig = TriggerKit::create(netlistp, staticp, senExprBuilder, senTreeps,
                                                  "act", extraTriggers, false);

    // Add post updates from the timing kit
    if (timingKit.m_postUpdates) actTrig.m_funcp->addStmtsp(timingKit.m_postUpdates);

    if (dpiExportTriggerVscp) {
        actTrig.addExtraTriggerAssignment(dpiExportTriggerVscp, dpiExportTriggerIndex);
    }
    addVirtIfaceTriggerAssignments(virtIfaceTriggers, firstVifTriggerIndex,
                                   firstVifMemberTriggerIndex, actTrig);

    AstVarScope* const actTrigVscp = actTrig.m_vscp;
    AstVarScope* const preTrigVscp = scopeTopp->createTempLike("__VpreTriggered", actTrigVscp);

    const auto cloneMapWithNewTriggerReferences
        = [=](const std::unordered_map<const AstSenTree*, AstSenTree*>& map, AstVarScope* vscp) {
              // Copy map
              auto newMap{map};
              // Replace references in each mapped value with a reference to the given vscp
              for (auto& pair : newMap) {
                  pair.second = pair.second->cloneTree(false);
                  pair.second->foreach([&](AstVarRef* refp) {
                      UASSERT_OBJ(refp->varScopep() == actTrigVscp, refp, "Unexpected reference");
                      UASSERT_OBJ(refp->access() == VAccess::READ, refp, "Should be read ref");
                      refp->replaceWith(new AstVarRef{refp->fileline(), vscp, VAccess::READ});
                      VL_DO_DANGLING(refp->deleteTree(), refp);
                  });
                  topScopep->addSenTreesp(pair.second);
              }
              return newMap;
          };

    const auto& actTrigMap = actTrig.m_map;
    const auto preTrigMap = cloneMapWithNewTriggerReferences(actTrigMap, preTrigVscp);
    if (v3Global.opt.stats()) V3Stats::statsStage("sched-create-triggers");

    // Note: Experiments so far show that running the Act (or Ico) regions on
    // multiple threads is always a net loss, so only use multi-threading for
    // NBA for now. This can be revised if evidence is available that it would
    // be beneficial

    // Step 9: Create the 'act' region evaluation function

    // Remap sensitivities of the input logic to the triggers
    remapSensitivities(logicRegions.m_pre, preTrigMap);
    remapSensitivities(logicRegions.m_act, actTrigMap);
    remapSensitivities(logicReplicas.m_act, actTrigMap);
    remapSensitivities(timingKit.m_lbs, actTrigMap);
    const auto& actTimingDomains = timingKit.remapDomains(actTrigMap);

    // Create the inverse map from trigger ref AstSenTree to original AstSenTree
    V3Order::TrigToSenMap trigToSenAct;
    invertAndMergeSenTreeMap(trigToSenAct, preTrigMap);
    invertAndMergeSenTreeMap(trigToSenAct, actTrigMap);

    // The DPI Export trigger AstSenTree
    AstSenTree* const dpiExportTriggeredAct
        = dpiExportTriggerVscp
              ? createTriggerSenTree(netlistp, actTrig.m_vscp, dpiExportTriggerIndex)
              : nullptr;

    const auto& vifTriggeredAct
        = virtIfaceTriggers.makeIfaceToSensMap(netlistp, firstVifTriggerIndex, actTrig.m_vscp);
    const auto& vifMemberTriggeredAct = virtIfaceTriggers.makeMemberToSensMap(
        netlistp, firstVifMemberTriggerIndex, actTrig.m_vscp);

    AstCFunc* const actFuncp = V3Order::order(
        netlistp, {&logicRegions.m_pre, &logicRegions.m_act, &logicReplicas.m_act}, trigToSenAct,
        "act", false, false, [&](const AstVarScope* vscp, std::vector<AstSenTree*>& out) {
            auto it = actTimingDomains.find(vscp);
            if (it != actTimingDomains.end()) out = it->second;
            if (vscp->varp()->isWrittenByDpi()) out.push_back(dpiExportTriggeredAct);
            if (vscp->varp()->sensIfacep()) {
                std::vector<AstSenTree*> ifaceTriggered
                    = findTriggeredIface(vscp, vifTriggeredAct, vifMemberTriggeredAct);
                out.insert(out.end(), ifaceTriggered.begin(), ifaceTriggered.end());
            }
        });
    util::splitCheck(actFuncp);
    if (v3Global.opt.stats()) V3Stats::statsStage("sched-create-act");

    const EvalKit& actKit = {actTrig.m_vscp, actTrig.m_funcp, actTrig.m_dumpp, actFuncp};

    // Orders a region's logic and creates the region eval function
    const auto order = [&](const std::string& name,
                           const std::vector<V3Sched::LogicByScope*>& logic) -> EvalKit {
        UINFO(2, "Scheduling " << name << " #logic = " << logic.size());
        AstVarScope* const trigVscp
            = scopeTopp->createTempLike("__V" + name + "Triggered", actTrigVscp);
        const auto trigMap = cloneMapWithNewTriggerReferences(actTrigMap, trigVscp);
        // Remap sensitivities of the input logic to the triggers
        for (LogicByScope* lbs : logic) remapSensitivities(*lbs, trigMap);

        // Create the inverse map from trigger ref AstSenTree to original AstSenTree
        V3Order::TrigToSenMap trigToSen;
        invertAndMergeSenTreeMap(trigToSen, trigMap);

        AstSenTree* const dpiExportTriggered
            = dpiExportTriggerVscp
                  ? createTriggerSenTree(netlistp, trigVscp, dpiExportTriggerIndex)
                  : nullptr;
        const auto& vifTriggered
            = virtIfaceTriggers.makeIfaceToSensMap(netlistp, firstVifTriggerIndex, trigVscp);
        const auto& vifMemberTriggered = virtIfaceTriggers.makeMemberToSensMap(
            netlistp, firstVifMemberTriggerIndex, trigVscp);

        const auto& timingDomains = timingKit.remapDomains(trigMap);
        AstCFunc* const funcp = V3Order::order(
            netlistp, logic, trigToSen, name, name == "nba" && v3Global.opt.mtasks(), false,
            [&](const AstVarScope* vscp, std::vector<AstSenTree*>& out) {
                auto it = timingDomains.find(vscp);
                if (it != timingDomains.end()) out = it->second;
                if (vscp->varp()->isWrittenByDpi()) out.push_back(dpiExportTriggered);
                if (vscp->varp()->sensIfacep()) {
                    std::vector<AstSenTree*> ifaceTriggered
                        = findTriggeredIface(vscp, vifTriggered, vifMemberTriggered);
                    out.insert(out.end(), ifaceTriggered.begin(), ifaceTriggered.end());
                }
            });

        // Create the trigger dumping function, which is the same as act trigger
        // dumping function, but referencing this region's trigger vector.
        AstCFunc* const dumpp = actTrig.m_dumpp->cloneTree(false);
        actTrig.m_dumpp->addNextHere(dumpp);
        dumpp->name("_dump_triggers__" + name);
        dumpp->foreach([&](AstVarRef* refp) {
            UASSERT_OBJ(refp->access().isReadOnly(), refp, "Should only read state");
            if (refp->varScopep() == actTrig.m_vscp) {
                refp->replaceWith(new AstVarRef{refp->fileline(), trigVscp, VAccess::READ});
                VL_DO_DANGLING(refp->deleteTree(), refp);
            }
        });
        dumpp->foreach([&](AstText* textp) {  //
            textp->text(VString::replaceWord(textp->text(), "act", name));
        });

        return {trigVscp, nullptr, dumpp, funcp};
    };

    // Step 10: Create the 'nba' region evaluation function
    const EvalKit& nbaKit = order("nba", {&logicRegions.m_nba, &logicReplicas.m_nba});
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
    const EvalKit& obsKit = orderIfNonEmpty("obs", {&logicRegions.m_obs, &logicReplicas.m_obs});

    // Step 12: Create the 're' region evaluation function
    const EvalKit& reactKit
        = orderIfNonEmpty("react", {&logicRegions.m_react, &logicReplicas.m_react});

    // Step 13: Create the 'postponed' region evaluation function
    auto* const postponedFuncp = createPostponed(netlistp, logicClasses);

    // Step 14: Bolt it all together to create the '_eval' function
    createEval(netlistp, icoLoopp, actKit, preTrigVscp, nbaKit, obsKit, reactKit, postponedFuncp,
               timingKit);

    // Haven't split static initializer yet
    util::splitCheck(staticp);

    // Dump
    V3Global::dumpCheckGlobalTree("sched", 0, dumpTreeEitherLevel() >= 3);
}

}  // namespace V3Sched
