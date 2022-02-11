// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Scheduling
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

#include "config_build.h"
#include "verilatedos.h"

#include "V3Ast.h"
#include "V3Sched.h"

namespace V3Sched {

LogicByScope LogicByScope::clone() const {
    LogicByScope result;
    for (const auto& pair : *this) {
        std::vector<AstActive*> clones;
        for (AstActive* const activep : pair.second) clones.push_back(activep->cloneTree(false));
        result.emplace_back(pair.first, std::move(clones));
    }
    return result;
}

struct LogicClasses final {
    LogicByScope m_statics;
    LogicByScope m_initial;
    LogicByScope m_final;
    LogicByScope m_comb;
    LogicByScope m_clocked;

    LogicClasses() = default;
    VL_UNCOPYABLE(LogicClasses);
    LogicClasses(LogicClasses&&) = default;
    LogicClasses& operator=(LogicClasses&&) = default;
};

static LogicClasses gatherLogicClasses(AstNetlist* netlistp) {
    LogicClasses result;

    const auto moveIfNotEmpty
        = [](LogicByScope& lbs, AstScope* scopep, std::vector<AstActive*>& vec) {
              if (!vec.empty()) lbs.emplace_back(scopep, std::move(vec));
          };

    netlistp->foreach<AstScope>([&](AstScope* scopep) {
        std::vector<AstActive*> statics;
        std::vector<AstActive*> initial;
        std::vector<AstActive*> final;
        std::vector<AstActive*> comb;
        std::vector<AstActive*> clocked;

        scopep->foreach<AstActive>([&](AstActive* activep) {
            AstSenTree* const senTreep = activep->sensesp();
            if (senTreep->hasStatic()) {
                UASSERT_OBJ(!senTreep->sensesp()->nextp(), activep,
                            "static initializer with additional sensitivities");
                statics.push_back(activep);
            } else if (senTreep->hasInitial()) {
                UASSERT_OBJ(!senTreep->sensesp()->nextp(), activep,
                            "'initial' logic with additional sensitivities");
                initial.push_back(activep);
            } else if (senTreep->hasFinal()) {
                UASSERT_OBJ(!senTreep->sensesp()->nextp(), activep,
                            "'final' logic with additional sensitivities");
                final.push_back(activep);
            } else if (senTreep->hasCombo()) {
                UASSERT_OBJ(!senTreep->sensesp()->nextp(), activep,
                            "combinational logic with additional sensitivities");
                comb.push_back(activep);
            } else {
                UASSERT_OBJ(senTreep->hasClocked(), activep, "What else could it be?");
                clocked.push_back(activep);
            }
        });

        moveIfNotEmpty(result.m_statics, scopep, statics);
        moveIfNotEmpty(result.m_initial, scopep, initial);
        moveIfNotEmpty(result.m_final, scopep, final);
        moveIfNotEmpty(result.m_comb, scopep, comb);
        moveIfNotEmpty(result.m_clocked, scopep, clocked);
    });

    return result;
}

static AstCFunc* makeTopFunction(AstNetlist* netlistp, const string& name, bool slow) {
    AstScope* const scopeTopp = netlistp->topScopep()->scopep();
    AstCFunc* const funcp = new AstCFunc{netlistp->fileline(), name, scopeTopp};
    funcp->dontCombine(true);
    funcp->isStatic(false);
    funcp->isLoose(true);
    funcp->entryPoint(true);
    funcp->slow(slow);
    funcp->isConst(false);
    funcp->declPrivate(true);
    scopeTopp->addActivep(funcp);
    return funcp;
}

static AstEval* makeEval(AstNetlist* netlistp, const string& name, bool slow) {
    AstScope* const scopeTopp = netlistp->topScopep()->scopep();
    AstEval* const evalp = new AstEval{netlistp->fileline(), name, slow};
    scopeTopp->addActivep(evalp);
    return evalp;
}

static void orderSequentially(AstCFunc* funcp, const LogicByScope& logicByScope) {
    for (const auto& pair : logicByScope) {
        AstScope* const scopep = pair.first;
        // Create a sub-function per scope for combining
        const string subName{funcp->name() + "__" + scopep->nameDotless()};
        AstCFunc* const subFuncp = new AstCFunc{scopep->fileline(), subName, scopep};
        subFuncp->isLoose(true);
        subFuncp->isConst(false);
        subFuncp->declPrivate(true);
        subFuncp->slow(funcp->slow());
        scopep->addActivep(subFuncp);
        // Call it from the top function
        funcp->addStmtsp(new AstCCall{scopep->fileline(), subFuncp});
        // Add statements to sub-function
        for (AstActive* activep : pair.second) {
            for (AstNode *logicp = activep->stmtsp(), *nextp; logicp; logicp = nextp) {
                nextp = logicp->nextp();
                if (AstNodeProcedure* const procp = VN_CAST(logicp, NodeProcedure)) {
                    if (AstNode* const bodyp = procp->bodysp()) {
                        bodyp->unlinkFrBackWithNext();
                        subFuncp->addStmtsp(bodyp);
                    }
                } else {
                    logicp->unlinkFrBackWithNext();
                    subFuncp->addStmtsp(logicp);
                }
            }
            activep->unlinkFrBack()->deleteTree();
        }
    }
}

static void createStatic(AstNetlist* netlistp, const LogicClasses& logicClasses) {
    AstCFunc* const funcp = makeTopFunction(netlistp, "_eval_static", /* slow: */ true);
    orderSequentially(funcp, logicClasses.m_statics);
    splitCheck(funcp);
}

static void createInitial(AstNetlist* netlistp, const LogicClasses& logicClasses) {
    AstCFunc* const funcp = makeTopFunction(netlistp, "_eval_initial", /* slow: */ true);
    orderSequentially(funcp, logicClasses.m_initial);
    // Not splitting yet as it is not final
    netlistp->initp(funcp);
}

static void createFinal(AstNetlist* netlistp, const LogicClasses& logicClasses) {
    AstCFunc* const funcp = makeTopFunction(netlistp, "_final", /* slow: */ true);
    orderSequentially(funcp, logicClasses.m_final);
    splitCheck(funcp);
}

static void createSettle(AstNetlist* netlistp, const LogicClasses& logicClasses) {
    AstEval* const evalp = makeEval(netlistp, "_eval_settle", /* slow: */ true);

    // Clone, because ordering is destructive, but we still need them for "_eval"
    LogicByScope comb = logicClasses.m_comb.clone();

    // Order it (slow code, so always single threaded)
    const auto activeps = orderST(netlistp, {&comb}, true);

    // Move the logic under the function being built
    for (AstActive* const activep : activeps) evalp->addBodyp(activep);

    // Dispose of the remnants of the clones
    for (const auto& pair : comb) {
        for (AstActive* const activep : pair.second) activep->deleteTree();
    }
}

static void createEval(AstNetlist* netlistp, const LogicClasses& logicClasses) {
    AstEval* const evalp = makeEval(netlistp, "_eval", /* slow: */ false);

    // Eval is built from both the combinational logic and the clocked logic
    const std::vector<const LogicByScope*> coll{&logicClasses.m_clocked, &logicClasses.m_comb};

    // Order it
    if (v3Global.opt.mtasks()) {
        AstExecGraph* const execGraphp = orderMT(netlistp, coll);
        evalp->addBodyp(execGraphp);
    } else {
        const auto activeps = orderST(netlistp, coll, false);
        for (AstActive* const activep : activeps) evalp->addBodyp(activep);
    }

    // Dispose of the remnants of the input AstActive trees
    for (const LogicByScope* const lbsp : coll) {
        for (const auto& pair : *lbsp) {
            for (AstActive* const activep : pair.second) activep->unlinkFrBack()->deleteTree();
        }
    }

    // Remember it
    netlistp->evalp(evalp);
}

void schedule(AstNetlist* netlistp) {
    const LogicClasses logicClasses = gatherLogicClasses(netlistp);

    createStatic(netlistp, logicClasses);
    createInitial(netlistp, logicClasses);
    createFinal(netlistp, logicClasses);
    V3Global::dumpCheckGlobalTree("sched-simple", 0, v3Global.opt.dumpTreeLevel(__FILE__) >= 3);

    createSettle(netlistp, logicClasses);
    V3Global::dumpCheckGlobalTree("sched-settle", 0, v3Global.opt.dumpTreeLevel(__FILE__) >= 3);

    createEval(netlistp, logicClasses);
    V3Global::dumpCheckGlobalTree("sched-eval", 0, v3Global.opt.dumpTreeLevel(__FILE__) >= 3);
}

void splitCheck(AstCFunc* ofuncp) {
    if (!v3Global.opt.outputSplitCFuncs() || !ofuncp->stmtsp()) return;
    if (ofuncp->nodeCount() < v3Global.opt.outputSplitCFuncs()) return;

    int funcnum = 0;
    int func_stmts = 0;
    AstCFunc* funcp = nullptr;

    // Unlink all statements, then add item by item to new sub-functions
    AstBegin* const tempp = new AstBegin{ofuncp->fileline(), "[EditWrapper]",
                                         ofuncp->stmtsp()->unlinkFrBackWithNext()};
    if (ofuncp->finalsp()) tempp->addStmtsp(ofuncp->finalsp()->unlinkFrBackWithNext());
    while (tempp->stmtsp()) {
        AstNode* const itemp = tempp->stmtsp()->unlinkFrBack();
        const int stmts = itemp->nodeCount();
        if (!funcp || (func_stmts + stmts) > v3Global.opt.outputSplitCFuncs()) {
            // Make a new function
            funcp = new AstCFunc{ofuncp->fileline(), ofuncp->name() + "__" + cvtToStr(funcnum++),
                                 ofuncp->scopep()};
            funcp->dontCombine(true);
            funcp->isStatic(false);
            funcp->isLoose(true);
            funcp->slow(ofuncp->slow());
            ofuncp->scopep()->addActivep(funcp);
            //
            AstCCall* const callp = new AstCCall{funcp->fileline(), funcp};
            ofuncp->addStmtsp(callp);
            func_stmts = 0;
        }
        funcp->addStmtsp(itemp);
        func_stmts += stmts;
    }
    VL_DO_DANGLING(tempp->deleteTree(), tempp);
}

}  // namespace V3Sched
