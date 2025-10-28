// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Utility functions used by code scheduling
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
//
//
//*************************************************************************

#include "V3PchAstNoMT.h"  // VL_MT_DISABLED_CODE_UNIT

#include "V3Const.h"
#include "V3EmitCBase.h"
#include "V3EmitV.h"
#include "V3Order.h"
#include "V3Sched.h"
#include "V3SenExprBuilder.h"
#include "V3Stats.h"

VL_DEFINE_DEBUG_FUNCTIONS;

namespace V3Sched {
namespace util {

AstCFunc* makeSubFunction(AstNetlist* netlistp, const string& name, bool slow) {
    AstScope* const scopeTopp = netlistp->topScopep()->scopep();
    AstCFunc* const funcp = new AstCFunc{netlistp->fileline(), name, scopeTopp, ""};
    funcp->dontCombine(true);
    funcp->isStatic(false);
    funcp->isLoose(true);
    funcp->slow(slow);
    funcp->isConst(false);
    funcp->declPrivate(true);
    scopeTopp->addBlocksp(funcp);
    return funcp;
}

AstCFunc* makeTopFunction(AstNetlist* netlistp, const string& name, bool slow) {
    AstCFunc* const funcp = makeSubFunction(netlistp, name, slow);
    funcp->entryPoint(true);
    funcp->keepIfEmpty(true);
    return funcp;
}

AstNodeStmt* setVar(AstVarScope* vscp, uint32_t val) {
    FileLine* const flp = vscp->fileline();
    AstVarRef* const refp = new AstVarRef{flp, vscp, VAccess::WRITE};
    AstConst* const valp = new AstConst{flp, AstConst::DTyped{}, vscp->dtypep()};
    valp->num().setLong(val);
    return new AstAssign{flp, refp, valp};
}

AstNodeStmt* incrementVar(AstVarScope* vscp) {
    FileLine* const flp = vscp->fileline();
    AstVarRef* const wrefp = new AstVarRef{flp, vscp, VAccess::WRITE};
    AstVarRef* const rrefp = new AstVarRef{flp, vscp, VAccess::READ};
    AstConst* const onep = new AstConst{flp, AstConst::DTyped{}, vscp->dtypep()};
    onep->num().setLong(1);
    return new AstAssign{flp, wrefp, new AstAdd{flp, rrefp, onep}};
}

AstNodeStmt* callVoidFunc(AstCFunc* funcp) {
    AstCCall* const callp = new AstCCall{funcp->fileline(), funcp};
    callp->dtypeSetVoid();
    return callp->makeStmt();
}

AstNodeStmt* checkIterationLimit(AstNetlist* netlistp, const string& name, AstVarScope* counterp,
                                 AstCFunc* trigDumpp) {
    FileLine* const flp = netlistp->fileline();

    // If we exceeded the iteration limit, die
    const uint32_t limit = v3Global.opt.convergeLimit();
    AstVarRef* const counterRefp = new AstVarRef{flp, counterp, VAccess::READ};
    AstConst* const constp = new AstConst{flp, AstConst::DTyped{}, counterp->dtypep()};
    constp->num().setLong(limit);
    AstNodeExpr* const condp = new AstGt{flp, counterRefp, constp};
    AstIf* const ifp = new AstIf{flp, condp};
    ifp->branchPred(VBranchPred::BP_UNLIKELY);
    AstCStmt* const stmtp = new AstCStmt{flp};
    ifp->addThensp(stmtp);
    FileLine* const locp = netlistp->topModulep()->fileline();
    const std::string& file = VIdProtect::protect(locp->filename());
    const std::string& line = std::to_string(locp->lineno());
    stmtp->add("#ifdef VL_DEBUG\n");
    stmtp->add(callVoidFunc(trigDumpp));
    stmtp->add("#endif\n");
    stmtp->add("VL_FATAL_MT(\"" + V3OutFormatter::quoteNameControls(file) + "\", " + line
               + ", \"\", \"" + name + " region did not converge after " + std::to_string(limit)
               + " tries\");");
    return ifp;
}

AstNodeStmt* profExecSectionPush(FileLine* flp, const string& section) {
    const string name
        = (v3Global.opt.hierChild() ? (v3Global.opt.topModule() + " ") : "") + section;
    return new AstCStmt{flp, "VL_EXEC_TRACE_ADD_RECORD(vlSymsp).sectionPush(\"" + name + "\");"};
}

AstNodeStmt* profExecSectionPop(FileLine* flp) {
    return new AstCStmt{flp, "VL_EXEC_TRACE_ADD_RECORD(vlSymsp).sectionPop();"};
}

static AstCFunc* splitCheckCreateNewSubFunc(AstCFunc* ofuncp) {
    static std::map<AstCFunc*, uint32_t> s_funcNums;  // What split number to attach to a function
    const uint32_t funcNum = s_funcNums[ofuncp]++;
    const std::string name = ofuncp->name() + "__" + cvtToStr(funcNum);
    AstCFunc* const subFuncp = new AstCFunc{ofuncp->fileline(), name, ofuncp->scopep()};
    subFuncp->dontCombine(true);
    subFuncp->isStatic(false);
    subFuncp->isLoose(true);
    subFuncp->slow(ofuncp->slow());
    subFuncp->declPrivate(ofuncp->declPrivate());
    if (ofuncp->needProcess()) subFuncp->setNeedProcess();
    return subFuncp;
};

// Split large function according to --output-split-cfuncs
void splitCheck(AstCFunc* ofuncp) {
    if (!v3Global.opt.outputSplitCFuncs() || !ofuncp->stmtsp()) return;
    if (ofuncp->nodeCount() < v3Global.opt.outputSplitCFuncs()) return;

    int func_stmts = 0;
    const bool is_ofuncp_coroutine = ofuncp->isCoroutine();
    AstCFunc* funcp = nullptr;

    const auto finishSubFuncp = [&](AstCFunc* subFuncp) {
        ofuncp->scopep()->addBlocksp(subFuncp);
        AstCCall* const callp = new AstCCall{subFuncp->fileline(), subFuncp};
        callp->dtypeSetVoid();

        if (is_ofuncp_coroutine && subFuncp->exists([](const AstCAwait*) {
                return true;
            })) {  // Wrap call with co_await
            subFuncp->rtnType("VlCoroutine");

            AstCAwait* const awaitp = new AstCAwait{subFuncp->fileline(), callp};
            awaitp->dtypeSetVoid();
            ofuncp->addStmtsp(awaitp->makeStmt());
        } else {
            ofuncp->addStmtsp(callp->makeStmt());
        }
    };

    funcp = splitCheckCreateNewSubFunc(ofuncp);
    func_stmts = 0;

    // Unlink all statements, then add item by item to new sub-functions
    AstBegin* const tempp = new AstBegin{ofuncp->fileline(), "[EditWrapper]",
                                         ofuncp->stmtsp()->unlinkFrBackWithNext(), false};
    while (tempp->stmtsp()) {
        AstNode* const itemp = tempp->stmtsp()->unlinkFrBack();
        const int stmts = itemp->nodeCount();

        if ((func_stmts + stmts) > v3Global.opt.outputSplitCFuncs()) {
            finishSubFuncp(funcp);
            funcp = splitCheckCreateNewSubFunc(ofuncp);
            func_stmts = 0;
        }

        funcp->addStmtsp(itemp);
        func_stmts += stmts;
    }
    finishSubFuncp(funcp);
    VL_DO_DANGLING(tempp->deleteTree(), tempp);
}

// Build an AstIf conditional on the given SenTree being triggered
AstIf* createIfFromSenTree(AstSenTree* senTreep) {
    senTreep = VN_AS(V3Const::constifyExpensiveEdit(senTreep), SenTree);
    UASSERT_OBJ(senTreep->sensesp(), senTreep, "No sensitivity list during scheduling");
    // Convert the SenTree to a boolean expression that is true when triggered
    AstNodeExpr* senEqnp = nullptr;
    for (AstSenItem *senp = senTreep->sensesp(), *nextp; senp; senp = nextp) {
        nextp = VN_AS(senp->nextp(), SenItem);
        // They should all be ET_TRUE, as set up by V3Sched
        UASSERT_OBJ(senp->edgeType() == VEdgeType::ET_TRUE, senp, "Bad scheduling trigger type");
        AstNodeExpr* const senOnep = senp->sensp()->cloneTree(false);
        senEqnp = senEqnp ? new AstOr{senp->fileline(), senEqnp, senOnep} : senOnep;
    }
    // Create the if statement conditional on the triggers
    return new AstIf{senTreep->fileline(), senEqnp};
}

}  // namespace util
}  // namespace V3Sched
