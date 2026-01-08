// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Utility functions used by code scheduling
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
    if (!funcp) return nullptr;
    AstCCall* const callp = new AstCCall{funcp->fileline(), funcp};
    callp->dtypeSetVoid();
    return callp->makeStmt();
}

AstNodeStmt* checkIterationLimit(AstNetlist* netlistp, const string& name, AstVarScope* counterp,
                                 AstNodeStmt* dumpCallp) {
    FileLine* const flp = netlistp->fileline();

    // If we exceeded the iteration limit, die
    const uint32_t limit = v3Global.opt.convergeLimit();
    AstVarRef* const counterRefp = new AstVarRef{flp, counterp, VAccess::READ};
    AstConst* const constp = new AstConst{flp, AstConst::DTyped{}, counterp->dtypep()};
    constp->num().setLong(limit);
    AstNodeExpr* const condp = new AstGt{flp, counterRefp, constp};
    AstIf* const ifp = new AstIf{flp, condp};
    ifp->branchPred(VBranchPred::BP_UNLIKELY);
    ifp->addThensp(dumpCallp);
    AstCStmt* const stmtp = new AstCStmt{flp};
    ifp->addThensp(stmtp);
    const FileLine* const locp = netlistp->topModulep()->fileline();
    const std::string& file = VIdProtect::protect(locp->filename());
    const std::string& line = std::to_string(locp->lineno());
    stmtp->add("VL_FATAL_MT(\"" + V3OutFormatter::quoteNameControls(file) + "\", " + line
               + ", \"\", \"DIDNOTCONVERGE: " + name + " region did not converge after "
               + std::to_string(limit) + " tries\");");
    return ifp;
}

static AstCFunc* splitCheckCreateNewSubFunc(AstCFunc* ofuncp) {
    static std::map<AstCFunc*, uint32_t> s_funcNums;  // What split number to attach to a function
    const uint32_t funcNum = s_funcNums[ofuncp]++;
    const std::string name = ofuncp->name() + "__" + cvtToStr(funcNum);
    AstScope* const scopep = ofuncp->scopep();
    AstCFunc* const subFuncp = new AstCFunc{ofuncp->fileline(), name, scopep};
    scopep->addBlocksp(subFuncp);
    subFuncp->dontCombine(true);
    subFuncp->isStatic(ofuncp->isStatic());
    subFuncp->isLoose(true);
    subFuncp->slow(ofuncp->slow());
    subFuncp->declPrivate(ofuncp->declPrivate());
    if (ofuncp->needProcess()) subFuncp->setNeedProcess();
    for (AstVar* argp = ofuncp->argsp(); argp; argp = VN_AS(argp->nextp(), Var)) {
        AstVar* const clonep = argp->cloneTree(false);
        subFuncp->addArgsp(clonep);
        AstVarScope* const vscp = new AstVarScope{clonep->fileline(), scopep, clonep};
        scopep->addVarsp(vscp);
        argp->user3p(vscp);
    }
    return subFuncp;
};

void splitCheckFinishSubFunc(AstCFunc* ofuncp, AstCFunc* subFuncp,
                             const std::unordered_map<const AstVar*, AstVarScope*>& argVscps) {
    FileLine* const flp = subFuncp->fileline();
    AstCCall* const callp = new AstCCall{subFuncp->fileline(), subFuncp};
    callp->dtypeSetVoid();
    // Pass arguments through to subfunction
    for (AstVar* argp = ofuncp->argsp(); argp; argp = VN_AS(argp->nextp(), Var)) {
        UASSERT_OBJ(argp->direction() == VDirection::CONSTREF, argp, "Unexpected direction");
        callp->addArgsp(new AstVarRef{flp, argVscps.at(argp), VAccess::READ});
    }

    bool containsAwait = false;
    subFuncp->foreach([&](AstNodeExpr* exprp) {
        // Record if it has a CAwait
        if (VN_IS(exprp, CAwait)) containsAwait = true;
        // Redirect references to arguments to the clone in the sub-function
        if (AstVarRef* const refp = VN_CAST(exprp, VarRef)) {
            if (AstVarScope* const vscp = VN_AS(refp->varp()->user3p(), VarScope)) {
                refp->varp(vscp->varp());
                refp->varScopep(vscp);
            }
        }
    });

    if (ofuncp->isCoroutine() && containsAwait) {  // Wrap call with co_await
        subFuncp->rtnType("VlCoroutine");
        AstCAwait* const awaitp = new AstCAwait{flp, callp};
        awaitp->dtypeSetVoid();
        ofuncp->addStmtsp(awaitp->makeStmt());
    } else {
        ofuncp->addStmtsp(callp->makeStmt());
    }
}

// Split large function according to --output-split-cfuncs
void splitCheck(AstCFunc* const ofuncp) {
    if (!ofuncp) return;
    UASSERT_OBJ(!ofuncp->varsp(), ofuncp, "Can't split function with local variables");
    if (!v3Global.opt.outputSplitCFuncs() || !ofuncp->stmtsp()) return;
    if (ofuncp->nodeCount() < v3Global.opt.outputSplitCFuncs()) return;

    // Need to find the AstVarScopes for the function arguments. They should be in the same Scope.
    std::unordered_map<const AstVar*, AstVarScope*> argVscps;
    for (AstVar* argp = ofuncp->argsp(); argp; argp = VN_AS(argp->nextp(), Var)) {
        UASSERT_OBJ(argVscps.size() < 2, argp, "There should be at most 2 arguments, or O(n^2)");
        bool found = false;
        for (AstVarScope *vscp = ofuncp->scopep()->varsp(), *nextp; vscp; vscp = nextp) {
            nextp = VN_AS(vscp->nextp(), VarScope);
            if (vscp->varp() != argp) continue;
            argVscps[argp] = vscp;
            found = true;
            break;
        }
        UASSERT_OBJ(found, argp, "Can't find VarScope for function argument");
    }

    // AstVar::user3p(): AstVarScope for function argument in clone
    const VNUser3InUse user3InUse;

    size_t size = 0;
    AstCFunc* subFuncp = nullptr;

    // Move statements one by one to the new sub-functions
    AstNode* stmtsp = ofuncp->stmtsp()->unlinkFrBackWithNext();
    while (AstNode* const itemp = stmtsp) {
        stmtsp = stmtsp->nextp();
        if (stmtsp) stmtsp->unlinkFrBackWithNext();
        const size_t itemSize = static_cast<size_t>(itemp->nodeCount());
        size += itemSize;

        if (size > static_cast<size_t>(v3Global.opt.outputSplitCFuncs())) {
            if (subFuncp) splitCheckFinishSubFunc(ofuncp, subFuncp, argVscps);
            subFuncp = nullptr;
            size = itemSize;
        }

        if (!subFuncp) subFuncp = splitCheckCreateNewSubFunc(ofuncp);
        subFuncp->addStmtsp(itemp);
    }
    if (subFuncp) splitCheckFinishSubFunc(ofuncp, subFuncp, argVscps);
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
