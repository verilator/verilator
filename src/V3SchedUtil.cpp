// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Utility functions used by code scheduling
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
//
//
//*************************************************************************

#include "V3PchAstNoMT.h"  // VL_MT_DISABLED_CODE_UNIT

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

AstVarScope* newArgument(AstCFunc* funcp, AstNodeDType* dtypep, const string& name,
                         VDirection direction) {
    FileLine* const flp = funcp->fileline();
    AstScope* const scopep = funcp->scopep();
    AstVar* const varp = new AstVar{flp, VVarType::BLOCKTEMP, name, dtypep};
    varp->funcLocal(true);
    varp->direction(direction);
    funcp->addArgsp(varp);
    AstVarScope* const vscp = new AstVarScope{flp, scopep, varp};
    scopep->addVarsp(vscp);
    return vscp;
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

// Pass the arguments of 'ofuncp' through to the sub-function called by 'callp'
static void splitCheckPassArgs(AstCFunc* ofuncp, AstCCall* callp,
                               const std::unordered_map<const AstVar*, AstVarScope*>& argVscps) {
    for (AstVar* argp = ofuncp->argsp(); argp; argp = VN_AS(argp->nextp(), Var)) {
        UASSERT_OBJ(argp->direction() == VDirection::CONSTREF
                        || argp->direction() == VDirection::REF,
                    argp, "Unexpected direction");
        const VAccess access = argp->isRef() ? VAccess::READWRITE : VAccess::READ;
        callp->addArgsp(new AstVarRef{callp->fileline(), argVscps.at(argp), access});
    }
}

void splitCheckFinishSubFunc(AstCFunc* ofuncp, AstCFunc* subFuncp,
                             const std::unordered_map<const AstVar*, AstVarScope*>& argVscps) {
    FileLine* const flp = subFuncp->fileline();
    AstCCall* const callp = new AstCCall{subFuncp->fileline(), subFuncp};
    callp->dtypeSetVoid();
    splitCheckPassArgs(ofuncp, callp, argVscps);

    bool containsAwait = false;
    subFuncp->foreach([&](AstNode* nodep) {
        // Record if it has a CAwait
        if (VN_IS(nodep, CAwait)) containsAwait = true;
        // Redirect references to arguments to the clone in the sub-function
        if (AstVarRef* const refp = VN_CAST(nodep, VarRef)) {
            if (AstVarScope* const vscp = VN_AS(refp->varp()->user3p(), VarScope)) {
                refp->varp(vscp->varp());
                refp->varScopep(vscp);
            }
        }
    });

    if (ofuncp->isCoroutine() && containsAwait) {  // Wrap call with co_await
        subFuncp->rtnType("VlCoroutine");
        ofuncp->addStmtsp(new AstCAwait{flp, callp});
    } else {
        ofuncp->addStmtsp(callp->makeStmt());
    }
}

// Compute, for each top level statement of 'ofuncp', whether a new sub-function may begin there.
// Sub-functions are emitted as separate C++ functions, so they cannot see each other's automatic
// storage. A function-local AstVar declared among the top level statements must therefore end up
// in the same sub-function as every reference to it, otherwise the emitted C++ refers to an
// undeclared identifier (and the AstVar can be deleted from under the still-live references).
static std::vector<bool> splitCheckBreakable(const AstCFunc* ofuncp) {
    // Gather the top level statements, and where each locally declared variable is declared
    std::vector<const AstNode*> stmtps;
    std::unordered_map<const AstVar*, size_t> declIdx;  // Local var -> index it is declared at
    for (const AstNode* nodep = ofuncp->stmtsp(); nodep; nodep = nodep->nextp()) {
        if (const AstVar* const varp = VN_CAST(nodep, Var)) declIdx.emplace(varp, stmtps.size());
        stmtps.push_back(nodep);
    }

    // Find the last statement referencing each locally declared variable
    std::vector<size_t> lastUse(stmtps.size());
    for (size_t i = 0; i < stmtps.size(); ++i) {
        lastUse[i] = i;  // A declaration is live at least where it is declared
        stmtps[i]->foreach([&](const AstNodeVarRef* refp) {
            const auto it = declIdx.find(refp->varp());  // 'end()' if not one of our locals
            if (it != declIdx.end()) lastUse[it->second] = std::max(lastUse[it->second], i);
        });
    }

    // A break before statement 'i' is allowed only if no local declared before 'i' is still live
    std::vector<bool> breakable(stmtps.size(), true);
    size_t liveEnd = 0;  // Last index any so far declared local is referenced at
    for (size_t i = 0; i < stmtps.size(); ++i) {
        breakable[i] = liveEnd < i;
        if (VN_IS(stmtps[i], Var)) liveEnd = std::max(liveEnd, lastUse[i]);
    }
    return breakable;
}

// Whether statement 'stmtp' can be moved into another function: it is not a declaration, and
// it does not jump out of itself, or test the condition of a loop around it
static bool splitCheckMovable(AstNode* stmtp) {
    if (VN_IS(stmtp, Var)) return false;
    std::unordered_set<const AstNode*> innerps;  // Jump blocks and loops inside 'stmtp'
    stmtp->foreach([&](AstNode* nodep) {
        if (VN_IS(nodep, JumpBlock) || VN_IS(nodep, Loop)) innerps.emplace(nodep);
    });
    return !stmtp->exists([&](AstNode* nodep) {
        if (const AstJumpGo* const gop = VN_CAST(nodep, JumpGo)) {
            return !innerps.count(gop->blockp());
        }
        if (const AstLoopTest* const testp = VN_CAST(nodep, LoopTest)) {
            return !innerps.count(testp->loopp());
        }
        return VN_IS(nodep, CReturn);
    });
}

// Move the statements 'firstp' to 'lastp' of a statement list in 'ofuncp' into a new
// sub-function, and call it in their place. Local variables of 'ofuncp' that the statements
// reference are passed by reference, as they may be live around them. Needs user3 (see
// splitCheck).
static AstCFunc*
splitCheckOutlineStmts(AstCFunc* ofuncp, AstNode* firstp, AstNode* lastp,
                       const std::unordered_map<const AstVar*, AstVarScope*>& argVscps) {
    FileLine* const flp = firstp->fileline();
    VNRelinker relinker;
    firstp->unlinkFrBackWithNext(&relinker);
    AstNode* const restp = lastp->nextp();
    if (restp) restp->unlinkFrBackWithNext();

    AstCFunc* const subFuncp = splitCheckCreateNewSubFunc(ofuncp);
    subFuncp->addStmtsp(firstp);
    AstCCall* const callp = new AstCCall{flp, subFuncp};
    callp->dtypeSetVoid();
    splitCheckPassArgs(ofuncp, callp, argVscps);
    std::unordered_map<const AstVar*, AstVarScope*> localVscps;  // Local -> argument passing it
    bool containsAwait = false;
    subFuncp->foreach([&](AstNode* nodep) {
        if (VN_IS(nodep, CAwait)) containsAwait = true;
        AstVarRef* const refp = VN_CAST(nodep, VarRef);
        if (!refp) return;
        AstVar* const varp = refp->varp();
        // Arguments of 'ofuncp' are passed through, see splitCheckCreateNewSubFunc
        AstVarScope* vscp = VN_AS(varp->user3p(), VarScope);
        if (!vscp && varp->isFuncLocal()) {
            const auto pair = localVscps.emplace(varp, nullptr);
            if (pair.second) {
                pair.first->second
                    = newArgument(subFuncp, varp->dtypep(), varp->name(), VDirection::REF);
                callp->addArgsp(new AstVarRef{flp, refp->varScopep(), VAccess::READWRITE});
            }
            vscp = pair.first->second;
        }
        if (vscp) {
            refp->varp(vscp->varp());
            refp->varScopep(vscp);
        }
    });

    AstNode* stmtp;
    if (containsAwait) {
        subFuncp->rtnType("VlCoroutine");
        stmtp = new AstCAwait{flp, callp};
    } else {
        stmtp = callp->makeStmt();
    }
    if (restp) stmtp->addNext(restp);
    relinker.relink(stmtp);
    V3Stats::addStatSum("Scheduling, outlined coroutine statements", 1);
    return subFuncp;
}

// Outline parts of 'stmtp', a statement of 'ofuncp' of 'size' nodes, into sub-functions until
// it is no larger than --output-split-cfuncs, moving the largest runs of movable statements in
// the statement lists directly under it first, then the inside of statements that could not
// move. Needs user3 (see splitCheck).
static void splitCheckOutline(AstCFunc* ofuncp, AstNode* stmtp, size_t size,
                              const std::unordered_map<const AstVar*, AstVarScope*>& argVscps,
                              std::vector<AstCFunc*>& newFuncpsr) {
    const size_t limit = static_cast<size_t>(v3Global.opt.outputSplitCFuncs());
    std::vector<AstNode*> listps;  // Statement lists directly under 'stmtp'
    if (AstNodeIf* const ifp = VN_CAST(stmtp, NodeIf)) {
        listps = {ifp->thensp(), ifp->elsesp()};
    } else if (AstLoop* const loopp = VN_CAST(stmtp, Loop)) {
        listps = {loopp->stmtsp()};
    } else if (AstNodeBlock* const blockp = VN_CAST(stmtp, NodeBlock)) {
        listps = {blockp->stmtsp()};
    } else if (AstJumpBlock* const jblockp = VN_CAST(stmtp, JumpBlock)) {
        listps = {jblockp->stmtsp()};
    }

    struct Run final {
        AstNode* m_firstp;  // First statement of the run
        AstNode* m_lastp;  // Last statement of the run
        size_t m_size;  // Node count of the statements
    };
    std::vector<Run> runs;
    std::vector<std::pair<AstNode*, size_t>> unmovedps;  // Statements that cannot move, sizes
    for (AstNode* const listp : listps) {
        Run run{nullptr, nullptr, 0};
        for (AstNode* nodep = listp; nodep; nodep = nodep->nextp()) {
            const size_t nodeSize = static_cast<size_t>(nodep->nodeCount());
            if (splitCheckMovable(nodep)) {
                if (!run.m_firstp) run.m_firstp = nodep;
                run.m_lastp = nodep;
                run.m_size += nodeSize;
                continue;
            }
            unmovedps.emplace_back(nodep, nodeSize);
            if (run.m_firstp) runs.push_back(run);
            run = Run{nullptr, nullptr, 0};
        }
        if (run.m_firstp) runs.push_back(run);
    }
    std::stable_sort(runs.begin(), runs.end(),
                     [](const Run& a, const Run& b) { return a.m_size > b.m_size; });
    for (const Run& run : runs) {
        if (size <= limit) break;
        newFuncpsr.push_back(splitCheckOutlineStmts(ofuncp, run.m_firstp, run.m_lastp, argVscps));
        size -= run.m_size;
    }
    for (const auto& pair : unmovedps) {
        if (size <= limit) break;
        if (pair.second <= limit) continue;
        splitCheckOutline(ofuncp, pair.first, pair.second, argVscps, newFuncpsr);
        size -= pair.second - static_cast<size_t>(pair.first->nodeCount());
    }
}

// Split large function according to --output-split-cfuncs, adding to 'newFuncpsr' the
// sub-functions of outlined statements, which may still need splitting
static void splitCheckOne(AstCFunc* const ofuncp, std::vector<AstCFunc*>& newFuncpsr) {
    if (!ofuncp) return;
    UASSERT_OBJ(!ofuncp->varsp(), ofuncp, "Can't split function with local variables");
    if (!v3Global.opt.outputSplitCFuncs() || !ofuncp->stmtsp()) return;
    if (ofuncp->nodeCount() < v3Global.opt.outputSplitCFuncs()) return;

    // Need to find the AstVarScopes for the function arguments. They should be in the same Scope.
    std::unordered_map<const AstVar*, AstVarScope*> argVscps;
    for (AstVar* argp = ofuncp->argsp(); argp; argp = VN_AS(argp->nextp(), Var)) {
        argVscps.emplace(argp, nullptr);
    }
    if (!argVscps.empty()) {
        for (AstVarScope *vscp = ofuncp->scopep()->varsp(), *nextp; vscp; vscp = nextp) {
            nextp = VN_AS(vscp->nextp(), VarScope);
            const auto it = argVscps.find(vscp->varp());
            if (it != argVscps.end()) it->second = vscp;
        }
    }
    for (const auto& pair : argVscps) {
        UASSERT_OBJ(pair.second, pair.first, "Can't find VarScope for function argument");
    }

    // AstVar::user3p(): AstVarScope for function argument in clone
    const VNUser3InUse user3InUse;

    // A statement larger than the limit cannot be split at the top level. A C++ compiler's
    // time and memory grow much faster than the size of a coroutine, so outline parts of
    // such statements into sub-functions, which are split in turn.
    if (ofuncp->isCoroutine()) {
        for (AstNode* nodep = ofuncp->stmtsp(); nodep; nodep = nodep->nextp()) {
            const size_t nodeSize = static_cast<size_t>(nodep->nodeCount());
            if (nodeSize > static_cast<size_t>(v3Global.opt.outputSplitCFuncs())) {
                splitCheckOutline(ofuncp, nodep, nodeSize, argVscps, newFuncpsr);
            }
        }
    }

    // Statement boundaries that would separate a local declaration from a reference to it
    const std::vector<bool> breakable = splitCheckBreakable(ofuncp);

    size_t size = 0;
    AstCFunc* subFuncp = nullptr;

    // Move statements one by one to the new sub-functions
    AstNode* stmtsp = ofuncp->stmtsp()->unlinkFrBackWithNext();
    for (size_t index = 0; AstNode* const itemp = stmtsp; ++index) {
        stmtsp = stmtsp->nextp();
        if (stmtsp) stmtsp->unlinkFrBackWithNext();
        const size_t itemSize = static_cast<size_t>(itemp->nodeCount());
        size += itemSize;

        if (size > static_cast<size_t>(v3Global.opt.outputSplitCFuncs()) && breakable[index]) {
            if (subFuncp) splitCheckFinishSubFunc(ofuncp, subFuncp, argVscps);
            subFuncp = nullptr;
            size = itemSize;
        }

        if (!subFuncp) subFuncp = splitCheckCreateNewSubFunc(ofuncp);
        subFuncp->addStmtsp(itemp);
    }
    if (subFuncp) splitCheckFinishSubFunc(ofuncp, subFuncp, argVscps);
}

// Split large function according to --output-split-cfuncs
void splitCheck(AstCFunc* const ofuncp) {
    std::vector<AstCFunc*> newFuncps;
    splitCheckOne(ofuncp, newFuncps);
    for (AstCFunc* const newFuncp : newFuncps) splitCheck(newFuncp);
}

}  // namespace util

}  // namespace V3Sched
