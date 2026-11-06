// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Outline parts of large coroutines into sub-functions
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
// V3Outline's Transformations:
//
// A timed process or task is emitted as a C++ coroutine, and the time and memory a C++
// compiler needs for a coroutine grow much faster than its size. V3Sched splits a large
// process only between its top level statements, so when most of a coroutine is inside one
// statement, such as the branches of an 'if' that call inlined tasks, the coroutine stays as
// large as the whole process. This pass moves parts of such statements into sub-functions,
// until each is no larger than --output-split-cfuncs.
//
// For each coroutine:
//  1. Analysis: one traversal records the size of each statement in nodes, and whether it can
//     move into another function: it cannot if it jumps out of itself, or tests the condition
//     of a loop around it.
//  2. Decision: for each top level statement larger than the limit, take the statement lists
//     directly under it. Their statements larger than the limit stay in place, and the same
//     is done in each of them first. The consecutive movable statements in between form runs.
//     Starting with the largest run, runs are cut into groups no larger than the limit to
//     move, until the statement is within the limit. Moved statements are within the limit,
//     so groups never nest, and new functions need no further splitting.
//  3. Rewrite: each group moves into a new function, called in its place, with co_await if it
//     suspends. Local variables of the coroutine that the group references are passed by
//     reference. This runs before V3Localize, while most variables are module variables, so
//     only the arguments and locals of tasks that are not inlined need passing.
//
//*************************************************************************

#include "V3PchAstNoMT.h"  // VL_MT_DISABLED_CODE_UNIT

#include "V3Outline.h"

#include "V3AstUserAllocator.h"
#include "V3EmitCBase.h"
#include "V3Sched.h"
#include "V3Stats.h"

#include <algorithm>
#include <limits>
#include <unordered_set>
#include <vector>

VL_DEFINE_DEBUG_FUNCTIONS;

//######################################################################
// Pass to a new function the local variables of the coroutine that its statements reference

class OutlineArgsVisitor final : public VNVisitor {
    // STATE
    AstCFunc* const m_funcp;  // New function
    AstCCall* const m_callp;  // Call of the new function
    // Local variable -> argument passing it, nullptr if declared in the new function
    std::unordered_map<const AstVar*, AstVarScope*> m_argVscps;
    std::unordered_set<const AstVar*> m_writtenps;  // Variables the new function writes
    bool m_hasAwait = false;  // The new function suspends

    // VISITORS
    void visit(AstCAwait* nodep) override {
        m_hasAwait = true;
        iterateChildren(nodep);
    }
    void visit(AstVar* nodep) override {
        m_argVscps.emplace(nodep, nullptr);
        iterateChildren(nodep);
    }
    void visit(AstVarRef* nodep) override {
        AstVar* const varp = nodep->varp();
        if (!varp->isFuncLocal()) return;
        const auto pair = m_argVscps.emplace(varp, nullptr);
        if (pair.second) {
            const bool constRef = varp->isConstRef();
            pair.first->second
                = V3Sched::util::newArgument(m_funcp, varp->dtypep(), varp->name(),
                                             constRef ? VDirection::CONSTREF : VDirection::REF);
            // Passed by reference either way; read-only at the call if the function only reads it
            const bool written = m_writtenps.count(varp);
            m_callp->addArgsp(new AstVarRef{m_callp->fileline(), nodep->varScopep(),
                                            written ? VAccess::READWRITE : VAccess::READ});
        }
        if (AstVarScope* const vscp = pair.first->second) {
            nodep->varp(vscp->varp());
            nodep->varScopep(vscp);
        }
    }
    void visit(AstNode* nodep) override { iterateChildren(nodep); }

public:
    // CONSTRUCTORS
    OutlineArgsVisitor(AstCFunc* funcp, AstCCall* callp)
        : m_funcp{funcp}
        , m_callp{callp} {
        funcp->stmtsp()->foreachAndNext([this](const AstVarRef* refp) {
            if (refp->access().isWriteOrRW()) m_writtenps.emplace(refp->varp());
        });
        iterateAndNextNull(funcp->stmtsp());
    }
    ~OutlineArgsVisitor() override = default;

    bool hasAwait() const { return m_hasAwait; }
};

//######################################################################
// Outline parts of large coroutines

class OutlineVisitor final : public VNVisitor {
    // NODE STATE
    //  AstNodeStmt::user1p()  -> StmtInfo. Analysis of statement in the current coroutine
    const VNUser1InUse m_user1InUse;

    // TYPES
    struct StmtInfo final {
        size_t m_size = 0;  // Number of nodes in the statement
        int m_depth = 0;  // Nesting depth of the statement in the coroutine
        bool m_movable = false;  // Can move into another function
    };
    struct StmtRange final {
        AstNodeStmt* m_firstp;  // First statement
        AstNodeStmt* m_lastp;  // Last statement
        size_t m_size;  // Number of nodes in the statements
    };

    // STATE
    AstUser1Allocator<AstNodeStmt, StmtInfo> m_info;
    const size_t m_limit = static_cast<size_t>(v3Global.opt.outputSplitCFuncs());
    AstCFunc* m_funcp = nullptr;  // Current coroutine
    size_t m_funcNum = 0;  // Number of functions outlined from the current coroutine
    std::vector<StmtRange> m_groups;  // Statements to move, each group into a new function
    size_t m_count = 0;  // Number of nodes analyzed
    int m_depth = 0;  // Nesting depth of the statement being analyzed
    int m_targetDepth = 0;  // Least depth of the jump and loop test targets in the statement
    VDouble0 m_statFuncs;  // Number of functions created

    // METHODS - analysis
    // Analyze 'nodep', which jumps to or tests the loop of the statement at 'targetDepth'
    void analyze(AstNodeStmt* nodep, int targetDepth) {
        StmtInfo& info = m_info(nodep);
        VL_RESTORER(m_depth);
        info.m_depth = ++m_depth;
        const size_t startCount = m_count++;
        const int outerTargetDepth = m_targetDepth;
        m_targetDepth = targetDepth;
        iterateChildren(nodep);
        info.m_size = m_count - startCount;
        info.m_movable = m_targetDepth >= info.m_depth;
        m_targetDepth = std::min(m_targetDepth, outerTargetDepth);
    }

    // METHODS - decision
    // Cut 'run' into groups no larger than the limit, to move
    void groupRun(const StmtRange& run) {
        StmtRange group{run.m_firstp, nullptr, 0};
        for (AstNode* nodep = run.m_firstp; nodep != run.m_lastp->nextp();
             nodep = nodep->nextp()) {
            AstNodeStmt* const stmtp = VN_AS(nodep, NodeStmt);
            const size_t size = m_info(stmtp).m_size;
            if (group.m_size + size > m_limit) {
                m_groups.push_back(group);
                group = StmtRange{stmtp, nullptr, 0};
            }
            group.m_lastp = stmtp;
            group.m_size += size;
        }
        m_groups.push_back(group);
    }
    // Choose statements under 'stmtp' to move until it is within the limit, return its size left
    size_t reduce(AstNodeStmt* stmtp) {
        size_t size = m_info(stmtp).m_size;
        std::vector<AstNode*> listps;  // Statement lists directly under 'stmtp'
        if (AstNodeIf* const ifp = VN_CAST(stmtp, NodeIf)) {
            listps = {ifp->thensp(), ifp->elsesp()};
        } else if (AstLoop* const loopp = VN_CAST(stmtp, Loop)) {
            listps = {loopp->stmtsp()};
        } else if (AstJumpBlock* const blockp = VN_CAST(stmtp, JumpBlock)) {
            listps = {blockp->stmtsp()};
        }
        std::vector<StmtRange> runs;  // Runs of movable statements no larger than the limit
        std::vector<AstNodeStmt*> largeps;  // Statements larger than the limit
        for (AstNode* const listp : listps) {
            StmtRange run{nullptr, nullptr, 0};
            for (AstNode* nodep = listp; nodep; nodep = nodep->nextp()) {
                AstNodeStmt* const subp = VN_CAST(nodep, NodeStmt);  // Else a declaration
                if (subp && m_info(subp).m_size > m_limit) largeps.push_back(subp);
                if (subp && m_info(subp).m_movable && m_info(subp).m_size <= m_limit) {
                    if (!run.m_firstp) run.m_firstp = subp;
                    run.m_lastp = subp;
                    run.m_size += m_info(subp).m_size;
                    continue;
                }
                if (run.m_firstp) runs.push_back(run);
                run = StmtRange{nullptr, nullptr, 0};
            }
            if (run.m_firstp) runs.push_back(run);
        }
        // Each of these alone is over the limit, so all need reducing
        for (AstNodeStmt* const largep : largeps) {
            size -= m_info(largep).m_size - reduce(largep);
        }
        std::stable_sort(runs.begin(), runs.end(), [](const StmtRange& a, const StmtRange& b) {
            return a.m_size > b.m_size;
        });
        for (const StmtRange& run : runs) {
            if (size <= m_limit) break;
            groupRun(run);
            size -= run.m_size;
        }
        return size;
    }

    // METHODS - rewrite
    // Move statements 'firstp' to 'lastp' into a new function, and call it in their place
    void outline(AstNodeStmt* firstp, AstNodeStmt* lastp) {
        FileLine* const flp = firstp->fileline();
        VNRelinker relinker;
        firstp->unlinkFrBackWithNext(&relinker);
        AstNode* const restp = lastp->nextp();
        if (restp) restp->unlinkFrBackWithNext();

        AstScope* const scopep = m_funcp->scopep();
        const std::string name = m_funcp->name() + "__outline" + cvtToStr(m_funcNum++);
        AstCFunc* const subFuncp = new AstCFunc{flp, name, scopep};
        scopep->addBlocksp(subFuncp);
        subFuncp->isStatic(m_funcp->isStatic());
        subFuncp->isLoose(m_funcp->isLoose());
        subFuncp->slow(m_funcp->slow());
        if (m_funcp->needProcess()) subFuncp->setNeedProcess();
        subFuncp->addStmtsp(firstp);
        AstCCall* const callp = new AstCCall{flp, subFuncp};
        callp->dtypeSetVoid();
        if (VN_IS(scopep->modp(), Class)) {
            subFuncp->argTypes(EmitCUtil::symClassVar());
            callp->argTypes("vlSymsp");
        }

        const OutlineArgsVisitor argsVisitor{subFuncp, callp};
        AstNode* stmtp;
        if (argsVisitor.hasAwait()) {
            subFuncp->rtnType("VlCoroutine");
            stmtp = new AstCAwait{flp, callp};
        } else {
            stmtp = callp->makeStmt();
        }
        if (restp) stmtp->addNext(restp);
        relinker.relink(stmtp);
        ++m_statFuncs;
    }

    void outlineFunc(AstCFunc* funcp) {
        m_funcp = funcp;
        m_funcNum = 0;
        m_count = 0;
        m_targetDepth = std::numeric_limits<int>::max();
        iterateAndNextNull(funcp->stmtsp());
        for (AstNode* nodep = funcp->stmtsp(); nodep; nodep = nodep->nextp()) {
            AstNodeStmt* const stmtp = VN_CAST(nodep, NodeStmt);  // Else a declaration
            if (stmtp && m_info(stmtp).m_size > m_limit) reduce(stmtp);
        }
        for (const StmtRange& group : m_groups) outline(group.m_firstp, group.m_lastp);
        m_groups.clear();
    }

    // VISITORS - analysis
    void visit(AstNodeStmt* nodep) override { analyze(nodep, std::numeric_limits<int>::max()); }
    void visit(AstJumpGo* nodep) override { analyze(nodep, m_info(nodep->blockp()).m_depth); }
    void visit(AstLoopTest* nodep) override { analyze(nodep, m_info(nodep->loopp()).m_depth); }
    // Returns from the coroutine, so no statement containing it can move
    void visit(AstFinishFork* nodep) override { analyze(nodep, 0); }
    void visit(AstNode* nodep) override {
        ++m_count;
        iterateChildren(nodep);
    }

    // CONSTRUCTORS
    explicit OutlineVisitor(AstNetlist* netlistp) {
        // Gather the coroutines first, as outlining adds functions
        std::vector<AstCFunc*> funcps;
        for (AstNode* modp = netlistp->modulesp(); modp; modp = modp->nextp()) {
            for (AstNode* nodep = VN_AS(modp, NodeModule)->stmtsp(); nodep;
                 nodep = nodep->nextp()) {
                AstScope* scopep = VN_CAST(nodep, Scope);
                if (AstTopScope* const topp = VN_CAST(nodep, TopScope)) scopep = topp->scopep();
                if (!scopep) continue;
                for (AstNode* blockp = scopep->blocksp(); blockp; blockp = blockp->nextp()) {
                    AstCFunc* const funcp = VN_AS(blockp, CFunc);
                    if (funcp->isCoroutine()) funcps.push_back(funcp);
                }
            }
        }
        for (AstCFunc* const funcp : funcps) outlineFunc(funcp);
    }
    ~OutlineVisitor() override { V3Stats::addStat("Outline, functions created", m_statFuncs); }

public:
    static void apply(AstNetlist* netlistp) { OutlineVisitor{netlistp}; }
};

//######################################################################
// Outline class functions

void V3Outline::outlineAll(AstNetlist* nodep) {
    UINFO(2, __FUNCTION__ << ":");
    OutlineVisitor::apply(nodep);
    V3Global::dumpCheckGlobalTree("outline", 0, dumpTreeEitherLevel() >= 3);
}
