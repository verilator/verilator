// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Create separate tasks for forked processes that
//              can outlive their parents
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2023 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************
// V3Fork's Transformations:
//
// Each module:
//      Look for FORKs [JOIN_NONE]/[JOIN_ANY]
//          FORK(stmts) -> TASK(stmts), FORK(TASKREF(inits))
//
// FORKs that spawn tasks which might outlive their parents require those
// tasks to carry their own frames and as such they require their own
// variable scopes.
//
//*************************************************************************

#include "config_build.h"
#include "verilatedos.h"

#include "V3Fork.h"

#include "V3Ast.h"
#include "V3AstNodeExpr.h"
#include "V3Global.h"

#include <algorithm>
#include <set>

VL_DEFINE_DEBUG_FUNCTIONS;

//######################################################################
// Fork visitor, transforms asynchronous blocks into separate tasks

class ForkVisitor final : public VNVisitor {
private:
    // NODE STATE
    // AstVar::user1           -> bool, 1 = Node was created as a call to an asynchronous task
    const VNUser1InUse m_inuser1;

    // STATE
    AstNodeModule* m_modp = nullptr;  // Class/module we are currently under
    int m_forkDepth = 0;  // Nesting level of asynchronous forks
    bool m_newProcess = false;  // True if we are directly under an asynchronous fork.
    AstVar* m_capturedVarsp = nullptr;  // Local copies of captured variables
    std::set<AstVar*> m_forkLocalsp;  // Variables local to a given fork
    AstArg* m_capturedVarRefsp = nullptr;  // References to captured variables (as args
    int m_createdTasksCount = 0;  // Number of tasks created by this visitor

    // METHODS
    void processCapturedRef(AstVarRef* vrefp) {
        AstVar* varp = nullptr;
        for (varp = m_capturedVarsp; varp; varp = VN_AS(varp->nextp(), Var))
            if (varp->name() == vrefp->name()) break;
        if (!varp) {
            // Create a local copy for a capture
            varp = new AstVar{vrefp->fileline(), VVarType::MEMBER, vrefp->name(), vrefp->dtypep()};
            varp->direction(VDirection::INPUT);
            varp->funcLocal(true);
            varp->lifetime(VLifetime::AUTOMATIC);
            m_capturedVarsp = AstNode::addNext(m_capturedVarsp, varp);
            // Use the original ref as an argument for call
            AstArg* arg = new AstArg{vrefp->fileline(), vrefp->name(), vrefp->cloneTree(false)};
            m_capturedVarRefsp = AstNode::addNext(m_capturedVarRefsp, arg);
        }
        vrefp->varp(varp);
    }

    AstTask* makeTask(FileLine* fl, AstNode* stmtsp, AstVar* captures, std::string name) {
        stmtsp = AstNode::addNext(static_cast<AstNode*>(captures), stmtsp);
        AstTask* taskp = new AstTask{fl, name, stmtsp};
        ++m_createdTasksCount;
        return taskp;
    }

    std::string generateTaskName(AstNode* fromp, std::string kind) {
        // TODO: Ensure no collisions occur
        return m_modp->name() + kind
               + (!fromp->name().empty() ? (fromp->name() + "__") : "UNNAMED__") + cvtToHex(fromp);
    }

    AstTask* turnBlockIntoTask(AstNodeBlock* blockp, AstVar* captures, VNRelinker& handle) {
        UASSERT(blockp->stmtsp(), "No stmtsp\n");
        std::string taskName = generateTaskName(blockp, "__FORK_BLOCK_");
        AstTask* task = makeTask(blockp->fileline(), blockp->stmtsp()->unlinkFrBackWithNext(),
                                 captures, taskName);
        blockp->unlinkFrBack(&handle);
        VL_DO_DANGLING(blockp->deleteTree(), blockp);
        return task;
    }

    AstTask* turnStatementIntoTask(AstNodeStmt* stmtp, AstVar* captures, VNRelinker& handle) {
        std::string taskName = generateTaskName(stmtp, "__FORK_STMT_");
        return makeTask(stmtp->fileline(), stmtp->unlinkFrBack(&handle), captures, taskName);
    }

    void visitBlockOrStmt(AstNode* nodep, bool block) {
        if (!m_newProcess || nodep->user1()) {
            VL_RESTORER(m_forkDepth);
            if (nodep->user1()) {
                UASSERT(m_forkDepth > 0, "Wrong fork depth!");
                --m_forkDepth;
            }
            iterateChildren(nodep);
            return;
        }

        VL_RESTORER(m_capturedVarsp);
        VL_RESTORER(m_capturedVarRefsp);
        VL_RESTORER(m_newProcess);
        m_capturedVarsp = nullptr;
        m_capturedVarRefsp = nullptr;
        m_newProcess = false;

        iterateChildren(nodep);

        if (m_capturedVarsp == nullptr) return;  // No captures - no need to taskify

        VNRelinker handle;
        AstTask* taskp
            = block ? turnBlockIntoTask(VN_AS(nodep, NodeBlock), m_capturedVarsp, handle)
                    : turnStatementIntoTask(VN_AS(nodep, NodeStmt), m_capturedVarsp, handle);
        m_modp->addStmtsp(taskp);

        AstTaskRef* taskrefp
            = new AstTaskRef{nodep->fileline(), taskp->name(), m_capturedVarRefsp};
        AstStmtExpr* taskcallp = new AstStmtExpr{nodep->fileline(), taskrefp};
        // Replaced nodes will be revisited, so we don't need to "lift" the arguments
        // as captures in case of nested forks.
        handle.relink(taskcallp);
        taskcallp->user1(true);
    }

    // VISITORS
    void visit(AstFork* nodep) override {
        VL_RESTORER(m_forkLocalsp);
        VL_RESTORER(m_newProcess);
        VL_RESTORER(m_forkDepth)
        if (!nodep->joinType().join()) {
            ++m_forkDepth;
            m_newProcess = true;
            m_forkLocalsp.clear();
        } else {
            m_newProcess = false;
        }
        iterateChildren(nodep);
    }
    void visit(AstBegin* nodep) override { visitBlockOrStmt(nodep, true); }
    void visit(AstNodeStmt* nodep) override { visitBlockOrStmt(nodep, false); }
    void visit(AstVar* nodep) override {
        if (m_forkDepth) m_forkLocalsp.insert(nodep);
    }
    void visit(AstVarRef* nodep) override {
        if (m_forkDepth && (m_forkLocalsp.count(nodep->varp()) == 0)
            && !nodep->varp()->lifetime().isStatic()) {
            if (nodep->access().isWriteOrRW()) {
                nodep->v3warn(E_TASKNSVAR, "Invalid capture: Process might outlive this "
                                           "variable. Initialize a local copy instead.");
                return;
            }
            UASSERT_OBJ(
                !nodep->varp()->lifetime().isNone(), nodep,
                "Variable's lifetime is unknown. Can't determine if a capture is necessary.");
            processCapturedRef(nodep);
        }
    }
    void visit(AstNodeModule* nodep) override {
        VL_RESTORER(m_modp);

        m_modp = nodep;
        iterateChildren(nodep);
    }
    void visit(AstNode* nodep) override {
        VL_RESTORER(m_newProcess)
        VL_RESTORER(m_forkDepth);
        if (nodep->user1()) --m_forkDepth;
        m_newProcess = false;
        iterateChildren(nodep);
    }

public:
    // CONSTRUCTORS
    ForkVisitor(AstNetlist* nodep) { visit(nodep); }
    ~ForkVisitor() override = default;

    // UTILITY
    int createdTasksCount() { return m_createdTasksCount; }
};

//######################################################################
// Fork class functions

int V3Fork::makeTasks(AstNetlist* nodep) {
    int createdTasksCount;

    UINFO(2, __FUNCTION__ << ": " << endl);
    {
        ForkVisitor fork_visitor(nodep);
        createdTasksCount = fork_visitor.createdTasksCount();
    }
    V3Global::dumpCheckGlobalTree("fork", 0, dumpTreeLevel() >= 3);

    return createdTasksCount;
}
