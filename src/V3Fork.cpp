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
    // STATE
    AstNodeModule* m_modp = nullptr;  // Class/module we are currently under
    int m_fork = 0;  // level of fork..join_* nesting
    AstVar* m_capturedVarsp = nullptr;  // Local copies of captured variables
    std::set<AstVar*> m_forkLocalsp;  // Variables local to a given fork
    AstArg* m_capturedVarRefsp = nullptr;  // References to captured variables (as args
    bool m_capture = false;  // Enable variable capturing
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

    AstTask* turnBlockToTask(AstNodeBlock* blockp, AstVar* captures) {
        AstNode* stmtsp = blockp->stmtsp();
        UASSERT(stmtsp, "No stmtsp\n");
        stmtsp = stmtsp->unlinkFrBackWithNext();
        stmtsp = AstNode::addNext(static_cast<AstNode*>(captures), stmtsp);
        // TODO: Ensure no collisions
        std::string taskName = m_modp->name() + "__BEGIN_"
                               + (!blockp->name().empty() ? (blockp->name() + "__") : "UNNAMED__")
                               + cvtToHex(blockp);
        AstTask* taskp = new AstTask{blockp->fileline(), taskName, stmtsp};
        ++m_createdTasksCount;
        return taskp;
    }

    // VISITORS
    void visit(AstFork* nodep) override {
        VL_RESTORER(m_fork);
        VL_RESTORER(m_forkLocalsp);
        if (!nodep->joinType().join()) {
            ++m_fork;
            m_forkLocalsp.clear();
        }
        iterateChildren(nodep);
    }
    void visit(AstNodeBlock* nodep) override {
        if (!m_fork) {
            iterateChildren(nodep);
            return;
        }

        VL_RESTORER(m_capture);
        VL_RESTORER(m_capturedVarsp);
        VL_RESTORER(m_capturedVarRefsp);

        m_capture = true;
        m_capturedVarsp = nullptr;
        m_capturedVarRefsp = nullptr;

        iterateChildren(nodep);

        AstTask* taskp = turnBlockToTask(nodep, m_capturedVarsp);
        m_modp->addStmtsp(taskp);

        AstTaskRef* taskrefp
            = new AstTaskRef{nodep->fileline(), taskp->name(), m_capturedVarRefsp};
        AstStmtExpr* taskcallp = new AstStmtExpr{nodep->fileline(), taskrefp};
        // Replaced nodes will be revisited, so we don't need to "lift" the arguments
        // as captures in case of nested forks
        nodep->replaceWith(taskcallp);
        VL_DO_DANGLING(nodep->deleteTree(), nodep);
    }
    void visit(AstVar* nodep) override {
        if (m_fork) m_forkLocalsp.insert(nodep);
        iterateChildren(nodep);
    }
    void visit(AstVarRef* nodep) override {
        if (m_capture && (m_forkLocalsp.count(nodep->varp()) == 0)
            && !nodep->varp()->lifetime().isStatic()) {
            if (nodep->access().isWriteOrRW()) {
                nodep->v3warn(E_TASKNSVAR, "Invalid capture: Process might outlive this "
                                           "variable. Initialize a local copy instead.");
                return;
            }
            processCapturedRef(nodep);
        }
        iterateChildren(nodep);
    }
    void visit(AstNodeModule* nodep) override {
        VL_RESTORER(m_modp);
        m_modp = nodep;
        iterateChildren(nodep);
    }
    void visit(AstNode* nodep) override { iterateChildren(nodep); }

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
