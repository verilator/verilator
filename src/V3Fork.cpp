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
    // AstNode::user1()         -> bool, 1 = Node was created as a call to an asynchronous task
    // AstVarRef::user2()       -> bool, 1 = Node is a class handle reference. The handle gets
    //                                       modified in the context of this reference.
    const VNUser1InUse m_inuser1;
    const VNUser2InUse m_inuser2;

    // STATE
    AstNodeModule* m_modp = nullptr;  // Class/module we are currently under
    int m_forkDepth = 0;  // Nesting level of asynchronous forks
    bool m_newProcess = false;  // True if we are directly under an asynchronous fork.
    AstVar* m_capturedVarsp = nullptr;  // Local copies of captured variables
    std::set<AstVar*> m_forkLocalsp;  // Variables local to a given fork
    AstArg* m_capturedVarRefsp = nullptr;  // References to captured variables (as args)
    int m_createdTasksCount = 0;  // Number of tasks created by this visitor

    // METHODS
    AstVar* captureRef(AstNodeExpr* refp) {
        AstVar* varp = nullptr;
        for (varp = m_capturedVarsp; varp; varp = VN_AS(varp->nextp(), Var))
            if (varp->name() == refp->name()) break;
        if (!varp) {
            // Create a local copy for a capture
            varp = new AstVar{refp->fileline(), VVarType::BLOCKTEMP, refp->name(), refp->dtypep()};
            varp->direction(VDirection::INPUT);
            varp->funcLocal(true);
            varp->lifetime(VLifetime::AUTOMATIC);
            m_capturedVarsp = AstNode::addNext(m_capturedVarsp, varp);
            // Use the original ref as an argument for call
            AstArg* arg = new AstArg{refp->fileline(), refp->name(), refp->cloneTree(false)};
            m_capturedVarRefsp = AstNode::addNext(m_capturedVarRefsp, arg);
        }
        return varp;
    }

    AstTask* makeTask(FileLine* fl, AstNode* stmtsp, std::string name) {
        stmtsp = AstNode::addNext(static_cast<AstNode*>(m_capturedVarsp), stmtsp);
        AstTask* const taskp = new AstTask{fl, name, stmtsp};
        ++m_createdTasksCount;
        return taskp;
    }

    std::string generateTaskName(AstNode* fromp, std::string kind) {
        // TODO: Ensure no collisions occur
        return "__V" + kind + (!fromp->name().empty() ? (fromp->name() + "__") : "UNNAMED__")
               + cvtToHex(fromp);
    }

    void visitTaskifiable(AstNode* nodep) {
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

        // If there are no captures, there's no need to taskify
        if (m_forkLocalsp.empty() && (m_capturedVarsp == nullptr) && !v3Global.opt.fTaskifyAll())
            return;

        VNRelinker handle;
        AstTask* taskp = nullptr;

        if (AstBegin* beginp = VN_CAST(nodep, Begin)) {
            UASSERT(beginp->stmtsp(), "No stmtsp\n");
            const std::string taskName = generateTaskName(beginp, "__FORK_BEGIN_");
            taskp
                = makeTask(beginp->fileline(), beginp->stmtsp()->unlinkFrBackWithNext(), taskName);
            beginp->unlinkFrBack(&handle);
            VL_DO_DANGLING(beginp->deleteTree(), beginp);
        } else if (AstNodeStmt* stmtp = VN_CAST(nodep, NodeStmt)) {
            const std::string taskName = generateTaskName(stmtp, "__FORK_STMT_");
            taskp = makeTask(stmtp->fileline(), stmtp->unlinkFrBack(&handle), taskName);
        } else if (AstFork* forkp = VN_CAST(nodep, Fork)) {
            const std::string taskName = generateTaskName(forkp, "__FORK_NESTED_");
            taskp = makeTask(forkp->fileline(), forkp->unlinkFrBack(&handle), taskName);
        }

        m_modp->addStmtsp(taskp);

        AstTaskRef* const taskrefp
            = new AstTaskRef{nodep->fileline(), taskp->name(), m_capturedVarRefsp};
        AstStmtExpr* const taskcallp = new AstStmtExpr{nodep->fileline(), taskrefp};
        // Replaced nodes will be revisited, so we don't need to "lift" the arguments
        // as captures in case of nested forks.
        handle.relink(taskcallp);
        taskcallp->user1(true);
    }

    // VISITORS
    void visit(AstFork* nodep) override {
        bool nested = m_newProcess;

        VL_RESTORER(m_forkLocalsp);
        VL_RESTORER(m_newProcess);
        VL_RESTORER(m_forkDepth)
        if (!nodep->joinType().join()) {
            ++m_forkDepth;
            m_newProcess = true;
            m_forkLocalsp.clear();
            // Nested forks get moved into separate tasks
            if (nested) {
                visitTaskifiable(nodep);
                return;
            }
        } else {
            m_newProcess = false;
        }
        iterateChildren(nodep);
    }
    void visit(AstBegin* nodep) override { visitTaskifiable(nodep); }
    void visit(AstNodeStmt* nodep) override { visitTaskifiable(nodep); }
    void visit(AstVar* nodep) override {
        if (m_forkDepth) m_forkLocalsp.insert(nodep);
    }
    void visit(AstVarRef* nodep) override {

        // VL_KEEP_THIS ensures that we hold a handle to the class
        if (m_forkDepth && !nodep->varp()->isFuncLocal() && nodep->varp()->isClassMember()) return;

        if (m_forkDepth && (m_forkLocalsp.count(nodep->varp()) == 0)
            && !nodep->varp()->lifetime().isStatic()) {
            if (nodep->access().isWriteOrRW()
                && (!nodep->isClassHandleValue() || nodep->user2())) {
                nodep->v3warn(
                    E_LIFETIME,
                    "Invalid reference: Process might outlive variable `"
                        << nodep->varp()->name() << "`.\n"
                        << nodep->varp()->warnMore()
                        << "... Suggest use it as read-only to initialize a local copy at the "
                           "beginning of the process, or declare it as static. It is also "
                           "possible to refer by reference to objects and their members.");
                return;
            }
            UASSERT_OBJ(
                !nodep->varp()->lifetime().isNone(), nodep,
                "Variable's lifetime is unknown. Can't determine if a capture is necessary.");

            AstVar* const varp = captureRef(nodep);
            nodep->varp(varp);
        }
    }
    void visit(AstAssign* nodep) override {
        if (VN_IS(nodep->lhsp(), VarRef) && nodep->lhsp()->isClassHandleValue()) {
            nodep->lhsp()->user2(true);
        }
        visit(static_cast<AstNodeStmt*>(nodep));
    }
    void visit(AstThisRef* nodep) override { return; }
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
