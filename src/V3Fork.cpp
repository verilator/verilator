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

class ForkVisitor final : public VNVisitor {
private:
    AstNodeModule* m_modp = nullptr;
    // AstNodeFTask* m_funcp = nullptr;
    AstFork* m_fork = nullptr;
    AstVar* m_capturedVarsp = nullptr;
    // Problem: where to lift the variables? What in case of nested forks?
    std::set<AstVar*> m_forkLocalsp;  // Variables local to a given fork
    AstArg* m_capturedVarRefsp = nullptr;
    bool m_capture = false;

    void processCapturedRef(AstVarRef* vrefp) {
        AstVar* varp
            = new AstVar{vrefp->fileline(), VVarType::MEMBER, vrefp->name(), vrefp->dtypep()};
        varp->direction(VDirection::INPUT);
        varp->funcLocal(true);
        varp->lifetime(VLifetime::AUTOMATIC);
        m_capturedVarsp = AstNode::addNext(m_capturedVarsp, varp);
        // Use the original ref as an argument for call
        AstArg* arg = new AstArg{vrefp->fileline(), vrefp->name(), vrefp->cloneTree(false)};
        m_capturedVarRefsp = AstNode::addNext(m_capturedVarRefsp, arg);
        vrefp->varp(varp);
        // We don't need to update scope as those don't exist yet.
    }

    AstTask* turnBlockToTask(AstNodeBlock* blockp, AstVar* captures) {
        AstNode* stmtsp = blockp->stmtsp();
        stmtsp = stmtsp->unlinkFrBackWithNext();

        //// Question: does it still work for nested forks?
        //// > Probably yes, in caseof nested fork we won't find any vars next time
        //// > [this could be optimized then]
        // stmtsp->foreach([&](AstVar* varp) {
        //     varp = varp->unlinkFrBack();
        //     m_liftedp = AstNode::addNext(m_liftedp, varp);
        // });

        std::string taskName = "test_name";  // TODO: Generate name

        stmtsp = AstNode::addNext(static_cast<AstNode*>(captures), stmtsp);

        AstTask* taskp = new AstTask{blockp->fileline(), taskName, stmtsp};
        // if (captures)
        //     taskp->fvarp(AstNode::addNext(taskp->fvarp(), captures));

        return taskp;
    }

    void visit(AstFork* nodep) override {
        VL_RESTORER(m_fork);
        VL_RESTORER(m_forkLocalsp);
        if (!nodep->joinType().join()) {
            m_fork = nodep;
            m_forkLocalsp.clear();
        }
        iterateChildren(nodep);
    }

    void visit(AstNodeBlock* nodep) override {
        if (!m_fork) {
            iterateChildren(nodep);
            return;
        }

        VL_RESTORER(m_capturedVarRefsp);

        // Collect captures
        AstVar* parentCapturesp = m_capturedVarsp;
        {
            VL_RESTORER(m_capture);
            m_capture = true;
            m_capturedVarsp = nullptr;
            iterateChildren(nodep);
        }
        // We might need to propagate the captures in case of nested forks
        if (m_capturedVarsp)
            parentCapturesp = AstNode::addNext(parentCapturesp, m_capturedVarsp->cloneTree(true));

        // TODO: Check scoping - captures can't be refs to fork's scope.

        AstTask* taskp = turnBlockToTask(nodep, m_capturedVarsp);
        m_modp->addStmtsp(taskp);

        m_capturedVarsp = parentCapturesp;  // Restore captures

        AstTaskRef* taskrefp
            = new AstTaskRef{nodep->fileline(), taskp->name(), m_capturedVarRefsp};
        AstStmtExpr* taskcallp = new AstStmtExpr{nodep->fileline(), taskrefp};
        nodep->replaceWith(taskcallp);
        VL_DO_DANGLING(nodep->deleteTree(), nodep);
    }

    void visit(AstVar* nodep) override {
        if (m_fork) m_forkLocalsp.insert(nodep);
        iterateChildren(nodep);
    }

    // Problem: we shouldn't treat refs to internal variables as captures.
    void visit(AstVarRef* nodep) override {
        // UINFO(1, "Referenced var: " << nodep->varp() << "\n");
        // UINFO(1, "Locals: \n");
        for (auto* item : m_forkLocalsp) { UINFO(1, "  * " << item << "\n"); }
        if (m_capture && (m_forkLocalsp.count(nodep->varp()) == 0)) {
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
    ForkVisitor(AstNetlist* nodep) { visit(nodep); }
};

void V3Fork::makeTasks(AstNetlist* nodep) {
    UINFO(2, __FUNCTION__ << ": " << endl);
    { ForkVisitor fork_visitor(nodep); }
    V3Global::dumpCheckGlobalTree("fork", 0, dumpTreeLevel() >= 3);
}
