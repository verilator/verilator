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
#include <stack>

VL_DEFINE_DEBUG_FUNCTIONS;

//######################################################################
// Fork visitor, transforms asynchronous blocks into separate tasks

class ForkVisitor final : public VNVisitor {
private:

    class DynScopeFrame {
    public:
        DynScopeFrame() = default;
        DynScopeFrame(FileLine *fl, string className, string handleName, AstNodeModule* modp) {
            m_classp = new AstClass{fl, className};
            m_refDTypep = new AstClassRefDType{fl, m_classp, nullptr};
            v3Global.rootp()->typeTablep()->addTypesp(m_refDTypep);
            UASSERT_OBJ(modp != m_classp, m_classp, "Adding self as dynamic scope");
            UASSERT_OBJ(!m_classp->nextp(), m_classp, "Dynamic scope is not alone");
            UASSERT_OBJ(!m_classp->backp(), m_classp, "Dynamic scope is already linked");
            modp = AstNode::addNext(modp, m_classp);

            m_handlep =
                new AstVar{fl, VVarType::BLOCKTEMP, handleName, m_refDTypep};
            m_handlep->funcLocal(true);
            m_handlep->lifetime(VLifetime::AUTOMATIC);
        }

        inline AstClass* classp() { return m_classp; }
        inline AstClassRefDType* dtypep() { return m_refDTypep; }
        inline AstVar* handlep() { return m_handlep; }

        inline void clear() {
            m_classp = nullptr;
            m_refDTypep = nullptr;
            m_handlep = nullptr;
        }

        inline operator bool() {
            return m_classp != nullptr;
        }

        void addConstructor() {
            AstFunc* newp = new AstFunc{m_classp->fileline(), "new", nullptr, nullptr};
            newp->isConstructor(true);
            newp->classMethod(true);
            newp->dtypep(newp->findVoidDType());
            m_classp->addStmtsp(newp);
            m_classp->repairCache();

            m_classp->user2(true);
        }

    private:
        AstClass* m_classp = nullptr; // Class for holding variables of dynamic scope
        AstClassRefDType* m_refDTypep = nullptr; // RefDType for the above
        AstVar* m_handlep = nullptr; // Class handle for holding variables of dynamic scope
    };



    // NODE STATE
    // AstNode::user1()         -> bool, 1 = Node was created as a call to an asynchronous task
    // AstVarRef::user2()       -> bool, 1 = Node is a class handle reference. The handle gets
    //                                       modified in the context of this reference.
    // AstVar::user2()          -> bool, 1 = Variable is moved to dynamic
    // AstClass::user2()        -> bool, 1 = Class is finalized (can no longer capture)
    const VNUser1InUse m_inuser1;
    const VNUser2InUse m_inuser2;

    // STATE
    AstNodeModule* m_modp = nullptr;  // Class/module we are currently under
    int m_forkDepth = 0;  // Nesting level of asynchronous forks
    bool m_newProcess = false;  // True if we are directly under an asynchronous fork.
    AstVar* m_capturedVarsp = nullptr;  // Local copies of captured variables
    DynScopeFrame m_dynScope;
    AstNode* m_procp = nullptr; // Task/function/block we are currently under (not forked)
    std::set<AstVar*> m_forkLocalsp;  // Variables local to a given fork
    AstArg* m_capturedVarRefsp = nullptr;  // References to captured variables (as args)

    // METHODS



    // Creates an "anonymous" class for holding variables that are accessed in async forks.
    DynScopeFrame& getDynScope() {
        UASSERT(m_procp != nullptr, "creating dynamic scope while not under a task/function");
        if (!m_dynScope) {
            new(&m_dynScope) DynScopeFrame{m_procp->fileline(),
                                           generateDynScopeClassName(m_procp),
                                           generateDynScopeHandleName(m_procp),
                                           m_modp};
        }
        return m_dynScope;
    }

    AstNode* getProcStmts() {
        AstNode* stmtsp = nullptr;
        if (!m_procp)
            return nullptr;
        if (AstBegin* beginp = VN_CAST(m_procp, Begin))
            stmtsp = beginp->stmtsp();
        else if (AstNodeFTask* taskp = VN_CAST(m_procp, NodeFTask))
            stmtsp = taskp->stmtsp();
        else
            v3fatal("m_procp is not a begin block or a procedure");
        return stmtsp;
    }

    bool isVarLocalToCurrentProc(AstVar* varp) {
        // Assumption: all local variables are declared at the beginning of the block

        //TODO: Handle nesteed declarations

        UINFO(1, "CURRENT PROC: " << m_procp << "\n");

        AstNode* stmtsp = getProcStmts();
        if (!stmtsp)
            return false;

        for (AstVar* pvarp = VN_CAST(stmtsp, Var); pvarp; pvarp = VN_CAST(pvarp->nextp(), Var)) {
            if (pvarp == varp)
                return true;
        }
        return false;
    }

    bool isVarInDynScope(AstVar* varp) {
        // Assumption: all local variables are declared at the beginning of the block

        //TODO: Handle nesteed declarations

        UINFO(1, "CURRENT PROC: " << m_procp << "\n");

        AstNode* stmtsp = getProcStmts();
        if (!stmtsp)
            return false;

        for (AstVar* pvarp = VN_CAST(stmtsp, Var); pvarp; pvarp = VN_CAST(pvarp->nextp(), Var)) {
            if (pvarp == varp)
                return true;
        }
        return false;
    }

    void replaceRefWithMembersel(AstVarRef* refp) {
        DynScopeFrame& dynScope = getDynScope();

        VNRelinker handle;
        refp->unlinkFrBack(&handle);
        AstMemberSel* membersel =
            new AstMemberSel{refp->fileline(),
                             new AstVarRef{refp->fileline(), dynScope.handlep(), refp->access()},
                             refp->dtypep()};
        membersel->name(refp->varp()->name());
        membersel->varp(refp->varp());
        handle.relink(membersel);
        VL_DO_DANGLING(refp->deleteTree(), refp);
    }

    // Updates all var refs that point to stuff that was moved to dynamic scope
    void updateRefsInCurrentProc() {
        m_procp->forall([&](AstVarRef* vrefp) -> bool {
            if (vrefp->varp()->user2())
                replaceRefWithMembersel(vrefp);
            return true;
        });
    }

    void instantiateDynScopeObject() {
        UASSERT_OBJ(!m_dynScope.handlep()->nextp(), m_dynScope.handlep(), "Handle already linked");

        AstNode* stmtp = getProcStmts();
        UASSERT(stmtp, "trying to instantiate dynamic scope while not under proc");

        // Find node after last variable declaration
        while (stmtp && VN_IS(stmtp, Var))
            stmtp = stmtp->nextp();
        UASSERT(stmtp, "no proc body");

        AstNew* newp = new AstNew{m_procp->fileline(), nullptr};
        newp->taskp(VN_AS(m_dynScope.classp()->findMember("new"), NodeFTask));
        newp->dtypep(m_dynScope.dtypep());

        AstNode* asgnp =
            new AstAssign{m_procp->fileline(),
                          new AstVarRef{m_procp->fileline(), m_dynScope.handlep(), VAccess::WRITE},
                          newp};

        AstNode::addNext(static_cast<AstNode*>(m_dynScope.handlep()), asgnp);

        stmtp->addHereThisAsNext(m_dynScope.handlep());
    }

    AstVar* captureRefAsArg(AstVarRef* refp) {
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

    void captureRefIntoDynScope(AstVarRef* refp) {
        DynScopeFrame& dynScope = getDynScope();

        UASSERT_OBJ(!dynScope.classp()->user2(), dynScope.classp(), "DynScope class is finalized");

        // Move the variable definition into class
        AstVar* varp = refp->varp()->unlinkFrBack();
        if (!dynScope.classp()->findMember(varp->name())) {
            // TODO: Handle a case where the variable is function's argument
            varp->funcLocal(false);
            varp->varType(VVarType::MEMBER);
            dynScope.classp()->addStmtsp(varp);
            dynScope.classp()->repairCache(); // TODO: Optimize
        }

        replaceRefWithMembersel(refp);

        varp->user2(true);
    }

    AstTask* makeTask(FileLine* fl, AstNode* stmtsp, string name) {
        stmtsp = AstNode::addNext(static_cast<AstNode*>(m_capturedVarsp), stmtsp);
        AstTask* const taskp = new AstTask{fl, name, stmtsp};
        return taskp;
    }

    string generateTaskName(AstNode* fromp, string kind) {
        // TODO: Ensure no collisions occur
        return "__V" + kind + (!fromp->name().empty() ? (fromp->name() + "__") : "UNNAMED__")
               + cvtToHex(fromp);
    }

    string generateDynScopeClassName(AstNode* fromp) {
        // TODO: Ensure no collisions occur
        string n = "__VDynScope__" + (!fromp->name().empty() ? (fromp->name() + "__") : "ANON__")
               + cvtToHex(fromp);
        UINFO(1, "Generated \"" << n << "\" class name\n");
        return n;
    }

    string generateDynScopeHandleName(AstNode* fromp) {
        return "__VDynScope_" + (fromp->name().empty() ? cvtToHex(fromp) : fromp->name());
    }

    void visitTaskifiable(AstNode* nodep) {
        if (!m_newProcess || nodep->user1()) {
            VL_RESTORER(m_forkDepth);
            if (nodep->user1()) {
                UASSERT(m_forkDepth > 0, "Wrong fork depth!");
                --m_forkDepth;
            }
            iterateChildren(nodep);

            if (m_dynScope)
                updateRefsInCurrentProc();

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
            const string taskName = generateTaskName(beginp, "__FORK_BEGIN_");
            taskp
                = makeTask(beginp->fileline(), beginp->stmtsp()->unlinkFrBackWithNext(), taskName);
            beginp->unlinkFrBack(&handle);
            VL_DO_DANGLING(beginp->deleteTree(), beginp);
        } else if (AstNodeStmt* stmtp = VN_CAST(nodep, NodeStmt)) {
            const string taskName = generateTaskName(stmtp, "__FORK_STMT_");
            taskp = makeTask(stmtp->fileline(), stmtp->unlinkFrBack(&handle), taskName);
        } else if (AstFork* forkp = VN_CAST(nodep, Fork)) {
            const string taskName = generateTaskName(forkp, "__FORK_NESTED_");
            taskp = makeTask(forkp->fileline(), forkp->unlinkFrBack(&handle), taskName);
        }

        m_modp->addStmtsp(taskp);

        AstTaskRef* const taskrefp
            = new AstTaskRef{nodep->fileline(), taskp->name(), m_capturedVarRefsp};
        taskrefp->taskp(taskp);
        AstStmtExpr* const taskcallp = new AstStmtExpr{nodep->fileline(), taskrefp};
        // Replaced nodes will be revisited, so we don't need to "lift" the arguments
        // as captures in case of nested forks.
        handle.relink(taskcallp);
        taskcallp->user1(true);

        if (m_dynScope)
            updateRefsInCurrentProc();
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
    void visit(AstBegin* nodep) override {
        VL_RESTORER(m_procp);
        VL_RESTORER(m_dynScope);

        if (!m_forkDepth) {
            m_procp = nodep;
            m_dynScope.clear();
        }
        visitTaskifiable(nodep);

        if (m_dynScope) {
            m_dynScope.addConstructor();
            instantiateDynScopeObject();
            UINFO(1, "Instantiated an instance of " << m_dynScope.classp()->name() << "\n");
        }
    }
    void visit(AstNodeStmt* nodep) override { visitTaskifiable(nodep); }
    void visit(AstVar* nodep) override {
        if (m_forkDepth) m_forkLocalsp.insert(nodep);
    }
    void visit(AstVarRef* nodep) override {

        // VL_KEEP_THIS ensures that we hold a handle to the class
        if (m_forkDepth && !nodep->varp()->isFuncLocal() && nodep->varp()->isClassMember()) return;

        if (m_forkDepth && (m_forkLocalsp.count(nodep->varp()) == 0)
            && !nodep->varp()->lifetime().isStatic()) {


            if (isVarLocalToCurrentProc(nodep->varp())) {
                captureRefIntoDynScope(nodep);
                return;
            }
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

            AstVar* const varp = captureRefAsArg(nodep);
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
        UINFO(1, "Entering module " << nodep << "\n");
        iterateChildren(nodep);
        UINFO(1, "DUMP:\n");
        nodep->dumpTree();
        UINFO(1, "\n\n");
    }
    void visit(AstNodeFTask* nodep) override {
        VL_RESTORER(m_procp);
        VL_RESTORER(m_dynScope);
        m_dynScope.clear();

        UASSERT(m_procp == nullptr, "FTask under FTask");
        m_procp = nodep;

        visit(static_cast<AstNode*>(nodep));

        if (m_dynScope) {
            m_dynScope.addConstructor();
            instantiateDynScopeObject();
            UINFO(1, "Instantiated an instance of " << m_dynScope.classp()->name() << "\n");
        }
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
};

//######################################################################
// Fork class functions

void V3Fork::makeTasks(AstNetlist* nodep) {
    UINFO(2, __FUNCTION__ << ": " << endl);
    {
        ForkVisitor fork_visitor(nodep);
    }
    V3Global::dumpCheckGlobalTree("fork", 0, dumpTreeLevel() >= 3);
}
