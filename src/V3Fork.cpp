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
//          VARREF(var) -> MEMBERSEL(var->name, VARREF(dynscope)) (for write/RW refs)
//          FORK(stmts) -> TASK(stmts), FORK(TASKREF(inits))
//
// FORKs that spawn tasks which might outlive their parents require those
// tasks to carry their own frames and as such they require their own
// variable scopes.
// There are two mechanisms that work together to achieve that. ForkVisitor
// moves bodies of forked prcesses into new tasks, which results in them getting their
// own scopes. The original statements get replaced with a call to the task which
// passes the required variables by value.
// The second mechanism, DynScopeVisitor, is designed to handle variables which can't be
// captured by value and instead require a reference. Those variables get moved into an
// "anonymous" object, ie. a class with appropriate fields gets generated and an object
// of this class gets instantiated in place of the original variable declarations.
// Any references to those variables are replaced with references to the object's field.
// Since objects are reference-counted this ensures that the variables are accessible
// as long as both the parent and the forked processes require them to be.
//
//*************************************************************************

#include "V3PchAstNoMT.h"  // VL_MT_DISABLED_CODE_UNIT

#include "V3Fork.h"

#include "V3AstNodeExpr.h"
#include "V3MemberMap.h"

#include <set>
#include <vector>

VL_DEFINE_DEBUG_FUNCTIONS;

class ForkDynScopeInstance final {
public:
    AstClass* m_classp = nullptr;  // Class for holding variables of dynamic scope
    AstClassRefDType* m_refDTypep = nullptr;  // RefDType for the above
    AstVar* m_handlep = nullptr;  // Class handle for holding variables of dynamic scope

    // True if the instance exists
    bool initialized() const { return m_classp != nullptr; }
};

class ForkDynScopeFrame final {
private:
    // MEMBERS
    AstNodeModule* const m_modp;  // Module to insert the scope into
    AstNode* const m_procp;  // Procedure/block associated with that dynscope
    std::set<AstVar*> m_captures;  // Variables to be moved into the dynscope
    ForkDynScopeInstance m_instance;  // Nodes to be injected into the AST to create the dynscope

public:
    ForkDynScopeFrame(AstNodeModule* modp, AstNode* procp)
        : m_modp{modp}
        , m_procp{procp} {}

    ForkDynScopeInstance& createInstancePrototype() {
        UASSERT_OBJ(!m_instance.initialized(), m_procp, "Dynamic scope already instantiated.");

        m_instance.m_classp
            = new AstClass{m_procp->fileline(), generateDynScopeClassName(m_procp)};
        m_instance.m_refDTypep
            = new AstClassRefDType{m_procp->fileline(), m_instance.m_classp, nullptr};
        v3Global.rootp()->typeTablep()->addTypesp(m_instance.m_refDTypep);
        m_instance.m_handlep
            = new AstVar{m_procp->fileline(), VVarType::BLOCKTEMP,
                         generateDynScopeHandleName(m_procp), m_instance.m_refDTypep};
        m_instance.m_handlep->funcLocal(true);
        m_instance.m_handlep->lifetime(VLifetime::AUTOMATIC);

        return m_instance;
    }

    const ForkDynScopeInstance& instance() const { return m_instance; }
    void captureVarInsert(AstVar* varp) { m_captures.insert(varp); }
    bool captured(AstVar* varp) { return m_captures.count(varp) != 0; }
    AstNode* procp() const { return m_procp; }

    void populateClass() {
        UASSERT_OBJ(m_instance.initialized(), m_procp, "No DynScope prototype");

        // Move variables into the class
        for (AstVar* varp : m_captures) {
            if (varp->direction() == VDirection::INPUT) {
                varp = varp->cloneTree(false);
                varp->direction(VDirection::NONE);
            } else {
                varp->unlinkFrBack();
            }
            varp->funcLocal(false);
            varp->varType(VVarType::MEMBER);
            varp->lifetime(VLifetime::AUTOMATIC);
            varp->usedLoopIdx(false);  // No longer unrollable
            m_instance.m_classp->addStmtsp(varp);
        }

        // Create class's constructor
        AstFunc* const newp
            = new AstFunc{m_instance.m_classp->fileline(), "new", nullptr, nullptr};
        newp->isConstructor(true);
        newp->classMethod(true);
        newp->dtypep(newp->findVoidDType());
        m_instance.m_classp->addStmtsp(newp);
    }

    void linkNodes(VMemberMap& memberMap) {
        UASSERT_OBJ(m_instance.initialized(), m_procp, "No dynamic scope prototype");
        UASSERT_OBJ(!linked(), m_instance.m_handlep, "Handle already linked");

        if (VN_IS(m_procp, Fork)) {
            linkNodesOfFork(memberMap);
            return;
        }

        AstNode* stmtp = getProcStmts();
        UASSERT(stmtp, "trying to instantiate dynamic scope while not under proc");
        VNRelinker stmtpHandle;
        stmtp->unlinkFrBackWithNext(&stmtpHandle);

        // Find node after last variable declaration
        AstNode* initp = stmtp;
        while (initp && VN_IS(initp, Var)) initp = initp->nextp();
        UASSERT(stmtp, "Procedure lacks body");
        UASSERT(initp, "Procedure lacks statements besides declarations");

        AstNew* const newp = new AstNew{m_procp->fileline(), nullptr};
        newp->taskp(VN_AS(memberMap.findMember(m_instance.m_classp, "new"), NodeFTask));
        newp->dtypep(m_instance.m_refDTypep);
        newp->classOrPackagep(m_instance.m_classp);

        AstNode* const asgnp = new AstAssign{
            m_procp->fileline(),
            new AstVarRef{m_procp->fileline(), m_instance.m_handlep, VAccess::WRITE}, newp};

        AstNode* initsp = nullptr;  // Arguments need to be copied
        for (AstVar* varp : m_captures) {
            if (varp->direction() != VDirection::INPUT) continue;

            AstMemberSel* const memberselp = new AstMemberSel{
                varp->fileline(),
                new AstVarRef{varp->fileline(), m_instance.m_handlep, VAccess::WRITE},
                varp->dtypep()};
            memberselp->name(varp->name());
            memberselp->varp(VN_AS(memberMap.findMember(m_instance.m_classp, varp->name()), Var));
            AstNode* initAsgnp
                = new AstAssign{varp->fileline(), memberselp,
                                new AstVarRef{varp->fileline(), varp, VAccess::READ}};
            initsp = AstNode::addNext(initsp, initAsgnp);
        }
        if (initsp) AstNode::addNext(asgnp, initsp);

        if (initp != stmtp) {
            initp->addHereThisAsNext(asgnp);
        } else {
            AstNode::addNext(asgnp, static_cast<AstNode*>(initp));
            stmtp = asgnp;
        }

        AstNode::addNext(static_cast<AstNode*>(m_instance.m_handlep), stmtp);
        stmtpHandle.relink(m_instance.m_handlep);
        m_modp->addStmtsp(m_instance.m_classp);
    }

    bool linked() const { return m_instance.initialized() && m_instance.m_handlep->backp(); }

private:
    AstAssign* instantiateDynScope(VMemberMap& memberMap) {
        AstNew* const newp = new AstNew{m_procp->fileline(), nullptr};
        newp->taskp(VN_AS(memberMap.findMember(m_instance.m_classp, "new"), NodeFTask));
        newp->dtypep(m_instance.m_refDTypep);
        newp->classOrPackagep(m_instance.m_classp);

        return new AstAssign{
            m_procp->fileline(),
            new AstVarRef{m_procp->fileline(), m_instance.m_handlep, VAccess::WRITE}, newp};
    }

    void linkNodesOfFork(VMemberMap& memberMap) {
        // Special case

        AstFork* const forkp = VN_AS(m_procp, Fork);
        VNRelinker forkHandle;
        forkp->unlinkFrBack(&forkHandle);

        AstBegin* const beginp = new AstBegin{
            forkp->fileline(),
            "_Vwrapped_" + (forkp->name().empty() ? cvtToHex(forkp) : forkp->name()),
            m_instance.m_handlep, false, true};
        forkHandle.relink(beginp);

        AstNode* const instAsgnp = instantiateDynScope(memberMap);

        beginp->stmtsp()->addNext(instAsgnp);
        beginp->stmtsp()->addNext(forkp);

        if (forkp->initsp()) {
            forkp->initsp()->foreach([forkp](AstAssign* asgnp) {
                asgnp->unlinkFrBack();
                forkp->addHereThisAsNext(asgnp);
            });
        }
        UASSERT_OBJ(!forkp->initsp(), forkp, "Leftover nodes in block_item_declaration");

        m_modp->addStmtsp(m_instance.m_classp);
    }

    static string generateDynScopeClassName(const AstNode* fromp) {
        string n = "__VDynScope__" + (!fromp->name().empty() ? (fromp->name() + "__") : "ANON__")
                   + cvtToHex(fromp);
        return n;
    }

    static string generateDynScopeHandleName(const AstNode* fromp) {
        return "__VDynScope_" + (fromp->name().empty() ? cvtToHex(fromp) : fromp->name());
    }

    AstNode* getProcStmts() {
        AstNode* stmtsp = nullptr;
        if (!m_procp) return nullptr;
        if (AstBegin* beginp = VN_CAST(m_procp, Begin)) {
            stmtsp = beginp->stmtsp();
        } else if (AstNodeFTask* taskp = VN_CAST(m_procp, NodeFTask)) {
            stmtsp = taskp->stmtsp();
        } else {
            m_procp->v3fatalSrc("m_procp is not a begin block or a procedure");
        }
        return stmtsp;
    }
};

//######################################################################
// Dynamic scope visitor, creates classes and objects for dynamic scoping of variables and
// replaces references to varibles that need a dynamic scope with references to object's
// members

class DynScopeVisitor final : public VNVisitor {
private:
    // NODE STATE
    // AstVar::user1()          -> int, timing-control fork nesting level of that variable
    // AstVarRef::user2()       -> bool, 1 = Node is a class handle reference. The handle gets
    //                                       modified in the context of this reference.
    const VNUser1InUse m_inuser1;
    const VNUser2InUse m_inuser2;

    // STATE
    AstNodeModule* m_modp = nullptr;  // Module we are currently under
    AstNode* m_procp = nullptr;  // Function/task/block we are currently under
    std::map<AstNode*, ForkDynScopeFrame*>
        m_frames;  // Mapping from nodes to related DynScopeFrames
    VMemberMap m_memberMap;  // Class member look-up
    int m_forkDepth = 0;  // Number of asynchronous forks we are currently under
    bool m_afterTimingControl = false;  // A timing control might've be executed in the current
                                        // process

    // METHODS

    ForkDynScopeFrame* frameOf(AstNode* nodep) {
        auto frameIt = m_frames.find(nodep);
        if (frameIt == m_frames.end()) return nullptr;
        return frameIt->second;
    }

    const ForkDynScopeFrame* frameOf(AstNode* nodep) const {
        auto frameIt = m_frames.find(nodep);
        if (frameIt == m_frames.end()) return nullptr;
        return frameIt->second;
    }

    ForkDynScopeFrame* pushDynScopeFrame(AstNode* procp) {
        ForkDynScopeFrame* const framep = new ForkDynScopeFrame{m_modp, procp};
        auto r = m_frames.emplace(std::make_pair(procp, framep));
        UASSERT_OBJ(r.second, m_modp, "Procedure already contains a frame");
        return framep;
    }

    void replaceWithMemberSel(AstVarRef* refp, const ForkDynScopeInstance& dynScope) {
        VNRelinker handle;
        refp->unlinkFrBack(&handle);
        AstMemberSel* const membersel = new AstMemberSel{
            refp->fileline(), new AstVarRef{refp->fileline(), dynScope.m_handlep, refp->access()},
            refp->dtypep()};
        membersel->name(refp->varp()->name());
        if (refp->varp()->direction() == VDirection::INPUT) {
            membersel->varp(
                VN_AS(m_memberMap.findMember(dynScope.m_classp, refp->varp()->name()), Var));
        } else {
            membersel->varp(refp->varp());
        }
        handle.relink(membersel);
        VL_DO_DANGLING(refp->deleteTree(), refp);
    }

    static bool hasAsyncFork(AstNode* nodep) {
        bool afork = false;
        nodep->foreach([&](AstFork* forkp) {
            if (!forkp->joinType().join()) afork = true;
        });
        return afork;
    }

    void bindNodeToDynScope(AstNode* nodep, ForkDynScopeFrame* frame) {
        m_frames.emplace(std::make_pair(nodep, frame));
    }

    bool needsDynScope(const AstVarRef* refp) const {
        return
            // Can this variable escape the scope
            ((m_forkDepth > refp->varp()->user1()) && refp->varp()->isFuncLocal())
            && (
                // Is it mutated
                (refp->varp()->isClassHandleValue() ? refp->user2() : refp->access().isWriteOrRW())
                // Or is it after a timing-control event
                || m_afterTimingControl);
    }

    // VISITORS
    void visit(AstNodeModule* nodep) override {
        VL_RESTORER(m_modp);
        if (!VN_IS(nodep, Class)) m_modp = nodep;
        iterateChildren(nodep);
    }
    void visit(AstNodeFTask* nodep) override {
        VL_RESTORER(m_procp);
        m_procp = nodep;
        if (hasAsyncFork(nodep)) pushDynScopeFrame(m_procp);
        iterateChildren(nodep);
    }
    void visit(AstBegin* nodep) override {
        VL_RESTORER(m_procp);
        m_procp = nodep;
        if (hasAsyncFork(nodep)) pushDynScopeFrame(m_procp);
        iterateChildren(nodep);
    }
    void visit(AstFork* nodep) override {
        VL_RESTORER(m_forkDepth);
        if (!nodep->joinType().join()) ++m_forkDepth;

        const bool oldAfterTimingControl = m_afterTimingControl;

        ForkDynScopeFrame* framep = nullptr;
        if (nodep->initsp()) framep = pushDynScopeFrame(nodep);

        for (AstNode* stmtp = nodep->initsp(); stmtp; stmtp = stmtp->nextp()) {
            if (AstVar* varp = VN_CAST(stmtp, Var)) {
                // This can be probably optimized to detect cases in which dynscopes
                // could be avoided
                if (!framep->instance().initialized()) framep->createInstancePrototype();
                framep->captureVarInsert(varp);
                bindNodeToDynScope(varp, framep);
            } else {
                AstAssign* const asgnp = VN_CAST(stmtp, Assign);
                UASSERT_OBJ(asgnp, stmtp,
                            "Invalid node under block item initialization part of fork");
                bindNodeToDynScope(asgnp->lhsp(), framep);
                iterate(asgnp->rhsp());
            }
        }

        for (AstNode* stmtp = nodep->stmtsp(); stmtp; stmtp = stmtp->nextp()) {
            m_afterTimingControl = false;
            iterate(stmtp);
        }
        m_afterTimingControl = oldAfterTimingControl;
        if (nodep->isTimingControl()) m_afterTimingControl = true;
    }
    void visit(AstNodeFTaskRef* nodep) override {
        visit(static_cast<AstNodeExpr*>(nodep));
        // We are before V3Timing, so unfortnately we need to treat any calls as suspending,
        // just to be safe. This might be improved if we could propagate suspendability
        // before doing all the other timing-related stuff.
        m_afterTimingControl = true;
    }
    void visit(AstVar* nodep) override {
        nodep->user1(m_forkDepth);
        ForkDynScopeFrame* const framep = frameOf(m_procp);
        if (!framep) return;  // Cannot be legally referenced from a fork
        bindNodeToDynScope(nodep, framep);
    }
    void visit(AstVarRef* nodep) override {
        ForkDynScopeFrame* const framep = frameOf(nodep->varp());
        if (!framep) return;

        if (needsDynScope(nodep)) {
            if (!framep->instance().initialized()) framep->createInstancePrototype();
            framep->captureVarInsert(nodep->varp());
        }
        bindNodeToDynScope(nodep, framep);
    }
    void visit(AstAssign* nodep) override {
        if (VN_IS(nodep->lhsp(), VarRef) && nodep->lhsp()->isClassHandleValue()) {
            nodep->lhsp()->user2(true);
        }
        visit(static_cast<AstNodeStmt*>(nodep));
    }
    void visit(AstNode* nodep) override {
        if (nodep->isTimingControl()) m_afterTimingControl = true;
        iterateChildren(nodep);
    }

public:
    // CONSTRUCTORS
    explicit DynScopeVisitor(AstNetlist* nodep) {
        // Create Dynamic scope class prototypes and objects
        visit(nodep);

        // Commit changes to AST
        bool typesAdded = false;
        for (auto frameIt : m_frames) {
            ForkDynScopeFrame* frame = frameIt.second;
            if (!frame->instance().initialized()) continue;

            if (!frame->linked()) {
                frame->populateClass();
                frame->linkNodes(m_memberMap);
                typesAdded = true;
            }

            if (AstVarRef* refp = VN_CAST(frameIt.first, VarRef)) {
                if (frame->captured(refp->varp())) replaceWithMemberSel(refp, frame->instance());
            }
        }

        if (typesAdded) v3Global.rootp()->typeTablep()->repairCache();
    }
    ~DynScopeVisitor() override = default;
};

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

    // METHODS

    AstVar* captureRef(AstVarRef* refp) {
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
            m_capturedVarRefsp
                = AstNode::addNext(m_capturedVarRefsp, new AstArg{refp->fileline(), refp->name(),
                                                                  refp->cloneTree(false)});
        }
        return varp;
    }

    AstTask* makeTask(FileLine* fl, AstNode* stmtsp, string name) {
        stmtsp = AstNode::addNext(static_cast<AstNode*>(m_capturedVarsp), stmtsp);
        AstTask* const taskp = new AstTask{fl, name, stmtsp};
        return taskp;
    }

    string generateTaskName(AstNode* fromp, const string& kind) {
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
        VL_RESTORER(m_forkLocalsp);
        m_capturedVarsp = nullptr;
        m_capturedVarRefsp = nullptr;
        m_newProcess = false;
        m_forkLocalsp.clear();

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
        AstStmtExpr* const taskcallp = taskrefp->makeStmt();
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
            if (m_forkLocalsp.count(nodep->varp()) == 0) {
                AstVar* const varp = captureRef(nodep);
                nodep->varp(varp);
            }
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
    explicit ForkVisitor(AstNetlist* nodep) { visit(nodep); }
    ~ForkVisitor() override = default;
};

//######################################################################
// Fork class functions

void V3Fork::makeDynamicScopes(AstNetlist* nodep) {
    UINFO(2, __FUNCTION__ << ": " << endl);
    { DynScopeVisitor{nodep}; }
    V3Global::dumpCheckGlobalTree("fork_dynscope", 0, dumpTreeLevel() >= 3);
}

void V3Fork::makeTasks(AstNetlist* nodep) {
    UINFO(2, __FUNCTION__ << ": " << endl);
    { ForkVisitor{nodep}; }
    V3Global::dumpCheckGlobalTree("fork", 0, dumpTreeLevel() >= 3);
}
