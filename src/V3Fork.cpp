// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Create separate tasks for forked processes that
//              can outlive their parents
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
//
// There are two mechanisms that work together to achieve that. ForkVisitor
// moves bodies of forked processes into new tasks, which results in them getting their
// own scopes. The original statements get replaced with a call to the task which
// passes the required variables by value.
//
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
    // MEMBERS
    AstNodeModule* const m_modp;  // Module to insert the scope into
    AstNode* const m_procp;  // Procedure/block associated with that dynscope
    std::deque<AstVar*> m_captureOrder;  // Variables to be moved into the dynscope
    std::set<AstVar*> m_captures;  // Variables to be moved into the dynscope
    ForkDynScopeInstance m_instance;  // Nodes to be injected into the AST to create the dynscope
    const size_t m_class_id;  // Dynscope class ID
    const size_t m_id;  // Dynscope ID

public:
    ForkDynScopeFrame(AstNodeModule* modp, AstNode* procp, size_t class_id, size_t id)
        : m_modp{modp}
        , m_procp{procp}
        , m_class_id{class_id}
        , m_id{id} {}

    ForkDynScopeInstance& createInstancePrototype() {
        UASSERT_OBJ(!m_instance.initialized(), m_procp, "Dynamic scope already instantiated.");

        m_instance.m_classp
            = new AstClass{m_procp->fileline(), generateDynScopeClassName(), m_modp->libname()};
        UINFO(9, "new dynscope class " << m_instance.m_classp);
        m_instance.m_refDTypep
            = new AstClassRefDType{m_procp->fileline(), m_instance.m_classp, nullptr};
        v3Global.rootp()->typeTablep()->addTypesp(m_instance.m_refDTypep);
        m_instance.m_handlep
            = new AstVar{m_procp->fileline(), VVarType::BLOCKTEMP,
                         generateDynScopeHandleName(m_procp), m_instance.m_refDTypep};
        m_instance.m_handlep->funcLocal(true);
        m_instance.m_handlep->lifetime(VLifetime::AUTOMATIC_EXPLICIT);
        UINFO(9, "new dynscope var " << m_instance.m_handlep);

        return m_instance;
    }

    const ForkDynScopeInstance& instance() const { return m_instance; }
    void captureVarInsert(AstVar* varp) {
        auto r = m_captures.emplace(varp);
        if (r.second) m_captureOrder.push_back(varp);
    }
    bool captured(AstVar* varp) { return m_captures.count(varp) != 0; }
    AstNode* procp() const { return m_procp; }

    void populateClass() {
        UASSERT_OBJ(m_instance.initialized(), m_procp, "No DynScope prototype");

        // Move variables into the class
        for (AstVar* varp : m_captureOrder) {
            if (varp->direction().isAny()) {
                varp = varp->cloneTree(false);
                varp->direction(VDirection::NONE);
            } else {
                varp->unlinkFrBack();
            }
            varp->funcLocal(false);
            varp->varType(VVarType::MEMBER);
            varp->lifetime(VLifetime::AUTOMATIC_EXPLICIT);
            varp->usedLoopIdx(false);  // No longer unrollable
            UINFO(9, "insert DynScope member " << varp);
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

        if (AstFork* const forkp = VN_CAST(m_procp, Fork)) {
            linkNodesOfFork(memberMap, forkp);
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
        for (AstVar* varp : m_captureOrder) {
            if (!varp->direction().isAny()) continue;

            if (varp->direction().isNonOutput()) {
                AstMemberSel* const memberselp = new AstMemberSel{
                    varp->fileline(),
                    new AstVarRef{varp->fileline(), m_instance.m_handlep, VAccess::WRITE},
                    VN_AS(memberMap.findMember(m_instance.m_classp, varp->name()), Var)};
                AstNode* initAsgnp
                    = new AstAssign{varp->fileline(), memberselp,
                                    new AstVarRef{varp->fileline(), varp, VAccess::READ}};
                initsp = AstNode::addNext(initsp, initAsgnp);
            }

            if (AstBasicDType* const dtypep = VN_CAST(varp->dtypep()->skipRefp(), BasicDType)) {
                v3Global.setAssignsEvents();
                if (dtypep->isEvent()) continue;
            }

            if (varp->direction().isWritable()) {
                AstMemberSel* const memberselp = new AstMemberSel{
                    varp->fileline(),
                    new AstVarRef{varp->fileline(), m_instance.m_handlep, VAccess::READ},
                    VN_AS(memberMap.findMember(m_instance.m_classp, varp->name()), Var)};
                AstNode* writebackAsgnp = new AstAssign{
                    varp->fileline(), new AstVarRef{varp->fileline(), varp, VAccess::WRITE},
                    memberselp};
                stmtp = AstNode::addNext(stmtp, writebackAsgnp);
            }
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

    // Wrap Fork in Begin
    void linkNodesOfFork(VMemberMap& memberMap, AstFork* forkp) {
        // Replace the Fork with a Begin
        const std::string name = "_Vwrapped_"  //
                                 + (forkp->name().empty() ? "" : forkp->name() + "_")  //
                                 + std::to_string(m_id);
        AstBegin* const beginp = new AstBegin{forkp->fileline(), name, m_instance.m_handlep, true};
        forkp->replaceWith(beginp);
        // Create the dynamic scope in the Begin
        beginp->addStmtsp(instantiateDynScope(memberMap));
        // Move all sequential statements there
        if (forkp->stmtsp()) beginp->addStmtsp(forkp->stmtsp()->unlinkFrBackWithNext());
        // Put the Fork back at the end of the Begin
        beginp->addStmtsp(forkp);
        m_modp->addStmtsp(m_instance.m_classp);
    }

    string generateDynScopeClassName() { return "__VDynScope_" + cvtToStr(m_class_id); }

    string generateDynScopeHandleName(const AstNode* fromp) {
        return "__VDynScope_" + (!fromp->name().empty() ? (fromp->name() + "_") : "ANON_")
               + cvtToStr(m_id);
    }

    AstNode* getProcStmts() {
        AstNode* stmtsp = nullptr;
        if (!m_procp) return nullptr;
        if (AstBegin* const beginp = VN_CAST(m_procp, Begin)) {
            stmtsp = beginp->stmtsp();
        } else if (AstNodeFTask* const taskp = VN_CAST(m_procp, NodeFTask)) {
            stmtsp = taskp->stmtsp();
        } else {
            m_procp->v3fatalSrc("m_procp is not a begin block or a procedure");
        }
        return stmtsp;
    }
};

//######################################################################
// Dynamic scope visitor, creates classes and objects for dynamic scoping of variables and
// replaces references to variables that need a dynamic scope with references to object's
// members

class DynScopeVisitor final : public VNVisitor {
    // NODE STATE
    // AstVar::user1()          -> int, timing-control fork nesting level of that variable
    // AstVarRef::user2()       -> bool, 1 = Node is a class handle reference. The handle gets
    //                                       modified in the context of this reference.
    // AstAssignDly::user2()    -> bool, true if already visited
    const VNUser1InUse m_inuser1;
    const VNUser2InUse m_inuser2;

    // STATE
    bool m_inFunc = false;  // True if in a function
    AstNodeModule* m_modp = nullptr;  // Module we are currently under
    AstNode* m_procp = nullptr;  // Function/task/block we are currently under
    std::deque<AstNode*> m_frameOrder;  // Ordered list of frames (for determinism)
    std::map<AstNode*, ForkDynScopeFrame*> m_frames;  // Map nodes to related DynScopeFrames
    VMemberMap m_memberMap;  // Class member look-up
    int m_forkDepth = 0;  // Number of asynchronous forks we are currently under
    bool m_afterTimingControl = false;  // A timing control might've be executed in the current
                                        // process
    size_t m_id = 0;  // Unique ID for a frame
    size_t m_class_id = 0;  // Unique ID for a frame class

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
        ForkDynScopeFrame* const framep
            = new ForkDynScopeFrame{m_modp, procp, m_class_id++, m_id++};
        auto r = m_frames.emplace(procp, framep);
        UASSERT_OBJ(r.second, m_modp, "Procedure already contains a frame");
        m_frameOrder.push_back(procp);
        return framep;
    }

    void replaceWithMemberSel(AstVarRef* refp, const ForkDynScopeInstance& dynScope) {
        VNRelinker handle;
        refp->unlinkFrBack(&handle);
        AstMemberSel* const membersel = new AstMemberSel{
            refp->fileline(), new AstVarRef{refp->fileline(), dynScope.m_handlep, refp->access()},
            refp->varp()};
        if (refp->varp()->direction().isAny()) {
            membersel->varp(
                VN_AS(m_memberMap.findMember(dynScope.m_classp, refp->varp()->name()), Var));
        } else {
            membersel->varp(refp->varp());
        }
        handle.relink(membersel);
        VL_DO_DANGLING(pushDeletep(refp), refp);
    }

    static bool hasAsyncFork(AstNode* nodep) {
        return nodep->exists([](AstFork* forkp) { return !forkp->joinType().join(); })
               || nodep->exists([](AstAssignDly*) { return true; });
    }

    void bindNodeToDynScope(AstNode* nodep, ForkDynScopeFrame* framep) {
        auto r = m_frames.emplace(nodep, framep);
        if (r.second) m_frameOrder.push_back(nodep);
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
        m_id = 0;
        iterateChildren(nodep);
    }
    void visit(AstNodeFTask* nodep) override {
        VL_RESTORER(m_procp);
        m_procp = nodep;
        VL_RESTORER(m_inFunc);
        m_inFunc = VN_IS(nodep, Func);
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
        if (nodep->declsp() || nodep->stmtsp()) framep = pushDynScopeFrame(nodep);

        // This can be probably optimized to detect cases in which dynscopes could be avoided
        for (AstNode* declp = nodep->declsp(); declp; declp = declp->nextp()) {
            AstVar* const varp = VN_CAST(declp, Var);
            UASSERT_OBJ(varp, declp, "Invalid node under block item initialization part of fork");
            if (!framep->instance().initialized()) framep->createInstancePrototype();
            framep->captureVarInsert(varp);
            bindNodeToDynScope(varp, framep);
        }
        for (AstNode* stmtp = nodep->stmtsp(); stmtp; stmtp = stmtp->nextp()) {
            AstAssign* const asgnp = VN_CAST(stmtp, Assign);
            UASSERT_OBJ(asgnp, stmtp, "Invalid node under block item initialization part of fork");
            bindNodeToDynScope(asgnp->lhsp(), framep);
            iterate(asgnp->rhsp());
        }

        for (AstNode* stmtp = nodep->forksp(); stmtp; stmtp = stmtp->nextp()) {
            m_afterTimingControl = false;
            iterate(stmtp);
        }
        m_afterTimingControl = oldAfterTimingControl;
        if (nodep->isTimingControl()) m_afterTimingControl = true;
    }
    void visit(AstNodeFTaskRef* nodep) override {
        visit(static_cast<AstNodeExpr*>(nodep));
        // We are before V3Timing, so unfortunately we need to treat any calls as suspending,
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
            bool isEvent = false;
            if (AstBasicDType* const dtypep = VN_CAST(nodep->dtypep()->skipRefp(), BasicDType)) {
                v3Global.setAssignsEvents();
                isEvent = dtypep->isEvent();
            }
            if (!isEvent && m_afterTimingControl && nodep->varp()->isWritable()
                && nodep->access().isWriteOrRW()) {
                // The output variable may not exist after a delay, so we can't just write to it
                if (m_inFunc) {
                    nodep->v3error(
                        "Writing to an "
                        << nodep->varp()->verilogKwd()
                        << " variable of a function after a timing control is not allowed");
                } else {
                    nodep->v3warn(E_UNSUPPORTED, "Unsupported: Writing to a captured "
                                                     << nodep->varp()->verilogKwd()
                                                     << " variable in a "
                                                     << (VN_IS(nodep->backp(), AssignDly)
                                                             ? "non-blocking assignment"
                                                             : "fork")
                                                     << " after a timing control");
                }
            }
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
    void visit(AstAssignDly* nodep) override {
        if (m_procp && !nodep->user2()  // Unhandled AssignDly in function/task
            && nodep->lhsp()->exists(  // And writes to a local variable
                [](AstVarRef* refp) {
                    return refp->access().isWriteOrRW() && refp->varp()->isFuncLocal();
                })) {
            nodep->user2(true);
            // Put it in a fork to prevent lifetime issues with the local
            FileLine* const flp = nodep->fileline();
            AstFork* const forkp = new AstFork{flp, VJoinType::JOIN_NONE};
            nodep->replaceWith(forkp);
            forkp->addForksp(new AstBegin{flp, "", nodep, false});
            UINFO(9, "assign new fork " << forkp);
        } else {
            visit(static_cast<AstNodeStmt*>(nodep));
        }
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
        for (auto orderp : m_frameOrder) {
            UINFO(9, "Frame commit " << orderp);
            auto frameIt = m_frames.find(orderp);
            UASSERT_OBJ(frameIt != m_frames.end(), orderp, "m_frames didn't contain m_frameOrder");
            ForkDynScopeFrame* framep = frameIt->second;
            if (!framep->instance().initialized()) continue;
            if (!framep->linked()) {
                framep->populateClass();
                framep->linkNodes(m_memberMap);
                typesAdded = true;
            }
            if (AstVarRef* const refp = VN_CAST(frameIt->first, VarRef)) {
                if (framep->captured(refp->varp())) replaceWithMemberSel(refp, framep->instance());
            }
        }

        if (typesAdded) v3Global.rootp()->typeTablep()->repairCache();
    }
    ~DynScopeVisitor() override {
        std::set<ForkDynScopeFrame*> frames;
        for (auto node_frame : m_frames) frames.insert(node_frame.second);
        for (auto* framep : frames) delete framep;
    }
};

//######################################################################
// Fork visitor, transforms asynchronous blocks into separate tasks

class ForkVisitor final : public VNVisitor {
    // NODE STATE
    // AstVarRef::user2()       -> bool, 1 = Node is a class handle reference. The handle gets
    //                                       modified in the context of this reference.
    const VNUser2InUse m_inuser2;

    // STATE - for current AstNodeModule
    AstNodeModule* m_modp = nullptr;  // Class/module we are currently under
    AstTask* m_tasksp = nullptr;  // Tasks exrtracted under current module
    size_t m_nForkTasks = 0;  // Sequence numbers for task names

    // STATE - for current AstFork item
    bool m_inFork = false;  // Traversal in an async fork
    std::set<AstVar*> m_forkLocalsp;  // Variables local to a given fork
    AstVar* m_capturedVarsp = nullptr;  // Local copies of captured variables
    AstArg* m_capturedArgsp = nullptr;  // References to captured variables (as args)

    // STATE - across all visitors
    AstClass* m_processClassp = nullptr;
    AstFunc* m_statusMethodp = nullptr;
    VMemberMap m_memberMap;  // for lookup of process class methods

    // METHODS
    AstVar* capture(AstVarRef* refp) {
        AstVar* varp = nullptr;
        for (varp = m_capturedVarsp; varp; varp = VN_AS(varp->nextp(), Var)) {
            if (varp->name() == refp->name()) break;
        }
        if (varp) return varp;

        // Create a local copy to capture
        FileLine* const flp = refp->fileline();
        varp = new AstVar{flp, VVarType::BLOCKTEMP, refp->name(), refp->dtypep()};
        varp->direction(VDirection::INPUT);
        varp->funcLocal(true);
        varp->lifetime(VLifetime::AUTOMATIC_EXPLICIT);
        m_capturedVarsp = AstNode::addNext(m_capturedVarsp, varp);
        // Pass variable as argument
        AstArg* const argp = new AstArg{flp, refp->name(), refp->cloneTree(false)};
        m_capturedArgsp = AstNode::addNext(m_capturedArgsp, argp);
        return varp;
    }

    // Wrap body of the given Begin (an AstFork branch), in an AstTask, and
    // replace body with a call to that task. Returns true iff wrapped.
    bool taskify(AstBegin* beginp) {
        // Visit statement to gather variables (And recursively process)
        VL_RESTORER(m_forkLocalsp);
        VL_RESTORER(m_capturedVarsp);
        VL_RESTORER(m_capturedArgsp);
        m_forkLocalsp.clear();
        m_capturedVarsp = nullptr;
        m_capturedArgsp = nullptr;
        iterate(beginp);

        // No need to do it if no variabels are captured
        if (m_forkLocalsp.empty() && !m_capturedVarsp && !v3Global.opt.fTaskifyAll()) return false;

        // Create task holding the statement and repalce statement with call to that task
        FileLine* const flp = beginp->fileline();
        const std::string name = "__VforkTask_" + std::to_string(m_nForkTasks++);
        AstTask* const taskp = new AstTask{flp, name, m_capturedVarsp};
        m_tasksp = AstNode::addNext(m_tasksp, taskp);
        if (beginp->declsp()) taskp->addStmtsp(beginp->declsp()->unlinkFrBackWithNext());
        if (beginp->stmtsp()) taskp->addStmtsp(beginp->stmtsp()->unlinkFrBackWithNext());
        AstTaskRef* const callp = new AstTaskRef{flp, taskp, m_capturedArgsp};
        beginp->addStmtsp(callp->makeStmt());

        // Variables were moved under the task, so make sure they are marked as funcLocal
        for (AstVar* const localp : m_forkLocalsp) localp->funcLocal(true);

        // We did wrap the body
        return true;
    }

    AstClass* getProcessClassp() {
        if (!m_processClassp)
            m_processClassp
                = VN_AS(m_memberMap.findMember(v3Global.rootp()->stdPackagep(), "process"), Class);
        return m_processClassp;
    }

    AstFunc* getStatusmethodp() {
        if (m_statusMethodp == nullptr)
            m_statusMethodp = VN_AS(m_memberMap.findMember(getProcessClassp(), "status"), Func);
        return m_statusMethodp;
    }

    // VISITORS
    void visit(AstNodeModule* nodep) override {
        VL_RESTORER(m_modp);
        VL_RESTORER(m_nForkTasks);
        VL_RESTORER(m_tasksp);
        m_modp = nodep;
        m_nForkTasks = 0;
        m_tasksp = nullptr;
        iterateChildren(nodep);
        // Add extracted tasks, they don't need to be visited again
        if (m_tasksp) nodep->addStmtsp(m_tasksp);
    }

    void visit(AstFork* nodep) override {
        if (nodep->joinType().join()) {
            iterateChildren(nodep);
            return;
        }

        // IEEE 1800-2023 9.3.2: In all cases, processes spawned by a fork-join block shall not
        // start executing until the parent process is blocked or terminates.
        // Because join and join_any block the parent process, it is only needed when join_none
        // is used.
        if (nodep->joinType().joinNone()) {
            UINFO(9, "Visiting fork..join_none " << nodep);
            FileLine* fl = nodep->fileline();
            AstVarRef* forkParentrefp = nodep->parentProcessp();

            if (forkParentrefp) {  // Forks created by V3Fork will not have this
                for (AstBegin *itemp = nodep->forksp(), *nextp; itemp; itemp = nextp) {
                    nextp = VN_AS(itemp->nextp(), Begin);
                    if (!itemp->stmtsp()) continue;
                    AstMethodCall* const statusCallp = new AstMethodCall{
                        fl, forkParentrefp->cloneTree(false), "status", nullptr};
                    statusCallp->taskp(getStatusmethodp());
                    statusCallp->classOrPackagep(getProcessClassp());
                    statusCallp->dtypep(getStatusmethodp()->dtypep());
                    AstNeq* const condp
                        = new AstNeq{fl, statusCallp,
                                     new AstConst{fl, AstConst::WidthedValue{},
                                                  getStatusmethodp()->dtypep()->width(), 1}};
                    AstWait* const waitStmt = new AstWait{fl, condp, nullptr};
                    itemp->stmtsp()->addHereThisAsNext(waitStmt);
                }
            }
        }

        iterateAndNextNull(nodep->declsp());
        iterateAndNextNull(nodep->stmtsp());
        std::vector<AstBegin*> wrappedp;
        {
            VL_RESTORER(m_inFork);
            m_inFork = true;
            for (AstBegin* itemp = nodep->forksp(); itemp; itemp = VN_AS(itemp->nextp(), Begin)) {
                if (taskify(itemp)) wrappedp.push_back(itemp);
            }
        }
        // Analyze replacements in context of enclosing fork
        for (AstBegin* const beginp : wrappedp) iterateAndNextNull(beginp);
    }
    void visit(AstVar* nodep) override {
        if (m_inFork) m_forkLocalsp.insert(nodep);
    }
    void visit(AstVarRef* nodep) override {
        if (!m_inFork) return;
        AstVar* const varp = nodep->varp();
        // Not sure why this is OK ...
        if (!varp->isFuncLocal() && varp->isClassMember()) return;
        // We must know the lifetime at this point, otherwise we can't decide if need to capture
        UASSERT_OBJ(!varp->lifetime().isNone(), nodep, "Variable's lifetime is unknown");
        // Static variables are fine, they are always availabel
        if (varp->lifetime().isStatic()) return;
        // If this ref is to a variable that will move into the task, then nothing to do
        if (m_forkLocalsp.count(varp)) return;

        if (nodep->access().isWriteOrRW() && (!nodep->isClassHandleValue() || nodep->user2())) {
            nodep->v3warn(
                E_LIFETIME,
                "Invalid reference: Process might outlive variable "
                    << varp->prettyNameQ() << ".\n"
                    << varp->warnMore()
                    << "... Suggest use it as read-only to initialize a local copy at the "
                       "beginning of the process, or declare it as static. It is also "
                       "possible to refer by reference to objects and their members.");
            return;
        }

        // Capture variable and redirect reference to the capturede copy
        nodep->varp(capture(nodep));
    }
    void visit(AstAssign* nodep) override {
        if (VN_IS(nodep->lhsp(), VarRef) && nodep->lhsp()->isClassHandleValue()) {
            nodep->lhsp()->user2(true);
        }
        iterateChildren(nodep);
    }
    void visit(AstThisRef* nodep) override {}
    void visit(AstNode* nodep) override { iterateChildren(nodep); }

public:
    // CONSTRUCTORS
    explicit ForkVisitor(AstNetlist* nodep) { visit(nodep); }
    ~ForkVisitor() override = default;
};

//######################################################################
// Fork class functions

void V3Fork::makeDynamicScopes(AstNetlist* nodep) {
    UINFO(2, __FUNCTION__ << ":");
    { DynScopeVisitor{nodep}; }
    V3Global::dumpCheckGlobalTree("fork_dynscope", 0, dumpTreeEitherLevel() >= 3);
}

void V3Fork::makeTasks(AstNetlist* nodep) {
    UINFO(2, __FUNCTION__ << ":");
    { ForkVisitor{nodep}; }
    V3Global::dumpCheckGlobalTree("fork_tasks", 0, dumpTreeEitherLevel() >= 3);
}
