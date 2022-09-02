// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Prepare AST for timing features
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2022 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
// TimingVisitor transformations:
// - for each intra-assignment timing control:
//     - if it's a continuous assignment, transform it into an always
//     - introduce an intermediate variable
//     - write the original RHS to the intermediate variable before the timing control
//     - write the intermediate variable to the original LHS after the timing control
// - for each delay:
//     - scale it according to the module's timescale
//     - replace it with a CAwait statement waiting on the global delay scheduler (with the
//       specified delay value)
//       - if there is no global delay scheduler (see verilated_timing.{h,cpp}), create it
// - for each event control:
//     - if there is no corresponding trigger scheduler (see verilated_timing.{h,cpp}), create it
//     - replace with a CAwait statement waiting on the corresponding trigger scheduler
// - for each wait(cond) statement:
//     - replace it with a loop like: while (!cond) @(<vars from cond>)
// - for each fork:
//     - put each statement in a begin if it isn't in one already
//     - if it's not a fork..join_none:
//         - create a join sync variable
//         - create statements that sync the main process with its children
// - for each process or C++ function, if it has CAwait statements, mark it as suspendable
//     - if we mark a virtual function as suspendable, mark all overriding and overridden functions
//     as suspendable, as well as calling processes
//
// See the internals documentation docs/internals.rst for more details.
//
//*************************************************************************

#include "config_build.h"
#include "verilatedos.h"

#include "V3Timing.h"

#include "V3Ast.h"
#include "V3Const.h"
#include "V3EmitV.h"
#include "V3Graph.h"
#include "V3SenExprBuilder.h"
#include "V3SenTree.h"
#include "V3UniqueNames.h"

VL_DEFINE_DEBUG_FUNCTIONS;

// ######################################################################
//  Transform nodes affected by timing

class TimingVisitor final : public VNVisitor {
private:
    // TYPES
    // Vertex of a dependency graph of suspendable nodes, e.g. if a node (process or task) is
    // suspendable, all its dependents should also be suspendable
    class DependencyVertex final : public V3GraphVertex {
        AstNode* const m_nodep;  // AST node represented by this graph vertex
        // ACCESSORS
        string name() const override {
            return cvtToHex(nodep()) + ' ' + nodep()->prettyTypeName();
        }
        FileLine* fileline() const override { return nodep()->fileline(); }
        string dotColor() const override { return nodep()->user2() ? "red" : "black"; }

    public:
        // CONSTRUCTORS
        DependencyVertex(V3Graph* graphp, AstNode* nodep)
            : V3GraphVertex{graphp}
            , m_nodep{nodep} {}
        ~DependencyVertex() override = default;

        // ACCESSORS
        virtual AstNode* nodep() const { return m_nodep; }
    };

    // NODE STATE
    //  AstNode::user1()                         -> bool.         Set true if the node has been
    //                                                            processed.
    //  AstSenTree::user1()                      -> AstVarScope*. Trigger scheduler assigned
    //                                                            to this sentree
    //  Ast{NodeProcedure,CFunc,Begin}::user2()  -> bool.         Set true if process/task is
    //                                                            suspendable
    //  AstSenTree::user2()                      -> AstText*.     Debug info passed to the
    //                                                            timing schedulers
    //  Ast{NodeProcedure,CFunc,Begin}::user3()  -> DependencyVertex*.  Vertex in m_depGraph
    const VNUser1InUse m_user1InUse;
    const VNUser2InUse m_user2InUse;
    const VNUser3InUse m_user3InUse;

    // STATE
    // Current context
    AstNetlist* const m_netlistp;  // Root node
    AstScope* const m_scopeTopp = m_netlistp->topScopep()->scopep();  // Scope at the top
    AstClass* m_classp = nullptr;  // Current class
    AstScope* m_scopep = nullptr;  // Current scope
    AstActive* m_activep = nullptr;  // Current active
    AstNode* m_procp = nullptr;  // NodeProcedure/CFunc/Fork we're under
    double m_timescaleFactor = 1.0;  // Factor to scale delays by

    // Unique names
    V3UniqueNames m_contAssignVarNames{"__VassignWtmp"};  // Names for temp AssignW vars
    V3UniqueNames m_intraValueNames{"__Vintraval"};  // Intra assign delay value var names
    V3UniqueNames m_intraIndexNames{"__Vintraidx"};  // Intra assign delay index var names
    V3UniqueNames m_intraLsbNames{"__Vintralsb"};  // Intra assign delay LSB var names
    V3UniqueNames m_forkNames{"__Vfork"};  // Fork name generator
    V3UniqueNames m_trigSchedNames{"__VtrigSched"};  // Trigger scheduler name generator
    V3UniqueNames m_dynTrigNames{"__VdynTrigger"};  // Dynamic trigger name generator

    // DTypes
    AstBasicDType* m_forkDtp = nullptr;  // Fork variable type
    AstBasicDType* m_trigSchedDtp = nullptr;  // Trigger scheduler type

    // Timing-related globals
    AstVarScope* m_delaySchedp = nullptr;  // Global delay scheduler
    AstVarScope* m_dynamicSchedp = nullptr;  // Global dynamic trigger scheduler
    AstSenTree* m_delaySensesp = nullptr;  // Domain to trigger if a delayed coroutine is resumed
    AstSenTree* m_dynamicSensesp = nullptr;  // Domain to trigger if a dynamic trigger is set

    // Other
    V3Graph m_depGraph;  // Dependency graph where a node is a dependency of another if it being
                         // suspendable makes the other node suspendable
    SenTreeFinder m_finder{m_netlistp};  // Sentree finder and uniquifier

    // METHODS
    // Get or create the dependency vertex for the given node
    DependencyVertex* getDependencyVertex(AstNode* const nodep) {
        if (!nodep->user3p()) nodep->user3p(new DependencyVertex{&m_depGraph, nodep});
        return nodep->user3u().to<DependencyVertex*>();
    }
    // Find net delay on the LHS of an assignment
    AstDelay* getLhsNetDelay(AstNodeAssign* nodep) const {
        bool foundWrite = false;
        AstDelay* delayp = nullptr;
        nodep->lhsp()->foreach([&](const AstNodeVarRef* const refp) {
            if (!refp->access().isWriteOrRW()) return;
            UASSERT_OBJ(!foundWrite, nodep, "Should only be one variable written to on the LHS");
            foundWrite = true;
            if (refp->varp()->delayp()) {
                delayp = refp->varp()->delayp();
                delayp->unlinkFrBack();
            }
        });
        return delayp;
    }
    // Transform an assignment with an intra timing control into a timing control with the
    // assignment under it
    AstNodeStmt* factorOutTimingControl(AstNodeAssign* nodep) const {
        AstNodeStmt* stmtp = nodep;
        AstDelay* delayp = getLhsNetDelay(nodep);
        FileLine* const flp = nodep->fileline();
        AstNode* const controlp = nodep->timingControlp();
        if (controlp) {
            controlp->unlinkFrBack();
            if (auto* const assignDelayp = VN_CAST(controlp, Delay)) {
                if (delayp) {
                    delayp->lhsp(new AstAdd{flp, delayp->lhsp()->unlinkFrBack(),
                                            assignDelayp->lhsp()->unlinkFrBack()});
                    VL_DO_DANGLING(assignDelayp->deleteTree(), nodep);
                } else {
                    delayp = assignDelayp;
                }
            }
        }
        if (delayp) {
            stmtp->replaceWith(delayp);
            delayp->addStmtsp(stmtp);
            stmtp = delayp;
        }
        if (auto* const sensesp = VN_CAST(controlp, SenTree)) {
            auto* const eventControlp = new AstEventControl{flp, sensesp, nullptr};
            stmtp->replaceWith(eventControlp);
            eventControlp->addStmtsp(stmtp);
            stmtp = eventControlp;
        }
        return stmtp == nodep ? nullptr : stmtp;
    }
    // Calculate the factor to scale delays by
    double calculateTimescaleFactor(VTimescale timeunit) const {
        int scalePowerOfTen = timeunit.powerOfTen() - m_netlistp->timeprecision().powerOfTen();
        return std::pow(10.0, scalePowerOfTen);
    }
    // Construct SenItems from VarRefs in an expression
    AstSenItem* varRefpsToSenItemsp(AstNode* const nodep) const {
        AstNode* senItemsp = nullptr;
        const VNUser4InUse user4InUse;
        nodep->foreach([&](AstNodeVarRef* refp) {
            if (refp->access().isWriteOnly()) return;
            AstVarScope* const vscp = refp->varScopep();
            if (vscp->user4SetOnce()) return;
            const bool isEvent = vscp->dtypep() && vscp->dtypep()->basicp()
                                 && vscp->dtypep()->basicp()->isEvent();
            const auto edgeType = isEvent ? VEdgeType::ET_EVENT : VEdgeType::ET_CHANGED;
            senItemsp = AstNode::addNext(
                senItemsp, new AstSenItem{refp->fileline(), edgeType,
                                          new AstVarRef{refp->fileline(), vscp, VAccess::READ}});
        });
        return VN_AS(senItemsp, SenItem);
    }
    // Creates the global delay scheduler variable
    AstVarScope* getCreateDelayScheduler() {
        if (m_delaySchedp) return m_delaySchedp;
        auto* const dlySchedDtp = new AstBasicDType{
            m_scopeTopp->fileline(), VBasicDTypeKwd::DELAY_SCHEDULER, VSigning::UNSIGNED};
        m_netlistp->typeTablep()->addTypesp(dlySchedDtp);
        m_delaySchedp = m_scopeTopp->createTemp("__VdlySched", dlySchedDtp);
        // Delay scheduler has to be accessible from top
        m_delaySchedp->varp()->sigPublic(true);
        m_netlistp->delaySchedulerp(m_delaySchedp->varp());
        return m_delaySchedp;
    }
    // Creates the delay sentree
    AstSenTree* getCreateDelaySenTree() {
        if (m_delaySensesp) return m_delaySensesp;
        FileLine* const flp = m_scopeTopp->fileline();
        auto* const awaitingCurrentTimep
            = new AstCMethodHard{flp, new AstVarRef{flp, getCreateDelayScheduler(), VAccess::READ},
                                 "awaitingCurrentTime"};
        awaitingCurrentTimep->dtypeSetBit();
        m_delaySensesp
            = new AstSenTree{flp, new AstSenItem{flp, VEdgeType::ET_TRUE, awaitingCurrentTimep}};
        m_netlistp->topScopep()->addSenTreesp(m_delaySensesp);
        return m_delaySensesp;
    }
    // Creates the global dynamic trigger scheduler variable
    AstVarScope* getCreateDynamicTriggerScheduler() {
        if (m_dynamicSchedp) return m_dynamicSchedp;
        auto* const dynSchedDtp
            = new AstBasicDType{m_scopeTopp->fileline(), VBasicDTypeKwd::DYNAMIC_TRIGGER_SCHEDULER,
                                VSigning::UNSIGNED};
        m_netlistp->typeTablep()->addTypesp(dynSchedDtp);
        m_dynamicSchedp = m_scopeTopp->createTemp("__VdynSched", dynSchedDtp);
        return m_dynamicSchedp;
    }
    // Creates the dynamic trigger sentree
    AstSenTree* getCreateDynamicTriggerSenTree() {
        if (m_dynamicSensesp) return m_dynamicSensesp;
        FileLine* const flp = m_scopeTopp->fileline();
        auto* const awaitingCurrentTimep = new AstCMethodHard{
            flp, new AstVarRef{flp, getCreateDynamicTriggerScheduler(), VAccess::READ},
            "evaluate"};
        awaitingCurrentTimep->dtypeSetBit();
        m_dynamicSensesp
            = new AstSenTree{flp, new AstSenItem{flp, VEdgeType::ET_TRUE, awaitingCurrentTimep}};
        m_netlistp->topScopep()->addSenTreesp(m_dynamicSensesp);
        return m_dynamicSensesp;
    }
    // Returns true if we are under a class or the given tree has any references to locals. These
    // are cases where static, globally-evaluated triggers are not suitable.
    bool needDynamicTrigger(AstNode* const nodep) const {
        return m_classp || nodep->exists([](const AstNodeVarRef* const refp) {
            return refp->varp()->isFuncLocal();
        });
    }
    // Returns true if the given trigger expression needs a destructive post update after trigger
    // evaluation. Currently this only applies to named events.
    bool destructivePostUpdate(AstNode* const exprp) const {
        return exprp->exists([](const AstNodeVarRef* const refp) {
            AstBasicDType* const dtypep = refp->dtypep()->basicp();
            return dtypep && dtypep->isEvent();
        });
    }
    // Creates a trigger scheduler variable
    AstVarScope* getCreateTriggerSchedulerp(AstSenTree* const sensesp) {
        if (!sensesp->user1p()) {
            if (!m_trigSchedDtp) {
                m_trigSchedDtp
                    = new AstBasicDType{m_scopeTopp->fileline(), VBasicDTypeKwd::TRIGGER_SCHEDULER,
                                        VSigning::UNSIGNED};
                m_netlistp->typeTablep()->addTypesp(m_trigSchedDtp);
            }
            AstVarScope* const trigSchedp
                = m_scopeTopp->createTemp(m_trigSchedNames.get(sensesp), m_trigSchedDtp);
            sensesp->user1p(trigSchedp);
        }
        return VN_AS(sensesp->user1p(), VarScope);
    }
    // Creates a string describing the sentree
    AstText* createEventDescription(AstSenTree* const sensesp) const {
        if (!sensesp->user2p()) {
            std::stringstream ss;
            ss << '"';
            V3EmitV::verilogForTree(sensesp, ss);
            ss << '"';
            auto* const commentp = new AstText{sensesp->fileline(), ss.str()};
            sensesp->user2p(commentp);
            return commentp;
        }
        return VN_AS(sensesp->user2p(), Text)->cloneTree(false);
    }
    // Adds debug info to a hardcoded method call
    void addDebugInfo(AstCMethodHard* const methodp) const {
        if (v3Global.opt.protectIds()) return;
        FileLine* const flp = methodp->fileline();
        methodp->addPinsp(new AstText{flp, '"' + flp->filename() + '"'});
        methodp->addPinsp(new AstText{flp, cvtToStr(flp->lineno())});
    }
    // Adds debug info to a trigSched.trigger() call
    void addEventDebugInfo(AstCMethodHard* const methodp, AstSenTree* const sensesp) const {
        if (v3Global.opt.protectIds()) return;
        methodp->addPinsp(createEventDescription(sensesp));
        addDebugInfo(methodp);
    }
    // Creates the fork handle type and returns it
    AstBasicDType* getCreateForkSyncDTypep() {
        if (m_forkDtp) return m_forkDtp;
        m_forkDtp = new AstBasicDType{m_scopeTopp->fileline(), VBasicDTypeKwd::FORK_SYNC,
                                      VSigning::UNSIGNED};
        m_netlistp->typeTablep()->addTypesp(m_forkDtp);
        return m_forkDtp;
    }
    // Create a temp variable and optionally put it before the specified node (mark local if so)
    AstVarScope* createTemp(FileLine* const flp, const std::string& name,
                            AstNodeDType* const dtypep, AstNode* const insertBeforep = nullptr) {
        AstVar* varp;
        if (insertBeforep) {
            varp = new AstVar{flp, VVarType::BLOCKTEMP, name, dtypep};
            varp->funcLocal(true);
            insertBeforep->addHereThisAsNext(varp);
        } else {
            varp = new AstVar{flp, VVarType::MODULETEMP, name, dtypep};
            m_scopep->modp()->addStmtsp(varp);
        }
        AstVarScope* vscp = new AstVarScope{flp, m_scopep, varp};
        m_scopep->addVarsp(vscp);
        return vscp;
    }
    // Add a done() call on the fork sync
    void addForkDone(AstBegin* const beginp, AstVarScope* const forkVscp) const {
        FileLine* const flp = beginp->fileline();
        auto* const donep = new AstCMethodHard{
            beginp->fileline(), new AstVarRef{flp, forkVscp, VAccess::WRITE}, "done"};
        donep->dtypeSetVoid();
        donep->statement(true);
        addDebugInfo(donep);
        beginp->addStmtsp(donep);
    }
    // Handle the 'join' part of a fork..join
    void makeForkJoin(AstFork* const forkp) {
        // Create a fork sync var
        FileLine* const flp = forkp->fileline();
        // If we're in a function, insert the sync var directly before the fork
        AstNode* const insertBeforep = VN_IS(m_procp, CFunc) ? forkp : nullptr;
        AstVarScope* forkVscp
            = createTemp(flp, forkp->name() + "__sync", getCreateForkSyncDTypep(), insertBeforep);
        unsigned joinCount = 0;  // Needed for join counter
        // Add a <fork sync>.done() to each begin
        for (AstNode* beginp = forkp->stmtsp(); beginp; beginp = beginp->nextp()) {
            addForkDone(VN_AS(beginp, Begin), forkVscp);
            joinCount++;
        }
        if (forkp->joinType().joinAny()) joinCount = 1;
        // Set the join counter
        auto* const initp = new AstCMethodHard{flp, new AstVarRef{flp, forkVscp, VAccess::WRITE},
                                               "init", new AstConst{flp, joinCount}};
        initp->dtypeSetVoid();
        initp->statement(true);
        forkp->addHereThisAsNext(initp);
        // Await the join at the end
        auto* const joinp
            = new AstCMethodHard{flp, new AstVarRef{flp, forkVscp, VAccess::WRITE}, "join"};
        joinp->dtypeSetVoid();
        addDebugInfo(joinp);
        auto* const awaitp = new AstCAwait{flp, joinp};
        awaitp->statement(true);
        forkp->addNextHere(awaitp);
    }

    // VISITORS
    void visit(AstNodeModule* nodep) override {
        UASSERT(!m_classp, "Module or class under class");
        VL_RESTORER(m_classp);
        m_classp = VN_CAST(nodep, Class);
        VL_RESTORER(m_timescaleFactor);
        m_timescaleFactor = calculateTimescaleFactor(nodep->timeunit());
        iterateChildren(nodep);
    }
    void visit(AstScope* nodep) override {
        VL_RESTORER(m_scopep);
        m_scopep = nodep;
        iterateChildren(nodep);
    }
    void visit(AstActive* nodep) override {
        m_activep = nodep;
        iterateChildren(nodep);
        m_activep = nullptr;
    }
    void visit(AstNodeProcedure* nodep) override {
        VL_RESTORER(m_procp);
        m_procp = nodep;
        iterateChildren(nodep);
        if (nodep->user2()) nodep->setSuspendable();
    }
    void visit(AstAlways* nodep) override {
        visit(static_cast<AstNodeProcedure*>(nodep));
        if (nodep->isSuspendable() && !nodep->user1SetOnce()) {
            FileLine* const flp = nodep->fileline();
            AstSenTree* const sensesp = m_activep->sensesp();
            if (sensesp->hasClocked()) {
                AstNode* bodysp = nodep->stmtsp()->unlinkFrBackWithNext();
                auto* const controlp = new AstEventControl{flp, sensesp->cloneTree(false), bodysp};
                nodep->addStmtsp(controlp);
                iterate(controlp);
            }
            // Note: The 'while (true)' outer loop will be added in V3Sched
            auto* const activep = new AstActive{
                flp, "", new AstSenTree{flp, new AstSenItem{flp, AstSenItem::Initial{}}}};
            activep->sensesStorep(activep->sensesp());
            activep->addStmtsp(nodep->unlinkFrBack());
            m_activep->addNextHere(activep);
        }
    }
    void visit(AstCFunc* nodep) override {
        VL_RESTORER(m_procp);
        m_procp = nodep;
        iterateChildren(nodep);
        DependencyVertex* const vxp = getDependencyVertex(nodep);
        if (m_classp && nodep->isVirtual()
            && !nodep->user1SetOnce()) {  // If virtual (only visit once)
            // Go over overridden functions
            m_classp->repairCache();
            for (auto* cextp = m_classp->extendsp(); cextp;
                 cextp = VN_AS(cextp->nextp(), ClassExtends)) {
                if (auto* const overriddenp
                    = VN_CAST(cextp->classp()->findMember(nodep->name()), CFunc)) {
                    if (overriddenp->user2()) {  // If suspendable
                        if (!nodep->user2()) {
                            // It should be a coroutine but it has no awaits. Add a co_return at
                            // the end (either that or a co_await is required in a coroutine)
                            nodep->addStmtsp(new AstCStmt{nodep->fileline(), "co_return;\n"});
                        }
                        nodep->user2(true);
                        // If it's suspendable already, no need to add it as our dependency or
                        // self to its dependencies
                    } else {
                        DependencyVertex* const overriddenVxp = getDependencyVertex(overriddenp);
                        new V3GraphEdge{&m_depGraph, vxp, overriddenVxp, 1};
                        new V3GraphEdge{&m_depGraph, overriddenVxp, vxp, 1};
                    }
                }
            }
        }
        if (nodep->user2() && !nodep->isCoroutine()) {  // If first marked as suspendable
            nodep->rtnType("VlCoroutine");
            // If in a class, create a shared pointer to 'this'
            if (m_classp) nodep->addInitsp(new AstCStmt{nodep->fileline(), "VL_KEEP_THIS;\n"});
            // Revisit dependent nodes if needed
            for (V3GraphEdge* edgep = vxp->inBeginp(); edgep; edgep = edgep->inNextp()) {
                auto* const depVxp = static_cast<DependencyVertex*>(edgep->fromp());
                AstNode* const depp = depVxp->nodep();
                if (!depp->user2()) {  // If dependent not suspendable
                    depp->user2(true);
                    if (auto* const funcp = VN_CAST(depp, CFunc)) {
                        // It's a coroutine but has no awaits (a class method that overrides/is
                        // overridden by a suspendable, but doesn't have any awaits itself). Add a
                        // co_return at the end (either that or a co_await is required in a
                        // coroutine)
                        funcp->addStmtsp(new AstCStmt{funcp->fileline(), "co_return;\n"});
                    }
                }
                iterate(depp);
            }
        }
    }
    void visit(AstNodeCCall* nodep) override {
        if (nodep->funcp()->user2()) {  // If suspendable
            VNRelinker relinker;
            nodep->unlinkFrBack(&relinker);
            relinker.relink(new AstCAwait{nodep->fileline(), nodep});
        } else {
            // Add our process/func as the CFunc's dependency as we might have to put an await here
            DependencyVertex* const procVxp = getDependencyVertex(m_procp);
            DependencyVertex* const funcVxp = getDependencyVertex(nodep->funcp());
            new V3GraphEdge{&m_depGraph, procVxp, funcVxp, 1};
        }
        iterateChildren(nodep);
    }
    void visit(AstCAwait* nodep) override {
        v3Global.setUsesTiming();
        m_procp->user2(true);
    }
    void visit(AstDelay* nodep) override {
        FileLine* const flp = nodep->fileline();
        AstNode* valuep = V3Const::constifyEdit(nodep->lhsp()->unlinkFrBack());
        auto* const constp = VN_CAST(valuep, Const);
        if (constp && constp->isZero()) {
            nodep->v3warn(ZERODLY, "Unsupported: #0 delays do not schedule process resumption in "
                                   "the Inactive region");
        } else {
            // Scale the delay
            if (valuep->dtypep()->isDouble()) {
                valuep = new AstRToIRoundS{
                    flp,
                    new AstMulD{flp, valuep,
                                new AstConst{flp, AstConst::RealDouble{}, m_timescaleFactor}}};
            } else {
                valuep = new AstMul{flp, valuep,
                                    new AstConst{flp, AstConst::Unsized64(),
                                                 static_cast<uint64_t>(m_timescaleFactor)}};
            }
        }
        // Replace self with a 'co_await dlySched.delay(<valuep>)'
        auto* const delayMethodp = new AstCMethodHard{
            flp, new AstVarRef{flp, getCreateDelayScheduler(), VAccess::WRITE}, "delay", valuep};
        delayMethodp->dtypeSetVoid();
        addDebugInfo(delayMethodp);
        // Create the co_await
        auto* const awaitp = new AstCAwait{flp, delayMethodp, getCreateDelaySenTree()};
        awaitp->statement(true);
        // Relink child statements after the co_await
        if (nodep->stmtsp()) {
            AstNode::addNext<AstNode, AstNode>(awaitp, nodep->stmtsp()->unlinkFrBackWithNext());
        }
        nodep->replaceWith(awaitp);
        VL_DO_DANGLING(nodep->deleteTree(), nodep);
    }
    void visit(AstEventControl* nodep) override {
        // Do not allow waiting on local named events, as they get enqueued for clearing, but can
        // go out of scope before that happens
        if (nodep->sensesp()->exists([](const AstNodeVarRef* refp) {
                AstBasicDType* const dtypep = refp->dtypep()->skipRefp()->basicp();
                return dtypep && dtypep->isEvent() && refp->varp()->isFuncLocal();
            })) {
            nodep->v3warn(E_UNSUPPORTED, "Unsupported: waiting on local event variables");
        }
        FileLine* const flp = nodep->fileline();
        // Relink child statements after the event control
        if (nodep->stmtsp()) nodep->addNextHere(nodep->stmtsp()->unlinkFrBackWithNext());
        if (needDynamicTrigger(nodep->sensesp())) {
            // Create the trigger variable and init it with 0
            AstVarScope* const trigvscp
                = createTemp(flp, m_dynTrigNames.get(nodep), nodep->findBitDType(), nodep);
            auto* const initp = new AstAssign{flp, new AstVarRef{flp, trigvscp, VAccess::WRITE},
                                              new AstConst{flp, AstConst::BitFalse{}}};
            nodep->addHereThisAsNext(initp);
            // Await the eval step with the dynamic trigger scheduler. First, create the method
            // call
            auto* const evalMethodp = new AstCMethodHard{
                flp, new AstVarRef{flp, getCreateDynamicTriggerScheduler(), VAccess::WRITE},
                "evaluation"};
            evalMethodp->dtypeSetVoid();
            auto* const sensesp = nodep->sensesp();
            addEventDebugInfo(evalMethodp, sensesp);
            // Create the co_await
            auto* const awaitEvalp
                = new AstCAwait{flp, evalMethodp, getCreateDynamicTriggerSenTree()};
            awaitEvalp->statement(true);
            // Construct the sen expression for this sentree
            SenExprBuilder senExprBuilder{m_scopep};
            auto* const assignp = new AstAssign{flp, new AstVarRef{flp, trigvscp, VAccess::WRITE},
                                                senExprBuilder.build(sensesp).first};
            // Put all the locals and inits before the trigger eval loop
            for (AstVar* const varp : senExprBuilder.getAndClearLocals()) {
                nodep->addHereThisAsNext(varp);
            }
            for (AstNodeStmt* const stmtp : senExprBuilder.getAndClearInits()) {
                nodep->addHereThisAsNext(stmtp);
            }
            // Create the trigger eval loop, which will await the evaluation step and check the
            // trigger
            auto* const loopp = new AstWhile{
                flp, new AstLogNot{flp, new AstVarRef{flp, trigvscp, VAccess::READ}}, awaitEvalp};
            // Put pre updates before the trigger check and assignment
            for (AstNodeStmt* const stmtp : senExprBuilder.getAndClearPreUpdates()) {
                loopp->addStmtsp(stmtp);
            }
            // Then the trigger check and assignment
            loopp->addStmtsp(assignp);
            // If the post update is destructive (e.g. event vars are cleared), create an await for
            // the post update step
            if (destructivePostUpdate(sensesp)) {
                auto* const awaitPostUpdatep = awaitEvalp->cloneTree(false);
                VN_AS(awaitPostUpdatep->exprp(), CMethodHard)->name("postUpdate");
                loopp->addStmtsp(awaitPostUpdatep);
            }
            // Put the post updates at the end of the loop
            for (AstNodeStmt* const stmtp : senExprBuilder.getAndClearPostUpdates()) {
                loopp->addStmtsp(stmtp);
            }
            // Finally, await the resumption step in 'act'
            auto* const awaitResumep = awaitEvalp->cloneTree(false);
            VN_AS(awaitResumep->exprp(), CMethodHard)->name("resumption");
            AstNode::addNext<AstNode, AstNode>(loopp, awaitResumep);
            // Replace the event control with the loop
            nodep->replaceWith(loopp);
        } else {
            auto* const sensesp = m_finder.getSenTree(nodep->sensesp());
            nodep->sensesp()->unlinkFrBack()->deleteTree();
            // Get this sentree's trigger scheduler
            FileLine* const flp = nodep->fileline();
            // Replace self with a 'co_await trigSched.trigger()'
            auto* const triggerMethodp = new AstCMethodHard{
                flp, new AstVarRef{flp, getCreateTriggerSchedulerp(sensesp), VAccess::WRITE},
                "trigger"};
            triggerMethodp->dtypeSetVoid();
            addEventDebugInfo(triggerMethodp, sensesp);
            // Create the co_await
            auto* const awaitp = new AstCAwait{flp, triggerMethodp, sensesp};
            awaitp->statement(true);
            nodep->replaceWith(awaitp);
        }
        VL_DO_DANGLING(nodep->deleteTree(), nodep);
    }
    void visit(AstNodeAssign* nodep) override {
        // Only process once to avoid infinite loops (due to the net delay)
        if (nodep->user1SetOnce()) return;
        AstNode* const controlp = factorOutTimingControl(nodep);
        if (!controlp) return;
        // Handle the intra assignment timing control
        FileLine* const flp = nodep->fileline();
        if (VN_IS(nodep, AssignDly)) {
            // If it's an NBA with an intra assignment delay, put it in a fork
            auto* const forkp = new AstFork{flp, "", nullptr};
            forkp->joinType(VJoinType::JOIN_NONE);
            controlp->replaceWith(forkp);
            forkp->addStmtsp(controlp);
        }
        // Insert new vars before the timing control if we're in a function; in a process we can't
        // do that. These intra-assignment vars will later be passed to forked processes by value.
        AstNode* const insertBeforep = VN_IS(m_procp, CFunc) ? controlp : nullptr;
        // Function for replacing values with intermediate variables
        const auto replaceWithIntermediate = [&](AstNode* const valuep, const std::string& name) {
            AstVarScope* const newvscp = createTemp(flp, name, valuep->dtypep(), insertBeforep);
            valuep->replaceWith(new AstVarRef{flp, newvscp, VAccess::READ});
            controlp->addHereThisAsNext(
                new AstAssign{flp, new AstVarRef{flp, newvscp, VAccess::WRITE}, valuep});
        };
        // Create the intermediate select vars. Note: because 'foreach' proceeds in
        // pre-order, and we replace indices in selects with variables, we cannot
        // reach another select under the index position. This is exactly what
        // we want as only the top level selects are LValues. As an example,
        // this transforms 'x[a[i]][b[j]] = y'
        // into 't1 = a[i]; t0 = b[j]; x[t1][t0] = y'.
        nodep->lhsp()->foreach([&](AstSel* selp) {
            if (VN_IS(selp->lsbp(), Const)) return;
            replaceWithIntermediate(selp->lsbp(), m_intraLsbNames.get(nodep));
            // widthp should be const
        });
        nodep->lhsp()->foreach([&](AstNodeSel* selp) {
            if (VN_IS(selp->bitp(), Const)) return;
            replaceWithIntermediate(selp->bitp(), m_intraIndexNames.get(nodep));
        });
        // Replace the RHS with an intermediate value var
        replaceWithIntermediate(nodep->rhsp(), m_intraValueNames.get(nodep));
    }
    void visit(AstAssignW* nodep) override {
        AstDelay* const netDelayp = getLhsNetDelay(nodep);
        if (!netDelayp && !nodep->timingControlp()) return;
        // This assignment will be converted to an always. In some cases this may generate an
        // UNOPTFLAT, e.g.: assign #1 clk = ~clk. We create a temp var for the LHS of this
        // assign, to disable the UNOPTFLAT warning for it.
        // TODO: Find a way to do this without introducing this var. Perhaps make
        // V3SchedAcyclic recognize awaits and prevent it from treating this kind of logic as
        // cyclic
        AstNode* const lhsp = nodep->lhsp()->unlinkFrBack();
        std::string varname;
        if (auto* const refp = VN_CAST(lhsp, VarRef)) {
            varname = m_contAssignVarNames.get(refp->name());
        } else {
            varname = m_contAssignVarNames.get(lhsp);
        }
        auto* const tempvscp = m_scopep->createTemp(varname, lhsp->dtypep());
        tempvscp->varp()->delayp(netDelayp);
        FileLine* const flp = nodep->fileline();
        flp->modifyWarnOff(V3ErrorCode::UNOPTFLAT, true);
        tempvscp->fileline(flp);
        tempvscp->varp()->fileline(flp);
        // Remap the LHS to the new temp var
        nodep->lhsp(new AstVarRef{flp, tempvscp, VAccess::WRITE});
        // Convert it to an always; the new assign with intra delay will be handled by
        // visit(AstNodeAssign*)
        AstAlways* const alwaysp = nodep->convertToAlways();
        visit(alwaysp);
        // Put the LHS back in the AssignW; put the temp var on the RHS
        nodep->lhsp(lhsp);
        nodep->rhsp(new AstVarRef{flp, tempvscp, VAccess::READ});
        // Put the AssignW right after the always. Different order can produce UNOPTFLAT on the LHS
        // var
        alwaysp->addNextHere(nodep);
    }
    void visit(AstWait* nodep) override {
        // Wait on changed events related to the vars in the wait statement
        FileLine* const flp = nodep->fileline();
        AstNode* const stmtsp = nodep->stmtsp();
        if (stmtsp) stmtsp->unlinkFrBackWithNext();
        AstNode* const condp = V3Const::constifyEdit(nodep->condp()->unlinkFrBack());
        auto* const constp = VN_CAST(condp, Const);
        if (constp) {
            condp->v3warn(WAITCONST, "Wait statement condition is constant");
            if (constp->isZero()) {
                // We have to await forever instead of simply returning in case we're deep in a
                // callstack
                auto* const awaitp = new AstCAwait{flp, new AstCStmt{flp, "VlForever{}"}};
                awaitp->statement(true);
                nodep->replaceWith(awaitp);
                if (stmtsp) VL_DO_DANGLING(stmtsp->deleteTree(), stmtsp);
            } else if (stmtsp) {
                // Just put the statements there
                nodep->replaceWith(stmtsp);
            }
            VL_DO_DANGLING(condp->deleteTree(), condp);
        } else if (needDynamicTrigger(condp)) {
            // No point in making a sentree, just use the expression as sensitivity
            // Put the event control in an if so we only wait if the condition isn't met already
            auto* const ifp = new AstIf{
                flp, new AstLogNot{flp, condp},
                new AstEventControl{flp,
                                    new AstSenTree{flp, new AstSenItem{flp, VEdgeType::ET_TRUE,
                                                                       condp->cloneTree(false)}},
                                    nullptr}};
            if (stmtsp) AstNode::addNext<AstNode, AstNode>(ifp, stmtsp);
            nodep->replaceWith(ifp);
        } else {
            AstSenItem* const senItemsp = varRefpsToSenItemsp(condp);
            UASSERT_OBJ(senItemsp, nodep, "No varrefs in wait statement condition");
            // Put the event control in a while loop with the wait expression as condition
            auto* const loopp
                = new AstWhile{flp, new AstLogNot{flp, condp},
                               new AstEventControl{flp, new AstSenTree{flp, senItemsp}, nullptr}};
            if (stmtsp) AstNode::addNext<AstNode, AstNode>(loopp, stmtsp);
            nodep->replaceWith(loopp);
        }
        VL_DO_DANGLING(nodep->deleteTree(), nodep);
    }
    void visit(AstFork* nodep) override {
        if (nodep->user1SetOnce()) return;
        // Create a unique name for this fork
        nodep->name(m_forkNames.get(nodep));
        unsigned idx = 0;  // Index for naming begins
        AstNode* stmtp = nodep->stmtsp();
        // Put each statement in a begin
        while (stmtp) {
            if (!VN_IS(stmtp, Begin)) {
                auto* const beginp = new AstBegin{stmtp->fileline(), "", nullptr};
                stmtp->replaceWith(beginp);
                beginp->addStmtsp(stmtp);
                stmtp = beginp;
            }
            auto* const beginp = VN_AS(stmtp, Begin);
            stmtp = beginp->nextp();
            VL_RESTORER(m_procp);
            m_procp = beginp;
            iterate(beginp);
            // Even if we do not find any awaits, we cannot simply inline the process here, as new
            // awaits could be added later.
            // Name the begin (later the name will be used for a new function)
            beginp->name(nodep->name() + "__" + cvtToStr(idx++));
        }
        if (!nodep->joinType().joinNone()) makeForkJoin(nodep);
    }

    //--------------------
    void visit(AstNodeMath*) override {}  // Accelerate
    void visit(AstVar*) override {}
    void visit(AstNode* nodep) override { iterateChildren(nodep); }

public:
    // CONSTRUCTORS
    explicit TimingVisitor(AstNetlist* nodep)
        : m_netlistp{nodep} {
        iterate(nodep);
        if (dumpGraph() >= 6) m_depGraph.dumpDotFilePrefixed("timing_deps");
    }
    ~TimingVisitor() override = default;
};

//######################################################################
// Timing class functions

void V3Timing::timingAll(AstNetlist* nodep) {
    UINFO(2, __FUNCTION__ << ": " << endl);
    TimingVisitor{nodep};
    V3Global::dumpCheckGlobalTree("timing", 0, dumpTree() >= 3);
}
