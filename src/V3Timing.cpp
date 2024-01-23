// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Prepare AST for timing features
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2024 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
// TimingSuspendableVisitor does not perform any AST transformations.
// Instead it propagates two types of flags:
// - flag "suspendable": (for detecting what will need to become a coroutine)
//     The visitor locates all C++ functions and processes that contain timing controls,
//     and marks them as suspendable. If a process calls a suspendable function,
//     then it is also marked as suspendable. If a function calls or overrides
//     a suspendable function, it is also marked as suspendable.
//     TimingSuspendableVisitor creates a dependency graph to propagate this property.
// - flag "needs process": (for detecting what needs a VlProcess argument in signature)
//   The visitor distinguishes 4 types of nodes:
//     - T_ALLOCS_PROC: nodes that can allocate VlProcess (forks, always, initial etc.),
//     - T_FORCES_PROC: nodes that make it necessary for the previous type to allocate VlProcess
//       (like process::self which then wraps it, allowing use inside Verilog).
//     - T_NEEDS_PROC: nodes that should obtain VlProcess if it will be allocated
//       (all of the previous type + timing controls, so they could update process state),
//     - T_HAS_PROC: nodes that are going to be emitted with a VlProcess argument.
//   T_FORCES_PROC and T_NEEDS_PROC are propagated upwards up to the nodes of type T_ALLOCS_PROC,
//   this is to detect which processes have to allocate VlProcess. Then nodes of these processes
//   get marked as T_HAS_PROC and the flag is propagated downwards through nodes
//   type T_NEEDS_PROC. Using only nodes type T_NEEDS_PROC assures the flags are only propagated
//   through paths leading to nodes that actually use VlProcess.
//
// TimingControlVisitor is the one that actually performs transformations:
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
//
// See the internals documentation docs/internals.rst for more details.
//
//*************************************************************************

#include "V3PchAstNoMT.h"  // VL_MT_DISABLED_CODE_UNIT

#include "V3Timing.h"

#include "V3Const.h"
#include "V3EmitV.h"
#include "V3Graph.h"
#include "V3MemberMap.h"
#include "V3SenExprBuilder.h"
#include "V3SenTree.h"
#include "V3UniqueNames.h"

#include <queue>

VL_DEFINE_DEBUG_FUNCTIONS;

// ######################################################################

enum NodeFlag : uint8_t {
    T_SUSPENDEE = 1 << 0,  // Suspendable (due to dependence on another suspendable)
    T_SUSPENDER = 1 << 1,  // Suspendable (has timing control)
    T_ALLOCS_PROC = 1 << 2,  // Can allocate VlProcess
    T_FORCES_PROC = 1 << 3,  // Forces VlProcess allocation
    T_NEEDS_PROC = 1 << 4,  // Needs access to VlProcess if it's allocated
    T_HAS_PROC = 1 << 5,  // Has VlProcess argument in the signature
};

enum ForkType : uint8_t {
    F_NONE = 0,  // Not under a fork
    F_MIGHT_SUSPEND = 1 << 0,  // Fork might suspend the execution of current process
    F_MIGHT_NEED_PROC = 1 << 1,  // Fork might need a process (any fork really)
};

enum PropagationType : uint8_t {
    P_CALL = 1,  // Propagation through call to a function/task/method
    P_FORK = 2,  // Propagation due to fork's behaviour
    P_SIGNATURE = 3,  // Propagation required to maintain C++ function's signature requirements
};

// Add timing flag to a node
static void addFlags(AstNode* const nodep, uint8_t flags) { nodep->user2(nodep->user2() | flags); }
// Check if a node has ALL of the expected flags set
static bool hasFlags(AstNode* const nodep, uint8_t flags) { return !(~nodep->user2() & flags); }

// ######################################################################
//  Detect nodes affected by timing and/or requiring a process

class TimingSuspendableVisitor final : public VNVisitor {
    // TYPES
    // Vertex of a dependency graph of suspendable nodes, e.g. if a node (process or task) is
    // suspendable, all its dependents should also be suspendable
    class DepVtx VL_NOT_FINAL : public V3GraphVertex {
        VL_RTTI_IMPL(DepVtx, V3GraphVertex)
        AstClass* const m_classp;  // Class associated with a method
        AstNode* const m_nodep;  // AST node represented by this graph vertex

        // ACCESSORS
        string name() const override {
            if (m_classp) {
                if (VN_IS(nodep(), CFunc)) {
                    return cvtToHex(nodep()) + ' ' + classp()->name() + "::" + nodep()->name();
                }
            }
            return cvtToHex(nodep()) + ' ' + nodep()->prettyTypeName();
        }
        FileLine* fileline() const override { return nodep()->fileline(); }

    public:
        // CONSTRUCTORS
        DepVtx(V3Graph* graphp, AstNode* nodep, AstClass* classp)
            : V3GraphVertex{graphp}
            , m_classp{classp}
            , m_nodep{nodep} {}
        ~DepVtx() override = default;

        // ACCESSORS
        virtual AstNode* nodep() const VL_MT_STABLE { return m_nodep; }
        virtual AstNode* classp() const VL_MT_STABLE { return m_classp; }
    };

    class SuspendDepVtx final : public DepVtx {
        VL_RTTI_IMPL(SuspendDepVtx, DepVtx)
        string dotColor() const override {
            if (hasFlags(nodep(), T_SUSPENDER)) return "red";
            if (hasFlags(nodep(), T_SUSPENDEE)) return "blue";
            return "black";
        }

    public:
        SuspendDepVtx(V3Graph* graphp, AstNode* nodep, AstClass* classp)
            : DepVtx{graphp, nodep, classp} {}
        ~SuspendDepVtx() override = default;
    };

    class NeedsProcDepVtx final : public DepVtx {
        VL_RTTI_IMPL(NeedsProcDepVtx, DepVtx)
        string dotColor() const override {
            if (hasFlags(nodep(), T_HAS_PROC)) return "blue";
            if (hasFlags(nodep(), T_NEEDS_PROC)) return "green";
            if (hasFlags(nodep(), T_FORCES_PROC)) return "red";
            return "black";
        }

    public:
        NeedsProcDepVtx(V3Graph* graphp, AstNode* nodep, AstClass* classp)
            : DepVtx{graphp, nodep, classp} {}
        ~NeedsProcDepVtx() override = default;
    };

    // NODE STATE
    //  AstClass::user1()                        -> bool.               Set true if the class
    //                                                                  member cache has been
    //                                                                  refreshed.
    //  Ast{NodeProcedure,CFunc,Begin}::user2()  -> int.                Set to >= T_SUSP if
    //                                                                  process/task suspendable
    //                                                                  and to T_PROC if it
    //                                                                  needs process metadata.
    //  Ast{NodeProcedure,CFunc,Begin}::user3()  -> DependencyVertex*.  Vertex in m_suspGraph
    //  Ast{NodeProcedure,CFunc,Begin}::user3()  -> DependencyVertex*.  Vertex in m_procGraph
    const VNUser1InUse m_user1InUse;
    const VNUser2InUse m_user2InUse;
    const VNUser3InUse m_user3InUse;
    const VNUser4InUse m_user4InUse;

    // STATE
    VMemberMap m_memberMap;  // Member names cached for fast lookup
    AstClass* m_classp = nullptr;  // Current class
    AstNode* m_procp = nullptr;  // NodeProcedure/CFunc/Begin we're under
    uint8_t m_underFork = F_NONE;  // F_NONE or flags of a fork we are under
    V3Graph m_suspGraph;  // Dependency graph where a node is a dependency of another if it being
                          // suspendable makes the other node suspendable
    V3Graph m_procGraph;  // Dependency graph where a node is a dependency of another if it being
                          // suspendable makes the other node suspendable

    // METHODS
    // Get or create the dependency vertex for the given node
    DepVtx* getSuspendDepVtx(AstNode* const nodep) {
        AstClass* classp = nullptr;
        if (AstCFunc* funcp = VN_CAST(nodep, CFunc)) {
            if (funcp->scopep() && funcp->scopep()->modp()) {
                classp = VN_CAST(funcp->scopep()->modp(), Class);
            }
        }
        if (!nodep->user3p()) nodep->user3p(new SuspendDepVtx{&m_suspGraph, nodep, classp});
        return nodep->user3u().to<SuspendDepVtx*>();
    }
    DepVtx* getNeedsProcDepVtx(AstNode* const nodep) {
        AstClass* classp = nullptr;
        if (AstCFunc* funcp = VN_CAST(nodep, CFunc)) {
            if (funcp->scopep() && funcp->scopep()->modp()) {
                classp = VN_CAST(funcp->scopep()->modp(), Class);
            }
        }
        if (!nodep->user4p()) nodep->user4p(new NeedsProcDepVtx{&m_procGraph, nodep, classp});
        return nodep->user4u().to<NeedsProcDepVtx*>();
    }
    // Pass timing flag between nodes
    bool passFlag(const AstNode* from, AstNode* to, NodeFlag flag) {
        if ((from->user2() & flag) && !(to->user2() & flag)) {
            addFlags(to, flag);
            return true;
        }
        return false;
    }
    // Propagate flag to all nodes that depend on the given one
    void propagateFlags(DepVtx* const vxp, NodeFlag flag) {
        auto* const parentp = vxp->nodep();
        for (V3GraphEdge* edgep = vxp->outBeginp(); edgep; edgep = edgep->outNextp()) {
            auto* const depVxp = static_cast<DepVtx*>(edgep->top());
            AstNode* const depp = depVxp->nodep();
            if (passFlag(parentp, depp, flag)) propagateFlags(depVxp, flag);
        }
    }
    template <typename Predicate>
    void propagateFlagsIf(DepVtx* const vxp, NodeFlag flag, Predicate p) {
        auto* const parentp = vxp->nodep();
        for (V3GraphEdge* edgep = vxp->outBeginp(); edgep; edgep = edgep->outNextp()) {
            auto* const depVxp = static_cast<DepVtx*>(edgep->top());
            AstNode* const depp = depVxp->nodep();
            if (p(edgep) && passFlag(parentp, depp, flag)) propagateFlagsIf(depVxp, flag, p);
        }
    }
    template <typename Predicate>
    void propagateFlagsReversedIf(DepVtx* const vxp, NodeFlag flag, Predicate p) {
        auto* const parentp = vxp->nodep();
        for (V3GraphEdge* edgep = vxp->inBeginp(); edgep; edgep = edgep->inNextp()) {
            auto* const depVxp = static_cast<DepVtx*>(edgep->fromp());
            AstNode* const depp = depVxp->nodep();
            if (p(edgep) && passFlag(parentp, depp, flag))
                propagateFlagsReversedIf(depVxp, flag, p);
        }
    }

    // VISITORS
    void visit(AstClass* nodep) override {
        UASSERT(!m_classp, "Class under class");
        VL_RESTORER(m_classp);
        m_classp = nodep;
        iterateChildren(nodep);
    }
    void visit(AstNodeProcedure* nodep) override {
        VL_RESTORER(m_procp);
        m_procp = nodep;
        getNeedsProcDepVtx(nodep);
        addFlags(nodep, T_ALLOCS_PROC);
        if (VN_IS(nodep, Always)) {
            UINFO(1, "Always does " << (nodep->needProcess() ? "" : "NOT ") << "need process\n");
        }
        iterateChildren(nodep);
    }
    void visit(AstDisableFork* nodep) override {
        visit(static_cast<AstNode*>(nodep));
        addFlags(m_procp, T_FORCES_PROC | T_NEEDS_PROC);
    }
    void visit(AstWaitFork* nodep) override {
        visit(static_cast<AstNode*>(nodep));
        addFlags(m_procp, T_FORCES_PROC | T_NEEDS_PROC);
    }
    void visit(AstWait* nodep) override {
        AstNodeExpr* const condp = V3Const::constifyEdit(nodep->condp());
        if (AstConst* const constp = VN_CAST(condp, Const)) {
            if (!nodep->fileline()->warnIsOff(V3ErrorCode::WAITCONST)) {
                condp->v3warn(WAITCONST, "Wait statement condition is constant");
            }
            if (!constp->isZero()) {
                // Remove AstWait before we track process as T_SUSPENDER
                if (AstNode* const stmtsp = nodep->stmtsp()) {
                    stmtsp->unlinkFrBackWithNext();
                    nodep->replaceWith(stmtsp);
                } else {
                    nodep->unlinkFrBack();
                }
                VL_DO_DANGLING(pushDeletep(nodep), nodep);
                return;
            }
        }
        v3Global.setUsesTiming();
        if (m_procp) addFlags(m_procp, T_SUSPENDEE | T_SUSPENDER | T_NEEDS_PROC);
        iterateChildren(nodep);
    }
    void visit(AstCFunc* nodep) override {
        VL_RESTORER(m_procp);
        m_procp = nodep;
        iterateChildren(nodep);
        if (nodep->needProcess()) addFlags(nodep, T_FORCES_PROC | T_NEEDS_PROC);
        DepVtx* const sVxp = getSuspendDepVtx(nodep);
        DepVtx* const pVxp = getNeedsProcDepVtx(nodep);
        if (!m_classp) return;

        // Go over overridden functions

        std::queue<AstClassExtends*> extends;
        if (m_classp->extendsp()) extends.push(m_classp->extendsp());

        while (!extends.empty()) {
            AstClassExtends* ext_list = extends.front();
            extends.pop();

            for (AstClassExtends* cextp = ext_list; cextp;
                 cextp = VN_AS(cextp->nextp(), ClassExtends)) {
                // TODO: It is possible that a methods the same name in the base class is not
                // actually overridden by our method. If this causes a problem, traverse to
                // the root of the inheritance hierarchy and check if the original method is
                // virtual or not.
                if (auto* const overriddenp
                    = VN_CAST(m_memberMap.findMember(cextp->classp(), nodep->name()), CFunc)) {
                    // Suspendability and process affects typing, so they propagate both ways
                    DepVtx* const overriddenSVxp = getSuspendDepVtx(overriddenp);
                    DepVtx* const overriddenPVxp = getNeedsProcDepVtx(overriddenp);
                    new V3GraphEdge{&m_suspGraph, sVxp, overriddenSVxp, P_SIGNATURE};
                    new V3GraphEdge{&m_suspGraph, overriddenSVxp, sVxp, P_SIGNATURE};
                    new V3GraphEdge{&m_procGraph, pVxp, overriddenPVxp, P_SIGNATURE};
                    new V3GraphEdge{&m_procGraph, overriddenPVxp, pVxp, P_SIGNATURE};
                } else {
                    AstClassExtends* more_extends = cextp->classp()->extendsp();
                    if (more_extends) extends.push(more_extends);
                }
            }
        }
    }
    void visit(AstNodeCCall* nodep) override {
        if (!m_underFork || (m_underFork & F_MIGHT_SUSPEND))
            new V3GraphEdge{&m_suspGraph, getSuspendDepVtx(nodep->funcp()),
                            getSuspendDepVtx(m_procp), m_underFork ? P_FORK : P_CALL};

        new V3GraphEdge{&m_procGraph, getNeedsProcDepVtx(nodep->funcp()),
                        getNeedsProcDepVtx(m_procp), P_CALL};

        if (m_underFork && !(m_underFork & F_MIGHT_SUSPEND)) {
            addFlags(nodep, T_NEEDS_PROC | T_ALLOCS_PROC);
        }

        iterateChildren(nodep);
    }
    void visit(AstBegin* nodep) override {
        VL_RESTORER(m_procp);
        VL_RESTORER(m_underFork);

        if (!m_underFork || (m_underFork & F_MIGHT_SUSPEND))
            new V3GraphEdge{&m_suspGraph, getSuspendDepVtx(nodep), getSuspendDepVtx(m_procp),
                            m_underFork ? P_FORK : P_CALL};

        new V3GraphEdge{&m_procGraph, getNeedsProcDepVtx(nodep), getNeedsProcDepVtx(m_procp),
                        P_CALL};

        if (m_underFork && !(m_underFork & F_MIGHT_SUSPEND)) {
            addFlags(nodep, T_NEEDS_PROC | T_ALLOCS_PROC);
        }

        m_procp = nodep;
        m_underFork = 0;
        iterateChildren(nodep);
    }
    void visit(AstFork* nodep) override {
        VL_RESTORER(m_underFork);

        v3Global.setUsesTiming();  // Even if there are no event controls, we have to set this flag
                                   // so that transformForks() in V3SchedTiming gets called and
                                   // removes all forks and begins
        if (nodep->isTimingControl() && m_procp) {
            addFlags(m_procp, T_SUSPENDEE | T_SUSPENDER);
            m_underFork |= F_MIGHT_SUSPEND;
        }
        m_underFork |= F_MIGHT_NEED_PROC;
        iterateChildren(nodep);
    }
    void visit(AstAssignDly* nodep) override {
        if (!VN_IS(m_procp, NodeProcedure)) v3Global.setUsesTiming();
        visit(static_cast<AstNode*>(nodep));
    }
    void visit(AstNode* nodep) override {
        if (nodep->isTimingControl()) {
            v3Global.setUsesTiming();
            if (m_procp) addFlags(m_procp, T_SUSPENDEE | T_SUSPENDER | T_NEEDS_PROC);
        }
        iterateChildren(nodep);
    }

    //--------------------
    void visit(AstVar*) override {}  // Accelerate

public:
    // CONSTRUCTORS
    explicit TimingSuspendableVisitor(AstNetlist* nodep) {
        iterate(nodep);
        m_suspGraph.removeTransitiveEdges();
        m_procGraph.removeTransitiveEdges();
        // Propagate suspendability
        for (V3GraphVertex* vxp = m_suspGraph.verticesBeginp(); vxp; vxp = vxp->verticesNextp()) {
            DepVtx* const depVxp = static_cast<DepVtx*>(vxp);
            if (hasFlags(depVxp->nodep(), T_SUSPENDEE)) propagateFlags(depVxp, T_SUSPENDEE);
        }
        if (dumpGraphLevel() >= 6) m_suspGraph.dumpDotFilePrefixed("timing_deps");

        // Propagate T_HAS_PROCESS
        for (V3GraphVertex* vxp = m_procGraph.verticesBeginp(); vxp; vxp = vxp->verticesNextp()) {
            DepVtx* const depVxp = static_cast<DepVtx*>(vxp);
            // Find processes that'll allocate VlProcess
            if (hasFlags(depVxp->nodep(), T_FORCES_PROC)) {
                propagateFlagsIf(depVxp, T_FORCES_PROC, [&](const V3GraphEdge* e) -> bool {
                    return !hasFlags(static_cast<DepVtx*>(e->fromp())->nodep(), T_ALLOCS_PROC);
                });
            }
            // Mark nodes on paths between processes and statements that use VlProcess
            if (hasFlags(depVxp->nodep(), T_NEEDS_PROC)) {
                propagateFlagsIf(depVxp, T_NEEDS_PROC, [&](const V3GraphEdge* e) -> bool {
                    return !hasFlags(static_cast<DepVtx*>(e->top())->nodep(), T_ALLOCS_PROC);
                });
            }
        }
        for (V3GraphVertex* vxp = m_procGraph.verticesBeginp(); vxp; vxp = vxp->verticesNextp()) {
            DepVtx* const depVxp = static_cast<DepVtx*>(vxp);
            // Mark nodes that will be emitted with a VlProcess argument
            if (hasFlags(depVxp->nodep(), T_ALLOCS_PROC | T_FORCES_PROC)) {
                addFlags(depVxp->nodep(), T_HAS_PROC);
                propagateFlagsReversedIf(depVxp, T_HAS_PROC, [&](const V3GraphEdge* e) -> bool {
                    return hasFlags(static_cast<DepVtx*>(e->fromp())->nodep(), T_NEEDS_PROC);
                });
            }
        }
        if (dumpGraphLevel() >= 6) m_procGraph.dumpDotFilePrefixed("proc_deps");
    }
    ~TimingSuspendableVisitor() override = default;
};

// ######################################################################
//  Transform nodes affected by timing

class TimingControlVisitor final : public VNVisitor {
    // NODE STATE
    //  Ast{Always,NodeCCall,Fork,NodeAssign}::user1()  -> bool.         Set true if the node has
    //                                                                   been processed.
    //  AstSenTree::user1()                             -> AstVarScope*. Trigger scheduler assigned
    //                                                                   to this sentree
    //  Ast{NodeProcedure,CFunc,Begin}::user2()         -> bool.         Set true if process/task
    //                                                                   is suspendable
    //  Ast{EventControl}::user2()                      -> bool.         Set true if event control
    //                                                                   should immediately be
    //                                                                   committed
    //  AstSenTree::user2()                             -> AstCExpr*.    Debug info passed to the
    //                                                                   timing schedulers
    // const VNUser1InUse m_user1InUse;      (Allocated for use in SuspendableVisitor)
    // const VNUser2InUse m_user2InUse;      (Allocated for use in SuspendableVisitor)

    // STATE
    // Current context
    AstNetlist* const m_netlistp;  // Root node
    AstScope* const m_scopeTopp = m_netlistp->topScopep()->scopep();  // Scope at the top
    AstClass* m_classp = nullptr;  // Current class
    AstScope* m_scopep = nullptr;  // Current scope
    AstActive* m_activep = nullptr;  // Current active
    AstNode* m_procp = nullptr;  // NodeProcedure/CFunc/Begin we're under
    int m_forkCnt = 0;  // Number of forks inside a module
    bool m_underJumpBlock = false;  // True if we are inside of a jump-block
    bool m_underProcedure = false;  // True if we are under an always or initial

    // Unique names
    V3UniqueNames m_dlyforkNames{"__Vdlyfork"};  // Names for temp AssignW vars
    V3UniqueNames m_contAssignVarNames{"__VassignWtmp"};  // Names for temp AssignW vars
    V3UniqueNames m_intraValueNames{"__Vintraval"};  // Intra assign delay value var names
    V3UniqueNames m_intraIndexNames{"__Vintraidx"};  // Intra assign delay index var names
    V3UniqueNames m_intraLsbNames{"__Vintralsb"};  // Intra assign delay LSB var names
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
    SenTreeFinder m_finder{m_netlistp};  // Sentree finder and uniquifier
    SenExprBuilder* m_senExprBuilderp = nullptr;  // Sens expression builder for current m_scope

    // METHODS
    // Find net delay on the LHS of an assignment
    AstDelay* getLhsNetDelayRecurse(const AstNodeExpr* const nodep) const {
        if (const AstNodeVarRef* const refp = VN_CAST(nodep, NodeVarRef)) {
            if (refp->varp()->delayp()) return refp->varp()->delayp()->unlinkFrBack();
        } else if (const AstSel* const selp = VN_CAST(nodep, Sel)) {
            return getLhsNetDelayRecurse(selp->fromp());
        }
        return nullptr;
    }
    // Transform an assignment with an intra timing control into a timing control with the
    // assignment under it
    AstNode* factorOutTimingControl(AstNodeAssign* nodep) const {
        AstNode* stmtp = nodep;
        AstDelay* delayp = getLhsNetDelayRecurse(nodep->lhsp());
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
        } else if (auto* const beginp = VN_CAST(controlp, Begin)) {
            // Begin from V3AssertPre
            stmtp->replaceWith(beginp);
            beginp->addStmtsp(stmtp);
            stmtp = beginp;
        }
        return stmtp == nodep ? nullptr : stmtp;
    }
    // Calculate the factor to scale delays by
    double calculateTimescaleFactor(AstNode* nodep, VTimescale timeunit) const {
        UASSERT_OBJ(!timeunit.isNone(), nodep, "timenunit must be set");
        const int scalePowerOfTen
            = timeunit.powerOfTen() - m_netlistp->timeprecision().powerOfTen();
        return std::pow(10.0, scalePowerOfTen);
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
    // Creates the event variable to trigger in NBA region
    AstEventControl* createNbaEventControl(FileLine* flp) {
        if (!m_netlistp->nbaEventp()) {
            auto* const nbaEventDtp = new AstBasicDType{m_scopeTopp->fileline(),
                                                        VBasicDTypeKwd::EVENT, VSigning::UNSIGNED};
            m_netlistp->typeTablep()->addTypesp(nbaEventDtp);
            m_netlistp->nbaEventp(m_scopeTopp->createTemp("__VnbaEvent", nbaEventDtp));
            v3Global.setHasEvents();
        }
        return new AstEventControl{
            flp,
            new AstSenTree{
                flp, new AstSenItem{flp, VEdgeType::ET_EVENT,
                                    new AstVarRef{flp, m_netlistp->nbaEventp(), VAccess::READ}}},
            nullptr};
    }
    // Creates the variable that, if set, causes the NBA event to be triggered
    AstAssign* createNbaEventTriggerAssignment(FileLine* flp) {
        if (!m_netlistp->nbaEventTriggerp()) {
            m_netlistp->nbaEventTriggerp(m_scopeTopp->createTemp("__VnbaEventTrigger", 1));
        }
        return new AstAssign{flp,
                             new AstVarRef{flp, m_netlistp->nbaEventTriggerp(), VAccess::WRITE},
                             new AstConst{flp, AstConst::BitTrue{}}};
    }
    // Returns true if we are under a class or the given tree has any references to locals. These
    // are cases where static, globally-evaluated triggers are not suitable.
    bool needDynamicTrigger(AstNode* const nodep) const {
        return m_classp || nodep->exists([](AstNode* const nodep) {
            if (AstNodeVarRef* varp = VN_CAST(nodep, NodeVarRef)) {
                return varp->varp()->isFuncLocal();
            }
            return !nodep->isPure();
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
    AstCExpr* createEventDescription(AstSenTree* const sensesp) const {
        if (!sensesp->user2p()) {
            std::stringstream ss;
            ss << '"';
            V3EmitV::verilogForTree(sensesp, ss);
            ss << '"';
            // possibly a multiline string
            std::string comment = ss.str();
            std::replace(comment.begin(), comment.end(), '\n', ' ');
            AstCExpr* const commentp = new AstCExpr{sensesp->fileline(), comment, 0};
            commentp->dtypeSetString();
            sensesp->user2p(commentp);
            return commentp;
        }
        return VN_AS(sensesp->user2p(), CExpr)->cloneTree(false);
    }
    // Adds debug info to a hardcoded method call
    void addDebugInfo(AstCMethodHard* const methodp) const {
        if (v3Global.opt.protectIds()) return;
        FileLine* const flp = methodp->fileline();
        AstCExpr* const ap = new AstCExpr{flp, '"' + flp->filename() + '"', 0};
        ap->dtypeSetString();
        methodp->addPinsp(ap);
        AstCExpr* const bp = new AstCExpr{flp, cvtToStr(flp->lineno()), 0};
        bp->dtypeSetString();
        methodp->addPinsp(bp);
    }
    // Adds debug info to a trigSched.trigger() call
    void addEventDebugInfo(AstCMethodHard* const methodp, AstSenTree* const sensesp) const {
        if (v3Global.opt.protectIds()) return;
        methodp->addPinsp(createEventDescription(sensesp));
        addDebugInfo(methodp);
    }
    // Adds process pointer to a hardcoded method call
    void addProcessInfo(AstCMethodHard* const methodp) const {
        FileLine* const flp = methodp->fileline();
        AstCExpr* const ap = new AstCExpr{
            flp, m_procp && (hasFlags(m_procp, T_HAS_PROC)) ? "vlProcess" : "nullptr", 0};
        ap->dtypeSetVoid();
        methodp->addPinsp(ap);
    }
    // Creates the fork handle type and returns it
    AstBasicDType* getCreateForkSyncDTypep() {
        if (m_forkDtp) return m_forkDtp;
        m_forkDtp = new AstBasicDType{m_scopeTopp->fileline(), VBasicDTypeKwd::FORK_SYNC,
                                      VSigning::UNSIGNED};
        m_netlistp->typeTablep()->addTypesp(m_forkDtp);
        return m_forkDtp;
    }
    // Move `insertBeforep` into `AstCLocalScope` if necessary to avoid jumping over
    // a variable initialization that whould be inserted before `insertBeforep`. All
    // access to this variable shoule be contained within returned `AstCLocalScope`.
    AstCLocalScope* addCLocalScope(FileLine* const flp, AstNode* const insertBeforep) const {
        if (!insertBeforep || !m_underJumpBlock) return nullptr;
        VNRelinker handle;
        insertBeforep->unlinkFrBack(&handle);
        AstCLocalScope* const cscopep = new AstCLocalScope{flp, insertBeforep};
        handle.relink(cscopep);
        return cscopep;
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
        addDebugInfo(donep);
        beginp->addStmtsp(donep->makeStmt());
    }
    // Handle the 'join' part of a fork..join
    void makeForkJoin(AstFork* const forkp) {
        // Create a fork sync var
        FileLine* const flp = forkp->fileline();
        // If we're in a function, insert the sync var directly before the fork
        AstNode* const insertBeforep = m_classp ? forkp : nullptr;
        addCLocalScope(flp, insertBeforep);
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
        addProcessInfo(initp);
        forkp->addHereThisAsNext(initp->makeStmt());
        // Await the join at the end
        auto* const joinp
            = new AstCMethodHard{flp, new AstVarRef{flp, forkVscp, VAccess::WRITE}, "join"};
        joinp->dtypeSetVoid();
        addProcessInfo(joinp);
        addDebugInfo(joinp);
        AstCAwait* const awaitp = new AstCAwait{flp, joinp};
        awaitp->dtypeSetVoid();
        forkp->addNextHere(awaitp->makeStmt());
    }

    // VISITORS
    void visit(AstNodeModule* nodep) override {
        UASSERT(!m_classp, "Module or class under class");
        VL_RESTORER(m_classp);
        m_classp = VN_CAST(nodep, Class);
        VL_RESTORER(m_forkCnt);
        m_forkCnt = 0;
        iterateChildren(nodep);
    }
    void visit(AstScope* nodep) override {
        VL_RESTORER(m_scopep);
        m_scopep = nodep;
        SenExprBuilder senExprBuilder{m_scopep};
        {  // Restore m_senExprBuilderp before destroying senExprBuilder
            VL_RESTORER(m_senExprBuilderp);
            m_senExprBuilderp = &senExprBuilder;
            iterateChildren(nodep);
        }
    }
    void visit(AstActive* nodep) override {
        m_activep = nodep;
        iterateChildren(nodep);
        m_activep = nullptr;
    }
    void visit(AstNodeProcedure* nodep) override {
        VL_RESTORER(m_procp);
        m_procp = nodep;
        VL_RESTORER(m_underProcedure);
        m_underProcedure = true;
        iterateChildren(nodep);
        if (hasFlags(nodep, T_SUSPENDEE)) nodep->setSuspendable();
        if (hasFlags(nodep, T_HAS_PROC)) nodep->setNeedProcess();
    }
    void visit(AstInitial* nodep) override {
        visit(static_cast<AstNodeProcedure*>(nodep));
        if (nodep->needProcess() && !nodep->user1SetOnce()) {
            nodep->addStmtsp(
                new AstCStmt{nodep->fileline(), "vlProcess->state(VlProcess::FINISHED);\n"});
        }
    }
    void visit(AstJumpBlock* nodep) override {
        VL_RESTORER(m_underJumpBlock);
        m_underJumpBlock = true;
        visit(static_cast<AstNodeStmt*>(nodep));
    }
    void visit(AstAlways* nodep) override {
        if (nodep->user1SetOnce()) return;
        VL_RESTORER(m_procp);
        m_procp = nodep;
        VL_RESTORER(m_underProcedure);
        m_underProcedure = true;
        // Workaround for killing `always` processes (doing that is pretty much UB)
        // TODO: Disallow killing `always` at runtime (throw an error)
        if (hasFlags(nodep, T_HAS_PROC)) addFlags(nodep, T_SUSPENDEE);

        iterateChildren(nodep);
        if (hasFlags(nodep, T_HAS_PROC)) nodep->setNeedProcess();
        if (!hasFlags(nodep, T_SUSPENDEE)) return;
        nodep->setSuspendable();
        FileLine* const flp = nodep->fileline();
        AstSenTree* const sensesp = m_activep->sensesp();
        if (sensesp->hasClocked()) {
            AstNode* const bodysp = nodep->stmtsp()->unlinkFrBackWithNext();
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
    void visit(AstCFunc* nodep) override {
        VL_RESTORER(m_procp);
        m_procp = nodep;
        iterateChildren(nodep);
        if (hasFlags(nodep, T_HAS_PROC)) nodep->setNeedProcess();
        if (!(hasFlags(nodep, T_SUSPENDEE))) return;

        nodep->rtnType("VlCoroutine");
        // If in a class, create a shared pointer to 'this'
        if (m_classp) nodep->addInitsp(new AstCStmt{nodep->fileline(), "VL_KEEP_THIS;\n"});
        AstNode* firstCoStmtp = nullptr;  // First co_* statement in the function
        nodep->exists([&](AstCAwait* const awaitp) -> bool { return (firstCoStmtp = awaitp); });
        if (!firstCoStmtp) {
            // It's a coroutine but has no awaits (a class method that overrides/is
            // overridden by a suspendable, but doesn't have any awaits itself). Add a
            // co_return at the end (either that or a co_await is required in a
            // coroutine)
            firstCoStmtp = new AstCStmt{nodep->fileline(), "co_return;\n"};
            nodep->addStmtsp(firstCoStmtp);
        }
        if (nodep->dpiExportImpl()) {
            // A DPI-exported coroutine won't be able to block the calling code
            // Error on the await node; fall back to the function node
            firstCoStmtp->v3warn(E_UNSUPPORTED,
                                 "Unsupported: Timing controls inside DPI-exported tasks");
        }
    }
    void visit(AstNodeCCall* nodep) override {
        if (hasFlags(nodep->funcp(), T_SUSPENDEE) && !nodep->user1SetOnce()) {  // If suspendable
            VNRelinker relinker;
            nodep->unlinkFrBack(&relinker);
            AstCAwait* const awaitp = new AstCAwait{nodep->fileline(), nodep};
            awaitp->dtypeSetVoid();
            relinker.relink(awaitp);
        }
        iterateChildren(nodep);
    }
    void visit(AstDelay* nodep) override {
        UASSERT_OBJ(!nodep->isCycleDelay(), nodep,
                    "Cycle delays should have been handled in V3AssertPre");
        FileLine* const flp = nodep->fileline();
        AstNodeExpr* valuep = V3Const::constifyEdit(nodep->lhsp()->unlinkFrBack());
        AstConst* const constp = VN_CAST(valuep, Const);
        if (!constp || !constp->isZero()) {
            // Scale the delay
            const double timescaleFactor = calculateTimescaleFactor(nodep, nodep->timeunit());
            if (valuep->dtypep()->isDouble()) {
                valuep = new AstRToIRoundS{
                    flp, new AstMulD{flp, valuep,
                                     new AstConst{flp, AstConst::RealDouble{}, timescaleFactor}}};
                valuep->dtypeSetBitSized(64, VSigning::UNSIGNED);
            } else {
                valuep->dtypeSetBitSized(64, VSigning::UNSIGNED);
                valuep = new AstMul{flp, valuep,
                                    new AstConst{flp, AstConst::Unsized64{},
                                                 static_cast<uint64_t>(timescaleFactor)}};
            }
        }
        // Replace self with a 'co_await dlySched.delay(<valuep>)'
        auto* const delayMethodp = new AstCMethodHard{
            flp, new AstVarRef{flp, getCreateDelayScheduler(), VAccess::WRITE}, "delay", valuep};
        delayMethodp->dtypeSetVoid();
        addProcessInfo(delayMethodp);
        addDebugInfo(delayMethodp);
        // Create the co_await
        AstCAwait* const awaitp = new AstCAwait{flp, delayMethodp, getCreateDelaySenTree()};
        awaitp->dtypeSetVoid();
        AstStmtExpr* const awaitStmtp = awaitp->makeStmt();
        // Relink child statements after the co_await
        if (nodep->stmtsp()) {
            AstNode::addNext<AstNode, AstNode>(awaitStmtp,
                                               nodep->stmtsp()->unlinkFrBackWithNext());
        }
        nodep->replaceWith(awaitStmtp);
        VL_DO_DANGLING(nodep->deleteTree(), nodep);
    }
    void visit(AstEventControl* nodep) override {
        // Do not allow waiting on local named events, as they get enqueued for clearing, but can
        // go out of scope before that happens
        if (!nodep->sensesp()) nodep->v3warn(E_UNSUPPORTED, "Unsupported: no sense equation (@*)");
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
            addProcessInfo(evalMethodp);
            auto* const sensesp = nodep->sensesp();
            addEventDebugInfo(evalMethodp, sensesp);
            // Create the co_await
            AstCAwait* const awaitEvalp
                = new AstCAwait{flp, evalMethodp, getCreateDynamicTriggerSenTree()};
            awaitEvalp->dtypeSetVoid();
            // Construct the sen expression for this sentree
            UASSERT_OBJ(m_senExprBuilderp, nodep, "No SenExprBuilder for this scope");
            auto* const assignp = new AstAssign{flp, new AstVarRef{flp, trigvscp, VAccess::WRITE},
                                                m_senExprBuilderp->build(sensesp).first};
            // Put all the locals and inits before the trigger eval loop
            for (AstVar* const varp : m_senExprBuilderp->getAndClearLocals()) {
                nodep->addHereThisAsNext(varp);
            }
            for (AstNodeStmt* const stmtp : m_senExprBuilderp->getAndClearInits()) {
                nodep->addHereThisAsNext(stmtp);
            }
            // Create the trigger eval loop, which will await the evaluation step and check the
            // trigger
            AstWhile* const loopp = new AstWhile{
                flp, new AstLogNot{flp, new AstVarRef{flp, trigvscp, VAccess::READ}},
                awaitEvalp->makeStmt()};
            // Put pre updates before the trigger check and assignment
            for (AstNodeStmt* const stmtp : m_senExprBuilderp->getAndClearPreUpdates()) {
                loopp->addStmtsp(stmtp);
            }
            // Then the trigger check and assignment
            loopp->addStmtsp(assignp);
            // Let the dynamic trigger scheduler know if this trigger was set
            // If it was, a call to the scheduler's evaluate() will return true
            AstCMethodHard* const anyTriggeredMethodp = new AstCMethodHard{
                flp, new AstVarRef{flp, getCreateDynamicTriggerScheduler(), VAccess::WRITE},
                "anyTriggered", new AstVarRef{flp, trigvscp, VAccess::READ}};
            anyTriggeredMethodp->dtypeSetVoid();
            loopp->addStmtsp(anyTriggeredMethodp->makeStmt());
            // If the post update is destructive (e.g. event vars are cleared), create an await for
            // the post update step
            if (destructivePostUpdate(sensesp)) {
                AstCAwait* const awaitPostUpdatep = awaitEvalp->cloneTree(false);
                VN_AS(awaitPostUpdatep->exprp(), CMethodHard)->name("postUpdate");
                loopp->addStmtsp(awaitPostUpdatep->makeStmt());
            }
            // Put the post updates at the end of the loop
            for (AstNodeStmt* const stmtp : m_senExprBuilderp->getAndClearPostUpdates()) {
                loopp->addStmtsp(stmtp);
            }
            // Finally, await the resumption step in 'act'
            AstCAwait* const awaitResumep = awaitEvalp->cloneTree(false);
            VN_AS(awaitResumep->exprp(), CMethodHard)->name("resumption");
            AstNode::addNext<AstNodeStmt, AstNodeStmt>(loopp, awaitResumep->makeStmt());
            // Replace the event control with the loop
            nodep->replaceWith(loopp);
        } else {
            auto* const sensesp = m_finder.getSenTree(nodep->sensesp());
            nodep->sensesp()->unlinkFrBack()->deleteTree();
            // Get this sentree's trigger scheduler
            // Replace self with a 'co_await trigSched.trigger()'
            auto* const triggerMethodp = new AstCMethodHard{
                flp, new AstVarRef{flp, getCreateTriggerSchedulerp(sensesp), VAccess::WRITE},
                "trigger"};
            triggerMethodp->dtypeSetVoid();
            // If it should be committed immediately, pass true, otherwise false
            triggerMethodp->addPinsp(nodep->user2() ? new AstConst{flp, AstConst::BitTrue{}}
                                                    : new AstConst{flp, AstConst::BitFalse{}});
            addProcessInfo(triggerMethodp);
            addEventDebugInfo(triggerMethodp, sensesp);
            // Create the co_await
            AstCAwait* const awaitp = new AstCAwait{flp, triggerMethodp, sensesp};
            awaitp->dtypeSetVoid();
            nodep->replaceWith(awaitp->makeStmt());
        }
        VL_DO_DANGLING(nodep->deleteTree(), nodep);
    }
    void visit(AstNodeAssign* nodep) override {
        // Only process once to avoid infinite loops (due to the net delay)
        if (nodep->user1SetOnce()) return;
        FileLine* const flp = nodep->fileline();
        AstNode* controlp = factorOutTimingControl(nodep);
        const bool inAssignDly = VN_IS(nodep, AssignDly);
        // Handle the intra assignment timing control
        // Transform if:
        // * there's a timing control in the assignment
        // * the assignment is an AssignDly and it's in a non-inlined function
        if (!controlp && (!inAssignDly || m_underProcedure)) return;
        // Insert new vars before the timing control if we're in a function; in a process we can't
        // do that. These intra-assignment vars will later be passed to forked processes by value.
        AstNode* insertBeforep = m_underProcedure ? nullptr : controlp;
        // Special case for NBA
        if (inAssignDly) {
            // Put it in a fork so it doesn't block
            // Could already be the only thing directly under a fork, reuse that if possible
            AstFork* forkp = !nodep->nextp() ? VN_CAST(nodep->firstAbovep(), Fork) : nullptr;
            if (!forkp) {
                forkp = new AstFork{flp, "", nullptr};
                forkp->joinType(VJoinType::JOIN_NONE);
            }
            if (!m_underProcedure) {
                // If it's in a function, it won't be handled by V3Delayed
                // Put it behind an additional named event that gets triggered in the NBA region
                AstEventControl* const nbaEventControlp = createNbaEventControl(flp);
                AstAssign* const trigAssignp = createNbaEventTriggerAssignment(flp);
                nodep->replaceWith(trigAssignp);
                trigAssignp->addNextHere(nbaEventControlp);
                nbaEventControlp->addStmtsp(nodep);
                insertBeforep = forkp;
                if (!controlp) controlp = nbaEventControlp;
            }
            controlp->replaceWith(forkp);
            forkp->addStmtsp(controlp);
        }
        UASSERT_OBJ(nodep, controlp, "Assignment should have timing control");
        addCLocalScope(flp, insertBeforep);
        // Function for replacing values with intermediate variables
        const auto replaceWithIntermediate = [&](AstNodeExpr* const valuep,
                                                 const std::string& name) {
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
        AstDelay* const netDelayp = getLhsNetDelayRecurse(nodep->lhsp());
        if (!netDelayp && !nodep->timingControlp()) return;
        // This assignment will be converted to an always. In some cases this may generate an
        // UNOPTFLAT, e.g.: assign #1 clk = ~clk. We create a temp var for the LHS of this
        // assign, to disable the UNOPTFLAT warning for it.
        // TODO: Find a way to do this without introducing this var. Perhaps make
        // V3SchedAcyclic recognize awaits and prevent it from treating this kind of logic as
        // cyclic
        AstNodeExpr* const lhsp = nodep->lhsp()->unlinkFrBack();
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
    void visit(AstWaitFork* nodep) override {
        AstCExpr* const exprp = new AstCExpr{nodep->fileline(), "vlProcess->completedFork()", 1};
        exprp->pure(false);
        AstWait* const waitp = new AstWait{nodep->fileline(), exprp, nullptr};
        nodep->replaceWith(waitp);
        VL_DO_DANGLING(nodep->deleteTree(), nodep);
    }
    void visit(AstWait* nodep) override {
        // Wait on changed events related to the vars in the wait statement
        FileLine* const flp = nodep->fileline();
        AstNode* const stmtsp = nodep->stmtsp();
        if (stmtsp) stmtsp->unlinkFrBackWithNext();
        AstNodeExpr* const condp = V3Const::constifyEdit(nodep->condp()->unlinkFrBack());
        auto* const constp = VN_CAST(condp, Const);
        if (constp) {
            if (constp->isZero()) {
                // We have to await forever instead of simply returning in case we're deep in a
                // callstack
                AstCExpr* const foreverp = new AstCExpr{flp, "VlForever{}", 0, true};
                foreverp->dtypeSetVoid();  // TODO: this is sloppy but harmless
                AstCAwait* const awaitp = new AstCAwait{flp, foreverp};
                awaitp->dtypeSetVoid();
                nodep->replaceWith(awaitp->makeStmt());
                if (stmtsp) VL_DO_DANGLING(stmtsp->deleteTree(), stmtsp);
                VL_DO_DANGLING(condp->deleteTree(), condp);
            } else {
                nodep->v3fatalSrc("constant wait should have been removed in "
                                  "TimingSuspendableVisitor::visit(AstWait)");
            }
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
            // We are using a global sentree, so we cannot use ET_TRUE, as that could lead to the
            // active region never converging. Because of this, we need to use ET_CHANGED in a
            // loop.
            AstEventControl* const controlp = new AstEventControl{
                flp,
                new AstSenTree{
                    flp, new AstSenItem{flp, VEdgeType::ET_CHANGED, condp->cloneTree(false)}},
                nullptr};
            controlp->user2(true);  // Commit immediately
            AstWhile* const loopp = new AstWhile{flp, new AstLogNot{flp, condp}, controlp};
            if (stmtsp) AstNode::addNext<AstNode, AstNode>(loopp, stmtsp);
            nodep->replaceWith(loopp);
        }
        VL_DO_DANGLING(nodep->deleteTree(), nodep);
    }
    void visit(AstBegin* nodep) override {
        VL_RESTORER(m_procp);
        m_procp = nodep;
        if (hasFlags(nodep, T_HAS_PROC)) nodep->setNeedProcess();
        iterateChildren(nodep);
    }
    void visit(AstFork* nodep) override {
        if (nodep->user1SetOnce()) return;
        v3Global.setUsesTiming();
        // Create a unique name for this fork
        nodep->name("__Vfork_" + cvtToStr(++m_forkCnt));
        unsigned idx = 0;  // Index for naming begins
        AstNode* stmtp = nodep->stmtsp();
        // Put each statement in a begin
        while (stmtp) {
            if (!VN_IS(stmtp, Begin)) {
                auto* const beginp = new AstBegin{stmtp->fileline(), "", nullptr};
                if (hasFlags(stmtp, T_HAS_PROC)) addFlags(beginp, T_HAS_PROC);
                stmtp->replaceWith(beginp);
                beginp->addStmtsp(stmtp);
                stmtp = beginp;
            }
            auto* const beginp = VN_AS(stmtp, Begin);
            stmtp = beginp->nextp();
            iterate(beginp);
            // Even if we do not find any awaits, we cannot simply inline the process here, as new
            // awaits could be added later.
            // Name the begin (later the name will be used for a new function)
            beginp->name(nodep->name() + "__" + cvtToStr(idx++));
        }
        if (!nodep->joinType().joinNone()) makeForkJoin(nodep);
    }

    //--------------------
    void visit(AstVar*) override {}  // Accelerate
    void visit(AstNode* nodep) override { iterateChildren(nodep); }

public:
    // CONSTRUCTORS
    explicit TimingControlVisitor(AstNetlist* nodep)
        : m_netlistp{nodep} {
        iterate(nodep);
    }
    ~TimingControlVisitor() override = default;
};

//######################################################################
// Timing class functions

void V3Timing::timingAll(AstNetlist* nodep) {
    UINFO(2, __FUNCTION__ << ": " << endl);
    TimingSuspendableVisitor susVisitor{nodep};
    if (v3Global.usesTiming()) TimingControlVisitor{nodep};
    V3Global::dumpCheckGlobalTree("timing", 0, dumpTreeEitherLevel() >= 3);
}
