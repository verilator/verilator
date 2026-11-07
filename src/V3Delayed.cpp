// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Lower non-blocking assignments (NBAs)
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
// V3Delayed's Transformations:
//
// Convert AstAssignDly ('<=') and non-blocking AstFireEvent ('->>') into
// temporaries and specially scheduled blocks.
// For the Pre/Post scheduling semantics, see V3OrderGraph.
//
// It is assumed and required in this pass that each NBA updates at
// most one variable. Earlier passes should have ensured this.
//
// There are several "Schemes" we can choose from for implementing a
// non-blocking update.
//
// The various Schemes have different costs and guarantees. Efficient
// schemes only guarantee correct behaviour e.g. if the location of
// the NBA is statically known relative to other NBAs and blocking writes.
//
// Each variable that is the target of an NBA needs to choose a scheme, which
// is used for all NBAs targeting that variable. This necessitates a global
// analysis of all code, recording NBAs, before the scheme can be chosen.
//
// Code is classified into 4 classes, based on the process that may execute it:
// - Combinational logic: processes sensitive to the values they read, such as
//   always_comb, 'always @*' and continuous assignments. Ordered by V3Order.
// - Clocked logic: processes triggered by the events explicitly listed in
//   their sensitivity list, such as clock edges. Ordered by V3Order.
// - Unordered code: suspendable processes and the branches of forks. They are
//   resumed (executed) outside of code ordered by V3Order. Hence 'unordered'.
// - Init code: static, initial and final blocks that do not suspend. They
//   run outside the eval loop.
// Furthermore, any process may contain calls to non-inlined functions. This
// means an NBA in such a function may be executed by different classes of logic.
//
// NBAs in combinational logic cannot be supported. These have either been
// converted to blocking assignments earlier in V3Active with a COMBDLY warning,
// or will be rejected in this pass with a COMBDLYCALL error if performed by a
// non-inlined function which is called from combinational logic.
//
// For the choice of the correct scheme, it is also necessary to know if the
// target of an NBA also has other blocking writes also targeting it.
//
// The algorithm proceeds in 3 steps, each implemented by a class.
// 1. DelayedRecord gathers all non-blocking assignments (NBAs) in the whole
//    design, without changing the tree. It notes the usage context of
//    variables updated by these NBAs, and builds the call graph of the
//    processes and non-inlined functions, with the writes in each.
// 2. DelayedAnalysis analyses the call graph, to find the functions that
//    may execute an NBA, and the classes of logic they are part of. Then for
//    each variable that is the target of an NBA, it decides which of the possible
//    conversion schemes to use.
// 3. DelayedRewrite converts each NBA gathered in step 1, based on the
//    scheme selected in step 2. This is implemented in the
//    'prepare*'/'convert*' methods. The 'prepare*' methods do the parts
//    common for all NBAs updating the given variable. The 'convert*'
//    methods then convert each NBA site separately.
//
// The possible NBA Schemes:
// "Shadow variable" scheme. Used for target variables in ordered code
// (clocked logic) that have no blocking writes, other than unpacked arrays
// updated only by element:
//   LHS <= RHS;
// is converted to:
//  - Add new "Pre-scheduled" logic:
//      __Vdly__LHS = LHS;
//  - In the original logic, replace the target variable 'LHS' with '__Vdly__LHS' variables:
//      __Vdly__LHS = RHS;
//  - Add new "Post-scheduled" logic:
//      LHS = __Vdly__LHS;
//
// "Shadow variable masked" scheme. Similar to the "Shadow variable" scheme,
// but allows for both blocking and non-blocking updates of packed target
// variables:
//   LHS[Index] <= RHS;
//   When there is also LHS[SomeNonOverlappingIndex] = RHS2;
// is converted to:
//  - In the original logic, replace the AstAssignDly with:
//      __Vdly__LHS[Index] = RHS;
//      __Vdly_Mask__LHS[Index] = '1;
//  - Add new "Post-scheduled" logic:
//      LHS = (__Vdly__LHS & __Vdly_Mask__LHS) | (LHS & ~__Vdly_Mask__LHS);
//      __Vdly_Mask__LHS = '0;
//
// "Shared flag" scheme. Used for unpacked arrays of basic or packed elements
// in ordered code, updated only by element, and not in a loop:
//   LHS[idxa][idxb] <= RHS
// is converted to:
//  - Add new "Pre-scheduled" logic:
//      __Vdly_Set__LHS = 0;
//  - In the original logic, replace the AstAssignDly with:
//      __Vdly_Set__LHS = 1;
//      __Vdly_Dim0__LHS = idxa;
//      __Vdly_Dim1__LHS = idxb;
//      __Vdly_Val__LHS = RHS;
//  - Add new "Post-scheduled" logic:
//      if (__Vdly_Set__LHS) LHS[__Vdly_Dim0__LHS][__Vdly_Dim1__LHS] = __Vdly_Val__LHS;
// Multiple consecutive NBAs of compatible form can share the same __Vdly_Set* flag
//
// "Generic" scheme is the most general, and uses a queue of closures, which
// when committed performs the update to the target variable in the order they were
// enqueued. This always guarantees NBAs are committed in the order the NBA statements
// were executed in the program. Closure structures are allocated via a memory pool:
//   LHS[idxa] <= RHS
// is converted to:
//  - In the original logic, replace the AstAssignDly with an AstNbaEnqueue:
//      closure = __VnbaClosurePool_M.allocate();
//      closure.m_funcp = __VnbaClosureFunc_N;
//      closure.val0 = RHS;
//      closure.val1 = idxa;
//      queue.enqueue(&closure);
//  - A new function is added, which executes the update:
//      __VnbaClosureFunc_N(closure) {
//        LHS[closure.val1] = closure.val0;
//        __VnbaClosurePool_M.release(closure);
//      }
//  - Add new "Post-scheduled" logic, committing the queue:
//      queue.commit();
//    This calls the functions of the closures in the order they were enqueued.
//
// There are two Generic schemes, both of which use a queue of closures, the
// difference is which queue is used.
//
// The "GenericLocal" scheme uses a queue specific to the target variable.
// Used for ordered logic where the other schemes cannot capture the update. E.g.:
// - arrays updated in a loop (iterations are not statically known)
// - arrays with elements of compound types (LHS of NBA can be an arbitrary expression)
// - non-packed variables also updated by blocking assignments (only the actual
//   components assigned by an NBA in the current eval must be updated)
// - non-blocking event trigger ('->>') (update is a compound statement)
//
// The "GenericGlobal" scheme uses a single global queue, shared by all
// variables using the scheme. Used for all variables updated by NBAs outside
// clocked logic: in unordered code, init code, or non-inlined functions. Also
// for members updated through a virtual interface or class handle, where the
// target cannot be statically resolved, and for the variables such a handle
// may refer to that are also updated directly.
//
// Use of the GenericGlobal scheme is conservative in some cases, and it
// would be possible to use a separate queue for each target known not to
// alias with other targets through virtual interface or class handle. This
// is a potential future optimization.
//
//*************************************************************************

#include "V3PchAstNoMT.h"  // VL_MT_DISABLED_CODE_UNIT

#include "V3Delayed.h"

#include "V3AstUserAllocator.h"
#include "V3CallTargets.h"
#include "V3Const.h"
#include "V3EmitCBase.h"
#include "V3Graph.h"
#include "V3LinkLValue.h"
#include "V3SharedTmps.h"
#include "V3Stats.h"

#include <unordered_set>

VL_DEFINE_DEBUG_FUNCTIONS;

//######################################################################
// 'DelayedBase' is a mixin class for the steps in this pass, it holds
// a reference to the State shared between the steps. It is otherwise
// stateless and exists only to help separate the code of the steps into
// logically separate classes.

class DelayedBase VL_NOT_FINAL {
protected:
    // TYPES

    // The various NBA conversion schemes
    enum class Scheme : uint8_t {
        Undecided = 0,
        ShadowVar,
        ShadowVarMasked,
        FlagShared,
        GenericLocal,
        GenericGlobal
    };

    // Vertex of the call graph, which is bipartite: code has edges to the calls it makes, and a
    // call has edges to the non-inlined functions it may call (see addEdge)
    class Vertex VL_NOT_FINAL : public V3GraphVertex {
        VL_RTTI_IMPL(Vertex, V3GraphVertex)
    public:
        std::unordered_set<const AstNodeStmt*> m_nbaps;  // The NBAs it may execute

    protected:
        explicit Vertex(V3Graph* graphp)
            : V3GraphVertex{graphp} {}
    };
    class CallVertex final : public Vertex {
        VL_RTTI_IMPL(CallVertex, Vertex)
    public:
        AstNodeCCall* const m_callp;  // The call, nullptr for DPI imports calling DPI exports
        CallVertex(V3Graph* graphp, AstNodeCCall* callp)
            : Vertex{graphp}
            , m_callp{callp} {}
    };
    // Code, which is part of some classes of logic: combinational logic, which only has blocking
    // writes (see V3Active), clocked logic, unordered code, which V3Order does not schedule:
    // suspendable processes and forks, and init code, which runs outside the eval loop: static,
    // initial and final blocks
    class CodeVertex VL_NOT_FINAL : public Vertex {
        VL_RTTI_IMPL(CodeVertex, Vertex)
    public:
        std::vector<AstNodeExpr*> m_wrps;  // Blocking write refs (AstVarRef or AstMemberSel)
        bool m_comb = false;  // Part of combinational logic
        bool m_clocked = false;  // Part of clocked logic
        bool m_unordered = false;  // Part of unordered code
        bool m_init = false;  // Part of init code

    protected:
        explicit CodeVertex(V3Graph* graphp)
            : Vertex{graphp} {}
    };
    // A process
    class ProcVertex final : public CodeVertex {
        VL_RTTI_IMPL(ProcVertex, CodeVertex)
        // True if what 'procp' writes cannot legally be written by other processes,
        // per the standard: IEEE 1800-2023 6.5, 9.2.2.2-9.2.2.4
        static bool isExclusive(const AstNodeProcedure* procp) {
            const AstAlways* const alwaysp = VN_CAST(procp, Always);
            return alwaysp && alwaysp->keyword() != VAlwaysKwd::ALWAYS;
        }

    public:
        const AstSenTree* const m_senTreep;  // Sensitivities of the AstActive it is under
        const bool m_exclusive;  // What it writes cannot legally be written by other processes
        ProcVertex(V3Graph* graphp, const AstSenTree* senTreep, const AstNodeProcedure* procp)
            : CodeVertex{graphp}
            , m_senTreep{senTreep}
            , m_exclusive{isExclusive(procp)} {
            if (procp->isSuspendable()) {
                m_unordered = true;
            } else {
                m_comb = senTreep->hasCombo();
                m_clocked = senTreep->hasClocked();
                m_init = !m_comb && !m_clocked;  // Static, initial or final block
            }
        }
    };
    // The branches of a fork, which are processes of their own
    class ForkVertex final : public CodeVertex {
        VL_RTTI_IMPL(ForkVertex, CodeVertex)
    public:
        explicit ForkVertex(V3Graph* graphp)
            : CodeVertex{graphp} {
            m_unordered = true;
        }
    };
    // A non-inlined function, part of the logic calling it
    class FuncVertex final : public CodeVertex {
        VL_RTTI_IMPL(FuncVertex, CodeVertex)
    public:
        explicit FuncVertex(V3Graph* graphp)
            : CodeVertex{graphp} {}
    };

    // All info associated with an NBA target during the pass
    class TargetInfo final {
    public:
        bool m_whole = false;  // Used on LHS of NBA directly via VarRef
        bool m_inLoop = false;  // Used on LHS of NBA in a loop
        bool m_event = false;  // Fired by a non-blocking event trigger ('->>')
        bool m_nonClocked = false;  // Used on LHS of NBA in init or unordered code, or a function
        bool m_mixed = false;  // Also written by blocking assignments outside init code
        Scheme m_scheme = Scheme::Undecided;  // Conversion scheme to use for this variable
        std::vector<AstNodeExpr*> m_nbaRefps;  // NBA write references
        std::vector<AstNodeExpr*> m_combBlkRefps;  // Racy blocking write references in comb. logic

    private:
        // Combined sensitivities of all NBAs targeting this variable
        AstSenTree* m_senTreep = nullptr;

        // Union of stuff needed for the various schemes - use accessors below!
        union {
            struct {  // Stuff needed for Scheme::ShadowVar
                AstVarScope* vscp;  // The shadow variable
            } m_shadowVariableKit;
            struct {  // Stuff needed for Scheme::ShadowVarMasked
                AstVarScope* vscp;  // The shadow variable
                AstVarScope* maskp;  // The mask variable
            } m_shadowVarMaskedKit;
            struct {  // Stuff needed for Scheme::FlagShared
                AstActive* activep;  // The active block for the Pre/Post logic
                AstAlwaysPost* postp;  // The post block for commiting results
                AstVarScope* commitFlagp;  // The commit flag variable, for reuse
                AstIf* commitIfp;  // The previous if statement for committing, for reuse
            } m_flagSharedKit;
            struct {  // Stuff needed for Scheme::GenericLocal/Scheme::GenericGlobal
                AstVarScope* queueVscp;  // The queue the closures are enqueued to
            } m_genericKit;
        } m_kitUnion;

    public:
        TargetInfo() = default;
        ~TargetInfo() {
            // Not linked if there was an error, or with Scheme::GenericGlobal, which copies it
            if (m_senTreep && !m_senTreep->backp()) {
                VL_DO_DANGLING(m_senTreep->deleteTree(), m_senTreep);
            }
        }
        // Accessors for the above union fields
        auto& shadowVariableKit() {
            UASSERT(m_scheme == Scheme::ShadowVar, "Inconsistent Scheme");
            return m_kitUnion.m_shadowVariableKit;
        }
        auto& shadowVarMaskedKit() {
            UASSERT(m_scheme == Scheme::ShadowVarMasked, "Inconsistent Scheme");
            return m_kitUnion.m_shadowVarMaskedKit;
        }
        auto& flagSharedKit() {
            UASSERT(m_scheme == Scheme::FlagShared, "Inconsistent Scheme");
            return m_kitUnion.m_flagSharedKit;
        }
        auto& genericKit() {
            UASSERT(m_scheme == Scheme::GenericLocal || m_scheme == Scheme::GenericGlobal,
                    "Inconsistent Scheme");
            return m_kitUnion.m_genericKit;
        }

        // Accessor
        AstSenTree* senTreep() const { return m_senTreep; }

        // Add sensitivities
        void addSensitivity(AstSenItem* nodep) {
            if (!m_senTreep) m_senTreep = new AstSenTree{nodep->fileline(), nullptr};
            // Add a copy of each term
            m_senTreep->addSensesp(nodep->cloneTree(true));
            // Remove duplicates
            V3Const::constifyExpensiveEdit(m_senTreep);
        }
        // cppcheck-suppress constParameterPointer
        void addSensitivity(AstSenTree* nodep) { addSensitivity(nodep->sensesp()); }
    };

    // Data required to lower an NBA later
    struct NBA final {
        AstNodeStmt* nodep;  // The AstAssignDly, or the non-blocking AstFireEvent
        AstNodeExpr* targetp;  // The AstVarRef it updates, or the AstMemberSel via a handle
        AstScope* scopep;  // The scope the NBA is in
    };

public:
    // The state of the pass, shared by the steps
    class State final {
        // NODE STATE
        //  AstVarScope::user1p()   -> TargetInfo via targetInfo
        //  AstVar::user1p()        -> TargetInfo via targetInfo, of a Var updated via a handle
        const VNUser1InUse m_user1InUse;

    public:
        AstUser1Allocator<AstNode, TargetInfo> targetInfo;  // See TargetInfo
        std::vector<AstVarScope*> nbaVscps;  // Variables updated by NBAs
        std::vector<AstVar*> nbaVarps;  // Members updated by NBAs via a handle, in any instance
        // Variables of each member of an interface, in all instances
        std::unordered_map<const AstVar*, std::vector<AstVarScope*>> ifaceVscps;
        std::vector<NBA> nbas;  // NBAs to lower
        V3Graph graph;  // The call graph
    };

protected:
    // STATE
    State& m_state;  // The state of the pass

    // CONSTRUCTORS
    explicit DelayedBase(State& state)
        : m_state{state} {}
};

//######################################################################
// Record the NBAs, writes and calls, without changing the tree

class DelayedRecord final : public VNVisitorConst, public DelayedBase {
    // NODE STATE
    //  AstVarScope::user2()    -> bool: True if seen an NBA to this target before
    //  AstVar::user2()         -> bool: True if seen an NBA to this target before
    //  AstCFunc::user3p()      -> FuncVertex*: FuncVertex of the function
    const VNUser2InUse m_user2InUse;
    const VNUser3InUse m_user3InUse;

    // STATE
    // To get the functions a virtual call may call
    const std::unique_ptr<V3CallTargets> m_callTargetsp = V3CallTargets::build();

    // Calls of all DPI exports, made by context DPI imports
    CallVertex* const m_dpiExportCallVtxp = new CallVertex{&m_state.graph, nullptr};

    // STATE - for current visit position (use VL_RESTORER)
    AstScope* m_scopep = nullptr;  // Current scope
    AstActive* m_activep = nullptr;  // Current activate
    CodeVertex* m_vtxp = nullptr;  // Vertex of the current process or function
    bool m_inLoop = false;  // True in loops
    bool m_inTarget = false;  // True under the target of an NBA or event trigger

    // METHODS

    // Get the call graph vertex of the given function
    FuncVertex* funcVtxp(AstCFunc* funcp) {
        if (!funcp->user3p()) funcp->user3p(new FuncVertex{&m_state.graph});
        return funcp->user3u().to<FuncVertex*>();
    }

    // Add an edge of the call graph
    void addEdge(CodeVertex* fromp, CallVertex* top) {
        new V3GraphEdge{&m_state.graph, fromp, top, 1};
    }
    void addEdge(CallVertex* fromp, FuncVertex* top) {
        new V3GraphEdge{&m_state.graph, fromp, top, 1};
    }

    // The expression identifying the target of the LValue expression 'lhsp'
    static AstNodeExpr* targetRefp(AstNodeExpr* lhsp) {
        while (true) {
            if (AstVarRef* const refp = VN_CAST(lhsp, VarRef)) {
                return refp;
            } else if (AstMemberSel* const selp = VN_CAST(lhsp, MemberSel)) {
                return selp;
            } else if (const AstSel* const selp = VN_CAST(lhsp, Sel)) {
                lhsp = selp->fromp();
            } else if (const AstNodeSel* const selp = VN_CAST(lhsp, NodeSel)) {
                lhsp = selp->fromp();
            } else if (const AstStructSel* const selp = VN_CAST(lhsp, StructSel)) {
                lhsp = selp->fromp();
            } else {
                lhsp->v3fatalSrc("Unexpected LHS expression of NBA");
            }
        }
    }

    // Record the NBA 'nodep' updating 'lhsp'
    void recordNba(AstNodeStmt* nodep, AstNodeExpr* lhsp) {
        UASSERT_OBJ(m_vtxp, nodep, "<= not under sensitivity block");
        UASSERT_OBJ(m_scopep, nodep, "<= not under scope");
        UASSERT_OBJ(!m_vtxp->m_comb, nodep, "V3Active failed to convert NBA in comb process");

        // Grab the target reference of this NBA
        AstNodeExpr* const nbaRefp = targetRefp(lhsp);

        // Get the target info structure, record target on first encounter
        TargetInfo& targetInfo = [&]() -> TargetInfo& {
            if (AstVarRef* const refp = VN_CAST(nbaRefp, VarRef)) {
                AstVarScope* const vscp = refp->varScopep();
                TargetInfo& info = m_state.targetInfo(vscp);
                if (!vscp->user2SetOnce()) m_state.nbaVscps.emplace_back(vscp);
                return info;
            }
            if (AstMemberSel* const selp = VN_CAST(nbaRefp, MemberSel)) {
                AstVar* const varp = selp->varp();
                TargetInfo& info = m_state.targetInfo(varp);
                if (!varp->user2SetOnce()) m_state.nbaVarps.emplace_back(varp);
                return info;
            }
            v3fatalSrc("Unexpected NBA target");
        }();

        // Note usage context
        targetInfo.m_whole |= VN_IS(lhsp, VarRef);  // At least one whole access
        targetInfo.m_inLoop |= m_inLoop;
        targetInfo.m_event |= VN_IS(nodep, FireEvent);

        // Record the sensitivities updating this variable, or that it's updated outside them
        const ProcVertex* const procVtxp = m_vtxp->cast<ProcVertex>();
        if (procVtxp && procVtxp->m_clocked) {
            targetInfo.addSensitivity(m_activep->sentreep());
        } else {
            targetInfo.m_nonClocked = true;
        }

        // Record the NBA to the vertex for later analysis
        m_vtxp->m_nbaps.insert(nodep);
        // Record the NBA for later conversion
        m_state.nbas.push_back({nodep, nbaRefp, m_scopep});

        // Record write reference
        targetInfo.m_nbaRefps.push_back(nbaRefp);
    }

    // Visit the target of an NBA or event trigger, for calls V3LiftExpr did not lift, those in a
    // 'with' clause. What it writes is the target, not a blocking write.
    void iterateTarget(AstNodeExpr* nodep) {
        VL_RESTORER(m_inTarget);
        m_inTarget = true;
        iterateConst(nodep);
    }

    // VISITORS
    void visit(AstScope* nodep) override {
        UASSERT_OBJ(!m_scopep, nodep, "Should not nest");
        VL_RESTORER(m_scopep);
        m_scopep = nodep;
        iterateChildrenConst(nodep);
    }
    void visit(AstVarScope* nodep) override {
        // A virtual interface may select any instance of an interface, record for consideration
        const AstIface* const ifacep = VN_CAST(m_scopep->modp(), Iface);
        if (ifacep && ifacep->hasVirtualRef()) m_state.ifaceVscps[nodep->varp()].push_back(nodep);
    }
    void visit(AstActive* nodep) override {
        UASSERT_OBJ(!m_activep, nodep, "Should not nest");
        VL_RESTORER(m_activep);
        m_activep = nodep;
        iterateChildrenConst(nodep);
    }

    void visit(AstNodeProcedure* nodep) override {
        VL_RESTORER(m_vtxp);
        m_vtxp = new ProcVertex{&m_state.graph, m_activep->sentreep(), nodep};
        iterateChildrenConst(nodep);
    }
    void visit(AstCoverToggle*) override {
        // Toggle coverage only writes its own variables, which are not updated by NBAs, ignored
    }
    void visit(AstCFunc* nodep) override {
        VL_RESTORER(m_vtxp);
        FuncVertex* const vtxp = funcVtxp(nodep);
        if (nodep->dpiImportPrototype() && nodep->dpiContext()) addEdge(vtxp, m_dpiExportCallVtxp);
        if (nodep->dpiExportImpl()) addEdge(m_dpiExportCallVtxp, vtxp);
        m_vtxp = vtxp;
        iterateChildrenConst(nodep);
    }
    void visit(AstFork* nodep) override {
        VL_RESTORER(m_vtxp);
        m_vtxp = new ForkVertex{&m_state.graph};
        UASSERT_OBJ(!nodep->declsp(), nodep, "Should have been moved by V3Begin");
        UASSERT_OBJ(!nodep->stmtsp(), nodep, "Should have been moved by V3Begin");
        iterateChildrenConst(nodep);
    }

    void visit(AstLoop* nodep) override {
        VL_RESTORER(m_inLoop);
        m_inLoop = true;
        iterateChildrenConst(nodep);
    }

    void visit(AstNodeCCall* nodep) override {
        iterateChildrenConst(nodep);
        // Made by the current process or function
        UASSERT_OBJ(m_vtxp, nodep, "Call not in a process or function");
        CallVertex* const callVtxp = new CallVertex{&m_state.graph, nodep};
        addEdge(m_vtxp, callVtxp);
        // Add edges to all functions that may be called, including through virtual calls
        for (AstCFunc* const cfuncp : m_callTargetsp->getTargets(nodep)) {
            addEdge(callVtxp, funcVtxp(cfuncp));
        }
    }

    void visit(AstAssignDly* nodep) override {
        recordNba(nodep, nodep->lhsp());
        iterateTarget(nodep->lhsp());
        iterateConst(nodep->rhsp());
    }
    void visit(AstFireEvent* nodep) override {
        UASSERT_OBJ(v3Global.hasEvents(), nodep, "Inconsistent");
        // Blocking event trigger does not assign the event, so can't race with an NBA, no need
        // to record it for BLKANDNBLK check.
        if (nodep->isDelayed()) recordNba(nodep, nodep->operandp());
        iterateTarget(nodep->operandp());
    }

    void visit(AstVarRef* nodep) override {
        // Only care about write refs, other than of NBA targets
        if (!nodep->access().isWriteOrRW() || m_inTarget) return;
        // Record write reference
        UASSERT_OBJ(m_vtxp, nodep, "Write not in a process or function");
        m_vtxp->m_wrps.push_back(nodep);
    }
    void visit(AstMemberSel* nodep) override {
        iterateChildrenConst(nodep);
        // Only care about write refs, other than of NBA targets
        if (!nodep->access().isWriteOrRW() || m_inTarget) return;
        // Record write reference
        UASSERT_OBJ(m_vtxp, nodep, "Write not in a process or function");
        m_vtxp->m_wrps.push_back(nodep);
    }

    // Post logic needs no conversion
    void visit(AstAlwaysPost*) override {}
    // Sensitivity lists are not part of any process or function.
    // They may contain writes we failed to error on/fix up earlier, so ignore them
    void visit(AstSenTree*) override {}

    //--------------------
    void visit(AstNode* nodep) override { iterateChildrenConst(nodep); }

    // CONSTRUCTORS
    DelayedRecord(State& state, AstNetlist* netlistp)
        : DelayedBase{state} {
        iterateConst(netlistp);
    }

public:
    static void apply(State& state, AstNetlist* netlistp) { DelayedRecord{state, netlistp}; }
};

//######################################################################
// Decide how to convert the NBAs, analysing all the recorded info

class DelayedAnalysis final : public DelayedBase {
    // METHODS

    // Propagate the reachable NBAs up the graph: a caller may execute those of its callees
    void propagateNbas() {
        std::vector<std::pair<const Vertex*, const AstNodeStmt*>> workList;
        for (const V3GraphVertex& vtx : m_state.graph.vertices()) {
            const Vertex* const vtxp = vtx.as<Vertex>();
            for (const AstNodeStmt* const nbap : vtxp->m_nbaps) {
                workList.emplace_back(vtxp, nbap);
            }
        }
        while (!workList.empty()) {
            const auto& item = workList.back();
            const Vertex* const vtxp = item.first;
            const AstNodeStmt* const nbap = item.second;
            workList.pop_back();
            for (const V3GraphEdge& edge : vtxp->inEdges()) {
                Vertex* const callerp = edge.fromp()->as<Vertex>();
                if (callerp->m_nbaps.insert(nbap).second) workList.emplace_back(callerp, nbap);
            }
        }
    }

    // Propagate the kind of logic that can reach a function, down the graph
    void propagateKind() {
        std::vector<const CodeVertex*> workList;
        for (const V3GraphVertex& vtx : m_state.graph.vertices()) {
            const CodeVertex* const vtxp = vtx.cast<CodeVertex>();
            if (vtxp && (vtxp->m_comb || vtxp->m_clocked || vtxp->m_unordered || vtxp->m_init)) {
                workList.push_back(vtxp);
            }
        }
        while (!workList.empty()) {
            const CodeVertex* const callerp = workList.back();
            workList.pop_back();
            for (const V3GraphEdge& caller2Call : callerp->outEdges()) {
                const CallVertex* const callp = caller2Call.top()->as<CallVertex>();
                for (const V3GraphEdge& call2Callee : callp->outEdges()) {
                    FuncVertex* const calleep = call2Callee.top()->as<FuncVertex>();
                    const bool newComb = callerp->m_comb && !calleep->m_comb;
                    const bool newClocked = callerp->m_clocked && !calleep->m_clocked;
                    const bool newUnordered = callerp->m_unordered && !calleep->m_unordered;
                    const bool newInit = callerp->m_init && !calleep->m_init;
                    if (!newComb && !newClocked && !newUnordered && !newInit) continue;
                    calleep->m_comb |= callerp->m_comb;
                    calleep->m_clocked |= callerp->m_clocked;
                    calleep->m_unordered |= callerp->m_unordered;
                    calleep->m_init |= callerp->m_init;
                    workList.push_back(calleep);
                }
            }
        }
    }

    // NBAs from combinational logic are not supported. V3Active already rejected/converted
    // those directly in combinational logic, but there might still be NBAs in functions
    // called from combinational logic. Report these as COMBDLYCALL at the call sites.
    void reportNbasFromComb() {
        for (const V3GraphVertex& vtx : m_state.graph.vertices()) {
            const ProcVertex* const procVtxp = vtx.cast<ProcVertex>();
            if (!procVtxp || !procVtxp->m_comb) continue;

            for (const V3GraphEdge& edge : procVtxp->outEdges()) {
                const CallVertex* const callVtxp = edge.top()->as<CallVertex>();
                if (callVtxp->m_nbaps.empty()) continue;

                // Report all NBAs the call may execute, in source order
                std::vector<const AstNodeStmt*> nbaps{callVtxp->m_nbaps.begin(),
                                                      callVtxp->m_nbaps.end()};
                std::sort(nbaps.begin(), nbaps.end(), [](const AstNode* ap, const AstNode* bp) {
                    return ap->fileline()->operatorCompare(*bp->fileline()) < 0;
                });
                std::ostringstream locations;
                for (const AstNodeStmt* const nbap : nbaps) {
                    locations << nbap->warnOther()
                              << "... Location of reachable non-blocking assignment\n"
                              << nbap->warnContextSecondary();
                }
                AstNodeCCall* const callp = callVtxp->m_callp;
                callp->v3warn(COMBDLYCALL, "Unsupported: Non-blocking assignment in a function "
                                           "called from combinational logic\n"
                                               << callp->warnContextPrimary() << '\n'
                                               << locations.str());
            }
        }
    }

    // Note the blocking write 'refp' in 'vtxp' may update the NBA target of 'targetInfop', if any
    static void noteBlockingWrite(TargetInfo* targetInfop, const CodeVertex* vtxp,
                                  AstNodeExpr* refp) {
        if (!targetInfop) return;  // Not a target of an NBA
        targetInfop->m_mixed = true;
        // Only blocking writes in combinational logic are racy with respect to NBAs
        if (vtxp->m_comb) targetInfop->m_combBlkRefps.push_back(refp);
    }

    // Note the targets of NBAs also written by blocking assignments in combinational, clocked or
    // unordered code, which may run while the NBAs are pending. Those only in init code, which
    // runs outside the eval loop, are safe, and are skipped.
    void noteBlockingWrites() {
        // Need a map from AstVar to all TargetInfos associated with the corresponding AstVarScopes
        std::unordered_map<const AstVar*, std::vector<TargetInfo*>> var2TargetInfops;
        for (AstVarScope* const vscp : m_state.nbaVscps) {
            var2TargetInfops[vscp->varp()].push_back(&m_state.targetInfo(vscp));
        }
        for (const V3GraphVertex& vtx : m_state.graph.vertices()) {
            const CodeVertex* const vtxp = vtx.cast<CodeVertex>();
            if (!vtxp) continue;
            if (!vtxp->m_comb && !vtxp->m_clocked && !vtxp->m_unordered) continue;
            for (AstNodeExpr* const refp : vtxp->m_wrps) {
                if (const AstVarRef* const vrefp = VN_CAST(refp, VarRef)) {
                    noteBlockingWrite(m_state.targetInfo.tryGet(vrefp->varScopep()), vtxp, refp);
                    // It might be the instance of an AstVar that is updated via a MemberSel.
                    // Record unless no other process can legally write it by IEEE.
                    // The legality restriction is to avoid excessive warnings on common use cases
                    // where e.g. one interface instance is written directly, another through a
                    // virtual interface handle.
                    const ProcVertex* const procVtxp = vtxp->cast<ProcVertex>();
                    if (!procVtxp || !procVtxp->m_exclusive) {
                        noteBlockingWrite(m_state.targetInfo.tryGet(vrefp->varp()), vtxp, refp);
                    }
                } else if (const AstMemberSel* const selp = VN_CAST(refp, MemberSel)) {
                    noteBlockingWrite(m_state.targetInfo.tryGet(selp->varp()), vtxp, refp);
                    // The handle may select the variable of any instance
                    const auto it = var2TargetInfops.find(selp->varp());
                    if (it == var2TargetInfops.end()) continue;
                    for (TargetInfo* const targetInfop : it->second) {
                        noteBlockingWrite(targetInfop, vtxp, refp);
                    }
                } else {
                    refp->v3fatalSrc("Unexpected write reference");
                }
            }
        }
    }

    // Issue BLKANDNBLK error if it cannot be proven statically that the racy mixed blocking and
    // non-blocking assignments to a variable are to independent parts, as this cannot be
    // implemented safely.
    void checkMixedUsage(const AstNode* targetp) {
        const TargetInfo& targetInfo = m_state.targetInfo(targetp);

        // We only run this function on targets of NBAs, so there should be at least one...
        UASSERT_OBJ(!targetInfo.m_nbaRefps.empty(), targetp, "Did not record NBA write");

        // If the blocking assignments are in clocked or unordered logic, then we can safely
        // implement it (there is no race between clocked logic and post scheduled logic),
        // so need not error
        if (targetInfo.m_combBlkRefps.empty()) return;

        const AstVarScope* const vscp = VN_CAST(targetp, VarScope);
        const AstVar* const varp = vscp ? vscp->varp() : VN_AS(targetp, Var);
        const AstNodeDType* const dtypep = varp->dtypep()->skipRefp();
        const AstUnpackArrayDType* const arrayp = VN_CAST(dtypep, UnpackArrayDType);

        // If not a packed variable or unpacked array, warn here as we can't prove independence
        if (!dtypep->isIntegralOrPacked() && !arrayp) {
            const AstNodeExpr* const blkRefp = targetInfo.m_combBlkRefps.front();
            const AstNodeExpr* const nbaRefp = targetInfo.m_nbaRefps.front();
            targetp->v3warn(
                BLKANDNBLK,
                "Unsupported: Blocking and non-blocking assignments to same non-packed variable: "
                    << varp->prettyNameQ() << '\n'
                    << targetp->warnContextPrimary() << '\n'
                    << blkRefp->warnOther() << "... Location of blocking assignment\n"
                    << blkRefp->warnContextSecondary() << '\n'
                    << nbaRefp->warnOther() << "... Location of nonblocking assignment\n"
                    << nbaRefp->warnContextSecondary());
            return;
        }

        struct Ref final {
            AstNodeExpr* m_refp;  // The reference
            int m_lo;  // Low end of the accessed range
            int m_hi;  // High end of the accessed range
        };

        // The ranges accessed by the given references. An element of an array is considered
        // accessed whole, even if only some of its bits are selected. This is imprecise,
        // but doing a proper static prefix check is complicated.
        const auto toRefs = [varp, arrayp](const std::vector<AstNodeExpr*>& refps) {
            // The parts written are bits of a packed variable, or elements of an array
            const int size = arrayp ? arrayp->elementsConst() : varp->width();

            std::vector<Ref> refs;
            for (AstNodeExpr* const refp : refps) {
                int lo = 0;
                int hi = size - 1;
                if (arrayp) {
                    if (const AstArraySel* const selp = VN_CAST(refp->backp(), ArraySel)) {
                        if (const AstConst* const idxp = VN_CAST(selp->bitp(), Const)) {
                            lo = hi = idxp->toSInt();
                        }
                    }
                } else if (const AstSel* const selp = VN_CAST(refp->backp(), Sel)) {
                    if (VN_IS(selp->lsbp(), Const)) {
                        lo = selp->lsbConst();
                        hi = selp->msbConst();
                    }
                }
                refs.push_back({refp, lo, hi});
            }
            return refs;
        };
        std::vector<Ref> blkRefs = toRefs(targetInfo.m_combBlkRefps);  // Blocking writes
        std::vector<Ref> nbaRefs = toRefs(targetInfo.m_nbaRefps);  // Non-blocking writes

        // We need to error if we can't prove the written parts are independent

        // Sort refs by interval
        const auto lessThanRef = [](const Ref& a, const Ref& b) {
            if (a.m_lo != b.m_lo) return a.m_lo < b.m_lo;
            return a.m_hi < b.m_hi;
        };
        std::stable_sort(blkRefs.begin(), blkRefs.end(), lessThanRef);
        std::stable_sort(nbaRefs.begin(), nbaRefs.end(), lessThanRef);
        // Iterate both vectors, checking for overlap
        auto bIt = blkRefs.begin();
        auto nIt = nbaRefs.begin();
        while (bIt != blkRefs.end() && nIt != nbaRefs.end()) {
            if (lessThanRef(*bIt, *nIt)) {
                if (nIt->m_lo <= bIt->m_hi) break;  // Stop on Overlap
                ++bIt;
            } else {
                if (bIt->m_lo <= nIt->m_hi) break;  // Stop on Overlap
                ++nIt;
            }
        }

        // If we found an overlapping range, then warn
        if (bIt != blkRefs.end() && nIt != nbaRefs.end()) {
            const Ref& blkRef = *bIt;
            const Ref& nbaRef = *nIt;
            const char* const partsp = arrayp ? "elements" : "bits";
            const char* const objectp = arrayp ? "unpacked array" : "packed variable";
            targetp->v3warn(BLKANDNBLK, "Unsupported: Blocking and non-blocking assignments to "
                                        "potentially overlapping "
                                            << partsp << " of same " << objectp << ": "
                                            << varp->prettyNameQ() << '\n'
                                            << targetp->warnContextPrimary() << '\n'
                                            << blkRef.m_refp->warnOther()
                                            << "... Location of blocking assignment (" << partsp
                                            << " [" << blkRef.m_hi << ":" << blkRef.m_lo << "])\n"
                                            << blkRef.m_refp->warnContextSecondary() << '\n'
                                            << nbaRef.m_refp->warnOther()
                                            << "... Location of nonblocking assignment (" << partsp
                                            << " [" << nbaRef.m_hi << ":" << nbaRef.m_lo << "])\n"
                                            << nbaRef.m_refp->warnContextSecondary());
        }
    }

    // Choose the NBA scheme used for the given variable.
    Scheme chooseScheme(const AstVarScope* vscp, const TargetInfo& targetInfo) {
        UASSERT_OBJ(targetInfo.m_scheme == Scheme::Undecided, vscp, "NBA scheme already decided");

        // NBAs outside clocked logic need to stay in program order, so use generic
        if (targetInfo.m_nonClocked) return Scheme::GenericGlobal;
        // NBAs to a variable also updated via a MemberSel use the global queue
        // to preserve program order
        if (m_state.targetInfo.tryGet(vscp->varp())) return Scheme::GenericGlobal;
        // Events fired by NBAs, also members of a struct, use generic, as the other schemes commit
        // values. They are rare and Generic means they need no special casing
        if (targetInfo.m_event) return Scheme::GenericLocal;

        const AstNodeDType* const dtypep = vscp->dtypep()->skipRefp();

        // Unpacked arrays, updated only element-wise have some more efficient schemes
        const AstUnpackArrayDType* const uaDTypep = VN_CAST(dtypep, UnpackArrayDType);
        if (uaDTypep && !targetInfo.m_whole) {
            // How many times a loop executes is not known, so must use a dynamic queue
            if (targetInfo.m_inLoop) return Scheme::GenericLocal;
            // Otherwise if an array of packed/basic elements, use the shared flag scheme
            if (uaDTypep->basicp()) return Scheme::FlagShared;
            // Finally use generic, which can handle any LHS expressions,
            // e.g. for arrays of structs updated member-wise
            return Scheme::GenericLocal;
        }

        // Other variables/unpacked arrays that are updated whole (array <= ...)
        if (targetInfo.m_mixed) {
            // When updated by both blocking and non-blocking assignments, those updates
            // must be ordered. For packed variables, the updates can be masked.
            if (dtypep->isIntegralOrPacked()) return Scheme::ShadowVarMasked;
            // Otherwise only the Generic scheme is safe to preserve program order
            return Scheme::GenericLocal;
        }

        // Variables only updated by non-blocking assignments use the simple
        // shadow variable scheme. This is by far the most common case.
        return Scheme::ShadowVar;
    }

    // CONSTRUCTORS
    explicit DelayedAnalysis(State& state)
        : DelayedBase{state} {
        // Analyze the call graph
        propagateNbas();
        propagateKind();

        // Report unsupported NBAs
        reportNbasFromComb();

        // Record blocking writes that might race with NBAs in ordered code
        noteBlockingWrites();

        // Report racy blocking writes
        for (AstVarScope* const vscp : m_state.nbaVscps) checkMixedUsage(vscp);
        for (AstVar* const varp : m_state.nbaVarps) checkMixedUsage(varp);

        // Choose the scheme for each variable
        // Targets updated via a MemberSel use the GenericGlobal scheme. This is the only one
        // that both respects program order and can capture arbitrary LHS expressions.
        for (AstVar* const varp : m_state.nbaVarps) {
            m_state.targetInfo(varp).m_scheme = Scheme::GenericGlobal;
        }
        // Targets updated directly via an AstVarRef have more choices
        for (AstVarScope* const vscp : m_state.nbaVscps) {
            TargetInfo& targetInfo = m_state.targetInfo(vscp);
            targetInfo.m_scheme = chooseScheme(vscp, targetInfo);
        }
    }

public:
    static void apply(State& state) { DelayedAnalysis{state}; }
};

//######################################################################
// Rewrite, converting the NBAs

class DelayedRewrite final : public VNDeleter, public DelayedBase {
    // STATE
    V3SharedTmps m_dlyTmps{"__Vdly", VVarType::BLOCKTEMP};  // Temporary variables
    AstNbaCommit* m_globalNbaCommitp = nullptr;  // Commit of the Scheme::GenericGlobal queue
    AstSenTree* m_globalNbaCommitSenTreep = nullptr;  // Sensitivities of m_globalNbaCommitp
    // Closure types, by the types of the values they capture
    std::map<std::vector<AstNodeDType*>, AstStructDType*> m_closureDTypeps;
    // Closure pools, by closure type and queue. Committing a queue releases its closures to their
    // pools, so a pool is only used with one queue, to be ordered by V3Order like that queue.
    std::map<std::pair<const AstStructDType*, const AstVarScope*>, AstVarScope*>
        m_closurePoolVscps;
    // Type of 'this' captured by closures, by class, so they can share closure types
    std::unordered_map<const AstClass*, AstClassRefDType*> m_thisDTypeps;
    size_t m_nClosureFuncs = 0;  // Number of closure functions, for unique names
    AstAssignDly* m_nextDlyp = nullptr;  // The nextp of the previous AstAssignDly
    AstVarScope* m_prevVscp = nullptr;  // The target of the previous AstAssignDly

    // STATE - Statistic tracking
    VDouble0 m_nSchemeShadowVar;  // Number of variables using Scheme::ShadowVar
    VDouble0 m_nSchemeShadowVarMasked;  // Number of variables using Scheme::ShadowVarMasked
    VDouble0 m_nSchemeFlagShared;  // Number of variables using Scheme::FlagShared
    VDouble0 m_nSchemeGenericLocal;  // Number of variables using Scheme::GenericLocal
    VDouble0 m_nSchemeGenericGlobal;  // Number of variables using Scheme::GenericGlobal
    VDouble0 m_nSharedSetFlags;  // "Set" flags actually shared by Scheme::FlagShared variables

    // METHODS

    // Return a statement enqueuing a closure to the queue 'queueVscp', to make the update
    // 'updatep'. The closure captures the values of the expressions 'captureps' in it at this
    // point (see 'captureVal'), which are replaced in the update with the members holding them.
    AstNbaEnqueue* newEnqueue(FileLine* flp, AstVarScope* queueVscp, AstNodeStmt* updatep,
                              const std::vector<AstNodeExpr*>& captureps) {
        AstTopScope* const topScopep = v3Global.rootp()->topScopep();
        AstScope* const scopep = topScopep->scopep();
        // The struct type of the closure, shared by closures capturing values of the same types
        AstStructDType* const dtypep = [&]() {
            std::vector<AstNodeDType*> memberDTypeps;
            for (AstNodeExpr* const exprp : captureps) {
                memberDTypeps.push_back(exprp->dtypep()->skipRefp());
            }
            AstStructDType*& dtypepr = m_closureDTypeps[memberDTypeps];
            if (dtypepr) return dtypepr;
            const std::string name
                = "__VnbaClosureType_" + std::to_string(m_closureDTypeps.size() - 1);
            dtypepr = new AstStructDType{flp, VSigning::NOSIGN};
            dtypepr->name(name);
            dtypepr->isClosure(true);
            dtypepr->classOrPackagep(scopep->modp());
            dtypepr->dtypep(dtypepr);
            dtypepr->widthForce(1, 1);  // Same as what V3Width does
            size_t nMembers = 0;
            for (AstNodeDType* const memberDTypep : memberDTypeps) {
                const std::string memberName = "val" + std::to_string(nMembers++);
                dtypepr->addMembersp(new AstMemberDType{flp, memberName, memberDTypep});
            }
            v3Global.rootp()->typeTablep()->addTypesp(dtypepr);
            // Typedef needed for V3Emit to actually emit the struct
            scopep->modp()->addStmtsp(new AstTypedef{flp, name, dtypepr, false});
            return dtypepr;
        }();
        // The runtime allocator pool of closures of this type enqueued to this queue
        AstVarScope* const poolVscp = [&]() {
            AstVarScope*& vscpr = m_closurePoolVscps[{dtypep, queueVscp}];
            if (vscpr) return vscpr;
            AstClosurePoolDType* const poolDTypep = new AstClosurePoolDType{flp, dtypep};
            v3Global.rootp()->typeTablep()->addTypesp(poolDTypep);
            const std::string name
                = "__VnbaClosurePool_" + std::to_string(m_closurePoolVscps.size() - 1);
            vscpr = topScopep->createTemp(name, poolDTypep);
            vscpr->varp()->noReset(true);
            // Like for the queue, taking a closure from the pool is not a data dependency. Used
            // only with the queue, its uses are ordered and serialized like those of the queue.
            vscpr->varp()->setIgnoreSchedWrite();
            return vscpr;
        }();
        // The function doing the update, then returning the closure to the pool
        AstCFunc* const funcp = [&]() {
            const std::string name = "__VnbaClosureFunc_" + std::to_string(m_nClosureFuncs++);
            AstCFunc* const funcp = new AstCFunc{flp, name, scopep};
            funcp->isStatic(true);
            funcp->isLoose(true);
            funcp->argTypes(EmitCUtil::symClassVar());
            scopep->addBlocksp(funcp);
            return funcp;
        }();
        // The argument to the function is a reference to the closure
        AstVarScope* const argVscp = [&]() {
            AstVar* const varp = new AstVar{flp, VVarType::BLOCKTEMP, "__Vclosure", dtypep};
            varp->funcLocal(true);
            varp->direction(VDirection::REF);
            funcp->addArgsp(varp);
            AstVarScope* const vscp = new AstVarScope{flp, scopep, varp};
            scopep->addVarsp(vscp);
            return vscp;
        }();
        // The enqueue statement, setting the members to the captured values
        AstVarRef* const queueRefp = new AstVarRef{flp, queueVscp, VAccess::READWRITE};
        AstVarRef* const poolRefp = new AstVarRef{flp, poolVscp, VAccess::READWRITE};
        AstNbaEnqueue* const enqueuep = new AstNbaEnqueue{flp, queueRefp, poolRefp, funcp};
        const AstMemberDType* memberp = dtypep->membersp();
        for (AstNodeExpr* const exprp : captureps) {
            AstVarRef* const argRefp = new AstVarRef{flp, argVscp, VAccess::READ};
            AstStructSel* const selp = new AstStructSel{flp, argRefp, memberp->name()};
            selp->dtypep(exprp->dtypep()->skipRefToEnump());
            exprp->replaceWith(selp);
            enqueuep->addArgsp(exprp);
            memberp = VN_AS(memberp->nextp(), MemberDType);
        }
        // The function makes the update, then returns the closure to the pool
        funcp->addStmtsp(updatep);
        funcp->addStmtsp([&]() {
            AstVarRef* const poolRefp = new AstVarRef{flp, poolVscp, VAccess::READWRITE};
            AstVarRef* const argRefp = new AstVarRef{flp, argVscp, VAccess::WRITE};
            AstCMethodHard* const releasep
                = new AstCMethodHard{flp, poolRefp, VCMethod::CLOSURE_POOL_RELEASE, argRefp};
            releasep->dtypeSetVoid();
            return releasep->makeStmt();
        }());
        return enqueuep;
    }

    // Given an expression 'exprp', return a new expression that always evaluates to the
    // value of the given expression at this point in the program and can be used in the
    // NBA commit block. That is:
    // - If given a constant, just return that constant.
    // - If capturing via a closure, add the expression to 'captureps', and return it, to be
    //   replaced with the member of the closure holding its value (see 'newEnqueue').
    // - Otherwise create a new temporary AstVarScope under the given 'scopep', with the given
    //   'name', assign the expression to it before 'insertp', and return a read reference to
    //   the new AstVarScope.
    AstNodeExpr* captureVal(AstScope* const scopep, AstNodeStmt* const insertp,
                            AstNodeExpr* const exprp, const std::string& name,
                            std::vector<AstNodeExpr*>* captureps = nullptr) {
        UASSERT_OBJ(!exprp->backp(), exprp, "Should have been unlinked");
        if (VN_IS(exprp, Const)) return exprp;
        // TODO: there are some const variables that could be simply referenced here
        if (captureps) {
            captureps->push_back(exprp);
            return exprp;
        }
        FileLine* const flp = exprp->fileline();
        AstVarScope* const tmpVscp = m_dlyTmps.make(flp, scopep, exprp->dtypep(), name);
        insertp->addHereThisAsNext(
            new AstAssign{flp, new AstVarRef{flp, tmpVscp, VAccess::WRITE}, exprp});
        return new AstVarRef{flp, tmpVscp, VAccess::READ};
    };

    // Similar to 'captureVal', but captures an LValue expression. That is, the returned
    // expression will reference the same location as the input expression at this point
    // in the program and can be used in the NBA commit block.
    AstNodeExpr* captureLhs(AstScope* const scopep, AstNodeStmt* const insertp,
                            AstNodeExpr* const lhsp, const std::string& baseName,
                            std::vector<AstNodeExpr*>* captureps = nullptr) {
        UASSERT_OBJ(!lhsp->backp(), lhsp, "Should have been unlinked");
        // Capture the indices of the selects, down to the target, through the same forms as
        // 'targetRefp'. If a handle selects the instance the target is a member of, capture the
        // handle instead, as it is only read, to select the target when the NBA is executed
        // (IEEE 1800-2023 10.4.2).
        size_t nIndices = 0;  // For unique names
        const auto capture = [&](AstNodeExpr* exprp, const std::string& prefix) {
            if (exprp->backp()) exprp->unlinkFrBack();
            return captureVal(scopep, insertp, exprp,
                              prefix + std::to_string(nIndices++) + baseName, captureps);
        };
        AstNodeExpr* nodep = lhsp;
        while (!VN_IS(nodep, VarRef)) {
            if (AstMemberSel* const selp = VN_CAST(nodep, MemberSel)) {
                V3LinkLValue::linkLValueSet(selp->fromp(), VAccess::READ);
                selp->fromp(capture(selp->fromp(), "Handle"));
                return lhsp;
            } else if (AstSel* const selp = VN_CAST(nodep, Sel)) {
                selp->lsbp(capture(selp->lsbp(), "Lsb"));
                nodep = selp->fromp();
            } else if (AstNodeSel* const selp = VN_CAST(nodep, NodeSel)) {
                selp->bitp(capture(selp->bitp(), "Dim"));
                nodep = selp->fromp();
            } else if (const AstStructSel* const selp = VN_CAST(nodep, StructSel)) {
                nodep = selp->fromp();
            } else {
                nodep->v3fatalSrc("Unexpected LHS expression of NBA");
            }
        }

        // The function of a closure is not a method, so it needs to capture 'this'
        // for class member references.
        if (!captureps) return lhsp;
        AstVarRef* const refp = VN_AS(nodep, VarRef);
        AstClass* const classp = VN_CAST(refp->varScopep()->scopep()->modp(), Class);
        if (!classp) return lhsp;

        FileLine* const flp = refp->fileline();
        AstClassRefDType*& dtypepr = m_thisDTypeps[classp];
        if (!dtypepr) {
            dtypepr = new AstClassRefDType{flp, classp, nullptr};
            v3Global.rootp()->typeTablep()->addTypesp(dtypepr);
        }
        AstNodeExpr* const thisp = capture(new AstThisRef{flp, dtypepr}, "This");
        AstMemberSel* const selp = new AstMemberSel{flp, thisp, refp->varp()};
        selp->access(refp->access());
        pushDeletep(refp);
        if (refp == lhsp) return selp;
        refp->replaceWith(selp);
        return lhsp;
    }

    // Return the commit of the global Scheme::GenericGlobal queue, creating it on first use
    AstNbaCommit* getGlobalNbaCommit() {
        if (m_globalNbaCommitp) return m_globalNbaCommitp;
        AstTopScope* const topScopep = v3Global.rootp()->topScopep();
        FileLine* const flp = topScopep->fileline();
        // Create the queue
        AstBasicDType* const dtypep = v3Global.rootp()->typeTablep()->findBasicDType(
            flp, VBasicDTypeKwd::NBA_GENERIC_QUEUE);
        AstVarScope* const queueVscp = topScopep->createTemp("__VNbaGlobalQueue", dtypep);
        v3Global.rootp()->nbaQueuep(queueVscp);
        // Enqueuing an update must not put the logic in the 'act' region, as it would for feeding
        // the trigger of the commit below. V3OrderGraphBuilder still orders the commit after it.
        queueVscp->varp()->setIgnoreSchedWrite();
        // Create the AstActive for the commit, explicitly triggered when an update is pending
        // during the trigger test (e.g. enqueue while in 'act'). Lowering specific NBAs in
        // clocked logic will also add the sensitivities of those blocks.
        AstCMethodHard* const triggerp
            = new AstCMethodHard{flp, new AstVarRef{flp, queueVscp, VAccess::READ},
                                 VCMethod::NBA_GENERIC_QUEUE_COMMIT_TRIGGER};
        triggerp->dtypeSetBit();
        m_globalNbaCommitSenTreep
            = new AstSenTree{flp, new AstSenItem{flp, VEdgeType::ET_TRUE, triggerp}};
        AstActive* const activep = new AstActive{flp, "nba-enqueued", m_globalNbaCommitSenTreep};
        activep->senTreeStorep(m_globalNbaCommitSenTreep);
        topScopep->scopep()->addBlocksp(activep);
        // Add 'Post' scheduled process for the commit
        AstAlwaysPost* const postp = new AstAlwaysPost{flp};
        activep->addStmtsp(postp);
        m_globalNbaCommitp
            = new AstNbaCommit{flp, new AstVarRef{flp, queueVscp, VAccess::READWRITE}};
        postp->addStmtsp(m_globalNbaCommitp);
        return m_globalNbaCommitp;
    }
    // Add the sensitivities to the global NBA commit
    void addGlobalNbaCommitSensitivity(const AstSenTree* senTreep) {
        getGlobalNbaCommit();  // Creates m_globalNbaCommitSenTreep
        m_globalNbaCommitSenTreep->addSensesp(senTreep->sensesp()->cloneTree(true));
        // Remove duplicates
        V3Const::constifyExpensiveEdit(m_globalNbaCommitSenTreep);
    }

    // Scheme::ShadowVar
    void prepareSchemeShadowVar(AstVarScope* vscp, TargetInfo& targetInfo) {
        UASSERT_OBJ(targetInfo.m_scheme == Scheme::ShadowVar, vscp, "Inconsistent NBA scheme");
        FileLine* const flp = vscp->fileline();
        AstScope* const scopep = vscp->scopep();
        // Create the shadow variable
        const std::string name = "_" + vscp->varp()->shortName();
        AstVarScope* const shadowVscp = m_dlyTmps.make(flp, scopep, vscp->dtypep(), name);
        targetInfo.shadowVariableKit().vscp = shadowVscp;
        // Mark both for V3LifePsot
        vscp->optimizeLifePost(true);
        shadowVscp->optimizeLifePost(true);
        // Create the AstActive for the Pre/Post logic
        AstActive* const activep = new AstActive{flp, "", targetInfo.senTreep()};
        activep->senTreeStorep(targetInfo.senTreep());
        scopep->addBlocksp(activep);
        // Add 'Pre' scheduled 'shadowVariable = originalVariable' assignment
        AstAlwaysPre* const prep = new AstAlwaysPre{flp};
        activep->addStmtsp(prep);
        prep->addStmtsp(new AstAssign{flp, new AstVarRef{flp, shadowVscp, VAccess::WRITE},
                                      new AstVarRef{flp, vscp, VAccess::READ}});
        // Add 'Post' scheduled 'originalVariable = shadowVariable' assignment
        AstAlwaysPost* const postp = new AstAlwaysPost{flp};
        activep->addStmtsp(postp);
        postp->addStmtsp(new AstAssign{flp, new AstVarRef{flp, vscp, VAccess::WRITE},
                                       new AstVarRef{flp, shadowVscp, VAccess::READ}});
    }
    void convertSchemeShadowVar(const NBA& nba, TargetInfo& targetInfo) {
        AstAssignDly* const nodep = VN_AS(nba.nodep, AssignDly);
        AstVarScope* const vscp = VN_AS(nba.targetp, VarRef)->varScopep();
        UASSERT_OBJ(targetInfo.m_scheme == Scheme::ShadowVar, vscp, "Inconsistent NBA scheme");
        AstVarScope* const shadowVscp = targetInfo.shadowVariableKit().vscp;

        // Replace the write ref on the LHS with the shadow variable
        nodep->lhsp()->foreach([&](AstVarRef* const refp) {
            if (!refp->access().isWriteOnly()) return;
            UASSERT_OBJ(refp->varScopep() == vscp, nodep, "NBA not setting expected variable");
            refp->varScopep(shadowVscp);
            refp->varp(shadowVscp->varp());
        });
    }

    // Scheme::ShadowVarMasked
    void prepareSchemeShadowVarMasked(AstVarScope* vscp, TargetInfo& targetInfo) {
        UASSERT_OBJ(targetInfo.m_scheme == Scheme::ShadowVarMasked, vscp,
                    "Inconsistent NBA scheme");
        FileLine* const flp = vscp->fileline();
        AstScope* const scopep = vscp->scopep();
        // Create the shadow variable
        const std::string shadowName = "_" + vscp->varp()->shortName();
        AstVarScope* const shadowVscp = m_dlyTmps.make(flp, scopep, vscp->dtypep(), shadowName);
        targetInfo.shadowVarMaskedKit().vscp = shadowVscp;
        // Create the mask variable
        const std::string maskName = "Mask__" + vscp->varp()->shortName();
        AstVarScope* const maskVscp = m_dlyTmps.make(flp, scopep, vscp->dtypep(), maskName);
        maskVscp->varp()->setIgnorePostWrite();
        targetInfo.shadowVarMaskedKit().maskp = maskVscp;
        // Create the AstActive for the Post logic
        AstActive* const activep = new AstActive{flp, "", targetInfo.senTreep()};
        activep->senTreeStorep(targetInfo.senTreep());
        scopep->addBlocksp(activep);
        // Add 'Post' scheduled process for the commit and mask clear
        AstAlwaysPost* const postp = new AstAlwaysPost{flp};
        activep->addStmtsp(postp);
        // Add the commit - vscp = (shadowVscp & maskVscp) | (vscp & ~maskVscp);
        postp->addStmtsp(new AstAssign{
            flp, new AstVarRef{flp, vscp, VAccess::WRITE},
            new AstOr{flp,
                      new AstAnd{flp, new AstVarRef{flp, shadowVscp, VAccess::READ},
                                 new AstVarRef{flp, maskVscp, VAccess::READ}},
                      new AstAnd{flp, new AstVarRef{flp, vscp, VAccess::READ},
                                 new AstNot{flp, new AstVarRef{flp, maskVscp, VAccess::READ}}}}});
        vscp->varp()->setIgnorePostRead();
        // Clear the mask - maskVscp = '0;
        postp->addStmtsp(
            new AstAssign{flp, new AstVarRef{flp, maskVscp, VAccess::WRITE},
                          new AstConst{flp, AstConst::WidthedValue{}, maskVscp->width(), 0}});
    }
    void convertSchemeShadowVarMasked(const NBA& nba, TargetInfo& targetInfo) {
        AstAssignDly* const nodep = VN_AS(nba.nodep, AssignDly);
        AstVarScope* const vscp = VN_AS(nba.targetp, VarRef)->varScopep();
        UASSERT_OBJ(targetInfo.m_scheme == Scheme::ShadowVarMasked, vscp,
                    "Inconsistent NBA scheme");
        AstVarScope* const shadowVscp = targetInfo.shadowVarMaskedKit().vscp;
        AstVarScope* const maskVscp = targetInfo.shadowVarMaskedKit().maskp;

        AstNodeExpr* lhsClonep = nodep->lhsp()->cloneTree(false);

        // Replace the write ref on the LHS with the shadow variable
        nodep->lhsp()->foreach([&](AstVarRef* const refp) {
            if (!refp->access().isWriteOnly()) return;
            UASSERT_OBJ(refp->varScopep() == vscp, nodep, "NBA not setting expected variable");
            refp->varScopep(shadowVscp);
            refp->varp(shadowVscp->varp());
        });
        // Set the same bits in the mask to 1
        lhsClonep->foreach([&](AstVarRef* const refp) {
            if (!refp->access().isWriteOnly()) return;
            UASSERT_OBJ(refp->varScopep() == vscp, nodep, "NBA not setting expected variable");
            refp->varScopep(maskVscp);
            refp->varp(maskVscp->varp());
        });
        FileLine* const flp = nodep->fileline();
        AstConst* const onesp = new AstConst{flp, AstConst::DTyped{}, lhsClonep->dtypep()};
        onesp->num().setAllBits1();
        nodep->addNextHere(new AstAssign{flp, lhsClonep, onesp});
    }

    // Scheme::FlagShared
    void prepareSchemeFlagShared(AstVarScope* vscp, TargetInfo& targetInfo) {
        UASSERT_OBJ(targetInfo.m_scheme == Scheme::FlagShared, vscp, "Inconsistent NBA scheme");
        FileLine* const flp = vscp->fileline();
        AstScope* const scopep = vscp->scopep();
        // Create the AstActive for the Pre/Post logic
        AstActive* const activep = new AstActive{flp, "", targetInfo.senTreep()};
        activep->senTreeStorep(targetInfo.senTreep());
        scopep->addBlocksp(activep);
        targetInfo.flagSharedKit().activep = activep;
        // Add 'Post' scheduled process to be populated later
        AstAlwaysPost* const postp = new AstAlwaysPost{flp};
        activep->addStmtsp(postp);
        targetInfo.flagSharedKit().postp = postp;
        // Initialize
        targetInfo.flagSharedKit().commitFlagp = nullptr;
        targetInfo.flagSharedKit().commitIfp = nullptr;
    }
    void convertSchemeFlagShared(const NBA& nba, TargetInfo& targetInfo) {
        AstAssignDly* nodep = VN_AS(nba.nodep, AssignDly);
        AstScope* const scopep = nba.scopep;
        AstVarScope* const vscp = VN_AS(nba.targetp, VarRef)->varScopep();
        UASSERT_OBJ(targetInfo.m_scheme == Scheme::FlagShared, vscp, "Inconsistent NBA scheme");
        FileLine* const flp = vscp->fileline();

        // Base name suffix for signals constructed below
        const std::string baseName = "__" + vscp->varp()->shortName();

        // Unlink and capture the RHS value
        AstNodeExpr* const capturedRhsp
            = captureVal(scopep, nodep, nodep->rhsp()->unlinkFrBack(), "Val" + baseName);

        // Unlink and capture the LHS reference
        AstNodeExpr* const capturedLhsp
            = captureLhs(scopep, nodep, nodep->lhsp()->unlinkFrBack(), baseName);

        // Is this NBA adjacent after the previously processed NBA?
        const bool consecutive = nodep == m_nextDlyp;
        m_nextDlyp = VN_CAST(nodep->nextp(), AssignDly);

        TargetInfo* const prevTargetInfop
            = consecutive ? &m_state.targetInfo(m_prevVscp) : nullptr;

        // We can reuse the flag of the previous assignment if:
        const bool reuseTheFlag =
            // Consecutive NBAs
            consecutive
            // ... that use the same scheme
            && prevTargetInfop->m_scheme == Scheme::FlagShared
            // ... and are in the same scope as the target variable
            && scopep == vscp->scopep()
            // ... and share the same overall update domain
            && prevTargetInfop->senTreep()->sameTree(targetInfo.senTreep());

        if (!reuseTheFlag) {
            // Create new flag
            AstVarScope* const flagVscp = m_dlyTmps.make(flp, scopep, 1, "Set" + baseName);
            // Set the flag at the original NBA
            nodep->addHereThisAsNext(  //
                new AstAssign{flp, new AstVarRef{flp, flagVscp, VAccess::WRITE},
                              new AstConst{flp, AstConst::BitTrue{}}});
            // Add the 'Pre' scheduled reset for the flag
            AstAlwaysPre* const prep = new AstAlwaysPre{flp};
            targetInfo.flagSharedKit().activep->addStmtsp(prep);
            prep->addStmtsp(new AstAssign{flp, new AstVarRef{flp, flagVscp, VAccess::WRITE},
                                          new AstConst{flp, AstConst::BitFalse{}}});
            // Add the 'Post' scheduled commit
            AstIf* const ifp = new AstIf{flp, new AstVarRef{flp, flagVscp, VAccess::READ}};
            targetInfo.flagSharedKit().postp->addStmtsp(ifp);
            targetInfo.flagSharedKit().commitFlagp = flagVscp;
            targetInfo.flagSharedKit().commitIfp = ifp;
        } else {
            if (vscp != m_prevVscp) {
                // Different variable, ensure the commit block exists for this variable,
                // can reuse existing one with the same flag, otherwise create a new one.
                AstVarScope* const flagVscp = prevTargetInfop->flagSharedKit().commitFlagp;
                UASSERT_OBJ(flagVscp, nodep, "Commit flag of previous assignment should exist");
                if (targetInfo.flagSharedKit().commitFlagp != flagVscp) {
                    AstIf* const ifp = new AstIf{flp, new AstVarRef{flp, flagVscp, VAccess::READ}};
                    targetInfo.flagSharedKit().postp->addStmtsp(ifp);
                    targetInfo.flagSharedKit().commitFlagp = flagVscp;
                    targetInfo.flagSharedKit().commitIfp = ifp;
                }
            } else {
                // Same variable, reuse the commit block of the previous assignment
                targetInfo.flagSharedKit().commitFlagp
                    = prevTargetInfop->flagSharedKit().commitFlagp;
                targetInfo.flagSharedKit().commitIfp = prevTargetInfop->flagSharedKit().commitIfp;
            }
            ++m_nSharedSetFlags;
        }
        // Commit the captured value to the captured destination
        targetInfo.flagSharedKit().commitIfp->addThensp(
            new AstAssign{flp, capturedLhsp, capturedRhsp});

        // Remember the variable for the next NBA
        m_prevVscp = vscp;

        // Delete original NBA
        VL_DO_DANGLING(pushDeletep(nodep->unlinkFrBack()), nodep);
    }

    // Scheme::GenericLocal
    void prepareSchemeGenericLocal(AstVarScope* vscp, TargetInfo& targetInfo) {
        UASSERT_OBJ(targetInfo.m_scheme == Scheme::GenericLocal, vscp, "Inconsistent NBA scheme");
        FileLine* const flp = vscp->fileline();
        AstScope* const scopep = vscp->scopep();
        // Create the queue
        AstBasicDType* const dtypep = v3Global.rootp()->typeTablep()->findBasicDType(
            flp, VBasicDTypeKwd::NBA_GENERIC_QUEUE);
        const std::string name = "NbaLocalQueue__" + vscp->varp()->shortName();
        AstVarScope* const queueVscp = m_dlyTmps.make(flp, scopep, dtypep, name);
        // Enqueuing is not a data dependency, V3OrderGraphBuilder orders the commit after it
        queueVscp->varp()->setIgnoreSchedWrite();
        targetInfo.genericKit().queueVscp = queueVscp;
        // Create the AstActive for the Post logic
        AstActive* const activep = new AstActive{flp, "", targetInfo.senTreep()};
        activep->senTreeStorep(targetInfo.senTreep());
        scopep->addBlocksp(activep);
        // Add 'Post' scheduled process for the commit
        AstAlwaysPost* const postp = new AstAlwaysPost{flp};
        activep->addStmtsp(postp);
        AstNbaCommit* const commitp
            = new AstNbaCommit{flp, new AstVarRef{flp, queueVscp, VAccess::READWRITE}};
        postp->addStmtsp(commitp);
        // Record updated variable
        commitp->addTargetsp(new AstVarRef{flp, vscp, VAccess::WRITE});
    }

    // Scheme::GenericGlobal
    void prepareSchemeGenericGlobal(AstNode* targetp, TargetInfo& targetInfo) {
        UASSERT_OBJ(targetInfo.m_scheme == Scheme::GenericGlobal, targetp,
                    "Inconsistent NBA scheme");
        AstNbaCommit* const commitp = getGlobalNbaCommit();
        // Use the global queue when converting
        targetInfo.genericKit().queueVscp = commitp->queuep()->varScopep();
        // Record additional sensitivities
        if (const AstSenTree* const senTreep = targetInfo.senTreep()) {
            addGlobalNbaCommitSensitivity(senTreep);
        }
        // Record updated variable
        if (AstVarScope* const vscp = VN_CAST(targetp, VarScope)) {
            commitp->addTargetsp(new AstVarRef{vscp->fileline(), vscp, VAccess::WRITE});
        } else {
            // A MemberSel via a virtual interface may select any instance of that interface
            for (AstVarScope* const vscp : m_state.ifaceVscps[VN_AS(targetp, Var)]) {
                // Avoid adding it twice if the instance is also the target of an explicit NBA
                if (m_state.targetInfo.tryGet(vscp)) continue;
                commitp->addTargetsp(new AstVarRef{vscp->fileline(), vscp, VAccess::WRITE});
            }
        }
    }

    // Scheme::GenericLocal/Scheme::GenericGlobal
    void convertSchemeGeneric(const NBA& nba, TargetInfo& targetInfo) {
        AstNodeStmt* nodep = nba.nodep;
        AstScope* const scopep = nba.scopep;
        FileLine* const flp = nodep->fileline();

        // The update, and the values it needs, to be captured in the closure
        std::vector<AstNodeExpr*> captureps;
        AstNodeStmt* updatep;
        if (AstFireEvent* const firep = VN_CAST(nodep, FireEvent)) {
            UASSERT_OBJ(firep->isDelayed(), firep, "Blocking fire event should not be recorded");
            // Unlink and capture the event reference
            AstNodeExpr* const capturedp
                = captureLhs(scopep, nodep, firep->operandp()->unlinkFrBack(), "", &captureps);
            updatep = new AstFireEvent{flp, capturedp, false};
        } else {
            AstAssignDly* const assignp = VN_AS(nodep, AssignDly);
            // Unlink and capture the RHS value
            AstNodeExpr* const capturedRhsp
                = captureVal(scopep, nodep, assignp->rhsp()->unlinkFrBack(), "", &captureps);
            // Unlink and capture the LHS reference
            AstNodeExpr* const capturedLhsp
                = captureLhs(scopep, nodep, assignp->lhsp()->unlinkFrBack(), "", &captureps);
            updatep = new AstAssign{flp, capturedLhsp, capturedRhsp};
        }

        // Replace the NBA with enqueuing the closure
        AstVarScope* const queueVscp = targetInfo.genericKit().queueVscp;
        nodep->replaceWith(newEnqueue(flp, queueVscp, updatep, captureps));
        VL_DO_DANGLING(pushDeletep(nodep), nodep);
    }

    // CONSTRUCTORS
    explicit DelayedRewrite(State& state)
        : DelayedBase{state} {
        // A call in a clocked process that may enqueue a global NBA is marked, so
        // V3Order can order it before the commit of the global NBA queue,
        // and the commit is triggered by the sensitivities of the enqueueing processes.
        // Calls in combinational processes are rejected by DelayedAnalysis.
        for (const V3GraphVertex& vtx : m_state.graph.vertices()) {
            const ProcVertex* const procVtxp = vtx.cast<ProcVertex>();
            if (!procVtxp || !procVtxp->m_clocked) continue;
            for (const V3GraphEdge& edge : procVtxp->outEdges()) {
                const CallVertex* const callVtxp = edge.top()->as<CallVertex>();
                if (callVtxp->m_nbaps.empty()) continue;
                callVtxp->m_callp->setMayEnqueueGlobalNBA();
                addGlobalNbaCommitSensitivity(procVtxp->m_senTreep);
            }
        }

        // Prepare each variable updated directly
        for (AstVarScope* const vscp : m_state.nbaVscps) {
            TargetInfo& targetInfo = m_state.targetInfo(vscp);
            // Run 'prepare' step
            switch (targetInfo.m_scheme) {
            case Scheme::Undecided:  // LCOV_EXCL_START
                UASSERT_OBJ(false, vscp, "Failed to choose NBA scheme");
                break;  // LCOV_EXCL_STOP
            case Scheme::ShadowVar: {
                ++m_nSchemeShadowVar;
                prepareSchemeShadowVar(vscp, targetInfo);
                break;
            }
            case Scheme::ShadowVarMasked: {
                ++m_nSchemeShadowVarMasked;
                prepareSchemeShadowVarMasked(vscp, targetInfo);
                break;
            }
            case Scheme::FlagShared: {
                ++m_nSchemeFlagShared;
                prepareSchemeFlagShared(vscp, targetInfo);
                break;
            }
            case Scheme::GenericLocal: {
                ++m_nSchemeGenericLocal;
                prepareSchemeGenericLocal(vscp, targetInfo);
                break;
            }
            case Scheme::GenericGlobal: {
                ++m_nSchemeGenericGlobal;
                prepareSchemeGenericGlobal(vscp, targetInfo);
                break;
            }
            }
        }
        // Prepare each accessed via a MemberSel
        for (AstVar* const varp : m_state.nbaVarps) {
            ++m_nSchemeGenericGlobal;
            prepareSchemeGenericGlobal(varp, m_state.targetInfo(varp));
        }

        // Convert all NBAs
        for (const NBA& nba : m_state.nbas) {
            const AstMemberSel* const selp = VN_CAST(nba.targetp, MemberSel);
            TargetInfo& targetInfo
                = selp ? m_state.targetInfo(selp->varp())  //
                       : m_state.targetInfo(VN_AS(nba.targetp, VarRef)->varScopep());
            // Run 'convert' step
            switch (targetInfo.m_scheme) {
            case Scheme::Undecided: {  // LCOV_EXCL_START
                UASSERT_OBJ(false, nba.targetp, "Unreachable");
                break;
            }  // LCOV_EXCL_STOP
            case Scheme::ShadowVar: {
                convertSchemeShadowVar(nba, targetInfo);
                break;
            }
            case Scheme::ShadowVarMasked: {
                convertSchemeShadowVarMasked(nba, targetInfo);
                break;
            }
            case Scheme::FlagShared: {
                convertSchemeFlagShared(nba, targetInfo);
                break;
            }
            case Scheme::GenericLocal:
            case Scheme::GenericGlobal: {
                convertSchemeGeneric(nba, targetInfo);
                break;
            }
            }
        }

        V3Stats::addStat("NBA, variables using ShadowVar scheme", m_nSchemeShadowVar);
        V3Stats::addStat("NBA, variables using ShadowVarMasked scheme", m_nSchemeShadowVarMasked);
        V3Stats::addStat("NBA, variables using FlagShared scheme", m_nSchemeFlagShared);
        V3Stats::addStat("NBA, variables using GenericLocal scheme", m_nSchemeGenericLocal);
        V3Stats::addStat("NBA, variables using GenericGlobal scheme", m_nSchemeGenericGlobal);
        V3Stats::addStat("Optimizations, NBA flags shared", m_nSharedSetFlags);
    }

public:
    static void apply(State& state) { DelayedRewrite{state}; }
};

//######################################################################
// Delayed class functions

void V3Delayed::delayedAll(AstNetlist* nodep) {
    UINFO(2, __FUNCTION__ << ":");
    {
        DelayedBase::State state;
        DelayedRecord::apply(state, nodep);
        DelayedAnalysis::apply(state);
        DelayedRewrite::apply(state);
    }  // Destruct before checking
    V3Global::dumpCheckGlobalTree("delayed", 0, dumpTreeEitherLevel() >= 3);
}
