// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Add temporaries, such as for delayed nodes
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
// Convert AstAssignDly into temporaries an specially scheduled blocks.
// For the Pre/Post scheduling semantics, see V3OrderGraph.
//
// There are several "Schemes" we can choose from for implementing a
// non-blocking assignment (NBA), represented by an AstAssignDly.
//
// It is assumed and required in this pass that each NBA updates at
// most one variable. Earlier passes should have ensured this.
//
// Each variable is associated with a single NBA scheme, that is, all
// NBAs targeting the same variable will use the scheme assigned to
// that variable. This necessitates a global analysis of all NBAs
// before any decision can be made on how to handle them.
//
// The algorithm proceeds in 3 steps.
// 1. Gather all AstAssignDly non-blocking assignments (NBAs) in the
//    whole design. Note usage context of variables updated by these NBAs.
//    This is implemented in the 'visit' methods
// 2. For each variable that is the target of an NBA, decide which of
//    the possible conversion schemes to use, based on info gathered in
//    step 1.
//    This is implemented in the 'chooseScheme' method
// 3. For each NBA gathered in step 1, convert it based on the scheme
//    selected in step 2.
//    This is implemented in the 'prepare*'/'convert*' methods. The
//    'prepare*' methods do the parts common for all NBAs updating
//    the given variable. The 'convert*' methods then convert each
//    AstAssignDly separately
//
// These are the possible NBA Schemes:
// "Shadow variable" scheme. Used for non-unpackedarray target
// variables in synthesizeable code. E.g.:
//   LHS <= RHS;
// is converted to:
//  - Add new "Pre-scheduled" logic:
//      __Vdly__LHS = LHS;
//  - In the original logic, replace the target variable 'LHS' with '__Vdly__LHS' variables:
//      __Vdly__LHS = RHS;
//  - Add new "Post-scheduled" logic:
//      LHS = __Vdly__LHS;
//
// "Shared flag" scheme. Used for unpacked array target variables
// in synthesizeable code. E.g.:
//   LHS[idxa][idxb] <= RHS
// is converted to:
//  - Add new "Pre-scheduled" logic:
//      __Vdly_Set__LHS = 0;
//  - In the original logic, replace the AstAssignDelay with:
//      __Vdly_Set__LHS = 1;
//      __Vdly_Dim0__LHS = idxa;
//      __Vdly_Dim1__LHS = idxb;
//      __Vdly_Val__LHS = RHS;
//  - Add new "Post-scheduled" logic:
//      if (__Vdly_Set__LHS) a[__Vdly_Dim0__LHS][__Vdly_Dim1__LHS] = __Vdly_Val__LHS;
// Multiple consecutive NBAs of compatible form can share the same  __Vdly_Set* flag
//
// "Shadow variable masked" scheme. Used for packed target variables that
// have both blocking and non-blocking updates. E.g.:
//   LHS[Index] <= RHS;
//   When there is also LHS[SomeNonOverlappingIndex] = RHS2;
// is converted to:
//  - In the original logic, replace the AstAssignDelay with:
//      __Vdly__LHS[Index] = RHS;
//      __Vdly_Mask__LHS[Index] = '1;
//  - Add new "Post-scheduled" logic:
//      LHS = (__Vdly__LHS & __Vdly_Mask__LHS) | (LHS & ~__Vdly_Mask__LHS);
//      __Vdly_Mask__LHS = '0;
//
// "Unique flag" scheme. Used for all variables updated by NBAs
// in suspendable processees or forks. E.g.:
//   #1 LHS <= RHS;
// is converted to:
//  - In the original logic, replace the AstAssignDelay with:
//      __Vdly_SetUnique__LHS = 1;
//      __Vdly_Val__LHS = RHS;
//  - Add new "Post-scheduled" logic:
//      if (__Vdly_SetUnique__LHS) {
//         __Vdly_SetUnique__LHS = 0;
//         LHS = __Vdly_Val__LHS;
//      }
//
// The "Value Queue Whole/Partial" schemes are used for cases where the
// target of an assignment cannot be statically determined, for example,
// with an array LHS in a loop:
//   LHS[idxa][idxb] <= RHS
// is converted to:
//  - In the original logic, replace the AstAssignDelay with:
//      __Vdly_Dim0__LHS = idxa;
//      __Vdly_Dim1__LHS = idxb;
//      __Vdly_Val__LHS = RHS;
//      __Vdly_CommitQueue__LHS.enqueue(0, __Vdly_Val__LHS, __Vdly_Dim0__LHS, __Vdly_Dim1__LHS);
//  - Add new "Post-scheduled" logic:
//      __Vdly_CommitQueue__LHS.commit(LHS);
// These schemes are also used for variables updated by NBAs with pending
// updates, from intra-assignment timing controls. V3Timing gives these NBAs
// tickets, taken when the NBA is executed, and the commit performs the updates
// in the order of their tickets (IEEE 1800-2023 4.6). Their other NBAs take a
// ticket when enqueueing, instead of 0.
//
// The "Generic Queue" scheme is used for all other NBAs that need such
// ordering, for NBAs to a target selected by a handle, which can be of any
// instance of an interface, and for NBAs in non-inlined functions, which can
// be executed in the context of any process calling them. All NBAs to the same
// variable, or member of an interface or class, use this scheme. Each NBA
// queues the values of its update in queues of its own, and adds the update to
// the order of the updates of the variable, which the commit, triggered also
// by the processes calling the functions, applies in the 'nba' region. E.g.:
//   vif.LHS[idx] <= RHS
// is converted to:
//  - In the original logic, replace the AstAssignDelay with:
//      __VnbaQueue0_0_0.push_back(RHS);
//      __VnbaQueue0_0_1.push_back(idx);
//      __VnbaQueue0_0_2.push_back(vif);
//      __VnbaOrder0__LHS.add(ticket, 0);
//  - Add new "Post-scheduled" logic, committing the updates in order:
//      while (__VnbaOrder0__LHS.next()) {
//          __Vdly_Site0__LHS = __VnbaOrder0__LHS.site();
//          __Vdly_Index0__LHS = __VnbaOrder0__LHS.index();
//          if (__Vdly_Site0__LHS == 0) {
//              __Vdly_Load0_0_1 = __VnbaQueue0_0_1.at(__Vdly_Index0__LHS);
//              __Vdly_Load0_0_2 = __VnbaQueue0_0_2.at(__Vdly_Index0__LHS);
//              __Vdly_Load0_0_2.LHS[__Vdly_Load0_0_1] = __VnbaQueue0_0_0.at(__Vdly_Index0__LHS);
//          }
//          ... the same for the other NBAs ("sites") of the variable
//      }
//      __VnbaQueue0_0_0.clear(); ...
//
// TODO: generic LHS scheme as discussed in #5092, also for other variables
//
//*************************************************************************

#include "V3PchAstNoMT.h"  // VL_MT_DISABLED_CODE_UNIT

#include "V3Delayed.h"

#include "V3AstUserAllocator.h"
#include "V3ClassGraph.h"
#include "V3Const.h"
#include "V3LinkLValue.h"
#include "V3SharedTmps.h"
#include "V3Stats.h"

#include <deque>
#include <map>

VL_DEFINE_DEBUG_FUNCTIONS;

// Whether a dynamic commit queue supports variables, or elements of arrays, of the given type
static bool isQueueable(const AstNodeDType* dtypep) {
    const AstBasicDType* const basicp = dtypep->basicp();
    return basicp && (basicp->isIntegralOrPacked() || basicp->isDouble() || basicp->isString());
}

// Whether the updates of an NBA to the given target can be in a dynamic commit queue, as
// convertSchemeValueQueue: a variable, or element of an unpacked array selected in all its
// dimensions, of a type isQueueable, or bits selected of it, if packed
static bool canQueue(const AstNodeExpr* lhsp) {
    const AstSel* const selp = VN_CAST(lhsp, Sel);
    const AstNode* nodep = selp ? selp->fromp() : lhsp;
    size_t nIndices = 0;
    while (const AstArraySel* const arraySelp = VN_CAST(nodep, ArraySel)) {
        nodep = arraySelp->fromp();
        ++nIndices;
    }
    const AstVarRef* const refp = VN_CAST(nodep, VarRef);
    if (!refp) return false;
    const AstNodeDType* dtypep = refp->varp()->dtypep()->skipRefp();
    for (; nIndices; --nIndices) dtypep = VN_AS(dtypep, UnpackArrayDType)->subDTypep()->skipRefp();
    if (VN_IS(dtypep, UnpackArrayDType)) return false;
    return selp ? dtypep->isIntegralOrPacked() : isQueueable(dtypep);
}

// The member select of the handle selecting the target of an NBA with the given LHS, following
// the selects of the target, or nullptr if the target is a variable
static AstMemberSel* handleSelp(AstNodeExpr* lhsp) {
    AstNode* nodep = lhsp->baseFromp(false);
    while (const AstStructSel* const selp = VN_CAST(nodep, StructSel)) {
        nodep = selp->fromp()->baseFromp(false);
    }
    return VN_CAST(nodep, MemberSel);
}

// Add a copy of the given sensitivities to the given sensitivity tree, creating it if needed
static void addSensitivities(AstSenTree*& senTreep, AstSenItem* nodep) {
    if (!senTreep) senTreep = new AstSenTree{nodep->fileline(), nullptr};
    // Add a copy of each term
    senTreep->addSensesp(nodep->cloneTree(true));
    // Remove duplicates
    V3Const::constifyExpensiveEdit(senTreep);
}

//######################################################################
// Convert AstAssignDlys (NBAs)

class DelayedVisitor final : public VNVisitor {
    // TYPES

    // The various NBA conversion schemes, including error cases
    enum class Scheme : uint8_t {
        Undecided = 0,
        UnsupportedCompoundArrayInLoop,
        ShadowVar,
        ShadowVarMasked,
        FlagShared,
        FlagUnique,
        ValueQueueWhole,
        ValueQueuePartial,
        GenericQueue
    };

    // All info associated with a variable that is the target of an NBA
    class VarScopeInfo final {
    public:
        // First write reference encountered to the VarScope as the target on an NBA
        const AstVarRef* m_firstNbaRefp = nullptr;
        // Active block 'm_firstNbaRefp' is under
        const AstActive* m_fistActivep = nullptr;
        bool m_whole = false;  // Used on LHS of NBA directly via VarRef
        bool m_partial = false;  // Used on LHS of NBA under a Sel
        bool m_inLoop = false;  // Used on LHS of NBA in a loop
        bool m_inSuspOrFork = false;  // Used on LHS of NBA in suspendable process or fork
        bool m_ordered = false;  // Used on LHS of NBA with a ticket, ordering its updates
        Scheme m_scheme = Scheme::Undecided;  // Conversion scheme to use for this variable

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
            struct {  // Stuff needed for Scheme::FlagUnique
                AstAlwaysPost* postp;  // The post block for commiting results
            } m_flagUniqueKit;
            struct {  // Stuff needed for Scheme::ValueQueueWhole/Scheme::ValueQueuePartial
                AstVarScope* vscp;  // The commit queue variable
            } m_valueQueueKit;
        } m_kitUnion;

    public:
        VarScopeInfo() = default;
        ~VarScopeInfo() {
            // Might not be linked if there was an error
            if (!m_senTreep->backp()) VL_DO_DANGLING(m_senTreep->deleteTree(), m_senTreep);
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
        auto& flagUniqueKit() {
            UASSERT(m_scheme == Scheme::FlagUnique, "Inconsistent Scheme");
            return m_kitUnion.m_flagUniqueKit;
        }
        auto& valueQueueKit() {
            UASSERT(m_scheme == Scheme::ValueQueuePartial || m_scheme == Scheme::ValueQueueWhole,
                    "Inconsistent Scheme");
            return m_kitUnion.m_valueQueueKit;
        }

        // Accessor
        AstSenTree* senTreep() const { return m_senTreep; }

        // Add sensitivities
        void addSensitivity(AstSenItem* nodep) { addSensitivities(m_senTreep, nodep); }
        // cppcheck-suppress constParameterPointer
        void addSensitivity(AstSenTree* nodep) { addSensitivity(nodep->sensesp()); }
    };

    // All info associated with a destination of NBAs: a variable, or a member of an interface,
    // which a handle can select in any instance
    class DestInfo final {
    public:
        bool m_handle = false;  // Updated through a handle, or by a method of the interface
        bool m_inCFunc = false;  // Updated by an NBA in a non-inlined function
        bool m_ordered = false;  // Updated by an NBA with a ticket, ordering its pending updates
        bool m_queueable = true;  // All NBAs updating it can use a dynamic commit queue
        // Stuff needed for Scheme::GenericQueue
        uint32_t m_id = 0;  // Number for unique names
        uint32_t m_nSites = 0;  // Number of NBAs using it
        AstVarScope* m_orderVscp = nullptr;  // The order of the updates (VlNBAOrder)
        AstVarScope* m_siteVscp = nullptr;  // The site of the update the commit applies
        AstVarScope* m_indexVscp = nullptr;  // The index of its values in the queues of the site
        AstAlwaysPost* m_postp = nullptr;  // The commit
        AstLoop* m_loopp = nullptr;  // The loop of the commit applying the updates in order
        std::vector<AstVarScope*> m_queueVscps;  // The queues of the values of all sites

    private:
        // Combined sensitivities of all NBAs updating it
        AstSenTree* m_senTreep = nullptr;

    public:
        DestInfo() = default;
        ~DestInfo() {
            // Might not be linked if there was an error
            if (m_senTreep && !m_senTreep->backp()) {
                VL_DO_DANGLING(m_senTreep->deleteTree(), m_senTreep);
            }
        }
        VL_UNCOPYABLE(DestInfo);
        // Whether it uses Scheme::GenericQueue
        bool isGeneric() const { return m_handle || m_inCFunc || (m_ordered && !m_queueable); }
        // Accessor
        AstSenTree* senTreep() const { return m_senTreep; }
        // Add sensitivities
        void addSensitivity(AstSenItem* nodep) { addSensitivities(m_senTreep, nodep); }
    };

    // Calls by a process, executing the NBAs in the called functions in its context
    struct ProcessCalls final {
        AstNodeProcedure* m_procp;  // The process
        const AstSenTree* m_clockedp;  // Its sensitivities, if clocked, otherwise nullptr
        std::vector<const AstSenTree*> m_domainps;  // Its timing domains
        std::vector<AstCFunc*> m_calleeps;  // Functions it calls
    };

    // Data structure to keep track of all writes to
    struct WriteReference final {
        AstVarRef* m_refp = nullptr;  // The reference
        bool m_isNBA = false;  // True if an NBA write
        bool m_inNonComb = false;  // True if reference is known to be in non-combinational logic
        WriteReference() = default;
        WriteReference(AstVarRef* refp, bool isNBA, bool inNonComb)
            : m_refp{refp}
            , m_isNBA{isNBA}
            , m_inNonComb{inNonComb} {}
    };

    // Data required to lower AstAssignDelay later
    struct NBA final {
        AstAssignDly* nodep = nullptr;  // The NBA this record refers to
        AstVarScope* vscp = nullptr;  // The target variable the NBA is updating, if known
        DestInfo* destp = nullptr;  // The destination the NBA is updating
        const AstCFunc* cfuncp = nullptr;  // The non-inlined function the NBA is in, if any
        bool receiver = false;  // Updating the instance of an interface its method is called on
    };

    // NODE STATE
    //  AstVar::user1()         -> bool.  Set true if already issued MULTIDRIVEN warning
    //  AstVarRef::user1()      -> bool.  Set true if target of NBA
    //  AstAssignDly::user1()   -> bool.  Set true if already visited
    //  AstCFunc::user1()       -> AstUser1Allocator.  See `m_cfuncsCache` below
    //  AstAssignDly::user2p()  -> AstVarScope*: Scope this AstAssignDelay is under
    //  AstVarScope::user1p()   -> VarScopeInfo via m_vscpInfo
    //  AstVarScope::user2p()   -> AstVarRef*: First write reference to the Variable
    //  AstVarScope::user3p()   -> std::vector<WriteReference> via m_writeRefs;
    const VNUser1InUse m_user1InUse;
    const VNUser2InUse m_user2InUse;
    const VNUser3InUse m_user3InUse;

    struct CFuncCache final {
        VInsertionSet<AstSenTree*> m_timingDomains;  // What shall be added to m_timingDomains
        std::vector<DestInfo*> m_destps;  // Destinations of the NBAs in this function
        VInsertionSet<AstCFunc*> m_calleeps;  // Functions this function calls
        std::set<AstCFunc*>
            m_includes;  // CFuncs whose CFuncCache shall be included into this - this is used to
                         // break cycles: A->B->A (instead of visiting A while it is still begin
                         // visited B just marks that it includes A)
        enum State : uint8_t {
            UNINITIALIZED = 0,  // Not initialized members are empty
            VISITING,  // Visiting - needed for breaking recursion
            INITIALIZED,  // Members contains correct values
        } m_state  // Current state of Cache
        = UNINITIALIZED;
    };

    // Caches what should be added to m_timingDomains because of calls to the AstCFunc (with
    // recursive check of other AstCFuncs called from inside)
    AstUser1Allocator<AstCFunc, CFuncCache> m_cfuncsCache;
    AstUser1Allocator<AstVarScope, VarScopeInfo> m_vscpInfo;
    AstUser3Allocator<AstVarScope, std::vector<WriteReference>> m_writeRefs;
    std::unordered_map<const AstVar*, DestInfo> m_dests;  // Destinations of NBAs, by variable
    std::vector<std::pair<const AstVar*, DestInfo*>> m_destps;  // The same, in order found

    // STATE - across all visitors
    VInsertionSet<AstSenTree*> m_timingDomains;  // Timing resume domains
    V3SharedTmps m_dlyTmps{"__Vdly", VVarType::BLOCKTEMP};  // Temporary variables
    // Commit queue data types, by element type and partial flag. Shared by all instances,
    // as m_dlyTmps only shares variables with the same data type.
    std::map<std::pair<const AstNodeDType*, bool>, AstNBACommitQueueDType*> m_cqDTypeps;

    const std::unique_ptr<V3ClassGraph>
        m_classGraphp;  // class graph to get possibly called functions from a virtual call
    std::vector<const AstCFunc*> m_callStack;  // Current callstack of AstCFuncs

    // STATE - for current visit position (use VL_RESTORER)
    AstActive* m_activep = nullptr;  // Current activate
    const AstCFunc* m_cfuncp = nullptr;  // Current public C Function
    AstNodeProcedure* m_procp = nullptr;  // Current process
    AstScope* m_scopep = nullptr;  // Current scope
    bool m_inLoop = false;  // True in for loops
    bool m_inSuspendableOrFork = false;  // True in suspendable processes and forks
    bool m_ignoreBlkAndNBlk = false;  // Suppress delayed assignment BLKANDNBLK
    bool m_inNonCombLogic = false;  // We are in non-combinational logic
    bool m_needsInitialTrigger = false;  // Whether a NodeProcedure needs a initial trigger
    std::vector<AstSenTree*> m_nbaEventSenTreeps;  // Sensitivities of '->>' in the process
    AstVarRef* m_currNbaLhsRefp = nullptr;  // Current NBA LHS variable reference
    VInsertionSet<AstCFunc*> m_procCalleeps;  // Functions the current process calls

    // STATE - during NBA conversion (after visit)
    std::vector<NBA> m_nbas;  // AstAssignDly instances to lower at the end
    std::vector<AstVarScope*> m_vscps;  // Target variables on LHSs of NBAs
    AstAssignDly* m_nextDlyp = nullptr;  // The nextp of the previous AstAssignDly
    AstVarScope* m_prevVscp = nullptr;  // The target of the previous AstAssignDly
    std::vector<ProcessCalls> m_processCalls;  // Calls of processes, to functions with NBAs
    // Processes calling functions with NBAs of Scheme::GenericQueue destinations
    std::vector<std::pair<AstNodeProcedure*, DestInfo*>> m_touchps;
    uint32_t m_nGenericQueues = 0;  // Number of destinations using Scheme::GenericQueue
    AstCDType* m_orderDTypep = nullptr;  // The type of their orders
    // The types of handles to instances of interfaces, by interface
    std::unordered_map<const AstIface*, AstIfaceRefDType*> m_ifaceRefDTypeps;
    // The instances of the variables of interfaces, by variable
    std::unordered_map<const AstVar*, std::vector<AstVarScope*>> m_ifaceVscps;

    // STATE - Statistic tracking
    VDouble0 m_nSchemeShadowVar;  // Number of variables using Scheme::ShadowVar
    VDouble0 m_nSchemeShadowVarMasked;  // Number of variabels using Scheme::ShadowVarMasked
    VDouble0 m_nSchemeFlagShared;  // Number of variables using Scheme::FlagShared
    VDouble0 m_nSchemeFlagUnique;  // Number of variables using Scheme::FlagUnique
    VDouble0 m_nSchemeValueQueuesWhole;  //  Number of variables using Scheme::ValueQueueWhole
    VDouble0 m_nSchemeValueQueuesPartial;  //  Number of variables using Scheme::ValueQueuePartial
    VDouble0 m_nSchemeGenericQueues;  // Number of variables using Scheme::GenericQueue
    VDouble0 m_nSharedSetFlags;  // "Set" flags actually shared by Scheme::FlagShared variables
    VDouble0 m_nInitialNBA;  // Number of procedural blocks with initial NBA
    VDouble0 m_nonInlinedCAwaitsWithSenTree;  // Count uses of not inlined co_awaits

    // METHODS

    // Return true iff a variable is assigned by both blocking and nonblocking
    // assignments. Issue BLKANDNBLK error if we can't prove the mixed
    // assignments are to independent bits and the blocking assignment can be
    // in combinational logic, which is something we can't safely implement
    // still.
    bool checkMixedUsage(const AstVarScope* vscp, bool isIntegralOrPacked) {

        struct Ref final {
            AstVarRef* m_refp;  // The reference
            bool m_inNonComb;  // True if known to be in non-combinational logic
            int m_lsb;  // LSB of accessed range
            int m_msb;  // MSB of accessed range
            Ref(AstVarRef* refp, bool inNonComb, int lsb, int msb)
                : m_refp{refp}
                , m_inNonComb{inNonComb}
                , m_lsb{lsb}
                , m_msb{msb} {}
        };

        std::vector<Ref> blkRefs;  // Blocking writes
        std::vector<Ref> nbaRefs;  // Non-blockign writes

        const int width = isIntegralOrPacked ? vscp->width() : 1;

        for (const auto& writeRef : m_writeRefs(vscp)) {
            int lsb = 0;
            int msb = width - 1;
            if (const AstSel* const selp = VN_CAST(writeRef.m_refp->backp(), Sel)) {
                if (VN_IS(selp->lsbp(), Const)) {
                    lsb = selp->lsbConst();
                    msb = selp->msbConst();
                }
            }
            if (writeRef.m_isNBA) {
                nbaRefs.emplace_back(writeRef.m_refp, writeRef.m_inNonComb, lsb, msb);
            } else {
                blkRefs.emplace_back(writeRef.m_refp, writeRef.m_inNonComb, lsb, msb);
            }
        }
        // We only run this function on targets of NBAs, so there should be at least one...
        UASSERT_OBJ(!nbaRefs.empty(), vscp, "Did not record NBA write");
        // If no blocking upadte, then we are good
        if (blkRefs.empty()) return false;

        // If the blocking assignment is in non-combinational logic (i.e.:
        // in logic that has an explicit trigger), then we can safely
        // implement it (there is no race between clocked logic and post
        // scheduled logic), so need not error
        blkRefs.erase(std::remove_if(blkRefs.begin(), blkRefs.end(),
                                     [](const Ref& ref) { return ref.m_inNonComb; }),
                      blkRefs.end());

        // If nothing left, then we need not error
        if (blkRefs.empty()) return true;

        // If not a packed variable, warn here as we can't prove independence
        if (!isIntegralOrPacked) {
            const Ref& blkRef = blkRefs.front();
            const Ref& nbaRef = nbaRefs.front();
            vscp->v3warn(
                BLKANDNBLK,
                "Unsupported: Blocking and non-blocking assignments to same non-packed variable: "
                    << vscp->varp()->prettyNameQ() << '\n'
                    << vscp->warnContextPrimary() << '\n'
                    << blkRef.m_refp->warnOther() << "... Location of blocking assignment\n"
                    << blkRef.m_refp->warnContextSecondary() << '\n'
                    << nbaRef.m_refp->warnOther() << "... Location of nonblocking assignment\n"
                    << nbaRef.m_refp->warnContextSecondary());
            return true;
        }

        // We need to error if we can't prove the written bits are independent

        // Sort refs by interval
        const auto lessThanRef = [](const Ref& a, const Ref& b) {
            if (a.m_lsb != b.m_lsb) return a.m_lsb < b.m_lsb;
            return a.m_msb < b.m_msb;
        };
        std::stable_sort(blkRefs.begin(), blkRefs.end(), lessThanRef);
        std::stable_sort(nbaRefs.begin(), nbaRefs.end(), lessThanRef);
        // Iterate both vectors, checking for overlap
        auto bIt = blkRefs.begin();
        auto nIt = nbaRefs.begin();
        while (bIt != blkRefs.end() && nIt != nbaRefs.end()) {
            if (lessThanRef(*bIt, *nIt)) {
                if (nIt->m_lsb <= bIt->m_msb) break;  // Stop on Overlap
                ++bIt;
            } else {
                if (bIt->m_lsb <= nIt->m_msb) break;  // Stop on Overlap
                ++nIt;
            }
        }

        // If we found an overlapping range that cannot be safely implemented, then wran...
        if (bIt != blkRefs.end() && nIt != nbaRefs.end()) {
            const Ref& blkRef = *bIt;
            const Ref& nbaRef = *nIt;
            vscp->v3warn(BLKANDNBLK, "Unsupported: Blocking and non-blocking assignments to "
                                     "potentially overlapping bits of same packed variable: "
                                         << vscp->varp()->prettyNameQ() << '\n'
                                         << vscp->warnContextPrimary() << '\n'
                                         << blkRef.m_refp->warnOther()
                                         << "... Location of blocking assignment" << " (bits ["
                                         << blkRef.m_msb << ":" << blkRef.m_lsb << "])\n"
                                         << blkRef.m_refp->warnContextSecondary() << '\n'
                                         << nbaRef.m_refp->warnOther()
                                         << "... Location of nonblocking assignment" << " (bits ["
                                         << nbaRef.m_msb << ":" << nbaRef.m_lsb << "])\n"
                                         << nbaRef.m_refp->warnContextSecondary());
        }

        return true;
    }

    // Choose the NBA scheme used for the given variable.
    Scheme chooseScheme(const AstVarScope* vscp, const VarScopeInfo& vscpInfo) {
        UASSERT_OBJ(vscpInfo.m_scheme == Scheme::Undecided, vscp, "NBA scheme already decided");

        const AstNodeDType* const dtypep = vscp->dtypep()->skipRefp();
        // Updated by an NBA with a ticket from V3Timing, ordering its pending update with the
        // others, so use a dynamic commit queue, committing all updates in the order of their
        // tickets. V3Timing ensures the queue supports all NBAs to the variable (canQueue).
        if (vscpInfo.m_ordered) {
            UASSERT_OBJ(!vscpInfo.m_whole || !VN_IS(dtypep, UnpackArrayDType), vscp,
                        "Ordered NBAs to a whole array");
            if (vscpInfo.m_partial) return Scheme::ValueQueuePartial;
            return Scheme::ValueQueueWhole;
        }
        // Unpacked arrays
        if (const AstUnpackArrayDType* const uaDTypep = VN_CAST(dtypep, UnpackArrayDType)) {
            // If whole array is target of NBA, use ShadowVar
            if (vscpInfo.m_whole) return Scheme::ShadowVar;
            // Basic underlying type of elements, if any.
            const AstBasicDType* const basicp = uaDTypep->basicp();
            // If used in a loop, we must have a dynamic commit queue. (Also works in suspendables)
            if (vscpInfo.m_inLoop) {
                // Arrays with compound element types are currently not supported in loops
                if (!isQueueable(uaDTypep)) return Scheme::UnsupportedCompoundArrayInLoop;
                if (vscpInfo.m_partial) return Scheme::ValueQueuePartial;
                return Scheme::ValueQueueWhole;
            }
            // In a suspendable of fork, we must use the unique flag scheme, TODO: why?
            if (vscpInfo.m_inSuspOrFork) return Scheme::FlagUnique;
            // Otherwise if an array of packed/basic elements, use the shared flag scheme
            if (basicp) return Scheme::FlagShared;
            // Finally fall back on the shadow variable scheme, e.g. for
            // arrays of unpacked structs. This will be slow.
            // TODO: generic LHS scheme as discussed in #5092
            return Scheme::ShadowVar;
        }

        // In a suspendable of fork, we must use the unique flag scheme, TODO: why?
        if (vscpInfo.m_inSuspOrFork) return Scheme::FlagUnique;

        const bool isIntegralOrPacked = dtypep->isIntegralOrPacked();
        // Check for mixed usage (this also warns if not OK)
        if (checkMixedUsage(vscp, isIntegralOrPacked)) {
            // If it's a variable updated by both blocking and non-blocking
            // assignments, use the ShadowVarMasked schem if masked update is
            // possible. This can handle blocking and non-blocking updates to
            // inpdendent parts correctly at run-time, and always works, even
            // in loops or other dynamic context.
            if (isIntegralOrPacked) return Scheme::ShadowVarMasked;
            // If it's inside a loop, use Scheme::ShadowVar, which is safe,
            // but will generate incorrect code if a partial update is used
            if (vscpInfo.m_inLoop) return Scheme::ShadowVar;
            // Otherwise (for not packed variables), use the FlagUnique scheme,
            // which at least handles partial updates correctly, but might break
            // in loops or other dynamic context
            return Scheme::FlagUnique;
        }

        // Otherwise use the simple shadow variable scheme
        return Scheme::ShadowVar;
    }

    // Given an expression 'exprp', return a new expression that always evaluates to the
    // value of the given expression at this point in the program. That is:
    // - If given a non-constant expression, create a new temporary AstVarScope under the given
    //   'scopep', with the given 'name', assign the expression to it, and return a read reference
    //   to the new AstVarScope.
    // - If given a constant, just return that constant.
    // New statements are inserted before 'insertp'
    AstNodeExpr* captureVal(AstScope* const scopep, AstNodeStmt* const insertp,
                            AstNodeExpr* const exprp, const std::string& name) {
        UASSERT_OBJ(!exprp->backp(), exprp, "Should have been unlinked");
        FileLine* const flp = exprp->fileline();
        if (VN_IS(exprp, Const)) return exprp;
        // TODO: there are some const variables that could be simply referenced here
        AstVarScope* const tmpVscp = m_dlyTmps.make(flp, scopep, exprp->dtypep(), name);
        insertp->addHereThisAsNext(
            new AstAssign{flp, new AstVarRef{flp, tmpVscp, VAccess::WRITE}, exprp});
        return new AstVarRef{flp, tmpVscp, VAccess::READ};
    };

    // Similar to 'captureVal', but captures an LValue expression. That is, the returned
    // expression will reference the same location as the input expression, at this point in the
    // program.
    AstNodeExpr* captureLhs(AstScope* const scopep, AstNodeStmt* const insertp,
                            AstNodeExpr* const lhsp, const std::string& baseName) {
        UASSERT_OBJ(!lhsp->backp(), lhsp, "Should have been unlinked");
        // Running node pointer
        AstNode* nodep = lhsp;
        // Capture AstSel indices - there should be only one
        if (AstSel* const selp = VN_CAST(nodep, Sel)) {
            const std::string tmpName{"Lsb" + baseName};
            selp->lsbp(captureVal(scopep, insertp, selp->lsbp()->unlinkFrBack(), tmpName));
            // Continue with target
            nodep = selp->fromp();
        }
        UASSERT_OBJ(!VN_IS(nodep, Sel), lhsp, "Multiple 'AstSel' applied to LHS reference");
        // Capture AstArraySel indices - might be many, also below unpacked struct members
        size_t nArraySels = 0;
        while (VN_IS(nodep, ArraySel) || VN_IS(nodep, StructSel)) {
            if (const AstStructSel* const structSelp = VN_CAST(nodep, StructSel)) {
                nodep = structSelp->fromp();
                continue;
            }
            AstArraySel* const arrSelp = VN_AS(nodep, ArraySel);
            const std::string tmpName{"Dim" + std::to_string(nArraySels++) + baseName};
            arrSelp->bitp(captureVal(scopep, insertp, arrSelp->bitp()->unlinkFrBack(), tmpName));
            nodep = arrSelp->fromp();
        }
        // What remains must be an AstVarRef, or some sort of select, we assume can reuse it.
        if (const AstAssocSel* const aselp = VN_CAST(nodep, AssocSel)) {
            UASSERT_OBJ(aselp->fromp()->isPure() && aselp->bitp()->isPure(), lhsp,
                        "Malformed LHS in NBA");
        } else {
            UASSERT_OBJ(nodep->isPure(), lhsp, "Malformed LHS in NBA");
        }
        // Now have been converted to use the captured values
        return lhsp;
    }

    void addCFuncCachedValues(const AstCFunc* const cfuncp,
                              std::unordered_set<const AstCFunc*>& visited) {
        if (!visited.insert(cfuncp).second) return;
        CFuncCache& value = m_cfuncsCache(cfuncp);
        m_timingDomains.insert(value.m_timingDomains.begin(), value.m_timingDomains.end());
        m_nonInlinedCAwaitsWithSenTree += value.m_timingDomains.size();
        for (const AstCFunc* const includedp : value.m_includes) {
            addCFuncCachedValues(includedp, visited);
        }
    }

    // Create a temporary variable in the given 'scopep', with the given 'name', and with 'dtypep'
    // type, with the bits selected by 'sLsbp'/'sWidthp' set to 'valuep', other bits set to zero.
    // Insert new statements before 'insertp'.
    // Returns a read reference to the temporary variable.
    AstVarRef* createWidened(FileLine* flp, AstScope* scopep, AstNodeDType* dtypep,
                             AstNodeExpr* sLsbp, int sWidth, const std::string& name,
                             AstNodeExpr* valuep, AstNode* insertp) {
        // Create temporary variable.
        AstVarScope* const tp = m_dlyTmps.make(flp, scopep, dtypep, name);
        // Zero it
        AstConst* const zerop = new AstConst{flp, AstConst::DTyped{}, dtypep};
        zerop->num().setAllBits0();
        insertp->addHereThisAsNext(
            new AstAssign{flp, new AstVarRef{flp, tp, VAccess::WRITE}, zerop});
        // Set the selected bits to 'valuep'
        AstSel* const selp = new AstSel{flp, new AstVarRef{flp, tp, VAccess::WRITE},
                                        sLsbp->cloneTreePure(true), sWidth};
        insertp->addHereThisAsNext(new AstAssign{flp, selp, valuep});
        // This is the expression to get the value of the temporary
        return new AstVarRef{flp, tp, VAccess::READ};
    }

    // Scheme::ShadowVar
    void prepareSchemeShadowVar(AstVarScope* vscp, VarScopeInfo& vscpInfo) {
        UASSERT_OBJ(vscpInfo.m_scheme == Scheme::ShadowVar, vscp, "Inconsistent NBA scheme");
        FileLine* const flp = vscp->fileline();
        AstScope* const scopep = vscp->scopep();
        // Create the shadow variable
        const std::string name = "_" + vscp->varp()->shortName();
        AstVarScope* const shadowVscp = m_dlyTmps.make(flp, scopep, vscp->dtypep(), name);
        vscpInfo.shadowVariableKit().vscp = shadowVscp;
        // Mark both for V3LifePsot
        vscp->optimizeLifePost(true);
        shadowVscp->optimizeLifePost(true);
        // Create the AstActive for the Pre/Post logic
        AstActive* const activep = new AstActive{flp, "nba-shadow-variable", vscpInfo.senTreep()};
        activep->senTreeStorep(vscpInfo.senTreep());
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
    void convertSchemeShadowVar(AstAssignDly* nodep, AstVarScope* vscp, VarScopeInfo& vscpInfo) {
        UASSERT_OBJ(vscpInfo.m_scheme == Scheme::ShadowVar, vscp, "Inconsistent NBA scheme");
        AstVarScope* const shadowVscp = vscpInfo.shadowVariableKit().vscp;

        // Replace the write ref on the LHS with the shadow variable
        nodep->lhsp()->foreach([&](AstVarRef* const refp) {
            if (!refp->access().isWriteOnly()) return;
            UASSERT_OBJ(refp->varScopep() == vscp, nodep, "NBA not setting expected variable");
            refp->varScopep(shadowVscp);
            refp->varp(shadowVscp->varp());
        });
    }

    // Scheme::ShadowVarMasked
    void prepareSchemeShadowVarMasked(AstVarScope* vscp, VarScopeInfo& vscpInfo) {
        UASSERT_OBJ(vscpInfo.m_scheme == Scheme::ShadowVarMasked, vscp, "Inconsistent NBA scheme");
        FileLine* const flp = vscp->fileline();
        AstScope* const scopep = vscp->scopep();
        // Create the shadow variable
        const std::string shadowName = "_" + vscp->varp()->shortName();
        AstVarScope* const shadowVscp = m_dlyTmps.make(flp, scopep, vscp->dtypep(), shadowName);
        vscpInfo.shadowVarMaskedKit().vscp = shadowVscp;
        // Create the makk variable
        const std::string maskName = "Mask__" + vscp->varp()->shortName();
        AstVarScope* const maskVscp = m_dlyTmps.make(flp, scopep, vscp->dtypep(), maskName);
        maskVscp->varp()->setIgnorePostWrite();
        vscpInfo.shadowVarMaskedKit().maskp = maskVscp;
        // Create the AstActive for the Post logic
        AstActive* const activep
            = new AstActive{flp, "nba-shadow-var-masked", vscpInfo.senTreep()};
        activep->senTreeStorep(vscpInfo.senTreep());
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
        // Clar the mask - maskVscp = '0;
        postp->addStmtsp(
            new AstAssign{flp, new AstVarRef{flp, maskVscp, VAccess::WRITE},
                          new AstConst{flp, AstConst::WidthedValue{}, maskVscp->width(), 0}});
    }
    void convertSchemeShadowVarMasked(AstAssignDly* nodep, AstVarScope* vscp,
                                      VarScopeInfo& vscpInfo) {
        UASSERT_OBJ(vscpInfo.m_scheme == Scheme::ShadowVarMasked, vscp, "Inconsistent NBA scheme");
        AstVarScope* const shadowVscp = vscpInfo.shadowVarMaskedKit().vscp;
        AstVarScope* const maskVscp = vscpInfo.shadowVarMaskedKit().maskp;

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
    void prepareSchemeFlagShared(AstVarScope* vscp, VarScopeInfo& vscpInfo) {
        UASSERT_OBJ(vscpInfo.m_scheme == Scheme::FlagShared, vscp, "Inconsistent NBA scheme");
        FileLine* const flp = vscp->fileline();
        AstScope* const scopep = vscp->scopep();
        // Create the AstActive for the Pre/Post logic
        AstActive* const activep = new AstActive{flp, "nba-flag-shared", vscpInfo.senTreep()};
        activep->senTreeStorep(vscpInfo.senTreep());
        scopep->addBlocksp(activep);
        vscpInfo.flagSharedKit().activep = activep;
        // Add 'Post' scheduled process to be populated later
        AstAlwaysPost* const postp = new AstAlwaysPost{flp};
        activep->addStmtsp(postp);
        vscpInfo.flagSharedKit().postp = postp;
        // Initialize
        vscpInfo.flagSharedKit().commitFlagp = nullptr;
        vscpInfo.flagSharedKit().commitIfp = nullptr;
    }
    void convertSchemeFlagShared(AstAssignDly* nodep, AstVarScope* vscp, VarScopeInfo& vscpInfo) {
        UASSERT_OBJ(vscpInfo.m_scheme == Scheme::FlagShared, vscp, "Inconsistent NBA scheme");
        FileLine* const flp = vscp->fileline();
        AstScope* const scopep = VN_AS(nodep->user2p(), Scope);

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

        VarScopeInfo* const prevVscpInfop = consecutive ? &m_vscpInfo(m_prevVscp) : nullptr;

        // We can reuse the flag of the previous assignment if:
        const bool reuseTheFlag =
            // Consecutive NBAs
            consecutive
            // ... that use the same scheme
            && prevVscpInfop->m_scheme == Scheme::FlagShared
            // ... and are in the same scope as the target variable
            && scopep == vscp->scopep()
            // ... and share the same overall update domain
            && prevVscpInfop->senTreep()->sameTree(vscpInfo.senTreep());

        if (!reuseTheFlag) {
            // Create new flag
            AstVarScope* const flagVscp = m_dlyTmps.make(flp, scopep, 1, "Set" + baseName);
            // Set the flag at the original NBA
            nodep->addHereThisAsNext(  //
                new AstAssign{flp, new AstVarRef{flp, flagVscp, VAccess::WRITE},
                              new AstConst{flp, AstConst::BitTrue{}}});
            // Add the 'Pre' scheduled reset for the flag
            AstAlwaysPre* const prep = new AstAlwaysPre{flp};
            vscpInfo.flagSharedKit().activep->addStmtsp(prep);
            prep->addStmtsp(new AstAssign{flp, new AstVarRef{flp, flagVscp, VAccess::WRITE},
                                          new AstConst{flp, AstConst::BitFalse{}}});
            // Add the 'Post' scheduled commit
            AstIf* const ifp = new AstIf{flp, new AstVarRef{flp, flagVscp, VAccess::READ}};
            vscpInfo.flagSharedKit().postp->addStmtsp(ifp);
            vscpInfo.flagSharedKit().commitFlagp = flagVscp;
            vscpInfo.flagSharedKit().commitIfp = ifp;
        } else {
            if (vscp != m_prevVscp) {
                // Different variable, ensure the commit block exists for this variable,
                // can reuse existing one with the same flag, otherwise create a new one.
                AstVarScope* const flagVscp = prevVscpInfop->flagSharedKit().commitFlagp;
                UASSERT_OBJ(flagVscp, nodep, "Commit flag of previous assignment should exist");
                if (vscpInfo.flagSharedKit().commitFlagp != flagVscp) {
                    AstIf* const ifp = new AstIf{flp, new AstVarRef{flp, flagVscp, VAccess::READ}};
                    vscpInfo.flagSharedKit().postp->addStmtsp(ifp);
                    vscpInfo.flagSharedKit().commitFlagp = flagVscp;
                    vscpInfo.flagSharedKit().commitIfp = ifp;
                }
            } else {
                // Same variable, reuse the commit block of the previous assignment
                vscpInfo.flagSharedKit().commitFlagp = prevVscpInfop->flagSharedKit().commitFlagp;
                vscpInfo.flagSharedKit().commitIfp = prevVscpInfop->flagSharedKit().commitIfp;
            }
            ++m_nSharedSetFlags;
        }
        // Commit the captured value to the captured destination
        vscpInfo.flagSharedKit().commitIfp->addThensp(
            new AstAssign{flp, capturedLhsp, capturedRhsp});

        // Remember the variable for the next NBA
        m_prevVscp = vscp;

        // Delete original NBA
        VL_DO_DANGLING(pushDeletep(nodep->unlinkFrBack()), nodep);
    }

    // Scheme::FlagUnique
    void prepareSchemeFlagUnique(AstVarScope* vscp, VarScopeInfo& vscpInfo) {
        UASSERT_OBJ(vscpInfo.m_scheme == Scheme::FlagUnique, vscp, "Inconsistent NBA scheme");
        FileLine* const flp = vscp->fileline();
        AstScope* const scopep = vscp->scopep();
        // Create the AstActive for the Pre/Post logic
        AstActive* const activep = new AstActive{flp, "nba-flag-unique", vscpInfo.senTreep()};
        activep->senTreeStorep(vscpInfo.senTreep());
        scopep->addBlocksp(activep);
        // Add 'Post' scheduled process to be populated later
        AstAlwaysPost* const postp = new AstAlwaysPost{flp};
        activep->addStmtsp(postp);
        vscpInfo.flagUniqueKit().postp = postp;
    }
    void convertSchemeFlagUnique(AstAssignDly* nodep, AstVarScope* vscp, VarScopeInfo& vscpInfo) {
        UASSERT_OBJ(vscpInfo.m_scheme == Scheme::FlagUnique, vscp, "Inconsistent NBA scheme");
        FileLine* const flp = vscp->fileline();
        AstScope* const scopep = VN_AS(nodep->user2p(), Scope);

        // Base name suffix for signals constructed below
        const std::string baseName = "__" + vscp->varp()->shortName();

        // Unlink and capture the RHS value
        AstNodeExpr* const capturedRhsp
            = captureVal(scopep, nodep, nodep->rhsp()->unlinkFrBack(), "Val" + baseName);

        // Unlink and capture the LHS reference
        AstNodeExpr* const capturedLhsp
            = captureLhs(scopep, nodep, nodep->lhsp()->unlinkFrBack(), baseName);

        // Create new flag
        AstVarScope* const flagVscp = m_dlyTmps.make(flp, scopep, 1, "Set" + baseName);
        flagVscp->varp()->setIgnorePostWrite();
        // Set the flag at the original NBA
        nodep->addHereThisAsNext(  //
            new AstAssign{flp, new AstVarRef{flp, flagVscp, VAccess::WRITE},
                          new AstConst{flp, AstConst::BitTrue{}}});
        // Add the 'Post' scheduled commit
        AstIf* const ifp = new AstIf{flp, new AstVarRef{flp, flagVscp, VAccess::READ}};
        vscpInfo.flagUniqueKit().postp->addStmtsp(ifp);
        // Immediately clear the flag
        ifp->addThensp(new AstAssign{flp, new AstVarRef{flp, flagVscp, VAccess::WRITE},
                                     new AstConst{flp, AstConst::BitFalse{}}});
        // Commit the value
        ifp->addThensp(new AstAssign{flp, capturedLhsp, capturedRhsp});

        // Delete original NBA
        VL_DO_DANGLING(pushDeletep(nodep->unlinkFrBack()), nodep);
    }

    // Scheme::ValueQueuePartial/Scheme::ValueQueueWhole
    template <bool N_Partial>
    void prepareSchemeValueQueue(AstVarScope* vscp, VarScopeInfo& vscpInfo) {
        UASSERT_OBJ(N_Partial ? vscpInfo.m_scheme == Scheme::ValueQueuePartial
                              : vscpInfo.m_scheme == Scheme::ValueQueueWhole,
                    vscp, "Inconsistent NBA scheme");
        FileLine* const flp = vscp->fileline();
        AstScope* const scopep = vscp->scopep();

        // Create the commit queue variable
        AstNodeDType* const elemDTypep = vscp->dtypep()->skipRefp();
        AstNBACommitQueueDType*& cqDTypep = m_cqDTypeps[{elemDTypep, N_Partial}];
        if (!cqDTypep) {
            cqDTypep = new AstNBACommitQueueDType{flp, elemDTypep, N_Partial};
            v3Global.rootp()->typeTablep()->addTypesp(cqDTypep);
        }
        const std::string name = "CommitQueue__" + vscp->varp()->shortName();
        AstVarScope* const queueVscp = m_dlyTmps.make(flp, scopep, cqDTypep, name);
        queueVscp->varp()->noReset(true);
        queueVscp->varp()->setIgnorePostWrite();
        vscpInfo.valueQueueKit().vscp = queueVscp;
        // Create the AstActive for the Post logic
        AstActive* const activep
            = new AstActive{flp, "nba-value-queue-whole", vscpInfo.senTreep()};
        activep->senTreeStorep(vscpInfo.senTreep());
        scopep->addBlocksp(activep);
        // Add 'Post' scheduled process for the commit
        AstAlwaysPost* const postp = new AstAlwaysPost{flp};
        activep->addStmtsp(postp);
        // Add the commit
        AstCMethodHard* const callp = new AstCMethodHard{
            flp, new AstVarRef{flp, queueVscp, VAccess::READWRITE}, VCMethod::NBA_COMMIT};
        callp->dtypeSetVoid();
        // TODO: this is a partial update, so must be READWRITE, but that breaks scheduling
        callp->addPinsp(new AstVarRef{flp, vscp, VAccess::WRITE});
        postp->addStmtsp(callp->makeStmt());
    }

    void convertSchemeValueQueue(AstAssignDly* nodep, AstVarScope* vscp, VarScopeInfo& vscpInfo,
                                 bool partial) {
        UASSERT_OBJ(partial ? vscpInfo.m_scheme == Scheme::ValueQueuePartial
                            : vscpInfo.m_scheme == Scheme::ValueQueueWhole,
                    vscp, "Inconsistent NBA scheme");
        FileLine* const flp = vscp->fileline();
        AstScope* const scopep = VN_AS(nodep->user2p(), Scope);

        // Base name suffix for signals constructed below
        const std::string baseName = "__" + vscp->varp()->shortName();

        // Unlink and capture the RHS value
        AstNodeExpr* const capturedRhsp
            = captureVal(scopep, nodep, nodep->rhsp()->unlinkFrBack(), "Val" + baseName);

        // Unlink and capture the LHS reference
        AstNodeExpr* const capturedLhsp
            = captureLhs(scopep, nodep, nodep->lhsp()->unlinkFrBack(), baseName);

        // RHS value (can be widened/masked iff Partial)
        AstNodeExpr* valuep = capturedRhsp;
        // RHS mask (iff Partial)
        AstNodeExpr* maskp = nullptr;

        // Running node for LHS deconstruction
        AstNodeExpr* lhsNodep = capturedLhsp;

        // If partial updates are required, construct the mask and the widened value
        if (partial) {
            // Type of array element
            AstNodeDType* const eDTypep = [&]() -> AstNodeDType* {
                AstNodeDType* dtypep = vscp->dtypep()->skipRefp();
                while (AstUnpackArrayDType* const ap = VN_CAST(dtypep, UnpackArrayDType)) {
                    dtypep = ap->subDTypep()->skipRefp();
                }
                return dtypep;
            }();

            if (const AstSel* const lSelp = VN_CAST(lhsNodep, Sel)) {
                // This is a partial assignment.
                // Need to create a mask and widen the value to element size.
                lhsNodep = lSelp->fromp();
                AstNodeExpr* const sLsbp = lSelp->lsbp();
                const int sWidth = lSelp->widthConst();

                // Create mask value
                maskp = [&]() -> AstNodeExpr* {
                    // Constant mask we can compute here
                    if (const AstConst* const cLsbp = VN_CAST(sLsbp, Const)) {
                        AstConst* const cp = new AstConst{flp, AstConst::DTyped{}, eDTypep};
                        cp->num().setMask(sWidth, cLsbp->toSInt());
                        return cp;
                    }

                    // A non-constant mask we must compute at run-time.
                    AstConst* const onesp = new AstConst{flp, AstConst::WidthedValue{}, sWidth, 0};
                    onesp->num().setAllBits1();
                    return createWidened(flp, scopep, eDTypep, sLsbp, sWidth, "Mask" + baseName,
                                         onesp, nodep);
                }();

                // Adjust value to element size
                valuep = [&]() -> AstNodeExpr* {
                    // Constant value with constant select we can compute here
                    if (AstConst* const cValuep = VN_CAST(valuep, Const)) {
                        if (const AstConst* const cLsbp = VN_CAST(sLsbp, Const)) {
                            AstConst* const cp = new AstConst{flp, AstConst::DTyped{}, eDTypep};
                            cp->num().setAllBits0();
                            cp->num().opSelInto(cValuep->num(), cLsbp->toSInt(), sWidth);
                            VL_DO_DANGLING(valuep->deleteTree(), valuep);
                            return cp;
                        }
                    }

                    // A non-constant value we must adjust.
                    return createWidened(flp, scopep, eDTypep, sLsbp, sWidth,  //
                                         "Elem" + baseName, valuep, nodep);
                }();
            } else {
                // If this assignment is not partial, set mask to ones and we are done
                AstConst* const ones = new AstConst{flp, AstConst::DTyped{}, eDTypep};
                ones->num().setAllBits1();
                maskp = ones;
            }
        }

        // Extract array indices, none of a variable that is not an array
        std::vector<AstNodeExpr*> idxps;
        {
            UASSERT_OBJ(vscpInfo.m_ordered || VN_IS(lhsNodep, ArraySel), lhsNodep,
                        "Unexpected LHS form");
            while (AstArraySel* const aSelp = VN_CAST(lhsNodep, ArraySel)) {
                idxps.emplace_back(aSelp->bitp()->unlinkFrBack());
                lhsNodep = aSelp->fromp();
            }
            UASSERT_OBJ(VN_IS(lhsNodep, VarRef), lhsNodep, "Unexpected LHS form");
            std::reverse(idxps.begin(), idxps.end());
        }

        // Done with the LHS at this point
        VL_DO_DANGLING(pushDeletep(capturedLhsp), capturedLhsp);

        // The ticket ordering the update: given by V3Timing if it was pending, or else taken
        // now if updates of the variable are ordered, otherwise all are enqueued in order
        AstNodeExpr* ticketp = nodep->ticketp();
        if (ticketp) {
            ticketp->unlinkFrBack();
        } else if (vscpInfo.m_ordered) {
            ticketp = V3Delayed::newTicketp(flp);
        } else {
            ticketp = new AstConst{flp, AstConst::Unsized64{}, 0};
        }

        // Enqueue the update at the site of the original NBA
        AstCMethodHard* const callp = new AstCMethodHard{
            flp, new AstVarRef{flp, vscpInfo.valueQueueKit().vscp, VAccess::READWRITE},
            VCMethod::NBA_ENQUEUE};
        callp->dtypeSetVoid();
        callp->addPinsp(ticketp);
        callp->addPinsp(valuep);
        if (partial) callp->addPinsp(maskp);
        for (AstNodeExpr* const indexp : idxps) callp->addPinsp(indexp);
        nodep->addHereThisAsNext(callp->makeStmt());

        // Delete original NBA
        VL_DO_DANGLING(pushDeletep(nodep->unlinkFrBack()), nodep);
    }

    // Scheme::GenericQueue
    void prepareSchemeGenericQueue(const AstVar* varp, DestInfo& dest) {
        FileLine* const flp = varp->fileline();
        AstTopScope* const topScopep = v3Global.rootp()->topScopep();
        AstScope* const scopep = topScopep->scopep();
        dest.m_id = m_nGenericQueues++;
        const std::string suffix = std::to_string(dest.m_id) + "__" + varp->shortName();
        // Create the order of the updates, the site and index variables
        if (!m_orderDTypep) {
            m_orderDTypep = new AstCDType{flp, "VlNBAOrder"};
            v3Global.rootp()->typeTablep()->addTypesp(m_orderDTypep);
        }
        dest.m_orderVscp = topScopep->createTemp("__VnbaOrder" + suffix, m_orderDTypep);
        dest.m_orderVscp->varp()->noReset(true);
        dest.m_orderVscp->varp()->setIgnorePostWrite();
        dest.m_siteVscp = m_dlyTmps.make(flp, scopep, 32, "Site" + suffix);
        dest.m_siteVscp->varp()->setIgnorePostWrite();
        dest.m_indexVscp = m_dlyTmps.make(flp, scopep, 32, "Index" + suffix);
        dest.m_indexVscp->varp()->setIgnorePostWrite();
        // Create the AstActive for the Post logic
        UASSERT_OBJ(dest.senTreep(), varp, "NBA without sensitivity");
        AstActive* const activep = new AstActive{flp, "nba-generic-queue", dest.senTreep()};
        activep->senTreeStorep(dest.senTreep());
        scopep->addBlocksp(activep);
        // Add 'Post' scheduled process for the commit
        dest.m_postp = new AstAlwaysPost{flp};
        activep->addStmtsp(dest.m_postp);
        // Add the loop applying the updates in order, to be populated later
        dest.m_loopp = new AstLoop{flp};
        dest.m_postp->addStmtsp(dest.m_loopp);
        AstCMethodHard* const nextp
            = new AstCMethodHard{flp, new AstVarRef{flp, dest.m_orderVscp, VAccess::READWRITE},
                                 VCMethod::NBA_ORDER_NEXT};
        nextp->dtypeSetBit();
        dest.m_loopp->addStmtsp(new AstLoopTest{flp, dest.m_loopp, nextp});
        const auto assignFromOrder = [&](AstVarScope* vscp, VCMethod method) {
            AstCMethodHard* const callp = new AstCMethodHard{
                flp, new AstVarRef{flp, dest.m_orderVscp, VAccess::READ}, method};
            callp->dtypeSetUInt32();
            dest.m_loopp->addStmtsp(
                new AstAssign{flp, new AstVarRef{flp, vscp, VAccess::WRITE}, callp});
        };
        assignFromOrder(dest.m_siteVscp, VCMethod::NBA_ORDER_SITE);
        assignFromOrder(dest.m_indexVscp, VCMethod::NBA_ORDER_INDEX);
    }
    void convertSchemeGenericQueue(AstAssignDly* nodep, const NBA& nba) {
        DestInfo& dest = *nba.destp;
        FileLine* const flp = nodep->fileline();
        AstScope* const scopep = v3Global.rootp()->topScopep()->scopep();
        const uint32_t site = dest.m_nSites++;
        const std::string suffix = std::to_string(dest.m_id) + "_" + std::to_string(site) + "_";
        size_t nQueues = 0;
        AstNodeStmt* enqueuesp = nullptr;  // Statements enqueueing the update, replacing the NBA
        AstNodeStmt* loadsp = nullptr;  // Statements of the commit loading values of the update
        // Enqueue the value of the given expression, of the given type, in a new queue of the
        // site, and return the expression reading it in the commit
        const auto enqueue = [&](AstNodeExpr* valuep, AstNodeDType* dtypep) {
            AstQueueDType* const queueDTypep = new AstQueueDType{flp, dtypep, nullptr};
            v3Global.rootp()->typeTablep()->addTypesp(queueDTypep);
            AstVarScope* const queueVscp = v3Global.rootp()->topScopep()->createTemp(
                "__VnbaQueue" + suffix + std::to_string(nQueues++), queueDTypep);
            queueVscp->varp()->noReset(true);
            queueVscp->varp()->setIgnorePostWrite();
            dest.m_queueVscps.push_back(queueVscp);
            AstCMethodHard* const pushp
                = new AstCMethodHard{flp, new AstVarRef{flp, queueVscp, VAccess::READWRITE},
                                     VCMethod::ARRAY_PUSH_BACK, valuep};
            pushp->dtypeSetVoid();
            enqueuesp = AstNode::addNext(enqueuesp, pushp->makeStmt());
            AstCMethodHard* const atp = new AstCMethodHard{
                flp, new AstVarRef{flp, queueVscp, VAccess::READ}, VCMethod::ARRAY_AT,
                new AstVarRef{flp, dest.m_indexVscp, VAccess::READ}};
            atp->dtypep(dtypep);
            return atp;
        };
        // Enqueue the given value, and return a reference to a new variable the commit loads it in
        const auto enqueueLoaded = [&](AstNodeExpr* valuep) {
            AstVarScope* const loadVscp = m_dlyTmps.make(
                flp, scopep, valuep->dtypep(), "Load" + suffix + std::to_string(nQueues));
            loadVscp->varp()->setIgnorePostWrite();
            loadsp = AstNode::addNext<AstNodeStmt, AstNodeStmt>(
                loadsp, new AstAssign{flp, new AstVarRef{flp, loadVscp, VAccess::WRITE},
                                      enqueue(valuep, valuep->dtypep())});
            return new AstVarRef{flp, loadVscp, VAccess::READ};
        };
        // Like other schemes, evaluate the value, then the expressions selecting the target,
        // which in the commit read the values they had
        AstNodeExpr* lhsp = nodep->lhsp()->unlinkFrBack();
        AstNodeExpr* const valuep = enqueue(nodep->rhsp()->unlinkFrBack(), lhsp->dtypep());
        const auto capture = [&](AstNodeExpr* exprp) {
            if (VN_IS(exprp, Const)) return;
            VNRelinker relinker;
            exprp->unlinkFrBack(&relinker);
            relinker.relink(enqueueLoaded(exprp));
        };
        AstNodeExpr* basep = lhsp;
        while (true) {
            if (AstSel* const selp = VN_CAST(basep, Sel)) {
                capture(selp->lsbp());
                basep = selp->fromp();
            } else if (AstNodeSel* const selp = VN_CAST(basep, NodeSel)) {
                capture(selp->bitp());
                basep = selp->fromp();
            } else if (const AstStructSel* const selp = VN_CAST(basep, StructSel)) {
                basep = selp->fromp();
            } else {
                break;
            }
        }
        if (AstMemberSel* const selp = VN_CAST(basep, MemberSel)) {
            // The handle selecting the target (IEEE 1800-2023 10.4.2), which is only read
            AstNodeExpr* const handlep = selp->fromp()->unlinkFrBack();
            V3LinkLValue::linkLValueSet(handlep, VAccess::READ);
            AstVarRef* const refp = enqueueLoaded(handlep);
            // Like the handle it replaces, mark one selecting a written member written
            refp->access(selp->access());
            selp->fromp(refp);
        } else if (nba.receiver) {
            // The variable is of the instance of the interface the method is called on, which
            // is 'this' of the generated method, kept as methods with a CExpr are not inlined
            UASSERT_OBJ(!nba.cfuncp->isLoose(), nodep, "Receiver of a loose function");
            AstVarRef* const refp = VN_AS(basep, VarRef);
            AstCExpr* const selfp = new AstCExpr{flp, "this"};
            selfp->dtypep(ifaceRefDTypep(VN_AS(refp->varScopep()->scopep()->modp(), Iface)));
            AstVarRef* const selfRefp = enqueueLoaded(selfp);
            selfRefp->access(refp->access());
            AstMemberSel* const newp = new AstMemberSel{flp, selfRefp, refp->varp()};
            newp->access(refp->access());
            if (refp == lhsp) {
                lhsp = newp;
            } else {
                refp->replaceWith(newp);
            }
            VL_DO_DANGLING(pushDeletep(refp), refp);
        }
        // Add the update to the order, with its ticket: given by V3Timing if it was pending, or
        // else taken now if updates of the destination are ordered, otherwise all in order
        AstNodeExpr* ticketp = nodep->ticketp();
        if (ticketp) {
            ticketp->unlinkFrBack();
        } else if (dest.m_ordered) {
            ticketp = V3Delayed::newTicketp(flp);
        } else {
            ticketp = new AstConst{flp, AstConst::Unsized64{}, 0};
        }
        AstCMethodHard* const addp
            = new AstCMethodHard{flp, new AstVarRef{flp, dest.m_orderVscp, VAccess::READWRITE},
                                 VCMethod::NBA_ORDER_ADD, ticketp};
        addp->addPinsp(new AstConst{flp, site});
        addp->dtypeSetVoid();
        enqueuesp = AstNode::addNext(enqueuesp, addp->makeStmt());
        // A function can be executed in a context not known to trigger the commit, so commit
        // also after the NBA event
        if (nba.cfuncp) {
            enqueuesp = AstNode::addNext<AstNodeStmt, AstNodeStmt>(
                enqueuesp,
                new AstAssign{
                    flp, new AstVarRef{flp, v3Global.rootp()->nbaEventTriggerp(), VAccess::WRITE},
                    new AstConst{flp, AstConst::BitTrue{}}});
        }
        // The commit applies the update if it is of this site
        AstIf* const ifp
            = new AstIf{flp, new AstEq{flp, new AstVarRef{flp, dest.m_siteVscp, VAccess::READ},
                                       new AstConst{flp, site}}};
        if (loadsp) ifp->addThensp(loadsp);
        ifp->addThensp(new AstAssign{flp, lhsp, valuep});
        dest.m_loopp->addStmtsp(ifp);
        // Replace the NBA
        nodep->addHereThisAsNext(enqueuesp);
        VL_DO_DANGLING(pushDeletep(nodep->unlinkFrBack()), nodep);
    }
    void finishSchemeGenericQueue(const AstVar* varp, DestInfo& dest) {
        FileLine* const flp = varp->fileline();
        // After the commit applied all updates, clear the queues of their values
        for (AstVarScope* const queueVscp : dest.m_queueVscps) {
            AstCMethodHard* const clearp = new AstCMethodHard{
                flp, new AstVarRef{flp, queueVscp, VAccess::WRITE}, VCMethod::DYN_CLEAR};
            clearp->dtypeSetVoid();
            dest.m_postp->addStmtsp(clearp->makeStmt());
        }
        // For scheduling, the commit through handles updates the variable of all instances of
        // the interface, which the handles can select (none if of a class, not scheduled)
        if (!dest.m_handle) return;
        AstCMethodHard* const writesp = new AstCMethodHard{
            flp, new AstVarRef{flp, dest.m_orderVscp, VAccess::READ}, VCMethod::NBA_ORDER_WRITES};
        writesp->dtypeSetVoid();
        for (AstVarScope* const vscp : m_ifaceVscps[varp]) {
            writesp->addPinsp(new AstVarRef{flp, vscp, VAccess::WRITE});
        }
        dest.m_postp->addStmtsp(writesp->makeStmt());
    }
    // The type of a handle to an instance of the given interface
    AstIfaceRefDType* ifaceRefDTypep(AstIface* ifacep) {
        AstIfaceRefDType*& dtypep = m_ifaceRefDTypeps[ifacep];
        if (!dtypep) {
            dtypep = new AstIfaceRefDType{ifacep->fileline(), "", ifacep->name()};
            dtypep->ifacep(ifacep);
            dtypep->isVirtual(true);
            dtypep->dtypep(dtypep);
            v3Global.rootp()->typeTablep()->addTypesp(dtypep);
        }
        return dtypep;
    }
    // The info of the destination of NBAs to the given variable
    DestInfo& getDest(const AstVar* varp) {
        const auto pair = m_dests.emplace(std::piecewise_construct, std::forward_as_tuple(varp),
                                          std::forward_as_tuple());
        if (pair.second) m_destps.emplace_back(varp, &pair.first->second);
        return pair.first->second;
    }
    // Add sensitivities to the target variable and destination of an NBA
    void addNbaSensitivity(const NBA& nba, AstSenItem* nodep) {
        if (nba.vscp) m_vscpInfo(nba.vscp).addSensitivity(nodep);
        nba.destp->addSensitivity(nodep);
    }

    // Record where a variable is assigned
    void recordWriteRef(AstVarRef* nodep, bool nonBlocking) {
        // Ignore references in certain contexts
        if (m_ignoreBlkAndNBlk) return;
        // Ignore if it's an array
        // TODO: we do this because it used to be the previous behaviour.
        //       Is it still required, or should we warn for arrays as well?
        //       Scheduling is no different for them...
        //       Clarification: This is OK for arrays of primitive types, but
        //       arrays that use the ShadowVar scheme don't work...
        if (VN_IS(nodep->varScopep()->dtypep()->skipRefp(), UnpackArrayDType)) return;

        m_writeRefs(nodep->varScopep()).emplace_back(nodep, nonBlocking, m_inNonCombLogic);
    }

    // Record a function called by the current function or process
    void recordCallee(AstCFunc* cfuncp) {
        if (m_cfuncp) {
            m_cfuncsCache(m_cfuncp).m_calleeps.insert(cfuncp);
        } else if (m_procp) {
            m_procCalleeps.insert(cfuncp);
        }
    }

    template <typename Procedure_T>
    static bool isProcedureWithSentreep(const AstNodeProcedure* const nodep) {
        const Procedure_T* const procedurep = AstNode::cast<Procedure_T>(nodep);
        return procedurep && procedurep->sentreep();
    }

    // Visit AstCFunc from a AstNodeCCall - this is made into a separate quasi-visitor because
    // AstCFunc that is not called from the code (e.g.: DPI exports) does not need to be visited
    // this way. Also, not visiting such AstCFuncs allows to avoid caching results for them which
    // this function does - which could lead to excessive memory usage
    void visitCalledCFunc(AstCFunc* const nodep) {
        CFuncCache& value = m_cfuncsCache(nodep);
        switch (value.m_state) {
        case CFuncCache::UNINITIALIZED: {
            // Save current state
            VL_RESTORER_CLEAR(m_timingDomains);

            // Visit
            value.m_state = CFuncCache::VISITING;
            m_callStack.push_back(nodep);
            {
                VL_RESTORER(m_cfuncp);
                m_cfuncp = nodep;
                iterateChildren(nodep);
            }
            m_callStack.pop_back();
            value.m_state = CFuncCache::INITIALIZED;

            // Save a cache
            std::swap(m_timingDomains, value.m_timingDomains);
        } break;
        case CFuncCache::VISITING: {
            for (size_t i = m_callStack.size() - 1; m_callStack.at(i) != nodep; --i) {
                m_cfuncsCache(m_callStack[i]).m_includes.insert(nodep);
            }
            return;  // Break recursion
        }
        case CFuncCache::INITIALIZED: break;
        }
        std::unordered_set<const AstCFunc*> visited;
        addCFuncCachedValues(nodep, visited);
    }

    // VISITORS
    void visit(AstNetlist* nodep) override {
        iterateChildren(nodep);
        // The NBAs in functions are executed in the contexts of the processes calling them, so
        // add the sensitivities of the processes to their destinations
        if (std::none_of(m_destps.begin(), m_destps.end(),
                         [](const auto& pair) { return pair.second->m_inCFunc; })) {
            m_processCalls.clear();
        }
        for (const ProcessCalls& calls : m_processCalls) {
            // The destinations of the NBAs in the functions the process calls
            VInsertionSet<DestInfo*> destps;
            std::unordered_set<const AstCFunc*> visited;
            std::vector<const AstCFunc*> stack{calls.m_calleeps.begin(), calls.m_calleeps.end()};
            while (!stack.empty()) {
                const AstCFunc* const cfuncp = stack.back();
                stack.pop_back();
                if (!visited.insert(cfuncp).second) continue;
                const CFuncCache& cache = m_cfuncsCache(cfuncp);
                destps.insert(cache.m_destps.begin(), cache.m_destps.end());
                stack.insert(stack.end(), cache.m_calleeps.begin(), cache.m_calleeps.end());
            }
            if (destps.empty()) continue;
            // The sensitivities of the process: its clock, if clocked, otherwise the initial NBA
            // region, like for its NBAs, and its timing domains
            AstSenItem* const sensesp
                = calls.m_clockedp
                      ? calls.m_clockedp->sensesp()->cloneTree(true)
                      : new AstSenItem{calls.m_procp->fileline(), AstSenItem::InitialNBA{}};
            for (const AstSenTree* const domainp : calls.m_domainps) {
                if (domainp->sensesp()) sensesp->addNext(domainp->sensesp()->cloneTree(true));
            }
            for (DestInfo* const destp : destps) {
                destp->addSensitivity(sensesp);
                // For scheduling, in the 'nba' region, the commit is after the process
                if (!calls.m_procp->isSuspendable()) m_touchps.emplace_back(calls.m_procp, destp);
            }
            VL_DO_DANGLING(sensesp->deleteTree(), sensesp);
        }
        // Decide which destinations use Scheme::GenericQueue and do the 'prepare' step
        for (const auto& pair : m_destps) {
            DestInfo& dest = *pair.second;
            if (!dest.isGeneric()) continue;
            // A function can be executed in a context not known above, so commit also after the
            // NBA event, which the NBA sets the trigger of
            if (dest.m_inCFunc) {
                FileLine* const flp = pair.first->fileline();
                AstSenItem* const itemp = new AstSenItem{
                    flp, VEdgeType::ET_EVENT,
                    new AstVarRef{flp, V3Delayed::nbaEventp(nodep), VAccess::READ}};
                dest.addSensitivity(itemp);
                VL_DO_DANGLING(itemp->deleteTree(), itemp);
            }
            ++m_nSchemeGenericQueues;
            prepareSchemeGenericQueue(pair.first, dest);
        }
        // Decide which scheme to use for each variable and do the 'prepare' step
        for (AstVarScope* const vscp : m_vscps) {
            VarScopeInfo& vscpInfo = m_vscpInfo(vscp);
            if (m_dests.at(vscp->varp()).isGeneric()) {
                vscpInfo.m_scheme = Scheme::GenericQueue;
                continue;
            }
            vscpInfo.m_scheme = chooseScheme(vscp, vscpInfo);
            // Run 'prepare' step
            switch (vscpInfo.m_scheme) {
            case Scheme::Undecided:  // LCOV_EXCL_START
                UASSERT_OBJ(false, vscp, "Failed to choose NBA scheme");
                break;  // LCOV_EXCL_STOP
            case Scheme::UnsupportedCompoundArrayInLoop: {
                // Will report error at the site of the NBA
                break;
            }
            case Scheme::ShadowVar: {
                ++m_nSchemeShadowVar;
                prepareSchemeShadowVar(vscp, vscpInfo);
                break;
            }
            case Scheme::ShadowVarMasked: {
                ++m_nSchemeShadowVarMasked;
                prepareSchemeShadowVarMasked(vscp, vscpInfo);
                break;
            }
            case Scheme::FlagShared: {
                ++m_nSchemeFlagShared;
                prepareSchemeFlagShared(vscp, vscpInfo);
                break;
            }
            case Scheme::FlagUnique: {
                ++m_nSchemeFlagUnique;
                prepareSchemeFlagUnique(vscp, vscpInfo);
                break;
            }
            case Scheme::ValueQueueWhole: {
                ++m_nSchemeValueQueuesWhole;
                prepareSchemeValueQueue</* Partial: */ false>(vscp, vscpInfo);
                break;
            }
            case Scheme::ValueQueuePartial: {
                ++m_nSchemeValueQueuesPartial;
                prepareSchemeValueQueue</* Partial: */ true>(vscp, vscpInfo);
                break;
            }
            case Scheme::GenericQueue: {  // LCOV_EXCL_START
                UASSERT_OBJ(false, vscp, "Destination should have prepared the scheme");
                break;
            }  // LCOV_EXCL_STOP
            }
        }
        // Convert all NBAs
        for (const NBA& nba : m_nbas) {
            AstAssignDly* const nbap = nba.nodep;
            if (nba.destp->isGeneric()) {
                convertSchemeGenericQueue(nbap, nba);
                continue;
            }
            AstVarScope* const vscp = nba.vscp;
            VarScopeInfo& vscpInfo = m_vscpInfo(vscp);
            // Run 'convert' step
            switch (vscpInfo.m_scheme) {
            case Scheme::Undecided: {  // LCOV_EXCL_START
                UASSERT_OBJ(false, vscp, "Unreachable");
                break;
            }  // LCOV_EXCL_STOP
            case Scheme::UnsupportedCompoundArrayInLoop: {
                // TODO: make this an E_UNSUPPORTED...
                nbap->v3warn(BLKLOOPINIT, "Unsupported: Non-blocking assignment to array with "
                                          "compound element type inside loop");
                break;
            }
            case Scheme::ShadowVar: {
                convertSchemeShadowVar(nbap, vscp, vscpInfo);
                break;
            }
            case Scheme::ShadowVarMasked: {
                convertSchemeShadowVarMasked(nbap, vscp, vscpInfo);
                break;
            }
            case Scheme::FlagShared: {
                convertSchemeFlagShared(nbap, vscp, vscpInfo);
                break;
            }
            case Scheme::FlagUnique: {
                convertSchemeFlagUnique(nbap, vscp, vscpInfo);
                break;
            }
            case Scheme::ValueQueueWhole: {
                convertSchemeValueQueue(nbap, vscp, vscpInfo, /* partial: */ false);
                break;
            }
            case Scheme::ValueQueuePartial:
                convertSchemeValueQueue(nbap, vscp, vscpInfo, /* partial: */ true);
                break;
            case Scheme::GenericQueue: {  // LCOV_EXCL_START
                UASSERT_OBJ(false, vscp, "Unreachable");
                break;
            }  // LCOV_EXCL_STOP
            }
        }
        // Complete the commits of Scheme::GenericQueue
        for (const auto& pair : m_destps) {
            if (pair.second->isGeneric()) finishSchemeGenericQueue(pair.first, *pair.second);
        }
        // For scheduling, mark the processes adding updates to them through functions, as
        // writing their orders, which their commits read
        for (const auto& pair : m_touchps) {
            FileLine* const flp = pair.first->fileline();
            AstCMethodHard* const touchp = new AstCMethodHard{
                flp, new AstVarRef{flp, pair.second->m_orderVscp, VAccess::WRITE},
                VCMethod::NBA_ORDER_TOUCH};
            touchp->dtypeSetVoid();
            pair.first->addStmtsp(touchp->makeStmt());
        }
    }
    void visit(AstScope* nodep) override {
        VL_RESTORER(m_scopep);
        m_scopep = nodep;
        iterateChildren(nodep);
    }
    void visit(AstVarScope* nodep) override {
        if (VN_IS(m_scopep->modp(), Iface)) m_ifaceVscps[nodep->varp()].push_back(nodep);
    }
    void visit(AstActive* nodep) override {
        UASSERT_OBJ(!m_activep, nodep, "Should not nest");
        VL_RESTORER(m_activep);
        VL_RESTORER(m_ignoreBlkAndNBlk);
        VL_RESTORER(m_inNonCombLogic);
        m_activep = nodep;
        const AstSenTree* const senTreep = nodep->sentreep();
        m_ignoreBlkAndNBlk = senTreep->hasStatic() || senTreep->hasInitial();
        m_inNonCombLogic = senTreep->hasClocked();
        iterateChildren(nodep);
    }
    void visit(AstNodeProcedure* nodep) override {
        VL_RESTORER(m_needsInitialTrigger);
        VL_RESTORER_CLEAR(m_nbaEventSenTreeps);
        VL_RESTORER_CLEAR(m_procCalleeps);
        const size_t firstNBAAddedIndex = m_nbas.size();
        {
            VL_RESTORER(m_inSuspendableOrFork);
            VL_RESTORER(m_procp);
            VL_RESTORER(m_ignoreBlkAndNBlk);
            VL_RESTORER(m_inNonCombLogic);
            // When we are dealing with initial block we need to
            // treat it as suspendable when we meet a NBA
            m_inSuspendableOrFork = nodep->isSuspendable() || VN_IS(nodep, Initial);
            m_procp = nodep;
            if (nodep->isSuspendable()) {
                m_ignoreBlkAndNBlk = false;
                m_inNonCombLogic = true;
            }
            iterateChildren(nodep);
        }
        auto containsClocled = [](const AstSenItem* itemp) {
            while (itemp) {
                if (itemp->edgeType().clockedStmt()) return true;
                itemp = VN_AS(itemp->nextp(), SenItem);
            }
            return false;
        };
        const bool addInitialTrigger = m_needsInitialTrigger
                                       && !(isProcedureWithSentreep<AstAlways>(nodep)
                                            || isProcedureWithSentreep<AstAlwaysObserved>(nodep)
                                            || isProcedureWithSentreep<AstAlwaysReactive>(nodep))
                                       && !containsClocled(m_activep->sentreep()->sensesp());
        if (!m_procCalleeps.empty()) {
            // Record the calls of the process, for the NBAs in the functions it calls
            const AstSenTree* const senTreep = m_activep->sentreep();
            m_processCalls.push_back(ProcessCalls{nodep,
                                                  senTreep->hasClocked() ? senTreep : nullptr,
                                                  {m_timingDomains.begin(), m_timingDomains.end()},
                                                  {m_procCalleeps.begin(), m_procCalleeps.end()}});
        }
        if (m_timingDomains.empty() && !addInitialTrigger) return;

        // There were some timing domains involved in the process. Add all of them as sensitivities
        // of all NBA targets in this process. Note this is a bit of a sledgehammer, we should only
        // need those that directly precede the NBA in control flow, but that is hard to compute,
        // so we will hammer away.

        // First gather all senItems
        AstSenItem* senItemp = nullptr;
        if (addInitialTrigger) {
            senItemp = new AstSenItem{nodep->fileline(), AstSenItem::InitialNBA{}};
            ++m_nInitialNBA;
        }

        for (const AstSenTree* const domainp : m_timingDomains) {
            if (domainp->sensesp())
                senItemp = AstNode::addNext(senItemp, domainp->sensesp()->cloneTree(true));
        }
        m_timingDomains.clear();
        // Add them to all nba targets we gathered in this process, not in the functions it calls
        for (size_t i = firstNBAAddedIndex; i < m_nbas.size(); ++i) {
            if (!m_nbas[i].cfuncp) addNbaSensitivity(m_nbas[i], senItemp);
        }
        for (AstSenTree* const senTreep : m_nbaEventSenTreeps)
            senTreep->addSensesp(senItemp->cloneTree(true));
        // Done with these
        VL_DO_DANGLING(senItemp->deleteTree(), senItemp);
    }
    void visit(AstFork* nodep) override {
        VL_RESTORER(m_inSuspendableOrFork);
        m_inSuspendableOrFork = true;
        iterateChildren(nodep);
    }
    void visit(AstCAwait* nodep) override {
        if (nodep->sentreep()) m_timingDomains.insert(nodep->sentreep());
        iterateChildren(nodep);
    }
    void visit(AstFireEvent* nodep) override {
        UASSERT_OBJ(v3Global.hasEvents(), nodep, "Inconsistent");
        FileLine* const flp = nodep->fileline();

        AstNodeExpr* const eventp = nodep->operandp()->unlinkFrBack();

        // Enqueue for clearing 'triggered' state on next eval
        AstCStmt* const cstmtp = new AstCStmt{flp};
        cstmtp->add("vlSymsp->fireEvent(");
        cstmtp->add(eventp);
        cstmtp->add(");");

        AstNode* newp = cstmtp;
        const AstVarRef* const vrefp = VN_CAST(eventp, VarRef);
        if (nodep->isDelayed() && (m_cfuncp || !vrefp)) {
            // V3Timing converts these with --timing
            nodep->v3warn(E_NOTIMING, "Nonblocking event trigger "
                                          << (m_cfuncp ? "in a non-inlined function/task"
                                                       : "of a class or interface member or "
                                                         "array element")
                                          << " requires --timing");
        } else if (nodep->isDelayed()) {
            const std::string newvarname = "_" + vrefp->varp()->shortName();
            AstVarScope* const dlyvscp
                = m_dlyTmps.make(flp, vrefp->varScopep()->scopep(), 1, newvarname);

            const auto dlyRef = [=](VAccess access) {  //
                return new AstVarRef{flp, dlyvscp, access};
            };

            AstAlwaysPost* const postp = new AstAlwaysPost{flp};
            AstIf* const ifp = new AstIf{flp, dlyRef(VAccess::READ)};
            postp->addStmtsp(ifp);

            UASSERT_OBJ(m_activep, nodep, "No active to handle FireEvent");
            AstSenTree* senTreep = m_activep->sentreep();
            AstActive* activep = nullptr;
            if (m_inSuspendableOrFork && (senTreep->hasInitial() || senTreep->hasClocked())) {
                // Suspendable code can trigger whenever it resumes, so fire when its NBAs are
                // committed (see visit(AstNodeProcedure*)), clearing the flag like
                // Scheme::FlagUnique
                senTreep = new AstSenTree{
                    flp, senTreep->hasClocked() ? senTreep->sensesp()->cloneTree(true) : nullptr};
                m_nbaEventSenTreeps.push_back(senTreep);
                m_needsInitialTrigger |= m_timingDomains.empty();
                dlyvscp->varp()->setIgnorePostWrite();
                ifp->addThensp(new AstAssign{flp, dlyRef(VAccess::WRITE),
                                             new AstConst{flp, AstConst::BitFalse{}}});
                activep = new AstActive{flp, "nba-event", senTreep};
                activep->senTreeStorep(senTreep);
            } else {
                activep = new AstActive{flp, "nba-event", senTreep};
                AstAlwaysPre* const prep = new AstAlwaysPre{flp};
                prep->addStmtsp(new AstAssign{flp, dlyRef(VAccess::WRITE),
                                              new AstConst{flp, AstConst::BitFalse{}}});
                activep->addStmtsp(prep);
            }
            ifp->addThensp(newp);
            m_activep->addNextHere(activep);
            activep->addStmtsp(postp);

            newp = new AstAssign{flp, dlyRef(VAccess::WRITE),
                                 new AstConst{flp, AstConst::BitTrue{}}};
        }
        nodep->replaceWith(newp);
        VL_DO_DANGLING(nodep->deleteTree(), nodep);
    }
    void visit(AstAssignDly* nodep) override {
        // Prevent double processing due to AstExprStmt being moved before this node
        if (nodep->user1SetOnce()) return;

        if (m_cfuncp && !v3Global.opt.timing().isSetTrue()) {
            nodep->v3warn(E_NOTIMING,
                          "Delayed assignment in a non-inlined function/task requires --timing");
            return;
        }
        // Scope of this NBA, of its function, executed in the contexts of the processes calling
        // it, or of its process
        AstScope* const scopep = m_cfuncp ? m_cfuncp->scopep() : m_scopep;
        if (!m_cfuncp) {
            UASSERT_OBJ(m_procp, nodep, "Delayed assignment not under process");
            UASSERT_OBJ(m_activep, nodep, "<= not under sensitivity block");
            UASSERT_OBJ(m_scopep, nodep, "<= not under scope");
            UASSERT_OBJ(m_inSuspendableOrFork || m_activep->hasClocked(), nodep,
                        "<= assignment in non-clocked block, should have been converted in "
                        "V3Active");
            m_needsInitialTrigger |= m_timingDomains.empty();
        }

        // Record scope of this NBA
        nodep->user2p(scopep);

        // Grab the reference to the target of the NBA, also lift ExprStmt statements on the LHS
        VL_RESTORER(m_currNbaLhsRefp);
        UASSERT_OBJ(!m_currNbaLhsRefp, nodep, "NBAs should not nest");
        nodep->lhsp()->foreach([&](AstNode* currp) {
            // cppcheck-suppress constVariablePointer
            if (AstExprStmt* const exprp = VN_CAST(currp, ExprStmt)) {
                // Move statements before the NBA
                nodep->addHereThisAsNext(exprp->stmtsp()->unlinkFrBackWithNext());
                // Replace with result
                currp->replaceWith(exprp->resultp()->unlinkFrBack());
                // Get rid of the AstExprStmt
                VL_DO_DANGLING2(pushDeletep(currp), currp, exprp);
            } else if (AstVarRef* const refp = VN_CAST(currp, VarRef)) {
                // Ignore reads (e.g.: '_[*here*] <= _')
                if (refp->access().isReadOnly()) return;
                // A RW ref on the LHS (e.g.: '_[preInc(*here*)] <= _') is asking for trouble at
                // this point. These should be lowered in an earlier pass into sequenced
                // temporaries.
                UASSERT_OBJ(!refp->access().isRW(), refp, "RW ref on LHS of NBA");
                // Multiple target variables
                // (e.g.: '{*here*, *and here*} <= _',or '*here*[*and here* = _] <= _').
                // These should be lowered in an earlier pass into sequenced statements.
                UASSERT_OBJ(!m_currNbaLhsRefp, refp, "Multiple Write refs on LHS of NBA");
                // Hold on to it
                m_currNbaLhsRefp = refp;
            }
        });
        // The destination: a member of an interface or class, if a handle selects the target, as
        // it can be of any instance, otherwise the target variable (there can only be one per NBA
        // at this point)
        const AstMemberSel* const selp = handleSelp(nodep->lhsp());
        UASSERT_OBJ(selp || m_currNbaLhsRefp, nodep, "NBA without target");
        AstVarScope* const vscp = selp ? nullptr : m_currNbaLhsRefp->varScopep();
        // In a method of an interface, its own variables are of the instance it is called on
        const bool receiver = vscp && m_cfuncp && !m_cfuncp->isStatic()
                              && VN_IS(scopep->modp(), Iface) && vscp->scopep() == scopep;
        DestInfo& dest = getDest(selp ? selp->varp() : vscp->varp());
        dest.m_handle |= selp || receiver;
        dest.m_inCFunc |= m_cfuncp != nullptr;
        dest.m_ordered |= nodep->ticketp() != nullptr;
        dest.m_queueable &= vscp && !m_cfuncp && canQueue(nodep->lhsp());
        if (vscp && !m_cfuncp) {
            // Record it on first encounter
            VarScopeInfo& vscpInfo = m_vscpInfo(vscp);
            if (!vscpInfo.m_firstNbaRefp) {
                vscpInfo.m_firstNbaRefp = m_currNbaLhsRefp;
                vscpInfo.m_fistActivep = m_activep;
                m_vscps.emplace_back(vscp);
            }
            // Note usage context
            vscpInfo.m_whole |= VN_IS(nodep->lhsp(), VarRef);
            vscpInfo.m_partial |= VN_IS(nodep->lhsp(), Sel);
            vscpInfo.m_inLoop |= m_inLoop;
            vscpInfo.m_inSuspOrFork |= m_inSuspendableOrFork;
            vscpInfo.m_ordered |= nodep->ticketp() != nullptr;
        }

        // Record the NBA for later processing
        m_nbas.emplace_back();
        NBA& nba = m_nbas.back();
        nba.nodep = nodep;
        nba.vscp = vscp;
        nba.destp = &dest;
        nba.cfuncp = m_cfuncp;
        nba.receiver = receiver;

        if (m_cfuncp) {
            // Add the sensitivities of the processes calling the function later
            m_cfuncsCache(m_cfuncp).m_destps.push_back(&dest);
        } else if (m_activep->sentreep()->hasClocked()) {
            // Sensitivity might be non-clocked, in a suspendable process, which are handled
            // elsewhere
            if (vscp) {
                const VarScopeInfo& vscpInfo = m_vscpInfo(vscp);
                if (vscpInfo.m_fistActivep != m_activep) {
                    AstVar* const varp = vscp->varp();
                    if (!varp->user1SetOnce()
                        && !varp->fileline()->warnIsOff(V3ErrorCode::MULTIDRIVEN)) {
                        varp->v3warn(MULTIDRIVEN,
                                     "Signal has multiple driving blocks with different clocking: "
                                         << varp->prettyNameQ() << '\n'
                                         << vscpInfo.m_firstNbaRefp->warnOther()
                                         << "... Location of first driving block\n"
                                         << vscpInfo.m_firstNbaRefp->warnContextSecondary()
                                         << m_currNbaLhsRefp->warnOther()
                                         << "... Location of other driving block\n"
                                         << m_currNbaLhsRefp->warnContextPrimary() << '\n');
                    }
                }
            }
            // Add this sensitivity to the variable
            addNbaSensitivity(nba, m_activep->sentreep()->sensesp());
        }

        // Record write reference
        if (vscp && !m_cfuncp) recordWriteRef(m_currNbaLhsRefp, true);

        iterateChildren(nodep);
    }
    void visit(AstVarRef* nodep) override {
        // Already checked the NBA LHS ref, ignore here
        if (nodep == m_currNbaLhsRefp) return;
        // Only care about write refs
        if (!nodep->access().isWriteOrRW()) return;
        // Record write reference
        recordWriteRef(nodep, false);
    }
    void visit(AstLoop* nodep) override {
        VL_RESTORER(m_inLoop);
        m_inLoop = true;
        iterateChildren(nodep);
    }
    void visit(AstNodeCCall* const nodep) override {
        iterateChildren(nodep);
        // We need to visit bodies of non-inlined functions
        const auto& cfuncps = m_classGraphp->getCallPossibleCFuncs(nodep);
        if (cfuncps.empty()) {
            recordCallee(nodep->funcp());
            visitCalledCFunc(nodep->funcp());
        } else {
            for (AstCFunc* const cfuncp : cfuncps) {
                recordCallee(cfuncp);
                visitCalledCFunc(cfuncp);
            }
        }
    }
    void visit(AstCFunc* const nodep) override {
        const auto& value = m_cfuncsCache(nodep);
        // Check whether it was already visited by visitCalledCFunc()
        if (value.m_state != CFuncCache::UNINITIALIZED) return;
        VL_RESTORER(m_cfuncp);
        m_cfuncp = nodep;
        iterateChildren(nodep);
    }

    // Pre/Post logic are created here and their content need no further changes, so ignore.
    void visit(AstAlwaysPre*) override {}
    void visit(AstAlwaysPost*) override {}

    //--------------------
    void visit(AstNode* nodep) override { iterateChildren(nodep); }

public:
    // CONSTRUCTORS
    explicit DelayedVisitor(AstNetlist* nodep)
        : m_classGraphp{V3ClassGraph::build(nodep)} {
        iterate(nodep);
    }
    ~DelayedVisitor() override {
        V3Stats::addStat("NBA, variables using ShadowVar scheme", m_nSchemeShadowVar);
        V3Stats::addStat("NBA, variables using ShadowVarMasked scheme", m_nSchemeShadowVarMasked);
        V3Stats::addStat("NBA, variables using FlagShared scheme", m_nSchemeFlagShared);
        V3Stats::addStat("NBA, variables using FlagUnique scheme", m_nSchemeFlagUnique);
        V3Stats::addStat("NBA, variables using ValueQueueWhole scheme", m_nSchemeValueQueuesWhole);
        V3Stats::addStat("NBA, variables using ValueQueuePartial scheme",
                         m_nSchemeValueQueuesPartial);
        V3Stats::addStat("NBA, variables using GenericQueue scheme", m_nSchemeGenericQueues);
        V3Stats::addStat("Optimizations, NBA flags shared", m_nSharedSetFlags);
        V3Stats::addStat("Procedures needing initial NBA trigger", m_nInitialNBA);
        V3Stats::addStat("Non-inlined co_awaits with SenTree", m_nonInlinedCAwaitsWithSenTree);
    }
};

//######################################################################
// Delayed class functions

void V3Delayed::delayedAll(AstNetlist* nodep) {
    UINFO(2, __FUNCTION__ << ":");
    { DelayedVisitor{nodep}; }  // Destruct before checking
    V3Global::dumpCheckGlobalTree("delayed", 0, dumpTreeEitherLevel() >= 3);
}

AstNodeExpr* V3Delayed::newTicketp(FileLine* flp) {
    return new AstCExpr{flp, "VlNBATicket::next()", 64};
}

AstVarScope* V3Delayed::nbaEventp(AstNetlist* netlistp) {
    if (!netlistp->nbaEventp()) {
        AstTopScope* const topScopep = netlistp->topScopep();
        AstBasicDType* const dtypep = new AstBasicDType{topScopep->scopep()->fileline(),
                                                        VBasicDTypeKwd::EVENT, VSigning::UNSIGNED};
        netlistp->typeTablep()->addTypesp(dtypep);
        netlistp->nbaEventp(topScopep->createTemp("__VnbaEvent", dtypep));
        netlistp->nbaEventTriggerp(topScopep->createTemp("__VnbaEventTrigger", 1));
        v3Global.setHasEvents();
    }
    return netlistp->nbaEventp();
}
