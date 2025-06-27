// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Add temporaries, such as for delayed nodes
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2025 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************
// V3Delayed's Transformations:
//
// Convert AstAssignDly into temporaries an specially scheduled blocks.
// For the Pre/Post scheduling semantics, see V3OrderGraph.
//
// There are several "Schemes" we can choose from for implementing a
// non-blocking assignment (NBA), repserented by an AstAssignDly.
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
//      __VdlySet__LHS = 0;
//  - In the original logic, replace the AstAssignDelay with:
//      __VdlySet__LHS = 1;
//      __VdlyDim0__LHS = idxa;
//      __VdlyDim1__LHS = idxb;
//      __VdlyVal__LHS = RHS;
//  - Add new "Post-scheduled" logic:
//      if (__VdlySet__LHS) a[__VdlyDim0__LHS][__VdlyDim1__LHS] = __VdlyVal__LHS;
// Multiple consecutive NBAs of compatible form can share the same  __VdlySet* flag
//
// "Unique flag" scheme. Used for all variables updated by NBAs
// in suspendable processees or forks. E.g.:
//   #1 LHS <= RHS;
// is converted to:
//  - In the original logic, replace the AstAssignDelay with:
//      __VdlySet__LHS = 1;
//      __VdlyVal__LHS = RHS;
//  - Add new "Post-scheduled" logic:
//      if (__VdlySet__LHS) {
//         __VdlySet__LHS = 0;
//         LHS = __VdlyVal__LHS;
//      }
//
// The "Value Queue Whole/Partial" schemes are used for cases where the
// target of an assignment cannot be statically determined, for example,
// with an array LHS in a loop:
//   LHS[idxa][idxb] <= RHS
// is converted to:
//  - In the original logic, replace the AstAssignDelay with:
//      __VdlyDim0__LHS = idxa;
//      __VdlyDim1__LHS = idxb;
//      __VdlyVal__LHS = RHS;
//      __VdlyCommitQueue__LHS.enqueue(__VdlyVal__LHS, __VdlyDim0__LHS, __VdlyDim1__LHS);
//  - Add new "Post-scheduled" logic:
//      __VdlyCommitQueue.commit(LHS);
//
// TODO: generic LHS scheme as discussed in #5092
//
//*************************************************************************

#include "V3PchAstNoMT.h"  // VL_MT_DISABLED_CODE_UNIT

#include "V3Delayed.h"

#include "V3AstUserAllocator.h"
#include "V3Const.h"
#include "V3Stats.h"

#include <deque>

VL_DEFINE_DEBUG_FUNCTIONS;

//######################################################################
// Convert AstAssignDlys (NBAs)

class DelayedVisitor final : public VNVisitor {
    // TYPES

    // The various NBA conversion schemes, including error cases
    enum class Scheme : uint8_t {
        Undecided = 0,
        UnsupportedCompoundArrayInLoop,
        ShadowVar,
        FlagShared,
        FlagUnique,
        ValueQueueWhole,
        ValueQueuePartial
    };

    // All info associated with a variable that is the target of an NBA
    class VarScopeInfo final {
    public:
        // First write reference encountered to the VarScope as the target on an NBA
        const AstVarRef* m_firstNbaRefp = nullptr;
        // Active block 'm_firstNbaRefp' is under
        const AstActive* m_fistActivep = nullptr;
        bool m_partial = false;  // Used on LHS of NBA under a Sel
        bool m_inLoop = false;  // Used on LHS of NBA in a loop
        bool m_inSuspOrFork = false;  // Used on LHS of NBA in suspendable process or fork
        Scheme m_scheme = Scheme::Undecided;  // Conversion scheme to use for this variable
        uint32_t m_nTmp = 0;  // Temporary number for unique names

    private:
        // Combined sensitivities of all NBAs targeting this variable
        AstSenTree* m_senTreep = nullptr;

        // Union of stuff needed for the various schemes - use accessors below!
        union {
            struct {  // Stuff needed for Scheme::ShadowVar
                AstVarScope* vscp;  // The shadow variable
            } m_shadowVariableKit;
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
        // Accessors for the above union fields
        auto& shadowVariableKit() {
            UASSERT(m_scheme == Scheme::ShadowVar, "Inconsistent Scheme");
            return m_kitUnion.m_shadowVariableKit;
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
        void addSensitivity(AstSenItem* nodep) {
            if (!m_senTreep) m_senTreep = new AstSenTree{nodep->fileline(), nullptr};
            // Add a copy of each term
            m_senTreep->addSensesp(nodep->cloneTree(true));
            // Remove duplicates
            V3Const::constifyExpensiveEdit(m_senTreep);
        }
        void addSensitivity(AstSenTree* nodep) { addSensitivity(nodep->sensesp()); }
    };

    // Data structure to keep track of all writes to
    struct WriteReference final {
        AstVarRef* refp = nullptr;  // The reference
        bool isNBA = false;  // True if an NBA write
        bool inNonComb = false;  // True if reference is known to be in non-combinational logic
        WriteReference() = default;
        WriteReference(AstVarRef* refp, bool isNBA, bool inNonComb)
            : refp{refp}
            , isNBA{isNBA}
            , inNonComb{inNonComb} {}
    };

    // Data required to lower AstAssignDelay later
    struct NBA final {
        AstAssignDly* nodep = nullptr;  // The NBA this record refers to
        AstVarScope* vscp = nullptr;  // The target variable the NBA is updating
    };

    // NODE STATE
    //  AstVar::user1()         -> bool.  Set true if already issued MULTIDRIVEN warning
    //  AstVarRef::user1()      -> bool.  Set true if target of NBA
    //  AstAssignDly::user1()   -> bool.  Set true if already visited
    //  AstNodeModule::user1p() -> std::unorded_map<std::string, AstVar*> temp map via m_varMap
    //  AstVarScope::user1p()   -> VarScopeInfo via m_vscpInfo
    //  AstVarScope::user2p()   -> AstVarRef*: First write reference to the Variable
    //  AstVarScope::user3p()   -> std::vector<WriteReference> via m_writeRefs;
    const VNUser1InUse m_user1InUse{};
    const VNUser2InUse m_user2InUse{};
    const VNUser3InUse m_user3InUse{};
    AstUser1Allocator<AstNodeModule, std::unordered_map<std::string, AstVar*>> m_varMap;
    AstUser1Allocator<AstVarScope, VarScopeInfo> m_vscpInfo;
    AstUser3Allocator<AstVarScope, std::vector<WriteReference>> m_writeRefs;

    // STATE - across all visitors
    std::set<AstSenTree*> m_timingDomains;  // Timing resume domains

    // STATE - for current visit position (use VL_RESTORER)
    AstActive* m_activep = nullptr;  // Current activate
    const AstCFunc* m_cfuncp = nullptr;  // Current public C Function
    AstNodeProcedure* m_procp = nullptr;  // Current process
    bool m_inLoop = false;  // True in for loops
    bool m_inSuspendableOrFork = false;  // True in suspendable processes and forks
    bool m_ignoreBlkAndNBlk = false;  // Suppress delayed assignment BLKANDNBLK
    bool m_inNonCombLogic = false;  // We are in non-combinational logic
    AstVarRef* m_currNbaLhsRefp = nullptr;  // Current NBA LHS variable reference

    // STATE - during NBA conversion (after visit)
    std::vector<NBA> m_nbas;  // AstAssignDly instances to lower at the end
    std::vector<AstVarScope*> m_vscps;  // Target variables on LHSs of NBAs
    AstAssignDly* m_nextDlyp = nullptr;  // The nextp of the previous AstAssignDly
    AstVarScope* m_prevVscp = nullptr;  // The target of the previous AstAssignDly

    // STATE - Statistic tracking
    VDouble0 m_nSchemeShadowVar;  // Number of variables using Scheme::ShadowVar
    VDouble0 m_nSchemeFlagShared;  // Number of variables using Scheme::FlagShared
    VDouble0 m_nSchemeFlagUnique;  // Number of variables using Scheme::FlagUnique
    VDouble0 m_nSchemeValueQueuesWhole;  //  Number of variables using Scheme::ValueQueueWhole
    VDouble0 m_nSchemeValueQueuesPartial;  //  Number of variables using Scheme::ValueQueuePartial
    VDouble0 m_nSharedSetFlags;  // "Set" flags actually shared by Scheme::FlagShared variables

    // METHODS

    // Return true iff a variable is assigned by both blocking and nonblocking
    // assignments. Issue BLKANDNBLK error if we can't prove the mixed
    // assignments are to independent bits and the blocking assignment can be
    // in combinational logic, which is something we can't safely implement
    // still.
    bool checkMixedUsage(const AstVarScope* vscp, bool isPacked) {

        struct Ref final {
            AstVarRef* refp;  // The reference
            bool inNonComb;  // True if known to be in non-combinational logic
            int lsb;  // LSB of accessed range
            int msb;  // MSB of accessed range
            Ref(AstVarRef* refp, bool inNonComb, int lsb, int msb)
                : refp{refp}
                , inNonComb{inNonComb}
                , lsb{lsb}
                , msb{msb} {}
        };

        std::vector<Ref> blkRefs;  // Blocking writes
        std::vector<Ref> nbaRefs;  // Non-blockign writes

        const int width = isPacked ? vscp->width() : 1;

        for (const auto& writeRef : m_writeRefs(vscp)) {
            int lsb = 0;
            int msb = width - 1;
            if (AstSel* const selp = VN_CAST(writeRef.refp->backp(), Sel)) {
                if (VN_IS(selp->lsbp(), Const)) {
                    lsb = selp->lsbConst();
                    msb = selp->msbConst();
                }
            }
            if (writeRef.isNBA) {
                nbaRefs.emplace_back(writeRef.refp, writeRef.inNonComb, lsb, msb);
            } else {
                blkRefs.emplace_back(writeRef.refp, writeRef.inNonComb, lsb, msb);
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
                                     [](const Ref& ref) { return ref.inNonComb; }),
                      blkRefs.end());

        // If nothing left, then we need not error
        if (blkRefs.empty()) return true;

        // If not a packed variable, warn here as we can't prove independence
        if (!isPacked) {
            const Ref& blkRef = blkRefs.front();
            const Ref& nbaRef = nbaRefs.front();
            vscp->v3warn(
                BLKANDNBLK,
                "Unsupported: Blocking and non-blocking assignments to same non-packed variable: "
                    << vscp->varp()->prettyNameQ() << '\n'
                    << vscp->warnContextPrimary() << '\n'
                    << blkRef.refp->warnOther() << "... Location of blocking assignment\n"
                    << blkRef.refp->warnContextSecondary() << '\n'
                    << nbaRef.refp->warnOther() << "... Location of nonblocking assignment\n"
                    << nbaRef.refp->warnContextSecondary());
            return true;
        }

        // We need to error if we can't prove the written bits are independent

        // Sort refs by interval
        const auto lessThanRef = [](const Ref& a, const Ref& b) {
            if (a.lsb != b.lsb) return a.lsb < b.lsb;
            return a.msb < b.msb;
        };
        std::stable_sort(blkRefs.begin(), blkRefs.end(), lessThanRef);
        std::stable_sort(nbaRefs.begin(), nbaRefs.end(), lessThanRef);
        // Iterate both vectors, checking for overlap
        auto bIt = blkRefs.begin();
        auto nIt = nbaRefs.begin();
        while (bIt != blkRefs.end() && nIt != nbaRefs.end()) {
            if (lessThanRef(*bIt, *nIt)) {
                if (nIt->lsb <= bIt->msb) break;  // Stop on Overlap
                ++bIt;
            } else {
                if (bIt->lsb <= nIt->msb) break;  // Stop on Overlap
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
                                         << blkRef.refp->warnOther()
                                         << "... Location of blocking assignment"
                                         << " (bits [" << blkRef.msb << ":" << blkRef.lsb << "])\n"
                                         << blkRef.refp->warnContextSecondary() << '\n'
                                         << nbaRef.refp->warnOther()
                                         << "... Location of nonblocking assignment"
                                         << " (bits [" << nbaRef.msb << ":" << nbaRef.lsb << "])\n"
                                         << nbaRef.refp->warnContextSecondary());
        }

        return true;
    }

    // Choose the NBA scheme used for the given variable.
    Scheme chooseScheme(const AstVarScope* vscp, const VarScopeInfo& vscpInfo) {
        UASSERT_OBJ(vscpInfo.m_scheme == Scheme::Undecided, vscp, "NBA scheme already decided");

        const AstNodeDType* const dtypep = vscp->dtypep()->skipRefp();
        // Unpacked arrays
        if (const AstUnpackArrayDType* const uaDTypep = VN_CAST(dtypep, UnpackArrayDType)) {
            // Basic underlying type of elements, if any.
            AstBasicDType* const basicp = uaDTypep->basicp();
            // If used in a loop, we must have a dynamic commit queue. (Also works in suspendables)
            if (vscpInfo.m_inLoop) {
                // Arrays with compound element types are currently not supported in loops
                if (!basicp
                    || !(basicp->isIntegralOrPacked()  //
                         || basicp->isDouble()  //
                         || basicp->isString())) {
                    return Scheme::UnsupportedCompoundArrayInLoop;
                }
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

        // Check for mixed usage (this also warns if not OK)
        const bool usedMixed = checkMixedUsage(vscp, dtypep->isIntegralOrPacked());
        // If it's a variable updated by both blocking and non-blocking
        // asignments, use the FlagUnique scheme. This can handle blocking
        // and non-blocking updates to inpdendent parts correctly at run-time.
        if (usedMixed) return Scheme::FlagUnique;

        // Otherwise use the simple shadow variable scheme
        return Scheme::ShadowVar;
    }

    // Create new AstVarScope in the given 'scopep', with the given 'name' and 'dtypep'
    AstVarScope* createTemp(FileLine* flp, AstScope* scopep, const std::string& name,
                            AstNodeDType* dtypep) {
        AstNodeModule* const modp = scopep->modp();
        // Get/create the corresponding AstVar
        AstVar*& varp = m_varMap(modp)[name];
        if (!varp) {
            varp = new AstVar{flp, VVarType::BLOCKTEMP, name, dtypep};
            modp->addStmtsp(varp);
        }
        // Create the AstVarScope
        AstVarScope* const varscp = new AstVarScope{flp, scopep, varp};
        scopep->addVarsp(varscp);
        return varscp;
    }

    // Same as above but create a 2-state scalar of the given 'width'
    AstVarScope* createTemp(FileLine* flp, AstScope* scopep, const std::string& name, int width) {
        AstNodeDType* const dtypep = scopep->findBitDType(width, width, VSigning::UNSIGNED);
        return createTemp(flp, scopep, name, dtypep);
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
        AstVarScope* const tmpVscp = createTemp(flp, scopep, name, exprp->dtypep());
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
            const std::string tmpName{"__VdlyLsb" + baseName};
            selp->lsbp(captureVal(scopep, insertp, selp->lsbp()->unlinkFrBack(), tmpName));
            // Continue with target
            nodep = selp->fromp();
        }
        UASSERT_OBJ(!VN_IS(nodep, Sel), lhsp, "Multiple 'AstSel' applied to LHS reference");
        // Capture AstArraySel indices - might be many
        size_t nArraySels = 0;
        while (AstArraySel* const arrSelp = VN_CAST(nodep, ArraySel)) {
            const std::string tmpName{"__VdlyDim" + std::to_string(nArraySels++) + baseName};
            arrSelp->bitp(captureVal(scopep, insertp, arrSelp->bitp()->unlinkFrBack(), tmpName));
            nodep = arrSelp->fromp();
        }
        // What remains must be an AstVarRef, or some sort of select, we assume can reuse it.
        if (AstAssocSel* const aselp = VN_CAST(nodep, AssocSel)) {
            UASSERT_OBJ(aselp->fromp()->isPure() && aselp->bitp()->isPure(), lhsp,
                        "Malformed LHS in NBA");
        } else {
            UASSERT_OBJ(nodep->isPure(), lhsp, "Malformed LHS in NBA");
        }
        // Now have been converted to use the captured values
        return lhsp;
    }

    // Create a temporary variable in the given 'scopep', with the given 'name', and with 'dtypep'
    // type, with the bits selected by 'sLsbp'/'sWidthp' set to 'valuep', other bits set to zero.
    // Insert new statements before 'insertp'.
    // Returns a read reference to the temporary variable.
    AstVarRef* createWidened(FileLine* flp, AstScope* scopep, AstNodeDType* dtypep,
                             AstNodeExpr* sLsbp, int sWidth, const std::string& name,
                             AstNodeExpr* valuep, AstNode* insertp) {
        // Create temporary variable.
        AstVarScope* const tp = createTemp(flp, scopep, name, dtypep);
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
        const std::string name = "__Vdly__" + vscp->varp()->shortName();
        AstVarScope* const shadowVscp = createTemp(flp, scopep, name, vscp->dtypep());
        vscpInfo.shadowVariableKit().vscp = shadowVscp;
        // Create the AstActive for the Pre/Post logic
        AstActive* const activep = new AstActive{flp, "nba-shadow-variable", vscpInfo.senTreep()};
        activep->sensesStorep(vscpInfo.senTreep());
        scopep->addBlocksp(activep);
        // Add 'Pre' scheduled 'shadowVariable = originalVariable' assignment
        activep->addStmtsp(new AstAssignPre{flp, new AstVarRef{flp, shadowVscp, VAccess::WRITE},
                                            new AstVarRef{flp, vscp, VAccess::READ}});
        // Add 'Post' scheduled 'originalVariable = shadowVariable' assignment
        activep->addStmtsp(new AstAssignPost{flp, new AstVarRef{flp, vscp, VAccess::WRITE},
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

    // Scheme::FlagShared
    void prepareSchemeFlagShared(AstVarScope* vscp, VarScopeInfo& vscpInfo) {
        UASSERT_OBJ(vscpInfo.m_scheme == Scheme::FlagShared, vscp, "Inconsistent NBA scheme");
        FileLine* const flp = vscp->fileline();
        AstScope* const scopep = vscp->scopep();
        // Create the AstActive for the Pre/Post logic
        AstActive* const activep = new AstActive{flp, "nba-flag-shared", vscpInfo.senTreep()};
        activep->sensesStorep(vscpInfo.senTreep());
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
        AstScope* const scopep = vscp->scopep();

        // Base name suffix for signals constructed below
        const std::string baseName{"__" + vscp->varp()->shortName() + "__v"
                                   + std::to_string(vscpInfo.m_nTmp++)};

        // Unlink and capture the RHS value
        AstNodeExpr* const capturedRhsp
            = captureVal(scopep, nodep, nodep->rhsp()->unlinkFrBack(), "__VdlyVal" + baseName);

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
            // ... and share the same overall update domain
            && prevVscpInfop->senTreep()->sameTree(vscpInfo.senTreep());

        if (!reuseTheFlag) {
            // Create new flag
            AstVarScope* const flagVscp = createTemp(flp, scopep, "__VdlySet" + baseName, 1);
            // Set the flag at the original NBA
            nodep->addHereThisAsNext(  //
                new AstAssign{flp, new AstVarRef{flp, flagVscp, VAccess::WRITE},
                              new AstConst{flp, AstConst::BitTrue{}}});
            // Add the 'Pre' scheduled reset for the flag
            vscpInfo.flagSharedKit().activep->addStmtsp(
                new AstAssignPre{flp, new AstVarRef{flp, flagVscp, VAccess::WRITE},
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
        pushDeletep(nodep->unlinkFrBack());
    }

    // Scheme::FlagUnique
    void prepareSchemeFlagUnique(AstVarScope* vscp, VarScopeInfo& vscpInfo) {
        UASSERT_OBJ(vscpInfo.m_scheme == Scheme::FlagUnique, vscp, "Inconsistent NBA scheme");
        FileLine* const flp = vscp->fileline();
        AstScope* const scopep = vscp->scopep();
        // Create the AstActive for the Pre/Post logic
        AstActive* const activep = new AstActive{flp, "nba-flag-unique", vscpInfo.senTreep()};
        activep->sensesStorep(vscpInfo.senTreep());
        scopep->addBlocksp(activep);
        // Add 'Post' scheduled process to be populated later
        AstAlwaysPost* const postp = new AstAlwaysPost{flp};
        activep->addStmtsp(postp);
        vscpInfo.flagUniqueKit().postp = postp;
    }
    void convertSchemeFlagUnique(AstAssignDly* nodep, AstVarScope* vscp, VarScopeInfo& vscpInfo) {
        UASSERT_OBJ(vscpInfo.m_scheme == Scheme::FlagUnique, vscp, "Inconsistent NBA scheme");
        FileLine* const flp = vscp->fileline();
        AstScope* const scopep = vscp->scopep();

        // Base name suffix for signals constructed below
        const std::string baseName{"__" + vscp->varp()->shortName() + "__v"
                                   + std::to_string(vscpInfo.m_nTmp++)};

        // Unlink and capture the RHS value
        AstNodeExpr* const capturedRhsp
            = captureVal(scopep, nodep, nodep->rhsp()->unlinkFrBack(), "__VdlyVal" + baseName);

        // Unlink and capture the LHS reference
        AstNodeExpr* const capturedLhsp
            = captureLhs(scopep, nodep, nodep->lhsp()->unlinkFrBack(), baseName);

        // Create new flag
        AstVarScope* const flagVscp = createTemp(flp, scopep, "__VdlySet" + baseName, 1);
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
        pushDeletep(nodep->unlinkFrBack());
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
        auto* const cqDTypep
            = new AstNBACommitQueueDType{flp, vscp->dtypep()->skipRefp(), N_Partial};
        v3Global.rootp()->typeTablep()->addTypesp(cqDTypep);
        const std::string name = "__VdlyCommitQueue" + vscp->varp()->shortName();
        AstVarScope* const queueVscp = createTemp(flp, scopep, name, cqDTypep);
        queueVscp->varp()->noReset(true);
        queueVscp->varp()->setIgnorePostWrite();
        vscpInfo.valueQueueKit().vscp = queueVscp;
        // Create the AstActive for the Post logic
        AstActive* const activep
            = new AstActive{flp, "nba-value-queue-whole", vscpInfo.senTreep()};
        activep->sensesStorep(vscpInfo.senTreep());
        scopep->addBlocksp(activep);
        // Add 'Post' scheduled process for the commit
        AstAlwaysPost* const postp = new AstAlwaysPost{flp};
        activep->addStmtsp(postp);
        // Add the commit
        AstCMethodHard* const callp
            = new AstCMethodHard{flp, new AstVarRef{flp, queueVscp, VAccess::READWRITE}, "commit"};
        callp->dtypeSetVoid();
        callp->addPinsp(new AstVarRef{flp, vscp, VAccess::WRITE});
        postp->addStmtsp(callp->makeStmt());
    }

    void convertSchemeValueQueue(AstAssignDly* nodep, AstVarScope* vscp, VarScopeInfo& vscpInfo,
                                 bool partial) {
        UASSERT_OBJ(partial ? vscpInfo.m_scheme == Scheme::ValueQueuePartial
                            : vscpInfo.m_scheme == Scheme::ValueQueueWhole,
                    vscp, "Inconsistent NBA scheme");
        FileLine* const flp = vscp->fileline();
        AstScope* const scopep = vscp->scopep();

        // Base name suffix for signals constructed below
        const std::string baseName{"__" + vscp->varp()->shortName() + "__v"
                                   + std::to_string(vscpInfo.m_nTmp++)};

        // Unlink and capture the RHS value
        AstNodeExpr* const capturedRhsp
            = captureVal(scopep, nodep, nodep->rhsp()->unlinkFrBack(), "__VdlyVal" + baseName);

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

            if (AstSel* const lSelp = VN_CAST(lhsNodep, Sel)) {
                // This is a partial assignment.
                // Need to create a mask and widen the value to element size.
                lhsNodep = lSelp->fromp();
                AstNodeExpr* const sLsbp = lSelp->lsbp();
                const int sWidth = lSelp->widthConst();

                // Create mask value
                maskp = [&]() -> AstNodeExpr* {
                    // Constant mask we can compute here
                    if (AstConst* const cLsbp = VN_CAST(sLsbp, Const)) {
                        AstConst* const cp = new AstConst{flp, AstConst::DTyped{}, eDTypep};
                        cp->num().setMask(sWidth, cLsbp->toSInt());
                        return cp;
                    }

                    // A non-constant mask we must compute at run-time.
                    AstConst* const onesp = new AstConst{flp, AstConst::WidthedValue{}, sWidth, 0};
                    onesp->num().setAllBits1();
                    return createWidened(flp, scopep, eDTypep, sLsbp, sWidth,
                                         "__VdlyMask" + baseName, onesp, nodep);
                }();

                // Adjust value to element size
                valuep = [&]() -> AstNodeExpr* {
                    // Constant value with constant select we can compute here
                    if (AstConst* const cValuep = VN_CAST(valuep, Const)) {
                        if (AstConst* const cLsbp = VN_CAST(sLsbp, Const)) {
                            AstConst* const cp = new AstConst{flp, AstConst::DTyped{}, eDTypep};
                            cp->num().setAllBits0();
                            cp->num().opSelInto(cValuep->num(), cLsbp->toSInt(), sWidth);
                            return cp;
                        }
                    }

                    // A non-constant value we must adjust.
                    return createWidened(flp, scopep, eDTypep, sLsbp, sWidth,  //
                                         "__VdlyElem" + baseName, valuep, nodep);
                }();
            } else {
                // If this assignment is not partial, set mask to ones and we are done
                AstConst* const ones = new AstConst{flp, AstConst::DTyped{}, eDTypep};
                ones->num().setAllBits1();
                maskp = ones;
            }
        }

        // Extract array indices
        std::vector<AstNodeExpr*> idxps;
        {
            UASSERT_OBJ(VN_IS(lhsNodep, ArraySel), lhsNodep, "Unexpected LHS form");
            while (AstArraySel* const aSelp = VN_CAST(lhsNodep, ArraySel)) {
                idxps.emplace_back(aSelp->bitp()->unlinkFrBack());
                lhsNodep = aSelp->fromp();
            }
            UASSERT_OBJ(VN_IS(lhsNodep, VarRef), lhsNodep, "Unexpected LHS form");
            std::reverse(idxps.begin(), idxps.end());
        }

        // Done with the LHS at this point
        VL_DO_DANGLING(pushDeletep(capturedLhsp), capturedLhsp);

        // Enqueue the update at the site of the original NBA
        AstCMethodHard* const callp = new AstCMethodHard{
            flp, new AstVarRef{flp, vscpInfo.valueQueueKit().vscp, VAccess::READWRITE}, "enqueue"};
        callp->dtypeSetVoid();
        callp->addPinsp(valuep);
        if (partial) callp->addPinsp(maskp);
        for (AstNodeExpr* const indexp : idxps) callp->addPinsp(indexp);
        nodep->addHereThisAsNext(callp->makeStmt());

        // Delete original NBA
        pushDeletep(nodep->unlinkFrBack());
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

    // VISITORS
    void visit(AstNetlist* nodep) override {
        iterateChildren(nodep);
        // Decide which scheme to use for each variable and do the 'prepare' step
        for (AstVarScope* const vscp : m_vscps) {
            VarScopeInfo& vscpInfo = m_vscpInfo(vscp);
            vscpInfo.m_scheme = chooseScheme(vscp, vscpInfo);
            // Run 'prepare' step
            switch (vscpInfo.m_scheme) {
            case Scheme::Undecided:  // LCOV_EXCL_START
                UASSERT_OBJ(false, vscp, "Failed to choose NBA scheme");
                break;
            case Scheme::UnsupportedCompoundArrayInLoop: {
                // Will report error at the site of the NBA
                break;
            }
            case Scheme::ShadowVar: {
                ++m_nSchemeShadowVar;
                prepareSchemeShadowVar(vscp, vscpInfo);
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
            }
        }
        // Convert all NBAs
        for (const NBA& nba : m_nbas) {
            AstAssignDly* const nbap = nba.nodep;
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
            }
        }
    }
    void visit(AstScope* nodep) override { iterateChildren(nodep); }
    void visit(AstCFunc* nodep) override {
        VL_RESTORER(m_cfuncp);
        m_cfuncp = nodep;
        iterateChildren(nodep);
    }
    void visit(AstActive* nodep) override {
        UASSERT_OBJ(!m_activep, nodep, "Should not nest");
        VL_RESTORER(m_activep);
        VL_RESTORER(m_ignoreBlkAndNBlk);
        VL_RESTORER(m_inNonCombLogic);
        m_activep = nodep;
        AstSenTree* const senTreep = nodep->sensesp();
        m_ignoreBlkAndNBlk = senTreep->hasStatic() || senTreep->hasInitial();
        m_inNonCombLogic = senTreep->hasClocked();
        iterateChildren(nodep);
    }
    void visit(AstNodeProcedure* nodep) override {
        const size_t firstNBAAddedIndex = m_nbas.size();
        {
            VL_RESTORER(m_inSuspendableOrFork);
            VL_RESTORER(m_procp);
            VL_RESTORER(m_ignoreBlkAndNBlk);
            VL_RESTORER(m_inNonCombLogic);
            m_inSuspendableOrFork = nodep->isSuspendable();
            m_procp = nodep;
            if (m_inSuspendableOrFork) {
                m_ignoreBlkAndNBlk = false;
                m_inNonCombLogic = true;
            }
            iterateChildren(nodep);
        }
        if (m_timingDomains.empty()) return;

        // There were some timing domains involved in the process. Add all of them as sensitivities
        // of all NBA targets in this process. Note this is a bit of a sledgehammer, we should only
        // need those that directly preceed the NBA in control flow, but that is hard to compute,
        // so we will hammer away.

        // First gather all senItems
        AstSenItem* senItemp = nullptr;
        for (AstSenTree* const domainp : m_timingDomains) {
            senItemp = AstNode::addNext(senItemp, domainp->sensesp()->cloneTree(true));
        }
        m_timingDomains.clear();
        // Add them to all nba targets we gathered in this process
        for (size_t i = firstNBAAddedIndex; i < m_nbas.size(); ++i) {
            m_vscpInfo(m_nbas[i].vscp).addSensitivity(senItemp);
        }
        // Done with these
        VL_DO_DANGLING(senItemp->deleteTree(), senItemp);
    }
    void visit(AstFork* nodep) override {
        VL_RESTORER(m_inSuspendableOrFork);
        m_inSuspendableOrFork = true;
        iterateChildren(nodep);
    }
    void visit(AstCAwait* nodep) override {
        if (nodep->sensesp()) m_timingDomains.insert(nodep->sensesp());
    }
    void visit(AstFireEvent* nodep) override {
        UASSERT_OBJ(v3Global.hasEvents(), nodep, "Inconsistent");
        FileLine* const flp = nodep->fileline();

        AstNodeExpr* const eventp = nodep->operandp()->unlinkFrBack();

        // Enqueue for clearing 'triggered' state on next eval
        AstTextBlock* const blockp = new AstTextBlock{flp};
        blockp->addText(flp, "vlSymsp->fireEvent(", true);
        blockp->addNodesp(eventp);
        blockp->addText(flp, ");\n", true);

        AstNode* newp = new AstCStmt{flp, blockp};
        if (nodep->isDelayed()) {
            AstVarRef* const vrefp = VN_AS(eventp, VarRef);
            const std::string newvarname = "__Vdly__" + vrefp->varp()->shortName();
            AstVarScope* const dlyvscp
                = createTemp(flp, vrefp->varScopep()->scopep(), newvarname, 1);

            const auto dlyRef = [=](VAccess access) {  //
                return new AstVarRef{flp, dlyvscp, access};
            };

            AstAssignPre* const prep = new AstAssignPre{flp, dlyRef(VAccess::WRITE),
                                                        new AstConst{flp, AstConst::BitFalse{}}};
            AstAlwaysPost* const postp = new AstAlwaysPost{flp};
            {
                AstIf* const ifp = new AstIf{flp, dlyRef(VAccess::READ)};
                postp->addStmtsp(ifp);
                ifp->addThensp(newp);
            }

            UASSERT_OBJ(m_activep, nodep, "No active to handle FireEvent");
            AstActive* const activep = new AstActive{flp, "nba-event", m_activep->sensesp()};
            m_activep->addNextHere(activep);
            activep->addStmtsp(prep);
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

        if (m_cfuncp) {
            if (!v3Global.rootp()->nbaEventp()) {
                nodep->v3warn(
                    E_NOTIMING,
                    "Delayed assignment in a non-inlined function/task requires --timing");
            }
            return;
        }
        UASSERT_OBJ(m_procp, nodep, "Delayed assignment not under process");
        UASSERT_OBJ(m_activep, nodep, "<= not under sensitivity block");
        UASSERT_OBJ(m_inSuspendableOrFork || m_activep->hasClocked(), nodep,
                    "<= assignment in non-clocked block, should have been converted in V3Active");

        // Grab the reference to the target of the NBA, also lift ExprStmt statements on the LHS
        VL_RESTORER(m_currNbaLhsRefp);
        UASSERT_OBJ(!m_currNbaLhsRefp, nodep, "NBAs should not nest");
        nodep->lhsp()->foreach([&](AstNode* currp) {
            if (AstExprStmt* const exprp = VN_CAST(currp, ExprStmt)) {
                // Move statements before the NBA
                nodep->addHereThisAsNext(exprp->stmtsp()->unlinkFrBackWithNext());
                // Replace with result
                currp->replaceWith(exprp->resultp()->unlinkFrBack());
                // Get rid of the AstExprStmt
                VL_DO_DANGLING(pushDeletep(currp), currp);
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
        // The target variable of the NBA (there can only be one per NBA at this point)
        AstVarScope* const vscp = m_currNbaLhsRefp->varScopep();
        // Record it on first encounter
        VarScopeInfo& vscpInfo = m_vscpInfo(vscp);
        if (!vscpInfo.m_firstNbaRefp) {
            vscpInfo.m_firstNbaRefp = m_currNbaLhsRefp;
            vscpInfo.m_fistActivep = m_activep;
            m_vscps.emplace_back(vscp);
        }
        // Note usage context
        vscpInfo.m_partial |= VN_IS(nodep->lhsp(), Sel);
        vscpInfo.m_inLoop |= m_inLoop;
        vscpInfo.m_inSuspOrFork |= m_inSuspendableOrFork;
        // Sensitivity might be non-clocked, in a suspendable process, which are handled elsewhere
        if (m_activep->sensesp()->hasClocked()) {
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
            // Add this sensitivity to the variable
            vscpInfo.addSensitivity(m_activep->sensesp());
        }

        // Record the NBA for later processing
        m_nbas.emplace_back();
        NBA& nba = m_nbas.back();
        nba.nodep = nodep;
        nba.vscp = vscp;

        // Record write reference
        recordWriteRef(m_currNbaLhsRefp, true);

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
    void visit(AstNodeFor* nodep) override {  // LCOV_EXCL_LINE
        nodep->v3fatalSrc("For statements should have been converted to while statements");
    }
    void visit(AstWhile* nodep) override {
        VL_RESTORER(m_inLoop);
        m_inLoop = true;
        iterateChildren(nodep);
    }

    // Pre/Post logic are created here and their content need no further changes, so ignore.
    void visit(AstAssignPre*) override {}
    void visit(AstAssignPost*) override {}
    void visit(AstAlwaysPost*) override {}

    //--------------------
    void visit(AstNode* nodep) override { iterateChildren(nodep); }

public:
    // CONSTRUCTORS
    explicit DelayedVisitor(AstNetlist* nodep) { iterate(nodep); }
    ~DelayedVisitor() override {
        V3Stats::addStat("NBA, variables using ShadowVar scheme", m_nSchemeShadowVar);
        V3Stats::addStat("NBA, variables using FlagShared scheme", m_nSchemeFlagShared);
        V3Stats::addStat("NBA, variables using FlagUnique scheme", m_nSchemeFlagUnique);
        V3Stats::addStat("NBA, variables using ValueQueueWhole scheme", m_nSchemeValueQueuesWhole);
        V3Stats::addStat("NBA, variables using ValueQueuePartial scheme",
                         m_nSchemeValueQueuesPartial);
        V3Stats::addStat("Optimizations, NBA flags shared", m_nSharedSetFlags);
    }
};

//######################################################################
// Delayed class functions

void V3Delayed::delayedAll(AstNetlist* nodep) {
    UINFO(2, __FUNCTION__ << ":");
    { DelayedVisitor{nodep}; }  // Destruct before checking
    V3Global::dumpCheckGlobalTree("delayed", 0, dumpTreeEitherLevel() >= 3);
}
