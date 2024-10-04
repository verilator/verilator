// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Add temporaries, such as for delayed nodes
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
        const AstVarRef* firstNbaRefp = nullptr;
        // Active block 'firstNbaRefp' is under
        const AstActive* fistActivep = nullptr;
        bool partial = false;  // Used on LHS of NBA under a Sel
        bool inLoop = false;  // Used on LHS of NBA in a loop
        bool inSuspOrFork = false;  // Used on LHS of NBA in suspendable process or fork
        Scheme scheme = Scheme::Undecided;  // Conversion scheme to use for this variable
        uint32_t nTmp = 0;  // Temporary number for unique names

    private:
        // Combined sensitivities of all NBAs targeting this variable
        AstSenTree* m_senTreep = nullptr;

        // Union of stuff needed for the various schemes - use accessors below!
        union {
            struct {  // Stuff needed for Scheme::ShadowVar
                AstVarScope* vscp;  // The shadow variable
            } shadowVariable;
            struct {  // Stuff needed for Scheme::FlagShared
                AstActive* activep;  // The active block for the Pre/Post logic
                AstAlwaysPost* postp;  // The post block for commiting results
                AstIf* commitIfp;  // The previous if statement for committing, for reuse
            } flagShared;
            struct {  // Stuff needed for Scheme::FlagUnique
                AstAlwaysPost* postp;  // The post block for commiting results
            } flagUnique;
            struct {  // Stuff needed for Scheme::ValueQueueWhole/Scheme::ValueQueuePartial
                AstVarScope* vscp;  // The commit queue variable
            } valueQueue;
        } m_union;

    public:
        // Accessors for the above union fields
        auto& shadowVariable() {
            UASSERT(scheme == Scheme::ShadowVar, "Inconsistent Scheme");
            return m_union.shadowVariable;
        }
        auto& flagShared() {
            UASSERT(scheme == Scheme::FlagShared, "Inconsistent Scheme");
            return m_union.flagShared;
        }
        auto& flagUnique() {
            UASSERT(scheme == Scheme::FlagUnique, "Inconsistent Scheme");
            return m_union.flagUnique;
        }
        auto& valueQueue() {
            UASSERT(scheme == Scheme::ValueQueuePartial || scheme == Scheme::ValueQueueWhole,
                    "Inconsistent Scheme");
            return m_union.valueQueue;
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

    // Data required to lower AstAssignDelay later
    struct NBA final {
        AstAssignDly* nodep = nullptr;  // The NBA this record refers to
        AstVarScope* vscp = nullptr;  // The target variable the NBA is updating
    };

    // NODE STATE
    //  AstVar::user1()         -> bool.  Set true if already issued MULTIDRIVEN warning
    //  AstVarRef::user1()      -> bool.  Set true if target of NBA
    //  AstNodeModule::user1p() -> std::unorded_map<std::string, AstVar*> temp map via m_varMap
    //  AstVarScope::user1p()   -> VarScopeInfo via m_vscpInfo
    //  AstVarScope::user2p()   -> AstVarRef*: First write reference to the Variable
    const VNUser1InUse m_user1InUse{};
    const VNUser2InUse m_user2InUse{};
    AstUser1Allocator<AstNodeModule, std::unordered_map<std::string, AstVar*>> m_varMap;
    AstUser1Allocator<AstVarScope, VarScopeInfo> m_vscpInfo;

    // STATE - across all visitors
    std::set<AstSenTree*> m_timingDomains;  // Timing resume domains

    // STATE - for current visit position (use VL_RESTORER)
    AstActive* m_activep = nullptr;  // Current activate
    const AstCFunc* m_cfuncp = nullptr;  // Current public C Function
    AstNodeProcedure* m_procp = nullptr;  // Current process
    bool m_inLoop = false;  // True in for loops
    bool m_inSuspendableOrFork = false;  // True in suspendable processes and forks
    bool m_ignoreBlkAndNBlk = false;  // Suppress delayed assignment BLKANDNBLK
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

    // Choose the NBA scheme used for the given variable.
    static Scheme chooseScheme(const AstVarScope* vscp, const VarScopeInfo& vscpInfo) {
        UASSERT_OBJ(vscpInfo.scheme == Scheme::Undecided, vscp, "NBA scheme already decided");

        const AstNodeDType* const dtypep = vscp->dtypep()->skipRefp();
        // Unpacked arrays
        if (const AstUnpackArrayDType* const uaDTypep = VN_CAST(dtypep, UnpackArrayDType)) {
            // If used in a loop, we must have a dynamic commit queue. (Also works in suspendables)
            if (vscpInfo.inLoop) {
                // Arrays with compound element types are currently not supported in loops
                AstBasicDType* const basicp = uaDTypep->basicp();
                if (!basicp
                    || !(basicp->isIntegralOrPacked()  //
                         || basicp->isDouble()  //
                         || basicp->isString())) {
                    return Scheme::UnsupportedCompoundArrayInLoop;
                }
                if (vscpInfo.partial) return Scheme::ValueQueuePartial;
                return Scheme::ValueQueueWhole;
            }
            // In a suspendable of fork, we must use the unique flag scheme, TODO: why?
            if (vscpInfo.inSuspOrFork) return Scheme::FlagUnique;
            // Otherwise use the shared flag scheme
            return Scheme::FlagShared;
        }

        // In a suspendable of fork, we must use the unique flag scheme, TODO: why?
        if (vscpInfo.inSuspOrFork) return Scheme::FlagUnique;
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
        // What remains must be an AstVarRef
        UASSERT_OBJ(VN_IS(nodep, VarRef), lhsp, "Malformed LHS in NBA");
        // Now have been converted to use the captured values
        return lhsp;
    }

    // Create a temporary variable in the given 'scopep', with the given 'name', and with 'dtypep'
    // type, with the bits selected by 'sLsbp'/'sWidthp' set to 'valuep', other bits set to zero.
    // Insert new statements before 'insertp'.
    // Returns a read reference to the temporary variable.
    AstVarRef* createWidened(FileLine* flp, AstScope* scopep, AstNodeDType* dtypep,
                             AstNodeExpr* sLsbp, AstNodeExpr* sWidthp, const std::string& name,
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
                                        sLsbp->cloneTreePure(true), sWidthp->cloneTreePure(true)};
        insertp->addHereThisAsNext(new AstAssign{flp, selp, valuep});
        // This is the expression to get the value of the temporary
        return new AstVarRef{flp, tp, VAccess::READ};
    }

    // Scheme::ShadowVar
    void prepareSchemeShadowVar(AstVarScope* vscp, VarScopeInfo& vscpInfo) {
        UASSERT_OBJ(vscpInfo.scheme == Scheme::ShadowVar, vscp, "Inconsistent NBA scheme");
        FileLine* const flp = vscp->fileline();
        AstScope* const scopep = vscp->scopep();
        // Create the shadow variable
        const std::string name = "__Vdly__" + vscp->varp()->shortName();
        AstVarScope* const shadowVscp = createTemp(flp, scopep, name, vscp->dtypep());
        vscpInfo.shadowVariable().vscp = shadowVscp;
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
        UASSERT_OBJ(vscpInfo.scheme == Scheme::ShadowVar, vscp, "Inconsistent NBA scheme");
        AstVarScope* const shadowVscp = vscpInfo.shadowVariable().vscp;

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
        UASSERT_OBJ(vscpInfo.scheme == Scheme::FlagShared, vscp, "Inconsistent NBA scheme");
        FileLine* const flp = vscp->fileline();
        AstScope* const scopep = vscp->scopep();
        // Create the AstActive for the Pre/Post logic
        AstActive* const activep = new AstActive{flp, "nba-flag-shared", vscpInfo.senTreep()};
        activep->sensesStorep(vscpInfo.senTreep());
        scopep->addBlocksp(activep);
        vscpInfo.flagShared().activep = activep;
        // Add 'Post' scheduled process to be populated later
        AstAlwaysPost* const postp = new AstAlwaysPost{flp};
        activep->addStmtsp(postp);
        vscpInfo.flagShared().postp = postp;
    }
    void convertSchemeFlagShared(AstAssignDly* nodep, AstVarScope* vscp, VarScopeInfo& vscpInfo) {
        UASSERT_OBJ(vscpInfo.scheme == Scheme::FlagShared, vscp, "Inconsistent NBA scheme");
        FileLine* const flp = vscp->fileline();
        AstScope* const scopep = vscp->scopep();

        // Base name suffix for signals constructed below
        const std::string baseName{"__" + vscp->varp()->shortName() + "__v"
                                   + std::to_string(vscpInfo.nTmp++)};

        // Unlink and capture the RHS value
        AstNodeExpr* const capturedRhsp
            = captureVal(scopep, nodep, nodep->rhsp()->unlinkFrBack(), "__VdlyVal" + baseName);

        // Unlink and capture the LHS reference
        AstNodeExpr* const capturedLhsp
            = captureLhs(scopep, nodep, nodep->lhsp()->unlinkFrBack(), baseName);

        // Is this NBA adjacent after the previously processed NBA?
        const bool consecutive = nodep == m_nextDlyp;
        m_nextDlyp = VN_CAST(nodep->nextp(), AssignDly);

        // We can reuse the flag of the previous assignment if:
        const bool reuseTheFlag =
            // Consecutive NBAs
            consecutive
            // ... that use the same scheme
            && m_vscpInfo(m_prevVscp).scheme == Scheme::FlagShared
            // ... and share the same overall update domain
            && m_vscpInfo(m_prevVscp).senTreep()->sameTree(vscpInfo.senTreep());

        if (!reuseTheFlag) {
            // Create new flag
            AstVarScope* const flagVscp = createTemp(flp, scopep, "__VdlySet" + baseName, 1);
            // Set the flag at the original NBA
            nodep->addHereThisAsNext(  //
                new AstAssign{flp, new AstVarRef{flp, flagVscp, VAccess::WRITE},
                              new AstConst{flp, AstConst::BitTrue{}}});
            // Add the 'Pre' scheduled reset for the flag
            vscpInfo.flagShared().activep->addStmtsp(
                new AstAssignPre{flp, new AstVarRef{flp, flagVscp, VAccess::WRITE},
                                 new AstConst{flp, AstConst::BitFalse{}}});
            // Add the 'Post' scheduled commit
            AstIf* const ifp = new AstIf{flp, new AstVarRef{flp, flagVscp, VAccess::READ}};
            vscpInfo.flagShared().postp->addStmtsp(ifp);
            vscpInfo.flagShared().commitIfp = ifp;
        } else {
            // Reuse the commit block of the previous assignment
            vscpInfo.flagShared().commitIfp = m_vscpInfo(m_prevVscp).flagShared().commitIfp;
            ++m_nSharedSetFlags;
        }
        // Commit the captured value to the captured destination
        vscpInfo.flagShared().commitIfp->addThensp(new AstAssign{flp, capturedLhsp, capturedRhsp});

        // Remember the variable for the next NBA
        m_prevVscp = vscp;

        // Delete original NBA
        pushDeletep(nodep->unlinkFrBack());
    }

    // Scheme::FlagUnique
    void prepareSchemeFlagUnique(AstVarScope* vscp, VarScopeInfo& vscpInfo) {
        UASSERT_OBJ(vscpInfo.scheme == Scheme::FlagUnique, vscp, "Inconsistent NBA scheme");
        FileLine* const flp = vscp->fileline();
        AstScope* const scopep = vscp->scopep();
        // Create the AstActive for the Pre/Post logic
        AstActive* const activep = new AstActive{flp, "nba-flag-unique", vscpInfo.senTreep()};
        activep->sensesStorep(vscpInfo.senTreep());
        scopep->addBlocksp(activep);
        // Add 'Post' scheduled process to be populated later
        AstAlwaysPost* const postp = new AstAlwaysPost{flp};
        activep->addStmtsp(postp);
        vscpInfo.flagUnique().postp = postp;
    }
    void convertSchemeFlagUnique(AstAssignDly* nodep, AstVarScope* vscp, VarScopeInfo& vscpInfo) {
        UASSERT_OBJ(vscpInfo.scheme == Scheme::FlagUnique, vscp, "Inconsistent NBA scheme");
        FileLine* const flp = vscp->fileline();
        AstScope* const scopep = vscp->scopep();

        // Base name suffix for signals constructed below
        const std::string baseName{"__" + vscp->varp()->shortName() + "__v"
                                   + std::to_string(vscpInfo.nTmp++)};

        // Unlink and capture the RHS value
        AstNodeExpr* const capturedRhsp
            = captureVal(scopep, nodep, nodep->rhsp()->unlinkFrBack(), "__VdlyVal" + baseName);

        // Unlink and capture the LHS reference
        AstNodeExpr* const capturedLhsp
            = captureLhs(scopep, nodep, nodep->lhsp()->unlinkFrBack(), baseName);

        // Create new flag
        AstVarScope* const flagVscp = createTemp(flp, scopep, "__VdlySet" + baseName, 1);
        // Set the flag at the original NBA
        nodep->addHereThisAsNext(  //
            new AstAssign{flp, new AstVarRef{flp, flagVscp, VAccess::WRITE},
                          new AstConst{flp, AstConst::BitTrue{}}});
        // Add the 'Post' scheduled commit
        AstIf* const ifp = new AstIf{flp, new AstVarRef{flp, flagVscp, VAccess::READ}};
        vscpInfo.flagUnique().postp->addStmtsp(ifp);
        // Immediately clear the flag
        ifp->addThensp(new AstAssign{flp, new AstVarRef{flp, flagVscp, VAccess::WRITE},
                                     new AstConst{flp, AstConst::BitFalse{}}});
        // Commit the value
        ifp->addThensp(new AstAssign{flp, capturedLhsp, capturedRhsp});

        // Delete original NBA
        pushDeletep(nodep->unlinkFrBack());
    }

    // Scheme::ValueQueuePartial/Scheme::ValueQueueWhole
    template <bool Partial>
    void prepareSchemeValueQueue(AstVarScope* vscp, VarScopeInfo& vscpInfo) {
        UASSERT_OBJ(Partial ? vscpInfo.scheme == Scheme::ValueQueuePartial
                            : vscpInfo.scheme == Scheme::ValueQueueWhole,
                    vscp, "Inconsisten<t NBA s>cheme");
        FileLine* const flp = vscp->fileline();
        AstScope* const scopep = vscp->scopep();

        // Create the commit queue variable
        auto* const cqDTypep
            = new AstNBACommitQueueDType{flp, vscp->dtypep()->skipRefp(), Partial};
        v3Global.rootp()->typeTablep()->addTypesp(cqDTypep);
        const std::string name = "__VdlyCommitQueue" + vscp->varp()->shortName();
        AstVarScope* const queueVscp = createTemp(flp, scopep, name, cqDTypep);
        queueVscp->varp()->noReset(true);
        vscpInfo.valueQueue().vscp = queueVscp;
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
        callp->addPinsp(new AstVarRef{flp, vscp, VAccess::READWRITE});
        postp->addStmtsp(callp->makeStmt());
    }
    template <bool Partial>
    void convertSchemeValueQueue(AstAssignDly* nodep, AstVarScope* vscp, VarScopeInfo& vscpInfo) {
        UASSERT_OBJ(Partial ? vscpInfo.scheme == Scheme::ValueQueuePartial
                            : vscpInfo.scheme == Scheme::ValueQueueWhole,
                    vscp, "Inconsistent NBA scheme");
        FileLine* const flp = vscp->fileline();
        AstScope* const scopep = vscp->scopep();

        // Base name suffix for signals constructed below
        const std::string baseName{"__" + vscp->varp()->shortName() + "__v"
                                   + std::to_string(vscpInfo.nTmp++)};

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
        if VL_CONSTEXPR_CXX17 (Partial) {
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
                AstConst* const sWidthp = VN_AS(lSelp->widthp(), Const);

                // Create mask value
                maskp = [&]() -> AstNodeExpr* {
                    // Constant mask we can compute here
                    if (AstConst* const cLsbp = VN_CAST(sLsbp, Const)) {
                        AstConst* const cp = new AstConst{flp, AstConst::DTyped{}, eDTypep};
                        cp->num().setMask(sWidthp->toSInt(), cLsbp->toSInt());
                        return cp;
                    }

                    // A non-constant mask we must compute at run-time.
                    AstConst* const onesp
                        = new AstConst{flp, AstConst::WidthedValue{}, sWidthp->toSInt(), 0};
                    onesp->num().setAllBits1();
                    return createWidened(flp, scopep, eDTypep, sLsbp, sWidthp,
                                         "__VdlyMask" + baseName, onesp, nodep);
                }();

                // Adjust value to element size
                valuep = [&]() -> AstNodeExpr* {
                    // Constant value with constant select we can compute here
                    if (AstConst* const cValuep = VN_CAST(valuep, Const)) {
                        if (AstConst* const cLsbp = VN_CAST(sLsbp, Const)) {
                            AstConst* const cp = new AstConst{flp, AstConst::DTyped{}, eDTypep};
                            cp->num().setAllBits0();
                            cp->num().opSelInto(cValuep->num(), cLsbp->toSInt(),
                                                sWidthp->toSInt());
                            return cp;
                        }
                    }

                    // A non-constant value we must adjust.
                    return createWidened(flp, scopep, eDTypep, sLsbp, sWidthp,  //
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
            flp, new AstVarRef{flp, vscpInfo.valueQueue().vscp, VAccess::READWRITE}, "enqueue"};
        callp->dtypeSetVoid();
        callp->addPinsp(valuep);
        if VL_CONSTEXPR_CXX17 (Partial) callp->addPinsp(maskp);
        for (AstNodeExpr* const indexp : idxps) callp->addPinsp(indexp);
        nodep->addHereThisAsNext(callp->makeStmt());

        // Delete original NBA
        pushDeletep(nodep->unlinkFrBack());
    }

    // Record and warn if a variable is assigned by both blocking and nonblocking assignments
    void checkVarUsage(AstVarRef* nodep, bool nonBlocking) {
        // Ignore references in certain contexts
        if (m_ignoreBlkAndNBlk) return;
        // Ignore if warning is disabled on this reference (used by V3Force).
        if (nodep->fileline()->warnIsOff(V3ErrorCode::BLKANDNBLK)) return;
        // Ignore if it's an array
        // TODO: we do this because it used to be the previous behaviour.
        //       Is it still required, or should we warn for arrays as well?
        //       Scheduling is no different for them...
        if (VN_IS(nodep->varScopep()->dtypep()->skipRefp(), UnpackArrayDType)) return;

        // Mark ref as blocking/non-blocking
        nodep->user1(nonBlocking);

        AstVarScope* const vscp = nodep->varScopep();

        // Pick up/set the first reference to this variable
        const AstVarRef* const firstRefp = VN_AS(vscp->user2p(), VarRef);
        if (!firstRefp) {
            vscp->user2p(nodep);
            return;
        }

        // If both blocking/non-blocking, it's OK
        if (firstRefp->user1() == static_cast<int>(nonBlocking)) return;

        // Otherwise warn that both blocking and non-blocking assignments are used
        const auto containingAssignment = [](const AstNode* nodep) -> const AstNode* {
            while (!VN_IS(nodep, NodeAssign)) nodep = nodep->backp();
            return nodep;
        };

        const AstNode* nonblockingp = nonBlocking ? nodep : firstRefp;
        if (const AstNode* np = containingAssignment(nonblockingp)) nonblockingp = np;
        const AstNode* blockingp = nonBlocking ? firstRefp : nodep;
        if (const AstNode* np = containingAssignment(blockingp)) blockingp = np;
        vscp->v3warn(BLKANDNBLK,
                     "Unsupported: Blocked and non-blocking assignments to same variable: "
                         << vscp->varp()->prettyNameQ() << '\n'
                         << vscp->warnContextPrimary() << '\n'
                         << blockingp->warnOther() << "... Location of blocking assignment\n"
                         << blockingp->warnContextSecondary() << '\n'
                         << nonblockingp->warnOther() << "... Location of nonblocking assignment\n"
                         << nonblockingp->warnContextSecondary());
    }

    // VISITORS
    void visit(AstNetlist* nodep) override {
        iterateChildren(nodep);
        // Decide which scheme to use for each variable and do the 'prepare' step
        for (AstVarScope* const vscp : m_vscps) {
            VarScopeInfo& vscpInfo = m_vscpInfo(vscp);
            vscpInfo.scheme = chooseScheme(vscp, vscpInfo);
            // Run 'prepare' step
            switch (vscpInfo.scheme) {
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
            switch (vscpInfo.scheme) {
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
                convertSchemeValueQueue</* Partial: */ false>(nbap, vscp, vscpInfo);
                break;
            }
            case Scheme::ValueQueuePartial:
                convertSchemeValueQueue</* Partial: */ true>(nbap, vscp, vscpInfo);
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
        m_activep = nodep;
        AstSenTree* const senTreep = nodep->sensesp();
        m_ignoreBlkAndNBlk = senTreep->hasStatic() || senTreep->hasInitial();
        iterateChildren(nodep);
    }
    void visit(AstNodeProcedure* nodep) override {
        const size_t firstNBAAddedIndex = m_nbas.size();
        {
            VL_RESTORER(m_inSuspendableOrFork);
            VL_RESTORER(m_procp);
            m_inSuspendableOrFork = nodep->isSuspendable();
            m_procp = nodep;
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

        // Grab the reference to the target of the NBA
        VL_RESTORER(m_currNbaLhsRefp);
        UASSERT_OBJ(!m_currNbaLhsRefp, nodep, "NBAs should not nest");
        nodep->lhsp()->foreach([&](AstVarRef* nodep) {
            // Ignore reads (e.g.: '_[*here*] <= _')
            if (nodep->access().isReadOnly()) return;
            // A RW ref on the LHS (e.g.: '_[preInc(*here*)] <= _') is asking for trouble at this
            // point. These should be lowered in an earlier pass into sequenced temporaries.
            UASSERT_OBJ(!nodep->access().isRW(), nodep, "RW ref on LHS of NBA");
            // Multiple target variables
            // (e.g.: '{*here*, *and here*} <= _',or '*here*[*and here* = _] <= _').
            // These should be lowered in an earlier pass into sequenced statements.
            UASSERT_OBJ(!m_currNbaLhsRefp, nodep, "Multiple Write refs on LHS of NBA");
            // Hold on to it
            m_currNbaLhsRefp = nodep;
        });
        // The target variable of the NBA (there can only be one per NBA at this point)
        AstVarScope* const vscp = m_currNbaLhsRefp->varScopep();
        // Record it on first encounter
        VarScopeInfo& vscpInfo = m_vscpInfo(vscp);
        if (!vscpInfo.firstNbaRefp) {
            vscpInfo.firstNbaRefp = m_currNbaLhsRefp;
            vscpInfo.fistActivep = m_activep;
            m_vscps.emplace_back(vscp);
        }
        // Note usage context
        vscpInfo.partial |= VN_IS(nodep->lhsp(), Sel);
        vscpInfo.inLoop |= m_inLoop;
        vscpInfo.inSuspOrFork |= m_inSuspendableOrFork;
        // Sensitivity might be non-clocked, in a suspendable process, which are handled elsewhere
        if (m_activep->sensesp()->hasClocked()) {
            if (vscpInfo.fistActivep != m_activep) {
                AstVar* const varp = vscp->varp();
                if (!varp->user1SetOnce()
                    && !varp->fileline()->warnIsOff(V3ErrorCode::MULTIDRIVEN)) {
                    varp->v3warn(MULTIDRIVEN,
                                 "Signal has multiple driving blocks with different clocking: "
                                     << varp->prettyNameQ() << '\n'
                                     << vscpInfo.firstNbaRefp->warnOther()
                                     << "... Location of first driving block\n"
                                     << vscpInfo.firstNbaRefp->warnContextSecondary()
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

        // Check var usage
        checkVarUsage(m_currNbaLhsRefp, true);

        iterateChildren(nodep);
    }
    void visit(AstVarRef* nodep) override {
        // Already checked the NBA LHS ref, ignore here
        if (nodep == m_currNbaLhsRefp) return;
        // Only care about write refs
        if (!nodep->access().isWriteOrRW()) return;
        // Check var usage
        checkVarUsage(nodep, false);
    }
    void visit(AstNodeReadWriteMem* nodep) override {
        VL_RESTORER(m_ignoreBlkAndNBlk);
        // $readmem/$writemem often used in mem models so we suppress BLKANDNBLK warnings
        m_ignoreBlkAndNBlk = true;
        iterateChildren(nodep);
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
    UINFO(2, __FUNCTION__ << ": " << endl);
    { DelayedVisitor{nodep}; }  // Destruct before checking
    V3Global::dumpCheckGlobalTree("delayed", 0, dumpTreeEitherLevel() >= 3);
}
