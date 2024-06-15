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
// A non-array LHS, outside suspendable processes and forks, e.g.::
//   a <= RHS;
// is converted as follows:
//  - Add new "Pre-scheduled" logic:
//      __Vdly__a = a;
//  - In the original logic, replace VarRefs on LHS with __Vdly__ variables:
//      __Vdly__a = RHS;
//  - Add new "Post-scheduled" logic:
//      a = __Vdly__a;
//
// An array LHS, that is not inside a loop:
//   a[idxa][idxb] <= RHS
// is converted:
//  - Add new "Pre_scheduled" logic:
//      __VdlySet__a = 0;
//  - In the original logic, replace the AstAssignDelay with:
//      __VdlySet__a = 1;
//      __VdlyDim0__a = idxa;
//      __VdlyDim1__a = idxb;
//      __VdlyVal__a = RHS;
//  - Add new "Post-scheduled" logic:
//      if (__VdlySet__a) a[__VdlyDim0__a][__VdlyDim1__a] = __VdlyVal__a;
//
// Any AstAssignDly in a suspendable process or fork also uses the
// '__VdlySet' flag based scheme, like arrays,  with some modifications.
//
// An array LHS, which is updated inside a loop (that is, we don't know
// statically how many updates there might be):
//   a[idxa][idxb] <= RHS
// is converted to:
//  - In the original logic, replace the AstAssignDelay with:
//      __VdlyDim0__a = idxa;
//      __VdlyDim1__a = idxb;
//      __VdlyVal__a = RHS;
//      __VdlyCommitQueue.enqueue(RHS, idxa, idxb);
//  - Add new "Post-scheduled" logic:
//      __VdlyCommitQueue.commit(array-on-LHS);
//
// Note that it is necessary to use the same commit queue for all NBAs
// targeting the same array, if any NBAs require a commit queue. Hence
// we can only decide whether to use a commit queue or not after having
// examined all NBAs.
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
// Delayed state, as a visitor of each AstNode

class DelayedVisitor final : public VNVisitor {
    // TYPES

    // Components of an AstAssignDly LHS expression, e.g.:
    //   Sel(ArraySel(ArraySel(_: VarRef, _: Index), _: Index), _: Lsb, _: Width))
    struct LhsComponents final {
        AstVarRef* refp = nullptr;  // The referenced variable
        std::vector<AstNodeExpr*> arrIdxps;  // The array indices applied to 'refp'
        AstNodeExpr* selLsbp = nullptr;  // The bit select LSB expression, after the array selects
        AstConst* selWidthp = nullptr;  // The width of the bit select
    };

    // Data required to lower AstAssignDelay later
    struct Deferred final {
        LhsComponents lhsComponents;  // The components of the LHS
        AstNodeExpr* rhsp = nullptr;  // The captured value being assigned by the AstAssignDly
        AstActive* activep = nullptr;  // The active block the AstAssignDly is under
        AstNode* insertionPointp = nullptr;  // The insertion point after the AstAssignDly
        std::string suffix;  // Suffix to add to additional variables created
        bool consecutive = false;  // Record corresponds to an AstAssignDly immediately adjacent
    };

    // NODE STATE
    //  AstVarScope::user1p()   -> aux
    //  AstVar::user1()         -> bool.  Set true if already made warning
    //  AstVarRef::user1()      -> bool.  Set true if is a non-blocking reference
    //  AstAlwaysPost::user1()  -> AstIf*.  Last IF (__VdlySet__) created under this AlwaysPost
    //
    // Cleared each scope/active:
    //  AstVarScope::user2()      -> AstVarScope*.  Commit queue for this variable
    //  AstVarRef::user2()        -> bool.  Set true if already processed
    //  AstAssignDly::user2()     -> AstVarScope*.  __VdlySet__ created for this assign
    //  AstAlwaysPost::user2()    -> AstVarScope*.  __VdlySet__ last referenced in IF
    //  AstNodeProcedure::user2() -> AstAcive*.  Active block used by this suspendable process
    const VNUser1InUse m_inuser1;
    const VNUser2InUse m_inuser2;

    struct AuxAstVarScope final {
        // Points to temp (shadow) variable created.
        AstVarScope* delayVscp = nullptr;
        // Points to AstActive block of the shadow variable 'delayVscp/post block 'postp'
        AstActive* activep = nullptr;
        // Post block for this variable used in suspendable processes
        AstAlwaysPost* suspPostp = nullptr;
        // Post block for this variable
        AstAlwaysPost* postp = nullptr;
        // First reference encountered to the VarScope
        const AstNodeVarRef* firstRefp = nullptr;
        // If the implementation cannot be deferred, this is the location why
        FileLine* nonDeferredFlp = nullptr;
        // Variable requires a commit queue due to dynamic NBA
        bool needsCommitQueue = false;
        // Array element is partially updated by at least some NBA
        bool hasPartialUpdate = false;
    };
    AstUser1Allocator<AstVarScope, AuxAstVarScope> m_vscpAux;

    // STATE - across all visitors
    std::unordered_map<const AstVarScope*, int> m_scopeVecMap;  // Next var number for each scope
    std::set<AstSenTree*> m_timingDomains;  // Timing resume domains
    // Table of new var names created under module
    std::map<const std::pair<AstNodeModule*, std::string>, AstVar*> m_modVarMap;
    AstNode* m_insertionPointp = nullptr;  // Where to insert new statements

    // STATE - for current visit position (use VL_RESTORER)
    AstActive* m_activep = nullptr;  // Current activate
    const AstCFunc* m_cfuncp = nullptr;  // Current public C Function
    AstAssignDly* m_nextDlyp = nullptr;  // The nextp of the previous AstAssignDly
    AstNodeProcedure* m_procp = nullptr;  // Current process
    bool m_inDlyLhs = false;  // True in lhs of AstAssignDelay
    bool m_inLoop = false;  // True in for loops
    bool m_inSuspendableOrFork = false;  // True in suspendable processes and forks
    bool m_ignoreBlkAndNBlk = false;  // Suppress delayed assignment BLKANDNBLK

    // STATE - for deferred conversion
    std::deque<Deferred> m_deferred;  // Deferred AstAssignDly instances to lower at the end
    AstVarScope* m_setVscp = nullptr;  // The last used set flag, for reuse

    // STATE - Statistic tracking
    VDouble0 m_statSharedSet;  // "VdlySet" variables eliminated by reuse
    VDouble0 m_commitQueuesWhole;  // Variables needing a commit queue without partial updates
    VDouble0 m_commitQueuesPartial;  // Variables needing a commit queue with partial updates

    // METHODS

    const AstNode* containingAssignment(const AstNode* nodep) {
        while (nodep && !VN_IS(nodep, NodeAssign)) nodep = nodep->backp();
        return nodep;
    }

    // Record and warn if a variable is assigned by both blocking and nonblocking assignments
    void markVarUsage(AstNodeVarRef* nodep, bool nonBlocking) {
        // Ignore references in certain contexts
        if (m_ignoreBlkAndNBlk) return;
        // Ignore if warning is disabled on this reference (used by V3Force).
        if (nodep->fileline()->warnIsOff(V3ErrorCode::BLKANDNBLK)) return;

        // Mark ref as blocking/non-blocking
        nodep->user1(nonBlocking);

        AstVarScope* const vscp = nodep->varScopep();

        // Pick up/set the first reference to this variable
        const AstNodeVarRef* const firstRefp = m_vscpAux(vscp).firstRefp;
        if (!firstRefp) {
            m_vscpAux(vscp).firstRefp = nodep;
            return;
        }

        // If both blocking/non-blocking, it's OK
        if (firstRefp->user1() == static_cast<int>(nonBlocking)) return;

        // Otherwise warn that both blocking and non-blocking assignments are used
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

    // Create new AstVarScope in the scope of the given 'vscp', with the given 'name' and 'dtypep'
    AstVarScope* createNewVarScope(AstVarScope* vscp, const string& name, AstNodeDType* dtypep) {
        FileLine* const flp = vscp->fileline();
        AstScope* const scopep = vscp->scopep();
        AstNodeModule* const modp = scopep->modp();
        // Get/create the corresponding AstVar
        AstVar*& varp = m_modVarMap[{modp, name}];
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
    AstVarScope* createNewVarScope(AstVarScope* vscp, const string& name, int width) {
        AstNodeDType* const dtypep = vscp->findBitDType(width, width, VSigning::UNSIGNED);
        return createNewVarScope(vscp, name, dtypep);
    }

    // Create a new AstActive, using the sensitivity list of the given 'activep'
    static AstActive* createActiveLike(FileLine* flp, AstActive* activep) {
        AstActive* const newActivep = new AstActive{flp, "sequentdly", activep->sensesp()};
        activep->addNextHere(newActivep);
        return newActivep;
    }

    // Check and ensure the given 'activep' contains the sensitivity of the 'currentActivep'.
    // Warn if they don't match (multiple domains assign the same signal via an NBA).
    static void checkActiveSense(AstVarRef* refp, AstActive* acivep, AstActive* currentActivep) {
        if (acivep->sensesp() == currentActivep->sensesp()) return;

        AstVar* const varp = refp->varScopep()->varp();
        // Warn once, if not turned off
        if (!varp->user1SetOnce() && !varp->fileline()->warnIsOff(V3ErrorCode::MULTIDRIVEN)) {
            varp->v3warn(MULTIDRIVEN,
                         "Signal has multiple driving blocks with different clocking: "
                             << varp->prettyNameQ() << '\n'
                             << refp->warnOther() << "... Location of first driving block\n"
                             << refp->warnContextPrimary() << '\n'
                             << acivep->warnOther() << "... Location of other driving block\n"
                             << acivep->warnContextSecondary());
        }

        // Make a new sensitivity list, which is the combination of both blocks
        AstSenItem* const sena = currentActivep->sensesp()->sensesp()->cloneTree(true);
        AstSenItem* const senb = acivep->sensesp()->sensesp()->cloneTree(true);
        AstSenTree* const treep = new AstSenTree{currentActivep->fileline(), sena};
        V3Const::constifyExpensiveEdit(treep);  // Remove duplicates
        treep->addSensesp(senb);
        if (AstSenTree* const storep = acivep->sensesStorep()) {
            VL_DO_DANGLING(storep->unlinkFrBack()->deleteTree(), storep);
        }
        acivep->sensesStorep(treep);
        acivep->sensesp(treep);
    }

    // Gather components of the given 'lhsp'. The component sub-expressions
    // are unlinked and unnecessary AstNodes deleted.
    static LhsComponents deconstructLhs(AstNodeExpr* const lhsp) {
        UASSERT_OBJ(!lhsp->backp(), lhsp, "Should have been unlinked");
        // The result being populated
        LhsComponents components;
        // Running node pointer
        AstNode* nodep = lhsp;
        // Gather AstSel applied - there should only be one
        if (AstSel* const selp = VN_CAST(nodep, Sel)) {
            nodep = selp->fromp()->unlinkFrBack();
            components.selLsbp = selp->lsbp()->unlinkFrBack();
            components.selWidthp = VN_AS(selp->widthp()->unlinkFrBack(), Const);
            VL_DO_DANGLING(selp->deleteTree(), selp);
        }
        UASSERT_OBJ(!VN_IS(nodep, Sel), lhsp, "Multiple 'AstSel' applied to LHS reference");
        // Gather AstArraySels applied
        while (AstArraySel* const arrSelp = VN_CAST(nodep, ArraySel)) {
            nodep = arrSelp->fromp()->unlinkFrBack();
            components.arrIdxps.push_back(arrSelp->bitp()->unlinkFrBack());
            VL_DO_DANGLING(arrSelp->deleteTree(), arrSelp);
        }
        std::reverse(components.arrIdxps.begin(), components.arrIdxps.end());
        // What remains must be an AstVarRef
        components.refp = VN_AS(nodep, VarRef);
        // Done
        return components;
    }

    // Reconstruct an LHS expression from the given 'components'. The component members
    // are linked under the returned expression without cloning, so they must be unlinked.
    static AstNodeExpr* reconstructLhs(const LhsComponents& components, FileLine* flp) {
        // Running node pointer
        AstNodeExpr* nodep = components.refp;
        // Apply AstArraySels
        for (AstNodeExpr* const idxp : components.arrIdxps) {
            nodep = new AstArraySel{flp, nodep, idxp};
        }
        // Apply AstSel, if any
        if (components.selLsbp) {
            nodep = new AstSel{flp, nodep, components.selLsbp, components.selWidthp};
        }
        // Done
        return nodep;
    }

    // Insert 'stmtp; after 'm_insertionPoint', then set 'm_insertionPoint' to the given statement
    // so the next insertion goes after the inserted statement.
    void insert(AstNode* stmtp) {
        m_insertionPointp->addNextHere(stmtp);
        m_insertionPointp = stmtp;
    }

    // Process the given AstAssignDly. Returns 'true' if the conversion is complete and 'nodep' can
    // be deleted. Returns 'false' if the 'nodep' must be retained for later processing.
    bool processAssignDly(AstAssignDly* nodep) {
        // Optimize consecutiev assignments
        const bool consecutive = m_nextDlyp == nodep;
        m_nextDlyp = VN_CAST(nodep->nextp(), AssignDly);

        // Insertion point
        UASSERT_OBJ(!m_insertionPointp, nodep, "Insertion point should be null");
        VL_RESTORER(m_insertionPointp);
        m_insertionPointp = nodep;

        // Deconstruct the LHS
        LhsComponents lhsComponents = deconstructLhs(nodep->lhsp()->unlinkFrBack());

        // The referenced variable
        AstVarScope* const vscp = lhsComponents.refp->varScopep();

        // Location of the AstAssignDly
        FileLine* const flp = nodep->fileline();

        // Name suffix for signals constructed below
        const std::string baseName
            = "__" + vscp->varp()->shortName() + "__v" + std::to_string(m_scopeVecMap[vscp]++);

        // Given an 'expression', return a new expression that always evaluates to the value of the
        // given expression at this point in the program. That is:
        // - If given a non-constant expression, create a new temporary AstVarScope with the given
        //   'name' prefix, assign the expression to it, and return a read reference to the new
        //   AstVarScope.
        // - If given a constant, just return that constant.
        const auto capture = [&](AstNodeExpr* exprp, const std::string& name) -> AstNodeExpr* {
            UASSERT_OBJ(!exprp->backp(), exprp, "Should have been unlinked");
            if (VN_IS(exprp, Const)) return exprp;
            const std::string realName = "__" + name + baseName;
            AstVarScope* const tmpVscp = createNewVarScope(vscp, realName, exprp->dtypep());
            insert(new AstAssign{flp, new AstVarRef{flp, tmpVscp, VAccess::WRITE}, exprp});
            return new AstVarRef{flp, tmpVscp, VAccess::READ};
        };

        // Unlink and Capture the RHS value
        AstNodeExpr* const rhsp = capture(nodep->rhsp()->unlinkFrBack(), "VdlyVal");

        // Capture the AstSel LSB - The width is always an AstConst, so nothing to do with that
        if (lhsComponents.selLsbp) {
            lhsComponents.selLsbp = capture(lhsComponents.selLsbp, "VdlyLsb");
        }

        // Capture the AstArraySel indices
        for (size_t i = 0; i < lhsComponents.arrIdxps.size(); ++i) {
            AstNodeExpr*& arrIdxpr = lhsComponents.arrIdxps[i];
            arrIdxpr = capture(arrIdxpr, "VdlyDim" + std::to_string(i));
        }

        if (m_inSuspendableOrFork) {
            if (m_inLoop && !lhsComponents.arrIdxps.empty()) {
                nodep->v3warn(BLKLOOPINIT,
                              "Unsupported: Non-blocking assignment to array inside loop "
                              "in suspendable process or fork");
                return true;
            }

            // Currently we convert all NBAs in suspendable blocks immediately.
            if (!m_vscpAux(vscp).nonDeferredFlp) {
                m_vscpAux(vscp).nonDeferredFlp = nodep->fileline();
            }

            // Get/Create 'Post' ordered block to commit the delayed value
            AstAlwaysPost* postp = m_vscpAux(vscp).suspPostp;
            if (!postp) {
                postp = new AstAlwaysPost{flp};
                if (!m_procp->user2p()) {
                    m_procp->user2p(createActiveLike(lhsComponents.refp->fileline(), m_activep));
                    // TODO: Somebody needs to explain me how it makes sense to set this
                    //       inside this 'if'. Shouldn't it be outside this 'if'? See #5084
                    m_vscpAux(vscp).suspPostp = postp;
                }
                VN_AS(m_procp->user2p(), Active)->addStmtsp(postp);
            }

            // Create the flag denoting an update is pending - no reuse here
            AstVarScope* const setVscp = createNewVarScope(vscp, "__VdlySet" + baseName, 1);
            // Set the flag here
            insert(new AstAssign{flp, new AstVarRef{flp, setVscp, VAccess::WRITE},
                                 new AstConst{flp, AstConst::BitTrue{}}});
            // Create 'if (__VdlySet) { ... commit .. }'
            AstIf* const ifp = new AstIf{flp, new AstVarRef{flp, setVscp, VAccess::READ}};
            postp->addStmtsp(ifp);
            // Clear __VdlySet in the post block
            ifp->addThensp(new AstAssign{flp, new AstVarRef{flp, setVscp, VAccess::WRITE},
                                         new AstConst{flp, 0}});
            // Finally assign the delayed value to the reconstructed LHS
            AstNodeExpr* const newLhsp = reconstructLhs(lhsComponents, flp);
            ifp->addThensp(new AstAssign{flp, newLhsp, rhsp});
            // The original AstAssignDly ('nodep') can be deleted
            return true;
        } else {
            if (m_inLoop) {
                UASSERT_OBJ(!lhsComponents.arrIdxps.empty(), nodep, "Should be an array");
                const AstBasicDType* const basicp = vscp->dtypep()->basicp();
                if (!basicp
                    || !(basicp->isIntegralOrPacked() || basicp->isDouble()
                         || basicp->isString())) {
                    nodep->v3warn(BLKLOOPINIT,
                                  "Unsupported: Non-blocking assignment to array with "
                                  "compound element type inside loop");
                    return true;
                }
                m_vscpAux(vscp).needsCommitQueue = true;
                if (lhsComponents.selLsbp) m_vscpAux(vscp).hasPartialUpdate = true;
            }
            // Record this AstAssignDly for deferred processing
            m_deferred.emplace_back();
            Deferred& record = m_deferred.back();
            // Populate it
            record.lhsComponents = std::move(lhsComponents);
            record.rhsp = rhsp;
            record.activep = m_activep;
            record.insertionPointp = m_insertionPointp;
            record.suffix = std::move(baseName);
            record.consecutive = consecutive;
            // Note consecutive assignment for optimization
            // If we inserted new statements, the original AstAssignDly ('nodep')
            // can be deleted. Otherwise, it must be kept as a placeholder.
            return m_insertionPointp != nodep;
        }
    }

    // Create a temporary variable in the scope of 'vscp',with the given 'name', and with 'dtypep'
    // type, with the bits selected by 'sLsbp'/'sWidthp' set to 'insertp', other bits set to zero.
    // Returns a read reference to the temporary variable.
    AstVarRef* createWidened(FileLine* flp, AstVarScope* vscp, AstNodeDType* dtypep,
                             AstNodeExpr* sLsbp, AstNodeExpr* sWidthp, const std::string& name,
                             AstNodeExpr* insertp) {
        // Create temporary variable.
        AstVarScope* const tp = createNewVarScope(vscp, name, dtypep);
        // Zero it
        AstConst* const zerop = new AstConst{flp, AstConst::DTyped{}, dtypep};
        zerop->num().setAllBits0();
        insert(new AstAssign{flp, new AstVarRef{flp, tp, VAccess::WRITE}, zerop});
        // Set the selected bits to 'insertp'
        AstSel* const selp = new AstSel{flp, new AstVarRef{flp, tp, VAccess::WRITE},
                                        sLsbp->cloneTreePure(true), sWidthp->cloneTreePure(true)};
        insert(new AstAssign{flp, selp, insertp});
        // This is the expression to get the value of the temporary
        return new AstVarRef{flp, tp, VAccess::READ};
    };

    // Convert the given deferred assignment for the given AstVarScope
    void convertDeferred(Deferred& record) {
        // Unpack all the parts
        LhsComponents lhsComponents = std::move(record.lhsComponents);
        AstActive*& oActivep = record.activep;  // Original AstActive the AstAssignDly was under

        // Insertion point
        UASSERT_OBJ(!m_insertionPointp, record.insertionPointp, "Insertion point should be null");
        VL_RESTORER(m_insertionPointp);
        m_insertionPointp = record.insertionPointp;

        // If the original AstAssignDly was kept as a placeholder, we will need to delete it
        AstAssignDly* const dlyp = VN_CAST(m_insertionPointp, AssignDly);

        FileLine* const flp = m_insertionPointp->fileline();
        AstVarScope* const vscp = lhsComponents.refp->varScopep();

        // Get/Create 'Post' ordered block to commit the delayed value
        AstAlwaysPost* const postp = [&]() {
            if (AstAlwaysPost* const p = m_vscpAux(vscp).postp) return p;
            // Make the new AstActive with identical sensitivity tree
            AstActive* const activep = createActiveLike(lhsComponents.refp->fileline(), oActivep);
            m_vscpAux(vscp).activep = activep;
            // Add the 'Post' scheduled block
            AstAlwaysPost* const p = new AstAlwaysPost{flp};
            activep->addStmtsp(p);
            m_vscpAux(vscp).postp = p;
            return p;
        }();
        // Pick up the active block containing 'postp'
        AstActive* const activep = m_vscpAux(vscp).activep;
        // Ensure it contains the current sensitivities
        checkActiveSense(lhsComponents.refp, activep, oActivep);

        if (m_vscpAux(vscp).needsCommitQueue) {
            if (FileLine* const badFlp = m_vscpAux(vscp).nonDeferredFlp) {
                m_insertionPointp->v3warn(
                    BLKLOOPINIT,
                    "Unsupported: Non-blocking assignment to array in both "
                    "loop and suspendable process/fork\n"
                        << badFlp->warnOther()
                        << "... Location of non-blocking assignment in suspendable process/fork\n"
                        << badFlp->warnContextSecondary() << m_insertionPointp->warnOther()
                        << "... Location of non-blocking assignment inside loop\n");
                return;
            }

            // Need special handling for variables that require partial updates
            const bool partial = m_vscpAux(vscp).hasPartialUpdate;

            // If partial updates are required, construct the mask and the widened value
            AstNodeExpr* valuep = record.rhsp;
            AstNodeExpr* maskp = nullptr;
            if (partial) {
                // Type of array element
                AstNodeDType* const eDTypep = [&]() -> AstNodeDType* {
                    AstNodeDType* dtypep = vscp->dtypep()->skipRefp();
                    while (AstUnpackArrayDType* const ap = VN_CAST(dtypep, UnpackArrayDType)) {
                        dtypep = ap->subDTypep()->skipRefp();
                    }
                    return dtypep;
                }();

                if (AstNodeExpr* const sLsbp = lhsComponents.selLsbp) {
                    // This is a partial assignment. Need to create a mask and widen the value to
                    // element size.
                    AstConst* const sWidthp = lhsComponents.selWidthp;

                    // Create mask value
                    maskp = [&]() -> AstNodeExpr* {
                        // Constant mask we can compute here
                        if (AstConst* const cLsbp = VN_CAST(sLsbp, Const)) {
                            AstConst* const cp = new AstConst{flp, AstConst::DTyped{}, eDTypep};
                            cp->num().setAllBits0();
                            const int lsb = cLsbp->toSInt();
                            const int msb = lsb + sWidthp->toSInt() - 1;
                            for (int bit = lsb; bit <= msb; ++bit) cp->num().setBit(bit, '1');
                            return cp;
                        }

                        // A non-constant mask we must compute at run-time.
                        AstConst* const onesp
                            = new AstConst{flp, AstConst::WidthedValue{}, sWidthp->toSInt(), 0};
                        onesp->num().setAllBits1();
                        return createWidened(flp, vscp, eDTypep, sLsbp, sWidthp,  //
                                             "__VdlyMask" + record.suffix, onesp);
                    }();

                    // Adjust value to element size
                    valuep = [&]() -> AstNodeExpr* {
                        // Constant value with constant select we can compute here
                        if (AstConst* const cValuep = VN_CAST(valuep, Const)) {
                            if (AstConst* const cLsbp = VN_CAST(sLsbp, Const)) {  //
                                AstConst* const cp
                                    = new AstConst{flp, AstConst::DTyped{}, eDTypep};
                                cp->num().setAllBits0();
                                cp->num().opSelInto(cValuep->num(), cLsbp->toSInt(),
                                                    sWidthp->toSInt());
                                return cp;
                            }
                        }

                        // A non-constant value we must adjust.
                        return createWidened(flp, vscp, eDTypep, sLsbp, sWidthp,  //
                                             "__VdlyElem" + record.suffix, valuep);
                    }();

                    // Finished with the sel operands here
                    VL_DO_DANGLING(lhsComponents.selLsbp->deleteTree(), lhsComponents.selLsbp);
                    VL_DO_DANGLING(lhsComponents.selWidthp->deleteTree(), lhsComponents.selWidthp);
                } else {
                    // If this assignment is not partial, set mask to ones and we are done
                    AstConst* const ones = new AstConst{flp, AstConst::DTyped{}, eDTypep};
                    ones->num().setAllBits1();
                    maskp = ones;
                }
            }

            // Create/get the commit queue
            if (!vscp->user2p()) {
                FileLine* const vflp = vscp->fileline();

                // Statistics
                if (partial) {
                    ++m_commitQueuesPartial;
                } else {
                    ++m_commitQueuesWhole;
                }

                // Create the commit queue variable
                auto* const cqDTypep
                    = new AstNBACommitQueueDType{vflp, vscp->dtypep()->skipRefp(), partial};
                v3Global.rootp()->typeTablep()->addTypesp(cqDTypep);
                const std::string name = "__VdlyCommitQueue" + record.suffix;
                AstVarScope* const newCqp = createNewVarScope(vscp, name, cqDTypep);
                newCqp->varp()->noReset(true);
                vscp->user2p(newCqp);

                // Commit it in the 'Post' block
                AstCMethodHard* const callp = new AstCMethodHard{
                    vflp, new AstVarRef{vflp, newCqp, VAccess::READWRITE}, "commit"};
                callp->dtypeSetVoid();
                callp->addPinsp(lhsComponents.refp->cloneTreePure(false));
                postp->addStmtsp(callp->makeStmt());
            }
            AstVarScope* const cqp = VN_AS(vscp->user2p(), VarScope);

            // Enqueue the update at the original location
            AstCMethodHard* const callp
                = new AstCMethodHard{flp, new AstVarRef{flp, cqp, VAccess::READWRITE}, "enqueue"};
            callp->dtypeSetVoid();
            callp->addPinsp(valuep);
            if (maskp) callp->addPinsp(maskp);
            for (AstNodeExpr* const indexp : lhsComponents.arrIdxps) callp->addPinsp(indexp);
            insert(callp->makeStmt());
        } else {
            // Create the flag denoting an update is pending
            if (record.consecutive) {
                // Simplistic optimization.  If the previous assignment was immediately before this
                // assignment, we can reuse the existing flag. This is good for code like:
                //   arrayA[0] <= something;
                //   arrayB[1] <= something;
                ++m_statSharedSet;
            } else {
                // Create new flag
                m_setVscp = createNewVarScope(vscp, "__VdlySet" + record.suffix, 1);
                // Set it here
                insert(new AstAssign{flp, new AstVarRef{flp, m_setVscp, VAccess::WRITE},
                                     new AstConst{flp, AstConst::BitTrue{}}});
                // Add the 'Pre' ordered reset for the flag
                activep->addStmtsp(new AstAssignPre{
                    flp, new AstVarRef{flp, m_setVscp, VAccess::WRITE}, new AstConst{flp, 0}});
            };

            // Create/Get 'if (__VdlySet) { ... commit .. }'
            AstIf* ifp = nullptr;
            if (postp->user2p() == m_setVscp) {
                // Optimize as above. If sharing VdlySet *ON SAME VARIABLE*, we can share the 'if'
                ifp = VN_AS(postp->user1p(), If);
            } else {
                ifp = new AstIf{flp, new AstVarRef{flp, m_setVscp, VAccess::READ}};
                postp->addStmtsp(ifp);
                postp->user1p(ifp);  // Remember the associated 'AstIf'
                postp->user2p(m_setVscp);  // Remember the VdlySet variable used as the condition.
            }

            // Finally assign the delayed value to the reconstructed LHS
            AstNodeExpr* const newLhsp = reconstructLhs(lhsComponents, flp);
            ifp->addThensp(new AstAssign{flp, newLhsp, record.rhsp});
        }

        // If the original AstAssignDelay was kept as a placeholder, we can nuke it now.
        if (dlyp) pushDeletep(dlyp->unlinkFrBack());
    }

    // VISITORS
    void visit(AstNetlist* nodep) override {
        iterateChildren(nodep);
        // Convert all AstAssignDelay instances that were not converted during the traversal
        for (Deferred& record : m_deferred) convertDeferred(record);
    }
    void visit(AstScope* nodep) override {
        AstNode::user2ClearTree();
        iterateChildren(nodep);
    }
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
        // Two sets to same variable in different actives must use different vars.
        AstNode::user2ClearTree();
        iterateChildren(nodep);
    }
    void visit(AstNodeProcedure* nodep) override {
        {
            VL_RESTORER(m_inSuspendableOrFork);
            VL_RESTORER(m_procp);
            m_inSuspendableOrFork = nodep->isSuspendable();
            m_procp = nodep;
            iterateChildren(nodep);
        }
        if (m_timingDomains.empty()) return;
        if (AstActive* const actp = VN_AS(nodep->user2p(), Active)) {
            // Merge all timing domains (and possibly the original active's domain)
            // to create a sentree for the pre/post logic
            // TODO: allow multiple sentrees per active, so we don't have
            //       to merge them and create a new trigger
            AstSenTree* senTreep = nullptr;
            if (actp->sensesp()->hasClocked()) senTreep = actp->sensesp()->cloneTree(false);
            for (AstSenTree* const domainp : m_timingDomains) {
                if (!senTreep) {
                    senTreep = domainp->cloneTree(false);
                } else {
                    senTreep->addSensesp(domainp->sensesp()->cloneTree(true));
                    senTreep->multi(true);  // Comment that it was made from multiple domains
                }
            }
            V3Const::constifyExpensiveEdit(senTreep);  // Remove duplicates
            actp->sensesp(senTreep);
            actp->sensesStorep(senTreep);
        }
        m_timingDomains.clear();
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
        if (nodep->isDelayed()) {
            AstVarRef* const vrefp = VN_AS(nodep->operandp(), VarRef);
            vrefp->unlinkFrBack();
            const std::string newvarname = "__Vdly__" + vrefp->varp()->shortName();
            AstVarScope* const dlyvscp = createNewVarScope(vrefp->varScopep(), newvarname, 1);

            const auto dlyRef = [=](VAccess access) {  //
                return new AstVarRef{flp, dlyvscp, access};
            };

            AstAssignPre* const prep = new AstAssignPre{flp, dlyRef(VAccess::WRITE),
                                                        new AstConst{flp, AstConst::BitFalse{}}};
            AstAlwaysPost* const postp = new AstAlwaysPost{flp};
            {
                AstIf* const ifp = new AstIf{flp, dlyRef(VAccess::READ)};
                postp->addStmtsp(ifp);
                AstCMethodHard* const callp = new AstCMethodHard{flp, vrefp, "fire"};
                callp->dtypeSetVoid();
                ifp->addThensp(callp->makeStmt());
            }

            AstActive* const activep = createActiveLike(flp, m_activep);
            activep->addStmtsp(prep);
            activep->addStmtsp(postp);

            AstAssign* const assignp = new AstAssign{flp, dlyRef(VAccess::WRITE),
                                                     new AstConst{flp, AstConst::BitTrue{}}};
            nodep->replaceWith(assignp);
        } else {
            AstCMethodHard* const callp
                = new AstCMethodHard{flp, nodep->operandp()->unlinkFrBack(), "fire"};
            callp->dtypeSetVoid();
            nodep->replaceWith(callp->makeStmt());
        }
        VL_DO_DANGLING(nodep->deleteTree(), nodep);
    }

    // Pre/Post logic are created here and their content need no further changes, so ignore.
    void visit(AstAssignPre*) override {}
    void visit(AstAssignPost*) override {}
    void visit(AstAlwaysPost*) override {}

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
        const bool isArray = VN_IS(nodep->lhsp(), ArraySel)
                             || (VN_IS(nodep->lhsp(), Sel)
                                 && VN_IS(VN_AS(nodep->lhsp(), Sel)->fromp(), ArraySel));
        if (isArray) {
            if (const AstBasicDType* const basicp = nodep->lhsp()->dtypep()->basicp()) {
                // TODO: this message is not covered by tests
                if (basicp->isEvent()) nodep->v3warn(E_UNSUPPORTED, "Unsupported: event arrays");
            }
            if (processAssignDly(nodep)) VL_DO_DANGLING(pushDeletep(nodep->unlinkFrBack()), nodep);
        } else if (m_inSuspendableOrFork) {
            const bool converted = processAssignDly(nodep);
            // Current implementation always converts these
            UASSERT_OBJ(converted, nodep, "NBA in suspendable processes should have be converted");
            VL_DO_DANGLING(pushDeletep(nodep->unlinkFrBack()), nodep);
        } else {
            {
                VL_RESTORER(m_inDlyLhs);
                m_inDlyLhs = true;
                iterate(nodep->lhsp());
            }
            iterate(nodep->rhsp());
        }
    }

    void visit(AstVarRef* nodep) override {
        // Ignore refs inserted by 'replaceWith' just below
        if (nodep->user2()) return;
        // Only care about write refs
        if (!nodep->access().isWriteOrRW()) return;
        // Check var usage
        markVarUsage(nodep, m_inDlyLhs);

        // Below we rewrite the LHS of AstAssignDelay only
        if (!m_inDlyLhs) return;

        UASSERT_OBJ(!nodep->access().isRW(), nodep, "<= on read+write method");
        UASSERT_OBJ(m_activep, nodep, "<= not under sensitivity block");
        UASSERT_OBJ(m_activep->hasClocked(), nodep,
                    "<= assignment in non-clocked block, should have been converted in V3Active");

        // Replace with reference to the shadow variable
        FileLine* const flp = nodep->fileline();
        AstVarScope* const vscp = nodep->varScopep();
        AstVarScope*& dlyVscp = m_vscpAux(vscp).delayVscp;

        // Create the shadow variable and related active block if not yet exists
        if (!dlyVscp) {
            // Create the shadow variable
            const std::string name = "__Vdly__" + vscp->varp()->shortName();
            dlyVscp = createNewVarScope(vscp, name, vscp->dtypep());
            // Make the new AstActive with identical sensitivity tree
            AstActive* const activep = createActiveLike(flp, m_activep);
            m_vscpAux(vscp).activep = activep;

            // Add 'Pre' scheduled 'shadowVariable = originalVariable' assignment
            activep->addStmtsp(new AstAssignPre{flp, new AstVarRef{flp, dlyVscp, VAccess::WRITE},
                                                new AstVarRef{flp, vscp, VAccess::READ}});
            // Add 'Post' scheduled 'originalVariable = shadowVariable' assignment
            activep->addStmtsp(new AstAssignPost{flp, new AstVarRef{flp, vscp, VAccess::WRITE},
                                                 new AstVarRef{flp, dlyVscp, VAccess::READ}});
        }

        // Ensure the active block of the shadow variable contains the current sensitivities
        checkActiveSense(nodep, m_vscpAux(vscp).activep, m_activep);

        // Replace reference with reference to the shadow variable
        AstVarRef* const newRefp = new AstVarRef{flp, dlyVscp, VAccess::WRITE};
        newRefp->user2(true);  // skip visit after repalce
        nodep->replaceWith(newRefp);
        VL_DO_DANGLING(pushDeletep(nodep), nodep);
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
    void visit(AstExprStmt* nodep) override {
        VL_RESTORER(m_inDlyLhs);
        // Restoring is needed, because AstExprStmt may contain assignments
        m_inDlyLhs = false;
        iterateChildren(nodep);
    }

    //--------------------
    void visit(AstNode* nodep) override { iterateChildren(nodep); }

public:
    // CONSTRUCTORS
    explicit DelayedVisitor(AstNetlist* nodep) { iterate(nodep); }
    ~DelayedVisitor() override {
        V3Stats::addStat("Optimizations, Delayed shared-sets", m_statSharedSet);
        V3Stats::addStat("Dynamic NBA, variables needing commit queue with partial updates",
                         m_commitQueuesPartial);
        V3Stats::addStat("Dynamic NBA, variables needing commit queue without partial updates",
                         m_commitQueuesWhole);
    }
};

//######################################################################
// Delayed class functions

void V3Delayed::delayedAll(AstNetlist* nodep) {
    UINFO(2, __FUNCTION__ << ": " << endl);
    { DelayedVisitor{nodep}; }  // Destruct before checking
    V3Global::dumpCheckGlobalTree("delayed", 0, dumpTreeEitherLevel() >= 3);
}
