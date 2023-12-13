// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Add temporaries, such as for delayed nodes
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
// V3Delayed's Transformations:
//
// Each module:
//      Replace ASSIGNDLY var, exp
//          With   ASSIGNDLY newvar, exp
//          At top of block:  VAR  newvar
//          At bottom of block: ASSIGNW var newvar
//              Need _x_dly = x at top of active if "x" is not always set
//                      For now we'll say it's set if at top of block (not under IF, etc)
//              Need x = _x_dly at bottom of active if "x" is never referenced on LHS
//                      in the active, and above rule applies too.
//                      (If so, use x on LHS, not _x_dly.)
//
//      If a signal is set in multiple always blocks, we need a dly read & set with
//      multiple clock sensitivities.  We have 3 options:
//          1. When detected, make a new ACTIVE and move earlier created delayed assignment there
//          2. Form unique ACTIVE for every multiple clocked assignment
//          3. Predetect signals from multiple always blocks and do #2 on them
//          Since all 3 require a top activation cleanup, we do #2 which is easiest.
//
// ASSIGNDLY (BITSEL(ARRAYSEL (VARREF(v), bits), selbits), rhs)
// ->   VAR __Vdlyvset_x
//      VAR __Vdlyvval_x
//      VAR __Vdlyvdim_x
//      VAR __Vdlyvlsb_x
//      ASSIGNW (__Vdlyvset_x,0)
//      ...
//      ASSIGNW (VARREF(__Vdlyvval_x), rhs)
//      ASSIGNW (__Vdlyvdim_x, dimension_number)
//      ASSIGNW (__Vdlyvset_x, 1)
//      ...
//      ASSIGNW (BITSEL(ARRAYSEL(VARREF(x), __Vdlyvdim_x), __Vdlyvlsb_x), __Vdlyvval_x)
//
//*************************************************************************

#include "V3PchAstNoMT.h"  // VL_MT_DISABLED_CODE_UNIT

#include "V3Delayed.h"

#include "V3AstUserAllocator.h"
#include "V3Stats.h"

#include <deque>

VL_DEFINE_DEBUG_FUNCTIONS;

//######################################################################
// Delayed state, as a visitor of each AstNode

class DelayedVisitor final : public VNVisitor {
    // NODE STATE
    // Cleared each module:
    //  AstVarScope::user1p()   -> aux
    //  AstVar::user2()         -> bool.  Set true if already made warning
    //  AstVarRef::user1()      -> bool.  Set true if was blocking reference
    //  AstVarRef::user2()      -> bool.  Set true if already processed
    //  AstAlwaysPost::user1()  -> AstIf*.  Last IF (__Vdlyvset__) created under this AlwaysPost
    //  AstAlwaysPost::user2()  -> ActActive*.  Points to activity block of signal
    //                                      (valid when AstAlwaysPost::user4p is valid)
    // Cleared each scope/active:
    //  AstAssignDly::user3()   -> AstVarScope*.  __Vdlyvset__ created for this assign
    //  AstAlwaysPost::user3()  -> AstVarScope*.  __Vdlyvset__ last referenced in IF
    const VNUser1InUse m_inuser1;
    const VNUser2InUse m_inuser2;
    const VNUser3InUse m_inuser3;

    struct AuxAstVarScope final {
        // Points to temp (shadow) variable created.
        AstVarScope* delayVscp = nullptr;
        // Points to activity block of signal (valid when AstVarScope::user1p is valid)
        AstActive* activep = nullptr;
        // Post block for this variable used for AssignDlys in suspendable processes
        AstAlwaysPost* suspFinalp = nullptr;
        // Post block for this variable
        AstAlwaysPost* finalp = nullptr;
        // Last blocking or non-blocking reference
        AstNodeVarRef* lastRefp = nullptr;
    };
    AstUser1Allocator<AstVarScope, AuxAstVarScope> m_vscpAux;

    // STATE - across all visitors
    std::unordered_map<const AstVarScope*, int> m_scopeVecMap;  // Next var number for each scope
    std::set<AstSenTree*> m_timingDomains;  // Timing resume domains
    using VarMap = std::map<const std::pair<AstNodeModule*, std::string>, AstVar*>;
    VarMap m_modVarMap;  // Table of new var names created under module
    VDouble0 m_statSharedSet;  // Statistic tracking

    // STATE - for current visit position (use VL_RESTORER)
    AstActive* m_activep = nullptr;  // Current activate
    const AstCFunc* m_cfuncp = nullptr;  // Current public C Function
    AstAssignDly* m_nextDlyp = nullptr;  // Next delayed assignment in a list of assignments
    AstNodeProcedure* m_procp = nullptr;  // Current process
    bool m_inDly = false;  // True in delayed assignments
    bool m_inLoop = false;  // True in for loops
    bool m_inInitial = false;  // True in static initializers and initial blocks
    bool m_inSuspendableOrFork = false;  // True in suspendable processes and forks
    bool m_ignoreBlkAndNBlk = false;  // Suppress delayed assignment BLKANDNBLK

    // METHODS

    const AstNode* containingAssignment(const AstNode* nodep) {
        while (nodep && !VN_IS(nodep, NodeAssign)) nodep = nodep->backp();
        return nodep;
    }

    void markVarUsage(AstNodeVarRef* nodep, bool blocking) {
        // Ignore if warning is disabled on this reference (used by V3Force).
        if (nodep->fileline()->warnIsOff(V3ErrorCode::BLKANDNBLK)) return;
        if (m_ignoreBlkAndNBlk) return;
        if (blocking) nodep->user1(true);
        AstVarScope* const vscp = nodep->varScopep();
        // UINFO(4, " MVU " << blocking << " " << nodep << endl);
        const AstNode* const lastrefp = m_vscpAux(vscp).lastRefp;
        if (!lastrefp) {
            m_vscpAux(vscp).lastRefp = nodep;
        } else {
            const bool last_was_blocking = lastrefp->user1();
            if (last_was_blocking != blocking) {
                const AstNode* nonblockingp = blocking ? nodep : lastrefp;
                if (const AstNode* np = containingAssignment(nonblockingp)) nonblockingp = np;
                const AstNode* blockingp = blocking ? lastrefp : nodep;
                if (const AstNode* np = containingAssignment(blockingp)) blockingp = np;
                vscp->v3warn(
                    BLKANDNBLK,
                    "Unsupported: Blocked and non-blocking assignments to same variable: "
                        << vscp->varp()->prettyNameQ() << '\n'
                        << vscp->warnContextPrimary() << '\n'
                        << blockingp->warnOther() << "... Location of blocking assignment\n"
                        << blockingp->warnContextSecondary() << '\n'
                        << nonblockingp->warnOther() << "... Location of nonblocking assignment\n"
                        << nonblockingp->warnContextSecondary());
            }
        }
    }
    AstVarScope* createVarSc(AstVarScope* oldvarscp, const string& name,
                             int width /*0==fromoldvar*/, AstNodeDType* newdtypep) {
        // Because we've already scoped it, we may need to add both the AstVar and the AstVarScope
        UASSERT_OBJ(oldvarscp->scopep(), oldvarscp, "Var unscoped");
        FileLine* const flp = oldvarscp->fileline();
        AstNodeModule* const addmodp = oldvarscp->scopep()->modp();
        // We need a new AstVar, but only one for all scopes, to match the new AstVarScope
        const auto pair = m_modVarMap.emplace(std::make_pair(addmodp, name), nullptr);
        if (pair.second) {
            AstVar* varp = nullptr;
            if (newdtypep) {
                varp = new AstVar{flp, VVarType::BLOCKTEMP, name, newdtypep};
            } else if (width == 0) {
                varp = new AstVar{flp, VVarType::BLOCKTEMP, name, oldvarscp->varp()};
                varp->dtypeFrom(oldvarscp);
            } else {  // Used for vset and dimensions, so can zero init
                varp = new AstVar{flp, VVarType::BLOCKTEMP, name, VFlagBitPacked{}, width};
            }
            addmodp->addStmtsp(varp);
            pair.first->second = varp;
        }
        AstVar* const varp = pair.first->second;

        AstVarScope* const varscp = new AstVarScope{flp, oldvarscp->scopep(), varp};
        oldvarscp->scopep()->addVarsp(varscp);
        return varscp;
    }

    AstActive* createActive(AstNode* varrefp) {
        AstActive* const newactp
            = new AstActive{varrefp->fileline(), "sequentdly", m_activep->sensesp()};
        // Was addNext(), but addNextHere() avoids a linear search.
        m_activep->addNextHere(newactp);
        return newactp;
    }
    void checkActivePost(AstVarRef* varrefp, AstActive* oldactivep) {
        // Check for MULTIDRIVEN, and if so make new sentree that joins old & new sentree
        UASSERT_OBJ(oldactivep, varrefp, "<= old dly assignment not put under sensitivity block");
        if (oldactivep->sensesp() != m_activep->sensesp()) {
            if (!varrefp->varp()->fileline()->warnIsOff(V3ErrorCode::MULTIDRIVEN)
                && !varrefp->varp()->user2()) {
                varrefp->varp()->v3warn(
                    MULTIDRIVEN,
                    "Signal has multiple driving blocks with different clocking: "
                        << varrefp->varp()->prettyNameQ() << '\n'
                        << varrefp->warnOther() << "... Location of first driving block\n"
                        << varrefp->warnContextPrimary() << '\n'
                        << oldactivep->warnOther() << "... Location of other driving block\n"
                        << oldactivep->warnContextSecondary());
                varrefp->varp()->user2(true);
            }
            UINFO(4, "AssignDupDlyVar: " << varrefp << endl);
            UINFO(4, "  Act: " << m_activep << endl);
            UINFO(4, "  Act: " << oldactivep << endl);
            // Make a new sensitivity list, which is the combination of both blocks
            AstSenItem* const sena = m_activep->sensesp()->sensesp()->cloneTree(true);
            AstSenItem* const senb = oldactivep->sensesp()->sensesp()->cloneTree(true);
            AstSenTree* const treep = new AstSenTree{m_activep->fileline(), sena};
            if (senb) treep->addSensesp(senb);
            if (AstSenTree* const storep = oldactivep->sensesStorep()) {
                storep->unlinkFrBack();
                pushDeletep(storep);
            }
            oldactivep->sensesStorep(treep);
            oldactivep->sensesp(treep);
        }
    }

    AstNodeExpr* createDlyOnSet(AstAssignDly* nodep, AstNodeExpr* lhsp) {
        // Create delayed assignment
        // See top of this file for transformation
        // Return the new LHS for the assignment, Null = unlink
        // Find selects
        AstNodeExpr* newlhsp = nullptr;  // nullptr = unlink old assign
        const AstSel* bitselp = nullptr;
        AstArraySel* arrayselp = nullptr;
        AstVarRef* varrefp = nullptr;
        if (VN_IS(lhsp, Sel)) {
            bitselp = VN_AS(lhsp, Sel);
            arrayselp = VN_CAST(bitselp->fromp(), ArraySel);
            if (!arrayselp) varrefp = VN_AS(bitselp->fromp(), VarRef);
        } else if (VN_IS(lhsp, ArraySel)) {
            arrayselp = VN_AS(lhsp, ArraySel);
        } else {
            varrefp = VN_AS(lhsp, VarRef);
        }
        if (arrayselp) {
            UASSERT_OBJ(!VN_IS(arrayselp->dtypep()->skipRefp(), UnpackArrayDType), nodep,
                        "ArraySel with unpacked arrays should have been removed in V3Slice");
            UINFO(4, "AssignDlyArray: " << nodep << endl);
        } else {
            UASSERT_OBJ(varrefp, nodep, "No arraysel nor varref");
            UINFO(4, "AssignDlyOnSet: " << nodep << endl);
        }
        //=== Dimensions: __Vdlyvdim__
        std::deque<AstNodeExpr*> dimvalp;  // Assignment value for each dimension of assignment
        AstNode* dimselp = arrayselp;
        for (; VN_IS(dimselp, ArraySel); dimselp = VN_AS(dimselp, ArraySel)->fromp()) {
            AstNodeExpr* const valp = VN_AS(dimselp, ArraySel)->bitp()->unlinkFrBack();
            dimvalp.push_front(valp);
        }
        if (dimselp) varrefp = VN_AS(dimselp, VarRef);
        UASSERT_OBJ(varrefp, nodep, "No var underneath arraysels");
        UASSERT_OBJ(varrefp->varScopep(), varrefp, "Var didn't get varscoped in V3Scope.cpp");
        varrefp->unlinkFrBack();
        const AstVar* const oldvarp = varrefp->varp();
        const int modVecNum = m_scopeVecMap[varrefp->varScopep()]++;
        //
        std::deque<AstNodeExpr*> dimreadps;  // Read value for each dimension of assignment
        for (unsigned dimension = 0; dimension < dimvalp.size(); dimension++) {
            AstNodeExpr* const dimp = dimvalp[dimension];
            if (VN_IS(dimp, Const)) {  // bit = const, can just use it
                dimreadps.push_front(dimp);
            } else {
                const string bitvarname = string{"__Vdlyvdim"} + cvtToStr(dimension) + "__"
                                          + oldvarp->shortName() + "__v" + cvtToStr(modVecNum);
                AstVarScope* const bitvscp
                    = createVarSc(varrefp->varScopep(), bitvarname, dimp->width(), nullptr);
                AstAssign* const bitassignp = new AstAssign{
                    nodep->fileline(), new AstVarRef{nodep->fileline(), bitvscp, VAccess::WRITE},
                    dimp};
                nodep->addNextHere(bitassignp);
                dimreadps.push_front(new AstVarRef{nodep->fileline(), bitvscp, VAccess::READ});
            }
        }
        //
        //=== Bitselect: __Vdlyvlsb__
        AstNodeExpr* bitreadp = nullptr;  // Code to read Vdlyvlsb
        if (bitselp) {
            AstNodeExpr* const lsbvaluep = bitselp->lsbp()->unlinkFrBack();
            if (VN_IS(bitselp->fromp(), Const)) {
                // vlsb = constant, can just push constant into where we use it
                bitreadp = lsbvaluep;
            } else {
                const string bitvarname
                    = string{"__Vdlyvlsb__"} + oldvarp->shortName() + "__v" + cvtToStr(modVecNum);
                AstVarScope* const bitvscp
                    = createVarSc(varrefp->varScopep(), bitvarname, lsbvaluep->width(), nullptr);
                AstAssign* const bitassignp = new AstAssign{
                    nodep->fileline(), new AstVarRef{nodep->fileline(), bitvscp, VAccess::WRITE},
                    lsbvaluep};
                nodep->addNextHere(bitassignp);
                bitreadp = new AstVarRef{nodep->fileline(), bitvscp, VAccess::READ};
            }
        }
        //
        //=== Value: __Vdlyvval__
        AstNodeExpr* valreadp;  // Code to read Vdlyvval
        if (VN_IS(nodep->rhsp(), Const)) {
            // vval = constant, can just push constant into where we use it
            valreadp = nodep->rhsp()->unlinkFrBack();
        } else {
            const string valvarname
                = string{"__Vdlyvval__"} + oldvarp->shortName() + "__v" + cvtToStr(modVecNum);
            AstVarScope* const valvscp
                = createVarSc(varrefp->varScopep(), valvarname, 0, nodep->rhsp()->dtypep());
            newlhsp = new AstVarRef{nodep->fileline(), valvscp, VAccess::WRITE};
            valreadp = new AstVarRef{nodep->fileline(), valvscp, VAccess::READ};
        }
        //
        //=== Setting/not setting boolean: __Vdlyvset__
        AstVarScope* setvscp;
        AstAssignPre* setinitp = nullptr;

        if (!m_inSuspendableOrFork && nodep->user3p()) {
            // Simplistic optimization.  If the previous statement in same scope was also a =>,
            // then we told this nodep->user3 we can use its Vdlyvset rather than making a new one.
            // This is good for code like:
            //    for (i=0; i<5; i++)  vector[i] <= something;
            setvscp = VN_AS(nodep->user3p(), VarScope);
            ++m_statSharedSet;
        } else {  // Create new one
            const string setvarname
                = string{"__Vdlyvset__"} + oldvarp->shortName() + "__v" + cvtToStr(modVecNum);
            setvscp = createVarSc(varrefp->varScopep(), setvarname, 1, nullptr);
            if (!m_inSuspendableOrFork) {
                // Suspendables reset __Vdlyvset__ in the AstAlwaysPost
                setinitp = new AstAssignPre{
                    nodep->fileline(), new AstVarRef{nodep->fileline(), setvscp, VAccess::WRITE},
                    new AstConst{nodep->fileline(), 0}};
            }
            AstAssign* const setassignp = new AstAssign{
                nodep->fileline(), new AstVarRef{nodep->fileline(), setvscp, VAccess::WRITE},
                new AstConst{nodep->fileline(), AstConst::BitTrue{}}};
            nodep->addNextHere(setassignp);
        }
        if (m_nextDlyp) {  // Tell next assigndly it can share the variable
            m_nextDlyp->user3p(setvscp);
        }
        //
        // Create ALWAYSPOST for delayed variable
        // We add all logic to the same block if it's for the same memory
        // This ensures that multiple assignments to the same memory will result
        // in correctly ordered code - the last assignment must be last.
        // It also has the nice side effect of assisting cache locality.
        varrefp->user2Inc();  // Do not generate a warning for the blocking assignment
                              // that uses this varref
        AstNodeExpr* selectsp = varrefp;
        for (int dimension = int(dimreadps.size()) - 1; dimension >= 0; --dimension) {
            selectsp = new AstArraySel{nodep->fileline(), selectsp, dimreadps[dimension]};
        }
        if (bitselp) {
            selectsp = new AstSel{nodep->fileline(), selectsp, bitreadp,
                                  bitselp->widthp()->cloneTreePure(false)};  // Always pure
        }
        // Build "IF (changeit) ...
        UINFO(9, "   For " << setvscp << endl);
        UINFO(9, "     & " << varrefp << endl);
        AstAlwaysPost* finalp = nullptr;
        if (m_inSuspendableOrFork) {
            finalp = m_vscpAux(varrefp->varScopep()).suspFinalp;
            if (!finalp) {
                FileLine* const flp = nodep->fileline();
                finalp = new AstAlwaysPost{flp, nullptr, nullptr};
                UINFO(9, "     Created " << finalp << endl);
                if (!m_procp->user3p()) {
                    AstActive* const newactp = createActive(varrefp);
                    m_procp->user3p(newactp);
                    m_vscpAux(varrefp->varScopep()).suspFinalp = finalp;
                }
                AstActive* const actp = VN_AS(m_procp->user3p(), Active);
                actp->addStmtsp(finalp);
            }
        } else {
            finalp = m_vscpAux(varrefp->varScopep()).finalp;
            if (finalp) {
                AstActive* const oldactivep = VN_AS(finalp->user2p(), Active);
                checkActivePost(varrefp, oldactivep);
                if (setinitp) oldactivep->addStmtsp(setinitp);
            } else {  // first time we've dealt with this memory
                finalp = new AstAlwaysPost{nodep->fileline(), nullptr /*sens*/, nullptr /*body*/};
                UINFO(9, "     Created " << finalp << endl);
                AstActive* const newactp = createActive(varrefp);
                newactp->addStmtsp(finalp);
                m_vscpAux(varrefp->varScopep()).finalp = finalp;
                finalp->user2p(newactp);
                if (setinitp) newactp->addStmtsp(setinitp);
            }
        }
        AstIf* postLogicp;
        if (finalp->user3p() == setvscp) {
            // Optimize as above; if sharing Vdlyvset *ON SAME VARIABLE*,
            // we can share the IF statement too
            postLogicp = VN_AS(finalp->user1p(), If);
            UASSERT_OBJ(postLogicp, nodep,
                        "Delayed assignment misoptimized; prev var found w/o associated IF");
        } else {
            postLogicp = new AstIf{nodep->fileline(),
                                   new AstVarRef{nodep->fileline(), setvscp, VAccess::READ}};
            UINFO(9, "     Created " << postLogicp << endl);
            finalp->addStmtsp(postLogicp);
            finalp->user3p(setvscp);  // Remember IF's vset variable
            finalp->user1p(postLogicp);  // and the associated IF, as we may be able to reuse it
        }
        postLogicp->addThensp(new AstAssign{nodep->fileline(), selectsp, valreadp});
        if (m_inSuspendableOrFork) {
            FileLine* const flp = nodep->fileline();
            postLogicp->addThensp(new AstAssign{flp, new AstVarRef{flp, setvscp, VAccess::WRITE},
                                                new AstConst{flp, 0}});
        }
        return newlhsp;
    }

    // VISITORS
    void visit(AstNetlist* nodep) override {
        // VV*****  We reset all userp() on the netlist
        m_modVarMap.clear();
        iterateChildren(nodep);
    }
    void visit(AstScope* nodep) override {
        UINFO(4, " MOD   " << nodep << endl);
        AstNode::user3ClearTree();
        iterateChildren(nodep);
    }
    void visit(AstCFunc* nodep) override {
        VL_RESTORER(m_cfuncp);
        m_cfuncp = nodep;
        iterateChildren(nodep);
    }
    void visit(AstActive* nodep) override {
        m_activep = nodep;
        VL_RESTORER(m_inInitial);
        {
            AstSenTree* const senTreep = nodep->sensesp();
            m_inInitial = senTreep->hasStatic() || senTreep->hasInitial();
            // Two sets to same variable in different actives must use different vars.
            AstNode::user3ClearTree();
            iterateChildren(nodep);
        }
    }
    void visit(AstNodeProcedure* nodep) override {
        VL_RESTORER(m_inSuspendableOrFork);
        m_inSuspendableOrFork = nodep->isSuspendable();
        {
            VL_RESTORER(m_procp);
            m_procp = nodep;
            m_timingDomains.clear();
            iterateChildren(nodep);
        }
        if (m_timingDomains.empty()) return;
        if (auto* const actp = VN_AS(nodep->user3p(), Active)) {
            // Merge all timing domains (and possibly the active's domain) to create a sentree for
            // the post logic
            // TODO: allow multiple sentrees per active, so we don't have to merge them and create
            // a new trigger
            auto* clockedDomain
                = actp->sensesp()->hasClocked() ? actp->sensesp()->cloneTree(false) : nullptr;
            for (auto* const domainp : m_timingDomains) {
                if (!clockedDomain) {
                    clockedDomain = domainp->cloneTree(false);
                } else {
                    clockedDomain->addSensesp(domainp->sensesp()->cloneTree(true));
                    clockedDomain->multi(true);  // Comment that it was made from multiple domains
                }
            }
            // We cannot constify the sentree using V3Const as user1-5 is already taken up by
            // V3Delayed
            actp->sensesp(clockedDomain);
            actp->sensesStorep(clockedDomain);
        }
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
            const string newvarname = string{"__Vdly__"} + vrefp->varp()->shortName();
            AstVarScope* const dlyvscp = createVarSc(vrefp->varScopep(), newvarname, 1, nullptr);

            const auto dlyRef = [=](VAccess access) {
                return new AstVarRef{flp, dlyvscp, access};
            };

            AstAssignPre* const prep = new AstAssignPre{flp, dlyRef(VAccess::WRITE),
                                                        new AstConst{flp, AstConst::BitFalse{}}};
            AstAlwaysPost* const postp = new AstAlwaysPost{flp, nullptr, nullptr};
            {
                AstIf* const ifp = new AstIf{flp, dlyRef(VAccess::READ)};
                postp->addStmtsp(ifp);
                AstCMethodHard* const callp = new AstCMethodHard{flp, vrefp, "fire"};
                callp->dtypeSetVoid();
                ifp->addThensp(callp->makeStmt());
            }

            AstActive* const activep = createActive(nodep);
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
        nodep->deleteTree();
    }
    void visit(AstAssignDly* nodep) override {
        VL_RESTORER(m_inDly);
        VL_RESTORER(m_nextDlyp);
        m_inDly = true;
        m_nextDlyp
            = VN_CAST(nodep->nextp(), AssignDly);  // Next assignment in same block, maybe nullptr.
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
        if (m_inSuspendableOrFork || isArray) {
            AstNodeExpr* const lhsp = nodep->lhsp();
            AstNodeExpr* const newlhsp = createDlyOnSet(nodep, lhsp);
            if (m_inLoop && isArray) {
                nodep->v3warn(BLKLOOPINIT, "Unsupported: Delayed assignment to array inside for "
                                           "loops (non-delayed is ok - see docs)");
            }
            const AstBasicDType* const basicp = lhsp->dtypep()->basicp();
            if (basicp && basicp->isEvent()) {
                nodep->v3warn(E_UNSUPPORTED, "Unsupported: event arrays");
            }
            if (newlhsp) {
                if (nodep->lhsp()) nodep->lhsp()->unlinkFrBack();
                nodep->lhsp(newlhsp);
            } else {
                VL_DO_DANGLING(pushDeletep(nodep->unlinkFrBack()), nodep);
            }
            if (!lhsp->backp()) VL_DO_DANGLING(pushDeletep(lhsp), lhsp);
        } else {
            iterate(nodep->lhsp());
            m_inDly = false;
            iterate(nodep->rhsp());
        }
    }

    void visit(AstVarRef* nodep) override {
        if (!nodep->user2Inc()) {  // Not done yet
            if (m_inDly && nodep->access().isWriteOrRW()) {
                UINFO(4, "AssignDlyVar: " << nodep << endl);
                markVarUsage(nodep, true);
                UASSERT_OBJ(m_activep, nodep, "<= not under sensitivity block");
                UASSERT_OBJ(!nodep->access().isRW(), nodep, "<= on read+write method");
                if (!m_activep->hasClocked()) {
                    nodep->v3error("Internal: Blocking <= assignment in non-clocked block, should "
                                   "have converted in V3Active");
                }
                AstVarScope* const oldvscp = nodep->varScopep();
                UASSERT_OBJ(oldvscp, nodep, "Var didn't get varscoped in V3Scope.cpp");
                AstVarScope* dlyvscp = m_vscpAux(oldvscp).delayVscp;
                if (dlyvscp) {  // Multiple use of delayed variable
                    AstActive* const oldactivep = m_vscpAux(dlyvscp).activep;
                    checkActivePost(nodep, oldactivep);
                } else {  // First use of this delayed variable
                    const string newvarname = string{"__Vdly__"} + nodep->varp()->shortName();
                    dlyvscp = createVarSc(oldvscp, newvarname, 0, nullptr);
                    AstNodeAssign* const prep = new AstAssignPre{
                        nodep->fileline(),
                        new AstVarRef{nodep->fileline(), dlyvscp, VAccess::WRITE},
                        new AstVarRef{nodep->fileline(), oldvscp, VAccess::READ}};
                    AstNodeAssign* const postp = new AstAssignPost{
                        nodep->fileline(),
                        new AstVarRef{nodep->fileline(), oldvscp, VAccess::WRITE},
                        new AstVarRef{nodep->fileline(), dlyvscp, VAccess::READ}};
                    postp->lhsp()->user2(true);  // Don't detect this assignment
                    m_vscpAux(oldvscp).delayVscp = dlyvscp;  // So we can find it later
                    // Make new ACTIVE with identical sensitivity tree
                    AstActive* const newactp = createActive(nodep);
                    m_vscpAux(dlyvscp).activep = newactp;
                    newactp->addStmtsp(prep);  // Add to FRONT of statements
                    newactp->addStmtsp(postp);
                }
                AstVarRef* const newrefp
                    = new AstVarRef{nodep->fileline(), dlyvscp, VAccess::WRITE};
                newrefp->user2(true);  // No reason to do it again
                nodep->replaceWith(newrefp);
                VL_DO_DANGLING(pushDeletep(nodep), nodep);
            } else if (!m_inDly && nodep->access().isWriteOrRW()) {
                // UINFO(9, "NBA " << nodep << endl);
                if (!m_inInitial) {
                    UINFO(4, "AssignNDlyVar: " << nodep << endl);
                    markVarUsage(nodep, false);
                }
            }
        }
    }

    void visit(AstNodeReadWriteMem* nodep) override {
        VL_RESTORER(m_ignoreBlkAndNBlk);
        m_ignoreBlkAndNBlk = true;  // $readmem/$writemem often used in mem models
        // so we will suppress BLKANDNBLK warnings
        iterateChildren(nodep);
    }

    void visit(AstNodeFor* nodep) override {  // LCOV_EXCL_LINE
        nodep->v3fatalSrc(
            "For statements should have been converted to while statements in V3Begin");
    }
    void visit(AstWhile* nodep) override {
        VL_RESTORER(m_inLoop);
        m_inLoop = true;
        iterateChildren(nodep);
    }
    void visit(AstExprStmt* nodep) override {
        VL_RESTORER(m_inDly);
        // Restoring is needed, because AstExprStmt may contain assignments
        m_inDly = false;
        iterateChildren(nodep);
    }

    //--------------------
    void visit(AstNode* nodep) override { iterateChildren(nodep); }

public:
    // CONSTRUCTORS
    explicit DelayedVisitor(AstNetlist* nodep) { iterate(nodep); }
    ~DelayedVisitor() override {
        V3Stats::addStat("Optimizations, Delayed shared-sets", m_statSharedSet);
    }
};

//######################################################################
// Delayed class functions

void V3Delayed::delayedAll(AstNetlist* nodep) {
    UINFO(2, __FUNCTION__ << ": " << endl);
    { DelayedVisitor{nodep}; }  // Destruct before checking
    V3Global::dumpCheckGlobalTree("delayed", 0, dumpTreeLevel() >= 3);
}
