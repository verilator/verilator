// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Collect and print statistics
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2005-2024 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#include "V3PchAstNoMT.h"  // VL_MT_DISABLED_CODE_UNIT

#include "V3Assert.h"

#include "V3Stats.h"

VL_DEFINE_DEBUG_FUNCTIONS;

//######################################################################
// Assert class functions

class AssertVisitor final : public VNVisitor {
    // TYPES
    enum assertType_e : uint8_t {
        ASSERT_TYPE_INTRINSIC,  // AstNodeAssertIntrinsinc
        ASSERT_TYPE_SVA,  // SVA, PSL
        ASSERT_TYPE_CASE,  // unique/unique0/priority case related checks
        ASSERT_TYPE_IF  // unique/unique0/priority if related checks
    };
    // NODE STATE/TYPES
    // Cleared on netlist
    //  AstNode::user()         -> bool.  True if processed
    const VNUser1InUse m_inuser1;

    // STATE
    AstNodeModule* m_modp = nullptr;  // Last module
    const AstBegin* m_beginp = nullptr;  // Last begin
    unsigned m_monitorNum = 0;  // Global $monitor numbering (not per module)
    AstVar* m_monitorNumVarp = nullptr;  // $monitor number variable
    AstVar* m_monitorOffVarp = nullptr;  // $monitoroff variable
    unsigned m_modPastNum = 0;  // Module past numbering
    unsigned m_modStrobeNum = 0;  // Module $strobe numbering
    const AstNodeProcedure* m_procedurep = nullptr;  // Current procedure
    VDouble0 m_statCover;  // Statistic tracking
    VDouble0 m_statAsNotImm;  // Statistic tracking
    VDouble0 m_statAsImm;  // Statistic tracking
    VDouble0 m_statAsFull;  // Statistic tracking
    bool m_inSampled = false;  // True inside a sampled expression

    // METHODS
    static bool assertTypeOn(assertType_e assertType) {
        if (assertType == ASSERT_TYPE_INTRINSIC) return true;
        if (v3Global.opt.assertOn()) return true;
        if (assertType == ASSERT_TYPE_CASE && v3Global.opt.assertCaseOn()) return true;
        return false;
    }
    string assertDisplayMessage(AstNode* nodep, const string& prefix, const string& message,
                                VDisplayType severity) {
        if (severity == VDisplayType::DT_ERROR || severity == VDisplayType::DT_FATAL) {
            return (string{"[%0t] " + prefix + ": "} + nodep->fileline()->filebasename() + ":"
                    + cvtToStr(nodep->fileline()->lineno()) + ": Assertion failed in %m"
                    + ((message != "") ? ": " : "") + message + "\n");
        } else {
            return (string{"[%0t] " + prefix + ": "} + nodep->fileline()->filebasename() + ":"
                    + cvtToStr(nodep->fileline()->lineno()) + ": %m"
                    + ((message != "") ? ": " : "") + message + "\n");
        }
    }
    void replaceDisplay(AstDisplay* nodep, const string& prefix) {
        nodep->fmtp()->text(
            assertDisplayMessage(nodep, prefix, nodep->fmtp()->text(), nodep->displayType()));
        nodep->displayType(VDisplayType::DT_WRITE);
        // cppcheck-suppress nullPointer
        AstNodeExpr* const timenewp = new AstTime{nodep->fileline(), m_modp->timeunit()};
        if (AstNodeExpr* const timesp = nodep->fmtp()->exprsp()) {
            timesp->unlinkFrBackWithNext();
            timenewp->addNext(timesp);
        }
        nodep->fmtp()->addExprsp(timenewp);
        if (!nodep->fmtp()->scopeNamep() && nodep->fmtp()->formatScopeTracking()) {
            nodep->fmtp()->scopeNamep(new AstScopeName{nodep->fileline(), true});
        }
    }
    AstSampled* newSampledExpr(AstNodeExpr* nodep) {
        const auto sampledp = new AstSampled{nodep->fileline(), nodep};
        sampledp->dtypeFrom(nodep);
        return sampledp;
    }
    AstVarRef* newMonitorNumVarRefp(AstNode* nodep, VAccess access) {
        if (!m_monitorNumVarp) {
            m_monitorNumVarp = new AstVar{nodep->fileline(), VVarType::MODULETEMP, "__VmonitorNum",
                                          nodep->findUInt64DType()};
            v3Global.rootp()->dollarUnitPkgAddp()->addStmtsp(m_monitorNumVarp);
        }
        const auto varrefp = new AstVarRef{nodep->fileline(), m_monitorNumVarp, access};
        varrefp->classOrPackagep(v3Global.rootp()->dollarUnitPkgAddp());
        return varrefp;
    }
    AstVarRef* newMonitorOffVarRefp(AstNode* nodep, VAccess access) {
        if (!m_monitorOffVarp) {
            m_monitorOffVarp = new AstVar{nodep->fileline(), VVarType::MODULETEMP, "__VmonitorOff",
                                          nodep->findBitDType()};
            v3Global.rootp()->dollarUnitPkgAddp()->addStmtsp(m_monitorOffVarp);
        }
        const auto varrefp = new AstVarRef{nodep->fileline(), m_monitorOffVarp, access};
        varrefp->classOrPackagep(v3Global.rootp()->dollarUnitPkgAddp());
        return varrefp;
    }
    AstNode* newIfAssertOn(AstNode* nodep, assertType_e assertType) {
        // Add a internal if to check assertions are on.
        // Don't make this a AND term, as it's unlikely to need to test this.
        FileLine* const fl = nodep->fileline();

        // If assertions are off, have constant propagation rip them out later
        // This allows syntax errors and such to be detected normally.
        AstNodeExpr* const condp
            = assertType == ASSERT_TYPE_INTRINSIC
                  ? static_cast<AstNodeExpr*>(new AstConst{fl, AstConst::BitTrue{}})
              : assertTypeOn(assertType)
                  ? static_cast<AstNodeExpr*>(
                      new AstCExpr{fl, "vlSymsp->_vm_contextp__->assertOn()", 1})
                  : static_cast<AstNodeExpr*>(new AstConst{fl, AstConst::BitFalse{}});
        AstNodeIf* const newp = new AstIf{fl, condp, nodep};
        newp->isBoundsCheck(true);  // To avoid LATCH warning
        newp->user1(true);  // Don't assert/cover this if
        return newp;
    }

    AstNode* newFireAssertUnchecked(AstNode* nodep, const string& message,
                                    AstNodeExpr* exprsp = nullptr) {
        // Like newFireAssert() but omits the asserts-on check
        AstDisplay* const dispp
            = new AstDisplay{nodep->fileline(), VDisplayType::DT_ERROR, message, nullptr, nullptr};
        dispp->fmtp()->timeunit(m_modp->timeunit());
        AstNode* const bodysp = dispp;
        replaceDisplay(dispp, "%%Error");  // Convert to standard DISPLAY format
        if (exprsp) dispp->fmtp()->exprsp()->addNext(exprsp);
        if (v3Global.opt.stopFail()) bodysp->addNext(new AstStop{nodep->fileline(), true});
        return bodysp;
    }

    AstNode* newFireAssert(AstNode* nodep, assertType_e assertType, const string& message,
                           AstNodeExpr* exprsp = nullptr) {
        AstNode* bodysp = newFireAssertUnchecked(nodep, message, exprsp);
        bodysp = newIfAssertOn(bodysp, assertType);
        return bodysp;
    }

    void newPslAssertion(AstNodeCoverOrAssert* nodep, AstNode* failsp) {
        if (m_beginp && nodep->name() == "") nodep->name(m_beginp->name());

        AstNodeExpr* const propp = VN_AS(nodep->propp()->unlinkFrBackWithNext(), NodeExpr);
        AstSenTree* const sentreep = nodep->sentreep();
        const string& message = nodep->name();
        AstNode* passsp = nodep->passsp();
        if (passsp) passsp->unlinkFrBackWithNext();
        if (failsp) failsp->unlinkFrBackWithNext();

        if (nodep->immediate()) {
            UASSERT_OBJ(!sentreep, nodep, "Immediate assertions don't have sensitivity");
        } else {
            UASSERT_OBJ(sentreep, nodep, "Concurrent assertions must have sensitivity");
            sentreep->unlinkFrBack();
            if (m_procedurep) {
                // To support this need queue of asserts to activate
                nodep->v3error("Unsupported: Procedural concurrent assertion with"
                               " clocking event inside always (IEEE 1800-2023 16.14.6)");
            }
        }
        //
        AstNode* bodysp = nullptr;
        bool selfDestruct = false;
        AstIf* ifp = nullptr;
        if (const AstCover* const snodep = VN_CAST(nodep, Cover)) {
            ++m_statCover;
            if (!v3Global.opt.coverageUser()) {
                selfDestruct = true;
            } else {
                // V3Coverage assigned us a bucket to increment.
                AstCoverInc* const covincp = VN_AS(snodep->coverincsp(), CoverInc);
                UASSERT_OBJ(covincp, snodep, "Missing AstCoverInc under assertion");
                covincp->unlinkFrBackWithNext();  // next() might have  AstAssign for trace
                if (message != "") covincp->declp()->comment(message);
                bodysp = covincp;
            }

            if (bodysp && passsp) bodysp = bodysp->addNext(passsp);
            ifp = new AstIf{nodep->fileline(), propp, bodysp};
            ifp->isBoundsCheck(true);  // To avoid LATCH warning
            bodysp = ifp;
        } else if (VN_IS(nodep, Assert) || VN_IS(nodep, AssertIntrinsic)) {
            if (nodep->immediate()) {
                ++m_statAsImm;
            } else {
                ++m_statAsNotImm;
            }
            const assertType_e assertType
                = VN_IS(nodep, AssertIntrinsic) ? ASSERT_TYPE_INTRINSIC : ASSERT_TYPE_SVA;
            if (passsp) passsp = newIfAssertOn(passsp, assertType);
            if (failsp) failsp = newIfAssertOn(failsp, assertType);
            if (!passsp && !failsp) failsp = newFireAssertUnchecked(nodep, "'assert' failed.");
            ifp = new AstIf{nodep->fileline(), propp, passsp, failsp};
            ifp->isBoundsCheck(true);  // To avoid LATCH warning
            // It's more LIKELY that we'll take the nullptr if clause
            // than the sim-killing else clause:
            ifp->branchPred(VBranchPred::BP_LIKELY);
            bodysp = newIfAssertOn(ifp, assertType);
        } else {
            nodep->v3fatalSrc("Unknown node type");
        }

        AstNode* newp;
        if (sentreep) {
            newp = new AstAlways{nodep->fileline(), VAlwaysKwd::ALWAYS, sentreep, bodysp};
        } else {
            newp = bodysp;
        }
        // Install it
        if (selfDestruct) {
            // Delete it after making the tree.  This way we can tell the user
            // if it wasn't constructed nicely or has other errors without needing --coverage.
            VL_DO_DANGLING(newp->deleteTree(), newp);
            nodep->unlinkFrBack();
        } else {
            nodep->replaceWith(newp);
        }
        // Bye
        VL_DO_DANGLING(pushDeletep(nodep), nodep);
    }

    // VISITORS
    void visit(AstIf* nodep) override {
        if (nodep->user1SetOnce()) return;
        if (nodep->uniquePragma() || nodep->unique0Pragma()) {
            const AstNodeIf* ifp = nodep;
            AstNodeExpr* propp = nullptr;
            bool hasDefaultElse = false;
            do {
                // If this statement ends with 'else if', then nextIf will point to the
                // nextIf statement.  Otherwise it will be null.
                const AstNodeIf* const nextifp = dynamic_cast<AstNodeIf*>(ifp->elsesp());
                iterateAndNextNull(ifp->condp());

                // Recurse into the true case.
                iterateAndNextNull(ifp->thensp());

                // If the last else is not an else if, recurse into that too.
                if (ifp->elsesp() && !nextifp) {  //
                    iterateAndNextNull(ifp->elsesp());
                }

                // Build a bitmask of the true predicates
                AstNodeExpr* const predp = ifp->condp()->cloneTreePure(false);
                if (propp) {
                    propp = new AstConcat{nodep->fileline(), predp, propp};
                } else {
                    propp = predp;
                }

                // Record if this ends with an 'else' that does not have an if
                if (ifp->elsesp() && !nextifp) hasDefaultElse = true;

                ifp = nextifp;
            } while (ifp);

            AstIf* const newifp = nodep->cloneTree(false);
            const bool allow_none = nodep->unique0Pragma();

            // Empty case means no property
            if (!propp) propp = new AstConst{nodep->fileline(), AstConst::BitFalse{}};

            // Note: if this ends with an 'else', then we don't need to validate that one of the
            // predicates evaluates to true.
            AstNodeExpr* const ohot
                = ((allow_none || hasDefaultElse)
                       ? static_cast<AstNodeExpr*>(new AstOneHot0{nodep->fileline(), propp})
                       : static_cast<AstNodeExpr*>(new AstOneHot{nodep->fileline(), propp}));
            AstIf* const checkifp = new AstIf{
                nodep->fileline(), new AstLogNot{nodep->fileline(), ohot},
                newFireAssert(nodep, ASSERT_TYPE_IF, "'unique if' statement violated"), newifp};
            checkifp->isBoundsCheck(true);  // To avoid LATCH warning
            checkifp->branchPred(VBranchPred::BP_UNLIKELY);
            nodep->replaceWith(checkifp);
            pushDeletep(nodep);
        } else {
            iterateChildren(nodep);
        }
    }

    //========== Case assertions
    void visit(AstCase* nodep) override {
        iterateChildren(nodep);
        if (!nodep->user1SetOnce()) {
            bool has_default = false;
            for (AstCaseItem* itemp = nodep->itemsp(); itemp;
                 itemp = VN_AS(itemp->nextp(), CaseItem)) {
                if (itemp->isDefault()) has_default = true;
            }
            const AstNodeDType* exprDtypep = nodep->exprp()->dtypep()->skipRefp();
            string valFmt;
            if (exprDtypep->isIntegralOrPacked())
                valFmt = " for '" + cvtToStr(exprDtypep->widthMin()) + "'h%X'";
            if (nodep->fullPragma() || nodep->priorityPragma()) {
                // Need to add a default if there isn't one already
                ++m_statAsFull;
                if (!has_default) {
                    nodep->addItemsp(new AstCaseItem{
                        nodep->fileline(), nullptr /*DEFAULT*/,
                        newFireAssert(nodep, ASSERT_TYPE_CASE,
                                      nodep->pragmaString() + ", but non-match found" + valFmt,
                                      valFmt.empty() ? nullptr
                                                     : nodep->exprp()->cloneTreePure(false))});
                }
            }
            if (nodep->parallelPragma() || nodep->uniquePragma() || nodep->unique0Pragma()) {
                // Need to check that one, and only one of the case items match at any moment
                // If there's a default, we allow none to match, else exactly one must match
                ++m_statAsFull;
                if (!has_default && !nodep->itemsp()) {
                    // Not parallel, but harmlessly so.
                } else {
                    AstNodeExpr* propp = nullptr;
                    for (AstCaseItem* itemp = nodep->itemsp(); itemp;
                         itemp = VN_AS(itemp->nextp(), CaseItem)) {
                        for (AstNodeExpr* icondp = itemp->condsp(); icondp;
                             icondp = VN_AS(icondp->nextp(), NodeExpr)) {
                            AstNodeExpr* onep;
                            if (AstInsideRange* const rcondp = VN_CAST(icondp, InsideRange)) {
                                onep = rcondp->newAndFromInside(
                                    nodep->exprp(), rcondp->lhsp()->cloneTreePure(true),
                                    rcondp->rhsp()->cloneTreePure(true));
                            } else if (nodep->casex() || nodep->casez() || nodep->caseInside()) {
                                onep = AstEqWild::newTyped(itemp->fileline(),
                                                           nodep->exprp()->cloneTreePure(false),
                                                           icondp->cloneTreePure(false));
                            } else {
                                onep = AstEq::newTyped(icondp->fileline(),
                                                       nodep->exprp()->cloneTreePure(false),
                                                       icondp->cloneTreePure(false));
                            }
                            if (propp) {
                                propp = new AstConcat{icondp->fileline(), onep, propp};
                            } else {
                                propp = onep;
                            }
                        }
                    }
                    // Empty case means no property
                    if (!propp) propp = new AstConst{nodep->fileline(), AstConst::BitFalse{}};
                    const bool allow_none = has_default || nodep->unique0Pragma();
                    // The following assertion lools as below.
                    // if (!$onehot(propp)) begin
                    //     if (propp == '0) begin if (!allow_none) $error("none match"); end
                    //     else $error("multiple match");
                    // end
                    AstNodeExpr* const ohot = new AstOneHot{nodep->fileline(), propp};
                    AstIf* const ohotIfp
                        = new AstIf{nodep->fileline(), new AstLogNot{nodep->fileline(), ohot}};
                    AstIf* const zeroIfp
                        = new AstIf{nodep->fileline(),
                                    new AstLogNot{nodep->fileline(), propp->cloneTreePure(false)}};
                    AstNodeExpr* const exprp = nodep->exprp();
                    const string pragmaStr = nodep->pragmaString();
                    if (!allow_none)
                        zeroIfp->addThensp(newFireAssert(
                            nodep, ASSERT_TYPE_CASE, pragmaStr + ", but none matched" + valFmt,
                            valFmt.empty() ? nullptr : exprp->cloneTreePure(false)));
                    zeroIfp->addElsesp(
                        newFireAssert(nodep, ASSERT_TYPE_CASE,
                                      pragmaStr + ", but multiple matches found" + valFmt,
                                      valFmt.empty() ? nullptr : exprp->cloneTreePure(false)));
                    ohotIfp->addThensp(zeroIfp);
                    ohotIfp->isBoundsCheck(true);  // To avoid LATCH warning
                    ohotIfp->branchPred(VBranchPred::BP_UNLIKELY);
                    nodep->addNotParallelp(ohotIfp);
                }
            }
        }
    }

    //========== Past
    void visit(AstPast* nodep) override {
        iterateChildren(nodep);
        uint32_t ticks = 1;
        if (nodep->ticksp()) {
            UASSERT_OBJ(VN_IS(nodep->ticksp(), Const), nodep,
                        "Expected constant ticks, checked in V3Width");
            ticks = VN_AS(nodep->ticksp(), Const)->toUInt();
        }
        UASSERT_OBJ(ticks >= 1, nodep, "0 tick should have been checked in V3Width");
        AstNodeExpr* const exprp = nodep->exprp()->unlinkFrBack();
        AstNodeExpr* inp = newSampledExpr(exprp);
        AstVar* invarp = nullptr;
        AstSenTree* const sentreep = nodep->sentreep()->unlinkFrBack();
        AstAlways* const alwaysp
            = new AstAlways{nodep->fileline(), VAlwaysKwd::ALWAYS, sentreep, nullptr};
        m_modp->addStmtsp(alwaysp);
        for (uint32_t i = 0; i < ticks; ++i) {
            AstVar* const outvarp = new AstVar{
                nodep->fileline(), VVarType::MODULETEMP,
                "_Vpast_" + cvtToStr(m_modPastNum++) + "_" + cvtToStr(i), inp->dtypep()};
            m_modp->addStmtsp(outvarp);
            AstNode* const assp = new AstAssignDly{
                nodep->fileline(), new AstVarRef{nodep->fileline(), outvarp, VAccess::WRITE}, inp};
            alwaysp->addStmtsp(assp);
            // if (debug() >= 9) assp->dumpTree("-  ass: ");
            invarp = outvarp;
            inp = new AstVarRef{nodep->fileline(), invarp, VAccess::READ};
        }
        nodep->replaceWith(inp);
        VL_DO_DANGLING(pushDeletep(nodep), nodep);
    }

    //========== Move $sampled down to read-only variables
    void visit(AstSampled* nodep) override {
        if (nodep->user1()) return;
        VL_RESTORER(m_inSampled);
        {
            m_inSampled = true;
            iterateChildren(nodep);
        }
        nodep->replaceWith(nodep->exprp()->unlinkFrBack());
        VL_DO_DANGLING(pushDeletep(nodep), nodep);
    }
    void visit(AstVarRef* nodep) override {
        iterateChildren(nodep);
        if (m_inSampled) {
            if (!nodep->access().isReadOnly()) {
                nodep->v3warn(E_UNSUPPORTED,
                              "Unsupported: Write to variable in sampled expression");
            } else {
                VNRelinker relinkHandle;
                nodep->unlinkFrBack(&relinkHandle);
                AstSampled* const newp = newSampledExpr(nodep);
                relinkHandle.relink(newp);
                newp->user1(1);
            }
        }
    }
    // Don't sample sensitivities
    void visit(AstSenItem* nodep) override {
        VL_RESTORER(m_inSampled);
        {
            m_inSampled = false;
            iterateChildren(nodep);
        }
    }

    //========== Statements
    void visit(AstDisplay* nodep) override {
        iterateChildren(nodep);
        // Replace the special types with standard text
        if (nodep->displayType() == VDisplayType::DT_INFO) {
            replaceDisplay(nodep, "-Info");
        } else if (nodep->displayType() == VDisplayType::DT_WARNING) {
            replaceDisplay(nodep, "%%Warning");
        } else if (nodep->displayType() == VDisplayType::DT_ERROR) {
            replaceDisplay(nodep, "%%Error");
        } else if (nodep->displayType() == VDisplayType::DT_FATAL) {
            replaceDisplay(nodep, "%%Fatal");
        } else if (nodep->displayType() == VDisplayType::DT_MONITOR) {
            nodep->displayType(VDisplayType::DT_DISPLAY);
            const auto fl = nodep->fileline();
            const auto monNum = ++m_monitorNum;
            // Where $monitor was we do "__VmonitorNum = N;"
            const auto newsetp = new AstAssign{fl, newMonitorNumVarRefp(nodep, VAccess::WRITE),
                                               new AstConst{fl, monNum}};
            nodep->replaceWith(newsetp);
            // Add "always_comb if (__VmonitorOn && __VmonitorNum==N) $display(...);"
            AstNode* const stmtsp = nodep;
            AstIf* const ifp = new AstIf{
                fl,
                new AstLogAnd{fl, new AstLogNot{fl, newMonitorOffVarRefp(nodep, VAccess::READ)},
                              new AstEq{fl, new AstConst{fl, monNum},
                                        newMonitorNumVarRefp(nodep, VAccess::READ)}},
                stmtsp};
            ifp->isBoundsCheck(true);  // To avoid LATCH warning
            ifp->branchPred(VBranchPred::BP_UNLIKELY);
            AstNode* const newp = new AstAlways{fl, VAlwaysKwd::ALWAYS, nullptr, ifp};
            m_modp->addStmtsp(newp);
        } else if (nodep->displayType() == VDisplayType::DT_STROBE) {
            nodep->displayType(VDisplayType::DT_DISPLAY);
            // Need one-shot
            const auto fl = nodep->fileline();
            const auto varp
                = new AstVar{fl, VVarType::MODULETEMP, "__Vstrobe" + cvtToStr(m_modStrobeNum++),
                             nodep->findBitDType()};
            m_modp->addStmtsp(varp);
            // Where $strobe was we do "__Vstrobe = '1;"
            const auto newsetp = new AstAssign{fl, new AstVarRef{fl, varp, VAccess::WRITE},
                                               new AstConst{fl, AstConst::BitTrue{}}};
            nodep->replaceWith(newsetp);
            // Add "always_comb if (__Vstrobe) begin $display(...); __Vstrobe = '0; end"
            AstNode* const stmtsp = nodep;
            AstIf* const ifp = new AstIf{fl, new AstVarRef{fl, varp, VAccess::READ}, stmtsp};
            ifp->isBoundsCheck(true);  // To avoid LATCH warning
            ifp->branchPred(VBranchPred::BP_UNLIKELY);
            AstNode* const newp = new AstAlwaysPostponed{fl, ifp};
            stmtsp->addNext(new AstAssign{fl, new AstVarRef{fl, varp, VAccess::WRITE},
                                          new AstConst{fl, AstConst::BitFalse{}}});
            m_modp->addStmtsp(newp);
        }
    }
    void visit(AstMonitorOff* nodep) override {
        const auto newp
            = new AstAssign{nodep->fileline(), newMonitorOffVarRefp(nodep, VAccess::WRITE),
                            new AstConst{nodep->fileline(), AstConst::BitTrue{}, nodep->off()}};
        nodep->replaceWith(newp);
        VL_DO_DANGLING(pushDeletep(nodep), nodep);
    }
    void visit(AstAssert* nodep) override {
        iterateChildren(nodep);
        newPslAssertion(nodep, nodep->failsp());
    }
    void visit(AstAssertIntrinsic* nodep) override {
        iterateChildren(nodep);
        newPslAssertion(nodep, nodep->failsp());
    }
    void visit(AstCover* nodep) override {
        iterateChildren(nodep);
        newPslAssertion(nodep, nullptr);
    }
    void visit(AstRestrict* nodep) override {
        iterateChildren(nodep);
        // IEEE says simulator ignores these
        VL_DO_DANGLING(pushDeletep(nodep->unlinkFrBack()), nodep);
    }

    void visit(AstNodeModule* nodep) override {
        VL_RESTORER(m_modp);
        VL_RESTORER(m_modPastNum);
        VL_RESTORER(m_modStrobeNum);
        {
            m_modp = nodep;
            m_modPastNum = 0;
            m_modStrobeNum = 0;
            iterateChildren(nodep);
        }
    }
    void visit(AstNodeProcedure* nodep) override {
        VL_RESTORER(m_procedurep);
        m_procedurep = nodep;
        iterateChildren(nodep);
    }
    void visit(AstBegin* nodep) override {
        // This code is needed rather than a visitor in V3Begin,
        // because V3Assert is called before V3Begin
        VL_RESTORER(m_beginp);
        {
            m_beginp = nodep;
            iterateChildren(nodep);
        }
    }

    void visit(AstNode* nodep) override { iterateChildren(nodep); }

public:
    // CONSTRUCTORS
    explicit AssertVisitor(AstNetlist* nodep) { iterate(nodep); }
    ~AssertVisitor() override {
        V3Stats::addStat("Assertions, assert non-immediate statements", m_statAsNotImm);
        V3Stats::addStat("Assertions, assert immediate statements", m_statAsImm);
        V3Stats::addStat("Assertions, cover statements", m_statCover);
        V3Stats::addStat("Assertions, full/parallel case", m_statAsFull);
    }
};

//######################################################################
// Top Assert class

void V3Assert::assertAll(AstNetlist* nodep) {
    UINFO(2, __FUNCTION__ << ": " << endl);
    { AssertVisitor{nodep}; }  // Destruct before checking
    V3Global::dumpCheckGlobalTree("assert", 0, dumpTreeEitherLevel() >= 3);
}
