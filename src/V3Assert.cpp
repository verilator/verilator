// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Collect and print statistics
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2005-2026 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#include "V3PchAstNoMT.h"  // VL_MT_DISABLED_CODE_UNIT

#include "V3Assert.h"

#include "V3AstUserAllocator.h"
#include "V3Stats.h"

VL_DEFINE_DEBUG_FUNCTIONS;

//######################################################################
// AssertDeFutureVisitor
// If any AstFuture, then move all non-future varrefs to be one cycle behind,
// see IEEE 1800-2023 16.9.4.

class AssertDeFutureVisitor final : public VNVisitor {
    // STATE - across all visitors
    AstNodeModule* const m_modp;  // Module future is underneath
    const AstFuture* m_futurep;  // First AstFuture found
    const unsigned m_pastNum;  // Prefix unique number for this module
    std::map<AstVar*, AstVar*> m_delayedVars;  // Old to delayed variable mapping
    // STATE - for current visit position (use VL_RESTORER)
    bool m_inFuture = false;  // Inside a future
    bool m_unsupported = false;  // Printed unsupported

    // METHODS
    void unsupported(AstNode* nodep) {
        if (m_unsupported) return;
        m_unsupported = true;
        nodep->v3warn(E_UNSUPPORTED,
                      "Unsupported/illegal: Future value function used with expression with "
                          << nodep->prettyOperatorName());
    }
    // VISITORS
    void visit(AstFuture* nodep) override {
        VL_RESTORER(m_inFuture);
        m_inFuture = true;
        iterateChildren(nodep);
        // Done with the future, this subexpression is current-time
        nodep->replaceWith(nodep->exprp()->unlinkFrBack());
        VL_DO_DANGLING(pushDeletep(nodep), nodep);
    }
    void visit(AstNodeVarRef* nodep) override {
        if (nodep->user1SetOnce()) return;
        if (m_inFuture || m_unsupported)
            return;  // Need user1 set above, don't process when Future is removed
        if (nodep->access().isWriteOrRW()) {
            unsupported(nodep);
            return;
        }
        auto it = m_delayedVars.find(nodep->varp());
        AstVar* outvarp;
        if (it == m_delayedVars.end()) {
            AstSenTree* const sentreep = m_futurep->sentreep();
            AstAlways* const alwaysp = new AstAlways{nodep->fileline(), VAlwaysKwd::ALWAYS,
                                                     sentreep->cloneTree(false), nullptr};
            m_modp->addStmtsp(alwaysp);
            outvarp = new AstVar{nodep->fileline(), VVarType::MODULETEMP,
                                 "__Vnotfuture" + cvtToStr(m_pastNum) + "_" + nodep->name(),
                                 nodep->dtypep()};
            m_modp->addStmtsp(outvarp);
            AstVarRef* varRefAWritep = new AstVarRef{nodep->fileline(), outvarp, VAccess::WRITE};
            varRefAWritep->user1(true);
            AstNodeVarRef* varRefAReadp = nodep->cloneTree(false);
            varRefAReadp->user1(true);
            AstNode* const assp = new AstAssignDly{nodep->fileline(), varRefAWritep, varRefAReadp};
            alwaysp->addStmtsp(assp);
            m_delayedVars.emplace(nodep->varp(), outvarp);
        } else {
            outvarp = it->second;
        }
        AstVarRef* newp = new AstVarRef{nodep->fileline(), outvarp, VAccess::READ};
        newp->user1(true);
        UINFO(9, "DeFuture " << nodep << "  becomes " << newp);
        nodep->replaceWith(newp);
        VL_DO_DANGLING(pushDeletep(nodep), nodep);
    }
    void visit(AstNodeFTaskRef* nodep) override { unsupported(nodep); }
    void visit(AstMethodCall* nodep) override { unsupported(nodep); }
    void visit(AstNode* nodep) override {
        if (!nodep->isPure()) unsupported(nodep);
        iterateChildren(nodep);
    }

public:
    // CONSTRUCTORS
    explicit AssertDeFutureVisitor(AstNode* nodep, AstNodeModule* modp, unsigned pastNum)
        : m_modp{modp}
        , m_pastNum{pastNum} {
        // See if any Future before we process
        if (nodep->forall([&](const AstFuture* futurep) -> bool {
                m_futurep = futurep;
                return false;
            }))
            return;
        // UINFOTREE(9, nodep, "", "defuture-in");
        visit(nodep);  // Nodep may get deleted
        // UINFOTREE(9, nodep, "", "defuture-ou");
    }
    ~AssertDeFutureVisitor() = default;
};

//######################################################################
// AssertVisitor

class AssertVisitor final : public VNVisitor {
    // CONSTANTS
    static constexpr uint8_t ALL_ASSERT_TYPES
        = std::numeric_limits<std::underlying_type<VAssertType::en>::type>::max();

    // NODE STATE/TYPES
    // Cleared on netlist
    //  AstNode::user1()         -> bool.  True if processed
    //  AstAlways::user2p()      -> std::vector<AstVar*>. Delayed variables via 'm_delayed'
    const VNUser1InUse m_user1InUse;
    const VNUser2InUse m_user2InUse;
    AstUser2Allocator<AstAlways, std::vector<AstVar*>> m_delayed;

    // STATE
    AstNodeModule* m_modp = nullptr;  // Last module
    const AstNode* m_beginp = nullptr;  // Last AstBegin/AstGenBlock
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
    VDouble0 m_statPastVars;  // Statistic tracking
    bool m_inSampled = false;  // True inside a sampled expression
    bool m_inRestrict = false;  // True inside restrict assertion
    AstNode* m_passsp = nullptr;  // Current pass statement
    AstNode* m_failsp = nullptr;  // Current fail statement
    bool m_underAssert = false;  // Visited from assert
    // Map from (expression, senTree) to AstAlways that computes delayed values of the expression
    std::unordered_map<VNRef<AstNodeExpr>, std::unordered_map<VNRef<AstSenTree>, AstAlways*>>
        m_modExpr2Sen2DelayedAlwaysp;

    // METHODS
    static AstNodeExpr* assertOnCond(FileLine* fl, VAssertType type,
                                     VAssertDirectiveType directiveType) {
        // cppcheck-suppress missingReturn
        switch (directiveType) {
        case VAssertDirectiveType::INTRINSIC: return new AstConst{fl, AstConst::BitTrue{}};
        case VAssertDirectiveType::VIOLATION_CASE: {
            if (v3Global.opt.assertCase()) {
                return new AstCExpr{fl, AstCExpr::Pure{}, "vlSymsp->_vm_contextp__->assertOn()",
                                    1};
            }
            // If assertions are off, have constant propagation rip them out later
            // This allows syntax errors and such to be detected normally.
            return new AstConst{fl, AstConst::BitFalse{}};
        }
        case VAssertDirectiveType::ASSERT:
        case VAssertDirectiveType::COVER:
        case VAssertDirectiveType::ASSUME: {
            if (v3Global.opt.assertOn()) {
                return new AstCExpr{fl, AstCExpr::Pure{},
                                    "vlSymsp->_vm_contextp__->assertOnGet("s + std::to_string(type)
                                        + ", "s + std::to_string(directiveType) + ")"s,
                                    1};
            }
            return new AstConst{fl, AstConst::BitFalse{}};
        }
        case VAssertDirectiveType::INTERNAL:
        case VAssertDirectiveType::VIOLATION_IF:
        case VAssertDirectiveType::RESTRICT: {
            if (v3Global.opt.assertOn()) {
                return new AstCExpr{fl, AstCExpr::Pure{}, "vlSymsp->_vm_contextp__->assertOn()",
                                    1};
            }
            return new AstConst{fl, AstConst::BitFalse{}};
        }
        }
        VL_UNREACHABLE;
    }
    string assertDisplayMessage(const AstNode* nodep, const string& prefix, const string& message,
                                VDisplayType severity) {
        if (severity == VDisplayType::DT_ERROR || severity == VDisplayType::DT_FATAL) {
            return ("[%0t] "s + prefix + ": " + nodep->fileline()->filebasename() + ":"
                    + cvtToStr(nodep->fileline()->lineno()) + ": Assertion failed in %m"
                    + ((message != "") ? ": " : "") + message + "\n");
        } else {
            return ("[%0t] "s + prefix + ": " + nodep->fileline()->filebasename() + ":"
                    + cvtToStr(nodep->fileline()->lineno()) + ": %m"
                    + ((message != "") ? ": " : "") + message + "\n");
        }
    }
    static bool resolveAssertType(AstAssertCtl* nodep) {
        if (!nodep->assertTypesp()) {
            nodep->ctlAssertTypes(VAssertType{ALL_ASSERT_TYPES});
            return true;
        }
        if (const AstConst* const assertTypesp = VN_CAST(nodep->assertTypesp(), Const)) {
            nodep->ctlAssertTypes(VAssertType{assertTypesp->toSInt()});
            return true;
        }
        return false;
    }
    static bool resolveControlType(AstAssertCtl* nodep) {
        if (const AstConst* const constp = VN_CAST(nodep->controlTypep(), Const)) {
            nodep->ctlType(constp->toSInt());
            return true;
        }
        return false;
    }
    static bool resolveDirectiveType(AstAssertCtl* nodep) {
        if (!nodep->directiveTypesp()) {
            nodep->ctlDirectiveTypes(VAssertDirectiveType::ASSERT | VAssertDirectiveType::ASSUME
                                     | VAssertDirectiveType::COVER);
            return true;
        }
        if (const AstConst* const directiveTypesp = VN_CAST(nodep->directiveTypesp(), Const)) {
            nodep->ctlDirectiveTypes(VAssertDirectiveType{directiveTypesp->toSInt()});
            return true;
        }
        return false;
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
        AstSampled* const sampledp = new AstSampled{nodep->fileline(), nodep};
        sampledp->dtypeFrom(nodep);
        return sampledp;
    }
    AstVarRef* newMonitorNumVarRefp(const AstNode* nodep, VAccess access) {
        if (!m_monitorNumVarp) {
            m_monitorNumVarp = new AstVar{nodep->fileline(), VVarType::MODULETEMP, "__VmonitorNum",
                                          nodep->findUInt64DType()};
            v3Global.rootp()->dollarUnitPkgAddp()->addStmtsp(m_monitorNumVarp);
        }
        AstVarRef* const varrefp = new AstVarRef{nodep->fileline(), m_monitorNumVarp, access};
        varrefp->classOrPackagep(v3Global.rootp()->dollarUnitPkgAddp());
        return varrefp;
    }
    AstVarRef* newMonitorOffVarRefp(const AstNode* nodep, VAccess access) {
        if (!m_monitorOffVarp) {
            m_monitorOffVarp = new AstVar{nodep->fileline(), VVarType::MODULETEMP, "__VmonitorOff",
                                          nodep->findBitDType()};
            v3Global.rootp()->dollarUnitPkgAddp()->addStmtsp(m_monitorOffVarp);
        }
        AstVarRef* const varrefp = new AstVarRef{nodep->fileline(), m_monitorOffVarp, access};
        varrefp->classOrPackagep(v3Global.rootp()->dollarUnitPkgAddp());
        return varrefp;
    }
    static AstNodeStmt* newIfAssertOn(AstNode* bodyp, VAssertDirectiveType directiveType,
                                      VAssertType type = VAssertType::INTERNAL) {
        // Add a internal if to check assertions are on.
        // Don't make this a AND term, as it's unlikely to need to test this.
        FileLine* const fl = bodyp->fileline();

        AstNodeExpr* const condp = assertOnCond(fl, type, directiveType);
        AstNodeIf* const newp = new AstIf{fl, condp, bodyp};
        newp->isBoundsCheck(true);  // To avoid LATCH warning
        newp->user1(true);  // Don't assert/cover this if
        return newp;
    }

    static AstIf* assertCond(const AstNodeCoverOrAssert* nodep, AstNodeExpr* propp,
                             AstNode* passsp, AstNode* failsp) {
        AstIf* const ifp = new AstIf{nodep->fileline(), propp, passsp, failsp};
        // It's more LIKELY that we'll take the nullptr if clause
        // than the sim-killing else clause:
        ifp->branchPred(VBranchPred::BP_LIKELY);
        ifp->isBoundsCheck(true);  // To avoid LATCH warning
        return ifp;
    }

    AstNode* assertBody(const AstNodeCoverOrAssert* nodep, AstNode* propp, AstNode* passsp,
                        AstNode* failsp) {
        AstNode* bodyp = nullptr;
        if (AstPExpr* const pexprp = VN_CAST(propp, PExpr)) {
            AstFork* const forkp = new AstFork{nodep->fileline(), VJoinType::JOIN_NONE};
            forkp->addForksp(pexprp->bodyp()->unlinkFrBack());
            VL_DO_DANGLING2(pushDeletep(pexprp), pexprp, propp);
            bodyp = forkp;
        } else {
            bodyp = assertCond(nodep, VN_AS(propp, NodeExpr), passsp, failsp);
        }
        return newIfAssertOn(bodyp, nodep->directive(), nodep->type());
    }

    AstNodeStmt* newFireAssertUnchecked(const AstNodeStmt* nodep, const string& message,
                                        AstNodeExpr* exprsp = nullptr) {
        // Like newFireAssert() but omits the asserts-on check
        AstDisplay* const dispp
            = new AstDisplay{nodep->fileline(), VDisplayType::DT_ERROR, message, nullptr, nullptr};
        dispp->fmtp()->timeunit(m_modp->timeunit());
        AstNodeStmt* const bodysp = dispp;
        replaceDisplay(dispp, "%%Error");  // Convert to standard DISPLAY format
        if (exprsp) dispp->fmtp()->exprsp()->addNext(exprsp);
        if (v3Global.opt.stopFail()) bodysp->addNext(new AstStop{nodep->fileline(), false});
        return bodysp;
    }

    AstNodeStmt* newFireAssert(const AstNodeStmt* nodep, VAssertDirectiveType directiveType,
                               VAssertType assertType, const string& message,
                               AstNodeExpr* exprsp = nullptr) {
        AstNodeStmt* bodysp = newFireAssertUnchecked(nodep, message, exprsp);
        bodysp = newIfAssertOn(bodysp, directiveType, assertType);
        return bodysp;
    }

    AstVar* createDelayedVar(const std::string& name, AstAlways* alwaysp, AstNodeExpr* exprp) {
        FileLine* const flp = exprp->fileline();
        AstVar* const varp = new AstVar{flp, VVarType::MODULETEMP, name, exprp->dtypep()};
        // TODO: this lifetime seems nonsene (can't have NBAs to automatics), but is as before
        varp->lifetime(VLifetime::AUTOMATIC_EXPLICIT);
        m_modp->addStmtsp(varp);
        ++m_statPastVars;
        // Actually set the delayed value
        AstNodeExpr* const lhsp = new AstVarRef{flp, varp, VAccess::WRITE};
        AstAssignDly* const assignp = new AstAssignDly{flp, lhsp, exprp};
        if (!alwaysp->stmtsp()) {
            alwaysp->addStmtsp(assignp);
        } else {
            alwaysp->stmtsp()->addHereThisAsNext(assignp);
        }
        return varp;
    }

    AstAlways* getDelayedAlways(AstNodeExpr* exprp, AstSenTree* senTreep) {
        AstAlways*& alwayspr = m_modExpr2Sen2DelayedAlwaysp[*exprp][*senTreep];
        if (!alwayspr) {
            FileLine* const flp = exprp->fileline();
            // Create the always block that computes the delayed values
            alwayspr = new AstAlways{flp, VAlwaysKwd::ALWAYS, senTreep, nullptr};
            m_modp->addStmtsp(alwayspr);
            // Create the once-delayed variable
            const std::string name = "_Vpast_" + cvtToStr(m_modPastNum++) + "_1";
            AstVar* const varp = createDelayedVar(name, alwayspr, exprp);
            // Add it to delayed variable vector
            m_delayed(alwayspr).emplace_back(varp);
        } else {
            // Reusing exiting, not needed
            VL_DO_DANGLING(pushDeletep(exprp), exprp);
            VL_DO_DANGLING(pushDeletep(senTreep), senTreep);
        }
        return alwayspr;
    }

    AstNodeExpr* getPastValue(AstNodeExpr* exprp, AstSenTree* senTreep, uint32_t ticks) {
        UASSERT_OBJ(ticks > 0, exprp, "Delay must be > 0");
        AstAlways* const alwaysp = getDelayedAlways(exprp, senTreep);
        std::vector<AstVar*>& delayedr = m_delayed(alwaysp);
        // Ensure the required delay exists
        while (delayedr.size() < ticks) {
            AstVar* const firstp = delayedr.front();
            FileLine* const flp = firstp->fileline();
            // Create once more delayed value
            std::string name = firstp->name();
            name.resize(name.size() - 1);
            name += std::to_string(delayedr.size() + 1);
            AstNodeExpr* const prevp = new AstVarRef{flp, delayedr.back(), VAccess::READ};
            AstVar* const varp = createDelayedVar(name, alwaysp, prevp);
            // Add it to delayed variable vector
            delayedr.emplace_back(varp);
        }
        // Return a reference to the appropriately delayed variable
        return new AstVarRef{exprp->fileline(), delayedr.at(ticks - 1), VAccess::READ};
    }

    void visitAssertionIterate(AstNodeCoverOrAssert* nodep, AstNode* failsp) {
        if (m_beginp && nodep->name() == "") nodep->name(m_beginp->name());

        { AssertDeFutureVisitor{nodep->propp(), m_modp, m_modPastNum++}; }
        iterateChildren(nodep);

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
                nodep->v3warn(E_UNSUPPORTED,
                              "Unsupported: Procedural concurrent assertion with"
                              " clocking event inside always (IEEE 1800-2023 16.14.6)");
            }
        }
        //
        bool selfDestruct = false;
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
                if (passsp) {
                    passsp = AstNode::addNext<AstNode, AstNode>(covincp, passsp);
                } else {
                    passsp = covincp;
                }
            }
        } else if (VN_IS(nodep, Assert) || VN_IS(nodep, AssertIntrinsic)) {
            if (nodep->immediate()) {
                ++m_statAsImm;
            } else {
                ++m_statAsNotImm;
            }
            if (!passsp && !failsp)
                failsp = newFireAssertUnchecked(
                    nodep, VN_IS(nodep, AssertIntrinsic) ? "'$cast' failed." : "'assert' failed.");
        } else {
            nodep->v3fatalSrc("Unknown node type");
        }

        VL_RESTORER(m_passsp);
        VL_RESTORER(m_failsp);
        VL_RESTORER(m_underAssert);
        m_passsp = passsp;
        m_failsp = failsp;
        m_underAssert = true;
        iterate(nodep->propp());

        AstNode* propExprp;
        AstNodeExpr* disablep = nullptr;
        if (AstPropSpec* const specp = VN_CAST(nodep->propp(), PropSpec)) {
            propExprp = specp->propp()->unlinkFrBack();
            if (specp->disablep()) disablep = specp->disablep()->unlinkFrBack();
        } else {
            propExprp = nodep->propp()->unlinkFrBack();
        }
        AstNode* bodysp = assertBody(nodep, propExprp, passsp, failsp);
        if (disablep) {
            bodysp
                = new AstIf{nodep->fileline(), new AstLogNot{nodep->fileline(), disablep}, bodysp};
        }
        if (sentreep) {
            bodysp = new AstAlways{nodep->fileline(), VAlwaysKwd::ALWAYS, sentreep, bodysp};
        }

        if (passsp && !passsp->backp()) VL_DO_DANGLING(pushDeletep(passsp), passsp);
        if (failsp && !failsp->backp()) VL_DO_DANGLING(pushDeletep(failsp), failsp);

        // Install it
        if (selfDestruct) {
            // Delete it after making the tree.  This way we can tell the user
            // if it wasn't constructed nicely or has other errors without needing --coverage.
            VL_DO_DANGLING(bodysp->deleteTree(), bodysp);
            nodep->unlinkFrBack();
        } else {
            nodep->replaceWith(bodysp);
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
            const VAssertType assertType
                = nodep->uniquePragma() ? VAssertType::UNIQUE : VAssertType::UNIQUE0;
            AstIf* const checkifp
                = new AstIf{nodep->fileline(), new AstLogNot{nodep->fileline(), ohot},
                            newFireAssert(nodep, VAssertDirectiveType::VIOLATION_IF, assertType,
                                          "'unique if' statement violated"),
                            newifp};
            checkifp->isBoundsCheck(true);  // To avoid LATCH warning
            checkifp->branchPred(VBranchPred::BP_UNLIKELY);
            nodep->replaceWith(checkifp);
            VL_DO_DANGLING(pushDeletep(nodep), nodep);
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

            VAssertType assertType = VAssertType::INTERNAL;
            if (nodep->priorityPragma()) {
                assertType = VAssertType::PRIORITY;
            } else if (nodep->uniquePragma()) {
                assertType = VAssertType::UNIQUE;
            } else if (nodep->unique0Pragma()) {
                assertType = VAssertType::UNIQUE0;
            }

            string valFmt;
            if (exprDtypep->isIntegralOrPacked())
                valFmt = " for '" + cvtToStr(exprDtypep->widthMin()) + "'h%X'";
            if (nodep->fullPragma() || nodep->priorityPragma()) {
                // Need to add a default if there isn't one already
                ++m_statAsFull;
                if (!has_default) {
                    nodep->addItemsp(new AstCaseItem{
                        nodep->fileline(), nullptr /*DEFAULT*/,
                        newFireAssert(nodep, VAssertDirectiveType::VIOLATION_CASE, assertType,
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
                        AstNodeExpr* itembitp = nullptr;
                        for (AstNodeExpr* icondp = itemp->condsp(); icondp;
                             icondp = VN_AS(icondp->nextp(), NodeExpr)) {
                            AstNodeExpr* onep;
                            if (AstInsideRange* const rcondp = VN_CAST(icondp, InsideRange)) {
                                onep = rcondp->newAndFromInside(
                                    nodep->exprp()->cloneTreePure(true),
                                    rcondp->lhsp()->cloneTreePure(true),
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
                            // OR together all conditions within the same case item
                            if (onep) {
                                if (itembitp) {
                                    itembitp = new AstOr{icondp->fileline(), onep, itembitp};
                                } else {
                                    itembitp = onep;
                                }
                            }
                        }
                        if (itembitp) {
                            if (propp) {
                                propp = new AstConcat{itemp->fileline(), itembitp, propp};
                            } else {
                                propp = itembitp;
                            }
                        }
                    }
                    // Empty case means no property
                    if (!propp) propp = new AstConst{nodep->fileline(), AstConst::BitFalse{}};
                    const bool allow_none = has_default || nodep->unique0Pragma();
                    // The following assertion looks as below.
                    // if (!$onehot(propp)) begin
                    //     if (propp == '0) begin if (!allow_none) $error("none match"); end
                    //     else $error("multiple match");
                    // end
                    AstNodeExpr* const ohot = new AstOneHot{nodep->fileline(), propp};
                    AstConst* const zero = new AstConst{
                        nodep->fileline(), AstConst::WidthedValue{}, propp->width(), 0};
                    AstIf* const ohotIfp
                        = new AstIf{nodep->fileline(), new AstLogNot{nodep->fileline(), ohot}};
                    AstIf* const zeroIfp = new AstIf{
                        nodep->fileline(),
                        new AstEq{nodep->fileline(), propp->cloneTreePure(false), zero}};
                    AstNodeExpr* const exprp = nodep->exprp();
                    const string pragmaStr = nodep->pragmaString();
                    if (!allow_none)
                        zeroIfp->addThensp(
                            newFireAssert(nodep, VAssertDirectiveType::VIOLATION_CASE, assertType,
                                          pragmaStr + ", but none matched" + valFmt,
                                          valFmt.empty() ? nullptr : exprp->cloneTreePure(false)));
                    zeroIfp->addElsesp(
                        newFireAssert(nodep, VAssertDirectiveType::VIOLATION_CASE, assertType,
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

    void visit(AstFuture* nodep) override {
        nodep->v3error("Future sampled value function called outside property or sequence "
                       "expression (IEEE 16.9.4)");
        nodep->replaceWith(new AstConst{nodep->fileline(), 0});
        VL_DO_DANGLING(pushDeletep(nodep), nodep);
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
        AstNodeExpr* const exprp = newSampledExpr(nodep->exprp()->unlinkFrBack());
        AstNodeExpr* inp = getPastValue(exprp, nodep->sentreep()->unlinkFrBack(), ticks);
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
        if (nodep->exprp()) {
            nodep->replaceWith(nodep->exprp()->unlinkFrBack());
        } else {
            nodep->unlinkFrBack();
        }
        VL_DO_DANGLING(pushDeletep(nodep), nodep);
    }
    void visit(AstVarRef* nodep) override {
        iterateChildren(nodep);
        if (m_inSampled && !VString::startsWith(nodep->name(), "__VcycleDly")) {
            if (!nodep->access().isReadOnly()) {
                nodep->v3warn(E_UNSUPPORTED,
                              "Unsupported: Write to variable in sampled expression");
            } else {
                VNRelinker relinkHandle;
                nodep->unlinkFrBack(&relinkHandle);
                AstSampled* const newp = newSampledExpr(nodep);
                relinkHandle.relink(newp);
                newp->user1(1);
                v3Global.setHasSampled();
            }
        }
    }
    // Don't sample sensitivities
    void visit(AstSenItem* nodep) override {
        VL_RESTORER(m_inSampled);
        m_inSampled = false;
        iterateChildren(nodep);
    }
    void visit(AstPExprClause* nodep) override {
        if (m_underAssert) {
            if (nodep->pass() && m_passsp) {
                // Cover adds COVERINC by AstNode::addNext, thus need to clone next too.
                nodep->replaceWith(m_passsp->cloneTree(true));
            } else if (!nodep->pass() && m_failsp) {
                // Asserts with multiple statements are wrapped in implicit begin/end blocks so no
                // need to clone next.
                nodep->replaceWith(m_failsp->cloneTree(false));
            } else {
                nodep->unlinkFrBack();
            }
            VL_DO_DANGLING(pushDeletep(nodep), nodep);
        }
    }
    void visit(AstPExpr* nodep) override {
        if (m_underAssert) {
            VL_RESTORER(m_inSampled);
            m_inSampled = false;
            iterateChildren(nodep);
        } else if (m_inRestrict) {
            VL_DO_DANGLING(pushDeletep(nodep->unlinkFrBack()), nodep);
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
            FileLine* const fl = nodep->fileline();
            AstNode* monExprsp = nodep->fmtp()->exprsp();
            AstSenItem* monSenItemsp = nullptr;
            while (monExprsp) {
                if (AstNodeVarRef* varrefp = VN_CAST(monExprsp, NodeVarRef)) {
                    AstSenItem* const senItemp
                        = new AstSenItem{fl, VEdgeType::ET_CHANGED,
                                         // Clone so get VarRef or VarXRef as needed
                                         varrefp->cloneTree(false)};
                    if (!monSenItemsp) {
                        monSenItemsp = senItemp;
                    } else {
                        monSenItemsp->addNext(senItemp);
                    }
                }
                monExprsp = monExprsp->nextp();
            }
            AstSenTree* const monSenTree = new AstSenTree{fl, monSenItemsp};
            const auto monNum = ++m_monitorNum;
            // Where $monitor was we do "__VmonitorNum = N;"
            AstAssign* const newsetp = new AstAssign{
                fl, newMonitorNumVarRefp(nodep, VAccess::WRITE), new AstConst{fl, monNum}};
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
            AstNode* const newp = new AstAlways{fl, VAlwaysKwd::ALWAYS, monSenTree, ifp};
            m_modp->addStmtsp(newp);
        } else if (nodep->displayType() == VDisplayType::DT_STROBE) {
            nodep->displayType(VDisplayType::DT_DISPLAY);
            // Need one-shot
            FileLine* const fl = nodep->fileline();
            AstVar* const varp
                = new AstVar{fl, VVarType::MODULETEMP, "__Vstrobe" + cvtToStr(m_modStrobeNum++),
                             nodep->findBitDType()};
            m_modp->addStmtsp(varp);
            // Where $strobe was we do "__Vstrobe = '1;"
            AstAssign* const newsetp = new AstAssign{fl, new AstVarRef{fl, varp, VAccess::WRITE},
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
        AstAssign* const newp
            = new AstAssign{nodep->fileline(), newMonitorOffVarRefp(nodep, VAccess::WRITE),
                            new AstConst{nodep->fileline(), AstConst::BitTrue{}, nodep->off()}};
        nodep->replaceWith(newp);
        VL_DO_DANGLING(pushDeletep(nodep), nodep);
    }
    void visit(AstAssert* nodep) override {  //
        visitAssertionIterate(nodep, nodep->failsp());
    }
    void visit(AstAssertCtl* nodep) override {
        if (VN_IS(m_modp, Class) || VN_IS(m_modp, Iface)) {
            nodep->v3warn(E_UNSUPPORTED, "Unsupported: assertcontrols in classes or interfaces");
            VL_DO_DANGLING(pushDeletep(nodep->unlinkFrBack()), nodep);
            return;
        }

        iterateChildren(nodep);

        if (!resolveAssertType(nodep)) {
            nodep->v3warn(E_UNSUPPORTED,
                          "Unsupported: non-constant assert assertion-type expression");
            VL_DO_DANGLING(pushDeletep(nodep->unlinkFrBack()), nodep);
            return;
        }
        if (nodep->ctlAssertTypes() != ALL_ASSERT_TYPES
            && nodep->ctlAssertTypes().containsAny(VAssertType::EXPECT | VAssertType::UNIQUE
                                                   | VAssertType::UNIQUE0
                                                   | VAssertType::PRIORITY)) {
            nodep->v3warn(E_UNSUPPORTED, "Unsupported: assert control assertion_type");
            VL_DO_DANGLING(pushDeletep(nodep->unlinkFrBack()), nodep);
            return;
        }
        if (!resolveControlType(nodep)) {
            nodep->v3warn(E_UNSUPPORTED, "Unsupported: non-const assert control type expression");
            VL_DO_DANGLING(pushDeletep(nodep->unlinkFrBack()), nodep);
            return;
        }
        if (!resolveDirectiveType(nodep)) {
            nodep->v3warn(E_UNSUPPORTED,
                          "Unsupported: non-const assert directive type expression");
            VL_DO_DANGLING(pushDeletep(nodep->unlinkFrBack()), nodep);
            return;
        }

        FileLine* const fl = nodep->fileline();
        switch (nodep->ctlType()) {
        case VAssertCtlType::ON:
            UINFO(9, "Generating assertctl for a module: " << m_modp);
            nodep->replaceWith(new AstCExpr{
                fl,
                "vlSymsp->_vm_contextp__->assertOnSet("s + std::to_string(nodep->ctlAssertTypes())
                    + ", "s + std::to_string(nodep->ctlDirectiveTypes()) + ");\n"s,
                1});
            break;
        case VAssertCtlType::OFF:
        case VAssertCtlType::KILL: {
            UINFO(9, "Generating assertctl for a module: " << m_modp);
            nodep->replaceWith(new AstCExpr{fl,
                                            "vlSymsp->_vm_contextp__->assertOnClear("s
                                                + std::to_string(nodep->ctlAssertTypes()) + " ,"s
                                                + std::to_string(nodep->ctlDirectiveTypes())
                                                + ");\n"s,
                                            1});
            break;
        }
        case VAssertCtlType::LOCK:
        case VAssertCtlType::UNLOCK:
        case VAssertCtlType::PASS_ON:
        case VAssertCtlType::PASS_OFF:
        case VAssertCtlType::FAIL_ON:
        case VAssertCtlType::FAIL_OFF:
        case VAssertCtlType::NONVACUOUS_ON:
        case VAssertCtlType::VACUOUS_OFF: {
            nodep->unlinkFrBack();
            nodep->v3warn(E_UNSUPPORTED, "Unsupported: $assertcontrol control_type '" << cvtToStr(
                                             static_cast<int>(nodep->ctlType())) << "'");
            break;
        }
        default: {
            nodep->unlinkFrBack();
            nodep->v3warn(EC_ERROR, "Bad $assertcontrol control_type '"
                                        << cvtToStr(static_cast<int>(nodep->ctlType()))
                                        << "' (IEEE 1800-2023 Table 20-5)");
        }
        }
        VL_DO_DANGLING(pushDeletep(nodep), nodep);
    }
    void visit(AstAssertIntrinsic* nodep) override {  //
        visitAssertionIterate(nodep, nodep->failsp());
    }
    void visit(AstCover* nodep) override {  //
        visitAssertionIterate(nodep, nullptr);
    }
    void visit(AstRestrict* nodep) override {
        VL_RESTORER(m_inRestrict);
        m_inRestrict = true;
        iterateChildren(nodep);
        // IEEE says simulator ignores these
        VL_DO_DANGLING(pushDeletep(nodep->unlinkFrBack()), nodep);
    }

    void visit(AstNodeModule* nodep) override {
        VL_RESTORER(m_modp);
        VL_RESTORER(m_modPastNum);
        VL_RESTORER(m_modStrobeNum);
        VL_RESTORER(m_modExpr2Sen2DelayedAlwaysp);
        m_modp = nodep;
        m_modPastNum = 0;
        m_modStrobeNum = 0;
        m_modExpr2Sen2DelayedAlwaysp.clear();
        iterateChildren(nodep);
    }
    void visit(AstNodeProcedure* nodep) override {
        VL_RESTORER(m_procedurep);
        m_procedurep = nodep;
        iterateChildren(nodep);
    }
    void visit(AstGenBlock* nodep) override {
        // This code is needed rather than a visitor in V3Begin,
        // because V3Assert is called before V3Begin
        VL_RESTORER(m_beginp);
        m_beginp = nodep;
        iterateChildren(nodep);
    }
    void visit(AstBegin* nodep) override {
        // This code is needed rather than a visitor in V3Begin,
        // because V3Assert is called before V3Begin
        VL_RESTORER(m_beginp);
        m_beginp = nodep;
        iterateChildren(nodep);
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
        V3Stats::addStat("Assertions, $past variables", m_statPastVars);
    }
};

//######################################################################
// Top Assert class

void V3Assert::assertAll(AstNetlist* nodep) {
    UINFO(2, __FUNCTION__ << ":");
    { AssertVisitor{nodep}; }  // Destruct before checking
    V3Global::dumpCheckGlobalTree("assert", 0, dumpTreeEitherLevel() >= 3);
}
