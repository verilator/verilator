// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Collect and print statistics
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2005-2026 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#include "V3PchAstNoMT.h"  // VL_MT_DISABLED_CODE_UNIT

#include "V3Assert.h"

#include "V3AstUserAllocator.h"
#include "V3Const.h"
#include "V3Stats.h"
#include "V3Task.h"
#include "V3UniqueNames.h"

VL_DEFINE_DEBUG_FUNCTIONS;

namespace {

class DefaultDisableLocalVisitor final : public VNVisitor {
    // STATE
    AstNode* m_scopep = nullptr;

    // VISITORS
    void visit(AstNodeModule* nodep) override {
        VL_RESTORER(m_scopep);
        m_scopep = nodep;
        nodep->defaultDisablep(nullptr);
        iterateChildren(nodep);
    }
    void visit(AstGenBlock* nodep) override {
        VL_RESTORER(m_scopep);
        m_scopep = nodep;
        nodep->defaultDisablep(nullptr);
        iterateChildren(nodep);
    }
    void visit(AstDefaultDisable* nodep) override {
        UASSERT_OBJ(nodep, m_scopep,
                    "default disable iff must be inside a module or generate block");
        AstDefaultDisable* defaultp = nullptr;
        if (const AstNodeModule* const modp = VN_CAST(m_scopep, NodeModule)) {
            defaultp = modp->defaultDisablep();
        } else {
            defaultp = VN_AS(m_scopep, GenBlock)->defaultDisablep();
        }
        if (VL_UNLIKELY(defaultp)) {
            nodep->v3error("Only one 'default disable iff' allowed per "
                           << (VN_IS(m_scopep, NodeModule) ? "module" : "generate block")
                           << " (IEEE 1800-2023 16.15)");
        } else if (AstNodeModule* const modp = VN_CAST(m_scopep, NodeModule)) {
            modp->defaultDisablep(nodep);
        } else {
            VN_AS(m_scopep, GenBlock)->defaultDisablep(nodep);
        }
    }
    void visit(AstNode* nodep) override { iterateChildren(nodep); }

public:
    explicit DefaultDisableLocalVisitor(AstNetlist* nodep) { iterate(nodep); }
};

class DefaultDisablePropagateVisitor final : public VNVisitor {
    // STATE
    AstDefaultDisable* m_defaultDisablep = nullptr;

    // VISITORS
    void visit(AstNodeModule* nodep) override {
        VL_RESTORER(m_defaultDisablep);
        m_defaultDisablep = nodep->defaultDisablep();
        iterateChildren(nodep);
    }
    void visit(AstGenBlock* nodep) override {
        VL_RESTORER(m_defaultDisablep);
        if (!nodep->defaultDisablep()) nodep->defaultDisablep(m_defaultDisablep);
        m_defaultDisablep = nodep->defaultDisablep();
        iterateChildren(nodep);
    }
    void visit(AstNode* nodep) override { iterateChildren(nodep); }

public:
    explicit DefaultDisablePropagateVisitor(AstNetlist* nodep) { iterate(nodep); }
};

// Lower a sequence used as an event control ('@seq', IEEE 1800-2023 9.4.2.4) into a
// synthesized event fired by an internal 'cover sequence' on each end-of-match
class SeqEventLowerVisitor final : public VNVisitor {
    // STATE
    AstNodeModule* m_modp = nullptr;  // Current module
    V3UniqueNames m_names{"__VseqEvent"};  // Synthesized event names

    // VISITORS
    void visit(AstNodeModule* nodep) override {
        VL_RESTORER(m_modp);
        m_modp = nodep;
        iterateChildren(nodep);
    }
    void visit(AstSenItem* nodep) override {
        AstFuncRef* const funcrefp = VN_CAST(nodep->sensp(), FuncRef);
        if (funcrefp && VN_IS(funcrefp->taskp(), Sequence)) {
            FileLine* const flp = nodep->fileline();
            AstVar* const eventp = new AstVar{flp, VVarType::MODULETEMP, m_names.get(nodep),
                                              m_modp->findBasicDType(VBasicDTypeKwd::EVENT)};
            eventp->lifetime(VLifetime::STATIC_EXPLICIT);
            m_modp->addStmtsp(eventp);
            v3Global.setHasEvents();
            funcrefp->unlinkFrBack();
            nodep->sensp(new AstVarRef{flp, eventp, VAccess::READ});
            const bool automaticActual = funcrefp->exists([](const AstNodeVarRef* refp) {
                return refp->varp() && refp->varp()->lifetime().isAutomatic();
            });
            if (automaticActual) {
                nodep->v3error("Arguments to a sequence used as an event control must be"
                               " static (IEEE 1800-2023 9.4.2.4)");
                VN_AS(funcrefp->taskp(), Sequence)->isReferenced(false);
                VL_DO_DANGLING(pushDeletep(funcrefp), funcrefp);
                return;
            }
            AstFireEvent* const firep
                = new AstFireEvent{flp, new AstVarRef{flp, eventp, VAccess::WRITE}, false};
            AstCover* const coverp
                = new AstCover{flp, new AstPropSpec{flp, nullptr, nullptr, funcrefp}, firep,
                               VAssertType::CONCURRENT};
            coverp->isCoverSeq(true);
            coverp->isSeqEvent(true);
            m_modp->addStmtsp(new AstAlways{flp, VAlwaysKwd::ASSERT_COVER, nullptr, coverp});
            return;
        }
        iterateChildren(nodep);
    }
    void visit(AstNode* nodep) override { iterateChildren(nodep); }

public:
    explicit SeqEventLowerVisitor(AstNetlist* nodep) { iterate(nodep); }
};

}  // namespace

void V3AssertCommon::collectDefaultDisable(AstNetlist* nodep) {
    { DefaultDisableLocalVisitor{nodep}; }
    { DefaultDisablePropagateVisitor{nodep}; }
}

void V3AssertCommon::lowerSequenceEvents(AstNetlist* nodep) {
    { SeqEventLowerVisitor{nodep}; }
    V3Global::dumpCheckGlobalTree("assertseqevent", 0, dumpTreeEitherLevel() >= 3);
}

string V3AssertCommon::assertCtlGetCall(const char* query, VAssertType type,
                                        VAssertDirectiveType directiveType) {
    // Template arguments let the runtime build the type/directive mask at C++ compile time
    return "vlSymsp->_vm_contextp__->assertCtlGet<"s + std::to_string(type) + ", "s
           + std::to_string(directiveType) + ">(VerilatedAssertCtlQuery::"s + query + ")"s;
}

bool V3AssertCommon::checkSvaValueLimit(AstNode* nodep, const AstConst* constp, const char* what) {
    // Temporal values can materialize as O(N) AST or state in later passes.
    // Leave headroom for a range ring's extra slot and V3Number's signed
    // `(bits + 31) / 32` word count.
    static constexpr unsigned SVA_VALUE_HARD_LIMIT
        = static_cast<unsigned>(std::numeric_limits<int>::max()) - 32U;
    const unsigned configuredLimit = static_cast<unsigned>(v3Global.opt.maxNumWidth());
    const unsigned limit = std::min(configuredLimit, SVA_VALUE_HARD_LIMIT);
    if (constp->num().fitsInUInt() && constp->toUInt() <= limit) return true;
    nodep->v3warn(E_UNSUPPORTED, "Unsupported: " << what << " exceeds implementation limit of "
                                                 << limit
                                                 << (configuredLimit <= SVA_VALUE_HARD_LIMIT
                                                         ? " (--max-num-width)"
                                                         : " (host arithmetic limit)"));
    return false;
}

// The bound of a cycle delay in a sequence, if a non-negative elaboration-time constant
static const AstConst* checkSvaDelayBound(AstNode* errp, AstNodeExpr* boundp, const char* what) {
    const AstConst* const constp = VN_CAST(boundp, Const);
    if (!constp || (constp->dtypep()->isSigned() && constp->num().isNegative())) {
        errp->v3error(what << " is not a non-negative elaboration-time constant"
                              " (IEEE 1800-2023 16.7)");
        return nullptr;
    }
    if (!V3AssertCommon::checkSvaValueLimit(errp, constp, "SVA cycle delay")) return nullptr;
    return constp;
}

// Fold the bounds of a cycle delay in a sequence, and return if they are valid, else report it
// on errp
static bool svaCycleDelayValid(const AstDelay* nodep, AstNode* errp) {
    V3Const::constifyParamsNoWarnEdit(nodep->lhsp());
    const AstConst* const minConstp = checkSvaDelayBound(
        errp, nodep->lhsp(), nodep->isRangeDelay() ? "Range delay minimum" : "Delay value");
    if (!nodep->rhsp() || nodep->isUnbounded()) return minConstp != nullptr;
    V3Const::constifyParamsNoWarnEdit(nodep->rhsp());
    const AstConst* const maxConstp
        = checkSvaDelayBound(errp, nodep->rhsp(), "Range delay maximum");
    if (!minConstp || !maxConstp) return false;
    if (maxConstp->toUInt() < minConstp->toUInt()) {
        errp->v3error("Range delay maximum must be >= minimum (IEEE 1800-2023 16.7)");
        return false;
    }
    return true;
}

void V3AssertCommon::checkSvaCycleDelay(AstDelay* nodep, AstNode* errp) {
    if (svaCycleDelayValid(nodep, errp)) return;
    // Make the delay valid, so later steps do not fail after the error
    FileLine* const flp = nodep->fileline();
    AstNodeExpr* const minp = nodep->lhsp();
    minp->replaceWith(new AstConst{flp, AstConst::BitFalseErroring{}});
    VL_DO_DANGLING(minp->deleteTree(), minp);
    if (nodep->rhsp() && !nodep->isUnbounded()) {
        AstNodeExpr* const maxp = nodep->rhsp();
        maxp->replaceWith(new AstConst{flp, AstConst::BitFalseErroring{}});
        VL_DO_DANGLING(maxp->deleteTree(), maxp);
    }
}

bool V3AssertCommon::refsSvaFormal(const AstNode* nodep) {
    return nodep->exists([](const AstNodeVarRef* refp) {
        const AstVar* const varp = refp->varp();
        if (!varp || !varp->isIO()) return false;
        const AstNode* const declp = varp->aboveLoopp();
        return VN_IS(declp, Sequence) || VN_IS(declp, Property);
    });
}

void V3AssertCommon::checkSvaInstanceDelays(AstNode* nodep, AstNode* instp) {
    // A delay still referencing a formal argument of an enclosing sequence or property is
    // checked when that is instanced. Collect first, as checking edits the delays.
    std::vector<AstDelay*> delayps;
    nodep->foreach([&](AstDelay* delayp) {
        if (!delayp->isCycleDelay() || refsSvaFormal(delayp->lhsp())) return;
        if (delayp->rhsp() && refsSvaFormal(delayp->rhsp())) return;
        delayps.push_back(delayp);
    });
    for (AstDelay* const delayp : delayps) checkSvaCycleDelay(delayp, instp);
}

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
            AstNodeStmt* const assp
                = new AstAssignDly{nodep->fileline(), varRefAWritep, varRefAReadp};
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
    ~AssertDeFutureVisitor() override = default;
};

// Prepare one default sampled expression.
class DefaultSampledValueVisitor final : public VNVisitor {
    // STATE
    bool m_defaulted = false;  // A reference below was replaced by its default

    // METHODS
    AstConst* newTypeDefault(AstNodeExpr* nodep) {
        m_defaulted = true;
        AstConst* const constp
            = new AstConst{nodep->fileline(), AstConst::DTyped{}, nodep->dtypep()};
        if (nodep->dtypep()->isFourstate()) constp->num().setAllBitsX();
        constp->dtypeFrom(nodep);
        return constp;
    }

    void visitSelect(AstNodeExpr* nodep) {
        // A select of a replaced value or index is itself the default of its type
        bool setDefaulted;
        {
            VL_RESTORER(m_defaulted);
            m_defaulted = false;
            iterateChildren(nodep);
            setDefaulted = m_defaulted;
        }
        if (setDefaulted) {
            m_defaulted = true;  // Propagate up that replacement was made
            nodep->replaceWith(newTypeDefault(nodep));
            VL_DO_DANGLING(pushDeletep(nodep), nodep);
            return;
        }
    }

    // VISITORS
    void visit(AstCMethodHard* nodep) override {
        if (nodep->method() == VCMethod::EVENT_IS_TRIGGERED) {
            nodep->replaceWith(new AstConst{nodep->fileline(), AstConst::BitFalse{}});
            VL_DO_DANGLING(pushDeletep(nodep), nodep);
        } else {
            iterateChildren(nodep);
        }
    }
    void visit(AstNodeVarRef* nodep) override {
        AstVar* const varp = nodep->varp();
        if (varp->isParam()
            || (!varp->isNet() && varp->lifetime().isStatic() && varp->hasUserInit())) {
            return;
        }
        nodep->replaceWith(newTypeDefault(nodep));
        VL_DO_DANGLING(pushDeletep(nodep), nodep);
    }
    void visit(AstArraySel* nodep) override { visitSelect(nodep); }
    void visit(AstSel* nodep) override { visitSelect(nodep); }
    void visit(AstNode* nodep) override { iterateChildren(nodep); }

public:
    explicit DefaultSampledValueVisitor(AstNode* nodep) { iterate(nodep); }
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
    //  AstNodeVarRef::user2()   -> bool.  True if shouldn't be sampled
    //  AstIf::user2()           -> bool.  True for assertOn() checks inserted in this pass
    const VNUser1InUse m_user1InUse;
    const VNUser2InUse m_user2InUse;
    AstUser2Allocator<AstAlways, std::vector<AstVar*>> m_delayed;

    // STATE
    AstNodeModule* m_modp = nullptr;  // Last module
    const AstNode* m_beginp = nullptr;  // Last AstBegin/AstGenBlock
    unsigned m_monitorNum = 0;  // Global $monitor numbering (not per module)
    AstVar* m_monitorNumVarp = nullptr;  // $monitor number variable
    AstVar* m_monitorOffVarp = nullptr;  // $monitoroff variable
    AstVar* m_monitorPendingVarp = nullptr;  // $monitor display pending variable
    unsigned m_modPastNum = 0;  // Module past numbering
    unsigned m_modStrobeNum = 0;  // Module $strobe numbering
    AstNodeStmt* m_obsFlushp = nullptr;  // Clears the current process's pending deferred calls
    AstVar* m_obsDoneVarp = nullptr;  // Set when the outermost scope ends without a disable
    std::vector<AstNode*> m_obsWaitsp;  // Current process waits, flushed if it has pending calls
    bool m_inSpawnedFork = false;  // Under a fork...join_any or fork...join_none
    AstVar* m_obsEventp = nullptr;  // Current module event to run deferred calls
    AstAlwaysReactive* m_obsReactivep = nullptr;  // Current module block running deferred calls
    AstNodeProcedure* m_procedurep = nullptr;  // Current procedure
    AstAlways* m_assertCoverp = nullptr;  // Process of the current concurrent assertion
    VDouble0 m_statCover;  // Statistic tracking
    VDouble0 m_statAsNotImm;  // Statistic tracking
    VDouble0 m_statAsImm;  // Statistic tracking
    VDouble0 m_statAsFull;  // Statistic tracking
    VDouble0 m_statPastVars;  // Statistic tracking
    VDouble0 m_statAssertOnCombined;  // Statistic tracking
    VDouble0 m_statAssertOnHoisted;  // Statistic tracking
    bool m_inSampled = false;  // True inside a sampled expression
    bool m_inRestrict = false;  // True inside restrict assertion
    AstNodeStmt* m_passsp = nullptr;  // Current pass statement
    AstNodeStmt* m_failsp = nullptr;  // Current fail statement
    AstNodeCoverOrAssert* m_assertp = nullptr;  // Current assertion
    AstFinal* m_finalp = nullptr;  // Current final block
    VDouble0 m_statLiftedCaseExprs;  // Count of purified case expressions
    AstNodeFTask* m_ftaskp = nullptr;  // Current function/task
    V3UniqueNames m_caseTempNames{"__VCase"};  // Unique names for case temporaries
    V3UniqueNames m_matchCountNames{"__VnfaRemainingMatchCount"};  // Match replay counter names
    V3UniqueNames m_obsNames{"__VassertObs"};  // Observed deferred assertion temp names
    // Maps from (expression, senTree) to the AstAlways that computes its delayed values.
    std::unordered_map<VNRef<AstNodeExpr>, std::unordered_map<VNRef<AstSenTree>, AstAlways*>>
        m_modExpr2Sen2DelayedAlwaysp;
    // Source sampled-value history is initialized, unlike internal property-lowering history.
    std::unordered_map<VNRef<AstNodeExpr>, std::unordered_map<VNRef<AstSenTree>, AstAlways*>>
        m_modExpr2Sen2DefaultDelayedAlwaysp;
    // Map from delayed-value AstAlways to its last-sampling-tick time variable
    std::unordered_map<const AstAlways*, AstVar*> m_delayedAlways2TickTimep;

    // METHODS
    static const char* assertPassOnQuery(bool vacuous) {
        static constexpr const char* queries[2]
            = {"ASSERT_CTL_PASS_ON_NONVACUOUS", "ASSERT_CTL_PASS_ON_VACUOUS"};
        return queries[vacuous];
    }
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
                return new AstCExpr{
                    fl, AstCExpr::Pure{},
                    V3AssertCommon::assertCtlGetCall("ASSERT_CTL_ON", type, directiveType), 1};
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

    static bool isControlled(VAssertDirectiveType directiveType) {
        return (static_cast<int>(directiveType)
                & (static_cast<int>(VAssertDirectiveType::ASSERT)
                   | static_cast<int>(VAssertDirectiveType::COVER)
                   | static_cast<int>(VAssertDirectiveType::ASSUME)));
    }
    static AstNodeExpr* assertPassOnCond(FileLine* fl, VAssertType type,
                                         VAssertDirectiveType directiveType, bool vacuous) {
        if (!isControlled(directiveType)) return new AstConst{fl, AstConst::BitTrue{}};
        if (!v3Global.opt.assertOn()) return new AstConst{fl, AstConst::BitFalse{}};
        return new AstCExpr{
            fl, AstCExpr::Pure{},
            V3AssertCommon::assertCtlGetCall(assertPassOnQuery(vacuous), type, directiveType), 1};
    }
    static AstNodeExpr* assertFailOnCond(FileLine* fl, VAssertType type,
                                         VAssertDirectiveType directiveType) {
        if (!isControlled(directiveType)) return new AstConst{fl, AstConst::BitTrue{}};
        if (!v3Global.opt.assertOn()) return new AstConst{fl, AstConst::BitFalse{}};
        return new AstCExpr{
            fl, AstCExpr::Pure{},
            V3AssertCommon::assertCtlGetCall("ASSERT_CTL_FAIL_ON", type, directiveType), 1};
    }
    string assertDisplayMessage(const AstNode* nodep, const string& prefix, const string& message,
                                VDisplayType severity) {
        if (severity == VDisplayType::DT_ERROR || severity == VDisplayType::DT_FATAL) {
            return ("[%0t] "s + prefix + ": " + nodep->fileline()->filebasename() + ":"
                    + cvtToStr(nodep->fileline()->lineno()) + ": Assertion failed in %m"
                    + ((message != "") ? ": " : "") + message + "\n");
        }
        return ("[%0t] "s + prefix + ": " + nodep->fileline()->filebasename() + ":"
                + cvtToStr(nodep->fileline()->lineno()) + ": %m" + ((message != "") ? ": " : "")
                + message + "\n");
    }
    void replaceDisplay(AstDisplay* nodep, const string& prefix) {
        nodep->fmtp()->text(
            assertDisplayMessage(nodep, prefix, nodep->fmtp()->text(), nodep->displayType()));
        nodep->displayType(VDisplayType::DT_WRITE);
        // cppcheck-suppress nullPointer
        AstNodeExpr* const timenewp = new AstTime{nodep->fileline(), m_modp->timeunit()};
        nodep->fmtp()->prependExprsp(timenewp);
        if (!nodep->fmtp()->scopeNamep() && nodep->fmtp()->formatScopeTracking()) {
            nodep->fmtp()->scopeNamep(new AstScopeName{nodep->fileline(), true});
        }
    }
    AstSampled* newSampledExpr(AstNodeExpr* nodep) {
        return new AstSampled{nodep->fileline(), nodep, nodep->dtypep(), true};
    }
    AstVarRef* newMonitorNumVarRefp(const AstNode* nodep, VAccess access) {
        if (!m_monitorNumVarp) {
            m_monitorNumVarp = new AstVar{nodep->fileline(), VVarType::MODULETEMP, "__VmonitorNum",
                                          nodep->findUInt64DType()};
            v3Global.rootp()->dollarUnitPkgp()->addStmtsp(m_monitorNumVarp);
        }
        AstVarRef* const varrefp = new AstVarRef{nodep->fileline(), m_monitorNumVarp, access};
        varrefp->classOrPackagep(v3Global.rootp()->dollarUnitPkgp());
        return varrefp;
    }
    AstVarRef* newMonitorOffVarRefp(const AstNode* nodep, VAccess access) {
        if (!m_monitorOffVarp) {
            m_monitorOffVarp = new AstVar{nodep->fileline(), VVarType::MODULETEMP, "__VmonitorOff",
                                          nodep->findBitDType()};
            v3Global.rootp()->dollarUnitPkgp()->addStmtsp(m_monitorOffVarp);
        }
        AstVarRef* const varrefp = new AstVarRef{nodep->fileline(), m_monitorOffVarp, access};
        varrefp->classOrPackagep(v3Global.rootp()->dollarUnitPkgp());
        return varrefp;
    }
    AstVarRef* newMonitorPendingVarRefp(const AstNode* nodep, VAccess access) {
        FileLine* const flp = nodep->fileline();
        if (!m_monitorPendingVarp) {
            m_monitorPendingVarp = new AstVar{flp, VVarType::MODULETEMP, "__VmonitorPending",
                                              nodep->findBitDType()};
            v3Global.rootp()->dollarUnitPkgp()->addStmtsp(m_monitorPendingVarp);
        }
        AstVarRef* const varrefp = new AstVarRef{flp, m_monitorPendingVarp, access};
        varrefp->classOrPackagep(v3Global.rootp()->dollarUnitPkgp());
        return varrefp;
    }
    AstAssign* newMonitorPendingSetp(const AstNode* nodep) {
        FileLine* const flp = nodep->fileline();
        return new AstAssign{flp, newMonitorPendingVarRefp(nodep, VAccess::WRITE),
                             new AstConst{flp, AstConst::BitTrue{}}};
    }
    static AstVar* newModuleTemp(FileLine* flp, const string& name, AstNodeDType* dtypep,
                                 AstNodeModule* ownerp) {
        AstVar* const varp = new AstVar{flp, VVarType::MODULETEMP, name, dtypep};
        varp->isInternal(true);
        ownerp->addStmtsp(varp);
        return varp;
    }
    AstNodeStmt* newDeferredAssertFlush(FileLine* flp) const {
        return new AstDeferredAssertFlush{flp, m_obsFlushp->cloneTree(true)};
    }
    // Add the flushes of a process once it is known to have observed deferred assertions
    template <typename T_Scope>
    void addObsFlushes(T_Scope* scopep) {
        if (!m_obsFlushp) return;
        for (AstNode* const nodep : m_obsWaitsp) {
            if (AstEventControl* const controlp = VN_CAST(nodep, EventControl)) {
                addResumeFlush(controlp);
            } else if (AstWait* const waitp = VN_CAST(nodep, Wait)) {
                addResumeFlush(waitp);
            } else {  // AstWaitFork has no statements
                nodep->addNextHere(newDeferredAssertFlush(nodep->fileline()));
            }
        }
        // IEEE 1800-2023 16.4.4: Flush when the outermost scope was exited by a disable
        if (m_obsDoneVarp) {
            FileLine* const flp = scopep->fileline();
            // Clear for the next run of an always
            AstAssign* const clearp
                = new AstAssign{flp, new AstVarRef{flp, m_obsDoneVarp, VAccess::WRITE},
                                new AstConst{flp, AstConst::BitFalse{}}};
            scopep->addStmtsp(new AstIf{flp, new AstVarRef{flp, m_obsDoneVarp, VAccess::READ},
                                        clearp, newDeferredAssertFlush(flp)});
        }
        VL_DO_DANGLING(m_obsFlushp->deleteTree(), m_obsFlushp);
    }
    template <typename T_HasStmtsp>
    void addResumeFlush(T_HasStmtsp* nodep) const {
        if (!m_obsFlushp) return;
        if (nodep->stmtsp()) {
            nodep->stmtsp()->addHereThisAsNext(newDeferredAssertFlush(nodep->fileline()));
        } else {
            nodep->addStmtsp(newDeferredAssertFlush(nodep->fileline()));
        }
    }
    static AstQueueDType* newQueueDTypep(FileLine* flp, AstNodeDType* elemDTypep) {
        AstQueueDType* const queueDtp = new AstQueueDType{flp, elemDTypep, nullptr};
        v3Global.rootp()->typeTablep()->addTypesp(queueDtp);
        return queueDtp;
    }
    static AstNodeStmt* newQueuePush(FileLine* flp, AstVar* queuep, AstNodeExpr* valuep) {
        AstCMethodHard* const callp = new AstCMethodHard{
            flp, new AstVarRef{flp, queuep, VAccess::WRITE}, VCMethod::ARRAY_PUSH_BACK, valuep};
        callp->dtypeSetVoid();
        return callp->makeStmt();
    }
    static AstCMethodHard* newQueuePop(FileLine* flp, AstVar* queuep, AstNodeDType* elemDTypep) {
        AstCMethodHard* const callp = new AstCMethodHard{
            flp, new AstVarRef{flp, queuep, VAccess::READWRITE}, VCMethod::ARRAY_POP_FRONT};
        callp->dtypeFrom(elemDTypep);
        return callp;
    }
    void snapshotObservedExpr(AstNodeExpr* exprp, AstNodeStmt*& queuesp) {
        // Constants and, within the time step of the call, the time cannot change
        if (VN_IS(exprp, Const) || VN_IS(exprp, Time)) return;
        FileLine* const flp = exprp->fileline();
        AstNodeDType* const dtypep = exprp->dtypep();
        AstVar* const queuep
            = newModuleTemp(flp, m_obsNames.get("ValQueue"), newQueueDTypep(flp, dtypep), m_modp);
        queuep->setIgnoreSchedWrite();
        VNRelinker handle;
        AstNodeExpr* const oldp = exprp->unlinkFrBack(&handle);
        handle.relink(newQueuePop(flp, queuep, dtypep));
        queuesp = AstNode::addNext(queuesp, newQueuePush(flp, queuep, oldp));
        AstCMethodHard* const clearp = new AstCMethodHard{
            flp, new AstVarRef{flp, queuep, VAccess::WRITE}, VCMethod::DYN_CLEAR};
        clearp->dtypeSetVoid();
        m_obsFlushp = AstNode::addNext(m_obsFlushp, clearp->makeStmt());
    }
    void snapshotObservedSFormatArgs(AstSFormatF* fmtp, AstNodeStmt*& queuesp) {
        for (AstNodeExpr* exprp = fmtp->exprsp(); exprp;) {
            AstNodeExpr* const nextp = VN_CAST(exprp->nextp(), NodeExpr);
            AstSFormatArg* const argp = VN_CAST(exprp, SFormatArg);
            snapshotObservedExpr(argp ? argp->exprp() : exprp, queuesp);
            exprp = nextp;
        }
    }
    static AstIf* newIfAssertOn(AstNodeStmt* bodyp, VAssertDirectiveType directiveType,
                                VAssertType type = VAssertType::INTERNAL) {
        // Add an internal if to check assertions are on.
        // Don't make this an AND term, as it's unlikely to need to test this.
        FileLine* const fl = bodyp->fileline();

        AstNodeExpr* const condp = assertOnCond(fl, type, directiveType);
        AstIf* const newp = new AstIf{fl, condp, bodyp};
        newp->isBoundsCheck(true);  // To avoid LATCH warning
        newp->user2(true);  // Mark as an assertOn() check
        return newp;
    }
    static AstNodeStmt* newIfAssertPassOn(AstNodeStmt* bodyp, VAssertDirectiveType directiveType,
                                          VAssertType type, bool vacuous) {
        // Add an internal if to check assertion passOn is enabled.
        // Don't make this an AND term, as it's unlikely to need to test this.
        FileLine* const fl = bodyp->fileline();
        AstNodeExpr* const condp = assertPassOnCond(fl, type, directiveType, vacuous);
        AstNodeIf* const newp = new AstIf{fl, condp, bodyp};
        newp->isBoundsCheck(true);  // To avoid LATCH warning
        newp->user1(true);  // Don't assert/cover this if
        newp->user2(true);  // Mark as an assertOn() check
        return newp;
    }
    static AstNodeStmt* newIfAssertFailOn(AstNodeStmt* bodyp, VAssertDirectiveType directiveType,
                                          VAssertType type) {
        // Add an internal if to check assertion failOn is enabled.
        // Don't make this an AND term, as it's unlikely to need to test this.
        FileLine* const fl = bodyp->fileline();
        AstNodeExpr* const condp = assertFailOnCond(fl, type, directiveType);
        AstNodeIf* const newp = new AstIf{fl, condp, bodyp};
        newp->isBoundsCheck(true);  // To avoid LATCH warning
        newp->user1(true);  // Don't assert/cover this if
        newp->user2(true);  // Mark as an assertOn() check
        return newp;
    }

    static AstIf* assertCond(const AstNodeCoverOrAssert* nodep, AstNodeExpr* propp,
                             AstNodeStmt* passsp, AstNodeStmt* failsp) {
        AstIf* const ifp = new AstIf{nodep->fileline(), propp, passsp, failsp};
        // It's more LIKELY that we'll take the nullptr if clause
        // than the sim-killing else clause:
        ifp->branchPred(VBranchPred::BP_LIKELY);
        ifp->isBoundsCheck(true);  // To avoid LATCH warning
        return ifp;
    }

    AstNodeStmt* assertBody(const AstNodeCoverOrAssert* nodep, AstNode* propp, AstNodeStmt* passsp,
                            AstNodeStmt* failsp) {
        if (AstPExpr* const pexprp = VN_CAST(propp, PExpr)) {
            if (!v3Global.opt.timing().isSetTrue()) {
                nodep->v3warn(E_NOTIMING, "This property expression requires --timing");
                VL_DO_DANGLING(pushDeletep(pexprp), pexprp);
                return new AstBegin{nodep->fileline(), "", nullptr, false};
            }
            AstFork* const forkp = new AstFork{nodep->fileline(), VJoinType::JOIN_NONE};
            forkp->addForksp(new AstForkItem{nodep->fileline(), pexprp->bodyp()->unlinkFrBack()});
            if (AstNodeStmt* const finalp = pexprp->finalp()) {
                if (!m_finalp) {
                    m_finalp = new AstFinal{m_modp->fileline(), finalp->unlinkFrBack()};
                    m_modp->addStmtsp(m_finalp);
                } else {
                    m_finalp->addStmtsp(finalp->unlinkFrBack());
                }
            }
            VL_DO_DANGLING2(pushDeletep(pexprp), pexprp, propp);
            return forkp;
        }

        return assertCond(nodep, VN_AS(propp, NodeExpr), passsp, failsp);
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

    AstVar* createDelayedVar(const std::string& name, AstAlways* alwaysp, AstNodeExpr* exprp,
                             AstNodeExpr* initp) {
        FileLine* const flp = exprp->fileline();
        AstVar* const varp = new AstVar{flp, VVarType::MODULETEMP, name, exprp->dtypep()};
        // TODO: this lifetime seems nonsene (can't have NBAs to automatics), but is as before
        varp->lifetime(VLifetime::AUTOMATIC_EXPLICIT);
        m_modp->addStmtsp(varp);
        // Before enough clock ticks, $past returns the expression's default sampled value.
        if (initp) {
            m_modp->addStmtsp(new AstInitialStatic{
                flp, new AstAssign{flp, new AstVarRef{flp, varp, VAccess::WRITE}, initp}});
        }
        ++m_statPastVars;
        // Actually set the delayed value
        AstNodeExpr* const lhsp = new AstVarRef{flp, varp, VAccess::WRITE};
        AstAssignDly* const assignp = new AstAssignDly{flp, lhsp, exprp};
        alwaysp->prependStmtsp(assignp);
        return varp;
    }

    AstAlways* getDelayedAlways(AstNodeExpr* exprp, AstNodeExpr* initp, AstSenTree* senTreep) {
        auto& expr2Sen2Alwaysr
            = initp ? m_modExpr2Sen2DefaultDelayedAlwaysp : m_modExpr2Sen2DelayedAlwaysp;
        AstAlways*& alwayspr = expr2Sen2Alwaysr[*exprp][*senTreep];
        if (!alwayspr) {
            FileLine* const flp = exprp->fileline();
            // Create the always block that computes the delayed values
            alwayspr = new AstAlways{flp, VAlwaysKwd::ALWAYS, senTreep, nullptr};
            m_modp->addStmtsp(alwayspr);
            // Create the once-delayed variable
            const std::string name = "_Vpast_" + cvtToStr(m_modPastNum++) + "_1";
            AstVar* const varp = createDelayedVar(name, alwayspr, exprp, initp);
            // Add it to delayed variable vector
            m_delayed(alwayspr).emplace_back(varp);
        } else {
            // Reusing exiting, not needed
            VL_DO_DANGLING(pushDeletep(exprp), exprp);
            if (initp) VL_DO_DANGLING(pushDeletep(initp), initp);
            VL_DO_DANGLING(pushDeletep(senTreep), senTreep);
        }
        return alwayspr;
    }

    AstNodeExpr* getPastValue(AstNodeExpr* exprp, AstNodeExpr* initp, AstSenTree* senTreep,
                              uint32_t ticks) {
        UASSERT_OBJ(ticks > 0, exprp, "Delay must be > 0");
        FileLine* const flp = exprp->fileline();
        AstAlways* const alwaysp
            = getDelayedAlways(exprp, initp ? initp->cloneTreePure(false) : nullptr, senTreep);
        AstNodeExpr* const resultp = pastValueRef(alwaysp, flp, ticks, initp);
        if (initp) VL_DO_DANGLING(pushDeletep(initp), initp);
        return resultp;
    }

    AstNodeExpr* pastValueRef(AstAlways* alwaysp, FileLine* flp, uint32_t ticks,
                              AstNodeExpr* initp) {
        std::vector<AstVar*>& delayedr = m_delayed(alwaysp);
        // Ensure the required delay exists
        while (delayedr.size() < ticks) {
            AstVar* const firstp = delayedr.front();
            FileLine* const varFlp = firstp->fileline();
            // Create once more delayed value
            std::string name = firstp->name();
            name.resize(name.size() - 1);
            name += std::to_string(delayedr.size() + 1);
            AstNodeExpr* const prevp = new AstVarRef{varFlp, delayedr.back(), VAccess::READ};
            AstVar* const varp = createDelayedVar(name, alwaysp, prevp,
                                                  initp ? initp->cloneTreePure(false) : nullptr);
            // Add it to delayed variable vector
            delayedr.emplace_back(varp);
        }
        // Return a reference to the appropriately delayed variable
        return new AstVarRef{flp, delayedr.at(ticks - 1), VAccess::READ};
    }

    // Time of the pipeline's last sampling tick, for end-of-simulation readers
    AstVar* getPastTickTimeVar(AstAlways* alwaysp) {
        AstVar*& varpr = m_delayedAlways2TickTimep[alwaysp];
        if (!varpr) {
            FileLine* const flp = alwaysp->fileline();
            varpr = new AstVar{flp, VVarType::MODULETEMP,
                               "_Vpast_" + cvtToStr(m_modPastNum++) + "_t",
                               m_modp->findUInt64DType()};
            m_modp->addStmtsp(varpr);
            AstNodeExpr* const timep = new AstCExpr{flp, "vlSymsp->_vm_contextp__->time()", 64};
            alwaysp->addStmtsp(
                new AstAssign{flp, new AstVarRef{flp, varpr, VAccess::WRITE}, timep});
        }
        return varpr;
    }

    // Lower observed deferred action into a pending call with its input arguments snapshotted.
    // Pending calls run in the Reactive region unless a flush of their process clears them
    // (IEEE 1800-2023 16.4.1).
    AstNodeStmt* newObservedDeferredAction(FileLine* flp, AstNodeStmt* actionsp) {
        if (!(actionsp->isOutputter() || VN_IS(actionsp, SFormat) || VN_IS(actionsp, StmtExpr))) {
            actionsp->v3error("Observed deferred immediate assertion action block must be a "
                              "single subroutine call (IEEE 1800-2023 16.4).");
            VL_DO_DANGLING(pushDeletep(actionsp), actionsp);
            return nullptr;
        }
        AstStmtExpr* const stmtexprp = VN_CAST(actionsp, StmtExpr);
        AstNodeFTaskRef* const refp
            = stmtexprp ? VN_CAST(stmtexprp->exprp(), NodeFTaskRef) : nullptr;
        if (!(VN_IS(actionsp, Display) || VN_IS(actionsp, SFormat) || VN_IS(actionsp, SystemT)
              || VN_IS(actionsp, Stop) || VN_IS(actionsp, Finish) || refp)) {
            actionsp->v3warn(E_UNSUPPORTED,
                             "Unsupported: Observed deferred immediate assertion action.");
            VL_DO_DANGLING(pushDeletep(actionsp), actionsp);
            return nullptr;
        }
        AstNodeStmt* queuesp = nullptr;
        if (AstDisplay* const displayp = VN_CAST(actionsp, Display)) {
            if (displayp->filep()) snapshotObservedExpr(displayp->filep(), queuesp);
            snapshotObservedSFormatArgs(displayp->fmtp(), queuesp);
        } else if (AstSFormat* const sformatp = VN_CAST(actionsp, SFormat)) {
            snapshotObservedSFormatArgs(sformatp->fmtp(), queuesp);
        } else if (AstSystemT* const systemp = VN_CAST(actionsp, SystemT)) {
            snapshotObservedExpr(systemp->lhsp(), queuesp);
        } else if (refp) {
            // Match actuals to formal ports, including named/default arguments
            const V3TaskConnects tconnects
                = V3Task::taskConnects(refp, refp->taskp()->declsp(), nullptr, false);
            for (const auto& tconnect : tconnects) {
                AstVar* const portp = tconnect.first;
                AstArg* const argp = tconnect.second;
                if (portp->isRef() || portp->isConstRef()) {
                    if (argp->exprp()->exists([](const AstNodeVarRef* varrefp) {
                            return varrefp->varp()->lifetime().isAutomatic()
                                   || varrefp->varp()->dtypep()->skipRefp()->isDynamicallySized();
                        })) {
                        argp->exprp()->v3error(
                            "Observed deferred immediate assertion ref action argument cannot "
                            "have automatic or dynamic storage (IEEE 1800-2023 16.4).");
                    }
                } else if (portp->isNonOutput()) {
                    snapshotObservedExpr(argp->exprp(), queuesp);
                } else {
                    argp->exprp()->v3error("Observed deferred immediate assertion action "
                                           "argument must be input, ref, or const ref "
                                           "(IEEE 1800-2023 16.4).");
                }
            }
        }
        return newObservedDeferredCall(flp, actionsp, queuesp);
    }
    // Make statements pending, appending what queues them to queuesp
    AstNodeStmt* newObservedDeferredCall(FileLine* flp, AstNodeStmt* callsp,
                                         AstNodeStmt* queuesp) {
        AstVar* const pendingp
            = newModuleTemp(flp, m_obsNames.get("Pending"), m_modp->findUInt32DType(), m_modp);
        pendingp->setIgnoreSchedWrite();
        m_obsFlushp = AstNode::addNext(
            m_obsFlushp, new AstAssign{flp, new AstVarRef{flp, pendingp, VAccess::WRITE},
                                       new AstConst{flp, 0}});
        if (!m_obsEventp) {
            m_obsEventp = newModuleTemp(flp, m_obsNames.get("Event"),
                                        m_modp->findBasicDType(VBasicDTypeKwd::EVENT), m_modp);
            v3Global.setHasEvents();
            v3Global.setUsesTiming();
            m_obsReactivep = new AstAlwaysReactive{
                flp,
                new AstSenTree{flp,
                               new AstSenItem{flp, VEdgeType::ET_EVENT,
                                              new AstVarRef{flp, m_obsEventp, VAccess::READ}}},
                nullptr};
            m_modp->addStmtsp(m_obsReactivep);
        }
        queuesp = AstNode::addNext(
            queuesp, new AstAssign{flp, new AstVarRef{flp, pendingp, VAccess::WRITE},
                                   new AstAdd{flp, new AstVarRef{flp, pendingp, VAccess::READ},
                                              new AstConst{flp, 1}}});
        queuesp = AstNode::addNext(
            queuesp,
            new AstFireEvent{flp, new AstVarRef{flp, m_obsEventp, VAccess::WRITE}, false});

        AstLoop* const reactLoopp = new AstLoop{flp};
        reactLoopp->addStmtsp(
            new AstLoopTest{flp, reactLoopp, new AstVarRef{flp, pendingp, VAccess::READ}});
        reactLoopp->addStmtsp(new AstAssign{
            flp, new AstVarRef{flp, pendingp, VAccess::WRITE},
            new AstSub{flp, new AstVarRef{flp, pendingp, VAccess::READ}, new AstConst{flp, 1}}});
        reactLoopp->addStmtsp(callsp);
        m_obsReactivep->addStmtsp(reactLoopp);
        return queuesp;
    }

    void visitAssertionIterate(AstNodeCoverOrAssert* nodep, AstNodeStmt* failsp) {
        FileLine* const flp = nodep->fileline();
        const bool obsDeferred = nodep->userType() == VAssertType::OBSERVED_DEFERRED_IMMEDIATE;
        if (obsDeferred && (!v3Global.opt.timing().isSetTrue() || m_ftaskp || m_inSpawnedFork)) {
            if (v3Global.opt.timing().isSetFalse()) {
                nodep->v3warn(E_NOTIMING,
                              "Observed deferred immediate assertion requires --timing");
            } else if (!v3Global.opt.timing().isSetTrue()) {
                nodep->v3warn(E_NEEDTIMINGOPT,
                              "Use --timing or --no-timing to specify how observed deferred "
                              "immediate assertions should be handled");
            } else {
                // Under fork...join_any/join_none, instances of a branch may run at once, but
                // would share one queue
                nodep->v3warn(E_UNSUPPORTED,
                              "Unsupported: Observed deferred immediate assertion in "
                                  << (m_ftaskp ? "a task or function."
                                               : "fork...join_any or fork...join_none."));
            }
            VL_DO_DANGLING(pushDeletep(nodep->unlinkFrBack()), nodep);
            return;
        }
        if (m_beginp && nodep->name() == "") nodep->name(m_beginp->name());

        { AssertDeFutureVisitor{nodep->propp(), m_modp, m_modPastNum++}; }

        iterateAndNextNull(nodep->sentreep());
        if (AstAssert* const assertp = VN_CAST(nodep, Assert)) {
            iterateAndNextNull(assertp->failsp());
        } else if (AstAssertIntrinsic* const assertp = VN_CAST(nodep, AssertIntrinsic)) {
            iterateAndNextNull(assertp->failsp());
        } else if (AstCover* const coverp = VN_CAST(nodep, Cover)) {
            iterateAndNextNull(coverp->coverincsp());
        } else if (!VN_IS(nodep, Restrict)) {
            nodep->v3fatalSrc("Unhandled assert type");
        }
        iterateAndNextNull(nodep->passsp());
        AstSenTree* sentreep = nodep->sentreep();
        if (nodep->immediate()) {
            UASSERT_OBJ(!sentreep, nodep, "Immediate assertions don't have sensitivity");
        } else {
            UASSERT_OBJ(sentreep, nodep, "Concurrent assertions must have sensitivity");
            // Explicit inline clock differs from the enclosing always: hoist
            // and warn. To support this need queue of asserts to activate.
            if (m_procedurep && !nodep->senFromAlways()) {
                nodep->v3warn(E_UNSUPPORTED,
                              "Unsupported: Procedural concurrent assertion with"
                              " clocking event inside always (IEEE 1800-2023 16.14.6)");
                m_procedurep->addNext(
                    new AstAlways{flp, VAlwaysKwd::ASSERT_COVER, nullptr, nodep->unlinkFrBack()});
                return;  // Later iterate will pick up
            }
            // A task is not a process, so the assertion gets its own beside the task
            if (m_ftaskp) {
                m_ftaskp->addNextHere(
                    new AstAlways{flp, VAlwaysKwd::ASSERT_COVER, nullptr, nodep->unlinkFrBack()});
                return;  // Later iterate will pick up
            }
            sentreep->unlinkFrBack();
            if (m_procedurep) { VL_DO_DANGLING(pushDeletep(sentreep), sentreep); }
        }
        //
        const string& message = nodep->name();
        AstNodeStmt* passsp = nodep->passsp();
        if (passsp) passsp->unlinkFrBackWithNext();
        if (AstAssert* const assertp = VN_CAST(nodep, Assert)) {
            failsp = assertp->failsp();
        } else if (AstAssertIntrinsic* const assertp = VN_CAST(nodep, AssertIntrinsic)) {
            failsp = assertp->failsp();
        }
        if (failsp) failsp->unlinkFrBackWithNext();

        bool selfDestruct = false;
        bool passspGated = false;
        const AstCover* const coverp = VN_CAST(nodep, Cover);
        // A sequence event control is not an assertion directive; no assertion control
        const bool seqEvent = coverp && coverp->isSeqEvent();
        if (coverp) {
            ++m_statCover;
            if (seqEvent) {
                // Keep the event-fire action, with no coverage bucket
            } else if (!v3Global.opt.coverageUser()) {
                selfDestruct = true;
            } else {
                // V3Coverage assigned us a bucket to increment.
                AstCoverInc* const covincp = VN_AS(coverp->coverincsp(), CoverInc);
                UASSERT_OBJ(covincp, coverp, "Missing AstCoverInc under assertion");
                covincp->unlinkFrBackWithNext();  // next() might have  AstAssign for trace
                if (message != "") covincp->declp()->comment(message);
                // IEEE 1800-2023 16.4.2: Deferred coverage is flushed like a pending report
                AstNodeStmt* creditsp = covincp;
                if (obsDeferred) {
                    creditsp = newObservedDeferredCall(flp, covincp, nullptr);
                    if (passsp) passsp = newObservedDeferredAction(flp, passsp);
                }
                if (passsp) {
                    passsp = newIfAssertPassOn(passsp, nodep->directive(), nodep->userType(),
                                               /*vacuous=*/false);
                    passspGated = true;
                    passsp = AstNode::addNext(creditsp, passsp);
                } else {
                    passsp = creditsp;
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
            if (obsDeferred) {
                if (passsp) passsp = newObservedDeferredAction(flp, passsp);
                if (failsp) failsp = newObservedDeferredAction(flp, failsp);
            }
        } else {
            nodep->v3fatalSrc("Unknown node type");
        }

        VL_RESTORER(m_passsp);
        VL_RESTORER(m_failsp);
        VL_RESTORER(m_assertp);
        m_passsp = passsp;
        m_failsp = failsp;
        m_assertp = nodep;
        iterate(nodep->propp());

        AstNode* propExprp;
        AstNodeExpr* disablep = nullptr;
        AstNodeExpr* matchCountp = nullptr;
        if (AstPropSpec* const specp = VN_CAST(nodep->propp(), PropSpec)) {
            propExprp = specp->propp()->unlinkFrBack();
            if (specp->disablep()) disablep = specp->disablep()->unlinkFrBack();
            matchCountp = specp->matchCountp();
        } else {
            propExprp = nodep->propp()->unlinkFrBack();
        }
        bool passspAlreadyGated = false;
        if (passsp && VN_IS(passsp, If)) passspAlreadyGated = VN_AS(passsp, If)->user1();
        if (passsp && !passspGated && !passspAlreadyGated && !VN_IS(propExprp, PExpr)
            && !seqEvent) {
            passsp = newIfAssertPassOn(passsp, nodep->directive(), nodep->userType(),
                                       /*vacuous=*/false);
        }
        if (failsp && !VN_IS(propExprp, PExpr)) {
            failsp = newIfAssertFailOn(failsp, nodep->directive(), nodep->userType());
        }
        if (coverp && matchCountp && passsp) {
            // Convert the match count into a loop that decrements a temporary variable until it
            // reaches zero.
            matchCountp->unlinkFrBack();
            AstVar* const remainingp = new AstVar{
                flp, VVarType::MODULETEMP, m_matchCountNames.get(""), matchCountp->dtypep()};
            remainingp->lifetime(VLifetime::STATIC_EXPLICIT);
            m_modp->addStmtsp(remainingp);
            AstNodeStmt* const replaysp
                = new AstAssign{flp, new AstVarRef{flp, remainingp, VAccess::WRITE}, matchCountp};
            AstLoop* const loopp = new AstLoop{flp};
            loopp->addStmtsp(
                new AstLoopTest{flp, loopp, new AstVarRef{flp, remainingp, VAccess::READ}});
            loopp->addStmtsp(passsp);
            loopp->addStmtsp(
                new AstAssign{flp, new AstVarRef{flp, remainingp, VAccess::WRITE},
                              new AstSub{flp, new AstVarRef{flp, remainingp, VAccess::READ},
                                         new AstConst{flp, AstConst::WidthedValue{},
                                                      remainingp->dtypep()->width(), 1}}});
            replaysp->addNext(loopp);
            passsp = replaysp;
        }
        AstNodeStmt* bodysp = assertBody(nodep, propExprp, passsp, failsp);
        if (disablep) bodysp = new AstIf{flp, new AstLogNot{flp, disablep}, bodysp};
        // Add assertOn check last, for better combining
        if (!seqEvent) bodysp = newIfAssertOn(bodysp, nodep->directive(), nodep->userType());

        if (passsp && !passsp->backp()) VL_DO_DANGLING(pushDeletep(passsp), passsp);
        if (failsp && !failsp->backp()) VL_DO_DANGLING(pushDeletep(failsp), failsp);

        // Install it
        if (selfDestruct) {
            // Delete it after making the tree.  This way we can tell the user
            // if it wasn't constructed nicely or has other errors without needing --coverage.
            VL_DO_DANGLING(bodysp->deleteTree(), bodysp);
            if (sentreep) VL_DO_DANGLING(sentreep->deleteTree(), sentreep);
            nodep->unlinkFrBack();
        } else {
            if (sentreep) {
                // The process of the concurrent assertion is clocked by it
                UASSERT_OBJ(m_assertCoverp, nodep, "Concurrent assertion not in its process");
                m_assertCoverp->keyword(VAlwaysKwd::ALWAYS);
                m_assertCoverp->sentreep(sentreep);
            }
            nodep->replaceWith(bodysp);
        }
        // Bye
        VL_DO_DANGLING(pushDeletep(nodep), nodep);
    }

    bool isEmptyStmt(AstNode* nodep) {
        if (!nodep) return true;
        if (AstBegin* const beginp = VN_CAST(nodep, Begin)) {
            if (beginp->declsp()) return false;
            for (AstNode* const stmtp : beginp->stmtspList()) {
                if (!isEmptyStmt(stmtp)) return false;
            }
            return true;
        }
        return false;
    }

    // VISITORS
    void visit(AstIf* nodep) override {
        if (!nodep->user1SetOnce()) {
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

                const bool allow_none = nodep->unique0Pragma();

                // Empty case means no property
                if (!propp) propp = new AstConst{nodep->fileline(), AstConst::BitFalse{}};

                // Note: if this ends with an 'else', then we don't need to validate that one of
                // the predicates evaluates to true.
                AstNodeExpr* const ohotp
                    = ((allow_none || hasDefaultElse)
                           ? static_cast<AstNodeExpr*>(new AstOneHot0{nodep->fileline(), propp})
                           : static_cast<AstNodeExpr*>(new AstOneHot{nodep->fileline(), propp}));
                const VAssertType assertType
                    = nodep->uniquePragma() ? VAssertType::UNIQUE : VAssertType::UNIQUE0;
                // Move, not clone, as the branches might declare referenced variables
                VNRelinker relinker;
                nodep->unlinkFrBack(&relinker);
                AstIf* const checkifp
                    = new AstIf{nodep->fileline(), new AstLogNot{nodep->fileline(), ohotp},
                                newFireAssert(nodep, VAssertDirectiveType::VIOLATION_IF,
                                              assertType, "'unique if' statement violated"),
                                nodep};
                checkifp->isBoundsCheck(true);  // To avoid LATCH warning
                checkifp->branchPred(VBranchPred::BP_UNLIKELY);
                relinker.relink(checkifp);
                return;
            }
        }

        iterateChildren(nodep);

        if (nodep->user2()) {
            // Combine consecutive assertOn checks if possible
            if (AstIf* const backp = VN_CAST(nodep->backp(), If)) {
                if (backp->nextp() == nodep  //
                    && backp->user2()  //
                    && backp->condp()->sameTree(nodep->condp())) {
                    ++m_statAssertOnCombined;
                    backp->addThensp(nodep->thensp()->unlinkFrBackWithNext());
                    nodep->unlinkFrBack();
                    VL_DO_DANGLING(pushDeletep(nodep), nodep);
                    return;
                }
            }
            // Combine nested assertOn checks if possible
            if (nodep->thensp() && !nodep->thensp()->nextp() && isEmptyStmt(nodep->elsesp())) {
                AstIf* const checkp = VN_CAST(nodep->thensp(), If);
                if (checkp  //
                    && checkp->user2()  //
                    && checkp->condp()->sameTree(nodep->condp())) {
                    ++m_statAssertOnCombined;
                    nodep->addThensp(checkp->thensp()->unlinkFrBackWithNext());
                    VL_DO_DANGLING(pushDeletep(checkp->unlinkFrBack()), checkp);
                    return;
                }
            }
            return;
        }

        // Swap assertOn check with single statement 'if' statement to bubble up for combining
        // Note we can't just swap the conditions as they two Ifs have different flags,
        // so swapping the Ifs themeselves then swapping back the bodies.
        if (nodep->condp()->isPure()) {
            if (nodep->thensp() && !nodep->thensp()->nextp() && isEmptyStmt(nodep->elsesp())) {
                AstIf* const checkp = VN_CAST(nodep->thensp(), If);
                if (checkp && checkp->user2()) {
                    ++m_statAssertOnHoisted;
                    nodep->replaceWith(checkp->unlinkFrBack());
                    nodep->addThensp(checkp->thensp()->unlinkFrBackWithNext());
                    checkp->addThensp(nodep);
                    return;
                }
            }
            if (nodep->elsesp() && !nodep->elsesp()->nextp() && isEmptyStmt(nodep->thensp())) {
                AstIf* const checkp = VN_CAST(nodep->elsesp(), If);
                if (checkp && checkp->user2()) {
                    ++m_statAssertOnHoisted;
                    nodep->replaceWith(checkp->unlinkFrBack());
                    nodep->addElsesp(checkp->thensp()->unlinkFrBackWithNext());
                    checkp->addThensp(nodep);
                    return;
                }
            }
        }
    }

    //========== Case assertions
    void visit(AstCase* nodep) override {
        // Introduce temporary variable for AstCase if needed - it is done here and not in V3Case
        // because this phase is before V3Scope and V3Case is not. Doing it before V3Scope ensures
        // that V3Scope will take care of a scope creation
        // We also need to do it before V3Begin, co that pragmas like `unique0` also work correctly
        if (!nodep->exprp()->isPure()) {
            ++m_statLiftedCaseExprs;
            FileLine* const fl = nodep->exprp()->fileline();
            AstVar* const varp = new AstVar{fl, VVarType::BLOCKTEMP, m_caseTempNames.get(nodep),
                                            nodep->exprp()->dtypep()};
            AstNodeExpr* const origp = nodep->exprp()->unlinkFrBack();
            nodep->addHereThisAsNext(
                new AstAssign{fl, new AstVarRef{fl, varp, VAccess::WRITE}, origp});
            nodep->exprp(new AstVarRef{fl, varp, VAccess::READ});
            if (m_ftaskp) {
                varp->funcLocal(true);
                varp->lifetime(VLifetime::AUTOMATIC_EXPLICIT);
                m_ftaskp->prependDeclsp(varp);
            } else {
                m_modp->prependStmtsp(varp);
            }
            VIsCached::clearCacheTree();
        }
        iterateChildren(nodep);
        if (!nodep->user1SetOnce()) {
            bool has_default = false;
            for (AstCaseItem* const itemp : nodep->itemspList()) {
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
                    for (AstCaseItem* const itemp : nodep->itemspList()) {
                        AstNodeExpr* itembitp = nullptr;
                        for (AstNodeExpr* const icondp : itemp->condspList()) {
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
                    AstNodeExpr* const ohotp = new AstOneHot{nodep->fileline(), propp};
                    AstConst* const zerop = new AstConst{
                        nodep->fileline(), AstConst::WidthedValue{}, propp->width(), 0};
                    AstIf* const ohotIfp
                        = new AstIf{nodep->fileline(), new AstLogNot{nodep->fileline(), ohotp}};
                    AstIf* const zeroIfp = new AstIf{
                        nodep->fileline(),
                        new AstEq{nodep->fileline(), propp->cloneTreePure(false), zerop}};
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
        if (!nodep->propertyTiming()) {
            nodep->initp(nodep->exprp()->cloneTreePure(false));
            { DefaultSampledValueVisitor{nodep->initp()}; }
        }
        AstNodeExpr* const initp = nodep->initp() ? nodep->initp()->unlinkFrBack() : nullptr;
        iterateChildren(nodep);
        uint32_t ticks = 1;
        if (nodep->ticksp()) {
            UASSERT_OBJ(VN_IS(nodep->ticksp(), Const), nodep,
                        "Expected constant ticks, checked in V3Width");
            ticks = VN_AS(nodep->ticksp(), Const)->toUInt();
        }
        UASSERT_OBJ(ticks >= 1, nodep, "0 tick should have been checked in V3Width");
        AstNodeExpr* const exprp = newSampledExpr(nodep->exprp()->unlinkFrBack());
        AstSenTree* const senTreep = nodep->sentreep()->unlinkFrBack();
        AstNodeExpr* inp = nullptr;
        // Deliberately emitted for every ftask $past; calls outside final take the normal stage
        if (VN_IS(m_procedurep, Final) || m_ftaskp) {
            // A sampling-tick finish reads one stage deeper (IEEE 1800-2023 16.9.3).
            FileLine* const flp = nodep->fileline();
            AstAlways* const alwaysp
                = getDelayedAlways(exprp, initp ? initp->cloneTreePure(false) : nullptr, senTreep);
            AstNodeExpr* const betweenTicksp = pastValueRef(alwaysp, flp, ticks, initp);
            AstNodeExpr* const onTickp = pastValueRef(alwaysp, flp, ticks + 1, initp);
            if (initp) VL_DO_DANGLING(pushDeletep(initp), initp);
            AstNodeExpr* const onTickCondp = new AstLogAnd{
                flp, new AstCExpr{flp, "vlSymsp->_vm_contextp__->executingFinal()", 1},
                new AstEq{flp, new AstVarRef{flp, getPastTickTimeVar(alwaysp), VAccess::READ},
                          new AstCExpr{flp, "vlSymsp->_vm_contextp__->finishPendingTime()", 64}}};
            AstCond* const condp = new AstCond{flp, onTickCondp, onTickp, betweenTicksp};
            condp->dtypeFrom(onTickp);
            inp = condp;
        } else {
            inp = getPastValue(exprp, initp, senTreep, ticks);
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
        if (nodep->exprp()) {
            nodep->replaceWith(nodep->exprp()->unlinkFrBack());
        } else {
            nodep->unlinkFrBack();
        }
        VL_DO_DANGLING(pushDeletep(nodep), nodep);
    }
    void visit(AstNodeVarRef* nodep) override {
        if (m_inSampled && !nodep->user2() && !nodep->varp()->isTemp()) {
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
        AstNodeStmt* stmtsp = nullptr;
        if (nodep->pass() && m_passsp) {
            // Cover adds COVERINC by AstNode::addNext, thus need to clone next too.
            stmtsp = m_passsp->cloneTree(true);
            stmtsp = newIfAssertPassOn(stmtsp, m_assertp->directive(), m_assertp->userType(),
                                       nodep->vacuous());
        } else if (!nodep->pass() && m_failsp) {
            stmtsp = m_failsp->cloneTree(true);
            stmtsp = newIfAssertFailOn(stmtsp, m_assertp->directive(), m_assertp->userType());
        }
        if (stmtsp) {
            stmtsp->foreachAndNext([](AstNodeVarRef* const refp) {
                // References inside action blocks shouldn't be implicitly sampled
                // m_passsp/m_failsp have been already visited once and refs explicitly sampled
                // are handled already
                refp->user2(1);
            });
            nodep->replaceWith(stmtsp);
        } else {
            nodep->unlinkFrBack();
        }
        VL_DO_DANGLING(pushDeletep(nodep), nodep);
    }
    void visit(AstPExpr* nodep) override {
        if (m_inRestrict) {
            VL_DO_DANGLING(pushDeletep(nodep->unlinkFrBack()), nodep);
        } else {
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
            FileLine* const fl = nodep->fileline();

            const auto monNum = ++m_monitorNum;
            // Where $monitor was we do "__VmonitorNum = N; __VmonitorPending = '1;", so it is
            // displayed when invoked
            AstAssign* const newsetp = new AstAssign{
                fl, newMonitorNumVarRefp(nodep, VAccess::WRITE), new AstConst{fl, monNum}};
            newsetp->addNext(newMonitorPendingSetp(nodep));
            nodep->replaceWith(newsetp);
            // Add "always @(args) if (__VmonitorNum == N) __VmonitorPending = '1;"
            AstSenItem* monSenItemsp = nullptr;
            if (AstNode* const monExprsp = nodep->fmtp()->exprsp()) {
                monExprsp->foreachAndNext([&](AstVarRef* varrefp) {
                    AstSenItem* const senItemp
                        = new AstSenItem{fl, VEdgeType::ET_CHANGED,
                                         // Clone so get VarRef or VarXRef as needed
                                         varrefp->cloneTree(false)};
                    monSenItemsp = AstNode::addNextNull(monSenItemsp, senItemp);
                });
            }
            if (monSenItemsp) {
                AstNodeExpr* const activep = new AstEq{fl, new AstConst{fl, monNum},
                                                       newMonitorNumVarRefp(nodep, VAccess::READ)};
                AstIf* const setIfp = new AstIf{fl, activep, newMonitorPendingSetp(nodep)};
                AstSenTree* const monSenTreep = new AstSenTree{fl, monSenItemsp};
                m_modp->addStmtsp(new AstAlways{fl, VAlwaysKwd::ALWAYS, monSenTreep, setIfp});
            }
            // Display once at the end of the time step (IEEE 1800-2023 21.2.3), like $strobe:
            // "always_postponed if (__VmonitorPending && __VmonitorNum == N) begin
            //    __VmonitorPending = '0; if (!__VmonitorOff) $display(...); end"
            AstNodeExpr* const pendingp
                = new AstLogAnd{fl, newMonitorPendingVarRefp(nodep, VAccess::READ),
                                new AstEq{fl, new AstConst{fl, monNum},
                                          newMonitorNumVarRefp(nodep, VAccess::READ)}};
            AstNodeExpr* const onp = new AstLogNot{fl, newMonitorOffVarRefp(nodep, VAccess::READ)};
            AstIf* const onIfp = new AstIf{fl, onp, nodep};
            onIfp->isBoundsCheck(true);  // To avoid LATCH warning
            AstAssign* const clearp
                = new AstAssign{fl, newMonitorPendingVarRefp(nodep, VAccess::WRITE),
                                new AstConst{fl, AstConst::BitFalse{}}};
            AstIf* const ifp = new AstIf{fl, pendingp, clearp};
            ifp->addThensp(onIfp);
            ifp->isBoundsCheck(true);  // To avoid LATCH warning
            ifp->branchPred(VBranchPred::BP_UNLIKELY);
            m_modp->addStmtsp(new AstAlwaysPostponed{fl, ifp});
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
            AstNodeStmt* const stmtsp = nodep;
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
        FileLine* const flp = nodep->fileline();
        AstAssign* const newp
            = new AstAssign{flp, newMonitorOffVarRefp(nodep, VAccess::WRITE),
                            new AstConst{flp, AstConst::BitTrue{}, nodep->off()}};
        // $monitoron displays immediately (IEEE 1800-2023 21.2.3)
        if (!nodep->off()) newp->addNext(newMonitorPendingSetp(nodep));
        nodep->replaceWith(newp);
        VL_DO_DANGLING(pushDeletep(nodep), nodep);
    }
    void visit(AstEventControl* nodep) override {
        iterateChildren(nodep);
        m_obsWaitsp.push_back(nodep);
    }
    void visit(AstWait* nodep) override {
        iterateChildren(nodep);
        m_obsWaitsp.push_back(nodep);
    }
    void visit(AstWaitFork* nodep) override {
        iterateChildren(nodep);
        m_obsWaitsp.push_back(nodep);
    }
    void visit(AstDisableTargetBody* nodep) override {
        iterateChildren(nodep);
        // V3LinkJump wraps only the body of a process's outermost scope. Running to its end
        // means the scope was not disabled.
        if (m_obsFlushp) {
            FileLine* const flp = nodep->fileline();
            m_obsDoneVarp
                = newModuleTemp(flp, m_obsNames.get("Done"), m_modp->findBitDType(), m_modp);
            m_obsDoneVarp->setIgnoreSchedWrite();
            nodep->addStmtsp(new AstAssign{flp, new AstVarRef{flp, m_obsDoneVarp, VAccess::WRITE},
                                           new AstConst{flp, AstConst::BitTrue{}}});
        }
        UASSERT_OBJ(nodep->stmtsp(), nodep, "V3LinkJump wraps only a non-empty body");
        nodep->addNextHere(nodep->stmtsp()->unlinkFrBackWithNext());
        VL_DO_DANGLING(pushDeletep(nodep->unlinkFrBack()), nodep);
    }
    void visit(AstFork* nodep) override {
        iterateAndNextNull(nodep->declsp());
        iterateAndNextNull(nodep->stmtsp());
        VL_RESTORER(m_inSpawnedFork);
        m_inSpawnedFork |= !nodep->joinType().join();
        for (AstForkItem* const branchp : nodep->forkspList()) {
            // V3LinkJump's wrapper runs part of the enclosing process
            if (branchp->disableWrapper()) {
                iterate(branchp);
                continue;
            }
            // IEEE 1800-2023 9.3.2: Each branch is a separate process
            VL_RESTORER(m_obsFlushp);
            VL_RESTORER(m_obsDoneVarp);
            VL_RESTORER_CLEAR(m_obsWaitsp);
            m_obsFlushp = nullptr;
            m_obsDoneVarp = nullptr;
            iterate(branchp);
            addObsFlushes(branchp);
        }
    }
    void visit(AstAssert* nodep) override {  //
        visitAssertionIterate(nodep, nodep->failsp());
    }
    void visit(AstAssertCtl* nodep) override {
        iterateChildren(nodep);

        bool assertTypeConst = true;
        if (!nodep->assertTypesp()) {
            nodep->assertTypes(VAssertType{ALL_ASSERT_TYPES});
        } else if (const AstConst* const assertTypesp = VN_CAST(nodep->assertTypesp(), Const)) {
            nodep->assertTypes(VAssertType{assertTypesp->toSInt()});
        } else {
            assertTypeConst = false;
        }

        bool controlTypeConst = false;
        if (const AstConst* const constp = VN_CAST(nodep->controlTypep(), Const)) {
            nodep->ctlType(constp->toSInt());
            controlTypeConst = true;
        }
        if (controlTypeConst
            && (nodep->ctlType() < VAssertCtlType::LOCK
                || nodep->ctlType() > VAssertCtlType::VACUOUS_OFF)) {
            nodep->unlinkFrBack();
            nodep->v3error("Bad $assertcontrol control_type '"
                           << cvtToStr(static_cast<int>(nodep->ctlType()))
                           << "' (IEEE 1800-2023 Table 20-5)");
            VL_DO_DANGLING(pushDeletep(nodep), nodep);
            return;
        }
        if (assertTypeConst && nodep->assertTypes() != ALL_ASSERT_TYPES
            && nodep->assertTypes().containsAny(VAssertType::UNIQUE | VAssertType::UNIQUE0
                                                | VAssertType::PRIORITY)) {
            nodep->v3warn(E_UNSUPPORTED, "Unsupported: assert control assertion_type");
            VL_DO_DANGLING(pushDeletep(nodep->unlinkFrBack()), nodep);
            return;
        }

        bool directiveTypeConst = true;
        if (!nodep->directiveTypesp()) {
            nodep->directiveTypes(VAssertDirectiveType::ASSERT | VAssertDirectiveType::ASSUME
                                  | VAssertDirectiveType::COVER);
        } else if (const AstConst* const directiveTypesp
                   = VN_CAST(nodep->directiveTypesp(), Const)) {
            nodep->directiveTypes(VAssertDirectiveType{directiveTypesp->toSInt()});
        } else {
            directiveTypeConst = false;
        }
        if (!directiveTypeConst) {
            nodep->v3warn(E_UNSUPPORTED,
                          "Unsupported: non-const assert directive type expression");
            VL_DO_DANGLING(pushDeletep(nodep->unlinkFrBack()), nodep);
            return;
        }

        FileLine* const fl = nodep->fileline();
        UINFO(9, "Generating assertctl for a module: " << m_modp);
        AstCStmt* const newp = new AstCStmt{fl};
        newp->add("vlSymsp->_vm_contextp__->assertCtl(");
        newp->add(nodep->controlTypep()->unlinkFrBack());
        newp->add(", ");
        if (nodep->assertTypesp()) {
            newp->add(nodep->assertTypesp()->unlinkFrBack());
        } else {
            newp->add(std::to_string(ALL_ASSERT_TYPES));
        }
        newp->add(", " + std::to_string(nodep->directiveTypes()) + ");\n");
        nodep->replaceWith(newp);
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
        VL_RESTORER_COPY(m_obsNames);
        VL_RESTORER(m_obsFlushp);
        VL_RESTORER(m_obsEventp);
        VL_RESTORER(m_obsReactivep);
        VL_RESTORER(m_modPastNum);
        VL_RESTORER(m_modStrobeNum);
        VL_RESTORER(m_finalp);
        VL_RESTORER_CLEAR(m_modExpr2Sen2DelayedAlwaysp);
        VL_RESTORER_CLEAR(m_modExpr2Sen2DefaultDelayedAlwaysp);
        VL_RESTORER_CLEAR(m_delayedAlways2TickTimep);
        m_modp = nodep;
        m_modPastNum = 0;
        m_obsNames.reset();
        m_obsFlushp = nullptr;
        m_obsEventp = nullptr;
        m_obsReactivep = nullptr;
        m_modStrobeNum = 0;
        m_finalp = nullptr;
        iterateChildren(nodep);
    }
    void visit(AstAlways* nodep) override {
        if (nodep->keyword() != VAlwaysKwd::ASSERT_COVER) {
            visit(static_cast<AstNodeProcedure*>(nodep));
            return;
        }
        // The process of a concurrent assertion, not a procedural context. The assertion clocks
        // it, or it goes with the assertion.
        VL_RESTORER(m_assertCoverp);
        m_assertCoverp = nodep;
        iterateChildren(nodep);
        if (nodep->keyword() == VAlwaysKwd::ASSERT_COVER) {
            VL_DO_DANGLING(pushDeletep(nodep->unlinkFrBack()), nodep);
        }
    }
    void visit(AstNodeProcedure* nodep) override {
        VL_RESTORER(m_procedurep);
        VL_RESTORER(m_obsFlushp);
        VL_RESTORER(m_obsDoneVarp);
        VL_RESTORER_CLEAR(m_obsWaitsp);
        m_procedurep = nodep;
        AstBegin* const scopep = VN_CAST(nodep->stmtsp(), Begin);
        iterateChildren(nodep);
        // IEEE 1800-2023 16.4.2: The process resumes from its event control, or was declared by
        // an always_comb or always_latch and is resumed due to a transition on one of its
        // dependent signals.
        if (AstAlways* const alwaysp = VN_CAST(nodep, Always)) {
            if (alwaysp->stmtsp()
                && (alwaysp->sentreep() || alwaysp->keyword() == VAlwaysKwd::ALWAYS_COMB
                    || alwaysp->keyword() == VAlwaysKwd::ALWAYS_LATCH)) {
                addResumeFlush(alwaysp);
            }
        }
        addObsFlushes(scopep);
    }
    void visit(AstNodeFTask* nodep) override {
        VL_RESTORER(m_ftaskp);
        VL_RESTORER(m_obsFlushp);
        m_ftaskp = nodep;
        m_obsFlushp = nullptr;
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
        // If the body is a single assertOn check, bubble it up for combining
        if (!nodep->declsp()) {
            if (AstIf* const ifp = VN_CAST(nodep->stmtsp(), If)) {
                if (ifp->user2() && !ifp->nextp()) {
                    ++m_statAssertOnHoisted;
                    nodep->replaceWith(ifp->unlinkFrBack());
                    nodep->addStmtsp(ifp->thensp()->unlinkFrBackWithNext());
                    ifp->addThensp(nodep);
                }
            }
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
        V3Stats::addStat("Assertions, $past variables", m_statPastVars);
        V3Stats::addStat("Assertions, assertOn checks combined", m_statAssertOnCombined);
        V3Stats::addStat("Assertions, assertOn checks hoisted", m_statAssertOnHoisted);
        V3Stats::addStat("Assertions, lifted impure case expressions", m_statLiftedCaseExprs);
        // Rewrites can change purity, e.g. by compiling out assertion statements with --no-assert
        VIsCached::clearCacheTree();
    }
};

//######################################################################
// Top Assert class

void V3Assert::assertAll(AstNetlist* nodep) {
    UINFO(2, __FUNCTION__ << ":");
    { AssertVisitor{nodep}; }  // Destruct before checking
    V3Global::dumpCheckGlobalTree("assert", 0, dumpTreeEitherLevel() >= 3);
}
