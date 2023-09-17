// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Collect and print statistics
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2005-2023 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************
//  Pre steps:
//      Attach clocks to each assertion
//      Substitute property references by property body (IEEE Std 1800-2012, section 16.12.1).
//      Transform clocking blocks into imperative logic
//*************************************************************************

#include "config_build.h"
#include "verilatedos.h"

#include "V3AssertPre.h"

#include "V3Ast.h"
#include "V3Const.h"
#include "V3Global.h"
#include "V3Task.h"
#include "V3UniqueNames.h"

VL_DEFINE_DEBUG_FUNCTIONS;

//######################################################################
// Assert class functions

class AssertPreVisitor final : public VNVisitor {
    // Removes clocks and other pre-optimizations
    // Eventually inlines calls to sequences, properties, etc.
    // We're not parsing the tree, or anything more complicated.
private:
    // NODE STATE
    const VNUser1InUse m_inuser1;
    // STATE
    // Current context:
    AstNetlist* const m_netlistp = nullptr;  // Current netlist
    AstNodeModule* m_modp = nullptr;  // Current module
    AstClocking* m_clockingp = nullptr;  // Current clocking block
    // Reset each module:
    AstClocking* m_defaultClockingp = nullptr;  // Default clocking for the current module
    // Reset each assertion:
    AstSenItem* m_senip = nullptr;  // Last sensitivity
    // Reset each always:
    AstSenItem* m_seniAlwaysp = nullptr;  // Last sensitivity in always
    // Reset each assertion:
    AstNodeExpr* m_disablep = nullptr;  // Last disable
    // Other:
    V3UniqueNames m_cycleDlyNames{"__VcycleDly"};  // Cycle delay counter name generator
    bool m_inAssign = false;  // True if in an AssignNode
    bool m_inAssignDlyLhs = false;  // True if in AssignDly's LHS
    bool m_inSynchDrive = false;  // True if in synchronous drive

    // METHODS

    AstSenTree* newSenTree(AstNode* nodep, AstSenTree* useTreep = nullptr) {
        // Create sentree based on clocked or default clock
        // Return nullptr for always
        if (useTreep) return useTreep;
        AstSenTree* newp = nullptr;
        AstSenItem* senip = m_senip;
        if (!senip && m_defaultClockingp) senip = m_defaultClockingp->sensesp();
        if (!senip) senip = m_seniAlwaysp;
        if (!senip) {
            nodep->v3warn(E_UNSUPPORTED, "Unsupported: Unclocked assertion");
            newp = new AstSenTree{nodep->fileline(), nullptr};
        } else {
            newp = new AstSenTree{nodep->fileline(), senip->cloneTree(true)};
        }
        return newp;
    }
    void clearAssertInfo() {
        m_senip = nullptr;
        m_disablep = nullptr;
    }
    AstPropSpec* getPropertyExprp(const AstProperty* const propp) {
        // The only statements possible in AstProperty are AstPropSpec (body)
        // and AstVar (arguments).
        AstNode* propExprp = propp->stmtsp();
        while (VN_IS(propExprp, Var)) propExprp = propExprp->nextp();
        return VN_CAST(propExprp, PropSpec);
    }
    void replaceVarRefsWithExprRecurse(AstNode* const nodep, const AstVar* varp,
                                       AstNode* const exprp) {
        if (!nodep) return;
        if (const AstVarRef* varrefp = VN_CAST(nodep, VarRef)) {
            if (varp == varrefp->varp()) nodep->replaceWith(exprp->cloneTree(false));
        }
        replaceVarRefsWithExprRecurse(nodep->op1p(), varp, exprp);
        replaceVarRefsWithExprRecurse(nodep->op2p(), varp, exprp);
        replaceVarRefsWithExprRecurse(nodep->op3p(), varp, exprp);
        replaceVarRefsWithExprRecurse(nodep->op4p(), varp, exprp);
    }
    AstPropSpec* substitutePropertyCall(AstPropSpec* nodep) {
        if (AstFuncRef* const funcrefp = VN_CAST(nodep->propp(), FuncRef)) {
            if (AstProperty* const propp = VN_CAST(funcrefp->taskp(), Property)) {
                AstPropSpec* propExprp = getPropertyExprp(propp);
                // Substitute inner property call before copying in order to not doing the same for
                // each call of outer property call.
                propExprp = substitutePropertyCall(propExprp);
                // Clone subtree after substitution. It is needed, because property might be called
                // multiple times with different arguments.
                propExprp = propExprp->cloneTree(false);
                // Substitute formal arguments with actual arguments
                const V3TaskConnects tconnects = V3Task::taskConnects(funcrefp, propp->stmtsp());
                for (const auto& tconnect : tconnects) {
                    const AstVar* const portp = tconnect.first;
                    AstArg* const argp = tconnect.second;
                    AstNode* const pinp = argp->exprp()->unlinkFrBack();
                    replaceVarRefsWithExprRecurse(propExprp, portp, pinp);
                }
                // Handle case with 2 disable iff statement (IEEE 1800-2017 16.12.1)
                if (nodep->disablep() && propExprp->disablep()) {
                    nodep->v3error("disable iff expression before property call and in its "
                                   "body is not legal");
                    pushDeletep(propExprp->disablep()->unlinkFrBack());
                }
                // If disable iff is in outer property, move it to inner
                if (nodep->disablep()) {
                    AstNodeExpr* const disablep = nodep->disablep()->unlinkFrBack();
                    propExprp->disablep(disablep);
                }

                if (nodep->sensesp() && propExprp->sensesp()) {
                    nodep->v3warn(E_UNSUPPORTED,
                                  "Unsupported: Clock event before property call and in its body");
                    pushDeletep(propExprp->sensesp()->unlinkFrBack());
                }
                // If clock event is in outer property, move it to inner
                if (nodep->sensesp()) {
                    AstSenItem* const sensesp = nodep->sensesp();
                    sensesp->unlinkFrBack();
                    propExprp->sensesp(sensesp);
                }

                // Now substitute property reference with property body
                nodep->replaceWith(propExprp);
                return propExprp;
            }
        }
        return nodep;
    }

    // VISITORS
    //========== Statements
    void visit(AstClocking* const nodep) override {
        VL_RESTORER(m_clockingp);
        m_clockingp = nodep;
        UINFO(8, "   CLOCKING" << nodep << endl);
        iterateChildren(nodep);
    }
    void visit(AstClockingItem* const nodep) override {
        FileLine* const flp = nodep->fileline();
        V3Const::constifyEdit(nodep->skewp());
        if (!VN_IS(nodep->skewp(), Const)) {
            nodep->skewp()->v3error("Skew must be constant (IEEE 1800-2017 14.4)");
            VL_DO_DANGLING(nodep->unlinkFrBack()->deleteTree(), nodep);
            return;
        }
        AstConst* const skewp = VN_AS(nodep->skewp(), Const);
        if (skewp->num().isNegative()) skewp->v3error("Skew cannot be negative");
        AstNodeExpr* const exprp = nodep->exprp();
        // Get a ref to the sampled/driven variable
        AstVar* const varp = nodep->varp()->unlinkFrBack();
        m_clockingp->addVarsp(varp);
        varp->user1p(nodep);
        if (nodep->direction() == VDirection::OUTPUT) {
            AstVarRef* const skewedRefp = new AstVarRef{flp, varp, VAccess::READ};
            skewedRefp->user1(true);
            AstAssign* const assignp = new AstAssign{flp, exprp->cloneTreePure(false), skewedRefp};
            if (skewp->isZero()) {
                // Drive the var in Re-NBA (IEEE 1800-2017 14.16)
                m_clockingp->addNextHere(new AstAlwaysReactive{
                    flp, new AstSenTree{flp, m_clockingp->sensesp()->cloneTree(false)}, assignp});
            } else if (skewp->fileline()->timingOn()) {
                // Create a fork so that this AlwaysObserved can be retriggered before the
                // assignment happens. Also then it can be combo, avoiding the need for creating
                // new triggers.
                AstFork* const forkp = new AstFork{flp, "", assignp};
                forkp->joinType(VJoinType::JOIN_NONE);
                // Use Observed for this to make sure we do not miss the event
                m_clockingp->addNextHere(new AstAlwaysObserved{
                    flp, new AstSenTree{flp, m_clockingp->sensesp()->cloneTree(false)}, forkp});
                if (v3Global.opt.timing().isSetTrue()) {
                    assignp->timingControlp(new AstDelay{flp, skewp->unlinkFrBack(), false});
                } else if (v3Global.opt.timing().isSetFalse()) {
                    nodep->v3warn(E_NOTIMING,
                                  "Clocking output skew greater than #0 requires --timing");
                } else {
                    nodep->v3warn(E_NEEDTIMINGOPT,
                                  "Use --timing or --no-timing to specify how "
                                  "clocking output skew greater than #0 should be handled");
                }
            }
        } else if (nodep->direction() == VDirection::INPUT) {
            // Ref to the clockvar
            AstVarRef* const refp = new AstVarRef{flp, varp, VAccess::WRITE};
            refp->user1(true);
            if (skewp->num().is1Step()) {
                // Assign the sampled expression to the clockvar (IEEE 1800-2017 14.13)
                AstSampled* const sampledp = new AstSampled{flp, exprp->cloneTreePure(false)};
                sampledp->dtypeFrom(exprp);
                m_clockingp->addNextHere(new AstAssignW{flp, refp, sampledp});
            } else if (skewp->isZero()) {
                // #0 means the var has to be sampled in Observed (IEEE 1800-2017 14.13)
                AstAssign* const assignp = new AstAssign{flp, refp, exprp->cloneTreePure(false)};
                m_clockingp->addNextHere(new AstAlwaysObserved{
                    flp, new AstSenTree{flp, m_clockingp->sensesp()->cloneTree(false)}, assignp});
            } else {
                // Create a queue where we'll store sampled values with timestamps
                AstSampleQueueDType* const queueDtp
                    = new AstSampleQueueDType{flp, exprp->dtypep()};
                m_netlistp->typeTablep()->addTypesp(queueDtp);
                AstVar* const queueVarp = new AstVar{
                    flp, VVarType::MODULETEMP,
                    "__Vqueue__" + m_clockingp->name() + "__DOT__" + varp->name(), queueDtp};
                m_clockingp->addNextHere(queueVarp);
                // Create a process like this:
                //     always queue.push(<sampled var>);
                AstCMethodHard* const pushp = new AstCMethodHard{
                    flp, new AstVarRef{flp, queueVarp, VAccess::WRITE}, "push",
                    new AstTime{nodep->fileline(), m_modp->timeunit()}};
                pushp->addPinsp(exprp->cloneTreePure(false));
                pushp->dtypeSetVoid();
                m_clockingp->addNextHere(
                    new AstAlways{flp, VAlwaysKwd::ALWAYS, nullptr, pushp->makeStmt()});
                // Create a process like this:
                //     always @<clocking event> queue.pop(<skew>, /*out*/<skewed var>});
                AstCMethodHard* const popp = new AstCMethodHard{
                    flp, new AstVarRef{flp, queueVarp, VAccess::READWRITE}, "pop",
                    new AstTime{nodep->fileline(), m_modp->timeunit()}};
                popp->addPinsp(skewp->unlinkFrBack());
                popp->addPinsp(refp);
                popp->dtypeSetVoid();
                m_clockingp->addNextHere(
                    new AstAlways{flp, VAlwaysKwd::ALWAYS,
                                  new AstSenTree{flp, m_clockingp->sensesp()->cloneTree(false)},
                                  popp->makeStmt()});
            }
        } else {
            nodep->v3fatal("Invalid direction");
        }
        pushDeletep(nodep->unlinkFrBack());
    }
    void visit(AstDelay* nodep) override {
        // Only cycle delays are relevant in this stage; also only process once
        if (!nodep->isCycleDelay()) {
            if (m_inSynchDrive) {
                nodep->v3error("Only cycle delays can be used in synchronous drives"
                               " (IEEE 1800-2017 14.16)");
            }
            return;
        }
        if (m_inAssign && !m_inSynchDrive) {
            nodep->v3error("Cycle delays not allowed as intra-assignment delays"
                           " (IEEE 1800-2017 14.11)");
            VL_DO_DANGLING(nodep->unlinkFrBack()->deleteTree(), nodep);
            return;
        }
        if (nodep->stmtsp()) nodep->addNextHere(nodep->stmtsp()->unlinkFrBackWithNext());
        FileLine* const flp = nodep->fileline();
        AstNodeExpr* valuep = V3Const::constifyEdit(nodep->lhsp()->unlinkFrBack());
        AstConst* const constp = VN_CAST(valuep, Const);
        if (constp->isZero()) {
            nodep->v3warn(E_UNSUPPORTED, "Unsupported: ##0 delays");
            VL_DO_DANGLING(nodep->unlinkFrBack()->deleteTree(), nodep);
            return;
        }
        if (!m_defaultClockingp) {
            nodep->v3error("Usage of cycle delays requires default clocking"
                           " (IEEE 1800-2017 14.11)");
            VL_DO_DANGLING(nodep->unlinkFrBack()->deleteTree(), nodep);
            return;
        }
        AstEventControl* const controlp = new AstEventControl{
            nodep->fileline(),
            new AstSenTree{flp, m_defaultClockingp->sensesp()->cloneTree(false)}, nullptr};
        const std::string delayName = m_cycleDlyNames.get(nodep);
        AstVar* const cntVarp = new AstVar{flp, VVarType::BLOCKTEMP, delayName + "__counter",
                                           nodep->findBasicDType(VBasicDTypeKwd::UINT32)};
        AstBegin* const beginp = new AstBegin{flp, delayName + "__block", cntVarp, false, true};
        beginp->addStmtsp(new AstAssign{flp, new AstVarRef{flp, cntVarp, VAccess::WRITE}, valuep});
        beginp->addStmtsp(new AstWhile{
            nodep->fileline(),
            new AstGt{flp, new AstVarRef{flp, cntVarp, VAccess::READ}, new AstConst{flp, 0}},
            controlp,
            new AstAssign{flp, new AstVarRef{flp, cntVarp, VAccess::WRITE},
                          new AstSub{flp, new AstVarRef{flp, cntVarp, VAccess::READ},
                                     new AstConst{flp, 1}}}});
        nodep->replaceWith(beginp);
        VL_DO_DANGLING(nodep->deleteTree(), nodep);
    }
    void visit(AstSenTree* nodep) override {
        if (m_inSynchDrive) {
            nodep->v3error("Event controls cannot be used in "
                           "synchronous drives (IEEE 1800-2017 14.16)");
        }
    }
    void visit(AstNodeVarRef* nodep) override {
        if (AstClockingItem* const itemp = VN_CAST(nodep->varp()->user1p(), ClockingItem)) {
            if (nodep->access().isReadOrRW() && !nodep->user1()
                && itemp->direction() == VDirection::OUTPUT) {
                nodep->v3error("Cannot read from output clockvar (IEEE 1800-2017 14.3)");
            }
            if (nodep->access().isWriteOrRW()) {
                if (itemp->direction() == VDirection::OUTPUT) {
                    if (!m_inAssignDlyLhs) {
                        nodep->v3error("Only non-blocking assignments can write "
                                       "to clockvars (IEEE 1800-2017 14.16)");
                    }
                    if (m_inAssign) m_inSynchDrive = true;
                } else if (!nodep->user1() && itemp->direction() == VDirection::INPUT) {
                    nodep->v3error("Cannot write to input clockvar (IEEE 1800-2017 14.3)");
                }
            }
        }
    }
    void visit(AstNodeAssign* nodep) override {
        if (nodep->user1()) return;
        VL_RESTORER(m_inAssign);
        VL_RESTORER(m_inSynchDrive);
        m_inAssign = true;
        m_inSynchDrive = false;
        {
            VL_RESTORER(m_inAssignDlyLhs);
            m_inAssignDlyLhs = VN_IS(nodep, AssignDly);
            iterate(nodep->lhsp());
        }
        iterate(nodep->rhsp());
        if (nodep->timingControlp()) {
            iterate(nodep->timingControlp());
        } else if (m_inSynchDrive) {
            AstAssign* const assignp = new AstAssign{
                nodep->fileline(), nodep->lhsp()->unlinkFrBack(), nodep->rhsp()->unlinkFrBack()};
            assignp->user1(true);
            nodep->replaceWith(assignp);
            VL_DO_DANGLING(nodep->deleteTree(), nodep);
        }
    }
    void visit(AstAlways* nodep) override {
        iterateAndNextNull(nodep->sensesp());
        if (nodep->sensesp()) m_seniAlwaysp = nodep->sensesp()->sensesp();
        iterateAndNextNull(nodep->stmtsp());
        m_seniAlwaysp = nullptr;
    }

    void visit(AstNodeCoverOrAssert* nodep) override {
        if (nodep->sentreep()) return;  // Already processed
        clearAssertInfo();
        // Find Clocking's buried under nodep->exprsp
        iterateChildren(nodep);
        if (!nodep->immediate()) nodep->sentreep(newSenTree(nodep));
        clearAssertInfo();
    }
    void visit(AstFell* nodep) override {
        if (nodep->user1SetOnce()) return;
        iterateChildren(nodep);
        FileLine* const fl = nodep->fileline();
        AstNodeExpr* exprp = nodep->exprp()->unlinkFrBack();
        if (exprp->width() > 1) exprp = new AstSel{fl, exprp, 0, 1};
        AstSenTree* sentreep = nodep->sentreep();
        if (sentreep) sentreep->unlinkFrBack();
        AstNodeExpr* const past = new AstPast{fl, exprp, nullptr};
        past->dtypeFrom(exprp);
        exprp = new AstAnd{fl, past, new AstNot{fl, exprp->cloneTreePure(false)}};
        exprp->dtypeSetBit();
        nodep->replaceWith(exprp);
        nodep->sentreep(newSenTree(nodep, sentreep));
        VL_DO_DANGLING(pushDeletep(nodep), nodep);
    }
    void visit(AstPast* nodep) override {
        if (nodep->sentreep()) return;  // Already processed
        iterateChildren(nodep);
        nodep->sentreep(newSenTree(nodep));
    }
    void visit(AstRose* nodep) override {
        if (nodep->user1SetOnce()) return;
        iterateChildren(nodep);
        FileLine* const fl = nodep->fileline();
        AstNodeExpr* exprp = nodep->exprp()->unlinkFrBack();
        if (exprp->width() > 1) exprp = new AstSel{fl, exprp, 0, 1};
        AstSenTree* sentreep = nodep->sentreep();
        if (sentreep) sentreep->unlinkFrBack();
        AstNodeExpr* const past = new AstPast{fl, exprp, nullptr};
        past->dtypeFrom(exprp);
        exprp = new AstAnd{fl, new AstNot{fl, past}, exprp->cloneTreePure(false)};
        exprp->dtypeSetBit();
        nodep->replaceWith(exprp);
        nodep->sentreep(newSenTree(nodep, sentreep));
        VL_DO_DANGLING(pushDeletep(nodep), nodep);
    }
    void visit(AstStable* nodep) override {
        if (nodep->user1SetOnce()) return;
        iterateChildren(nodep);
        FileLine* const fl = nodep->fileline();
        AstNodeExpr* exprp = nodep->exprp()->unlinkFrBack();
        AstSenTree* sentreep = nodep->sentreep();
        if (sentreep) sentreep->unlinkFrBack();
        AstNodeExpr* const past = new AstPast{fl, exprp, nullptr};
        past->dtypeFrom(exprp);
        exprp = new AstEq{fl, past, exprp->cloneTreePure(false)};
        exprp->dtypeSetBit();
        nodep->replaceWith(exprp);
        nodep->sentreep(newSenTree(nodep, sentreep));
        VL_DO_DANGLING(pushDeletep(nodep), nodep);
    }

    void visit(AstImplication* nodep) override {
        if (nodep->sentreep()) return;  // Already processed

        FileLine* const fl = nodep->fileline();
        AstNodeExpr* const rhsp = nodep->rhsp()->unlinkFrBack();
        AstNodeExpr* lhsp = nodep->lhsp()->unlinkFrBack();

        if (m_disablep) lhsp = new AstAnd{fl, new AstNot{fl, m_disablep}, lhsp};

        AstNodeExpr* const past = new AstPast{fl, lhsp, nullptr};
        past->dtypeFrom(lhsp);
        AstNodeExpr* const exprp = new AstOr{fl, new AstNot{fl, past}, rhsp};
        exprp->dtypeSetBit();
        nodep->replaceWith(exprp);
        nodep->sentreep(newSenTree(nodep));
        VL_DO_DANGLING(pushDeletep(nodep), nodep);
    }

    void visit(AstPropSpec* nodep) override {
        nodep = substitutePropertyCall(nodep);
        // No need to iterate the body, once replace will get iterated
        iterateAndNextNull(nodep->sensesp());
        if (m_senip)
            nodep->v3warn(E_UNSUPPORTED, "Unsupported: Only one PSL clock allowed per assertion");
        // Block is the new expression to evaluate
        AstNodeExpr* blockp = VN_AS(nodep->propp()->unlinkFrBack(), NodeExpr);
        if (AstNodeExpr* const disablep = nodep->disablep()) {
            m_disablep = disablep->cloneTreePure(false);
            if (VN_IS(nodep->backp(), Cover)) {
                blockp = new AstAnd{disablep->fileline(),
                                    new AstNot{disablep->fileline(), disablep->unlinkFrBack()},
                                    blockp};
            } else {
                blockp = new AstOr{disablep->fileline(), disablep->unlinkFrBack(), blockp};
            }
        }
        // Unlink and just keep a pointer to it, convert to sentree as needed
        m_senip = nodep->sensesp();
        nodep->replaceWith(blockp);
        VL_DO_DANGLING(pushDeletep(nodep), nodep);
    }
    void visit(AstNodeModule* nodep) override {
        VL_RESTORER(m_defaultClockingp);
        VL_RESTORER(m_modp);
        m_defaultClockingp = nullptr;
        nodep->foreach([&](AstClocking* const clockingp) {
            if (clockingp->isDefault()) {
                if (m_defaultClockingp) {
                    clockingp->v3error("Only one default clocking block allowed per module"
                                       " (IEEE 1800-2017 14.12)");
                }
                m_defaultClockingp = clockingp;
            }
        });
        m_modp = nodep;
        iterateChildren(nodep);
    }
    void visit(AstProperty* nodep) override {
        // The body will be visited when will be substituted in place of property reference
        // (AstFuncRef)
        VL_DO_DANGLING(pushDeletep(nodep->unlinkFrBack()), nodep);
    }
    void visit(AstNode* nodep) override { iterateChildren(nodep); }

public:
    // CONSTRUCTORS
    explicit AssertPreVisitor(AstNetlist* nodep)
        : m_netlistp{nodep} {
        clearAssertInfo();
        // Process
        iterate(nodep);
    }
    ~AssertPreVisitor() override = default;
};

//######################################################################
// Top Assert class

void V3AssertPre::assertPreAll(AstNetlist* nodep) {
    UINFO(2, __FUNCTION__ << ": " << endl);
    { AssertPreVisitor{nodep}; }  // Destruct before checking
    V3Global::dumpCheckGlobalTree("assertpre", 0, dumpTreeLevel() >= 3);
}
