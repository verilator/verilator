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
//  Pre steps:
//      Attach clocks to each assertion
//      Substitute property references by property body (IEEE 1800-2023 16.12.1).
//      Transform clocking blocks into imperative logic
//*************************************************************************

#include "V3PchAstNoMT.h"  // VL_MT_DISABLED_CODE_UNIT

#include "V3AssertPre.h"

#include "V3Const.h"
#include "V3Task.h"
#include "V3UniqueNames.h"

#include <unordered_map>

VL_DEFINE_DEBUG_FUNCTIONS;

//######################################################################
// Assert class functions

class AssertPreVisitor final : public VNVisitor {
    // Removes clocks and other pre-optimizations
    // Eventually inlines calls to sequences, properties, etc.
    // We're not parsing the tree, or anything more complicated.
private:
    // NODE STATE
    // AstClockingItem::user1p()         // AstVar*.      varp() of ClockingItem after unlink
    // AstPExpr::user1()                 // bool.         Created from AstUntil
    const VNUser1InUse m_inuser1;
    // STATE
    // Current context:
    AstNetlist* const m_netlistp = nullptr;  // Current netlist
    AstNodeModule* m_modp = nullptr;  // Current module
    AstClocking* m_clockingp = nullptr;  // Current clocking block
    // Reset each module:
    AstClocking* m_defaultClockingp = nullptr;  // Default clocking for current module
    AstVar* m_defaultClkEvtVarp = nullptr;  // Event var for default clocking (for ##0)
    AstDefaultDisable* m_defaultDisablep = nullptr;  // Default disable for current module
    // Reset each assertion:
    AstSenItem* m_senip = nullptr;  // Last sensitivity
    // Reset each always:
    AstSenItem* m_seniAlwaysp = nullptr;  // Last sensitivity in always
    // Reset each assertion:
    AstNodeExpr* m_disablep = nullptr;  // Last disable
    AstIf* m_disableSeqIfp = nullptr;  // Used for handling disable iff in sequences
    AstPExpr* m_pexprp = nullptr;  // Last AstPExpr
    // Other:
    V3UniqueNames m_cycleDlyNames{"__VcycleDly"};  // Cycle delay counter name generator
    V3UniqueNames m_consRepNames{"__VconsRep"};  // Consecutive repetition counter name generator
    V3UniqueNames m_gotoRepNames{"__VgotoRep"};  // Goto repetition counter name generator
    V3UniqueNames m_nonConsRepNames{"__VnonConsRep"};  // Nonconsecutive rep name generator
    V3UniqueNames m_disableCntNames{"__VdisableCnt"};  // Disable condition counter name generator
    V3UniqueNames m_propVarNames{"__Vpropvar"};  // Property-local variable name generator
    V3UniqueNames m_activeNames{"__VassertsActive"};  // Active asserts map name generator
    bool m_inAssign = false;  // True if in an AssignNode
    bool m_inAssignDlyLhs = false;  // True if in AssignDly's LHS
    bool m_inSynchDrive = false;  // True if in synchronous drive
    bool m_hasCycleDelay = false;  // True if node has cycle delay beneath
    std::vector<AstVarXRef*> m_xrefsp;  // list of xrefs that need name fixup
    std::vector<AstSequence*> m_seqsToCleanup;  // Sequences to clean up after traversal

    // METHODS

    AstSenTree* newSenTree(AstNode* nodep, AstSenTree* useTreep = nullptr,
                           AstNodeCoverOrAssert* cassertp = nullptr) {
        // Create sentree based on clocked or default clock
        // Return nullptr for always
        if (useTreep) return useTreep;
        AstSenTree* newp = nullptr;
        AstSenItem* senip = m_senip;
        bool fromAlways = false;
        if (!senip && m_defaultClockingp) senip = m_defaultClockingp->sensesp();
        if (!senip) {
            senip = m_seniAlwaysp;
            fromAlways = true;
        }
        if (!senip) {
            nodep->v3warn(E_UNSUPPORTED, "Unsupported: Unclocked assertion");
            newp = new AstSenTree{nodep->fileline(), nullptr};
        } else {
            if (cassertp && fromAlways) cassertp->senFromAlways(true);
            newp = new AstSenTree{nodep->fileline(), senip->cloneTree(true)};
        }
        return newp;
    }
    AstNodeExpr* getSequenceBodyExprp(const AstSequence* const seqp) const {
        // The statements in AstSequence are optional AstVar (ports) followed by body expr.
        AstNode* bodyp = seqp->stmtsp();
        while (bodyp && VN_IS(bodyp, Var)) bodyp = bodyp->nextp();
        return VN_CAST(bodyp, NodeExpr);
    }
    AstPropSpec* getPropertyExprp(const AstProperty* const propp) {
        // Statements in AstProperty: AstVar (ports/local vars),
        // AstInitialStaticStmt/AstInitialAutomaticStmt (var init), AstPropSpec (body).
        AstNode* propExprp = propp->stmtsp();
        while (propExprp
               && (VN_IS(propExprp, Var) || VN_IS(propExprp, InitialStaticStmt)
                   || VN_IS(propExprp, InitialAutomaticStmt))) {
            propExprp = propExprp->nextp();
        }
        return VN_CAST(propExprp, PropSpec);
    }
    void substituteSequenceCall(AstFuncRef* funcrefp, AstSequence* seqp) {
        // IEEE 1800-2023 16.7 (sequence declarations), 16.8 (sequence instances)
        // Inline the sequence body at the call site, replacing the FuncRef
        AstNodeExpr* bodyExprp = getSequenceBodyExprp(seqp);
        UASSERT_OBJ(bodyExprp, funcrefp, "Sequence has no body expression");
        // Clone the body expression since the sequence may be referenced multiple times
        AstNodeExpr* clonedp = bodyExprp->cloneTree(false);
        // Build substitution map, then do a single traversal to replace all formals
        // (textual substitution per IEEE 16.8.2).
        const V3TaskConnects tconnects = V3Task::taskConnects(funcrefp, seqp->stmtsp());
        std::unordered_map<const AstVar*, AstNodeExpr*> portMap;
        for (const auto& tconnect : tconnects) {
            portMap[tconnect.first] = tconnect.second->exprp();
        }
        clonedp->foreach([&](AstVarRef* refp) {
            const auto it = portMap.find(refp->varp());
            if (it != portMap.end()) {
                refp->replaceWith(it->second->cloneTree(false));
                VL_DO_DANGLING(pushDeletep(refp), refp);
            }
        });
        for (const auto& tconnect : tconnects) {
            pushDeletep(tconnect.second->exprp()->unlinkFrBack());
        }
        // Replace the FuncRef with the inlined body
        funcrefp->replaceWith(clonedp);
        VL_DO_DANGLING(pushDeletep(funcrefp), funcrefp);
        // Clear referenced flag; sequences with isReferenced==false are deleted in assertPreAll
        seqp->isReferenced(false);
    }
    AstPropSpec* substitutePropertyCall(AstPropSpec* nodep) {
        if (AstFuncRef* const funcrefp = VN_CAST(nodep->propp(), FuncRef)) {
            if (const AstProperty* const propp = VN_CAST(funcrefp->taskp(), Property)) {
                AstPropSpec* propExprp = getPropertyExprp(propp);
                // Substitute inner property call before copying in order to not doing the same for
                // each call of outer property call.
                propExprp = substitutePropertyCall(propExprp);
                // Clone subtree after substitution. It is needed, because property might be called
                // multiple times with different arguments.
                propExprp = propExprp->cloneTree(false);
                // Build substitution maps for formal arguments and property-local
                // variables, then perform a single foreach to apply all replacements.
                // Map port vars to their actual argument expressions
                const V3TaskConnects tconnects = V3Task::taskConnects(funcrefp, propp->stmtsp());
                std::unordered_map<const AstVar*, AstNodeExpr*> portMap;
                for (const auto& tconnect : tconnects) {
                    portMap[tconnect.first] = tconnect.second->exprp();
                }

                // Promote property-local variables (non-port vars, IEEE 16.10) to
                // module-level __Vpropvar temps. Cross-cycle persistence is handled
                // by the match item lowering in visit(AstImplication*).
                std::unordered_map<const AstVar*, AstVar*> localVarMap;
                for (AstNode* stmtp = propp->stmtsp(); stmtp; stmtp = stmtp->nextp()) {
                    if (AstVar* const varp = VN_CAST(stmtp, Var)) {
                        if (!varp->isIO()) {
                            const string newName = m_propVarNames.get(varp);
                            AstVar* const newVarp = new AstVar{
                                varp->fileline(), VVarType::MODULETEMP, newName, varp->dtypep()};
                            newVarp->lifetime(VLifetime::STATIC_EXPLICIT);
                            m_modp->addStmtsp(newVarp);
                            localVarMap[varp] = newVarp;
                        }
                    }
                }

                // Single traversal: substitute ports and update local var references
                propExprp->foreach([&](AstVarRef* refp) {
                    {
                        const auto portIt = portMap.find(refp->varp());
                        if (portIt != portMap.end()) {
                            refp->replaceWith(portIt->second->cloneTree(false));
                            VL_DO_DANGLING(pushDeletep(refp), refp);
                            return;
                        }
                    }
                    {
                        const auto localIt = localVarMap.find(refp->varp());
                        if (localIt != localVarMap.end()) { refp->varp(localIt->second); }
                    }
                });

                // Clean up argument expressions
                for (const auto& tconnect : tconnects) {
                    pushDeletep(tconnect.second->exprp()->unlinkFrBack());
                }

                // Handle case with 2 disable iff statement (IEEE 1800-2023 16.12.1)
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
                VL_DO_DANGLING(pushDeletep(nodep), nodep);
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
        UINFO(8, "   CLOCKING" << nodep);
        if (nodep->isDefault()) {
            if (m_defaultClockingp) {
                nodep->v3error("Only one default clocking block allowed per module"
                               " (IEEE 1800-2023 14.12)");
            } else {
                m_defaultClockingp = nodep;
                m_defaultClkEvtVarp = nodep->ensureEventp();
            }
        }
        iterateChildren(nodep);
        if (nodep->eventp()) nodep->addNextHere(nodep->eventp()->unlinkFrBack());
        VL_DO_DANGLING(pushDeletep(nodep->unlinkFrBack()), nodep);
    }
    void visit(AstModportClockingRef* const nodep) override {
        // It has to be converted to a list of ModportClockingVarRefs,
        // because clocking blocks are removed in this pass
        for (AstNode* itemp = nodep->clockingp()->itemsp(); itemp; itemp = itemp->nextp()) {
            if (const AstClockingItem* citemp = VN_CAST(itemp, ClockingItem)) {
                if (AstVar* const varp
                    = citemp->varp() ? citemp->varp() : VN_AS(citemp->user1p(), Var)) {
                    AstModportVarRef* const modVarp = new AstModportVarRef{
                        nodep->fileline(), varp->name(), citemp->direction()};
                    modVarp->varp(varp);
                    nodep->addNextHere(modVarp);
                }
            }
        }
        VL_DO_DANGLING(pushDeletep(nodep->unlinkFrBack()), nodep);
    }
    void visit(AstClockingItem* const nodep) override {
        // Get a ref to the sampled/driven variable
        AstVar* const varp = nodep->varp();
        if (!varp) {
            // Unused item
            return;
        }
        FileLine* const flp = nodep->fileline();
        V3Const::constifyEdit(nodep->skewp());
        if (!VN_IS(nodep->skewp(), Const)) {
            nodep->skewp()->v3error("Skew must be constant (IEEE 1800-2023 14.4)");
            return;
        }
        AstConst* const skewp = VN_AS(nodep->skewp(), Const);
        if (skewp->num().isNegative()) skewp->v3error("Skew cannot be negative");
        AstNodeExpr* const exprp = nodep->exprp();
        varp->name(m_clockingp->name() + "__DOT__" + varp->name());
        m_clockingp->addNextHere(varp->unlinkFrBack());
        nodep->user1p(varp);
        varp->user1p(nodep);
        if (nodep->direction() == VDirection::OUTPUT) {
            exprp->foreach([](const AstNodeVarRef* varrefp) {
                // Prevent confusing BLKANDNBLK warnings on clockvars due to generated assignments
                varrefp->fileline()->warnOff(V3ErrorCode::BLKANDNBLK, true);
            });
            AstVarRef* const skewedReadRefp = new AstVarRef{flp, varp, VAccess::READ};
            skewedReadRefp->user1(true);
            // Initialize the clockvar
            AstVarRef* const skewedWriteRefp = new AstVarRef{flp, varp, VAccess::WRITE};
            skewedWriteRefp->user1(true);
            AstInitialStatic* const initClockvarp = new AstInitialStatic{
                flp, new AstAssign{flp, skewedWriteRefp, exprp->cloneTreePure(false)}};
            m_modp->addStmtsp(initClockvarp);
            // A var to keep the previous value of the clockvar
            AstVar* const prevVarp = new AstVar{
                flp, VVarType::MODULETEMP, "__Vclocking_prev__" + varp->name(), exprp->dtypep()};
            prevVarp->lifetime(VLifetime::STATIC_EXPLICIT);
            AstInitialStatic* const initPrevClockvarp = new AstInitialStatic{
                flp, new AstAssign{flp, new AstVarRef{flp, prevVarp, VAccess::WRITE},
                                   skewedReadRefp->cloneTreePure(false)}};
            m_modp->addStmtsp(prevVarp);
            m_modp->addStmtsp(initPrevClockvarp);
            // Assign the clockvar to the actual var; only do it if the clockvar's value has
            // changed
            AstAssign* const assignp
                = new AstAssign{flp, exprp->cloneTreePure(false), skewedReadRefp};
            AstIf* const ifp
                = new AstIf{flp,
                            new AstNeq{flp, new AstVarRef{flp, prevVarp, VAccess::READ},
                                       skewedReadRefp->cloneTreePure(false)},
                            assignp};
            ifp->addThensp(new AstAssign{flp, new AstVarRef{flp, prevVarp, VAccess::WRITE},
                                         skewedReadRefp->cloneTree(false)});
            if (skewp->isZero()) {
                // Drive the var in Re-NBA (IEEE 1800-2023 14.16)
                AstSenTree* senTreep
                    = new AstSenTree{flp, m_clockingp->sensesp()->cloneTree(false)};
                senTreep->addSensesp(
                    new AstSenItem{flp, VEdgeType::ET_CHANGED, skewedReadRefp->cloneTree(false)});
                AstCMethodHard* const trigp = new AstCMethodHard{
                    nodep->fileline(),
                    new AstVarRef{flp, m_clockingp->ensureEventp(), VAccess::READ},
                    VCMethod::EVENT_IS_TRIGGERED};
                trigp->dtypeSetBit();
                ifp->condp(new AstLogAnd{flp, ifp->condp()->unlinkFrBack(), trigp});
                m_clockingp->addNextHere(new AstAlwaysReactive{flp, senTreep, ifp});
            } else if (skewp->fileline()->timingOn()) {
                // Create a fork so that this AlwaysObserved can be retriggered before the
                // assignment happens. Also then it can be combo, avoiding the need for creating
                // new triggers.
                AstFork* const forkp = new AstFork{flp, VJoinType::JOIN_NONE};
                forkp->addForksp(new AstBegin{flp, "", ifp, true});
                // Use Observed for this to make sure we do not miss the event
                m_clockingp->addNextHere(new AstAlwaysObserved{
                    flp, new AstSenTree{flp, m_clockingp->sensesp()->cloneTree(false)}, forkp});
                if (v3Global.opt.timing().isSetTrue()) {
                    AstDelay* const delayp = new AstDelay{flp, skewp->unlinkFrBack(), false};
                    delayp->timeunit(m_modp->timeunit());
                    assignp->timingControlp(delayp);
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
                // #1step means the value that is sampled is always the signal's last value
                // before the clock edge (IEEE 1800-2023 14.4)
                AstSampled* const sampledp = new AstSampled{flp, exprp->cloneTreePure(false)};
                sampledp->dtypeFrom(exprp);
                AstAssign* const assignp = new AstAssign{flp, refp, sampledp};
                m_clockingp->addNextHere(new AstAlways{
                    flp, VAlwaysKwd::ALWAYS,
                    new AstSenTree{flp, m_clockingp->sensesp()->cloneTree(false)}, assignp});
            } else if (skewp->isZero()) {
                // #0 means the var has to be sampled in Observed (IEEE 1800-2023 14.13)
                AstAssign* const assignp = new AstAssign{flp, refp, exprp->cloneTreePure(false)};
                m_clockingp->addNextHere(new AstAlwaysObserved{
                    flp, new AstSenTree{flp, m_clockingp->sensesp()->cloneTree(false)}, assignp});
            } else {
                // Create a queue where we'll store sampled values with timestamps
                AstSampleQueueDType* const queueDtp
                    = new AstSampleQueueDType{flp, exprp->dtypep()};
                m_netlistp->typeTablep()->addTypesp(queueDtp);
                AstVar* const queueVarp
                    = new AstVar{flp, VVarType::MODULETEMP, "__Vqueue__" + varp->name(), queueDtp};
                queueVarp->lifetime(VLifetime::STATIC_EXPLICIT);
                m_clockingp->addNextHere(queueVarp);
                // Create a process like this:
                //     always queue.push(<sampled var>);
                AstCMethodHard* const pushp = new AstCMethodHard{
                    flp, new AstVarRef{flp, queueVarp, VAccess::WRITE}, VCMethod::DYN_PUSH,
                    new AstTime{nodep->fileline(), m_modp->timeunit()}};
                pushp->addPinsp(exprp->cloneTreePure(false));
                pushp->dtypeSetVoid();
                m_clockingp->addNextHere(
                    new AstAlways{flp, VAlwaysKwd::ALWAYS, nullptr, pushp->makeStmt()});
                // Create a process like this:
                //     always @<clocking event> queue.pop(<skew>, /*out*/<skewed var>);
                AstCMethodHard* const popp = new AstCMethodHard{
                    flp, new AstVarRef{flp, queueVarp, VAccess::READWRITE}, VCMethod::DYN_POP,
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
            nodep->v3fatalSrc("Invalid direction");
        }
    }
    void visit(AstDelay* nodep) override {
        m_hasCycleDelay = true;
        // Only cycle delays are relevant in this stage; also only process once
        if (!nodep->isCycleDelay()) {
            if (m_inSynchDrive) {
                nodep->v3error("Only cycle delays can be used in synchronous drives"
                               " (IEEE 1800-2023 14.16)");
            }
            iterateChildren(nodep);
            return;
        }
        if (m_inAssign && !m_inSynchDrive) {
            nodep->v3error("Cycle delays not allowed as intra-assignment delays"
                           " (IEEE 1800-2023 14.11)");
            VL_DO_DANGLING(nodep->unlinkFrBack()->deleteTree(), nodep);
            return;
        }
        if (nodep->stmtsp()) nodep->addNextHere(nodep->stmtsp()->unlinkFrBackWithNext());
        FileLine* const flp = nodep->fileline();
        AstNodeExpr* valuep = V3Const::constifyEdit(nodep->lhsp()->unlinkFrBack());
        const AstConst* const constp = VN_CAST(valuep, Const);
        if (!constp) {
            // V3AssertNfa handles non-const delays before this pass and
            // replaces the property; this branch should never be reached.
            nodep->v3fatalSrc("Non-constant cycle delay in assertion: "
                              "should have been caught by V3AssertNfa");
        } else if (constp->isZero()) {
            VL_DO_DANGLING(pushDeletep(valuep), valuep);
            if (m_inSynchDrive) {
                // ##0 has no effect in synchronous drives (IEEE 1800-2023 14.11)
                VL_DO_DANGLING(pushDeletep(nodep->unlinkFrBack()), nodep);
                return;
            }
            if (m_pexprp) {
                // ##0 in sequence context = zero delay = same clock tick
                VL_DO_DANGLING(pushDeletep(nodep->unlinkFrBack()), nodep);
                return;
            }
            // Procedural ##0: synchronize with default clocking event (IEEE 1800-2023 14.11)
            // If the clocking event has not yet occurred this timestep, wait for it;
            // otherwise continue without suspension.
            if (!m_defaultClockingp) {
                nodep->v3error("Usage of cycle delays requires default clocking"
                               " (IEEE 1800-2023 14.11)");
                VL_DO_DANGLING(pushDeletep(nodep->unlinkFrBack()), nodep);
                return;
            }
            AstVar* const evtVarp = m_defaultClkEvtVarp;
            UASSERT_OBJ(evtVarp, nodep, "Default clocking event var not pre-created");
            AstCMethodHard* const isTriggeredp = new AstCMethodHard{
                flp, new AstVarRef{flp, evtVarp, VAccess::READ}, VCMethod::EVENT_IS_TRIGGERED};
            isTriggeredp->dtypeSetBit();
            AstEventControl* const waitp = new AstEventControl{
                flp,
                new AstSenTree{flp, new AstSenItem{flp, VEdgeType::ET_EVENT,
                                                   new AstVarRef{flp, evtVarp, VAccess::READ}}},
                nullptr};
            AstIf* const ifp = new AstIf{flp, new AstNot{flp, isTriggeredp}, waitp};
            nodep->replaceWith(ifp);
            VL_DO_DANGLING(pushDeletep(nodep), nodep);
            return;
        }
        AstSenItem* sensesp = nullptr;
        if (!m_defaultClockingp) {
            if (!m_pexprp) {
                nodep->v3error("Usage of cycle delays requires default clocking"
                               " (IEEE 1800-2023 14.11)");
                VL_DO_DANGLING(nodep->unlinkFrBack()->deleteTree(), nodep);
                VL_DO_DANGLING(valuep->deleteTree(), valuep);
                return;
            }
            sensesp = m_senip;
        } else {
            sensesp = m_defaultClockingp->sensesp();
        }
        AstEventControl* const controlp = new AstEventControl{
            nodep->fileline(), new AstSenTree{flp, sensesp->cloneTree(false)}, nullptr};
        const std::string delayName = m_cycleDlyNames.get(nodep);
        AstNodeExpr* throughoutp
            = nodep->throughoutp() ? nodep->throughoutp()->unlinkFrBack() : nullptr;

        AstVar* const cntVarp = new AstVar{flp, VVarType::BLOCKTEMP, delayName + "__counter",
                                           nodep->findBasicDType(VBasicDTypeKwd::UINT32)};
        cntVarp->lifetime(VLifetime::AUTOMATIC_EXPLICIT);
        AstBegin* const beginp = new AstBegin{flp, delayName + "__block", cntVarp, true};
        beginp->addStmtsp(new AstAssign{flp, new AstVarRef{flp, cntVarp, VAccess::WRITE}, valuep});

        // Throughout: create flag tracking whether condition held every tick
        AstVar* throughoutOkp = nullptr;
        if (throughoutp) {
            throughoutOkp = new AstVar{flp, VVarType::BLOCKTEMP, delayName + "__throughoutOk",
                                       nodep->findBasicDType(VBasicDTypeKwd::LOGIC_IMPLICIT)};
            throughoutOkp->lifetime(VLifetime::AUTOMATIC_EXPLICIT);
            beginp->addStmtsp(throughoutOkp);
            beginp->addStmtsp(new AstAssign{flp, new AstVarRef{flp, throughoutOkp, VAccess::WRITE},
                                            new AstConst{flp, AstConst::BitTrue{}}});
            // Check condition at tick 0 (sequence start, before entering loop)
            beginp->addStmtsp(
                new AstIf{flp, new AstLogNot{flp, throughoutp->cloneTreePure(false)},
                          new AstAssign{flp, new AstVarRef{flp, throughoutOkp, VAccess::WRITE},
                                        new AstConst{flp, AstConst::BitFalse{}}}});
        }

        {
            AstLoop* const loopp = new AstLoop{flp};
            // When throughout is present, exit loop early if condition fails
            AstNodeExpr* loopCondp
                = new AstGt{flp, new AstVarRef{flp, cntVarp, VAccess::READ}, new AstConst{flp, 0}};
            if (throughoutOkp) {
                loopCondp = new AstLogAnd{flp, loopCondp,
                                          new AstVarRef{flp, throughoutOkp, VAccess::READ}};
            }
            loopp->addStmtsp(new AstLoopTest{flp, loopp, loopCondp});
            loopp->addStmtsp(controlp);
            loopp->addStmtsp(
                new AstAssign{flp, new AstVarRef{flp, cntVarp, VAccess::WRITE},
                              new AstSub{flp, new AstVarRef{flp, cntVarp, VAccess::READ},
                                         new AstConst{flp, 1}}});
            // Check throughout condition at each tick during delay (IEEE 1800-2023 16.9.9)
            if (throughoutp) {
                loopp->addStmtsp(
                    new AstIf{flp, new AstLogNot{flp, throughoutp},
                              new AstAssign{flp, new AstVarRef{flp, throughoutOkp, VAccess::WRITE},
                                            new AstConst{flp, AstConst::BitFalse{}}}});
            }
            beginp->addStmtsp(loopp);
        }
        // Compose wrappers on remaining sequence: throughout gate (inner), disable iff (outer)
        AstNode* remainp = nodep->nextp() ? nodep->nextp()->unlinkFrBackWithNext() : nullptr;
        if (throughoutOkp) {
            // If condition failed during delay, fail assertion
            remainp = new AstIf{flp, new AstVarRef{flp, throughoutOkp, VAccess::READ}, remainp,
                                new AstPExprClause{flp, /*pass=*/false}};
        }
        if (m_disableSeqIfp && remainp) {
            AstIf* const disableSeqIfp = m_disableSeqIfp->cloneTree(false);
            // Keep continuation statements in a proper statement-list container.
            disableSeqIfp->addThensp(new AstBegin{flp, "", remainp, true});
            remainp = disableSeqIfp;
        }
        if (remainp) {
            if (throughoutOkp) {
                // throughoutOkp is declared in beginp scope -- check must be inside it
                beginp->addStmtsp(remainp);
            } else {
                nodep->addNextHere(remainp);
            }
        }
        nodep->replaceWith(beginp);
        VL_DO_DANGLING(nodep->deleteTree(), nodep);
    }
    void visit(AstSenTree* nodep) override {
        if (m_inSynchDrive) {
            nodep->v3error("Event controls cannot be used in "
                           "synchronous drives (IEEE 1800-2023 14.16)");
        }

        const AstSampled* sampledp;
        if (nodep->exists([&sampledp](const AstSampled* const sp) {
                sampledp = sp;
                return true;
            })) {
            sampledp->v3warn(E_UNSUPPORTED, "Unsupported: $sampled inside sensitivity list");
        }
    }
    void visit(AstNodeVarRef* nodep) override {
        UINFO(8, " -varref:  " << nodep);
        UINFO(8, " -varref-var-back:  " << nodep->varp()->backp());
        UINFO(8, " -varref-var-user1:  " << nodep->varp()->user1p());
        if (AstClockingItem* const itemp = VN_CAST(
                nodep->varp()->user1p() ? nodep->varp()->user1p() : nodep->varp()->firstAbovep(),
                ClockingItem)) {
            if (nodep->user1()) return;

            // ensure linking still works, this has to be done only once
            if (AstVarXRef* xrefp = VN_CAST(nodep, VarXRef)) {
                UINFO(8, " -clockvarxref-in:  " << xrefp);
                string dotted = xrefp->dotted();
                const size_t dotPos = dotted.rfind('.');
                dotted.erase(dotPos, string::npos);
                xrefp->dotted(dotted);
                UINFO(8, " -clockvarxref-out: " << xrefp);
                m_xrefsp.emplace_back(xrefp);
            }

            if (nodep->access().isReadOrRW() && itemp->direction() == VDirection::OUTPUT) {
                nodep->v3error("Cannot read from output clockvar (IEEE 1800-2023 14.3)");
            }
            if (nodep->access().isWriteOrRW()) {
                if (itemp->direction() == VDirection::OUTPUT) {
                    if (!m_inAssignDlyLhs) {
                        nodep->v3error("Only non-blocking assignments can write "
                                       "to clockvars (IEEE 1800-2023 14.16)");
                    }
                    if (m_inAssign) m_inSynchDrive = true;
                } else if (itemp->direction() == VDirection::INPUT) {
                    nodep->v3error("Cannot write to input clockvar (IEEE 1800-2023 14.3)");
                }
            }
            nodep->user1(true);
        }
    }
    void visit(AstMemberSel* nodep) override {
        if (AstClockingItem* const itemp = VN_CAST(
                nodep->varp()->user1p() ? nodep->varp()->user1p() : nodep->varp()->firstAbovep(),
                ClockingItem)) {
            if (nodep->access().isReadOrRW() && itemp->direction() == VDirection::OUTPUT) {
                nodep->v3error("Cannot read from output clockvar (IEEE 1800-2023 14.3)");
            }
            if (nodep->access().isWriteOrRW()) {
                if (itemp->direction() == VDirection::OUTPUT) {
                    if (!m_inAssignDlyLhs) {
                        nodep->v3error("Only non-blocking assignments can write "
                                       "to clockvars (IEEE 1800-2023 14.16)");
                    }
                    if (m_inAssign) m_inSynchDrive = true;
                } else if (itemp->direction() == VDirection::INPUT) {
                    nodep->v3error("Cannot write to input clockvar (IEEE 1800-2023 14.3)");
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
        iterateAndNextNull(nodep->sentreep());
        if (nodep->sentreep()) m_seniAlwaysp = nodep->sentreep()->sensesp();
        iterateAndNextNull(nodep->stmtsp());
        m_seniAlwaysp = nullptr;
    }

    void visit(AstNodeCoverOrAssert* nodep) override {
        if (nodep->sentreep()) return;  // Already processed

        VL_RESTORER(m_senip);
        VL_RESTORER(m_disablep);
        m_senip = nullptr;
        m_disablep = nullptr;

        // Find Clocking's buried under nodep->exprsp
        iterateChildren(nodep);
        if (!nodep->immediate()) nodep->sentreep(newSenTree(nodep, nullptr, nodep));
    }
    void visit(AstFalling* nodep) override {
        if (nodep->user1SetOnce()) return;
        iterateChildren(nodep);
        FileLine* const fl = nodep->fileline();
        AstNodeExpr* exprp = nodep->exprp()->unlinkFrBack();
        if (exprp->width() > 1) exprp = new AstSel{fl, exprp, 0, 1};
        AstNodeExpr* const futurep = new AstFuture{fl, exprp, newSenTree(nodep)};
        futurep->dtypeFrom(exprp);
        exprp = new AstAnd{fl, exprp->cloneTreePure(false), new AstNot{fl, futurep}};
        exprp->dtypeSetBit();
        nodep->replaceWith(exprp);
        VL_DO_DANGLING(pushDeletep(nodep), nodep);
    }
    void visit(AstFell* nodep) override {
        if (nodep->user1SetOnce()) return;
        iterateChildren(nodep);
        FileLine* const fl = nodep->fileline();
        AstNodeExpr* exprp = nodep->exprp()->unlinkFrBack();
        if (exprp->width() > 1) exprp = new AstSel{fl, exprp, 0, 1};
        AstSenTree* sentreep = nodep->sentreep();
        if (sentreep) sentreep->unlinkFrBack();
        AstPast* const pastp = new AstPast{fl, exprp};
        pastp->dtypeFrom(exprp);
        pastp->sentreep(newSenTree(nodep, sentreep));
        exprp = new AstAnd{fl, pastp, new AstNot{fl, exprp->cloneTreePure(false)}};
        exprp->dtypeSetBit();
        nodep->replaceWith(exprp);
        VL_DO_DANGLING(pushDeletep(nodep), nodep);
    }
    void visit(AstFuture* nodep) override {
        if (nodep->user1SetOnce()) return;
        iterateChildren(nodep);
        AstSenTree* const sentreep = nodep->sentreep();
        if (sentreep) VL_DO_DANGLING(pushDeletep(sentreep->unlinkFrBack()), sentreep);
        nodep->sentreep(newSenTree(nodep));
    }
    void visit(AstPast* nodep) override {
        if (nodep->sentreep()) return;  // Already processed
        iterateChildren(nodep);
        nodep->sentreep(newSenTree(nodep));
    }
    void visit(AstSConsRep* nodep) override {
        // IEEE 1800-2023 16.9.2 -- Lower standalone exact [*N] (N >= 2) via saturating counter.
        // Range/unbounded forms and SExpr-contained forms are lowered by V3AssertNfa.
        iterateChildren(nodep);
        // V3AssertNfa handles unbounded/ranged forms upstream, so this fast-path
        // is effectively unreachable when NFA is enabled.
        if (nodep->unbounded() || nodep->maxCountp()) return;  // LCOV_EXCL_LINE
        const AstConst* const constp = VN_CAST(nodep->countp(), Const);
        if (VL_UNLIKELY(!constp || constp->toSInt() < 1)) {
            nodep->v3fatalSrc("Consecutive repetition count must be a positive constant"
                              " (should have been caught by V3Width)");
            return;
        }
        const int n = constp->toSInt();
        FileLine* const flp = nodep->fileline();
        AstNodeExpr* const exprp = nodep->exprp()->unlinkFrBack();
        if (n == 1) {
            nodep->replaceWith(exprp);
            VL_DO_DANGLING(pushDeletep(nodep), nodep);
            return;
        }
        // Saturating counter: if (expr) cnt <= min(cnt+1, N); else cnt <= 0;
        AstVar* const cntVarp = new AstVar{flp, VVarType::MODULETEMP, m_consRepNames.get(""),
                                           nodep->findBasicDType(VBasicDTypeKwd::UINT32)};
        cntVarp->lifetime(VLifetime::STATIC_EXPLICIT);
        m_modp->addStmtsp(cntVarp);
        AstNodeExpr* const exprClonep = exprp->cloneTreePure(false);
        AstNodeExpr* const saturatingIncrp = new AstCond{
            flp,
            new AstLt{flp, new AstVarRef{flp, cntVarp, VAccess::READ},
                      new AstConst{flp, static_cast<uint32_t>(n)}},
            new AstAdd{flp, new AstVarRef{flp, cntVarp, VAccess::READ}, new AstConst{flp, 1u}},
            new AstConst{flp, static_cast<uint32_t>(n)}};
        AstAssignDly* const incrAssignp
            = new AstAssignDly{flp, new AstVarRef{flp, cntVarp, VAccess::WRITE}, saturatingIncrp};
        AstAssignDly* const resetAssignp = new AstAssignDly{
            flp, new AstVarRef{flp, cntVarp, VAccess::WRITE}, new AstConst{flp, 0u}};
        AstIf* const ifp = new AstIf{flp, exprClonep, incrAssignp, resetAssignp};
        AstSenTree* const senTreep = newSenTree(nodep);
        AstAlways* const alwaysp = new AstAlways{flp, VAlwaysKwd::ALWAYS, senTreep, ifp};
        cntVarp->addNextHere(alwaysp);
        // Match: cnt >= N-1 (previous cycles via NBA) && expr (current cycle)
        AstNodeExpr* const cntCheckp = new AstGte{flp, new AstVarRef{flp, cntVarp, VAccess::READ},
                                                  new AstConst{flp, static_cast<uint32_t>(n - 1)}};
        cntCheckp->dtypeSetBit();
        AstNodeExpr* const matchp = new AstAnd{flp, cntCheckp, exprp};
        matchp->dtypeSetBit();
        nodep->replaceWith(matchp);
        VL_DO_DANGLING(pushDeletep(nodep), nodep);
    }
    void visit(AstRising* nodep) override {
        if (nodep->user1SetOnce()) return;
        iterateChildren(nodep);
        FileLine* const fl = nodep->fileline();
        AstNodeExpr* exprp = nodep->exprp()->unlinkFrBack();
        if (exprp->width() > 1) exprp = new AstSel{fl, exprp, 0, 1};
        AstNodeExpr* const futurep = new AstFuture{fl, exprp, newSenTree(nodep)};
        futurep->dtypeFrom(exprp);
        exprp = new AstAnd{fl, new AstNot{fl, exprp->cloneTreePure(false)}, futurep};
        exprp->dtypeSetBit();
        nodep->replaceWith(exprp);
        VL_DO_DANGLING(pushDeletep(nodep), nodep);
    }
    void visit(AstRose* nodep) override {
        if (nodep->user1SetOnce()) return;
        iterateChildren(nodep);
        FileLine* const fl = nodep->fileline();
        AstNodeExpr* exprp = nodep->exprp()->unlinkFrBack();
        if (exprp->width() > 1) exprp = new AstSel{fl, exprp, 0, 1};
        AstSenTree* sentreep = nodep->sentreep();
        if (sentreep) sentreep->unlinkFrBack();
        AstPast* const pastp = new AstPast{fl, exprp};
        pastp->dtypeFrom(exprp);
        pastp->sentreep(newSenTree(nodep, sentreep));
        exprp = new AstAnd{fl, new AstNot{fl, pastp}, exprp->cloneTreePure(false)};
        exprp->dtypeSetBit();
        nodep->replaceWith(exprp);
        VL_DO_DANGLING(pushDeletep(nodep), nodep);
    }
    static AstAssocArrayDType* getProcessAssocArrayType(FileLine* const flp) {
        // Type of __VassertsActive___x[std::process]
        AstNodeDType* valp
            = v3Global.rootp()->typeTablep()->findBasicDType(flp, VBasicDTypeKwd::BIT);
        AstClassRefDType* keyp
            = new AstClassRefDType{flp, v3Global.rootp()->stdPackageClassp(), nullptr};
        keyp->classOrPackagep(v3Global.rootp()->stdPackageClassp());
        v3Global.rootp()->typeTablep()->addTypesp(keyp);
        AstAssocArrayDType* const typep = new AstAssocArrayDType{flp, valp, keyp};
        typep->dtypep(typep);
        v3Global.rootp()->typeTablep()->addTypesp(typep);
        return typep;
    }
    static AstStmtExpr* getProcessAssocArrayDelete(AstVarRef* const refp) {
        // Constructs refp.delete(std::process::self()) statement
        FileLine* const flp = refp->fileline();
        refp->classOrPackagep(v3Global.rootp()->stdPackageClassp());
        AstCMethodHard* const deletep = new AstCMethodHard{
            flp, refp, VCMethod::ASSOC_ERASE, v3Global.rootp()->stdPackageProcessSelfp(flp)};
        deletep->dtypep(refp->findVoidDType());
        return new AstStmtExpr{flp, deletep};
    }
    static AstNodeExpr* getProcessAssocArraySize(AstVarRef* const refp) {
        // Constructs refp.size() statement
        refp->classOrPackagep(v3Global.rootp()->stdPackageClassp());
        AstCMethodHard* const sizep
            = new AstCMethodHard{refp->fileline(), refp, VCMethod::ASSOC_SIZE};
        sizep->dtypep(refp->findBasicDType(VBasicDTypeKwd::UINT32));
        return sizep;
    }
    void visit(AstSEventually* nodep) override {
        UASSERT(v3Global.rootp()->stdPackagep(), "Should be imported");

        AstSenTree* const sentreep = newSenTree(nodep);
        if (!sentreep->sensesp()) {
            VL_DO_DANGLING(pushDeletep(sentreep), sentreep);
            nodep->replaceWith(new AstConst{nodep->fileline(), AstConst::BitFalse{}});
            VL_DO_DANGLING(pushDeletep(nodep), nodep);
            return;
        }

        FileLine* const flp = nodep->fileline();

        // Track active assertions
        AstVar* const activep = new AstVar{flp, VVarType::MODULETEMP, m_activeNames.get(""),
                                           getProcessAssocArrayType(flp)};
        activep->lifetime(VLifetime::STATIC_EXPLICIT);
        m_modp->addStmtsp(activep);

        // Assertion condition check
        AstLoop* const loopp = new AstLoop{flp};
        AstNodeExpr* const condp = new AstSampled{flp, nodep->exprp()->unlinkFrBack()};
        loopp->addStmtsp(new AstLoopTest{flp, loopp, new AstLogNot{flp, condp}});
        loopp->addStmtsp(new AstEventControl{flp, sentreep, nullptr});

        // Add assertion to the active set
        AstAssocSel* const selp = new AstAssocSel{flp, new AstVarRef{flp, activep, VAccess::WRITE},
                                                  v3Global.rootp()->stdPackageProcessSelfp(flp)};
        AstAssign* const incrementp = new AstAssign{flp, selp, new AstConst{flp, 1}};
        AstPExprClause* const clausep = new AstPExprClause{flp};
        AstStmtExpr* const deletep
            = getProcessAssocArrayDelete(new AstVarRef{flp, activep, VAccess::WRITE});

        // Main assertion block
        AstBegin* const bodyp = new AstBegin{flp, "", nullptr, true};
        bodyp->addStmtsp(incrementp);
        bodyp->addStmtsp(loopp);
        bodyp->addStmtsp(clausep);
        bodyp->addStmtsp(deletep);

        // Validate assertion condition for each active assert
        AstVar* const activeCountp = new AstVar{flp, VVarType::BLOCKTEMP, "__VassertCount",
                                                nodep->findBasicDType(VBasicDTypeKwd::UINT32)};
        activeCountp->lifetime(VLifetime::AUTOMATIC_EXPLICIT);

        AstAssign* const initActiveCountp
            = new AstAssign{flp, new AstVarRef{flp, activeCountp, VAccess::WRITE},
                            getProcessAssocArraySize(new AstVarRef{flp, activep, VAccess::READ})};
        AstLoop* const finalLoopp = new AstLoop{flp};
        AstIf* const finalBodypCondp
            = new AstIf{flp, condp->cloneTreePure(false), new AstPExprClause{flp},
                        new AstPExprClause{flp, false}};
        finalLoopp->addStmtsp(
            new AstLoopTest{flp, finalLoopp,
                            new AstNeq{flp, new AstVarRef{flp, activeCountp, VAccess::READ},
                                       new AstConst{flp, 0}}});
        finalLoopp->addStmtsp(finalBodypCondp);
        finalLoopp->addStmtsp(
            new AstAssign{flp, new AstVarRef{flp, activeCountp, VAccess::WRITE},
                          new AstSub{flp, new AstVarRef{flp, activeCountp, VAccess::READ},
                                     new AstConst{flp, 1}}});

        // Final assertion block
        AstBegin* const finalp = new AstBegin{flp, "", nullptr, true};
        finalp->addStmtsp(activeCountp);
        finalp->addStmtsp(initActiveCountp);
        finalp->addStmtsp(finalLoopp);

        m_pexprp = new AstPExpr{flp, bodyp, finalp, nodep->dtypep()};
        VL_RESTORER(m_hasCycleDelay);
        m_hasCycleDelay = false;
        iterate(bodyp);
        iterate(finalp);

        if (m_hasCycleDelay) {
            nodep->v3warn(E_UNSUPPORTED, "Unsupported: cycle delay in s_eventually");
            nodep->replaceWith(new AstConst{nodep->fileline(), AstConst::BitFalse{}});
            VL_DO_DANGLING(pushDeletep(nodep), nodep);
            VL_DO_DANGLING(m_pexprp->deleteTree(), m_pexprp);
            return;
        }

        nodep->replaceWith(m_pexprp);
        VL_DO_DANGLING(pushDeletep(nodep), nodep);
    }
    void visit(AstStable* nodep) override {
        if (nodep->user1SetOnce()) return;
        iterateChildren(nodep);
        FileLine* const fl = nodep->fileline();
        AstNodeExpr* exprp = nodep->exprp()->unlinkFrBack();
        AstSenTree* sentreep = nodep->sentreep();
        if (sentreep) sentreep->unlinkFrBack();
        AstPast* const pastp = new AstPast{fl, exprp};
        pastp->dtypeFrom(exprp);
        pastp->sentreep(newSenTree(nodep, sentreep));
        exprp = new AstEq{fl, pastp, exprp->cloneTreePure(false)};
        exprp->dtypeSetBit();
        nodep->replaceWith(exprp);
        VL_DO_DANGLING(pushDeletep(nodep), nodep);
    }
    void visit(AstSteady* nodep) override {
        if (nodep->user1SetOnce()) return;
        iterateChildren(nodep);
        FileLine* const fl = nodep->fileline();
        AstNodeExpr* exprp = nodep->exprp()->unlinkFrBack();
        if (exprp->width() > 1) exprp = new AstSel{fl, exprp, 0, 1};
        AstNodeExpr* const futurep = new AstFuture{fl, exprp, newSenTree(nodep)};
        futurep->dtypeFrom(exprp);
        exprp = new AstEq{fl, exprp->cloneTreePure(false), futurep};
        exprp->dtypeSetBit();
        nodep->replaceWith(exprp);
        VL_DO_DANGLING(pushDeletep(nodep), nodep);
    }

    // Validate repetition count: must be a non-negative elaboration-time constant.
    // Shared by goto [->N] and nonconsecutive [=N] repetition.
    // On error, replaces nodep with BitFalse placeholder and returns nullptr.
    const AstConst* validateRepCount(AstNode* nodep, AstNodeExpr*& countp) {
        countp = V3Const::constifyEdit(countp);
        const AstConst* const constp = VN_CAST(countp, Const);
        if (!constp) {
            nodep->v3error("Repetition count is not an elaboration-time constant"
                           " (IEEE 1800-2023 16.9.2)");
            VL_DO_DANGLING(pushDeletep(countp), countp);
            nodep->replaceWith(new AstConst{nodep->fileline(), AstConst::BitFalse{}});
            VL_DO_DANGLING(pushDeletep(nodep), nodep);
            return nullptr;
        }
        if (constp->toSInt() < 0) {
            nodep->v3error("Repetition count must be non-negative"
                           " (IEEE 1800-2023 16.9.2)");
            VL_DO_DANGLING(pushDeletep(countp), countp);
            nodep->replaceWith(new AstConst{nodep->fileline(), AstConst::BitFalse{}});
            VL_DO_DANGLING(pushDeletep(nodep), nodep);
            return nullptr;
        }
        if (constp->isZero()) {
            nodep->v3warn(E_UNSUPPORTED, "Unsupported: zero repetition count"
                                         " (IEEE 1800-2023 16.9.2)");
            VL_DO_DANGLING(pushDeletep(countp), countp);
            nodep->replaceWith(new AstConst{nodep->fileline(), AstConst::BitFalse{}});
            VL_DO_DANGLING(pushDeletep(nodep), nodep);
            return nullptr;
        }
        return constp;
    }

    // Lower goto/nonconsecutive repetition to a counter-based PExpr loop.
    // IEEE 1800-2023 16.9.2:
    //   Goto [->N]: count N occurrences, then check consequent
    //   Nonconsec [=N] = [->N] ##1 !b[*0:$]: count N, then scan trailing !b window
    // Generated structure for goto [->N]:
    //   begin
    //     automatic uint32 cnt = 0;
    //     loop { test(cnt < N); if (sampled(expr)) cnt++; if (cnt < N) @(clk); }
    //     // consequent check or pass clause
    //   end
    // Generated structure for nonconsec [=N] with implication:
    //   begin
    //     automatic uint32 cnt = 0;
    //     loop { test(cnt < N); if (sampled(expr)) cnt++; if (cnt < N) @(clk); }
    //     @(clk);  // ##1
    //     if (!isOverlapped) @(clk);  // |=> delay
    //     loop { if (sampled(expr)) fail; if (sampled(rhs)) pass; @(clk); }
    //   end
    AstPExpr* createRepPExpr(FileLine* flp, AstNodeExpr* exprp, AstNodeExpr* countp,
                             AstNodeExpr* rhsp, bool isOverlapped, bool isNonConsec) {
        AstSenItem* const sensesp = m_senip;
        UASSERT_OBJ(sensesp, exprp, "Repetition requires a clock");

        const std::string name
            = isNonConsec ? m_nonConsRepNames.get(exprp) : m_gotoRepNames.get(exprp);
        AstVar* const cntVarp = new AstVar{flp, VVarType::BLOCKTEMP, name + "__counter",
                                           exprp->findBasicDType(VBasicDTypeKwd::UINT32)};
        cntVarp->lifetime(VLifetime::AUTOMATIC_EXPLICIT);

        AstBegin* const beginp = new AstBegin{flp, name + "__block", cntVarp, true};
        beginp->addStmtsp(
            new AstAssign{flp, new AstVarRef{flp, cntVarp, VAccess::WRITE}, new AstConst{flp, 0}});

        // Counting loop: find N occurrences of expr (shared by goto and nonconsec)
        AstLoop* const loopp = new AstLoop{flp};
        loopp->addStmtsp(new AstLoopTest{flp, loopp,
                                         new AstLt{flp, new AstVarRef{flp, cntVarp, VAccess::READ},
                                                   countp->cloneTreePure(false)}});
        // if (expr) cnt++ -- sampled is applied to whole property expr by V3Assert
        loopp->addStmtsp(
            new AstIf{flp, exprp,
                      new AstAssign{flp, new AstVarRef{flp, cntVarp, VAccess::WRITE},
                                    new AstAdd{flp, new AstVarRef{flp, cntVarp, VAccess::READ},
                                               new AstConst{flp, 1}}}});
        loopp->addStmtsp(new AstIf{
            flp, new AstLt{flp, new AstVarRef{flp, cntVarp, VAccess::READ}, countp},
            new AstEventControl{flp, new AstSenTree{flp, sensesp->cloneTree(false)}, nullptr}});

        beginp->addStmtsp(loopp);

        if (isNonConsec && rhsp) {
            // IEEE 16.9.2: b[=N] = b[->N] ##1 !b[*0:$]
            // Trailing window: ##1 advance, then scan !expr cycles checking rhs.
            // Window closes when expr becomes true again (fail if rhs was never true).
            beginp->addStmtsp(new AstEventControl{
                flp, new AstSenTree{flp, sensesp->cloneTree(false)}, nullptr});  // ##1
            if (!isOverlapped) {
                beginp->addStmtsp(new AstEventControl{
                    flp, new AstSenTree{flp, sensesp->cloneTree(false)}, nullptr});  // |=>
            }
            // Window loop: check rhs at each !expr cycle (done variable for termination)
            AstVar* const doneVarp
                = new AstVar{flp, VVarType::BLOCKTEMP, name + "__done", exprp->findBitDType()};
            doneVarp->lifetime(VLifetime::AUTOMATIC_EXPLICIT);
            beginp->addStmtsp(doneVarp);
            beginp->addStmtsp(new AstAssign{flp, new AstVarRef{flp, doneVarp, VAccess::WRITE},
                                            new AstConst{flp, AstConst::BitFalse{}}});
            auto setDone = [&]() {
                return new AstAssign{flp, new AstVarRef{flp, doneVarp, VAccess::WRITE},
                                     new AstConst{flp, AstConst::BitTrue{}}};
            };
            AstLoop* const windowp = new AstLoop{flp};
            // LoopTest: continue while !done
            windowp->addStmtsp(new AstLoopTest{
                flp, windowp, new AstNot{flp, new AstVarRef{flp, doneVarp, VAccess::READ}}});
            // if (expr) { fail; done = 1; } -- window closed, expr true again
            AstBegin* const failBlockp = new AstBegin{flp, "", nullptr, true};
            failBlockp->addStmtsp(new AstPExprClause{flp, false});
            failBlockp->addStmtsp(setDone());
            windowp->addStmtsp(new AstIf{flp, exprp->cloneTreePure(false), failBlockp});
            // if (rhs) { pass; done = 1; } -- consequent true at this !expr endpoint
            AstBegin* const passBlockp = new AstBegin{flp, "", nullptr, true};
            passBlockp->addStmtsp(new AstPExprClause{flp, true});
            passBlockp->addStmtsp(setDone());
            windowp->addStmtsp(new AstIf{flp, rhsp, passBlockp});
            // @(clk) -- advance to next cycle in window
            windowp->addStmtsp(
                new AstEventControl{flp, new AstSenTree{flp, sensesp->cloneTree(false)}, nullptr});
            beginp->addStmtsp(windowp);
        } else if (isNonConsec) {
            // Standalone nonconsec: ##1 into window, then pass
            beginp->addStmtsp(
                new AstEventControl{flp, new AstSenTree{flp, sensesp->cloneTree(false)}, nullptr});
            beginp->addStmtsp(new AstPExprClause{flp, true});
        } else if (rhsp) {
            // Goto rep: check consequent once at match endpoint
            if (!isOverlapped) {
                beginp->addStmtsp(new AstEventControl{
                    flp, new AstSenTree{flp, sensesp->cloneTree(false)}, nullptr});
            }
            beginp->addStmtsp(new AstIf{flp, rhsp, new AstPExprClause{flp, true},
                                        new AstPExprClause{flp, false}});
        } else {
            // Standalone goto: pass after counting
            beginp->addStmtsp(new AstPExprClause{flp, true});
        }

        return new AstPExpr{flp, beginp, exprp->findBitDType()};
    }

    void visit(AstSGotoRep* nodep) override {
        // Standalone goto rep (not inside implication antecedent)
        iterateChildren(nodep);
        FileLine* const flp = nodep->fileline();
        AstNodeExpr* countp = nodep->countp()->unlinkFrBack();
        if (!validateRepCount(nodep, countp)) return;
        AstNodeExpr* const exprp = nodep->exprp()->unlinkFrBack();
        AstPExpr* const pexprp = createRepPExpr(flp, exprp, countp, nullptr, true, false);
        nodep->replaceWith(pexprp);
        VL_DO_DANGLING(pushDeletep(nodep), nodep);
    }

    void visit(AstSNonConsRep* nodep) override {
        // Standalone nonconsecutive rep (not inside implication antecedent)
        iterateChildren(nodep);
        FileLine* const flp = nodep->fileline();
        AstNodeExpr* countp = nodep->countp()->unlinkFrBack();
        if (!validateRepCount(nodep, countp)) return;
        AstNodeExpr* const exprp = nodep->exprp()->unlinkFrBack();
        AstPExpr* const pexprp = createRepPExpr(flp, exprp, countp, nullptr, true, true);
        nodep->replaceWith(pexprp);
        VL_DO_DANGLING(pushDeletep(nodep), nodep);
    }

    void visit(AstFuncRef* nodep) override {
        // IEEE 1800-2023 16.8: Inline sequence instances wherever they appear
        // in the expression tree (inside implications, boolean ops, nested refs, etc.)
        if (AstSequence* const seqp = VN_CAST(nodep->taskp(), Sequence)) {
            substituteSequenceCall(nodep, seqp);
            // The FuncRef has been replaced; do not access nodep after this point.
            // The replacement node will be visited by the parent's iterateChildren.
            return;
        }
        iterateChildren(nodep);
    }
    void visit(AstImplication* nodep) override {
        if (nodep->sentreep()) return;  // Already processed

        // Top-level followed-by is claimed by V3AssertNfa; anything reaching here
        // is nested inside iff/implies/or. IEEE 1800-2023 16.12.9 permits the
        // composition, but silent lowering would drop non-vacuous-fail semantics.
        if (nodep->isFollowedBy()) {
            nodep->v3warn(E_UNSUPPORTED,
                          "Unsupported: followed-by (#-# / #=#) nested inside property operator"
                          " (iff/implies/or) (IEEE 1800-2023 16.12.9)");
            nodep->replaceWith(new AstConst{nodep->fileline(), AstConst::BitFalse{}});
            VL_DO_DANGLING(pushDeletep(nodep), nodep);
            return;
        }

        // Handle goto repetition as antecedent before iterateChildren,
        // so the standalone AstSGotoRep visitor doesn't process it
        if (AstSGotoRep* const gotop = VN_CAST(nodep->lhsp(), SGotoRep)) {
            iterateChildren(gotop);
            iterateAndNextNull(nodep->rhsp());
            FileLine* const flp = nodep->fileline();
            AstNodeExpr* countp = gotop->countp()->unlinkFrBack();
            if (!validateRepCount(nodep, countp)) return;
            AstNodeExpr* const exprp = gotop->exprp()->unlinkFrBack();
            AstNodeExpr* const rhsp = nodep->rhsp()->unlinkFrBack();
            AstPExpr* const pexprp
                = createRepPExpr(flp, exprp, countp, rhsp, nodep->isOverlapped(), false);
            nodep->replaceWith(pexprp);
            VL_DO_DANGLING(pushDeletep(nodep), nodep);
            return;
        }

        // Handle nonconsecutive repetition as antecedent before iterateChildren,
        // so the standalone AstSNonConsRep visitor doesn't process it
        if (AstSNonConsRep* const ncrp = VN_CAST(nodep->lhsp(), SNonConsRep)) {
            iterateChildren(ncrp);
            iterateAndNextNull(nodep->rhsp());
            FileLine* const flp = nodep->fileline();
            AstNodeExpr* countp = ncrp->countp()->unlinkFrBack();
            if (!validateRepCount(nodep, countp)) return;
            AstNodeExpr* const exprp = ncrp->exprp()->unlinkFrBack();
            AstNodeExpr* const rhsp = nodep->rhsp()->unlinkFrBack();
            AstPExpr* const pexprp
                = createRepPExpr(flp, exprp, countp, rhsp, nodep->isOverlapped(), true);
            nodep->replaceWith(pexprp);
            VL_DO_DANGLING(pushDeletep(nodep), nodep);
            return;
        }

        iterateChildren(nodep);

        FileLine* const flp = nodep->fileline();
        AstNodeExpr* const rhsp = nodep->rhsp()->unlinkFrBack();
        AstNodeExpr* lhsp = nodep->lhsp()->unlinkFrBack();

        // Lower sequence match items (IEEE 16.11): (expr, var = val, ...) |-> / |=>
        if (AstExprStmt* const exprStmtp = VN_CAST(lhsp, ExprStmt)) {
            AstNodeExpr* const antExprp = exprStmtp->resultp()->unlinkFrBack();

            if (nodep->isOverlapped()) {
                // |-> : assign to __Vpropvar via always_comb (continuous).
                // The assign evaluates RHS once; V3Sampled snapshots the
                // result so all consequent refs read the same value.
                AstNode* matchAssignsp = nullptr;
                for (AstNode* stmtp = exprStmtp->stmtsp(); stmtp;) {
                    AstNode* const nextp = stmtp->nextp();
                    if (AstAssign* const assignp = VN_CAST(stmtp, Assign)) {
                        assignp->unlinkFrBack();
                        if (!matchAssignsp) {
                            matchAssignsp = assignp;
                        } else {
                            matchAssignsp->addNext(assignp);
                        }
                    }
                    stmtp = nextp;
                }
                VL_DO_DANGLING(pushDeletep(lhsp), lhsp);
                lhsp = antExprp;

                if (matchAssignsp) {
                    AstAlways* const alwaysp
                        = new AstAlways{flp, VAlwaysKwd::ALWAYS_COMB, nullptr, matchAssignsp};
                    m_modp->addStmtsp(alwaysp);
                }
            } else {
                // |=> : assign to __Vpropvar via NBA in a clocked always block.
                // The NBA commits before the next cycle's sampled snapshot,
                // so the consequent (which already references __Vpropvar)
                // sees the captured value.
                AstNode* matchAssignsp = nullptr;
                for (AstNode* stmtp = exprStmtp->stmtsp(); stmtp;) {
                    AstNode* const nextp = stmtp->nextp();
                    if (AstAssign* const assignp = VN_CAST(stmtp, Assign)) {
                        assignp->unlinkFrBack();
                        AstNodeExpr* const assignLhsp = assignp->lhsp()->unlinkFrBack();
                        AstNodeExpr* const assignRhsp = assignp->rhsp()->unlinkFrBack();
                        AstAssignDly* const dlyp = new AstAssignDly{flp, assignLhsp, assignRhsp};
                        VL_DO_DANGLING(pushDeletep(assignp), assignp);
                        if (!matchAssignsp) {
                            matchAssignsp = dlyp;
                        } else {
                            matchAssignsp->addNext(dlyp);
                        }
                    }
                    stmtp = nextp;
                }
                VL_DO_DANGLING(pushDeletep(lhsp), lhsp);
                lhsp = antExprp;

                if (matchAssignsp) {
                    AstIf* const condp
                        = new AstIf{flp, antExprp->cloneTreePure(false), matchAssignsp};
                    AstAlways* const alwaysp
                        = new AstAlways{flp, VAlwaysKwd::ALWAYS, newSenTree(nodep), condp};
                    m_modp->addStmtsp(alwaysp);
                }
            }
        }

        if (AstPExpr* const pexprp = VN_CAST(rhsp, PExpr)) {
            // Implication with sequence expression on RHS (IEEE 1800-2023 16.11, 16.12.7).
            // The PExpr was lowered from the property expression earlier in this pass.
            // Wrap the PExpr body with the antecedent check so the sequence only
            // starts when the antecedent holds.
            AstNodeExpr* condp;
            if (nodep->isOverlapped()) {
                // Overlapped implication (|->): check antecedent on same cycle.
                // disable iff is applied at the assertion level, not at the
                // antecedent gate, matching the existing non-PExpr overlapped path.
                condp = lhsp;
            } else {
                // Non-overlapped implication (|=>): check antecedent from previous cycle
                if (m_disablep) {
                    lhsp
                        = new AstAnd{flp, new AstNot{flp, m_disablep->cloneTreePure(false)}, lhsp};
                }
                AstPast* const pastp = new AstPast{flp, lhsp};
                pastp->dtypeFrom(lhsp);
                pastp->sentreep(newSenTree(nodep));
                condp = pastp;
            }
            // Wrap existing PExpr body: if (antecedent) { <original body> } else { /* vacuous pass
            // */ }
            AstBegin* const bodyp = pexprp->bodyp();
            AstNode* const origStmtsp = bodyp->stmtsp()->unlinkFrBackWithNext();
            AstIf* const guardp = new AstIf{flp, condp, new AstBegin{flp, "", origStmtsp, true}};
            bodyp->addStmtsp(guardp);
            nodep->replaceWith(pexprp);
            // Don't iterate pexprp here -- it was already iterated when created
            // (in visit(AstSExpr*)), so delays and disable iff are already processed.
        } else if (nodep->isOverlapped()) {
            nodep->replaceWith(new AstLogOr{flp, new AstLogNot{flp, lhsp}, rhsp});
        } else {
            if (m_disablep) {
                lhsp = new AstAnd{flp, new AstNot{flp, m_disablep->cloneTreePure(false)}, lhsp};
            }

            AstPast* const pastp = new AstPast{flp, lhsp};
            pastp->dtypeFrom(lhsp);
            pastp->sentreep(newSenTree(nodep));
            AstNodeExpr* const exprp = new AstOr{flp, new AstNot{flp, pastp}, rhsp};
            exprp->dtypeSetBit();
            nodep->replaceWith(exprp);
        }
        VL_DO_DANGLING(pushDeletep(nodep), nodep);
    }
    void visit(AstUntil* nodep) override {
        FileLine* const flp = nodep->fileline();
        if (m_pexprp) {
            nodep->v3warn(E_UNSUPPORTED, "Unsupported: 'until' in complex property expression");
            nodep->replaceWith(new AstConst{flp, AstConst::BitFalse{}});
            VL_DO_DANGLING(pushDeletep(nodep), nodep);
            return;
        }
        if (nodep->isStrong()) {
            nodep->v3warn(E_UNSUPPORTED, "Unsupported: s_until"
                                             << (nodep->isOverlapping() ? "_with" : "")
                                             << " (in property expresion)");
            nodep->replaceWith(new AstConst{flp, AstConst::BitFalse{}});
            VL_DO_DANGLING(pushDeletep(nodep), nodep);
            return;
        }
        AstLoop* const loopp = new AstLoop{flp};
        AstNodeExpr* const rhsp = nodep->rhsp()->unlinkFrBack();
        AstNodeExpr* const lhsp = nodep->lhsp()->unlinkFrBack();
        AstLogAnd* const loopCondp = new AstLogAnd{flp, lhsp, new AstLogNot{flp, rhsp}};
        loopp->addStmtsp(new AstLoopTest{flp, loopp, loopCondp});
        loopp->addStmtsp(new AstEventControl{flp, newSenTree(nodep), nullptr});

        AstNodeExpr* const rhsCopyp = rhsp->cloneTreePure(false);
        AstNodeExpr* const passCondp
            = nodep->isOverlapping() ? new AstLogAnd{flp, lhsp->cloneTreePure(false), rhsCopyp}
                                     : rhsCopyp;
        AstBegin* const beginp = new AstBegin{flp, "", loopp, true};
        beginp->addStmtsp(
            new AstIf{flp, passCondp, new AstPExprClause{flp}, new AstPExprClause{flp, false}});

        AstPExpr* const pexprp = new AstPExpr{flp, beginp, nodep->dtypep()};
        pexprp->user1(1);
        nodep->replaceWith(pexprp);
        VL_DO_DANGLING(pushDeletep(nodep), nodep);
    }

    void visit(AstDefaultDisable* nodep) override {
        if (m_defaultDisablep) {
            nodep->v3error("Only one 'default disable iff' allowed per module"
                           " (IEEE 1800-2023 16.15)");
        } else {
            m_defaultDisablep = nodep;
        }
        VL_DO_DANGLING(pushDeletep(nodep->unlinkFrBack()), nodep);
    }
    void visit(AstInferredDisable* nodep) override {
        AstNode* newp;
        if (m_defaultDisablep) {
            newp = m_defaultDisablep->condp()->cloneTreePure(true);
        } else {
            newp = new AstConst{nodep->fileline(), AstConst::BitFalse{}};
        }
        nodep->replaceWith(newp);
        VL_DO_DANGLING(pushDeletep(nodep), nodep);
    }

    void visit(AstPropSpec* nodep) override {
        nodep = substitutePropertyCall(nodep);
        iterateAndNextNull(nodep->sensesp());
        if (m_senip && m_senip != nodep->sensesp())
            nodep->v3warn(E_UNSUPPORTED, "Unsupported: Only one PSL clock allowed per assertion");
        if (!nodep->disablep() && m_defaultDisablep) {
            nodep->disablep(m_defaultDisablep->condp()->cloneTreePure(true));
        }
        m_disablep = nodep->disablep();
        // Unlink and just keep a pointer to it, convert to sentree as needed
        m_senip = nodep->sensesp();
        iterateNull(nodep->disablep());
        if (!VN_AS(nodep->backp(), NodeCoverOrAssert)->immediate()) {
            const AstNodeDType* const propDtp = nodep->propp()->dtypep();
            nodep->propp(new AstSampled{nodep->fileline(), nodep->propp()->unlinkFrBack()});
            nodep->propp()->dtypeFrom(propDtp);
        }
        iterate(nodep->propp());
    }
    void visit(AstPExpr* nodep) override {
        // V3AssertNfa handles multi-cycle property expressions before this pass,
        // so the following unsupported paths are defensive and typically unreached.
        if (m_pexprp && m_pexprp->user1()) {  // LCOV_EXCL_START
            nodep->v3warn(E_UNSUPPORTED,
                          "Unsupported: Complex property expression inside 'until''");
            nodep->replaceWith(new AstConst{nodep->fileline(), AstConst::BitFalse{}});
            VL_DO_DANGLING(pushDeletep(nodep), nodep);
            return;
        }  // LCOV_EXCL_STOP
        if (AstLogNot* const notp = VN_CAST(nodep->backp(), LogNot)) {
            notp->replaceWith(nodep->unlinkFrBack());
            VL_DO_DANGLING(pushDeletep(notp), notp);
            iterate(nodep);
            return;
        }
        // Sequence expression as antecedent of implication is not yet supported
        if (AstImplication* const implp = VN_CAST(nodep->backp(), Implication)) {
            if (implp->lhsp() == nodep) {  // LCOV_EXCL_START
                implp->v3warn(E_UNSUPPORTED,
                              "Unsupported: Implication with sequence expression as antecedent");
                nodep->replaceWith(new AstConst{nodep->fileline(), AstConst::BitFalse{}});
                VL_DO_DANGLING(pushDeletep(nodep), nodep);
                return;
            }  // LCOV_EXCL_STOP
        }
        VL_RESTORER(m_pexprp);
        VL_RESTORER(m_disableSeqIfp);
        m_pexprp = nodep;

        if (m_disablep) {
            const AstSampled* sampledp = nullptr;
            if (m_disablep->exists([&sampledp](const AstSampled* const sp) {
                    sampledp = sp;
                    return true;
                })) {
                sampledp->v3warn(E_UNSUPPORTED,
                                 "Unsupported: $sampled inside disabled condition of a sequence");
                m_disablep = new AstConst{m_disablep->fileline(), AstConst::BitFalse{}};
                // always a copy is used, so remove it now
                pushDeletep(m_disablep);
            }
            FileLine* const flp = nodep->fileline();
            // Add counter which counts times the condition turned true
            AstVar* const disableCntp
                = new AstVar{flp, VVarType::MODULETEMP, m_disableCntNames.get(""),
                             nodep->findBasicDType(VBasicDTypeKwd::UINT32)};
            disableCntp->lifetime(VLifetime::STATIC_EXPLICIT);
            m_modp->addStmtsp(disableCntp);
            AstVarRef* const readCntRefp = new AstVarRef{flp, disableCntp, VAccess::READ};
            AstVarRef* const writeCntRefp = new AstVarRef{flp, disableCntp, VAccess::WRITE};
            AstAssign* const incrStmtp = new AstAssign{
                flp, writeCntRefp, new AstAdd{flp, readCntRefp, new AstConst{flp, 1}}};
            AstAlways* const alwaysp
                = new AstAlways{flp, VAlwaysKwd::ALWAYS,
                                new AstSenTree{flp, new AstSenItem{flp, VEdgeType::ET_POSEDGE,
                                                                   m_disablep->cloneTree(false)}},
                                incrStmtp};
            disableCntp->addNextHere(alwaysp);

            // Store value of that counter at the beginning of sequence evaluation
            AstBegin* const bodyp = nodep->bodyp();
            AstVar* const initialCntp = new AstVar{flp, VVarType::BLOCKTEMP, "__VinitialCnt",
                                                   nodep->findBasicDType(VBasicDTypeKwd::UINT32)};
            initialCntp->lifetime(VLifetime::AUTOMATIC_EXPLICIT);
            AstAssign* const assignp
                = new AstAssign{flp, new AstVarRef{flp, initialCntp, VAccess::WRITE},
                                readCntRefp->cloneTree(false)};
            // Prepend to the sequence body to keep statement list structure valid.
            AstNode* const origStmtsp = bodyp->stmtsp()->unlinkFrBackWithNext();
            bodyp->addStmtsp(initialCntp);
            initialCntp->addNextHere(assignp);
            assignp->addNextHere(origStmtsp);

            m_disableSeqIfp
                = new AstIf{flp, new AstEq{flp, new AstVarRef{flp, initialCntp, VAccess::READ},
                                           readCntRefp->cloneTree(false)}};
            // Delete it, because it is always copied before insetion to the AST
            pushDeletep(m_disableSeqIfp);
        }
        iterateChildren(nodep);
    }
    void visit(AstNodeModule* nodep) override {
        VL_RESTORER(m_defaultClockingp);
        VL_RESTORER(m_defaultClkEvtVarp);
        VL_RESTORER(m_defaultDisablep);
        VL_RESTORER(m_modp);
        m_defaultClockingp = nullptr;
        m_defaultClkEvtVarp = nullptr;
        m_defaultDisablep = nullptr;
        m_modp = nodep;
        iterateChildren(nodep);
    }
    void visit(AstProperty* nodep) override {
        // The body will be visited when will be substituted in place of property reference
        // (AstFuncRef)
        VL_DO_DANGLING(pushDeletep(nodep->unlinkFrBack()), nodep);
    }
    void visit(AstSequence* nodep) override {
        // Sequence declarations are not visited directly; their bodies are inlined
        // at call sites by visit(AstFuncRef*). Collect for post-traversal cleanup.
        m_seqsToCleanup.push_back(nodep);
    }
    void visit(AstNode* nodep) override { iterateChildren(nodep); }

public:
    // CONSTRUCTORS
    explicit AssertPreVisitor(AstNetlist* nodep)
        : m_netlistp{nodep} {
        // Process
        iterate(nodep);
        // Fix up varref names
        for (AstVarXRef* xrefp : m_xrefsp) xrefp->name(xrefp->varp()->name());
        // Clean up sequence declarations after inlining.
        // Referenced sequences that were inlined have isReferenced cleared.
        // Remaining referenced sequences are in unsupported contexts (e.g. @seq event).
        for (AstSequence* seqp : m_seqsToCleanup) {
            if (seqp->isReferenced()) {
                seqp->v3warn(E_UNSUPPORTED,
                             "Unsupported: sequence referenced outside assertion property");
            } else {
                VL_DO_DANGLING(seqp->unlinkFrBack()->deleteTree(), seqp);
            }
        }
    }
    ~AssertPreVisitor() override = default;
};

//######################################################################
// Top Assert class

void V3AssertPre::assertPreAll(AstNetlist* nodep) {
    UINFO(2, __FUNCTION__ << ":");
    { AssertPreVisitor{nodep}; }  // Destruct before checking
    V3Global::dumpCheckGlobalTree("assertpre", 0, dumpTreeEitherLevel() >= 3);
}
