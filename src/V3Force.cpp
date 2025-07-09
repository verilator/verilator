// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Covert forceable signals, process force/release
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
//  V3Force's Transformations:
//
//  For each forceable net with name "<name>":
//      add 3 extra signals:
//          - <name>__VforceRd: a net with same type as signal
//          - <name>__VforceEn: a var with same type as signal, which is the bitwise force enable
//          - <name>__VforceVal: a var with same type as signal, which is the forced value
//      add an initial statement:
//          initial <name>__VforceEn = 0;
//      add a continuous assignment:
//          assign <name>__VforceRd = <name>__VforceEn ? <name>__VforceVal : <name>;
//      replace all READ references to <name> with a read reference to <name>_VforceRd
//
//  Replace each AstAssignForce with 3 assignments:
//      - <lhs>__VforceEn = 1
//      - <lhs>__VforceVal = <rhs>
//      - <lhs>__VforceRd = <rhs>
//
//  Replace each AstRelease with 1 or 2 assignments:
//      - <lhs>__VforceEn = 0
//      - <lhs>__VforceRd = <lhs> // iff lhs is a net
//
//  After each WRITE of forced LHS
//      reevaluate <lhs>__VforceRd to support immediate force/release
//
//  After each WRITE of forced RHS
//      reevaluate <lhs>__VforceVal to support VarRef rollback after release
//*************************************************************************

#include "V3PchAstNoMT.h"  // VL_MT_DISABLED_CODE_UNIT

#include "V3Force.h"

#include "V3AstUserAllocator.h"

VL_DEFINE_DEBUG_FUNCTIONS;

//######################################################################
// Convert force/release statements and signals marked 'forceable'

class ForceState final {
    // TYPES
    struct ForceComponentsVar final {
        AstVar* const m_rdVarp;  // New variable to replace read references with
        AstVar* const m_valVarp;  // Forced value
        AstVar* const m_enVarp;  // Force enabled signal
        explicit ForceComponentsVar(AstVar* varp)
            : m_rdVarp{new AstVar{varp->fileline(), VVarType::WIRE, varp->name() + "__VforceRd",
                                  varp->dtypep()}}
            , m_valVarp{new AstVar{varp->fileline(), VVarType::VAR, varp->name() + "__VforceVal",
                                   varp->dtypep()}}
            , m_enVarp{new AstVar{
                  varp->fileline(), VVarType::VAR, varp->name() + "__VforceEn",
                  (ForceState::isRangedDType(varp) ? varp->dtypep() : varp->findBitDType())}} {
            m_rdVarp->addNext(m_enVarp);
            m_rdVarp->addNext(m_valVarp);
            varp->addNextHere(m_rdVarp);
        }
    };

public:
    struct ForceComponentsVarScope final {
        AstVarScope* const m_rdVscp;  // New variable to replace read references with
        AstVarScope* const m_valVscp;  // Forced value
        AstVarScope* const m_enVscp;  // Force enabled signal
        explicit ForceComponentsVarScope(AstVarScope* vscp, ForceComponentsVar& fcv)
            : m_rdVscp{new AstVarScope{vscp->fileline(), vscp->scopep(), fcv.m_rdVarp}}
            , m_valVscp{new AstVarScope{vscp->fileline(), vscp->scopep(), fcv.m_valVarp}}
            , m_enVscp{new AstVarScope{vscp->fileline(), vscp->scopep(), fcv.m_enVarp}} {
            m_rdVscp->addNext(m_enVscp);
            m_rdVscp->addNext(m_valVscp);
            vscp->addNextHere(m_rdVscp);

            FileLine* const flp = vscp->fileline();

            {  // Add initialization of the enable signal
                AstVarRef* const lhsp = new AstVarRef{flp, m_enVscp, VAccess::WRITE};
                V3Number zero{m_enVscp, m_enVscp->width()};
                zero.setAllBits0();
                AstNodeExpr* const rhsp = new AstConst{flp, zero};
                AstAssign* const assignp = new AstAssign{flp, lhsp, rhsp};
                AstActive* const activep = new AstActive{
                    flp, "force-init",
                    new AstSenTree{flp, new AstSenItem{flp, AstSenItem::Static{}}}};
                activep->sensesStorep(activep->sensesp());

                activep->addStmtsp(new AstInitial{flp, assignp});
                vscp->scopep()->addBlocksp(activep);
            }
            {  // Add the combinational override
                AstVarRef* const lhsp = new AstVarRef{flp, m_rdVscp, VAccess::WRITE};
                AstNodeExpr* const rhsp = forcedUpdate(vscp);

                // Explicitly list dependencies for update.
                // Note: rdVscp is also needed to retrigger assignment for the first time.
                AstSenItem* const itemsp = new AstSenItem{
                    flp, VEdgeType::ET_CHANGED, new AstVarRef{flp, m_rdVscp, VAccess::READ}};
                itemsp->addNext(new AstSenItem{flp, VEdgeType::ET_CHANGED,
                                               new AstVarRef{flp, m_valVscp, VAccess::READ}});
                itemsp->addNext(new AstSenItem{flp, VEdgeType::ET_CHANGED,
                                               new AstVarRef{flp, m_enVscp, VAccess::READ}});
                AstVarRef* const origp = new AstVarRef{flp, vscp, VAccess::READ};
                ForceState::markNonReplaceable(origp);
                itemsp->addNext(
                    new AstSenItem{flp, VEdgeType::ET_CHANGED, origp->cloneTree(false)});
                AstActive* const activep
                    = new AstActive{flp, "force-update", new AstSenTree{flp, itemsp}};
                activep->sensesStorep(activep->sensesp());
                activep->addStmtsp(new AstAlways{flp, VAlwaysKwd::ALWAYS, nullptr,
                                                 new AstAssign{flp, lhsp, rhsp}});
                vscp->scopep()->addBlocksp(activep);
            }
        }
        AstNodeExpr* forcedUpdate(AstVarScope* const vscp) const {
            FileLine* const flp = vscp->fileline();
            AstVarRef* const origp = new AstVarRef{flp, vscp, VAccess::READ};
            ForceState::markNonReplaceable(origp);
            if (ForceState::isRangedDType(vscp)) {
                return new AstOr{
                    flp,
                    new AstAnd{flp, new AstVarRef{flp, m_enVscp, VAccess::READ},
                               new AstVarRef{flp, m_valVscp, VAccess::READ}},
                    new AstAnd{flp, new AstNot{flp, new AstVarRef{flp, m_enVscp, VAccess::READ}},
                               origp}};
            }
            return new AstCond{flp, new AstVarRef{flp, m_enVscp, VAccess::READ},
                               new AstVarRef{flp, m_valVscp, VAccess::READ}, origp};
        }
    };

private:
    // NODE STATE
    //  AstVar::user1p        -> ForceComponentsVar* instance (via m_forceComponentsVar)
    //  AstVarScope::user1p   -> ForceComponentsVarScope* instance (via m_forceComponentsVarScope)
    //  AstVarRef::user2      -> Flag indicating not to replace reference
    //  AstVarScope::user3      -> AstVarScope*, a `valVscp` force component for each VarScope of
    //  forced RHS
    const VNUser1InUse m_user1InUse;
    const VNUser2InUse m_user2InUse;
    const VNUser3InUse m_user3InUse;
    AstUser1Allocator<AstVar, ForceComponentsVar> m_forceComponentsVar;
    AstUser1Allocator<AstVarScope, ForceComponentsVarScope> m_forceComponentsVarScope;

public:
    // CONSTRUCTORS
    ForceState() = default;
    VL_UNCOPYABLE(ForceState);

    // STATIC METHODS
    static bool isRangedDType(AstNode* nodep) {
        // If ranged we need a multibit enable to support bit-by-bit part-select forces,
        // otherwise forcing a real or other opaque dtype and need a single bit enable.
        const AstBasicDType* const basicp = nodep->dtypep()->skipRefp()->basicp();
        return basicp && basicp->isRanged();
    }
    static bool isNotReplaceable(const AstVarRef* const nodep) { return nodep->user2(); }
    static void markNonReplaceable(AstVarRef* const nodep) { nodep->user2SetOnce(); }
    static AstVarScope* getValVscp(AstVarRef* const refp) {
        return VN_CAST(refp->varScopep()->user3p(), VarScope);
    }
    static void setValVscp(AstNodeVarRef* const refp, AstVarScope* const vscp) {
        refp->varScopep()->user3p(vscp);
    }

    // METHODS
    const ForceComponentsVarScope& getForceComponents(AstVarScope* vscp) {
        AstVar* const varp = vscp->varp();
        return m_forceComponentsVarScope(vscp, vscp, m_forceComponentsVar(varp, varp));
    }
    ForceComponentsVarScope* tryGetForceComponents(AstVarRef* nodep) const {
        return m_forceComponentsVarScope.tryGet(nodep->varScopep());
    }
};

class ForceConvertVisitor final : public VNVisitor {
    // STATE
    ForceState& m_state;

    // STATIC METHODS
    // Replace each AstNodeVarRef in the given 'nodep' that writes a variable by transforming the
    // referenced AstVarScope with the given function.
    static void transformWritenVarScopes(AstNode* nodep,
                                         std::function<AstVarScope*(AstVarScope*)> f) {
        UASSERT_OBJ(nodep->backp(), nodep, "Must have backp, otherwise will be lost if replaced");
        nodep->foreach([&f](AstNodeVarRef* refp) {
            if (refp->access() != VAccess::WRITE) return;
            // TODO: this is not strictly speaking safe for some complicated lvalues, eg.:
            //       'force foo[a(cnt)] = 1;', where 'cnt' is an out parameter, but it will
            //       do for now...
            refp->replaceWith(
                new AstVarRef{refp->fileline(), f(refp->varScopep()), VAccess::WRITE});
            VL_DO_DANGLING(refp->deleteTree(), refp);
        });
    }

    // VISITORS
    void visit(AstNode* nodep) override { iterateChildren(nodep); }

    void visit(AstAssignForce* nodep) override {
        // The AstAssignForce node will be removed for sure
        FileLine* const flp = nodep->fileline();
        AstNodeExpr* const lhsp = nodep->lhsp();  // The LValue we are forcing
        AstNodeExpr* const rhsp = nodep->rhsp();  // The value we are forcing it to
        VNRelinker relinker;
        nodep->unlinkFrBack(&relinker);
        VL_DO_DANGLING(pushDeletep(nodep), nodep);

        // Set corresponding enable signals to ones
        V3Number ones{lhsp, ForceState::isRangedDType(lhsp) ? lhsp->width() : 1};
        ones.setAllBits1();
        AstAssign* const setEnp
            = new AstAssign{flp, lhsp->cloneTreePure(false), new AstConst{rhsp->fileline(), ones}};
        transformWritenVarScopes(setEnp->lhsp(), [this](AstVarScope* vscp) {
            return m_state.getForceComponents(vscp).m_enVscp;
        });
        // Set corresponding value signals to the forced value
        AstAssign* const setValp
            = new AstAssign{flp, lhsp->cloneTreePure(false), rhsp->cloneTreePure(false)};
        transformWritenVarScopes(setValp->lhsp(), [this, rhsp](AstVarScope* vscp) {
            AstVarScope* const valVscp = m_state.getForceComponents(vscp).m_valVscp;
            // TODO support multiple VarRefs on RHS
            if (AstVarRef* const refp = VN_CAST(rhsp, VarRef))
                ForceState::setValVscp(refp, valVscp);
            return valVscp;
        });

        // Set corresponding read signal directly as well, in case something in the same
        // process reads it later
        AstAssign* const setRdp = new AstAssign{flp, lhsp->unlinkFrBack(), rhsp->unlinkFrBack()};
        transformWritenVarScopes(setRdp->lhsp(), [this](AstVarScope* vscp) {
            return m_state.getForceComponents(vscp).m_rdVscp;
        });

        setEnp->addNext(setValp);
        setEnp->addNext(setRdp);
        relinker.relink(setEnp);
    }

    void visit(AstRelease* nodep) override {
        FileLine* const flp = nodep->fileline();
        AstNodeExpr* const lhsp = nodep->lhsp();  // The LValue we are releasing
        // The AstRelease node will be removed for sure
        VNRelinker relinker;
        nodep->unlinkFrBack(&relinker);
        VL_DO_DANGLING(pushDeletep(nodep), nodep);

        // Set corresponding enable signals to zero
        V3Number zero{lhsp, ForceState::isRangedDType(lhsp) ? lhsp->width() : 1};
        zero.setAllBits0();
        AstAssign* const resetEnp
            = new AstAssign{flp, lhsp->cloneTreePure(false), new AstConst{lhsp->fileline(), zero}};
        transformWritenVarScopes(resetEnp->lhsp(), [this](AstVarScope* vscp) {
            return m_state.getForceComponents(vscp).m_enVscp;
        });
        // IEEE 1800-2023 10.6.2: If this is a net, and not a variable, then reset the read
        // signal directly as well, in case something in the same process reads it later. Also, if
        // it is a variable, and not a net, set the original signal to the forced value, as it
        // needs to retain the forced value until the next procedural update, which might happen on
        // a later eval. Luckily we can do all this in a single assignment.
        AstAssign* const resetRdp
            = new AstAssign{flp, lhsp->cloneTreePure(false), lhsp->unlinkFrBack()};
        // Replace write refs on the LHS
        resetRdp->lhsp()->foreach([this](AstNodeVarRef* refp) {
            if (refp->access() != VAccess::WRITE) return;
            AstVarScope* const vscp = refp->varScopep();
            AstVarScope* const newVscp = vscp->varp()->isContinuously()
                                             ? m_state.getForceComponents(vscp).m_rdVscp
                                             : vscp;
            AstVarRef* const newpRefp = new AstVarRef{refp->fileline(), newVscp, VAccess::WRITE};
            refp->replaceWith(newpRefp);
            VL_DO_DANGLING(refp->deleteTree(), refp);
        });
        // Replace write refs on RHS
        resetRdp->rhsp()->foreach([this](AstNodeVarRef* refp) {
            if (refp->access() != VAccess::WRITE) return;
            AstVarScope* const vscp = refp->varScopep();
            if (vscp->varp()->isContinuously()) {
                AstVarRef* const newpRefp = new AstVarRef{refp->fileline(), vscp, VAccess::READ};
                ForceState::markNonReplaceable(newpRefp);
                refp->replaceWith(newpRefp);
            } else {
                refp->replaceWith(m_state.getForceComponents(vscp).forcedUpdate(vscp));
            }

            VL_DO_DANGLING(refp->deleteTree(), refp);
        });

        resetRdp->addNext(resetEnp);
        relinker.relink(resetRdp);
    }

    void visit(AstVarScope* nodep) override {
        // If this signal is marked externally forceable, create the public force signals
        if (nodep->varp()->isForceable()) {
            const ForceState::ForceComponentsVarScope& fc = m_state.getForceComponents(nodep);
            fc.m_enVscp->varp()->sigUserRWPublic(true);
            fc.m_valVscp->varp()->sigUserRWPublic(true);
        }
    }

public:
    // CONSTRUCTOR
    explicit ForceConvertVisitor(AstNetlist* nodep, ForceState& state)
        : m_state{state} {
        // Transform all force and release statements
        iterateAndNextNull(nodep->modulesp());
    }
};

class ForceReplaceVisitor final : public VNVisitor {
    // STATE
    const ForceState& m_state;
    AstNodeStmt* m_stmtp = nullptr;
    bool m_inLogic = false;

    // METHODS
    void iterateLogic(AstNode* logicp) {
        VL_RESTORER(m_inLogic);
        m_inLogic = true;
        iterateChildren(logicp);
    }

    // VISITORS
    void visit(AstNodeStmt* nodep) override {
        VL_RESTORER(m_stmtp);
        m_stmtp = nodep;
        iterateChildren(nodep);
    }
    void visit(AstAlwaysPublic* nodep) override { iterateLogic(nodep); }
    void visit(AstCFunc* nodep) override { iterateLogic(nodep); }
    void visit(AstCoverToggle* nodep) override { iterateLogic(nodep); }
    void visit(AstNodeProcedure* nodep) override { iterateLogic(nodep); }
    void visit(AstSenItem* nodep) override { iterateLogic(nodep); }
    void visit(AstVarRef* nodep) override {
        if (ForceState::isNotReplaceable(nodep)) return;

        switch (nodep->access()) {
        case VAccess::READ: {
            // Replace VarRef from forced LHS with rdVscp.
            if (ForceState::ForceComponentsVarScope* const fcp
                = m_state.tryGetForceComponents(nodep)) {
                FileLine* const flp = nodep->fileline();
                AstVarRef* const origp = new AstVarRef{flp, nodep->varScopep(), VAccess::READ};
                ForceState::markNonReplaceable(origp);
                nodep->varp(fcp->m_rdVscp->varp());
                nodep->varScopep(fcp->m_rdVscp);
            }
            break;
        }
        case VAccess::WRITE: {
            if (!m_inLogic) return;
            // Emit rdVscp update after each write to any VarRef on forced LHS.
            if (ForceState::ForceComponentsVarScope* const fcp
                = m_state.tryGetForceComponents(nodep)) {
                FileLine* const flp = nodep->fileline();
                AstVarRef* const lhsp = new AstVarRef{flp, fcp->m_rdVscp, VAccess::WRITE};
                AstNodeExpr* const rhsp = fcp->forcedUpdate(nodep->varScopep());
                m_stmtp->addNextHere(new AstAssign{flp, lhsp, rhsp});
            }
            // Emit valVscp update after each write to any VarRef on forced RHS.
            if (AstVarScope* const valVscp = ForceState::getValVscp(nodep)) {
                FileLine* const flp = nodep->fileline();
                AstVarRef* const valp = new AstVarRef{flp, valVscp, VAccess::WRITE};
                AstVarRef* const rhsp = new AstVarRef{flp, nodep->varScopep(), VAccess::READ};

                ForceState::markNonReplaceable(valp);
                ForceState::markNonReplaceable(rhsp);

                m_stmtp->addNextHere(new AstAssign{flp, valp, rhsp});
            }
            break;
        }
        default:
            nodep->v3error("Unsupported: Signals used via read-write reference cannot be forced");
            break;
        }
    }
    void visit(AstNode* nodep) override { iterateChildren(nodep); }

public:
    // CONSTRUCTOR
    explicit ForceReplaceVisitor(AstNetlist* nodep, const ForceState& state)
        : m_state{state} {
        iterateChildren(nodep);
    }
};
//######################################################################
//

void V3Force::forceAll(AstNetlist* nodep) {
    UINFO(2, __FUNCTION__ << ":");
    if (!v3Global.hasForceableSignals()) return;
    {
        ForceState state;
        { ForceConvertVisitor{nodep, state}; }
        { ForceReplaceVisitor{nodep, state}; }
        V3Global::dumpCheckGlobalTree("force", 0, dumpTreeEitherLevel() >= 3);
    }
}
