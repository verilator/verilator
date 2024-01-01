// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Covert forceable signals, process force/release
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
//  V3Force's Transformations:
//
//  For each forceable net with name "<name>":
//      add 3 extra signals:
//          - <name>__VforceRd: a net with same type as signal
//          - <name>__VforceEn: a var with same type as signal, which is the bitwise force enable
//          - <name>__VforceVl: a var with same type as signal, which is the forced value
//      add an initial statement:
//          initial <name>__VforceEn = 0;
//      add a continuous assignment:
//          assign <name>__VforceRd = <name>__VforceEn ? <name>__VforceVl : <name>;
//      replace all READ references to <name> with a read reference to <name>_VforceRd
//
//  Replace each AstAssignForce with 3 assignments:
//      - <lhs>__VforceEn = 1
//      - <lhs>__VforceVl = <rhs>
//      - <lhs>__VforceRd = <rhs>
//
//  Replace each AstRelease with 1 or 2 assignments:
//      - <lhs>__VforceEn = 0
//      - <lhs>__VforceRd = <lhs> // iff lhs is a net
//
//*************************************************************************

#include "V3PchAstNoMT.h"  // VL_MT_DISABLED_CODE_UNIT

#include "V3Force.h"

#include "V3AstUserAllocator.h"

VL_DEFINE_DEBUG_FUNCTIONS;

//######################################################################
// Convert force/release statements and signals marked 'forceable'

class ForceConvertVisitor final : public VNVisitor {
    // TYPES
    struct ForceComponentsVar {
        AstVar* const m_rdVarp;  // New variable to replace read references with
        AstVar* const m_valVarp;  // Forced value
        AstVar* const m_enVarp;  // Force enabled signal
        explicit ForceComponentsVar(AstVar* varp)
            : m_rdVarp{new AstVar{varp->fileline(), VVarType::WIRE, varp->name() + "__VforceRd",
                                  varp->dtypep()}}
            , m_valVarp{new AstVar{varp->fileline(), VVarType::VAR, varp->name() + "__VforceVal",
                                   varp->dtypep()}}
            , m_enVarp{new AstVar{varp->fileline(), VVarType::VAR, varp->name() + "__VforceEn",
                                  (isRangedDType(varp) ? varp->dtypep() : varp->findBitDType())}} {
            m_rdVarp->addNext(m_enVarp);
            m_rdVarp->addNext(m_valVarp);
            varp->addNextHere(m_rdVarp);

            if (varp->isPrimaryIO()) {
                varp->v3warn(
                    E_UNSUPPORTED,
                    "Unsupported: Force/Release on primary input/output net "
                        << varp->prettyNameQ() << "\n"
                        << varp->warnMore()
                        << "... Suggest assign it to/from a temporary net and force/release that");
            }
        }
    };

    struct ForceComponentsVarScope {
        AstVarScope* const m_rdVscp;  // New variable to replace read references with
        AstVarScope* const m_enVscp;  // Force enabled signal
        AstVarScope* const m_valVscp;  // Forced value
        explicit ForceComponentsVarScope(AstVarScope* vscp, ForceComponentsVar& fcv)
            : m_rdVscp{new AstVarScope{vscp->fileline(), vscp->scopep(), fcv.m_rdVarp}}
            , m_enVscp{new AstVarScope{vscp->fileline(), vscp->scopep(), fcv.m_enVarp}}
            , m_valVscp{new AstVarScope{vscp->fileline(), vscp->scopep(), fcv.m_valVarp}} {
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
                    new AstSenTree{flp, new AstSenItem{flp, AstSenItem::Initial{}}}};
                activep->sensesStorep(activep->sensesp());
                activep->addStmtsp(new AstInitial{flp, assignp});
                vscp->scopep()->addBlocksp(activep);
            }

            {  // Add the combinational override
                AstVarRef* const lhsp = new AstVarRef{flp, m_rdVscp, VAccess::WRITE};
                AstVarRef* const origp = new AstVarRef{flp, vscp, VAccess::READ};
                origp->user2(1);  // Don't replace this read ref with the read signal
                AstNodeExpr* rhsp;
                if (isRangedDType(vscp)) {
                    rhsp = new AstOr{
                        flp,
                        new AstAnd{flp, new AstVarRef{flp, m_enVscp, VAccess::READ},
                                   new AstVarRef{flp, m_valVscp, VAccess::READ}},
                        new AstAnd{flp,
                                   new AstNot{flp, new AstVarRef{flp, m_enVscp, VAccess::READ}},
                                   origp}};
                } else {
                    rhsp = new AstCond{flp, new AstVarRef{flp, m_enVscp, VAccess::READ},
                                       new AstVarRef{flp, m_valVscp, VAccess::READ}, origp};
                }

                AstActive* const activep
                    = new AstActive{flp, "force-comb",
                                    new AstSenTree{flp, new AstSenItem{flp, AstSenItem::Combo{}}}};
                activep->sensesStorep(activep->sensesp());
                activep->addStmtsp(new AstAssignW{flp, lhsp, rhsp});
                vscp->scopep()->addBlocksp(activep);
            }
        }
    };

    // NODE STATE
    //  AstVar::user1p        -> ForceComponentsVar* instance (via m_forceComponentsVar)
    //  AstVarScope::user1p   -> ForceComponentsVarScope* instance (via m_forceComponentsVarScope)
    //  AstVarRef::user2      -> Flag indicating not to replace reference
    const VNUser1InUse m_user1InUse;
    const VNUser2InUse m_user2InUse;
    AstUser1Allocator<AstVar, ForceComponentsVar> m_forceComponentsVar;
    AstUser1Allocator<AstVarScope, ForceComponentsVarScope> m_forceComponentsVarScope;

    // METHODS
    static bool isRangedDType(AstNode* nodep) {
        // If ranged we need a multibit enable to support bit-by-bit part-select forces,
        // otherwise forcing a real or other opaque dtype and need a single bit enable.
        const AstBasicDType* const basicp = nodep->dtypep()->skipRefp()->basicp();
        return basicp && basicp->isRanged();
    }
    const ForceComponentsVarScope& getForceComponents(AstVarScope* vscp) {
        AstVar* const varp = vscp->varp();
        return m_forceComponentsVarScope(vscp, vscp, m_forceComponentsVar(varp, varp));
    }

    // Replace each AstNodeVarRef in the given 'nodep' that writes a variable by transforming the
    // referenced AstVarScope with the given function.
    void transformWritenVarScopes(AstNode* nodep, std::function<AstVarScope*(AstVarScope*)> f) {
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

    // VISIT methods
    void visit(AstNode* nodep) override { iterateChildren(nodep); }

    void visit(AstAssignForce* nodep) override {
        // The AstAssignForce node will be removed for sure
        VNRelinker relinker;
        nodep->unlinkFrBack(&relinker);
        pushDeletep(nodep);

        FileLine* const flp = nodep->fileline();
        AstNodeExpr* const lhsp = nodep->lhsp();  // The LValue we are forcing
        AstNodeExpr* const rhsp = nodep->rhsp();  // The value we are forcing it to

        // Set corresponding enable signals to ones
        V3Number ones{lhsp, isRangedDType(lhsp) ? lhsp->width() : 1};
        ones.setAllBits1();
        AstAssign* const setEnp
            = new AstAssign{flp, lhsp->cloneTreePure(false), new AstConst{rhsp->fileline(), ones}};
        transformWritenVarScopes(setEnp->lhsp(), [this](AstVarScope* vscp) {
            return getForceComponents(vscp).m_enVscp;
        });
        // Set corresponding value signals to the forced value
        AstAssign* const setValp
            = new AstAssign{flp, lhsp->cloneTreePure(false), rhsp->cloneTreePure(false)};
        transformWritenVarScopes(setValp->lhsp(), [this](AstVarScope* vscp) {
            return getForceComponents(vscp).m_valVscp;
        });
        // Set corresponding read signal directly as well, in case something in the same process
        // reads it later
        AstAssign* const setRdp = new AstAssign{flp, lhsp->unlinkFrBack(), rhsp->unlinkFrBack()};
        transformWritenVarScopes(setRdp->lhsp(), [this](AstVarScope* vscp) {
            return getForceComponents(vscp).m_rdVscp;
        });

        setEnp->addNext(setValp);
        setEnp->addNext(setRdp);
        relinker.relink(setEnp);
    }

    void visit(AstRelease* nodep) override {
        // The AstRelease node will be removed for sure
        VNRelinker relinker;
        nodep->unlinkFrBack(&relinker);
        pushDeletep(nodep);

        FileLine* const flp = nodep->fileline();
        AstNodeExpr* const lhsp = nodep->lhsp();  // The LValue we are releasing

        // Set corresponding enable signals to zero
        V3Number zero{lhsp, isRangedDType(lhsp) ? lhsp->width() : 1};
        zero.setAllBits0();
        AstAssign* const resetEnp
            = new AstAssign{flp, lhsp->cloneTreePure(false), new AstConst{lhsp->fileline(), zero}};
        transformWritenVarScopes(resetEnp->lhsp(), [this](AstVarScope* vscp) {
            return getForceComponents(vscp).m_enVscp;
        });
        // IEEE 1800-2017 10.6.2: If this is a net, and not a variable, then reset the read
        // signal directly as well, in case something in the same process reads it later. Also, if
        // it is a variable, and not a net, set the original signal to the forced value, as it
        // needs to retain the forced value until the next procedural update, which might happen on
        // a later eval. Luckily we can do all this in a single assignment.
        FileLine* const fl_nowarn = new FileLine{flp};
        fl_nowarn->warnOff(V3ErrorCode::BLKANDNBLK, true);
        AstAssign* const resetRdp
            = new AstAssign{fl_nowarn, lhsp->cloneTreePure(false), lhsp->unlinkFrBack()};
        // Replace write refs on the LHS
        resetRdp->lhsp()->foreach([this](AstNodeVarRef* refp) {
            if (refp->access() != VAccess::WRITE) return;
            AstVarScope* const vscp = refp->varScopep();
            AstVarScope* const newVscp
                = vscp->varp()->isContinuously() ? getForceComponents(vscp).m_rdVscp : vscp;
            // Disable BLKANDNBLK for this reference
            FileLine* const flp = new FileLine{refp->fileline()};
            flp->warnOff(V3ErrorCode::BLKANDNBLK, true);
            AstVarRef* const newpRefp = new AstVarRef{flp, newVscp, VAccess::WRITE};
            refp->replaceWith(newpRefp);
            VL_DO_DANGLING(refp->deleteTree(), refp);
        });
        // Replace write refs on RHS
        resetRdp->rhsp()->foreach([this](AstNodeVarRef* refp) {
            if (refp->access() != VAccess::WRITE) return;
            AstVarScope* const vscp = refp->varScopep();
            FileLine* const flp = new FileLine{refp->fileline()};
            AstVarRef* const newpRefp = new AstVarRef{refp->fileline(), vscp, VAccess::READ};
            newpRefp->user2(1);  // Don't replace this read ref with the read signal
            if (vscp->varp()->isContinuously()) {
                refp->replaceWith(newpRefp);
            } else if (isRangedDType(vscp)) {
                refp->replaceWith(new AstOr{
                    flp,
                    new AstAnd{
                        flp, new AstVarRef{flp, getForceComponents(vscp).m_enVscp, VAccess::READ},
                        new AstVarRef{flp, getForceComponents(vscp).m_valVscp, VAccess::READ}},
                    new AstAnd{
                        flp,
                        new AstNot{flp, new AstVarRef{flp, getForceComponents(vscp).m_enVscp,
                                                      VAccess::READ}},
                        newpRefp}});
            } else {
                refp->replaceWith(new AstCond{
                    flp, new AstVarRef{flp, getForceComponents(vscp).m_enVscp, VAccess::READ},
                    new AstVarRef{flp, getForceComponents(vscp).m_valVscp, VAccess::READ},
                    newpRefp});
            }
            VL_DO_DANGLING(refp->deleteTree(), refp);
        });

        resetRdp->addNext(resetEnp);
        relinker.relink(resetRdp);
    }

    void visit(AstVarScope* nodep) override {
        // If this signal is marked externally forceable, create the public force signals
        if (nodep->varp()->isForceable()) {
            const ForceComponentsVarScope& fc = getForceComponents(nodep);
            fc.m_enVscp->varp()->sigUserRWPublic(true);
            fc.m_valVscp->varp()->sigUserRWPublic(true);
        }
    }

    // CONSTRUCTOR
    explicit ForceConvertVisitor(AstNetlist* nodep) {
        // Transform all force and release statements
        iterateAndNextNull(nodep->modulesp());

        // Replace references to forced signals
        nodep->modulesp()->foreachAndNext([this](AstVarRef* nodep) {
            if (ForceComponentsVarScope* const fcp
                = m_forceComponentsVarScope.tryGet(nodep->varScopep())) {
                switch (nodep->access()) {
                case VAccess::READ:
                    // Read references replaced to read the new, possibly forced signal
                    if (!nodep->user2()) {
                        nodep->varp(fcp->m_rdVscp->varp());
                        nodep->varScopep(fcp->m_rdVscp);
                    }
                    break;
                case VAccess::WRITE:
                    // Write references use the original signal
                    break;
                default:
                    nodep->v3error(
                        "Unsupported: Signals used via read-write reference cannot be forced");
                    break;
                }
            }
        });
    }

public:
    static void apply(AstNetlist* nodep) { ForceConvertVisitor{nodep}; }
};

//######################################################################
//

void V3Force::forceAll(AstNetlist* nodep) {
    UINFO(2, __FUNCTION__ << ": " << endl);
    if (!v3Global.hasForceableSignals()) return;
    ForceConvertVisitor::apply(nodep);
    V3Global::dumpCheckGlobalTree("force", 0, dumpTreeLevel() >= 3);
}
