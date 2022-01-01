// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Make lookup forces
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2022 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************
// FORCE TRANSFORMATIONS:
//   Step 1 (ForceVisitor):
//      For forced nets, make:
//         __forceon - enable bitmask of what bits are forced
//         __forcein - value being forced
//         __preforce - value before force is applied
//
//      Force sets the appropriate __forceon bits indicating a force is in
//      effect using the value in __forcein.  Release clears the
//      appropriate __forceon bits.
//
//      IEEE says that procedural assignments "hold" the forced value even
//      after a release, so add an assignment to the original __preforce too.
//
//      Tristates can't be forced, that would need a __forceen and makes a
//      large mess, so just error out.
//
//   Step 2 (ForceReplaceVisitor): (If any forces made)
//
//      Replace any VarRef's to a forced signal to instead go to the
//      reconsiled signal.
//
//*************************************************************************

#include "config_build.h"
#include "verilatedos.h"

#include "V3Global.h"
#include "V3Force.h"
#include "V3Simulate.h"
#include "V3Stats.h"
#include "V3Ast.h"

#include <cmath>
#include <vector>

//######################################################################
// Force shared state

class ForceBaseVisitor VL_NOT_FINAL : public AstNVisitor {
    // TYPES
public:
    // Enum value must correspond to which user#p is used
    enum class FVar : uint8_t { FORCEON = 2, FORCEIN = 3, PREFORCE = 4 };

private:
    // NODE STATE
    //   Ast*::user1            -> bool - processed
    //   AstVar::user1          -> bool - created here
    //   AstVarScope::user1     -> bool - created here
    //   AstVar::user2p         -> AstVar* pointer to __forceon
    //   AstVarScope::user2p    -> AstVarScope* pointer to __forceon
    //   AstVar::user3p         -> AstVar* pointer to __forcein
    //   AstVarScope::user3p    -> AstVarScope* pointer to __forcein
    //   AstVar::user4p         -> AstVar* pointer to __preforce
    //   AstVarScope::user4p    -> AstVarScope* pointer to __preforce
    // Uses are in ForceVisitor

public:
    VL_DEBUG_FUNC;  // Declare debug()

    static string fvarName(FVar fvar) {
        switch (fvar) {
        case FVar::FORCEON: return "__forceon";
        case FVar::FORCEIN: return "__forcein";
        case FVar::PREFORCE: return "__preforce";
        }
        v3fatalSrc("bad case");
        return "";
    }
    static AstVar* getForceVarNull(const AstVar* const nodep, FVar fvar) {
        // E.g. trying to make a __perforce__FOO would be bad
        UASSERT_OBJ(!nodep->user1(), nodep, "lookup on var that Force made itself");
        return VN_AS(nodep->usernp(static_cast<int>(fvar)), Var);
    }
    static AstVar* getForceVar(AstVar* const nodep, FVar fvar) {
        AstVar* const foundp = getForceVarNull(nodep, fvar);
        if (foundp) return foundp;
        if (nodep->isPrimaryIO()) {
            nodep->v3warn(
                E_UNSUPPORTED,
                "Unsupported: Force/Release on primary input/output net "
                    << nodep->prettyNameQ() << "\n"
                    << nodep->warnMore()
                    << "... Suggest assign it to/from a temporary net and force/release that");
        }
        auto* const newp = new AstVar{nodep->fileline(), AstVarType::MODULETEMP,
                                      nodep->name() + fvarName(fvar), nodep};
        newp->user1(true);
        UINFO(9, "getForceVar for " << nodep << endl);
        UINFO(9, "getForceVar new " << newp << endl);
        nodep->addNextHere(newp);
        nodep->usernp(static_cast<int>(fvar), newp);
        return newp;
    }
    static AstVarScope* getForceVscNull(const AstVarScope* const nodep, FVar fvar) {
        // E.g. trying to make a __perforce__FOO would be bad
        UASSERT_OBJ(!nodep->user1(), nodep, "lookup on varscope that Force made itself");
        return VN_AS(nodep->usernp(static_cast<int>(fvar)), VarScope);
    }
    static AstVarScope* getForceVsc(AstVarScope* const nodep, FVar fvar) {
        AstVarScope* const foundp = getForceVscNull(nodep, fvar);
        if (foundp) return foundp;
        FileLine* const fl_nowarn = new FileLine{nodep->fileline()};
        fl_nowarn->warnOff(V3ErrorCode::BLKANDNBLK, true);
        auto* const newp
            = new AstVarScope{fl_nowarn, nodep->scopep(), getForceVar(nodep->varp(), fvar)};
        newp->user1(true);
        UINFO(9, "getForceVsc for " << nodep << endl);
        UINFO(9, "getForceVsc new " << newp << endl);
        nodep->addNextHere(newp);
        nodep->usernp(static_cast<int>(fvar), newp);
        return newp;
    }
    static AstVarRef* makeVarRef(AstNodeVarRef* nodep, FVar fvar, VAccess access) {
        return new AstVarRef{nodep->fileline(), getForceVsc(nodep->varScopep(), fvar), access};
    }
    static AstNode* makeForcingEquation(AstNodeVarRef* nodep) {
        // Forcing:  out = ((__forceon & __forcein) | (~__forceon & __preforce))
        UINFO(9, "makeForcingEquation for " << nodep << endl);
        FileLine* const fl = nodep->fileline();
        AstNode* const orp = new AstOr{
            fl,
            new AstAnd{fl, makeVarRef(nodep, FVar::FORCEON, VAccess::READ),
                       makeVarRef(nodep, FVar::FORCEIN, VAccess::READ)},
            new AstAnd{fl, new AstNot{fl, makeVarRef(nodep, FVar::FORCEON, VAccess::READ)},
                       makeVarRef(nodep, FVar::PREFORCE, VAccess::READ)}};
        return orp;
    }
};

//######################################################################
// Recurse left-hand-side variables to do replaces underneath a force or release

class ForceLhsVisitor final : public ForceBaseVisitor {
private:
    // STATE
    FVar const m_fvar;  // Which variable to replace with
    AstNodeVarRef* m_releaseVarRefp = nullptr;  // Left hand side variable under release

    virtual void visit(AstNodeVarRef* nodep) override {
        if (nodep->user1()) return;
        if (nodep->access().isWriteOrRW()) {
            if (m_releaseVarRefp) {
                nodep->v3error("Multiple variables forced in single statement: "
                               << m_releaseVarRefp->prettyNameQ() << ", "
                               << nodep->varScopep()->prettyNameQ());
                return;
            }
            m_releaseVarRefp = nodep;
            AstNode* const newp = makeVarRef(nodep, m_fvar, VAccess::WRITE);
            newp->user1(true);
            nodep->replaceWith(newp);
            pushDeletep(nodep);
        }
    }
    virtual void visit(AstNode* nodep) override { iterateChildren(nodep); }

public:
    // CONSTRUCTORS
    explicit ForceLhsVisitor(AstNode* nodep, FVar fvar)
        : m_fvar(fvar) {
        iterate(nodep);
    }
    virtual ~ForceLhsVisitor() override = default;
    // METHODS
    AstNodeVarRef* releaseVarRefp() const { return m_releaseVarRefp; }
};

//######################################################################
// Force class functions

class ForceVisitor final : public ForceBaseVisitor {
private:
    // NODE STATE
    // See ForceBaseVisitor
    const AstUser1InUse m_inuser1;
    const AstUser2InUse m_inuser2;
    const AstUser3InUse m_inuser3;
    const AstUser4InUse m_inuser4;

    // STATE
    bool m_anyForce = false;  // Any force, need reconciliation step
    VDouble0 m_statForces;  // stat tracking

    std::deque<AstAssignForce*> m_forces;  // Pointer to found forces
    std::deque<AstAssignRelease*> m_releases;  // Pointer to found releases

    virtual void visit(AstAssignForce* nodep) override { m_forces.push_back(nodep); }
    void visitEarlierForce(AstAssignForce* nodep) {
        if (nodep->user1SetOnce()) return;
        if (debug() >= 9) nodep->dumpTree(cout, "-force-i- ");
        ++m_statForces;
        m_anyForce = true;
        // For force/release, duplicate assignment to make
        //      AssignForce __forceon = '1
        //      AssignForce __forcein = {value}
        // and clone LHS's node tree to handle appropriate extractions
        {  // __forceon = '1
            AstNodeAssign* const newp = nodep->cloneTree(false);
            pushDeletep(newp->rhsp()->unlinkFrBack());
            V3Number num{nodep, nodep->width()};
            num.setAllBits1();
            newp->rhsp(new AstConst{nodep->fileline(), num});
            { ForceLhsVisitor{newp->lhsp(), FVar::FORCEON}; }
            newp->user1(true);  // Don't process it again
            nodep->addNextHere(newp);
            if (debug() >= 9) newp->dumpTree(cout, "-force-fo- ");
        }
        {  // Edit to create assignment to have VarRef that refers to __forceon
            { ForceLhsVisitor{nodep->lhsp(), FVar::FORCEIN}; }
            nodep->user1(true);  // Don't process it again
            if (debug() >= 9) nodep->dumpTree(cout, "-force-fi- ");
        }
    }
    virtual void visit(AstAssignRelease* nodep) override { m_releases.push_back(nodep); }
    void visitEarlierRelease(AstAssignRelease* nodep) {
        if (nodep->user1SetOnce()) return;
        if (debug() >= 9) nodep->dumpTree(cout, "-release-i- ");
        // RHS is not relevant, so no iterate
        // For release, edit assignment to make
        //   AssignRelease __forceon = `0
        //   we already have 0's on RHS, were made when AstNode created
        // Create assignment to have VarRef that refers to __forceon
        ForceLhsVisitor fvisitor{nodep->lhsp(), FVar::FORCEON};
        // releaseVarRefp might be deleted when ForceLhsVisitor destructs, so
        // keep ForceLhsVisitor in scope for now
        AstNodeVarRef* const releaseVarRefp = fvisitor.releaseVarRefp();
        UASSERT_OBJ(releaseVarRefp, nodep, "No LHS variable found under release");
        if (!getForceVscNull(releaseVarRefp->varScopep(), FVar::FORCEIN)) {
            UINFO(9, "Deleting release of variable that's never forced: " << nodep << endl);
            VL_DO_DANGLING(pushDeletep(nodep->unlinkFrBack()), nodep);
            return;
        }
        if (!releaseVarRefp->varp()->isContinuously()) {
            // Create assignment __out == _forceen so when release happens value sticks
            // See IEEE - a strange historical language artifact
            UINFO(9, "force var is procedural " << releaseVarRefp->varScopep() << endl);
            FileLine* const fl_nowarn = new FileLine{nodep->fileline()};
            fl_nowarn->warnOff(V3ErrorCode::BLKANDNBLK, true);
            AstNodeAssign* const newp = new AstAssignRelease{
                fl_nowarn, makeVarRef(releaseVarRefp, FVar::PREFORCE, VAccess::WRITE),
                makeForcingEquation(releaseVarRefp)};
            newp->user1(true);  // Don't process it again
            nodep->addHereThisAsNext(newp);  // Must go before change forceon
            if (debug() >= 9) newp->dumpTree(cout, "-release-rp- ");
        }
        if (debug() >= 9) nodep->dumpTree(cout, "-release-ro- ");
    }

    virtual void visit(AstNode* nodep) override { iterateChildren(nodep); }

public:
    // CONSTRUCTORS
    explicit ForceVisitor(AstNetlist* nodep) {
        iterate(nodep);
        // Now that we know procedural markers in user5, do forces
        for (auto* const nodep : m_forces) visitEarlierForce(nodep);
        m_forces.clear();  // As dangling pointers now
        // Do releases after all forces are processed, so we can just
        // ignore any release with no corresponding force
        for (auto* const nodep : m_releases) visitEarlierRelease(nodep);
        m_releases.clear();  // As dangling pointers now
    }
    virtual ~ForceVisitor() override {  //
        V3Stats::addStat("Tristate, Forces", m_statForces);
    }
    // METHODS
    bool anyForce() const { return m_anyForce; }
};

//######################################################################
// Force class functions

class ForceReplace final : public ForceBaseVisitor {
    // This extra complete-netlist visit could be avoided by recording all
    // AstVarRefs to every AstVar, but that's a lot of data structure
    // building, faster to read-only iterate.
    // As we only care about VarRef's we use direct recusion rather than a visitor

private:
    void visitVarRef(AstNodeVarRef* nodep) {
        if (nodep->varScopep()->user2p()) {
            if (nodep->access().isRW()) {
                nodep->v3warn(E_UNSUPPORTED,
                              "Unsupported: forced variable used in read-modify-write context");
            } else if (nodep->access().isWriteOrRW()) {
                UINFO(9, "  changeRecurse-WR-replace " << nodep << endl);
                AstNode* const newp = makeVarRef(nodep, FVar::PREFORCE, VAccess::WRITE);
                newp->user1(true);
                nodep->replaceWith(newp);
                pushDeletep(nodep);
                return;
            } else if (nodep->access().isReadOrRW()) {
                // We build forcing equation on each usage rather than making
                // a variable otherwise we wouldn't know where between a statement
                // that sets a preforce and uses a forced to insert the proposed
                // assignment
                UINFO(9, "  changeRecurse-RD-replace " << nodep << endl);
                AstNode* const newp = makeForcingEquation(nodep);
                newp->user1(true);
                nodep->replaceWith(newp);
                pushDeletep(nodep);
                return;
            }
        }
    }

    void changeRecurse(AstNode* nodep) {
        // Recurse and replace any VarRef WRITEs to refer to the force equation
        if (VL_LIKELY(!nodep->user1())) {  // Else processed already
            if (auto* const varrefp = VN_CAST(nodep, NodeVarRef)) {
                visitVarRef(varrefp);
                return;  // Might have been edited -- and has no children so ok to exit
            }
        }
        nodep->prefetch();
        if (nodep->op1p()) changeRecurse(nodep->op1p());
        if (nodep->op2p()) changeRecurse(nodep->op2p());
        if (nodep->op3p()) changeRecurse(nodep->op3p());
        if (nodep->op4p()) changeRecurse(nodep->op4p());
        if (nodep->nextp()) changeRecurse(nodep->nextp());
    }

    virtual void visit(AstNode* nodep) override { v3error("Unused"); }  // LCOV_EXCL_LINE

public:
    // CONSTRUCTORS
    explicit ForceReplace(AstNetlist* nodep) { changeRecurse(nodep); }
    virtual ~ForceReplace() override = default;
};

//######################################################################
// Force class functions

void V3Force::forceAll(AstNetlist* nodep) {
    UINFO(2, __FUNCTION__ << ": " << endl);
    {  // Destruct before final check
        ForceVisitor visitor{nodep};
        if (visitor.anyForce()) {
            V3Global::dumpCheckGlobalTree("force-mid", 0,
                                          v3Global.opt.dumpTreeLevel(__FILE__) >= 3);
            ForceReplace{nodep};
        }
    }
    V3Global::dumpCheckGlobalTree("force", 0, v3Global.opt.dumpTreeLevel(__FILE__) >= 3);
}
