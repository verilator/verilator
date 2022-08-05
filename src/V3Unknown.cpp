// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Add Unknown assigns
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
// V3Unknown's Transformations:
//
// Each module:
//      TBD: Eliminate tristates by adding __in, __inen, __en wires in parallel
//          Need __en in changed list if a signal is on the LHS of a assign
//      Constants:
//          RHS, Replace 5'bx_1_x with a module global we init to a random value
//              CONST(5'bx_1_x) -> VARREF(_{numberedtemp})
//                              -> VAR(_{numberedtemp})
//                              -> INITIAL(VARREF(_{numberedtemp}),
//                                         OR(5'bx_1_x,AND(random,5'b0_1_x))
//              OPTIMIZE: Must not collapse this initial back into the equation.
//
//*************************************************************************

#include "config_build.h"
#include "verilatedos.h"

#include "V3Unknown.h"

#include "V3Ast.h"
#include "V3Const.h"
#include "V3Global.h"
#include "V3Stats.h"
#include "V3UniqueNames.h"

#include <algorithm>

//######################################################################

class UnknownVisitor final : public VNVisitor {
private:
    // NODE STATE
    // Cleared on Netlist
    //  AstSel::user()          -> bool.  Set true if already processed
    //  AstArraySel::user()     -> bool.  Set true if already processed
    //  AstNode::user2p()       -> AstIf* Inserted if assignment for conditional
    const VNUser1InUse m_inuser1;
    const VNUser2InUse m_inuser2;

    // STATE
    AstNodeModule* m_modp = nullptr;  // Current module
    AstAssignW* m_assignwp = nullptr;  // Current assignment
    AstAssignDly* m_assigndlyp = nullptr;  // Current assignment
    bool m_constXCvt = false;  // Convert X's
    bool m_allowXUnique = true;  // Allow unique assignments
    VDouble0 m_statUnkVars;  // Statistic tracking
    V3UniqueNames m_lvboundNames;  // For generating unique temporary variable names
    V3UniqueNames m_xrandNames;  // For generating unique temporary variable names

    // METHODS
    VL_DEBUG_FUNC;  // Declare debug()

    void replaceBoundLvalue(AstNode* nodep, AstNode* condp) {
        // Spec says a out-of-range LHS SEL results in a NOP.
        // This is a PITA.  We could:
        //  1. IF(...) around an ASSIGN,
        //     but that would break a "foo[TOO_BIG]=$fopen(...)".
        //  2. Hack to extend the size of the output structure
        //     by one bit, and write to that temporary, but never read it.
        //     That makes there be two widths() and is likely a bug farm.
        //  3. Make a special SEL to choose between the real lvalue
        //     and a temporary NOP register.
        //  4. Assign to a temp, then IF that assignment.
        //     This is suspected to be nicest to later optimizations.
        // 4 seems best but breaks later optimizations.  3 was tried,
        // but makes a mess in the emitter as lvalue switching is needed.  So 4.
        // SEL(...) -> temp
        //             if (COND(LTE(bit<=maxlsb))) ASSIGN(SEL(...)),temp)
        if (m_assignwp) {
            // Wire assigns must become always statements to deal with insertion
            // of multiple statements.  Perhaps someday make all wassigns into always's?
            UINFO(5, "     IM_WireRep  " << m_assignwp << endl);
            m_assignwp->convertToAlways();
            VL_DO_CLEAR(pushDeletep(m_assignwp), m_assignwp = nullptr);
        }
        const bool needDly = (m_assigndlyp != nullptr);
        if (m_assigndlyp) {
            // Delayed assignments become normal assignments,
            // then the temp created becomes the delayed assignment
            AstNode* const newp = new AstAssign(m_assigndlyp->fileline(),
                                                m_assigndlyp->lhsp()->unlinkFrBackWithNext(),
                                                m_assigndlyp->rhsp()->unlinkFrBackWithNext());
            m_assigndlyp->replaceWith(newp);
            VL_DO_CLEAR(pushDeletep(m_assigndlyp), m_assigndlyp = nullptr);
        }
        AstNode* prep = nodep;

        // Scan back to put the condlvalue above all selects (IE top of the lvalue)
        while (VN_IS(prep->backp(), NodeSel) || VN_IS(prep->backp(), Sel)) {
            prep = prep->backp();
        }
        FileLine* const fl = nodep->fileline();
        VL_DANGLING(nodep);  // Zap it so we don't use it by mistake - use prep

        // Already exists; rather than IF(a,... IF(b... optimize to IF(a&&b,
        // Saves us teaching V3Const how to optimize, and it won't be needed again.
        if (const AstIf* const ifp = VN_AS(prep->user2p(), If)) {
            UASSERT_OBJ(!needDly, prep, "Should have already converted to non-delay");
            VNRelinker replaceHandle;
            AstNode* const earliercondp = ifp->condp()->unlinkFrBack(&replaceHandle);
            AstNode* const newp = new AstLogAnd(condp->fileline(), condp, earliercondp);
            UINFO(4, "Edit BOUNDLVALUE " << newp << endl);
            replaceHandle.relink(newp);
        } else {
            AstVar* const varp
                = new AstVar(fl, VVarType::MODULETEMP, m_lvboundNames.get(prep), prep->dtypep());
            m_modp->addStmtp(varp);
            AstNode* const abovep = prep->backp();  // Grab above point before we replace 'prep'
            prep->replaceWith(new AstVarRef(fl, varp, VAccess::WRITE));
            AstIf* const newp = new AstIf(
                fl, condp,
                (needDly ? static_cast<AstNode*>(
                     new AstAssignDly(fl, prep, new AstVarRef(fl, varp, VAccess::READ)))
                         : static_cast<AstNode*>(
                             new AstAssign(fl, prep, new AstVarRef(fl, varp, VAccess::READ)))));
            newp->branchPred(VBranchPred::BP_LIKELY);
            newp->isBoundsCheck(true);
            if (debug() >= 9) newp->dumpTree(cout, "     _new: ");
            abovep->addNextStmt(newp, abovep);
            prep->user2p(newp);  // Save so we may LogAnd it next time
        }
    }

    // VISITORS
    virtual void visit(AstNodeModule* nodep) override {
        UINFO(4, " MOD   " << nodep << endl);
        VL_RESTORER(m_modp);
        VL_RESTORER(m_constXCvt);
        VL_RESTORER(m_allowXUnique);
        {
            m_modp = nodep;
            m_constXCvt = true;
            // Class X randomization causes Vxrand in strange places, so disable
            if (VN_IS(nodep, Class)) m_allowXUnique = false;
            m_lvboundNames.reset();
            m_xrandNames.reset();
            iterateChildren(nodep);
        }
    }
    virtual void visit(AstAssignDly* nodep) override {
        VL_RESTORER(m_assigndlyp);
        {
            m_assigndlyp = nodep;
            VL_DO_DANGLING(iterateChildren(nodep), nodep);  // May delete nodep.
        }
    }
    virtual void visit(AstAssignW* nodep) override {
        VL_RESTORER(m_assignwp);
        {
            m_assignwp = nodep;
            VL_DO_DANGLING(iterateChildren(nodep), nodep);  // May delete nodep.
        }
    }
    virtual void visit(AstCaseItem* nodep) override {
        VL_RESTORER(m_constXCvt);
        {
            m_constXCvt = false;  // Avoid losing the X's in casex
            iterateAndNextNull(nodep->condsp());
            m_constXCvt = true;
            iterateAndNextNull(nodep->bodysp());
        }
    }
    virtual void visit(AstNodeDType* nodep) override {
        VL_RESTORER(m_constXCvt);
        {
            m_constXCvt = false;  // Avoid losing the X's in casex
            iterateChildren(nodep);
        }
    }
    void visitEqNeqCase(AstNodeBiop* nodep) {
        UINFO(4, " N/EQCASE->EQ " << nodep << endl);
        V3Const::constifyEdit(nodep->lhsp());  // lhsp may change
        V3Const::constifyEdit(nodep->rhsp());  // rhsp may change
        if (VN_IS(nodep->lhsp(), Const) && VN_IS(nodep->rhsp(), Const)) {
            // Both sides are constant, node can be constant
            VL_DO_DANGLING(V3Const::constifyEdit(nodep), nodep);
            return;
        } else {
            AstNode* const lhsp = nodep->lhsp()->unlinkFrBack();
            AstNode* const rhsp = nodep->rhsp()->unlinkFrBack();
            AstNode* newp;
            // If we got ==1'bx it can never be true (but 1'bx==1'bx can be!)
            if (((VN_IS(lhsp, Const) && VN_AS(lhsp, Const)->num().isFourState())
                 || (VN_IS(rhsp, Const) && VN_AS(rhsp, Const)->num().isFourState()))) {
                newp = new AstConst(nodep->fileline(), AstConst::WidthedValue(), 1,
                                    (VN_IS(nodep, EqCase) ? 0 : 1));
                VL_DO_DANGLING(lhsp->deleteTree(), lhsp);
                VL_DO_DANGLING(rhsp->deleteTree(), rhsp);
            } else {
                if (VN_IS(nodep, EqCase)) {
                    newp = new AstEq(nodep->fileline(), lhsp, rhsp);
                } else {
                    newp = new AstNeq(nodep->fileline(), lhsp, rhsp);
                }
            }
            nodep->replaceWith(newp);
            VL_DO_DANGLING(nodep->deleteTree(), nodep);
            // Iterate tree now that we may have gotten rid of Xs
            iterateChildren(newp);
        }
    }
    void visitEqNeqWild(AstNodeBiop* nodep) {
        UINFO(4, " N/EQWILD->EQ " << nodep << endl);
        V3Const::constifyEdit(nodep->lhsp());  // lhsp may change
        V3Const::constifyEdit(nodep->rhsp());  // rhsp may change
        if (VN_IS(nodep->lhsp(), Const) && VN_IS(nodep->rhsp(), Const)) {
            // Both sides are constant, node can be constant
            VL_DO_DANGLING(V3Const::constifyEdit(nodep), nodep);
            return;
        } else {
            AstNode* const lhsp = nodep->lhsp()->unlinkFrBack();
            AstNode* const rhsp = nodep->rhsp()->unlinkFrBack();
            AstNode* newp;
            if (!VN_IS(rhsp, Const)) {
                nodep->v3warn(E_UNSUPPORTED, "Unsupported: RHS of ==? or !=? must be "
                                             "constant to be synthesizable");  // Says spec.
                // Replace with anything that won't cause more errors
                newp = new AstEq(nodep->fileline(), lhsp, rhsp);
            } else {
                // X or Z's become mask, ala case statements.
                V3Number nummask(rhsp, rhsp->width());
                nummask.opBitsNonX(VN_AS(rhsp, Const)->num());
                V3Number numval(rhsp, rhsp->width());
                numval.opBitsOne(VN_AS(rhsp, Const)->num());
                AstNode* const and1p = new AstAnd(nodep->fileline(), lhsp,
                                                  new AstConst(nodep->fileline(), nummask));
                AstNode* const and2p = new AstConst(nodep->fileline(), numval);
                if (VN_IS(nodep, EqWild)) {
                    newp = new AstEq(nodep->fileline(), and1p, and2p);
                } else {
                    newp = new AstNeq(nodep->fileline(), and1p, and2p);
                }
                VL_DO_DANGLING(rhsp->deleteTree(), rhsp);
            }
            nodep->replaceWith(newp);
            VL_DO_DANGLING(nodep->deleteTree(), nodep);
            // Iterate tree now that we may have gotten rid of the compare
            iterateChildren(newp);
        }
    }

    virtual void visit(AstEqCase* nodep) override { visitEqNeqCase(nodep); }
    virtual void visit(AstNeqCase* nodep) override { visitEqNeqCase(nodep); }
    virtual void visit(AstEqWild* nodep) override { visitEqNeqWild(nodep); }
    virtual void visit(AstNeqWild* nodep) override { visitEqNeqWild(nodep); }
    virtual void visit(AstIsUnknown* nodep) override {
        iterateChildren(nodep);
        // Ahh, we're two state, so this is easy
        UINFO(4, " ISUNKNOWN->0 " << nodep << endl);
        AstConst* const newp = new AstConst(nodep->fileline(), AstConst::BitFalse());
        nodep->replaceWith(newp);
        VL_DO_DANGLING(nodep->deleteTree(), nodep);
    }
    virtual void visit(AstCountBits* nodep) override {
        // Ahh, we're two state, so this is easy
        std::array<bool, 3> dropop;
        dropop[0] = VN_IS(nodep->rhsp(), Const) && VN_AS(nodep->rhsp(), Const)->num().isAnyX();
        dropop[1] = VN_IS(nodep->thsp(), Const) && VN_AS(nodep->thsp(), Const)->num().isAnyX();
        dropop[2] = VN_IS(nodep->fhsp(), Const) && VN_AS(nodep->fhsp(), Const)->num().isAnyX();
        UINFO(4, " COUNTBITS(" << dropop[0] << dropop[1] << dropop[2] << " " << nodep << endl);

        AstNode* nonXp = nullptr;
        if (!dropop[0]) {
            nonXp = nodep->rhsp();
        } else if (!dropop[1]) {
            nonXp = nodep->thsp();
        } else if (!dropop[2]) {
            nonXp = nodep->fhsp();
        } else {  // Was all X-s
            UINFO(4, " COUNTBITS('x)->0 " << nodep << endl);
            AstConst* const newp = new AstConst(nodep->fileline(), AstConst::BitFalse());
            nodep->replaceWith(newp);
            VL_DO_DANGLING(nodep->deleteTree(), nodep);
            return;
        }
        if (dropop[0]) {
            nodep->rhsp()->unlinkFrBack()->deleteTree();
            nodep->rhsp(nonXp->cloneTree(true));
        }
        if (dropop[1]) {
            nodep->thsp()->unlinkFrBack()->deleteTree();
            nodep->thsp(nonXp->cloneTree(true));
        }
        if (dropop[2]) {
            nodep->fhsp()->unlinkFrBack()->deleteTree();
            nodep->fhsp(nonXp->cloneTree(true));
        }
        iterateChildren(nodep);
    }
    virtual void visit(AstConst* nodep) override {
        if (m_constXCvt && nodep->num().isFourState()) {
            UINFO(4, " CONST4 " << nodep << endl);
            if (debug() >= 9) nodep->dumpTree(cout, "  Const_old: ");
            // CONST(num) -> VARREF(newvarp)
            //          -> VAR(newvarp)
            //          -> INITIAL(VARREF(newvarp, OR(num_No_Xs,AND(random,num_1s_Where_X))
            V3Number numb1(nodep, nodep->width());
            numb1.opBitsOne(nodep->num());
            V3Number numbx(nodep, nodep->width());
            numbx.opBitsXZ(nodep->num());
            if (!m_allowXUnique || v3Global.opt.xAssign() != "unique") {
                // All X bits just become 0; fastest simulation, but not nice
                V3Number numnew(nodep, numb1.width());
                if (v3Global.opt.xAssign() == "1") {
                    numnew.opOr(numb1, numbx);
                } else {
                    numnew.opAssign(numb1);
                }
                AstConst* const newp = new AstConst(nodep->fileline(), numnew);
                nodep->replaceWith(newp);
                VL_DO_DANGLING(nodep->deleteTree(), nodep);
                UINFO(4, "   -> " << newp << endl);
            } else {
                // Make a Vxrand variable
                // We use the special XTEMP type so it doesn't break pure functions
                UASSERT_OBJ(m_modp, nodep, "X number not under module");
                AstVar* const newvarp
                    = new AstVar(nodep->fileline(), VVarType::XTEMP, m_xrandNames.get(nodep),
                                 VFlagLogicPacked(), nodep->width());
                newvarp->lifetime(VLifetime::STATIC);
                ++m_statUnkVars;
                VNRelinker replaceHandle;
                nodep->unlinkFrBack(&replaceHandle);
                AstNodeVarRef* const newref1p
                    = new AstVarRef(nodep->fileline(), newvarp, VAccess::READ);
                replaceHandle.relink(newref1p);  // Replace const with varref
                AstInitial* const newinitp = new AstInitial(
                    nodep->fileline(),
                    new AstAssign(
                        nodep->fileline(),
                        new AstVarRef(nodep->fileline(), newvarp, VAccess::WRITE),
                        new AstOr(nodep->fileline(), new AstConst(nodep->fileline(), numb1),
                                  new AstAnd(nodep->fileline(),
                                             new AstConst(nodep->fileline(), numbx),
                                             new AstRand(nodep->fileline(), AstRand::Reset{},
                                                         nodep->dtypep(), true)))));
                // Add inits in front of other statement.
                // In the future, we should stuff the initp into the module's constructor.
                AstNode* const afterp = m_modp->stmtsp()->unlinkFrBackWithNext();
                m_modp->addStmtp(newvarp);
                m_modp->addStmtp(newinitp);
                m_modp->addStmtp(afterp);
                if (debug() >= 9) newref1p->dumpTree(cout, "     _new: ");
                if (debug() >= 9) newvarp->dumpTree(cout, "     _new: ");
                if (debug() >= 9) newinitp->dumpTree(cout, "     _new: ");
                VL_DO_DANGLING(nodep->deleteTree(), nodep);
            }
        }
    }

    virtual void visit(AstSel* nodep) override {
        iterateChildren(nodep);
        if (!nodep->user1SetOnce()) {
            // Guard against reading/writing past end of bit vector array
            const AstNode* const basefromp = AstArraySel::baseFromp(nodep, true);
            bool lvalue = false;
            if (const AstNodeVarRef* const varrefp = VN_CAST(basefromp, NodeVarRef)) {
                lvalue = varrefp->access().isWriteOrRW();
            }
            // Find range of dtype we are selecting from
            // Similar code in V3Const::warnSelect
            const int maxmsb = nodep->fromp()->dtypep()->width() - 1;
            if (debug() >= 9) nodep->dumpTree(cout, "sel_old: ");

            // If (maxmsb >= selected), we're in bound
            AstNode* condp = new AstGte(nodep->fileline(),
                                        new AstConst(nodep->fileline(), AstConst::WidthedValue(),
                                                     nodep->lsbp()->width(), maxmsb),
                                        nodep->lsbp()->cloneTree(false));
            // See if the condition is constant true (e.g. always in bound due to constant select)
            // Note below has null backp(); the Edit function knows how to deal with that.
            condp = V3Const::constifyEdit(condp);
            if (condp->isOne()) {
                // We don't need to add a conditional; we know the existing expression is ok
                VL_DO_DANGLING(condp->deleteTree(), condp);
            } else if (!lvalue) {
                // SEL(...) -> COND(LTE(bit<=maxmsb), ARRAYSEL(...), {width{1'bx}})
                VNRelinker replaceHandle;
                nodep->unlinkFrBack(&replaceHandle);
                V3Number xnum(nodep, nodep->width());
                xnum.setAllBitsX();
                AstNode* const newp = new AstCondBound(nodep->fileline(), condp, nodep,
                                                       new AstConst(nodep->fileline(), xnum));
                if (debug() >= 9) newp->dumpTree(cout, "        _new: ");
                // Link in conditional
                replaceHandle.relink(newp);
                // Added X's, tristate them too
                iterate(newp);
            } else {  // lvalue
                replaceBoundLvalue(nodep, condp);
            }
        }
    }

    // visit(AstSliceSel) not needed as its bounds are constant and checked
    // in V3Width.

    virtual void visit(AstArraySel* nodep) override {
        iterateChildren(nodep);
        if (!nodep->user1SetOnce()) {
            if (debug() == 9) nodep->dumpTree(cout, "-in: ");
            // Guard against reading/writing past end of arrays
            AstNode* const basefromp = AstArraySel::baseFromp(nodep->fromp(), true);
            bool lvalue = false;
            if (const AstNodeVarRef* const varrefp = VN_CAST(basefromp, NodeVarRef)) {
                lvalue = varrefp->access().isWriteOrRW();
            } else if (VN_IS(basefromp, Const)) {
                // If it's a PARAMETER[bit], then basefromp may be a constant instead of a varrefp
            } else {
                nodep->v3fatalSrc("No VarRef or Const under ArraySel");
            }
            // Find range of dtype we are selecting from
            int declElements = -1;
            AstNodeDType* const dtypep = nodep->fromp()->dtypep()->skipRefp();
            UASSERT_OBJ(dtypep, nodep, "Select of non-selectable type");
            if (const AstNodeArrayDType* const adtypep = VN_CAST(dtypep, NodeArrayDType)) {
                declElements = adtypep->elementsConst();
            } else {
                nodep->v3error("Select from non-array " << dtypep->prettyTypeName());
            }
            if (debug() >= 9) nodep->dumpTree(cout, "arraysel_old: ");

            // See if the condition is constant true
            AstNode* condp = new AstGte(nodep->fileline(),
                                        new AstConst(nodep->fileline(), AstConst::WidthedValue(),
                                                     nodep->bitp()->width(), declElements - 1),
                                        nodep->bitp()->cloneTree(false));
            // Note below has null backp(); the Edit function knows how to deal with that.
            condp = V3Const::constifyEdit(condp);
            if (condp->isOne()) {
                // We don't need to add a conditional; we know the existing expression is ok
                VL_DO_DANGLING(condp->deleteTree(), condp);
            } else if (!lvalue
                       // Making a scalar would break if we're making an array
                       && !VN_IS(nodep->dtypep()->skipRefp(), NodeArrayDType)) {
                // ARRAYSEL(...) -> COND(LT(bit<maxbit), ARRAYSEL(...), {width{1'bx}})
                VNRelinker replaceHandle;
                nodep->unlinkFrBack(&replaceHandle);
                V3Number xnum(nodep, nodep->width());
                if (nodep->isString()) {
                    xnum = V3Number(V3Number::String(), nodep, "");
                } else {
                    xnum.setAllBitsX();
                }
                AstNode* const newp = new AstCondBound(nodep->fileline(), condp, nodep,
                                                       new AstConst(nodep->fileline(), xnum));
                if (debug() >= 9) newp->dumpTree(cout, "        _new: ");
                // Link in conditional, can blow away temp xor
                replaceHandle.relink(newp);
                // Added X's, tristate them too
                iterate(newp);
            } else if (!lvalue) {  // Mid-multidimension read, just use zero
                // ARRAYSEL(...) -> ARRAYSEL(COND(LT(bit<maxbit), bit, 0))
                VNRelinker replaceHandle;
                AstNode* const bitp = nodep->bitp()->unlinkFrBack(&replaceHandle);
                AstNode* const newp = new AstCondBound(
                    bitp->fileline(), condp, bitp,
                    new AstConst(bitp->fileline(), AstConst::WidthedValue(), bitp->width(), 0));
                // Added X's, tristate them too
                if (debug() >= 9) newp->dumpTree(cout, "        _new: ");
                replaceHandle.relink(newp);
                iterate(newp);
            } else {  // lvalue
                replaceBoundLvalue(nodep, condp);
            }
        }
    }
    //--------------------
    virtual void visit(AstNode* nodep) override { iterateChildren(nodep); }

public:
    // CONSTRUCTORS
    explicit UnknownVisitor(AstNetlist* nodep)
        : m_lvboundNames{"__Vlvbound"}
        , m_xrandNames{"__Vxrand"} {
        iterate(nodep);
    }
    virtual ~UnknownVisitor() override {  //
        V3Stats::addStat("Unknowns, variables created", m_statUnkVars);
    }
};

//######################################################################
// Unknown class functions

void V3Unknown::unknownAll(AstNetlist* nodep) {
    UINFO(2, __FUNCTION__ << ": " << endl);
    { UnknownVisitor{nodep}; }  // Destruct before checking
    V3Global::dumpCheckGlobalTree("unknown", 0, v3Global.opt.dumpTreeLevel(__FILE__) >= 3);
}
