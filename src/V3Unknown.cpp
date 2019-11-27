// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Add Unknown assigns
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2019 by Wilson Snyder.  This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
//
// Verilator is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
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

#include "V3Global.h"
#include "V3Unknown.h"
#include "V3Ast.h"
#include "V3Const.h"
#include "V3Stats.h"

#include <algorithm>
#include <cstdarg>

//######################################################################

class UnknownVisitor : public AstNVisitor {
private:
    // NODE STATE
    // Cleared on Netlist
    //  AstSel::user()          -> bool.  Set true if already processed
    //  AstArraySel::user()     -> bool.  Set true if already processed
    //  AstNode::user2p()       -> AstIf* Inserted if assignment for conditional
    AstUser1InUse       m_inuser1;
    AstUser2InUse       m_inuser2;

    // STATE
    AstNodeModule*      m_modp;         // Current module
    bool                m_constXCvt;    // Convert X's
    VDouble0            m_statUnkVars;  // Statistic tracking
    AstAssignW*         m_assignwp;     // Current assignment
    AstAssignDly*       m_assigndlyp;   // Current assignment

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
            UINFO(5,"     IM_WireRep  "<<m_assignwp<<endl);
            m_assignwp->convertToAlways(); pushDeletep(m_assignwp); m_assignwp = NULL;
        }
        bool needDly = (m_assigndlyp != NULL);
        if (m_assigndlyp) {
            // Delayed assignments become normal assignments,
            // then the temp created becomes the delayed assignment
            AstNode* newp = new AstAssign(m_assigndlyp->fileline(),
                                          m_assigndlyp->lhsp()->unlinkFrBackWithNext(),
                                          m_assigndlyp->rhsp()->unlinkFrBackWithNext());
            m_assigndlyp->replaceWith(newp); pushDeletep(m_assigndlyp); m_assigndlyp = NULL;
        }
        AstNode* prep = nodep;

        // Scan back to put the condlvalue above all selects (IE top of the lvalue)
        while (VN_IS(prep->backp(), NodeSel)
               || VN_IS(prep->backp(), Sel)) {
            prep = prep->backp();
        }
        FileLine* fl = nodep->fileline();
        VL_DANGLING(nodep);  // Zap it so we don't use it by mistake - use prep

        // Already exists; rather than IF(a,... IF(b... optimize to IF(a&&b,
        // Saves us teaching V3Const how to optimize, and it won't be needed again.
        if (AstIf* ifp = VN_CAST(prep->user2p(), If)) {
            UASSERT_OBJ(!needDly, prep, "Should have already converted to non-delay");
            AstNRelinker replaceHandle;
            AstNode* earliercondp = ifp->condp()->unlinkFrBack(&replaceHandle);
            AstNode* newp = new AstLogAnd(condp->fileline(),
                                          condp, earliercondp);
            UINFO(4, "Edit BOUNDLVALUE "<<newp<<endl);
            replaceHandle.relink(newp);
        }
        else {
            string name = (string("__Vlvbound")+cvtToStr(m_modp->varNumGetInc()));
            AstVar* varp = new AstVar(fl, AstVarType::MODULETEMP, name,
                                      prep->dtypep());
            m_modp->addStmtp(varp);

            AstNode* abovep = prep->backp();  // Grab above point before lose it w/ next replace
            prep->replaceWith(new AstVarRef(fl, varp, true));
            AstIf* newp = new AstIf(fl, condp,
                                    (needDly
                                     ? static_cast<AstNode*>
                                     (new AstAssignDly(fl, prep,
                                                       new AstVarRef(fl, varp, false)))
                                     : static_cast<AstNode*>
                                     (new AstAssign(fl, prep,
                                                    new AstVarRef(fl, varp, false)))),
                                    NULL);
            newp->branchPred(VBranchPred::BP_LIKELY);
            if (debug()>=9) newp->dumpTree(cout, "     _new: ");
            abovep->addNextStmt(newp, abovep);
            prep->user2p(newp);  // Save so we may LogAnd it next time
        }
    }

    // VISITORS
    virtual void visit(AstNodeModule* nodep) {
        UINFO(4," MOD   "<<nodep<<endl);
        m_modp = nodep;
        m_constXCvt = true;
        iterateChildren(nodep);
        m_modp = NULL;
    }
    virtual void visit(AstAssignDly* nodep) {
        m_assigndlyp = nodep;
        iterateChildren(nodep); VL_DANGLING(nodep);  // May delete nodep.
        m_assigndlyp = NULL;
    }
    virtual void visit(AstAssignW* nodep) {
        m_assignwp = nodep;
        iterateChildren(nodep); VL_DANGLING(nodep);  // May delete nodep.
        m_assignwp = NULL;
    }
    virtual void visit(AstCaseItem* nodep) {
        m_constXCvt = false;  // Avoid losing the X's in casex
        iterateAndNextNull(nodep->condsp());
        m_constXCvt = true;
        iterateAndNextNull(nodep->bodysp());
    }
    virtual void visit(AstNodeDType* nodep) {
        m_constXCvt = false;  // Avoid losing the X's in casex
        iterateChildren(nodep);
        m_constXCvt = true;
    }
    void visitEqNeqCase(AstNodeBiop* nodep) {
        UINFO(4," N/EQCASE->EQ "<<nodep<<endl);
        V3Const::constifyEdit(nodep->lhsp());  // lhsp may change
        V3Const::constifyEdit(nodep->rhsp());  // rhsp may change
        if (VN_IS(nodep->lhsp(), Const) && VN_IS(nodep->rhsp(), Const)) {
            // Both sides are constant, node can be constant
            V3Const::constifyEdit(nodep); VL_DANGLING(nodep);
            return;
        } else {
            AstNode* lhsp = nodep->lhsp()->unlinkFrBack();
            AstNode* rhsp = nodep->rhsp()->unlinkFrBack();
            AstNode* newp;
            // If we got ==1'bx it can never be true (but 1'bx==1'bx can be!)
            if (((VN_IS(lhsp, Const) && VN_CAST(lhsp, Const)->num().isFourState())
                 || (VN_IS(rhsp, Const) && VN_CAST(rhsp, Const)->num().isFourState()))) {
                newp = new AstConst(nodep->fileline(), AstConst::WidthedValue(),
                                    1, (VN_IS(nodep, EqCase) ? 0 : 1));
                lhsp->deleteTree(); VL_DANGLING(lhsp);
                rhsp->deleteTree(); VL_DANGLING(rhsp);
            } else {
                if (VN_IS(nodep, EqCase)) {
                    newp = new AstEq(nodep->fileline(), lhsp, rhsp);
                } else { newp = new AstNeq(nodep->fileline(), lhsp, rhsp); }
            }
            nodep->replaceWith(newp);
            nodep->deleteTree(); VL_DANGLING(nodep);
            // Iterate tree now that we may have gotten rid of Xs
            iterateChildren(newp);
        }
    }
    void visitEqNeqWild(AstNodeBiop* nodep) {
        UINFO(4," N/EQWILD->EQ "<<nodep<<endl);
        V3Const::constifyEdit(nodep->lhsp());  // lhsp may change
        V3Const::constifyEdit(nodep->rhsp());  // rhsp may change
        if (VN_IS(nodep->lhsp(), Const) && VN_IS(nodep->rhsp(), Const)) {
            // Both sides are constant, node can be constant
            V3Const::constifyEdit(nodep); VL_DANGLING(nodep);
            return;
        } else {
            AstNode* lhsp = nodep->lhsp()->unlinkFrBack();
            AstNode* rhsp = nodep->rhsp()->unlinkFrBack();
            AstNode* newp;
            if (!VN_IS(rhsp, Const)) {
                nodep->v3error("Unsupported: RHS of ==? or !=? must be constant to be synthesizable");  // Says spec.
                // Replace with anything that won't cause more errors
                newp = new AstEq(nodep->fileline(), lhsp, rhsp);
            } else {
                // X or Z's become mask, ala case statements.
                V3Number nummask (rhsp, rhsp->width());
                nummask.opBitsNonX(VN_CAST(rhsp, Const)->num());
                V3Number numval (rhsp, rhsp->width());
                numval.opBitsOne(VN_CAST(rhsp, Const)->num());
                AstNode* and1p = new AstAnd(nodep->fileline(), lhsp,
                                            new AstConst(nodep->fileline(), nummask));
                AstNode* and2p = new AstConst(nodep->fileline(), numval);
                if (VN_IS(nodep, EqWild)) {
                    newp  = new AstEq(nodep->fileline(), and1p, and2p);
                } else { newp = new AstNeq(nodep->fileline(), and1p, and2p); }
                rhsp->deleteTree(); VL_DANGLING(rhsp);
            }
            nodep->replaceWith(newp);
            nodep->deleteTree(); VL_DANGLING(nodep);
            // Iterate tree now that we may have gotten rid of the compare
            iterateChildren(newp);
        }
    }

    virtual void visit(AstEqCase* nodep) {
        visitEqNeqCase(nodep);
    }
    virtual void visit(AstNeqCase* nodep) {
        visitEqNeqCase(nodep);
    }
    virtual void visit(AstEqWild* nodep) {
        visitEqNeqWild(nodep);
    }
    virtual void visit(AstNeqWild* nodep) {
        visitEqNeqWild(nodep);
    }
    virtual void visit(AstIsUnknown* nodep) {
        iterateChildren(nodep);
        // Ahh, we're two state, so this is easy
        UINFO(4," ISUNKNOWN->0 "<<nodep<<endl);
        AstConst* newp = new AstConst(nodep->fileline(), AstConst::LogicFalse());
        nodep->replaceWith(newp);
        nodep->deleteTree(); VL_DANGLING(nodep);
    }
    virtual void visit(AstConst* nodep) {
        if (m_constXCvt
            && nodep->num().isFourState()) {
            UINFO(4," CONST4 "<<nodep<<endl);
            if (debug()>=9) nodep->dumpTree(cout, "  Const_old: ");
            // CONST(num) -> VARREF(newvarp)
            //          -> VAR(newvarp)
            //          -> INITIAL(VARREF(newvarp, OR(num_No_Xs,AND(random,num_1s_Where_X))
            V3Number numb1 (nodep, nodep->width());
            numb1.opBitsOne(nodep->num());
            V3Number numbx (nodep, nodep->width());
            numbx.opBitsXZ(nodep->num());
            if (v3Global.opt.xAssign()!="unique") {
                // All X bits just become 0; fastest simulation, but not nice
                V3Number numnew (nodep, numb1.width());
                if (v3Global.opt.xAssign()=="1") {
                    numnew.opOr(numb1, numbx);
                } else {
                    numnew.opAssign(numb1);
                }
                AstConst* newp = new AstConst(nodep->fileline(), numnew);
                nodep->replaceWith(newp);
                nodep->deleteTree(); VL_DANGLING(nodep);
                UINFO(4,"   -> "<<newp<<endl);
            } else {
                // Make a Vxrand variable
                // We use the special XTEMP type so it doesn't break pure functions
                UASSERT_OBJ(m_modp, nodep, "X number not under module");
                string newvarname = (string("__Vxrand")
                                     +cvtToStr(m_modp->varNumGetInc()));
                AstVar* newvarp
                    = new AstVar(nodep->fileline(), AstVarType::XTEMP, newvarname,
                                 VFlagLogicPacked(), nodep->width());
                ++m_statUnkVars;
                AstNRelinker replaceHandle;
                nodep->unlinkFrBack(&replaceHandle);
                AstNodeVarRef* newref1p = new AstVarRef(nodep->fileline(), newvarp, false);
                replaceHandle.relink(newref1p);  // Replace const with varref
                AstInitial* newinitp
                    = new AstInitial(
                        nodep->fileline(),
                        new AstAssign(
                            nodep->fileline(),
                            new AstVarRef(nodep->fileline(), newvarp, true),
                            new AstOr(nodep->fileline(),
                                      new AstConst(nodep->fileline(), numb1),
                                      new AstAnd(nodep->fileline(),
                                                 new AstConst(nodep->fileline(), numbx),
                                                 new AstRand(nodep->fileline(),
                                                             nodep->dtypep(), true)))));
                // Add inits in front of other statement.
                // In the future, we should stuff the initp into the module's constructor.
                AstNode* afterp = m_modp->stmtsp()->unlinkFrBackWithNext();
                m_modp->addStmtp(newvarp);
                m_modp->addStmtp(newinitp);
                m_modp->addStmtp(afterp);
                if (debug()>=9) newref1p->dumpTree(cout, "     _new: ");
                if (debug()>=9) newvarp->dumpTree(cout, "     _new: ");
                if (debug()>=9) newinitp->dumpTree(cout, "     _new: ");
                nodep->deleteTree(); VL_DANGLING(nodep);
            }
        }
    }

    virtual void visit(AstSel* nodep) {
        iterateChildren(nodep);
        if (!nodep->user1SetOnce()) {
            // Guard against reading/writing past end of bit vector array
            AstNode* basefromp = AstArraySel::baseFromp(nodep);
            bool lvalue = false;
            if (const AstNodeVarRef* varrefp = VN_CAST(basefromp, NodeVarRef)) {
                lvalue = varrefp->lvalue();
            }
            // Find range of dtype we are selecting from
            // Similar code in V3Const::warnSelect
            int maxmsb = nodep->fromp()->dtypep()->width()-1;
            if (debug()>=9) nodep->dumpTree(cout, "sel_old: ");

            // If (maxmsb >= selected), we're in bound
            AstNode* condp = new AstGte(nodep->fileline(),
                                        new AstConst(nodep->fileline(),
                                                     AstConst::WidthedValue(),
                                                     nodep->lsbp()->width(), maxmsb),
                                        nodep->lsbp()->cloneTree(false));
            // See if the condition is constant true (e.g. always in bound due to constant select)
            // Note below has null backp(); the Edit function knows how to deal with that.
            condp = V3Const::constifyEdit(condp);
            if (condp->isOne()) {
                // We don't need to add a conditional; we know the existing expression is ok
                condp->deleteTree();
            }
            else if (!lvalue) {
                // SEL(...) -> COND(LTE(bit<=maxmsb), ARRAYSEL(...), {width{1'bx}})
                AstNRelinker replaceHandle;
                nodep->unlinkFrBack(&replaceHandle);
                V3Number xnum (nodep, nodep->width());
                xnum.setAllBitsX();
                AstNode* newp = new AstCondBound(nodep->fileline(),
                                                 condp,
                                                 nodep,
                                                 new AstConst(nodep->fileline(), xnum));
                if (debug()>=9) newp->dumpTree(cout, "        _new: ");
                // Link in conditional
                replaceHandle.relink(newp);
                // Added X's, tristate them too
                iterate(newp);
            }
            else {  // lvalue
                replaceBoundLvalue(nodep, condp);
            }
        }
    }

    // visit(AstSliceSel) not needed as its bounds are constant and checked
    // in V3Width.

    virtual void visit(AstArraySel* nodep) {
        iterateChildren(nodep);
        if (!nodep->user1SetOnce()) {
            if (debug()==9) nodep->dumpTree(cout, "-in: ");
            // Guard against reading/writing past end of arrays
            AstNode* basefromp = AstArraySel::baseFromp(nodep->fromp());
            bool lvalue = false;
            if (const AstNodeVarRef* varrefp = VN_CAST(basefromp, NodeVarRef)) {
                lvalue = varrefp->lvalue();
            } else if (VN_IS(basefromp, Const)) {
                // If it's a PARAMETER[bit], then basefromp may be a constant instead of a varrefp
            } else {
                nodep->v3fatalSrc("No VarRef or Const under ArraySel");
            }
            // Find range of dtype we are selecting from
            int declElements = -1;
            AstNodeDType* dtypep = nodep->fromp()->dtypep()->skipRefp();
            UASSERT_OBJ(dtypep, nodep, "Select of non-selectable type");
            if (const AstNodeArrayDType* adtypep = VN_CAST(dtypep, NodeArrayDType)) {
                declElements = adtypep->elementsConst();
            } else {
                nodep->v3error("Select from non-array "<<dtypep->prettyTypeName());
            }
            if (debug()>=9) nodep->dumpTree(cout, "arraysel_old: ");

            // See if the condition is constant true
            AstNode* condp = new AstGte(nodep->fileline(),
                                        new AstConst(nodep->fileline(), AstConst::WidthedValue(),
                                                     nodep->bitp()->width(), declElements-1),
                                        nodep->bitp()->cloneTree(false));
            // Note below has null backp(); the Edit function knows how to deal with that.
            condp = V3Const::constifyEdit(condp);
            if (condp->isOne()) {
                // We don't need to add a conditional; we know the existing expression is ok
                condp->deleteTree();
            }
            else if (!lvalue
                     // Making a scalar would break if we're making an array
                     && !VN_IS(nodep->dtypep()->skipRefp(), NodeArrayDType)) {
                // ARRAYSEL(...) -> COND(LT(bit<maxbit), ARRAYSEL(...), {width{1'bx}})
                AstNRelinker replaceHandle;
                nodep->unlinkFrBack(&replaceHandle);
                V3Number xnum (nodep, nodep->width());
                if (nodep->isString()) {
                    xnum = V3Number(V3Number::String(), nodep, "");
                } else {
                    xnum.setAllBitsX();
                }
                AstNode* newp = new AstCondBound(nodep->fileline(),
                                                 condp, nodep,
                                                 new AstConst(nodep->fileline(), xnum));
                if (debug()>=9) newp->dumpTree(cout, "        _new: ");
                // Link in conditional, can blow away temp xor
                replaceHandle.relink(newp);
                // Added X's, tristate them too
                iterate(newp);
            }
            else if (!lvalue) {  // Mid-multidimension read, just use zero
                // ARRAYSEL(...) -> ARRAYSEL(COND(LT(bit<maxbit), bit, 0))
                AstNRelinker replaceHandle;
                AstNode* bitp = nodep->bitp()->unlinkFrBack(&replaceHandle);
                AstNode* newp = new AstCondBound(bitp->fileline(),
                                                 condp, bitp,
                                                 new AstConst(bitp->fileline(),
                                                              AstConst::WidthedValue(),
                                                              bitp->width(), 0));
                // Added X's, tristate them too
                if (debug()>=9) newp->dumpTree(cout, "        _new: ");
                replaceHandle.relink(newp);
                iterate(newp);
            }
            else {  // lvalue
                replaceBoundLvalue(nodep, condp);
            }
        }
    }
    //--------------------
    // Default: Just iterate
    virtual void visit(AstNode* nodep) {
        iterateChildren(nodep);
    }

public:
    // CONSTRUCTORS
    explicit UnknownVisitor(AstNetlist* nodep) {
        m_modp = NULL;
        m_assigndlyp = NULL;
        m_assignwp = NULL;
        m_constXCvt = false;
        iterate(nodep);
    }
    virtual ~UnknownVisitor() {
        V3Stats::addStat("Unknowns, variables created", m_statUnkVars);
    }
};

//######################################################################
// Unknown class functions

void V3Unknown::unknownAll(AstNetlist* nodep) {
    UINFO(2,__FUNCTION__<<": "<<endl);
    {
        UnknownVisitor visitor (nodep);
    }  // Destruct before checking
    V3Global::dumpCheckGlobalTree("unknown", 0, v3Global.opt.dumpTreeLevel(__FILE__) >= 3);
}
