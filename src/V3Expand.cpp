// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Add temporaries, such as for expand nodes
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2004-2021 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************
// V3Expand's Transformations:
//
// Each module:
//      Expand verilated.h macros into internal micro optimizations (RTL)
//      this will enable later optimizations.
//      Wide operands become assignments to each word of the vector, (WORDSELs)
//          Note in this case that the widthMin is not correct for the MSW of
//          the vector.  This must be accounted for if doing later constant
//          propagation across signals.
//
//*************************************************************************

#include "config_build.h"
#include "verilatedos.h"

#include "V3Global.h"
#include "V3Expand.h"
#include "V3Stats.h"
#include "V3Ast.h"

#include <algorithm>

//######################################################################
// Expand state, as a visitor of each AstNode

class ExpandVisitor final : public AstNVisitor {
private:
    // NODE STATE
    //  AstNode::user1()        -> bool.  Processed
    AstUser1InUse m_inuser1;

    // STATE
    AstNode* m_stmtp = nullptr;  // Current statement
    VDouble0 m_statWides;  // Statistic tracking
    VDouble0 m_statWideWords;  // Statistic tracking
    VDouble0 m_statWideLimited;  // Statistic tracking

    // METHODS
    VL_DEBUG_FUNC;  // Declare debug()

    bool doExpand(AstNode* nodep) {
        ++m_statWides;
        if (nodep->widthWords() <= v3Global.opt.expandLimit()) {
            m_statWideWords += nodep->widthWords();
            return true;
        } else {
            ++m_statWideLimited;
            return false;
        }
    }

    int longOrQuadWidth(AstNode* nodep) {
        return (nodep->width() + (VL_EDATASIZE - 1)) & ~(VL_EDATASIZE - 1);
    }
    V3Number notWideMask(AstNode* nodep) {
        return V3Number(nodep, VL_EDATASIZE, ~VL_MASK_E(nodep->widthMin()));
    }
    V3Number wordMask(AstNode* nodep) {
        if (nodep->isWide()) {
            return V3Number(nodep, VL_EDATASIZE, VL_MASK_E(nodep->widthMin()));
        } else {
            V3Number mask(nodep, longOrQuadWidth(nodep));
            mask.setMask(nodep->widthMin());
            return mask;
        }
    }

    void insertBefore(AstNode* placep, AstNode* newp) {
        newp->user1(1);  // Already processed, don't need to re-iterate
        AstNRelinker linker;
        placep->unlinkFrBack(&linker);
        newp->addNext(placep);
        linker.relink(newp);
    }
    void replaceWithDelete(AstNode* nodep, AstNode* newp) {
        newp->user1(1);  // Already processed, don't need to re-iterate
        nodep->replaceWith(newp);
        VL_DO_DANGLING(nodep->deleteTree(), nodep);
    }
    AstNode* newWordAssign(AstNodeAssign* placep, int word, AstNode* lhsp, AstNode* rhsp) {
        AstAssign* newp = new AstAssign(placep->fileline(),
                                        new AstWordSel(placep->fileline(), lhsp->cloneTree(true),
                                                       new AstConst(placep->fileline(), word)),
                                        rhsp);
        return newp;
    }
    void addWordAssign(AstNodeAssign* placep, int word, AstNode* lhsp, AstNode* rhsp) {
        insertBefore(placep, newWordAssign(placep, word, lhsp, rhsp));
    }
    void addWordAssign(AstNodeAssign* placep, int word, AstNode* rhsp) {
        addWordAssign(placep, word, placep->lhsp(), rhsp);
    }

    void fixCloneLvalue(AstNode* nodep) {
        // In AstSel transforms, we call clone() on VarRefs that were lvalues,
        // but are now being used on the RHS of the assignment
        if (VN_IS(nodep, VarRef)) VN_CAST(nodep, VarRef)->access(VAccess::READ);
        // Iterate
        if (nodep->op1p()) fixCloneLvalue(nodep->op1p());
        if (nodep->op2p()) fixCloneLvalue(nodep->op2p());
        if (nodep->op3p()) fixCloneLvalue(nodep->op3p());
        if (nodep->op4p()) fixCloneLvalue(nodep->op4p());
    }

    AstNode* newAstWordSelClone(AstNode* nodep, int word) {
        // Get the specified word number from a wide array
        // Or, if it's a long/quad, do appropriate conversion to wide
        // Concat may pass negative word numbers, that means it wants a zero
        if (nodep->isWide() && word >= 0 && word < nodep->widthWords()) {
            return new AstWordSel(nodep->fileline(), nodep->cloneTree(true),
                                  new AstConst(nodep->fileline(), word));
        } else if (nodep->isQuad() && word == 0) {
            AstNode* quadfromp = nodep->cloneTree(true);
            quadfromp->dtypeSetBitUnsized(VL_QUADSIZE, quadfromp->widthMin(), VSigning::UNSIGNED);
            return new AstCCast(nodep->fileline(), quadfromp, VL_EDATASIZE);
        } else if (nodep->isQuad() && word == 1) {
            AstNode* quadfromp = nodep->cloneTree(true);
            quadfromp->dtypeSetBitUnsized(VL_QUADSIZE, quadfromp->widthMin(), VSigning::UNSIGNED);
            return new AstCCast(nodep->fileline(),
                                new AstShiftR(nodep->fileline(), quadfromp,
                                              new AstConst(nodep->fileline(), VL_EDATASIZE),
                                              VL_EDATASIZE),
                                VL_EDATASIZE);
        } else if (!nodep->isWide() && !nodep->isQuad() && word == 0) {
            return nodep->cloneTree(true);
        } else {  // Out of bounds
            return new AstConst(nodep->fileline(), 0);
        }
    }

    AstNode* newWordGrabShift(FileLine* fl, int word, AstNode* lhsp, int shift) {
        // Extract the expression to grab the value for the specified word, if it's the shift
        // of shift bits from lhsp
        AstNode* newp;
        // Negative word numbers requested for lhs when it's "before" what we want.
        // We get a 0 then.
        int othword = word - shift / VL_EDATASIZE;
        AstNode* llowp = newAstWordSelClone(lhsp, othword);
        if (int loffset = VL_BITBIT_E(shift)) {
            AstNode* lhip = newAstWordSelClone(lhsp, othword - 1);
            int nbitsonright = VL_EDATASIZE - loffset;  // bits that end up in lword
            newp = new AstOr(
                fl,
                new AstAnd(fl, new AstConst(fl, AstConst::SizedEData(), VL_MASK_E(loffset)),
                           new AstShiftR(fl, lhip, new AstConst(fl, nbitsonright), VL_EDATASIZE)),
                new AstAnd(fl, new AstConst(fl, AstConst::SizedEData(), ~VL_MASK_E(loffset)),
                           new AstShiftL(fl, llowp, new AstConst(fl, loffset), VL_EDATASIZE)));
        } else {
            newp = llowp;
        }
        return newp;
    }

    AstNode* newWordSel(FileLine* fl, AstNode* fromp, AstNode* lsbp, int wordAdder) {
        // Return equation to get the VL_BITWORD of a constant or non-constant
        UASSERT_OBJ(fromp->isWide(), fromp, "Only need AstWordSel on wide from's");
        if (wordAdder >= fromp->widthWords()) {
            // e.g. "logic [95:0] var[0]; logic [0] sel; out = var[sel];"
            // Squash before C++ to avoid getting a C++ compiler warning
            // (even though code would be unreachable as presumably a
            // AstCondBound is protecting above this node.
            return new AstConst(fl, AstConst::SizedEData(), 0);
        } else {
            AstNode* wordp;
            if (VN_IS(lsbp, Const)) {
                wordp = new AstConst(lsbp->fileline(),
                                     wordAdder + VL_BITWORD_E(VN_CAST(lsbp, Const)->toUInt()));
            } else {
                wordp = new AstShiftR(lsbp->fileline(), lsbp->cloneTree(true),
                                      new AstConst(lsbp->fileline(), VL_EDATASIZE_LOG2),
                                      VL_EDATASIZE);
                if (wordAdder != 0) {
                    wordp = new AstAdd(lsbp->fileline(),
                                       // This is indexing a arraysel, so a 32 bit constant is fine
                                       new AstConst(lsbp->fileline(), wordAdder), wordp);
                }
            }
            return new AstWordSel(fl, fromp, wordp);
        }
    }

    AstNode* dropCondBound(AstNode* nodep) {
        // Experimental only...
        //  If there's a CONDBOUND safety to keep arrays in bounds,
        //  we're going to AND it to a value that always fits inside a
        //  word, so we don't need it.
        // if (VN_IS(nodep, CondBound) && VN_IS(VN_CAST(nodep, CondBound)->lhsp(), Lte)) {
        //    nodep = VN_CAST(nodep, CondBound)->rhsp();
        //}
        return nodep;
    }

    AstNode* newSelBitBit(AstNode* lsbp) {
        // Return equation to get the VL_BITBIT of a constant or non-constant
        if (VN_IS(lsbp, Const)) {
            return new AstConst(lsbp->fileline(), VL_BITBIT_E(VN_CAST(lsbp, Const)->toUInt()));
        } else {
            return new AstAnd(lsbp->fileline(), new AstConst(lsbp->fileline(), VL_EDATASIZE - 1),
                              dropCondBound(lsbp)->cloneTree(true));
        }
    }

    //====================

    bool expandWide(AstNodeAssign* nodep, AstConst* rhsp) {
        UINFO(8, "    Wordize ASSIGN(CONST) " << nodep << endl);
        if (!doExpand(nodep)) return false;
        // -> {for each_word{ ASSIGN(WORDSEL(wide,#),WORDSEL(CONST,#))}}
        if (rhsp->num().isFourState()) {
            rhsp->v3warn(E_UNSUPPORTED,  // LCOV_EXCL_LINE  // impossible?
                         "Unsupported: 4-state numbers in this context");
        }
        for (int w = 0; w < nodep->widthWords(); w++) {
            addWordAssign(
                nodep, w,
                new AstConst(nodep->fileline(), AstConst::SizedEData(), rhsp->num().edataWord(w)));
        }
        return true;
    }
    //-------- Uniops
    bool expandWide(AstNodeAssign* nodep, AstVarRef* rhsp) {
        UINFO(8, "    Wordize ASSIGN(VARREF) " << nodep << endl);
        if (!doExpand(nodep)) return false;
        for (int w = 0; w < nodep->widthWords(); w++) {
            addWordAssign(nodep, w, newAstWordSelClone(rhsp, w));
        }
        return true;
    }
    bool expandWide(AstNodeAssign* nodep, AstArraySel* rhsp) {
        UINFO(8, "    Wordize ASSIGN(ARRAYSEL) " << nodep << endl);
        UASSERT_OBJ(!VN_IS(nodep->dtypep()->skipRefp(), UnpackArrayDType), nodep,
                    "ArraySel with unpacked arrays should have been removed in V3Slice");
        if (!doExpand(nodep)) return false;
        for (int w = 0; w < nodep->widthWords(); w++) {
            addWordAssign(nodep, w, newAstWordSelClone(rhsp, w));
        }
        return true;
    }
    bool expandWide(AstNodeAssign* nodep, AstNot* rhsp) {
        UINFO(8, "    Wordize ASSIGN(NOT) " << nodep << endl);
        // -> {for each_word{ ASSIGN(WORDSEL(wide,#),NOT(WORDSEL(lhs,#))) }}
        if (!doExpand(nodep)) return false;
        for (int w = 0; w < nodep->widthWords(); w++) {
            addWordAssign(nodep, w,
                          new AstNot(rhsp->fileline(), newAstWordSelClone(rhsp->lhsp(), w)));
        }
        return true;
    }
    //-------- Biops
    bool expandWide(AstNodeAssign* nodep, AstAnd* rhsp) {
        UINFO(8, "    Wordize ASSIGN(AND) " << nodep << endl);
        if (!doExpand(nodep)) return false;
        for (int w = 0; w < nodep->widthWords(); w++) {
            addWordAssign(nodep, w,
                          new AstAnd(nodep->fileline(), newAstWordSelClone(rhsp->lhsp(), w),
                                     newAstWordSelClone(rhsp->rhsp(), w)));
        }
        return true;
    }
    bool expandWide(AstNodeAssign* nodep, AstOr* rhsp) {
        UINFO(8, "    Wordize ASSIGN(OR) " << nodep << endl);
        if (!doExpand(nodep)) return false;
        for (int w = 0; w < nodep->widthWords(); w++) {
            addWordAssign(nodep, w,
                          new AstOr(nodep->fileline(), newAstWordSelClone(rhsp->lhsp(), w),
                                    newAstWordSelClone(rhsp->rhsp(), w)));
        }
        return true;
    }
    bool expandWide(AstNodeAssign* nodep, AstXor* rhsp) {
        UINFO(8, "    Wordize ASSIGN(XOR) " << nodep << endl);
        if (!doExpand(nodep)) return false;
        for (int w = 0; w < nodep->widthWords(); w++) {
            addWordAssign(nodep, w,
                          new AstXor(nodep->fileline(), newAstWordSelClone(rhsp->lhsp(), w),
                                     newAstWordSelClone(rhsp->rhsp(), w)));
        }
        return true;
    }
    //-------- Triops
    bool expandWide(AstNodeAssign* nodep, AstNodeCond* rhsp) {
        UINFO(8, "    Wordize ASSIGN(COND) " << nodep << endl);
        if (!doExpand(nodep)) return false;
        for (int w = 0; w < nodep->widthWords(); w++) {
            addWordAssign(nodep, w,
                          new AstCond(nodep->fileline(), rhsp->condp()->cloneTree(true),
                                      newAstWordSelClone(rhsp->expr1p(), w),
                                      newAstWordSelClone(rhsp->expr2p(), w)));
        }
        return true;
    }

    // VISITORS
    virtual void visit(AstExtend* nodep) override {
        if (nodep->user1SetOnce()) return;  // Process once
        iterateChildren(nodep);
        if (nodep->isWide()) {
            // See under ASSIGN(EXTEND)
        } else {
            AstNode* lhsp = nodep->lhsp()->unlinkFrBack();
            AstNode* newp = lhsp;
            if (nodep->isQuad()) {
                if (lhsp->isQuad()) {
                    lhsp->dtypeFrom(nodep);  // Just mark it, else nop
                } else if (lhsp->isWide()) {
                    nodep->v3fatalSrc("extending larger thing into smaller?");
                } else {
                    UINFO(8, "    EXTEND(q<-l) " << nodep << endl);
                    newp = new AstCCast(nodep->fileline(), lhsp, nodep);
                }
            } else {  // Long
                UASSERT_OBJ(!(lhsp->isQuad() || lhsp->isWide()), nodep,
                            "extending larger thing into smaller?");
                lhsp->dtypeFrom(nodep);  // Just mark it, else nop
            }
            VL_DO_DANGLING(replaceWithDelete(nodep, newp), nodep);
        }
    }

    virtual void visit(AstSel* nodep) override {
        if (nodep->user1SetOnce()) return;  // Process once
        iterateChildren(nodep);
        // Remember, Sel's may have non-integer rhs, so need to optimize for that!
        UASSERT_OBJ(nodep->widthMin() == nodep->widthConst(), nodep, "Width mismatch");
        if (VN_IS(nodep->backp(), NodeAssign)
            && nodep == VN_CAST(nodep->backp(), NodeAssign)->lhsp()) {
            // Sel is an LHS assignment select
        } else if (nodep->isWide()) {
            // See under ASSIGN(WIDE)
        } else if (nodep->fromp()->isWide()) {
            UINFO(8, "    SEL(wide) " << nodep << endl);
            UASSERT_OBJ(nodep->widthConst() <= 64, nodep, "Inconsistent width");
            // Selection amounts
            // Check for constant shifts & save some constification work later.
            // Grab lowest bit(s)
            AstNode* lowwordp = newWordSel(nodep->fromp()->fileline(),
                                           nodep->fromp()->cloneTree(true), nodep->lsbp(), 0);
            if (nodep->isQuad() && !lowwordp->isQuad()) {
                lowwordp = new AstCCast(nodep->fileline(), lowwordp, nodep);
            }
            AstNode* lowp = new AstShiftR(nodep->fileline(), lowwordp, newSelBitBit(nodep->lsbp()),
                                          nodep->width());
            // If > 1 bit, we might be crossing the word boundary
            AstNode* midp = nullptr;
            V3Number zero(nodep, longOrQuadWidth(nodep));
            if (nodep->widthConst() > 1) {
                const uint32_t midMsbOffset
                    = std::min<uint32_t>(nodep->widthConst(), VL_EDATASIZE) - 1;
                AstNode* const midMsbp
                    = new AstAdd(nodep->lsbp()->fileline(),
                                 new AstConst(nodep->lsbp()->fileline(), midMsbOffset),
                                 nodep->lsbp()->cloneTree(false));
                AstNode* midwordp =  // SEL(from,[midwordnum])
                    newWordSel(nodep->fromp()->fileline(), nodep->fromp()->cloneTree(true),
                               midMsbp, 0);
                // newWordSel clones the index, so delete it
                VL_DO_DANGLING(midMsbp->deleteTree(), midMsbp);
                if (nodep->isQuad() && !midwordp->isQuad()) {
                    midwordp = new AstCCast(nodep->fileline(), midwordp, nodep);
                }
                AstNode* const midshiftp
                    = new AstSub(nodep->lsbp()->fileline(),
                                 new AstConst(nodep->lsbp()->fileline(), VL_EDATASIZE),
                                 newSelBitBit(nodep->lsbp()));
                // If we're selecting bit zero, then all 32 bits in the mid word
                // get shifted << by 32 bits, so ignore them.
                midp = new AstCond(
                    nodep->fileline(),
                    // lsb % VL_EDATASIZE == 0 ?

                    new AstEq(nodep->fileline(), new AstConst(nodep->fileline(), 0),
                              newSelBitBit(nodep->lsbp())),
                    // 0 :
                    new AstConst(nodep->fileline(), zero),
                    //  midword >> (VL_EDATASIZE - (lbs % VL_EDATASIZE))
                    new AstShiftL(nodep->fileline(), midwordp, midshiftp, nodep->width()));
            }
            // If > 32 bits, we might be crossing the second word boundary
            AstNode* hip = nullptr;
            if (nodep->widthConst() > VL_EDATASIZE) {
                const uint32_t hiMsbOffset = nodep->widthConst() - 1;
                AstNode* const hiMsbp
                    = new AstAdd(nodep->lsbp()->fileline(),
                                 new AstConst(nodep->lsbp()->fileline(), hiMsbOffset),
                                 nodep->lsbp()->cloneTree(false));
                AstNode* hiwordp =  // SEL(from,[hiwordnum])
                    newWordSel(nodep->fromp()->fileline(), nodep->fromp()->cloneTree(true), hiMsbp,
                               0);
                // newWordSel clones the index, so delete it
                VL_DO_DANGLING(hiMsbp->deleteTree(), hiMsbp);
                if (nodep->isQuad() && !hiwordp->isQuad()) {
                    hiwordp = new AstCCast(nodep->fileline(), hiwordp, nodep);
                }
                AstNode* const hishiftp
                    = new AstCond(nodep->fileline(),
                                  // lsb % VL_EDATASIZE == 0 ?
                                  new AstEq(nodep->fileline(), new AstConst(nodep->fileline(), 0),
                                            newSelBitBit(nodep->lsbp())),
                                  // VL_EDATASIZE :
                                  new AstConst(nodep->lsbp()->fileline(), VL_EDATASIZE),
                                  // 64 - (lbs % VL_EDATASIZE)
                                  new AstSub(nodep->lsbp()->fileline(),
                                             new AstConst(nodep->lsbp()->fileline(), 64),
                                             newSelBitBit(nodep->lsbp())));
                hip = new AstShiftL(nodep->fileline(), hiwordp, hishiftp, nodep->width());
            }

            AstNode* newp = lowp;
            if (midp) newp = new AstOr(nodep->fileline(), midp, newp);
            if (hip) newp = new AstOr(nodep->fileline(), hip, newp);
            newp->dtypeFrom(nodep);
            VL_DO_DANGLING(replaceWithDelete(nodep, newp), nodep);
        } else {  // Long/Quad from Long/Quad
            UINFO(8, "    SEL->SHIFT " << nodep << endl);
            AstNode* fromp = nodep->fromp()->unlinkFrBack();
            AstNode* lsbp = nodep->lsbp()->unlinkFrBack();
            if (nodep->isQuad() && !fromp->isQuad()) {
                fromp = new AstCCast(nodep->fileline(), fromp, nodep);
            }
            AstNode* newp = new AstShiftR(
                nodep->fileline(), fromp, dropCondBound(lsbp),
                fromp->width());  // {large}>>32 requires 64-bit shift operation; then cast
            newp->dtypeFrom(fromp);
            if (!nodep->isQuad() && fromp->isQuad()) {
                newp = new AstCCast(newp->fileline(), newp, nodep);
            }
            newp->dtypeFrom(nodep);
            VL_DO_DANGLING(replaceWithDelete(nodep, newp), nodep);
        }
    }

    bool expandWide(AstNodeAssign* nodep, AstSel* rhsp) {
        UASSERT_OBJ(nodep->widthMin() == rhsp->widthConst(), nodep, "Width mismatch");
        if (!doExpand(nodep)) return false;
        if (VN_IS(rhsp->lsbp(), Const) && VL_BITBIT_E(rhsp->lsbConst()) == 0) {
            int lsb = rhsp->lsbConst();
            UINFO(8, "    Wordize ASSIGN(SEL,align) " << nodep << endl);
            for (int w = 0; w < nodep->widthWords(); w++) {
                addWordAssign(nodep, w, newAstWordSelClone(rhsp->fromp(), w + VL_BITWORD_E(lsb)));
            }
            return true;
        } else {
            UINFO(8, "    Wordize ASSIGN(EXTRACT,misalign) " << nodep << endl);
            for (int w = 0; w < nodep->widthWords(); w++) {
                // Grab lowest bits
                AstNode* lowwordp = newWordSel(rhsp->fileline(), rhsp->fromp()->cloneTree(true),
                                               rhsp->lsbp(), w);
                AstNode* lowp = new AstShiftR(rhsp->fileline(), lowwordp,
                                              newSelBitBit(rhsp->lsbp()), VL_EDATASIZE);
                // Upper bits
                V3Number zero(nodep, VL_EDATASIZE, 0);
                AstNode* midwordp =  // SEL(from,[1+wordnum])
                    newWordSel(rhsp->fromp()->fileline(), rhsp->fromp()->cloneTree(true),
                               rhsp->lsbp(), w + 1);
                AstNode* midshiftp = new AstSub(
                    rhsp->lsbp()->fileline(), new AstConst(rhsp->lsbp()->fileline(), VL_EDATASIZE),
                    newSelBitBit(rhsp->lsbp()));
                AstNode* midmayp
                    = new AstShiftL(rhsp->fileline(), midwordp, midshiftp, VL_EDATASIZE);
                AstNode* midp
                    = new AstCond(rhsp->fileline(),
                                  new AstEq(rhsp->fileline(), new AstConst(rhsp->fileline(), 0),
                                            newSelBitBit(rhsp->lsbp())),
                                  new AstConst(rhsp->fileline(), zero), midmayp);
                AstNode* newp = new AstOr(nodep->fileline(), midp, lowp);
                addWordAssign(nodep, w, newp);
            }
            return true;
        }
    }

    bool expandLhs(AstNodeAssign* nodep, AstSel* lhsp) {
        // Possibilities
        //      destp: wide or narrow
        //      rhsp:  wide (destp must be wide), narrow, or 1 bit wide
        //      rhsp:  may be allones and can remove AND NOT gate
        //      lsbp:  constant or variable
        // Yuk.
        bool destwide = lhsp->fromp()->isWide();
        bool ones = nodep->rhsp()->isAllOnesV();
        if (VN_IS(lhsp->lsbp(), Const)) {
            // The code should work without this constant test, but it won't
            // constify as nicely as we'd like.
            AstNode* rhsp = nodep->rhsp()->unlinkFrBack();
            AstNode* destp = lhsp->fromp()->unlinkFrBack();
            int lsb = lhsp->lsbConst();
            int msb = lhsp->msbConst();
            V3Number maskset(nodep, destp->widthMin());
            for (int bit = lsb; bit < (msb + 1); bit++) maskset.setBit(bit, 1);
            V3Number maskold(nodep, destp->widthMin());
            maskold.opNot(maskset);
            if (destwide) {
                UINFO(8, "    ASSIGNSEL(const,wide) " << nodep << endl);
                for (int w = 0; w < destp->widthWords(); w++) {
                    if (w >= VL_BITWORD_E(lsb) && w <= VL_BITWORD_E(msb)) {
                        // else we would just be setting it to the same exact value
                        AstNode* oldvalp = newAstWordSelClone(destp, w);
                        fixCloneLvalue(oldvalp);
                        if (!ones) {
                            oldvalp
                                = new AstAnd(lhsp->fileline(),
                                             new AstConst(lhsp->fileline(), AstConst::SizedEData(),
                                                          maskold.edataWord(w)),
                                             oldvalp);
                        }

                        // Appropriate word of new value to insert:
                        AstNode* newp = newWordGrabShift(lhsp->fileline(), w, rhsp, lsb);

                        // Apply cleaning at the top word of the destination
                        // (no cleaning to do if dst's width is a whole number
                        // of words).
                        if (w == destp->widthWords() - 1 && VL_BITBIT_E(destp->widthMin()) != 0) {
                            V3Number cleanmask(nodep, VL_EDATASIZE);
                            cleanmask.setMask(VL_BITBIT_E(destp->widthMin()));
                            newp = new AstAnd(lhsp->fileline(), newp,
                                              new AstConst(lhsp->fileline(), cleanmask));
                        }

                        addWordAssign(nodep, w, destp, new AstOr(lhsp->fileline(), oldvalp, newp));
                    }
                }
                VL_DO_DANGLING(rhsp->deleteTree(), rhsp);
                VL_DO_DANGLING(destp->deleteTree(), destp);
            } else {
                UINFO(8, "    ASSIGNSEL(const,narrow) " << nodep << endl);
                if (destp->isQuad() && !rhsp->isQuad()) {
                    rhsp = new AstCCast(nodep->fileline(), rhsp, nodep);
                }
                AstNode* oldvalp = destp->cloneTree(true);
                fixCloneLvalue(oldvalp);
                if (!ones) {
                    oldvalp = new AstAnd(lhsp->fileline(), new AstConst(lhsp->fileline(), maskold),
                                         oldvalp);
                }

                // The bit-select can refer to bits outside the width of nodep
                // which we aren't allowed to assign to.  This is a mask of the
                // valid range of nodep which we apply to the new shifted RHS.
                V3Number cleanmask(nodep, destp->widthMin());
                cleanmask.setMask(destp->widthMin());
                AstNode* shifted = new AstShiftL(
                    lhsp->fileline(), rhsp, new AstConst(lhsp->fileline(), lsb), destp->width());
                AstNode* cleaned = new AstAnd(lhsp->fileline(), shifted,
                                              new AstConst(lhsp->fileline(), cleanmask));
                AstNode* newp = new AstOr(lhsp->fileline(), oldvalp, cleaned);
                newp = new AstAssign(nodep->fileline(), destp, newp);
                insertBefore(nodep, newp);
            }
            return true;
        } else {  // non-const select offset
            if (destwide && lhsp->widthConst() == 1) {
                UINFO(8, "    ASSIGNSEL(varlsb,wide,1bit) " << nodep << endl);
                AstNode* rhsp = nodep->rhsp()->unlinkFrBack();
                AstNode* destp = lhsp->fromp()->unlinkFrBack();
                AstNode* oldvalp
                    = newWordSel(lhsp->fileline(), destp->cloneTree(true), lhsp->lsbp(), 0);
                fixCloneLvalue(oldvalp);
                if (!ones) {
                    oldvalp = new AstAnd(
                        lhsp->fileline(),
                        new AstNot(
                            lhsp->fileline(),
                            new AstShiftL(lhsp->fileline(), new AstConst(nodep->fileline(), 1),
                                          // newSelBitBit may exceed the MSB of this variable.
                                          // That's ok as we'd just AND with a larger value,
                                          // but oldval would clip the upper bits to sanity
                                          newSelBitBit(lhsp->lsbp()), VL_EDATASIZE)),
                        oldvalp);
                }
                // Restrict the shift amount to 0-31, see bug804.
                AstNode* shiftp = new AstAnd(nodep->fileline(), lhsp->lsbp()->cloneTree(true),
                                             new AstConst(nodep->fileline(), VL_EDATASIZE - 1));
                AstNode* newp
                    = new AstOr(lhsp->fileline(), oldvalp,
                                new AstShiftL(lhsp->fileline(), rhsp, shiftp, VL_EDATASIZE));
                newp = new AstAssign(nodep->fileline(),
                                     newWordSel(nodep->fileline(), destp, lhsp->lsbp(), 0), newp);
                insertBefore(nodep, newp);
                return true;
            } else if (destwide) {
                UINFO(8, "    ASSIGNSEL(varlsb,wide) -- NoOp -- " << nodep << endl);
                //   For wide destp, we can either form a equation for every destination word,
                // with the appropriate long equation of if it's being written or not.
                //   Or, we can use a LHS variable arraysel with
                //   non-constant index to set the vector.
                // Doing the variable arraysel is better for globals and large arrays,
                // doing every word is better for temporaries and if we're setting most words
                // since it may result in better substitution optimizations later.
                //   This results in so much code, we're better off leaving a function call.
                // Reconsider if we get subexpression elimination.
                return false;
            } else {
                UINFO(8, "    ASSIGNSEL(varlsb,narrow) " << nodep << endl);
                // nodep->dumpTree(cout, "-  old: ");
                AstNode* rhsp = nodep->rhsp()->unlinkFrBack();
                AstNode* destp = lhsp->fromp()->unlinkFrBack();
                AstNode* oldvalp = destp->cloneTree(true);
                fixCloneLvalue(oldvalp);

                V3Number maskwidth(nodep, destp->widthMin());
                for (int bit = 0; bit < lhsp->widthConst(); bit++) maskwidth.setBit(bit, 1);

                if (destp->isQuad() && !rhsp->isQuad()) {
                    rhsp = new AstCCast(nodep->fileline(), rhsp, nodep);
                }
                if (!ones) {
                    oldvalp = new AstAnd(
                        lhsp->fileline(),
                        new AstNot(lhsp->fileline(),
                                   new AstShiftL(lhsp->fileline(),
                                                 new AstConst(nodep->fileline(), maskwidth),
                                                 lhsp->lsbp()->cloneTree(true), destp->width())),
                        oldvalp);
                }
                AstNode* newp = new AstShiftL(lhsp->fileline(), rhsp,
                                              lhsp->lsbp()->cloneTree(true), destp->width());
                // Apply cleaning to the new value being inserted.  Mask is
                // slightly wider than necessary to avoid an AND with all ones
                // being optimized out.  No need to clean if destp is
                // quad-sized as there are no extra bits to contaminate
                if (destp->widthMin() != 64) {
                    V3Number cleanmask(nodep, destp->widthMin() + 1);
                    cleanmask.setMask(destp->widthMin());
                    newp = new AstAnd(lhsp->fileline(), newp,
                                      new AstConst(lhsp->fileline(), cleanmask));
                }

                newp = new AstAssign(nodep->fileline(), destp,
                                     new AstOr(lhsp->fileline(), oldvalp, newp));
                // newp->dumpTree(cout, "-  new: ");
                insertBefore(nodep, newp);
                return true;
            }
        }
    }

    virtual void visit(AstConcat* nodep) override {
        if (nodep->user1SetOnce()) return;  // Process once
        iterateChildren(nodep);
        if (nodep->isWide()) {
            // See under ASSIGN(WIDE)
        } else {
            UINFO(8, "    CONCAT " << nodep << endl);
            AstNode* lhsp = nodep->lhsp()->unlinkFrBack();
            AstNode* rhsp = nodep->rhsp()->unlinkFrBack();
            int rhsshift = rhsp->widthMin();
            if (nodep->isQuad() && !lhsp->isQuad()) {
                lhsp = new AstCCast(nodep->fileline(), lhsp, nodep);
            }
            if (nodep->isQuad() && !rhsp->isQuad()) {
                rhsp = new AstCCast(nodep->fileline(), rhsp, nodep);
            }
            AstNode* newp = new AstOr(nodep->fileline(),
                                      new AstShiftL(nodep->fileline(), lhsp,
                                                    new AstConst(nodep->fileline(), rhsshift),
                                                    nodep->width()),
                                      rhsp);
            newp->dtypeFrom(nodep);  // Unsigned
            VL_DO_DANGLING(replaceWithDelete(nodep, newp), nodep);
        }
    }
    bool expandWide(AstNodeAssign* nodep, AstConcat* rhsp) {
        UINFO(8, "    Wordize ASSIGN(CONCAT) " << nodep << endl);
        if (!doExpand(rhsp)) return false;
        // Lhs or Rhs may be word, long, or quad.
        // newAstWordSelClone nicely abstracts the difference.
        int rhsshift = rhsp->rhsp()->widthMin();
        // Sometimes doing the words backwards is preferable.
        // When we have x={x,foo} backwards is better, when x={foo,x} forward is better
        // However V3Subst tends to rip this up, so not worth optimizing now.
        for (int w = 0; w < rhsp->widthWords(); w++) {
            addWordAssign(nodep, w,
                          new AstOr(rhsp->fileline(),
                                    newWordGrabShift(rhsp->fileline(), w, rhsp->lhsp(), rhsshift),
                                    newAstWordSelClone(rhsp->rhsp(), w)));
        }
        return true;
    }

    virtual void visit(AstReplicate* nodep) override {
        if (nodep->user1SetOnce()) return;  // Process once
        iterateChildren(nodep);
        if (nodep->isWide()) {
            // See under ASSIGN(WIDE)
        } else {
            AstNode* lhsp = nodep->lhsp()->unlinkFrBack();
            AstNode* newp;
            int lhswidth = lhsp->widthMin();
            if (lhswidth == 1) {
                UINFO(8, "    REPLICATE(w1) " << nodep << endl);
                newp = new AstNegate(nodep->fileline(), lhsp);
            } else {
                UINFO(8, "    REPLICATE " << nodep << endl);
                const AstConst* constp = VN_CAST(nodep->rhsp(), Const);
                UASSERT_OBJ(constp, nodep,
                            "Replication value isn't a constant.  Checked earlier!");
                uint32_t times = constp->toUInt();
                if (nodep->isQuad() && !lhsp->isQuad()) {
                    lhsp = new AstCCast(nodep->fileline(), lhsp, nodep);
                }
                newp = lhsp->cloneTree(true);
                for (unsigned repnum = 1; repnum < times; repnum++) {
                    int rhsshift = repnum * lhswidth;
                    newp = new AstOr(nodep->fileline(),
                                     new AstShiftL(nodep->fileline(), lhsp->cloneTree(true),
                                                   new AstConst(nodep->fileline(), rhsshift),
                                                   nodep->width()),
                                     newp);
                    newp->dtypeFrom(nodep);  // Unsigned
                }
                VL_DO_DANGLING(lhsp->deleteTree(), lhsp);  // Never used
            }
            newp->dtypeFrom(nodep);  // Unsigned
            VL_DO_DANGLING(replaceWithDelete(nodep, newp), nodep);
        }
    }
    bool expandWide(AstNodeAssign* nodep, AstReplicate* rhsp) {
        UINFO(8, "    Wordize ASSIGN(REPLICATE) " << nodep << endl);
        if (!doExpand(rhsp)) return false;
        AstNode* lhsp = rhsp->lhsp();
        int lhswidth = lhsp->widthMin();
        const AstConst* constp = VN_CAST(rhsp->rhsp(), Const);
        UASSERT_OBJ(constp, rhsp, "Replication value isn't a constant.  Checked earlier!");
        uint32_t times = constp->toUInt();
        for (int w = 0; w < rhsp->widthWords(); w++) {
            AstNode* newp;
            if (lhswidth == 1) {
                newp = new AstNegate(nodep->fileline(), lhsp->cloneTree(true));
                newp->dtypeSetLogicSized(VL_EDATASIZE,
                                         VSigning::UNSIGNED);  // Replicate always unsigned
            } else {
                newp = newAstWordSelClone(lhsp, w);
                for (unsigned repnum = 1; repnum < times; repnum++) {
                    newp = new AstOr(
                        nodep->fileline(),
                        newWordGrabShift(rhsp->fileline(), w, lhsp, lhswidth * repnum), newp);
                }
            }
            addWordAssign(nodep, w, newp);
        }
        return true;
    }

    virtual void visit(AstChangeXor* nodep) override {
        if (nodep->user1SetOnce()) return;  // Process once
        iterateChildren(nodep);
        UINFO(8, "    Wordize ChangeXor " << nodep << endl);
        // -> (0=={or{for each_word{WORDSEL(lhs,#)^WORDSEL(rhs,#)}}}
        AstNode* newp = nullptr;
        for (int w = 0; w < nodep->lhsp()->widthWords(); w++) {
            AstNode* eqp = new AstXor(nodep->fileline(), newAstWordSelClone(nodep->lhsp(), w),
                                      newAstWordSelClone(nodep->rhsp(), w));
            newp = (newp == nullptr) ? eqp : (new AstOr(nodep->fileline(), newp, eqp));
        }
        VL_DO_DANGLING(replaceWithDelete(nodep, newp), nodep);
    }

    void visitEqNeq(AstNodeBiop* nodep) {
        if (nodep->user1SetOnce()) return;  // Process once
        iterateChildren(nodep);
        if (nodep->lhsp()->isWide()) {
            UINFO(8, "    Wordize EQ/NEQ " << nodep << endl);
            // -> (0=={or{for each_word{WORDSEL(lhs,#)^WORDSEL(rhs,#)}}}
            AstNode* newp = nullptr;
            for (int w = 0; w < nodep->lhsp()->widthWords(); w++) {
                AstNode* eqp = new AstXor(nodep->fileline(), newAstWordSelClone(nodep->lhsp(), w),
                                          newAstWordSelClone(nodep->rhsp(), w));
                newp = (newp == nullptr) ? eqp : (new AstOr(nodep->fileline(), newp, eqp));
            }
            if (VN_IS(nodep, Neq)) {
                newp
                    = new AstNeq(nodep->fileline(),
                                 new AstConst(nodep->fileline(), AstConst::SizedEData(), 0), newp);
            } else {
                newp = new AstEq(nodep->fileline(),
                                 new AstConst(nodep->fileline(), AstConst::SizedEData(), 0), newp);
            }
            VL_DO_DANGLING(replaceWithDelete(nodep, newp), nodep);
        }
    }
    virtual void visit(AstEq* nodep) override { visitEqNeq(nodep); }
    virtual void visit(AstNeq* nodep) override { visitEqNeq(nodep); }

    virtual void visit(AstRedOr* nodep) override {
        if (nodep->user1SetOnce()) return;  // Process once
        iterateChildren(nodep);
        if (nodep->lhsp()->isWide()) {
            UINFO(8, "    Wordize REDOR " << nodep << endl);
            // -> (0!={or{for each_word{WORDSEL(lhs,#)}}}
            AstNode* newp = nullptr;
            for (int w = 0; w < nodep->lhsp()->widthWords(); w++) {
                AstNode* eqp = newAstWordSelClone(nodep->lhsp(), w);
                newp = (newp == nullptr) ? eqp : (new AstOr(nodep->fileline(), newp, eqp));
            }
            newp = new AstNeq(nodep->fileline(),
                              new AstConst(nodep->fileline(), AstConst::SizedEData(), 0), newp);
            VL_DO_DANGLING(replaceWithDelete(nodep, newp), nodep);
        } else {
            UINFO(8, "    REDOR->EQ " << nodep << endl);
            AstNode* lhsp = nodep->lhsp()->unlinkFrBack();
            AstNode* newp = new AstNeq(nodep->fileline(),
                                       new AstConst(nodep->fileline(), AstConst::WidthedValue(),
                                                    longOrQuadWidth(nodep), 0),
                                       lhsp);
            VL_DO_DANGLING(replaceWithDelete(nodep, newp), nodep);
        }
    }
    virtual void visit(AstRedAnd* nodep) override {
        if (nodep->user1SetOnce()) return;  // Process once
        iterateChildren(nodep);
        if (nodep->lhsp()->isWide()) {
            UINFO(8, "    Wordize REDAND " << nodep << endl);
            // -> (0!={and{for each_word{WORDSEL(lhs,#)}}}
            AstNode* newp = nullptr;
            for (int w = 0; w < nodep->lhsp()->widthWords(); w++) {
                AstNode* eqp = newAstWordSelClone(nodep->lhsp(), w);
                if (w == nodep->lhsp()->widthWords() - 1) {
                    // Rather than doing a (slowish) ==##, we OR in the
                    // bits that aren't part of the mask
                    eqp = new AstOr(nodep->fileline(),
                                    new AstConst(nodep->fileline(), notWideMask(nodep->lhsp())),
                                    // Bug in cppcheck
                                    // cppcheck-suppress memleak
                                    eqp);
                }
                newp = (newp == nullptr) ? eqp : (new AstAnd(nodep->fileline(), newp, eqp));
            }
            newp = new AstEq(
                nodep->fileline(),
                new AstConst(nodep->fileline(), AstConst::SizedEData(), VL_MASK_E(VL_EDATASIZE)),
                newp);
            VL_DO_DANGLING(replaceWithDelete(nodep, newp), nodep);
        } else {
            UINFO(8, "    REDAND->EQ " << nodep << endl);
            AstNode* lhsp = nodep->lhsp()->unlinkFrBack();
            AstNode* newp = new AstEq(nodep->fileline(),
                                      new AstConst(nodep->fileline(), wordMask(lhsp)), lhsp);
            VL_DO_DANGLING(replaceWithDelete(nodep, newp), nodep);
        }
    }
    virtual void visit(AstRedXor* nodep) override {
        if (nodep->user1SetOnce()) return;  // Process once
        iterateChildren(nodep);
        if (nodep->lhsp()->isWide()) {
            UINFO(8, "    Wordize REDXOR " << nodep << endl);
            // -> (0!={redxor{for each_word{XOR(WORDSEL(lhs,#))}}}
            AstNode* newp = nullptr;
            for (int w = 0; w < nodep->lhsp()->widthWords(); w++) {
                AstNode* eqp = newAstWordSelClone(nodep->lhsp(), w);
                newp = (newp == nullptr) ? eqp : (new AstXor(nodep->fileline(), newp, eqp));
            }
            newp = new AstRedXor(nodep->fileline(), newp);
            UINFO(8, "    Wordize REDXORnew " << newp << endl);
            VL_DO_DANGLING(replaceWithDelete(nodep, newp), nodep);
        }
        // We don't reduce non-wide XORs, as its more efficient to use a temp register,
        // which the inlined function does nicely.
    }

    virtual void visit(AstNodeStmt* nodep) override {
        if (nodep->user1SetOnce()) return;  // Process once
        if (!nodep->isStatement()) {
            iterateChildren(nodep);
            return;
        }
        m_stmtp = nodep;
        iterateChildren(nodep);
        m_stmtp = nullptr;
    }
    virtual void visit(AstNodeAssign* nodep) override {
        if (nodep->user1SetOnce()) return;  // Process once
        m_stmtp = nodep;
        iterateChildren(nodep);
        bool did = false;
        if (nodep->isWide() && ((VN_IS(nodep->lhsp(), VarRef) || VN_IS(nodep->lhsp(), ArraySel)))
            && ((VN_IS(nodep->lhsp(), VarRef) || VN_IS(nodep->lhsp(), ArraySel)))
            && !AstVar::scVarRecurse(nodep->lhsp())  // Need special function for SC
            && !AstVar::scVarRecurse(nodep->rhsp())) {
            if (AstConst* rhsp = VN_CAST(nodep->rhsp(), Const)) {
                did = expandWide(nodep, rhsp);
            } else if (AstVarRef* rhsp = VN_CAST(nodep->rhsp(), VarRef)) {
                did = expandWide(nodep, rhsp);
            } else if (AstSel* rhsp = VN_CAST(nodep->rhsp(), Sel)) {
                did = expandWide(nodep, rhsp);
            } else if (AstArraySel* rhsp = VN_CAST(nodep->rhsp(), ArraySel)) {
                did = expandWide(nodep, rhsp);
            } else if (AstConcat* rhsp = VN_CAST(nodep->rhsp(), Concat)) {
                did = expandWide(nodep, rhsp);
            } else if (AstReplicate* rhsp = VN_CAST(nodep->rhsp(), Replicate)) {
                did = expandWide(nodep, rhsp);
            } else if (AstAnd* rhsp = VN_CAST(nodep->rhsp(), And)) {
                did = expandWide(nodep, rhsp);
            } else if (AstOr* rhsp = VN_CAST(nodep->rhsp(), Or)) {
                did = expandWide(nodep, rhsp);
            } else if (AstNot* rhsp = VN_CAST(nodep->rhsp(), Not)) {
                did = expandWide(nodep, rhsp);
            } else if (AstXor* rhsp = VN_CAST(nodep->rhsp(), Xor)) {
                did = expandWide(nodep, rhsp);
            } else if (AstNodeCond* rhsp = VN_CAST(nodep->rhsp(), NodeCond)) {
                did = expandWide(nodep, rhsp);
            }
        } else if (AstSel* lhsp = VN_CAST(nodep->lhsp(), Sel)) {
            did = expandLhs(nodep, lhsp);
        }
        // Cleanup common code
        if (did) VL_DO_DANGLING(nodep->unlinkFrBack()->deleteTree(), nodep);
        m_stmtp = nullptr;
    }

    //--------------------
    virtual void visit(AstVar*) override {}  // Don't hit varrefs under vars
    virtual void visit(AstNode* nodep) override { iterateChildren(nodep); }

public:
    // CONSTRUCTORS
    explicit ExpandVisitor(AstNetlist* nodep) { iterate(nodep); }
    virtual ~ExpandVisitor() override {
        V3Stats::addStat("Optimizations, expand wides", m_statWides);
        V3Stats::addStat("Optimizations, expand wide words", m_statWideWords);
        V3Stats::addStat("Optimizations, expand limited", m_statWideLimited);
    }
};

//----------------------------------------------------------------------
// Top loop

//######################################################################
// Expand class functions

void V3Expand::expandAll(AstNetlist* nodep) {
    UINFO(2, __FUNCTION__ << ": " << endl);
    { ExpandVisitor visitor(nodep); }  // Destruct before checking
    V3Global::dumpCheckGlobalTree("expand", 0, v3Global.opt.dumpTreeLevel(__FILE__) >= 3);
}
