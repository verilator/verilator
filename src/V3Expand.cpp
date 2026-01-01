// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Add temporaries, such as for expand nodes
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2004-2026 by Wilson Snyder. This program is free software; you
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

#include "V3PchAstNoMT.h"  // VL_MT_DISABLED_CODE_UNIT

#include "V3Expand.h"

#include "V3Const.h"
#include "V3Stats.h"

VL_DEFINE_DEBUG_FUNCTIONS;

//######################################################################
// Find nodes with side effects, to mark as non-expandable

class ExpandOkVisitor final : public VNVisitorConst {
    // NODE STATE
    //  AstNode::user2()        -> bool.  Is pure (along with all children)
    const VNUser2InUse m_inuser2;

    // STATE - for current visit position (use VL_RESTORER)
    // Tracks similar to AstNode::isTreePureRecurse(), but avoid O(n^2)
    // False = pure, as nodes that ExpandVisitor inserts preserve pureness
    bool m_isImpure = true;  // Currently pure

    void visit(AstNode* nodep) override {
        bool selfImpure = !nodep->isPure();
        {
            VL_RESTORER(m_isImpure);
            m_isImpure = false;
            iterateChildrenConst(nodep);
            selfImpure |= m_isImpure;
            nodep->user2(selfImpure);
        }
        m_isImpure |= selfImpure;
    }

public:
    // CONSTRUCTORS
    explicit ExpandOkVisitor(AstNetlist* nodep) { iterateConst(nodep); }
    ~ExpandOkVisitor() = default;
};

//######################################################################
// Expand state, as a visitor of each AstNode

class ExpandVisitor final : public VNVisitor {
    // NODE STATE
    //  AstNode::user1()        -> bool.  Processed
    const VNUser1InUse m_inuser1;

    // STATE - for current visit position (use VL_RESTORER)
    AstNode* m_stmtp = nullptr;  // Current statement

    // STATE - across all visitors
    AstCFunc* m_funcp = nullptr;  // Current function
    VDouble0 m_statWides;  // Statistic tracking
    VDouble0 m_statWideWords;  // Statistic tracking
    VDouble0 m_statWideLimited;  // Statistic tracking

    // STATE - for current function
    size_t m_nTmps = 0;  // Sequence numbers for temopraries

    // METHODS
    // Use state that ExpandOkVisitor calculated
    bool isImpure(AstNode* nodep) {
        const bool impure = nodep->user2();
        if (impure) UINFO(9, "      impure " << nodep);
        return impure;
    }

    bool doExpandWide(AstNode* nodep) {
        if (isImpure(nodep)) return false;
        if (nodep->widthWords() <= v3Global.opt.expandLimit()) {
            ++m_statWides;
            m_statWideWords += nodep->widthWords();
            return true;
        } else {
            ++m_statWideLimited;
            return false;
        }
    }

    static int longOrQuadWidth(AstNode* nodep) {
        return (nodep->width() + (VL_EDATASIZE - 1)) & ~(VL_EDATASIZE - 1);
    }
    static V3Number notWideMask(AstNode* nodep) {
        return V3Number{nodep, VL_EDATASIZE, ~VL_MASK_E(nodep->widthMin())};
    }
    static V3Number wordMask(AstNode* nodep) {
        if (nodep->isWide()) {
            return V3Number{nodep, VL_EDATASIZE, VL_MASK_E(nodep->widthMin())};
        } else {
            V3Number mask{nodep, longOrQuadWidth(nodep)};
            mask.setMask(nodep->widthMin());
            return mask;
        }
    }

    static void insertBefore(AstNode* placep, AstNode* newp) {
        newp->user1(1);  // Already processed, don't need to re-iterate
        placep->addHereThisAsNext(newp);
    }
    static void replaceWithDelete(AstNode* nodep, AstNode* newp) {
        newp->user1(1);  // Already processed, don't need to re-iterate
        if (newp->width() != nodep->width()) {
            UASSERT_OBJ(newp->widthMin() == nodep->widthMin(), nodep,
                        "Replacement width mismatch");
            newp->dtypeChgWidth(nodep->width(), nodep->widthMin());
        }
        nodep->replaceWith(newp);
        VL_DO_DANGLING(nodep->deleteTree(), nodep);
    }
    static AstNode* newWordAssign(AstNodeAssign* placep, int word, AstNodeExpr* lhsp,
                                  AstNodeExpr* rhsp) {
        FileLine* const fl = placep->fileline();
        return new AstAssign{fl,
                             new AstWordSel{fl, lhsp->cloneTreePure(true),
                                            new AstConst{fl, static_cast<uint32_t>(word)}},
                             rhsp};
    }
    static void addWordAssign(AstNodeAssign* placep, int word, AstNodeExpr* lhsp,
                              AstNodeExpr* rhsp) {
        insertBefore(placep, newWordAssign(placep, word, lhsp, rhsp));
    }
    static void addWordAssign(AstNodeAssign* placep, int word, AstNodeExpr* rhsp) {
        addWordAssign(placep, word, placep->lhsp(), rhsp);
    }

    AstVar* addLocalTmp(AstNode* placep, const char* namep, AstNodeExpr* valuep) {
        const std::string name = "__V"s + namep + "_"s + std::to_string(m_nTmps);
        FileLine* const flp = placep->fileline();
        AstVar* const tmpp = new AstVar{flp, VVarType::STMTTEMP, name, valuep->dtypep()};
        tmpp->funcLocal(true);
        tmpp->isInternal(true);
        tmpp->noReset(true);
        tmpp->substConstOnly(true);
        m_funcp->addVarsp(tmpp);
        insertBefore(placep, new AstAssign{flp, new AstVarRef{flp, tmpp, VAccess::WRITE}, valuep});
        return tmpp;
    }

    static void fixCloneLvalue(AstNode* nodep) {
        // In AstSel transforms, we call clone() on VarRefs that were lvalues,
        // but are now being used on the RHS of the assignment
        if (VN_IS(nodep, VarRef)) VN_AS(nodep, VarRef)->access(VAccess::READ);
        // Iterate
        if (AstNode* const refp = nodep->op1p()) fixCloneLvalue(refp);
        if (AstNode* const refp = nodep->op2p()) fixCloneLvalue(refp);
        if (AstNode* const refp = nodep->op3p()) fixCloneLvalue(refp);
        if (AstNode* const refp = nodep->op4p()) fixCloneLvalue(refp);
    }

    static AstNodeExpr* newAstWordSelClone(AstNodeExpr* nodep, int word) {
        // Get the specified word number from a wide array
        // Or, if it's a long/quad, do appropriate conversion to wide
        // Concat may pass negative word numbers, that means it wants a zero
        FileLine* const fl = nodep->fileline();
        if (nodep->isWide() && word >= 0 && word < nodep->widthWords()) {
            return new AstWordSel{fl, nodep->cloneTreePure(true),
                                  new AstConst{fl, static_cast<uint32_t>(word)}};
        } else if (nodep->isQuad() && word == 0) {
            AstNodeExpr* const quadfromp = nodep->cloneTreePure(true);
            quadfromp->dtypeSetBitUnsized(VL_QUADSIZE, quadfromp->widthMin(), VSigning::UNSIGNED);
            return new AstCCast{fl, quadfromp, VL_EDATASIZE};
        } else if (nodep->isQuad() && word == 1) {
            AstNodeExpr* const quadfromp = nodep->cloneTreePure(true);
            quadfromp->dtypeSetBitUnsized(VL_QUADSIZE, quadfromp->widthMin(), VSigning::UNSIGNED);
            return new AstCCast{
                fl, new AstShiftR{fl, quadfromp, new AstConst{fl, VL_EDATASIZE}, VL_EDATASIZE},
                VL_EDATASIZE};
        } else if (!nodep->isWide() && !nodep->isQuad() && word == 0) {
            return nodep->cloneTreePure(true);
        } else {  // Out of bounds
            return new AstConst{fl, 0};
        }
    }

    static AstNodeExpr* newWordGrabShift(FileLine* fl, int word, AstNodeExpr* lhsp, int shift) {
        // Extract the expression to grab the value for the specified word, if it's the shift
        // of shift bits from lhsp
        AstNodeExpr* newp;
        // Negative word numbers requested for lhs when it's "before" what we want.
        // We get a 0 then.
        const int othword = word - shift / VL_EDATASIZE;
        AstNodeExpr* const llowp = newAstWordSelClone(lhsp, othword);
        if (const int loffset = VL_BITBIT_E(shift)) {
            AstNodeExpr* const lhip = newAstWordSelClone(lhsp, othword - 1);
            const int nbitsonright = VL_EDATASIZE - loffset;  // bits that end up in lword
            newp = new AstOr{
                fl,
                new AstAnd{fl, new AstConst{fl, AstConst::SizedEData{}, VL_MASK_E(loffset)},
                           new AstShiftR{fl, lhip,
                                         new AstConst{fl, static_cast<uint32_t>(nbitsonright)},
                                         VL_EDATASIZE}},
                new AstAnd{fl,
                           new AstConst{fl, AstConst::SizedEData{},
                                        static_cast<uint32_t>(~VL_MASK_E(loffset))},
                           new AstShiftL{fl, llowp,
                                         new AstConst{fl, static_cast<uint32_t>(loffset)},
                                         VL_EDATASIZE}}};
            newp = V3Const::constifyEditCpp(newp);
        } else {
            newp = llowp;
        }
        return newp;
    }

    // Return expression indexing the word that contains 'lsbp' + the given word offset
    static AstNodeExpr* newWordIndex(AstNodeExpr* lsbp, uint32_t wordOffset = 0) {
        // This is indexing a WordSel, so a 32 bit constants are fine
        FileLine* const flp = lsbp->fileline();
        if (const AstConst* constp = VN_CAST(lsbp, Const)) {
            return new AstConst{flp, wordOffset + VL_BITWORD_E(constp->toUInt())};
        }

        if (lsbp->backp()) lsbp = lsbp->cloneTreePure(false);
        AstNodeExpr* const wwl2p = new AstConst{flp, VL_EDATASIZE_LOG2};  // Word width log 2
        AstNodeExpr* indexp = new AstShiftR{flp, lsbp, wwl2p, VL_EDATASIZE};
        if (wordOffset) indexp = new AstAdd{flp, new AstConst{flp, wordOffset}, indexp};
        return indexp;
    }

    // Return word of fromp that contains word indexp + the given word offset.
    static AstNodeExpr* newWordSelWord(FileLine* flp, AstNodeExpr* fromp, AstNodeExpr* indexp,
                                       uint32_t wordOffset = 0) {
        UASSERT_OBJ(fromp->isWide(), fromp, "Only need AstWordSel on wide from's");

        if (const AstConst* const constp = VN_CAST(indexp, Const)) {
            indexp = nullptr;
            wordOffset += constp->toUInt();
        }

        // e.g. "logic [95:0] var[0]; logic [0] sel; out = var[sel];"
        // Squash before C++ to avoid getting a C++ compiler warning
        // (even though code would be unreachable as presumably a
        // AstCond is protecting above this node.
        if (wordOffset >= static_cast<uint32_t>(fromp->widthWords())) {
            return new AstConst{flp, AstConst::SizedEData{}, 0};
        }

        if (fromp->backp()) fromp = fromp->cloneTreePure(false);

        // If indexp was constant, just use it
        if (!indexp) return new AstWordSel{flp, fromp, new AstConst{flp, wordOffset}};

        // Otherwise compute at runtime
        if (indexp->backp()) indexp = indexp->cloneTreePure(false);
        if (wordOffset) indexp = new AstAdd{flp, new AstConst{flp, wordOffset}, indexp};
        return new AstWordSel{flp, fromp, indexp};
    }

    // Return word of fromp that contains bit lsbp + the given word offset.
    static AstNodeExpr* newWordSelBit(FileLine* flp, AstNodeExpr* fromp, AstNodeExpr* lsbp,
                                      uint32_t wordOffset = 0) {
        AstNodeExpr* const indexp = newWordIndex(lsbp, wordOffset);
        AstNodeExpr* const wordSelp = newWordSelWord(flp, fromp, indexp);
        if (!indexp->backp()) VL_DO_DANGLING(indexp->deleteTree(), indexp);
        return wordSelp;
    }

    static AstNodeExpr* newSelBitBit(AstNodeExpr* lsbp) {
        // Return equation to get the VL_BITBIT of a constant or non-constant
        FileLine* const fl = lsbp->fileline();
        if (VN_IS(lsbp, Const)) {
            return new AstConst{fl, VL_BITBIT_E(VN_AS(lsbp, Const)->toUInt())};
        } else {
            return new AstAnd{fl, new AstConst{fl, VL_EDATASIZE - 1}, lsbp->cloneTreePure(true)};
        }
    }

    //====================

    bool expandWide(AstNodeAssign* nodep, AstConst* rhsp) {
        UINFO(8, "    Wordize ASSIGN(CONST) " << nodep);
        if (!doExpandWide(nodep)) return false;
        // -> {for each_word{ ASSIGN(WORDSEL(wide,#),WORDSEL(CONST,#))}}
        if (rhsp->num().isFourState()) {
            rhsp->v3warn(E_UNSUPPORTED,  // LCOV_EXCL_LINE  // impossible?
                         "Unsupported: 4-state numbers in this context");
        }
        FileLine* const fl = nodep->fileline();
        for (int w = 0; w < nodep->widthWords(); ++w) {
            addWordAssign(nodep, w,
                          new AstConst{fl, AstConst::SizedEData{}, rhsp->num().edataWord(w)});
        }
        return true;
    }
    //-------- Uniops
    bool expandWide(AstNodeAssign* nodep, AstVarRef* rhsp) {
        UINFO(8, "    Wordize ASSIGN(VARREF) " << nodep);
        if (!doExpandWide(nodep)) return false;
        for (int w = 0; w < nodep->widthWords(); ++w) {
            addWordAssign(nodep, w, newAstWordSelClone(rhsp, w));
        }
        return true;
    }
    bool expandWide(AstNodeAssign* nodep, AstArraySel* rhsp) {
        UINFO(8, "    Wordize ASSIGN(ARRAYSEL) " << nodep);
        UASSERT_OBJ(!VN_IS(nodep->dtypep()->skipRefp(), UnpackArrayDType), nodep,
                    "ArraySel with unpacked arrays should have been removed in V3Slice");
        if (!doExpandWide(nodep)) return false;
        for (int w = 0; w < nodep->widthWords(); ++w) {
            addWordAssign(nodep, w, newAstWordSelClone(rhsp, w));
        }
        return true;
    }
    bool expandWide(AstNodeAssign* nodep, AstNot* rhsp) {
        UINFO(8, "    Wordize ASSIGN(NOT) " << nodep);
        // -> {for each_word{ ASSIGN(WORDSEL(wide,#),NOT(WORDSEL(lhs,#))) }}
        if (!doExpandWide(nodep)) return false;
        FileLine* const fl = rhsp->fileline();
        for (int w = 0; w < nodep->widthWords(); ++w) {
            addWordAssign(nodep, w, new AstNot{fl, newAstWordSelClone(rhsp->lhsp(), w)});
        }
        return true;
    }
    //-------- Biops
    bool expandWide(AstNodeAssign* nodep, AstAnd* rhsp) {
        UINFO(8, "    Wordize ASSIGN(AND) " << nodep);
        if (!doExpandWide(nodep)) return false;
        FileLine* const fl = nodep->fileline();
        for (int w = 0; w < nodep->widthWords(); ++w) {
            addWordAssign(nodep, w,
                          new AstAnd{fl, newAstWordSelClone(rhsp->lhsp(), w),
                                     newAstWordSelClone(rhsp->rhsp(), w)});
        }
        return true;
    }
    bool expandWide(AstNodeAssign* nodep, AstOr* rhsp) {
        UINFO(8, "    Wordize ASSIGN(OR) " << nodep);
        if (!doExpandWide(nodep)) return false;
        FileLine* const fl = nodep->fileline();
        for (int w = 0; w < nodep->widthWords(); ++w) {
            addWordAssign(nodep, w,
                          new AstOr{fl, newAstWordSelClone(rhsp->lhsp(), w),
                                    newAstWordSelClone(rhsp->rhsp(), w)});
        }
        return true;
    }
    bool expandWide(AstNodeAssign* nodep, AstXor* rhsp) {
        UINFO(8, "    Wordize ASSIGN(XOR) " << nodep);
        if (!doExpandWide(nodep)) return false;
        FileLine* const fl = nodep->fileline();
        for (int w = 0; w < nodep->widthWords(); ++w) {
            addWordAssign(nodep, w,
                          new AstXor{fl, newAstWordSelClone(rhsp->lhsp(), w),
                                     newAstWordSelClone(rhsp->rhsp(), w)});
        }
        return true;
    }
    //-------- Triops
    bool expandWide(AstNodeAssign* nodep, AstCond* rhsp) {
        UINFO(8, "    Wordize ASSIGN(COND) " << nodep);
        if (!doExpandWide(nodep)) return false;
        FileLine* const fl = nodep->fileline();
        for (int w = 0; w < nodep->widthWords(); ++w) {
            addWordAssign(nodep, w,
                          new AstCond{fl, rhsp->condp()->cloneTreePure(true),
                                      newAstWordSelClone(rhsp->thenp(), w),
                                      newAstWordSelClone(rhsp->elsep(), w)});
        }
        return true;
    }

    // VISITORS
    void visit(AstCFunc* nodep) override {
        VL_RESTORER(m_funcp);
        VL_RESTORER(m_nTmps);
        m_funcp = nodep;
        m_nTmps = 0;
        const VDouble0 statWidesBefore = m_statWides;
        iterateChildren(nodep);

        // Constant fold here if anything was expanded, as Ast size can likely be reduced
        if (v3Global.opt.fConstEager() && m_statWides != statWidesBefore) {
            AstNode* const editedp = V3Const::constifyEditCpp(nodep);
            UASSERT_OBJ(editedp == nodep, editedp, "Should not have replaced CFunc");
        }
    }

    void visit(AstExtend* nodep) override {
        if (nodep->user1SetOnce()) return;  // Process once
        iterateChildren(nodep);
        if (nodep->isWide()) {
            // See under ASSIGN(EXTEND)
        } else {
            if (isImpure(nodep)) return;
            AstNodeExpr* const lhsp = nodep->lhsp()->unlinkFrBack();
            AstNodeExpr* newp = lhsp;
            if (nodep->isQuad()) {
                if (lhsp->isQuad()) {
                    lhsp->dtypeFrom(nodep);  // Just mark it, else nop
                } else if (lhsp->isWide()) {
                    nodep->v3fatalSrc("extending larger thing into smaller?");
                } else {
                    UINFO(8, "    EXTEND(q<-l) " << nodep);
                    newp = new AstCCast{nodep->fileline(), lhsp, nodep};
                }
            } else {  // Long
                UASSERT_OBJ(!(lhsp->isQuad() || lhsp->isWide()), nodep,
                            "extending larger thing into smaller?");
                lhsp->dtypeFrom(nodep);  // Just mark it, else nop
            }
            VL_DO_DANGLING(replaceWithDelete(nodep, newp), nodep);
        }
    }
    bool expandWide(AstNodeAssign* nodep, AstExtend* rhsp) {
        UINFO(8, "    Wordize ASSIGN(EXTEND) " << nodep);
        if (!doExpandWide(nodep)) return false;
        AstNodeExpr* const rlhsp = rhsp->lhsp();
        for (int w = 0; w < rlhsp->widthWords(); ++w) {
            addWordAssign(nodep, w, newAstWordSelClone(rlhsp, w));
        }
        for (int w = rlhsp->widthWords(); w < nodep->widthWords(); ++w) {
            addWordAssign(nodep, w, new AstConst{nodep->fileline(), AstConst::SizedEData{}, 0});
        }
        return true;
    }

    void visit(AstSel* nodep) override {
        if (nodep->user1SetOnce()) return;  // Process once
        iterateChildren(nodep);
        // Remember, Sel's may have non-integer rhs, so need to optimize for that!
        UASSERT_OBJ(nodep->widthMin() == nodep->widthConst(), nodep, "Width mismatch");
        if (VN_IS(nodep->backp(), NodeAssign)
            && nodep == VN_AS(nodep->backp(), NodeAssign)->lhsp()) {
            // Sel is an LHS assignment select
        } else if (nodep->isWide()) {
            // See under ASSIGN(WIDE)
        } else if (nodep->fromp()->isWide()) {
            if (isImpure(nodep)) return;
            UINFO(8, "    SEL(wide) " << nodep);
            UASSERT_OBJ(nodep->widthConst() <= 64, nodep, "Inconsistent width");
            // Selection amounts
            // Check for constant shifts & save some constification work later.
            // Grab lowest bit(s)
            FileLine* const nfl = nodep->fileline();
            FileLine* const lfl = nodep->lsbp()->fileline();
            FileLine* const ffl = nodep->fromp()->fileline();
            AstNodeExpr* lowwordp = newWordSelBit(ffl, nodep->fromp(), nodep->lsbp());
            if (nodep->isQuad() && !lowwordp->isQuad()) {
                lowwordp = new AstCCast{nfl, lowwordp, nodep};
            }
            AstNodeExpr* const lowp
                = new AstShiftR{nfl, lowwordp, newSelBitBit(nodep->lsbp()), nodep->width()};
            // If > 1 bit, we might be crossing the word boundary
            AstNodeExpr* midp = nullptr;
            if (nodep->widthConst() > 1) {
                const uint32_t midMsbOffset
                    = std::min<uint32_t>(nodep->widthConst(), VL_EDATASIZE) - 1;
                AstNodeExpr* const midMsbp = new AstAdd{lfl, new AstConst{lfl, midMsbOffset},
                                                        nodep->lsbp()->cloneTreePure(true)};
                AstNodeExpr* midwordp = newWordSelBit(ffl, nodep->fromp(), midMsbp, 0);
                if (!midMsbp->backp()) VL_DO_DANGLING(midMsbp->deleteTree(), midMsbp);
                if (nodep->isQuad() && !midwordp->isQuad()) {
                    midwordp = new AstCCast{nfl, midwordp, nodep};
                }
                AstNodeExpr* const midshiftp = new AstSub{lfl, new AstConst{lfl, VL_EDATASIZE},
                                                          newSelBitBit(nodep->lsbp())};
                // If we're selecting bit zero, then all 32 bits in the mid word
                // get shifted << by 32 bits, so ignore them.
                const V3Number zero{nodep, longOrQuadWidth(nodep)};
                midp = new AstCond{
                    nfl,
                    // lsb % VL_EDATASIZE == 0 ?
                    new AstEq{nfl, new AstConst{nfl, 0}, newSelBitBit(nodep->lsbp())},
                    // 0 :
                    new AstConst{nfl, zero},
                    //  midword >> (VL_EDATASIZE - (lbs % VL_EDATASIZE))
                    new AstShiftL{nfl, midwordp, midshiftp, nodep->width()}};
            }
            // If > 32 bits, we might be crossing the second word boundary
            AstNodeExpr* hip = nullptr;
            if (nodep->widthConst() > VL_EDATASIZE) {
                const uint32_t hiMsbOffset = nodep->widthConst() - 1;
                AstNodeExpr* const hiMsbp = new AstAdd{lfl, new AstConst{lfl, hiMsbOffset},
                                                       nodep->lsbp()->cloneTreePure(true)};
                AstNodeExpr* hiwordp = newWordSelBit(ffl, nodep->fromp(), hiMsbp);
                if (!hiMsbp->backp()) VL_DO_DANGLING(hiMsbp->deleteTree(), hiMsbp);
                if (nodep->isQuad() && !hiwordp->isQuad()) {
                    hiwordp = new AstCCast{nfl, hiwordp, nodep};
                }
                AstNodeExpr* const hishiftp = new AstCond{
                    nfl,
                    // lsb % VL_EDATASIZE == 0 ?
                    new AstEq{nfl, new AstConst{nfl, 0}, newSelBitBit(nodep->lsbp())},
                    // VL_EDATASIZE :
                    new AstConst{lfl, VL_EDATASIZE},
                    // 64 - (lbs % VL_EDATASIZE)
                    new AstSub{lfl, new AstConst{lfl, 64}, newSelBitBit(nodep->lsbp())}};
                hip = new AstShiftL{nfl, hiwordp, hishiftp, nodep->width()};
            }

            AstNodeExpr* newp = lowp;
            if (midp) newp = new AstOr{nfl, midp, newp};
            if (hip) newp = new AstOr{nfl, hip, newp};
            newp->dtypeFrom(nodep);
            VL_DO_DANGLING(replaceWithDelete(nodep, newp), nodep);
        } else {  // Long/Quad from Long/Quad
            // No isImpure() check - can handle side effects in below
            UINFO(8, "    SEL->SHIFT " << nodep);
            FileLine* const fl = nodep->fileline();
            AstNodeExpr* fromp = nodep->fromp()->unlinkFrBack();
            AstNodeExpr* const lsbp = nodep->lsbp()->unlinkFrBack();
            if (nodep->isQuad() && !fromp->isQuad()) fromp = new AstCCast{fl, fromp, nodep};
            // {large}>>32 requires 64-bit shift operation; then cast
            AstNodeExpr* newp = new AstShiftR{fl, fromp, lsbp, fromp->width()};
            newp->dtypeFrom(fromp);
            if (!nodep->isQuad() && fromp->isQuad()) newp = new AstCCast{fl, newp, nodep};
            newp->dtypeFrom(nodep);
            VL_DO_DANGLING(replaceWithDelete(nodep, newp), nodep);
        }
    }

    bool expandWide(AstNodeAssign* nodep, AstSel* rhsp) {
        UASSERT_OBJ(nodep->widthMin() == rhsp->widthConst(), nodep, "Width mismatch");
        if (!doExpandWide(nodep)) return false;

        // Simplify the index, in case it becomes a constant
        V3Const::constifyEditCpp(rhsp->lsbp());

        // If it's a constant select and aligned, we can just copy the words
        if (const AstConst* const lsbConstp = VN_CAST(rhsp->lsbp(), Const)) {
            const uint32_t lsb = lsbConstp->toUInt();
            if (VL_BITBIT_E(lsb) == 0) {
                UINFO(8, "    Wordize ASSIGN(SEL,align) " << nodep);
                const uint32_t word = VL_BITWORD_E(lsb);
                for (int w = 0; w < nodep->widthWords(); ++w) {
                    addWordAssign(nodep, w, newAstWordSelClone(rhsp->fromp(), w + word));
                }
                return true;
            }
        }

        UINFO(8, "    Wordize ASSIGN(EXTRACT,misalign) " << nodep);
        FileLine* const flp = rhsp->fileline();

        // Use fresh set of temporaries
        ++m_nTmps;

        // Compute word index of LSB, store to temporary if not constant
        AstNodeExpr* const wordLsbp = rhsp->lsbp()->cloneTreePure(false);
        AstNodeExpr* wordIdxp = newWordIndex(wordLsbp);
        if (!wordLsbp->backp()) VL_DO_DANGLING(wordLsbp->deleteTree(), wordLsbp);
        wordIdxp = V3Const::constifyEditCpp(wordIdxp);
        if (!VN_IS(wordIdxp, Const)) {
            AstVar* const tmpp = addLocalTmp(nodep, "ExpandSel_WordIdx", wordIdxp);
            wordIdxp = new AstVarRef{flp, tmpp, VAccess::READ};
        }

        // Compute shift amounts and mask, store to temporaries if not constants
        AstNodeExpr* loShftp = nullptr;
        AstNodeExpr* hiShftp = nullptr;
        AstNodeExpr* hiMaskp = nullptr;
        if (const AstConst* const lsbConstp = VN_CAST(rhsp->lsbp(), Const)) {
            const uint32_t bitOffset = VL_BITBIT_E(lsbConstp->toUInt());
            // Must be unaligned, otherwise we would have handled it above
            UASSERT_OBJ(bitOffset, nodep, "Missed aligned wide select");
            loShftp = new AstConst{flp, bitOffset};
            hiShftp = new AstConst{flp, VL_EDATASIZE - bitOffset};
            hiMaskp = nullptr;
        } else {
            // Compute Low word shift amount: bottom bits of lsb index
            AstNodeExpr* const lsbp = rhsp->lsbp()->cloneTreePure(false);
            loShftp = new AstAnd{flp, new AstConst{flp, VL_SIZEBITS_E}, lsbp};
            AstVar* const loTmpp = addLocalTmp(nodep, "ExpandSel_LoShift", loShftp);
            loShftp = new AstVarRef{flp, loTmpp, VAccess::READ};

            // Compute if aligned: Low word shift amount is 0
            AstNodeExpr* const zerop = new AstConst{flp, 0};
            AstNodeExpr* alignedp = new AstEq{flp, zerop, loShftp->cloneTreePure(false)};
            AstVar* const alignedTmpp = addLocalTmp(nodep, "ExpandSel_Aligned", alignedp);
            alignedp = new AstVarRef{flp, alignedTmpp, VAccess::READ};

            // Computed High word shift amount: 0 if aligned else VL_EDATASIZE - Low word shift
            AstNodeExpr* const edsp = new AstConst{flp, VL_EDATASIZE};
            AstNodeExpr* const subp = new AstSub{flp, edsp, loShftp->cloneTreePure(false)};
            hiShftp = new AstCond{flp, alignedp, new AstConst{flp, 0}, subp};
            AstVar* const hiTmpp = addLocalTmp(nodep, "ExpandSel_HiShift", hiShftp);
            hiShftp = new AstVarRef{flp, hiTmpp, VAccess::READ};

            // Compute the High word mask: 0 if aligned, ones otherwise
            hiMaskp = new AstCond{flp, alignedp->cloneTreePure(false),
                                  new AstConst{flp, AstConst::SizedEData{}, 0},
                                  new AstConst{flp, AstConst::SizedEData{}, -1ULL}};
            AstVar* const maskTmpp = addLocalTmp(nodep, "ExpandSel_HiMask", hiMaskp);
            hiMaskp = new AstVarRef{flp, maskTmpp, VAccess::READ};
        }

        // Create each word of the selected result
        AstNodeExpr* const fromp = rhsp->fromp();
        const int selWords = nodep->widthWords();
        for (int w = 0; w < selWords; ++w) {
            // Grab bits from word 'VL_BITWORD_E(lsb) + w'
            AstNodeExpr* const loWordp = newWordSelWord(fromp->fileline(), fromp, wordIdxp, w);
            AstNodeExpr* const loShftClonep = loShftp->cloneTreePure(false);
            AstNodeExpr* const lop = new AstShiftR{flp, loWordp, loShftClonep, VL_EDATASIZE};
            // Grab bits from word 'VL_BITWORD_E(lsb) + w + 1'
            AstNodeExpr* hiWordp = newWordSelWord(fromp->fileline(), fromp, wordIdxp, w + 1);
            // For the last word of the result, avoid an OOB access when the Sel is not OOB
            if (w == selWords - 1) {
                const uint32_t max = fromp->widthWords() - w - 1;
                AstNodeExpr* const maxp = new AstConst{flp, max};
                AstNodeExpr* const condp = new AstGte{flp, wordIdxp->cloneTreePure(false), maxp};
                AstNodeExpr* const zerop = new AstConst{flp, AstConst::SizedEData{}, 0};
                hiWordp = new AstCond{flp, condp, zerop, hiWordp};
            }
            AstNodeExpr* const hiShftClonep = hiShftp->cloneTreePure(false);
            AstNodeExpr* const hiPartp = new AstShiftL{flp, hiWordp, hiShftClonep, VL_EDATASIZE};
            AstNodeExpr* const hip
                = hiMaskp ? new AstAnd{flp, hiPartp, hiMaskp->cloneTreePure(false)} : hiPartp;
            // Combine them
            addWordAssign(nodep, w, new AstOr{nodep->fileline(), hip, lop});
        }

        // Delete parts not captured during construction
        if (!wordIdxp->backp()) VL_DO_DANGLING(wordIdxp->deleteTree(), wordIdxp);
        if (!loShftp->backp()) VL_DO_DANGLING(loShftp->deleteTree(), loShftp);
        if (!hiShftp->backp()) VL_DO_DANGLING(hiShftp->deleteTree(), hiShftp);
        if (hiMaskp && !hiMaskp->backp()) VL_DO_DANGLING(hiMaskp->deleteTree(), hiMaskp);

        return true;
    }

    bool expandLhs(AstNodeAssign* nodep, AstSel* lhsp) {
        // Possibilities
        //      destp: wide or narrow
        //      rhsp:  wide (destp must be wide), narrow, or 1 bit wide
        //      rhsp:  may be allones and can remove AND NOT gate
        //      lsbp:  constant or variable
        // Yuk.
        if (isImpure(nodep)) return false;
        FileLine* const nfl = nodep->fileline();
        FileLine* const lfl = lhsp->fileline();
        const bool destwide = lhsp->fromp()->isWide();
        const bool ones = nodep->rhsp()->isAllOnesV();
        if (VN_IS(lhsp->lsbp(), Const)) {
            // The code should work without this constant test, but it won't
            // constify as nicely as we'd like.
            AstNodeExpr* rhsp = nodep->rhsp()->unlinkFrBack();
            AstNodeExpr* const destp = lhsp->fromp()->unlinkFrBack();
            const int lsb = lhsp->lsbConst();
            const int msb = lhsp->msbConst();
            V3Number maskset{nodep, destp->widthMin()};
            maskset.setMask(msb + 1 - lsb, lsb);
            V3Number maskold{nodep, destp->widthMin()};
            maskold.opNot(maskset);
            if (destwide) {
                UINFO(8, "    ASSIGNSEL(const,wide) " << nodep);
                for (int w = 0; w < destp->widthWords(); ++w) {
                    if (w >= VL_BITWORD_E(lsb) && w <= VL_BITWORD_E(msb)) {
                        // else we would just be setting it to the same exact value
                        AstNodeExpr* oldvalp = newAstWordSelClone(destp, w);
                        fixCloneLvalue(oldvalp);
                        if (!ones) {
                            oldvalp = new AstAnd{
                                lfl,
                                new AstConst{lfl, AstConst::SizedEData{}, maskold.edataWord(w)},
                                oldvalp};
                        }

                        // Appropriate word of new value to insert:
                        AstNodeExpr* newp = newWordGrabShift(lfl, w, rhsp, lsb);

                        // Apply cleaning at the top word of the destination
                        // (no cleaning to do if dst's width is a whole number
                        // of words).
                        if (w == destp->widthWords() - 1 && VL_BITBIT_E(destp->widthMin()) != 0) {
                            V3Number cleanmask{nodep, VL_EDATASIZE};
                            cleanmask.setMask(VL_BITBIT_E(destp->widthMin()));
                            newp = new AstAnd{lfl, newp, new AstConst{lfl, cleanmask}};
                        }
                        AstNodeExpr* const orp
                            = V3Const::constifyEditCpp(new AstOr{lfl, oldvalp, newp});
                        addWordAssign(nodep, w, destp, orp);
                    }
                }
                VL_DO_DANGLING(rhsp->deleteTree(), rhsp);
                VL_DO_DANGLING(destp->deleteTree(), destp);
            } else {
                UINFO(8, "    ASSIGNSEL(const,narrow) " << nodep);
                if (destp->isQuad() && !rhsp->isQuad()) rhsp = new AstCCast{nfl, rhsp, nodep};
                AstNodeExpr* oldvalp = destp->cloneTreePure(true);
                fixCloneLvalue(oldvalp);
                if (!ones) oldvalp = new AstAnd{lfl, new AstConst{lfl, maskold}, oldvalp};

                // The bit-select can refer to bits outside the width of nodep
                // which we aren't allowed to assign to.  This is a mask of the
                // valid range of nodep which we apply to the new shifted RHS.
                V3Number cleanmask{nodep, destp->widthMin()};
                cleanmask.setMask(destp->widthMin());
                AstNodeExpr* const shifted = new AstShiftL{
                    lfl, rhsp, new AstConst{lfl, static_cast<uint32_t>(lsb)}, destp->width()};
                AstNodeExpr* const cleaned
                    = new AstAnd{lfl, shifted, new AstConst{lfl, cleanmask}};
                AstNodeExpr* const orp
                    = V3Const::constifyEditCpp(new AstOr{lfl, oldvalp, cleaned});
                insertBefore(nodep, new AstAssign{nfl, destp, orp});
            }
            return true;
        } else {  // non-const select offset
            if (destwide && lhsp->widthConst() == 1) {
                UINFO(8, "    ASSIGNSEL(varlsb,wide,1bit) " << nodep);
                AstNodeExpr* const rhsp = nodep->rhsp()->unlinkFrBack();
                AstNodeExpr* const destp = lhsp->fromp()->unlinkFrBack();
                AstNodeExpr* oldvalp
                    = newWordSelBit(lfl, destp->cloneTreePure(false), lhsp->lsbp());
                fixCloneLvalue(oldvalp);
                if (!ones) {
                    oldvalp = new AstAnd{
                        lfl,
                        new AstNot{
                            lfl, new AstShiftL{lfl, new AstConst{nfl, 1},
                                               // newSelBitBit may exceed the MSB of this variable.
                                               // That's ok as we'd just AND with a larger value,
                                               // but oldval would clip the upper bits to sanity
                                               newSelBitBit(lhsp->lsbp()), VL_EDATASIZE}},
                        oldvalp};
                }
                // Restrict the shift amount to 0-31, see bug804.
                AstNodeExpr* const shiftp = new AstAnd{nfl, lhsp->lsbp()->cloneTreePure(true),
                                                       new AstConst{nfl, VL_EDATASIZE - 1}};
                AstNode* const newp = new AstAssign{
                    nfl, newWordSelBit(nfl, destp, lhsp->lsbp()),
                    new AstOr{lfl, oldvalp, new AstShiftL{lfl, rhsp, shiftp, VL_EDATASIZE}}};
                insertBefore(nodep, newp);
                return true;
            } else if (destwide) {
                UINFO(8, "    ASSIGNSEL(varlsb,wide) -- NoOp -- " << nodep);
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
                UINFO(8, "    ASSIGNSEL(varlsb,narrow) " << nodep);
                // nodep->dumpTree("-  old: ");
                AstNodeExpr* rhsp = nodep->rhsp()->unlinkFrBack();
                AstNodeExpr* const destp = lhsp->fromp()->unlinkFrBack();
                AstNodeExpr* oldvalp = destp->cloneTreePure(true);
                fixCloneLvalue(oldvalp);

                V3Number maskwidth{nodep, destp->widthMin()};
                maskwidth.setMask(lhsp->widthConst());

                if (destp->isQuad() && !rhsp->isQuad()) rhsp = new AstCCast{nfl, rhsp, nodep};
                if (!ones) {
                    oldvalp = new AstAnd{
                        lfl,
                        new AstNot{lfl, new AstShiftL{lfl, new AstConst{nfl, maskwidth},
                                                      lhsp->lsbp()->cloneTreePure(true),
                                                      destp->width()}},
                        oldvalp};
                }
                AstNodeExpr* newp
                    = new AstShiftL{lfl, rhsp, lhsp->lsbp()->cloneTreePure(true), destp->width()};
                // Apply cleaning to the new value being inserted.  Mask is
                // slightly wider than necessary to avoid an AND with all ones
                // being optimized out.  No need to clean if destp is
                // quad-sized as there are no extra bits to contaminate
                if (destp->widthMin() != 64) {
                    V3Number cleanmask{nodep, destp->widthMin() + 1};
                    cleanmask.setMask(destp->widthMin());
                    newp = new AstAnd{lfl, newp, new AstConst{lfl, cleanmask}};
                }

                insertBefore(nodep, new AstAssign{nfl, destp, new AstOr{lfl, oldvalp, newp}});
                return true;
            }
        }
    }

    void visit(AstConcat* nodep) override {
        if (nodep->user1SetOnce()) return;  // Process once
        iterateChildren(nodep);
        if (nodep->isWide()) {
            // See under ASSIGN(WIDE)
        } else {
            // No isImpure() check - can handle side effects in below
            UINFO(8, "    CONCAT " << nodep);
            FileLine* const fl = nodep->fileline();
            AstNodeExpr* lhsp = nodep->lhsp()->unlinkFrBack();
            AstNodeExpr* rhsp = nodep->rhsp()->unlinkFrBack();
            const uint32_t rhsshift = rhsp->widthMin();
            if (nodep->isQuad() && !lhsp->isQuad()) lhsp = new AstCCast{fl, lhsp, nodep};
            if (nodep->isQuad() && !rhsp->isQuad()) rhsp = new AstCCast{fl, rhsp, nodep};
            AstNodeExpr* const newp = new AstOr{
                fl, new AstShiftL{fl, lhsp, new AstConst{fl, rhsshift}, nodep->width()}, rhsp};
            newp->dtypeFrom(nodep);  // Unsigned
            VL_DO_DANGLING(replaceWithDelete(nodep, newp), nodep);
        }
    }
    bool expandWide(AstNodeAssign* nodep, AstConcat* rhsp) {
        UINFO(8, "    Wordize ASSIGN(CONCAT) " << nodep);
        if (!doExpandWide(rhsp)) return false;
        FileLine* const fl = rhsp->fileline();
        // Lhs or Rhs may be word, long, or quad.
        // newAstWordSelClone nicely abstracts the difference.
        const int rhsshift = rhsp->rhsp()->widthMin();
        // Sometimes doing the words backwards is preferable.
        // When we have x={x,foo} backwards is better, when x={foo,x} forward is better
        // However V3Subst tends to rip this up, so not worth optimizing now.
        for (int w = 0; w < rhsp->widthWords(); ++w) {
            addWordAssign(nodep, w,
                          new AstOr{fl, newWordGrabShift(fl, w, rhsp->lhsp(), rhsshift),
                                    newAstWordSelClone(rhsp->rhsp(), w)});
        }
        return true;
    }

    void visit(AstReplicate* nodep) override {
        if (nodep->user1SetOnce()) return;  // Process once
        iterateChildren(nodep);
        if (nodep->isWide()) {
            // See under ASSIGN(WIDE)
        } else {
            if (isImpure(nodep)) return;
            FileLine* const fl = nodep->fileline();
            AstNodeExpr* lhsp = nodep->srcp()->unlinkFrBack();
            AstNodeExpr* newp;
            const int lhswidth = lhsp->widthMin();
            if (lhswidth == 1) {
                UINFO(8, "    REPLICATE(w1) " << nodep);
                newp = new AstNegate{fl, lhsp};
            } else {
                UINFO(8, "    REPLICATE " << nodep);
                const AstConst* const constp = VN_AS(nodep->countp(), Const);
                UASSERT_OBJ(constp, nodep,
                            "Replication value isn't a constant.  Checked earlier!");
                const uint32_t times = constp->toUInt();
                if (nodep->isQuad() && !lhsp->isQuad()) lhsp = new AstCCast{fl, lhsp, nodep};
                newp = lhsp->cloneTreePure(true);
                for (unsigned repnum = 1; repnum < times; repnum++) {
                    const int rhsshift = repnum * lhswidth;
                    newp = new AstOr{
                        fl,
                        new AstShiftL{fl, lhsp->cloneTreePure(true),
                                      new AstConst{fl, static_cast<uint32_t>(rhsshift)},
                                      nodep->width()},
                        newp};
                    newp->dtypeFrom(nodep);  // Unsigned
                }
                VL_DO_DANGLING(lhsp->deleteTree(), lhsp);  // Never used
            }
            newp->dtypeFrom(nodep);  // Unsigned
            VL_DO_DANGLING(replaceWithDelete(nodep, newp), nodep);
        }
    }
    bool expandWide(AstNodeAssign* nodep, AstReplicate* rhsp) {
        UINFO(8, "    Wordize ASSIGN(REPLICATE) " << nodep);
        if (!doExpandWide(rhsp)) return false;
        FileLine* const fl = nodep->fileline();
        AstNodeExpr* const lhsp = rhsp->srcp();
        const int lhswidth = lhsp->widthMin();
        const AstConst* const constp = VN_AS(rhsp->countp(), Const);
        UASSERT_OBJ(constp, rhsp, "Replication value isn't a constant.  Checked earlier!");
        const uint32_t times = constp->toUInt();
        for (int w = 0; w < rhsp->widthWords(); ++w) {
            AstNodeExpr* newp;
            if (lhswidth == 1) {
                newp = new AstNegate{fl, lhsp->cloneTreePure(true)};
                // Replicate always unsigned
                newp->dtypeSetLogicSized(VL_EDATASIZE, VSigning::UNSIGNED);
            } else {
                newp = newAstWordSelClone(lhsp, w);
                FileLine* const rfl = rhsp->fileline();
                for (unsigned repnum = 1; repnum < times; repnum++) {
                    newp = new AstOr{fl, newWordGrabShift(rfl, w, lhsp, lhswidth * repnum), newp};
                }
            }
            addWordAssign(nodep, w, newp);
        }
        return true;
    }

    void visitEqNeq(AstNodeBiop* nodep) {
        if (nodep->user1SetOnce()) return;  // Process once
        iterateChildren(nodep);
        if (nodep->lhsp()->isWide()) {
            if (isImpure(nodep)) return;
            if (!doExpandWide(nodep->lhsp())) return;
            if (!doExpandWide(nodep->rhsp())) return;
            UINFO(8, "    Wordize EQ/NEQ " << nodep);
            // -> (0=={or{for each_word{WORDSEL(lhs,#)^WORDSEL(rhs,#)}}}
            FileLine* const fl = nodep->fileline();
            AstNodeExpr* newp = nullptr;
            for (int w = 0; w < nodep->lhsp()->widthWords(); ++w) {
                AstNodeExpr* const eqp = new AstXor{fl, newAstWordSelClone(nodep->lhsp(), w),
                                                    newAstWordSelClone(nodep->rhsp(), w)};
                newp = newp ? new AstOr{fl, newp, eqp} : eqp;
            }
            if (VN_IS(nodep, Neq)) {
                newp = new AstNeq{fl, new AstConst{fl, AstConst::SizedEData{}, 0}, newp};
            } else {
                newp = new AstEq{fl, new AstConst{fl, AstConst::SizedEData{}, 0}, newp};
            }
            VL_DO_DANGLING(replaceWithDelete(nodep, newp), nodep);
        }
    }
    void visit(AstEq* nodep) override { visitEqNeq(nodep); }
    void visit(AstNeq* nodep) override { visitEqNeq(nodep); }

    void visit(AstRedOr* nodep) override {
        if (nodep->user1SetOnce()) return;  // Process once
        iterateChildren(nodep);
        FileLine* const fl = nodep->fileline();
        if (nodep->lhsp()->isWide()) {
            if (isImpure(nodep)) return;
            if (!doExpandWide(nodep->lhsp())) return;
            UINFO(8, "    Wordize REDOR " << nodep);
            // -> (0!={or{for each_word{WORDSEL(lhs,#)}}}
            AstNodeExpr* newp = nullptr;
            for (int w = 0; w < nodep->lhsp()->widthWords(); ++w) {
                AstNodeExpr* const eqp = newAstWordSelClone(nodep->lhsp(), w);
                newp = newp ? new AstOr{fl, newp, eqp} : eqp;
            }
            newp = new AstNeq{fl, new AstConst{fl, AstConst::SizedEData{}, 0}, newp};
            VL_DO_DANGLING(replaceWithDelete(nodep, newp), nodep);
        } else {
            // No isImpure() check - can handle side effects in below
            UINFO(8, "    REDOR->EQ " << nodep);
            AstNodeExpr* const lhsp = nodep->lhsp()->unlinkFrBack();
            AstNodeExpr* const newp = new AstNeq{
                fl, new AstConst{fl, AstConst::WidthedValue{}, longOrQuadWidth(nodep), 0}, lhsp};
            VL_DO_DANGLING(replaceWithDelete(nodep, newp), nodep);
        }
    }
    void visit(AstRedAnd* nodep) override {
        if (nodep->user1SetOnce()) return;  // Process once
        iterateChildren(nodep);
        FileLine* const fl = nodep->fileline();
        if (nodep->lhsp()->isWide()) {
            if (isImpure(nodep)) return;
            if (!doExpandWide(nodep->lhsp())) return;
            UINFO(8, "    Wordize REDAND " << nodep);
            // -> (0!={and{for each_word{WORDSEL(lhs,#)}}}
            AstNodeExpr* newp = nullptr;
            for (int w = 0; w < nodep->lhsp()->widthWords(); ++w) {
                AstNodeExpr* eqp = newAstWordSelClone(nodep->lhsp(), w);
                if (w == nodep->lhsp()->widthWords() - 1) {
                    // Rather than doing a (slowish) ==##, we OR in the
                    // bits that aren't part of the mask
                    eqp = new AstOr{fl, new AstConst{fl, notWideMask(nodep->lhsp())},
                                    // Bug in cppcheck
                                    // cppcheck-suppress memleak
                                    eqp};
                }
                newp = newp ? new AstAnd{fl, newp, eqp} : eqp;
            }
            newp = new AstEq{fl, new AstConst{fl, AstConst::SizedEData{}, VL_MASK_E(VL_EDATASIZE)},
                             newp};
            VL_DO_DANGLING(replaceWithDelete(nodep, newp), nodep);
        } else {
            // No isImpure() check - can handle side effects in below
            UINFO(8, "    REDAND->EQ " << nodep);
            AstNodeExpr* const lhsp = nodep->lhsp()->unlinkFrBack();
            AstNodeExpr* const newp = new AstEq{fl, new AstConst{fl, wordMask(lhsp)}, lhsp};
            VL_DO_DANGLING(replaceWithDelete(nodep, newp), nodep);
        }
    }
    void visit(AstRedXor* nodep) override {
        if (nodep->user1SetOnce()) return;  // Process once
        iterateChildren(nodep);
        if (nodep->lhsp()->isWide()) {
            if (isImpure(nodep)) return;
            if (!doExpandWide(nodep->lhsp())) return;
            UINFO(8, "    Wordize REDXOR " << nodep);
            // -> (0!={redxor{for each_word{XOR(WORDSEL(lhs,#))}}}
            FileLine* const fl = nodep->fileline();
            AstNodeExpr* newp = nullptr;
            for (int w = 0; w < nodep->lhsp()->widthWords(); ++w) {
                AstNodeExpr* const eqp = newAstWordSelClone(nodep->lhsp(), w);
                newp = newp ? new AstXor{fl, newp, eqp} : eqp;
            }
            newp = new AstRedXor{fl, newp};
            UINFO(8, "    Wordize REDXORnew " << newp);
            VL_DO_DANGLING(replaceWithDelete(nodep, newp), nodep);
        }
        // We don't reduce non-wide XORs, as its more efficient to use a temp register,
        // which the inlined function does nicely.
    }

    void visit(AstNodeStmt* nodep) override {
        if (nodep->user1SetOnce()) return;  // Process once
        VL_RESTORER(m_stmtp);
        m_stmtp = nodep;
        iterateChildren(nodep);
    }
    void visit(AstNodeAssign* nodep) override {
        if (nodep->user1SetOnce()) return;  // Process once
        if (VN_IS(nodep->dtypep()->skipRefp(), UnpackArrayDType)) {
            return;  // Skip for UnpackArrayDType
        }

        VL_RESTORER(m_stmtp);
        m_stmtp = nodep;
        iterateChildren(nodep);
        bool did = false;
        if (nodep->isWide() && ((VN_IS(nodep->lhsp(), VarRef) || VN_IS(nodep->lhsp(), ArraySel)))
            && ((VN_IS(nodep->lhsp(), VarRef) || VN_IS(nodep->lhsp(), ArraySel)))
            && !AstVar::scVarRecurse(nodep->lhsp())  // Need special function for SC
            && !AstVar::scVarRecurse(nodep->rhsp())) {
            if (AstConst* const rhsp = VN_CAST(nodep->rhsp(), Const)) {
                did = expandWide(nodep, rhsp);
            } else if (AstVarRef* const rhsp = VN_CAST(nodep->rhsp(), VarRef)) {
                did = expandWide(nodep, rhsp);
            } else if (AstSel* const rhsp = VN_CAST(nodep->rhsp(), Sel)) {
                did = expandWide(nodep, rhsp);
            } else if (AstArraySel* const rhsp = VN_CAST(nodep->rhsp(), ArraySel)) {
                did = expandWide(nodep, rhsp);
            } else if (AstConcat* const rhsp = VN_CAST(nodep->rhsp(), Concat)) {
                did = expandWide(nodep, rhsp);
            } else if (AstExtend* const rhsp = VN_CAST(nodep->rhsp(), Extend)) {
                did = expandWide(nodep, rhsp);
            } else if (AstReplicate* const rhsp = VN_CAST(nodep->rhsp(), Replicate)) {
                did = expandWide(nodep, rhsp);
            } else if (AstAnd* const rhsp = VN_CAST(nodep->rhsp(), And)) {
                did = expandWide(nodep, rhsp);
            } else if (AstOr* const rhsp = VN_CAST(nodep->rhsp(), Or)) {
                did = expandWide(nodep, rhsp);
            } else if (AstNot* const rhsp = VN_CAST(nodep->rhsp(), Not)) {
                did = expandWide(nodep, rhsp);
            } else if (AstXor* const rhsp = VN_CAST(nodep->rhsp(), Xor)) {
                did = expandWide(nodep, rhsp);
            } else if (AstCond* const rhsp = VN_CAST(nodep->rhsp(), Cond)) {
                did = expandWide(nodep, rhsp);
            }
        } else if (AstSel* const lhsp = VN_CAST(nodep->lhsp(), Sel)) {
            did = expandLhs(nodep, lhsp);
        }
        // Cleanup common code
        if (did) VL_DO_DANGLING(nodep->unlinkFrBack()->deleteTree(), nodep);
    }

    //--------------------
    void visit(AstVar*) override {}  // Don't hit varrefs under vars
    void visit(AstNode* nodep) override { iterateChildren(nodep); }

public:
    // CONSTRUCTORS
    explicit ExpandVisitor(AstNetlist* nodep) { iterate(nodep); }
    ~ExpandVisitor() override {
        V3Stats::addStat("Optimizations, expand wides", m_statWides);
        V3Stats::addStat("Optimizations, expand wide words", m_statWideWords);
        V3Stats::addStat("Optimizations, expand limited", m_statWideLimited);
    }
};

//######################################################################
// Expand class functions

void V3Expand::expandAll(AstNetlist* nodep) {
    UINFO(2, __FUNCTION__ << ":");
    {
        ExpandOkVisitor okVisitor{nodep};
        ExpandVisitor{nodep};
    }  // Destruct before checking
    V3Global::dumpCheckGlobalTree("expand", 0, dumpTreeEitherLevel() >= 3);
}
