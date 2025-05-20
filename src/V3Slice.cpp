// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Parse module/signal name references
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
// Slice TRANSFORMATIONS:
//      Top-down traversal (SliceVisitor):
//        NODEASSIGN
//          ARRAYSEL
//            Compare the dimensions to the Var to check for implicit slices.
//            Using ->length() calculate the number of clones needed.
//          VARREF
//            Check the dimensions of the Var for an implicit slice.
//            Replace with ArraySel nodes if needed.
//          SEL, EXTEND
//            We might be assigning a 1-D packed array to a 2-D packed array,
//            this is unsupported.
//          SliceCloneVisitor (called if this node is a slice):
//            NODEASSIGN
//              Clone and iterate the clone:
//                ARRAYSEL
//                  Modify bitp() for the new value and set ->length(1)
//
// TODO: This code was written before SLICESEL was a type, it might be
// simplified to look primarily for SLICESELs.
//*************************************************************************

#include "V3PchAstNoMT.h"  // VL_MT_DISABLED_CODE_UNIT

#include "V3Slice.h"

#include "V3Stats.h"

VL_DEFINE_DEBUG_FUNCTIONS;

//*************************************************************************

class SliceVisitor final : public VNVisitor {
    // NODE STATE
    // Cleared on netlist
    //  AstNodeAssign::user1()      -> bool.  True if find is complete
    //  AstNodeUniop::user1()       -> bool.  True if find is complete
    //  AstArraySel::user1p()       -> AstVarRef. The VarRef that the final ArraySel points to
    const VNUser1InUse m_inuser1;
    //  AstInitArray::user2()       -> Previously accessed itemIdx
    //  AstInitItem::user2()        -> Corresponding first elemIdx
    const VNUser2InUse m_inuser2;

    // STATE - across all visitors
    VDouble0 m_statAssigns;  // Statistic tracking

    // STATE - for current visit position (use VL_RESTORER)
    AstNode* m_assignp = nullptr;  // Assignment we are under
    bool m_assignError = false;  // True if the current assign already has an error
    bool m_okInitArray = false;  // Allow InitArray children

    // METHODS
    AstNodeExpr* cloneAndSel(AstNodeExpr* const nodep, int elements, int elemIdx,
                             const bool needPure) {
        // Insert an ArraySel, except for a few special cases
        const AstUnpackArrayDType* const arrayp
            = VN_CAST(nodep->dtypep()->skipRefp(), UnpackArrayDType);
        if (!arrayp) {  // V3Width should have complained, but...
            if (!m_assignError) {
                nodep->v3error(
                    nodep->prettyTypeName()
                    << " is not an unpacked array, but is in an unpacked array context");
            } else {
                V3Error::incErrors();  // Otherwise might infinite loop
            }
            m_assignError = true;
            // Likely will cause downstream errors
            return nodep->cloneTree(false, needPure);
        }
        if (arrayp->rangep()->elementsConst() != elements) {
            if (!m_assignError) {
                nodep->v3error(
                    "Slices of arrays in assignments have different unpacked dimensions, "
                    << elements << " versus " << arrayp->rangep()->elementsConst());
            }
            m_assignError = true;
            elements = 1;
            elemIdx = 0;
        }
        AstNodeExpr* newp;
        if (AstInitArray* const initp = VN_CAST(nodep, InitArray)) {
            UINFO(9, "  cloneInitArray(" << elements << "," << elemIdx << ") " << nodep << endl);

            auto considerOrder = [](const auto* nodep, int idxFromLeft) -> int {
                return !nodep->rangep()->ascending()
                           ? nodep->rangep()->elementsConst() - 1 - idxFromLeft
                           : idxFromLeft;
            };
            newp = nullptr;
            int itemIdx = 0;
            int i = 0;
            if (const int prevItemIdx = initp->user2()) {
                const AstInitArray::KeyItemMap& itemMap = initp->map();
                const auto it = itemMap.find(considerOrder(arrayp, prevItemIdx));
                if (it != itemMap.end()) {
                    const AstInitItem* itemp = it->second;
                    if (itemp->user2() && itemp->user2() < elemIdx) {
                        // Let's resume traversal from the previous position
                        itemIdx = prevItemIdx;
                        i = itemp->user2();
                    }
                }
            }
            const AstNodeDType* const expectedItemDTypep = arrayp->subDTypep()->skipRefp();
            while (i <= elemIdx) {
                AstNodeExpr* const itemp
                    = initp->getIndexDefaultedValuep(considerOrder(arrayp, itemIdx));
                if (!itemp && !m_assignError) {
                    nodep->v3error("Array initialization has too few elements, need element "
                                   << elemIdx);
                    m_assignError = true;
                }
                const AstNodeDType* itemRawDTypep = itemp->dtypep()->skipRefp();
                const VCastable castable
                    = AstNode::computeCastable(expectedItemDTypep, itemRawDTypep, itemp);
                if (castable == VCastable::SAMEISH || castable == VCastable::COMPATIBLE) {
                    if (i == elemIdx) {
                        newp = itemp->cloneTreePure(false);
                        break;
                    } else {  // Check the next item
                        ++i;
                        ++itemIdx;
                    }
                } else {
                    const AstUnpackArrayDType* const itemDTypep
                        = VN_CAST(itemRawDTypep, UnpackArrayDType);
                    if (!itemDTypep
                        || !expectedItemDTypep->isSame(itemDTypep->subDTypep()->skipRefp())) {
                        if (!m_assignError) {
                            itemp->v3error("Item is incompatible with the array type.");
                        }
                        m_assignError = true;
                        break;
                    }
                    if (i + itemDTypep->elementsConst()
                        > elemIdx) {  // This item contains the element
                        int offset = considerOrder(itemDTypep, elemIdx - i);
                        if (AstSliceSel* const slicep = VN_CAST(itemp, SliceSel)) {
                            offset += slicep->declRange().lo();
                            newp = new AstArraySel{nodep->fileline(),
                                                   slicep->fromp()->cloneTreePure(false), offset};
                        } else {
                            newp = new AstArraySel{nodep->fileline(), itemp->cloneTreePure(false),
                                                   offset};
                        }

                        if (!m_assignError && elemIdx + 1 == elements
                            && i + itemDTypep->elementsConst() > elements) {
                            nodep->v3error("Array initialization has too many elements. "
                                           << elements << " elements are expected, but at least "
                                           << i + itemDTypep->elementsConst()
                                           << " elements exist.");
                            m_assignError = true;
                        }
                        break;
                    } else {  // Check the next item
                        i += itemDTypep->elementsConst();
                        ++itemIdx;
                    }
                }
            }
            if (elemIdx + 1 == elements && static_cast<size_t>(itemIdx) + 1 < initp->map().size()
                && !m_assignError) {
                nodep->v3error("Array initialization has too many elements. "
                               << elements << " elements are expected, but at least "
                               << i + initp->map().size() - itemIdx << " elements exist.");
                m_assignError = true;
            }
            if (newp) {
                const AstInitArray::KeyItemMap& itemMap = initp->map();
                const auto it = itemMap.find(considerOrder(arrayp, itemIdx));
                if (it != itemMap.end()) {  // Remember current position for the next invocation.
                    initp->user2(itemIdx);
                    it->second->user2(i);
                }
            }
            if (!newp) newp = new AstConst{nodep->fileline(), 0};
        } else if (AstNodeCond* const snodep = VN_CAST(nodep, NodeCond)) {
            UINFO(9, "  cloneCond(" << elements << "," << elemIdx << ") " << nodep << endl);
            return snodep->cloneType(snodep->condp()->cloneTree(false, needPure),
                                     cloneAndSel(snodep->thenp(), elements, elemIdx, needPure),
                                     cloneAndSel(snodep->elsep(), elements, elemIdx, needPure));
        } else if (const AstSliceSel* const snodep = VN_CAST(nodep, SliceSel)) {
            UINFO(9, "  cloneSliceSel(" << elements << "," << elemIdx << ") " << nodep << endl);
            const int leOffset = (snodep->declRange().lo()
                                  + (!snodep->declRange().ascending()
                                         ? snodep->declRange().elements() - 1 - elemIdx
                                         : elemIdx));
            newp = new AstArraySel{nodep->fileline(), snodep->fromp()->cloneTree(false, needPure),
                                   leOffset};
        } else if (AstExprStmt* const snodep = VN_CAST(nodep, ExprStmt)) {
            UINFO(9, "  cloneExprStmt(" << elements << "," << elemIdx << ") " << nodep << endl);
            AstNodeExpr* const resultSelp
                = cloneAndSel(snodep->resultp(), elements, elemIdx, needPure);
            if (snodep->stmtsp()) {
                return new AstExprStmt{nodep->fileline(), snodep->stmtsp()->unlinkFrBackWithNext(),
                                       resultSelp};
            } else {
                return resultSelp;
            }
        } else if (VN_IS(nodep, NodeVarRef) || VN_IS(nodep, NodeSel) || VN_IS(nodep, CMethodHard)
                   || VN_IS(nodep, MemberSel) || VN_IS(nodep, StructSel)) {
            UINFO(9, "  cloneSel(" << elements << "," << elemIdx << ") " << nodep << endl);
            const int leOffset = !arrayp->rangep()->ascending()
                                     ? arrayp->rangep()->elementsConst() - 1 - elemIdx
                                     : elemIdx;
            newp = new AstArraySel{nodep->fileline(), nodep->cloneTree(false, needPure), leOffset};
        } else {
            if (!m_assignError) {
                nodep->v3error(nodep->prettyTypeName()
                               << " unexpected in assignment to unpacked array");
            }
            m_assignError = true;
            // Likely will cause downstream errors
            newp = nodep->cloneTree(false, needPure);
        }
        return newp;
    }

    bool assignOptimize(AstNodeAssign* nodep) {
        // Return true if did optimization
        AstNodeDType* const dtp = nodep->lhsp()->dtypep()->skipRefp();
        AstNode* stp = nodep->rhsp();
        const AstUnpackArrayDType* const arrayp = VN_CAST(dtp, UnpackArrayDType);
        if (!arrayp) return false;
        if (VN_IS(stp, CvtPackedToArray)) return false;

        // Any isSc variables must be expanded regardless of --fno-slice
        const bool hasSc
            = nodep->exists([&](const AstVarRef* refp) -> bool { return refp->varp()->isSc(); });
        if (!hasSc && !v3Global.opt.fSlice()) {
            m_okInitArray = true;  // VL_RESTORER in visit(AstNodeAssign)
            return false;
        }

        UINFO(4, "Slice optimizing " << nodep << endl);
        ++m_statAssigns;

        // Left and right could have different ascending/descending range,
        // but #elements is common and all variables are realigned to start at zero
        // Assign of an ascending range slice to a descending range one must reverse
        // the elements
        AstNodeAssign* newlistp = nullptr;
        const int elements = arrayp->rangep()->elementsConst();
        for (int elemIdx = 0; elemIdx < elements; ++elemIdx) {
            // Original node is replaced, so it is safe to copy it one time even if it is impure.
            AstNodeAssign* const newp
                = nodep->cloneType(cloneAndSel(nodep->lhsp(), elements, elemIdx, elemIdx != 0),
                                   cloneAndSel(nodep->rhsp(), elements, elemIdx, elemIdx != 0));
            if (elemIdx == 0) {
                nodep->foreach([this](AstExprStmt* const exprp) {
                    // Result expression is always evaluated to the same value, so the statements
                    // can be removed once they were included in the expression created for the 1st
                    // element.
                    AstNodeExpr* const resultp = exprp->resultp()->unlinkFrBack();
                    exprp->replaceWith(resultp);
                    VL_DO_DANGLING(pushDeletep(exprp), exprp);
                });
            }
            if (debug() >= 9) newp->dumpTree("-  new: ");
            newlistp = AstNode::addNext(newlistp, newp);
        }
        if (debug() >= 9) nodep->dumpTree("-  Deslice-Dn: ");
        nodep->replaceWith(newlistp);
        VL_DO_DANGLING(nodep->deleteTree(), nodep);
        // Normal edit iterator will now iterate on all of the expansion assignments
        // This will potentially call this function again to resolve next level of slicing
        return true;
    }

    void visit(AstNodeAssign* nodep) override {
        // Called recursively on newly created assignments
        if (nodep->user1SetOnce()) return;  // Process once
        if (VN_IS(nodep, AssignAlias)) return;
        if (debug() >= 9) nodep->dumpTree("-  Deslice-In: ");
        VL_RESTORER(m_assignError);
        VL_RESTORER(m_assignp);
        VL_RESTORER(m_okInitArray);  // Set in assignOptimize
        m_assignError = false;
        m_assignp = nodep;
        if (assignOptimize(nodep)) return;
        iterateChildren(nodep);
    }

    void visit(AstConsPackUOrStruct* nodep) override {
        VL_RESTORER(m_okInitArray);
        m_okInitArray = true;
        iterateChildren(nodep);
    }
    void visit(AstConsDynArray* nodep) override {
        VL_RESTORER(m_okInitArray);
        m_okInitArray = true;
        iterateChildren(nodep);
    }
    void visit(AstConsQueue* nodep) override {
        VL_RESTORER(m_okInitArray);
        m_okInitArray = true;
        iterateChildren(nodep);
    }
    void visit(AstInitArray* nodep) override {
        UASSERT_OBJ(!m_assignp || m_okInitArray, nodep,
                    "Array initialization should have been removed earlier");
    }

    void expandBiOp(AstNodeBiop* nodep) {
        if (nodep->user1SetOnce()) return;  // Process once
        UINFO(9, "  Bi-Eq/Neq expansion " << nodep << endl);

        // Only expand if lhs is an unpacked array (we assume type checks already passed)
        const AstNodeDType* const fromDtp = nodep->lhsp()->dtypep()->skipRefp();
        if (const AstUnpackArrayDType* const adtypep = VN_CAST(fromDtp, UnpackArrayDType)) {
            AstNodeBiop* logp = nullptr;

            const int elements = adtypep->rangep()->elementsConst();
            for (int elemIdx = 0; elemIdx < elements; ++elemIdx) {
                // EQ(a,b) -> LOGAND(EQ(ARRAYSEL(a,0), ARRAYSEL(b,0)), ...[1])
                // Original node is replaced, so it is safe to copy it one time even if it is
                // impure.
                AstNodeBiop* const clonep = VN_AS(
                    nodep->cloneType(cloneAndSel(nodep->lhsp(), elements, elemIdx, elemIdx != 0),
                                     cloneAndSel(nodep->rhsp(), elements, elemIdx, elemIdx != 0)),
                    NodeBiop);
                if (elemIdx == 0) {
                    nodep->foreach([this](AstExprStmt* const exprp) {
                        // Result expression is always evaluated to the same value, so the
                        // statements can be removed once they were included in the expression
                        // created for the 1st element.
                        AstNodeExpr* const resultp = exprp->resultp()->unlinkFrBack();
                        exprp->replaceWith(resultp);
                        VL_DO_DANGLING(pushDeletep(exprp), exprp);
                    });
                }

                if (!logp) {
                    logp = clonep;
                } else {
                    switch (nodep->type()) {
                    case VNType::atEq:  // FALLTHRU
                    case VNType::atEqCase:
                        logp = new AstLogAnd{nodep->fileline(), logp, clonep};
                        break;
                    case VNType::atNeq:  // FALLTHRU
                    case VNType::atNeqCase:
                        logp = new AstLogOr{nodep->fileline(), logp, clonep};
                        break;
                    default: nodep->v3fatalSrc("Unknown node type processing array slice"); break;
                    }
                }
            }
            UASSERT_OBJ(logp, nodep, "Unpacked array with empty indices range");
            nodep->replaceWith(logp);
            VL_DO_DANGLING(pushDeletep(nodep), nodep);
            nodep = logp;
        }

        iterateChildren(nodep);
    }

    void visit(AstEq* nodep) override { expandBiOp(nodep); }
    void visit(AstNeq* nodep) override { expandBiOp(nodep); }
    void visit(AstEqCase* nodep) override { expandBiOp(nodep); }
    void visit(AstNeqCase* nodep) override { expandBiOp(nodep); }

    void visit(AstNode* nodep) override { iterateChildren(nodep); }

public:
    // CONSTRUCTORS
    explicit SliceVisitor(AstNetlist* nodep) { iterate(nodep); }
    ~SliceVisitor() override {
        V3Stats::addStat("Optimizations, Slice array assignments", m_statAssigns);
    }
};

//######################################################################
// Link class functions

void V3Slice::sliceAll(AstNetlist* nodep) {
    UINFO(2, __FUNCTION__ << ": " << endl);
    { SliceVisitor{nodep}; }  // Destruct before checking
    V3Global::dumpCheckGlobalTree("slice", 0, dumpTreeEitherLevel() >= 3);
}
