// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Parse module/signal name references
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
// TODO: This code was written before SLICESEL was a type it might be
// simplified to look primarily for SLICESELs.
//*************************************************************************

#include "config_build.h"
#include "verilatedos.h"

#include "V3Slice.h"

#include "V3Ast.h"
#include "V3Global.h"

//*************************************************************************

class SliceVisitor final : public VNVisitor {
    // NODE STATE
    // Cleared on netlist
    //  AstNodeAssign::user1()      -> bool.  True if find is complete
    //  AstNodeUniop::user1()       -> bool.  True if find is complete
    //  AstArraySel::user1p()       -> AstVarRef. The VarRef that the final ArraySel points to
    const VNUser1InUse m_inuser1;

    // STATE
    AstNode* m_assignp = nullptr;  // Assignment we are under
    bool m_assignError = false;  // True if the current assign already has an error

    // METHODS
    VL_DEBUG_FUNC;  // Declare debug()

    AstNode* cloneAndSel(AstNode* nodep, int elements, int offset) {
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
            return nodep->cloneTree(false);  // Likely will cause downstream errors
        }
        if (arrayp->rangep()->elementsConst() != elements) {
            if (!m_assignError) {
                nodep->v3error(
                    "Slices of arrays in assignments have different unpacked dimensions, "
                    << elements << " versus " << arrayp->rangep()->elementsConst());
            }
            m_assignError = true;
            elements = 1;
            offset = 0;
        }
        AstNode* newp;
        if (const AstInitArray* const initp = VN_CAST(nodep, InitArray)) {
            UINFO(9, "  cloneInitArray(" << elements << "," << offset << ") " << nodep << endl);
            const int leOffset = !arrayp->rangep()->littleEndian()
                                     ? arrayp->rangep()->elementsConst() - 1 - offset
                                     : offset;
            AstNode* itemp = initp->getIndexDefaultedValuep(leOffset);
            if (!itemp) {
                nodep->v3error("Array initialization has too few elements, need element "
                               << offset);
                itemp = initp->initsp();
            }
            newp = itemp->cloneTree(false);
        } else if (AstNodeCond* const snodep = VN_CAST(nodep, NodeCond)) {
            UINFO(9, "  cloneCond(" << elements << "," << offset << ") " << nodep << endl);
            return snodep->cloneType(snodep->condp()->cloneTree(false),
                                     cloneAndSel(snodep->expr1p(), elements, offset),
                                     cloneAndSel(snodep->expr2p(), elements, offset));
        } else if (const AstSliceSel* const snodep = VN_CAST(nodep, SliceSel)) {
            UINFO(9, "  cloneSliceSel(" << elements << "," << offset << ") " << nodep << endl);
            const int leOffset = (snodep->declRange().lo()
                                  + (!snodep->declRange().littleEndian()
                                         ? snodep->declRange().elements() - 1 - offset
                                         : offset));
            newp = new AstArraySel(nodep->fileline(), snodep->fromp()->cloneTree(false), leOffset);
        } else if (VN_IS(nodep, ArraySel) || VN_IS(nodep, NodeVarRef) || VN_IS(nodep, NodeSel)
                   || VN_IS(nodep, CMethodHard) || VN_IS(nodep, MemberSel)) {
            UINFO(9, "  cloneSel(" << elements << "," << offset << ") " << nodep << endl);
            const int leOffset = !arrayp->rangep()->littleEndian()
                                     ? arrayp->rangep()->elementsConst() - 1 - offset
                                     : offset;
            newp = new AstArraySel(nodep->fileline(), nodep->cloneTree(false), leOffset);
        } else {
            if (!m_assignError) {
                nodep->v3error(nodep->prettyTypeName()
                               << " unexpected in assignment to unpacked array");
            }
            m_assignError = true;
            newp = nodep->cloneTree(false);  // Likely will cause downstream errors
        }
        return newp;
    }

    virtual void visit(AstNodeAssign* nodep) override {
        // Called recursively on newly created assignments
        if (!nodep->user1() && !VN_IS(nodep, AssignAlias)) {
            nodep->user1(true);
            m_assignError = false;
            if (debug() >= 9) nodep->dumpTree(cout, " Deslice-In: ");
            AstNodeDType* const dtp = nodep->lhsp()->dtypep()->skipRefp();
            if (const AstUnpackArrayDType* const arrayp = VN_CAST(dtp, UnpackArrayDType)) {
                // Left and right could have different msb/lsbs/endianness, but #elements is common
                // and all variables are realigned to start at zero
                // Assign of a little endian'ed slice to a big endian one must reverse the elements
                AstNodeAssign* newlistp = nullptr;
                const int elements = arrayp->rangep()->elementsConst();
                for (int offset = 0; offset < elements; ++offset) {
                    AstNodeAssign* const newp
                        = VN_AS(nodep->cloneType(cloneAndSel(nodep->lhsp(), elements, offset),
                                                 cloneAndSel(nodep->rhsp(), elements, offset)),
                                NodeAssign);
                    if (debug() >= 9) newp->dumpTree(cout, "-new ");
                    newlistp = AstNode::addNextNull(newlistp, newp);
                }
                if (debug() >= 9) nodep->dumpTree(cout, " Deslice-Dn: ");
                nodep->replaceWith(newlistp);
                VL_DO_DANGLING(nodep->deleteTree(), nodep);
                // Normal edit iterator will now iterate on all of the expansion assignments
                // This will potentially call this function again to resolve next level of slicing
                return;
            }
            m_assignp = nodep;
            iterateChildren(nodep);
            m_assignp = nullptr;
        }
    }

    virtual void visit(AstInitArray* nodep) override {
        UASSERT_OBJ(!m_assignp, nodep, "Array initialization should have been removed earlier");
    }

    void expandBiOp(AstNodeBiop* nodep) {
        if (!nodep->user1()) {
            nodep->user1(true);
            // If it's an unpacked array, blow it up into comparing each element
            AstNodeDType* const fromDtp = nodep->lhsp()->dtypep()->skipRefp();
            UINFO(9, "  Bi-Eq/Neq expansion " << nodep << endl);
            if (const AstUnpackArrayDType* const adtypep = VN_CAST(fromDtp, UnpackArrayDType)) {
                AstNodeBiop* logp = nullptr;
                if (!VN_IS(nodep->lhsp()->dtypep()->skipRefp(), NodeArrayDType)) {
                    nodep->lhsp()->v3error(
                        "Slice operator "
                        << nodep->lhsp()->prettyTypeName()
                        << " on non-slicable (e.g. non-vector) left-hand-side operand");
                } else if (!VN_IS(nodep->rhsp()->dtypep()->skipRefp(), NodeArrayDType)) {
                    nodep->rhsp()->v3error(
                        "Slice operator "
                        << nodep->rhsp()->prettyTypeName()
                        << " on non-slicable (e.g. non-vector) right-hand-side operand");
                } else {
                    for (int index = 0; index < adtypep->rangep()->elementsConst(); ++index) {
                        // EQ(a,b) -> LOGAND(EQ(ARRAYSEL(a,0), ARRAYSEL(b,0)), ...[1])
                        AstNodeBiop* const clonep
                            = VN_AS(nodep->cloneType(
                                        new AstArraySel(nodep->fileline(),
                                                        nodep->lhsp()->cloneTree(false), index),
                                        new AstArraySel(nodep->fileline(),
                                                        nodep->rhsp()->cloneTree(false), index)),
                                    NodeBiop);
                        if (!logp) {
                            logp = clonep;
                        } else {
                            switch (nodep->type()) {
                            case VNType::atEq:  // FALLTHRU
                            case VNType::atEqCase:
                                logp = new AstLogAnd(nodep->fileline(), logp, clonep);
                                break;
                            case VNType::atNeq:  // FALLTHRU
                            case VNType::atNeqCase:
                                logp = new AstLogOr(nodep->fileline(), logp, clonep);
                                break;
                            default:
                                nodep->v3fatalSrc("Unknown node type processing array slice");
                                break;
                            }
                        }
                    }
                    UASSERT_OBJ(logp, nodep, "Unpacked array with empty indices range");
                    nodep->replaceWith(logp);
                    VL_DO_DANGLING(pushDeletep(nodep), nodep);
                    nodep = logp;
                }
            }
            iterateChildren(nodep);
        }
    }
    virtual void visit(AstEq* nodep) override { expandBiOp(nodep); }
    virtual void visit(AstNeq* nodep) override { expandBiOp(nodep); }
    virtual void visit(AstEqCase* nodep) override { expandBiOp(nodep); }
    virtual void visit(AstNeqCase* nodep) override { expandBiOp(nodep); }

    virtual void visit(AstNode* nodep) override { iterateChildren(nodep); }

public:
    // CONSTRUCTORS
    explicit SliceVisitor(AstNetlist* nodep) { iterate(nodep); }
    virtual ~SliceVisitor() override = default;
};

//######################################################################
// Link class functions

void V3Slice::sliceAll(AstNetlist* nodep) {
    UINFO(2, __FUNCTION__ << ": " << endl);
    { SliceVisitor{nodep}; }  // Destruct before checking
    V3Global::dumpCheckGlobalTree("slice", 0, v3Global.opt.dumpTreeLevel(__FILE__) >= 3);
}
