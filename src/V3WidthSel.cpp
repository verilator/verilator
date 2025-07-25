// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Expression width calculations
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
// V3WidthSel's Transformations:
//      Top down traversal:
//          Replace SELPLUS/SELMINUS with SEL
//          Replace SELEXTRACT with SEL
//          Replace SELBIT with SEL or ARRAYSEL
//
// This code was once in V3LinkResolve, but ascending bit range vectors won't
// work that early.  It was considered for V3Width and V3Param, but is
// fairly ugly both places as the nodes change in too strongly
// interconnected ways.
//
//*************************************************************************

#include "V3PchAstNoMT.h"  // VL_MT_DISABLED_CODE_UNIT

#include "V3Const.h"
#include "V3Width.h"

VL_DEFINE_DEBUG_FUNCTIONS;

//######################################################################
// Width state, as a visitor of each AstNode

class WidthSelVisitor final : public VNVisitor {
    // IMPORTANT
    //**** This is not a normal visitor, in that all iteration is instead
    //  done by the caller (V3Width).  This avoids duplicating much of the
    //  complicated GenCase/GenFor/Cell/Function call logic that all depends
    //  on if widthing top-down or just for parameters.
#define iterateChildren DO_NOT_iterateChildern_IN_V3WidthSel

    // METHODS

    void checkConstantOrReplace(AstNode* nodep, const string& message) {
        // See also V3Width::checkConstantOrReplace
        // Note can't call V3Const::constifyParam(nodep) here, as constify may change nodep on us!
        if (!VN_IS(nodep, Const)) {
            nodep->v3error(message);
            nodep->replaceWith(new AstConst{nodep->fileline(), AstConst::Unsized32{}, 1});
            VL_DO_DANGLING(pushDeletep(nodep), nodep);
        }
    }

    // RETURN TYPE
    struct FromData final {
        AstNodeDType* const m_errp;  // Node that was found, for error reporting if not known type
        AstNodeDType* const m_dtypep;  // Data type for the 'from' slice
        VNumRange m_fromRange;  // Numeric range bounds for the 'from' slice
        FromData(AstNodeDType* errp, AstNodeDType* dtypep, const VNumRange& fromRange)
            : m_errp{errp}
            , m_dtypep{dtypep}
            , m_fromRange{fromRange} {}
        ~FromData() = default;
    };
    static FromData fromDataForArray(AstNode* nodep, AstNode* basefromp) {
        // What is the data type and information for this SEL-ish's from()?
        UINFO(9, "  fromData start ddtypep = " << basefromp);
        VNumRange fromRange;  // constructs to isRanged(false)
        while (basefromp) {
            if (VN_IS(basefromp, AttrOf)) {
                basefromp = VN_AS(basefromp, AttrOf)->fromp();
                continue;
            }
            break;
        }
        UASSERT_OBJ(basefromp && basefromp->dtypep(), nodep, "Select with no from dtype");
        AstNodeDType* const ddtypep = basefromp->dtypep()->skipRefp();
        AstNodeDType* const errp = ddtypep;
        UINFO(9, "  fromData.ddtypep = " << ddtypep);
        if (const AstNodeArrayDType* const adtypep = VN_CAST(ddtypep, NodeArrayDType)) {
            fromRange = adtypep->declRange();
        } else if (VN_IS(ddtypep, AssocArrayDType)) {
        } else if (VN_IS(ddtypep, WildcardArrayDType)) {
        } else if (VN_IS(ddtypep, DynArrayDType)) {
        } else if (VN_IS(ddtypep, QueueDType)) {
        } else if (const AstNodeUOrStructDType* const adtypep
                   = VN_CAST(ddtypep, NodeUOrStructDType)) {
            fromRange = adtypep->declRange();
        } else if (const AstBasicDType* const adtypep = VN_CAST(ddtypep, BasicDType)) {
            if (adtypep->isString() && VN_IS(nodep, SelBit)) {
            } else if (adtypep->isRanged()) {
                UASSERT_OBJ(
                    !(adtypep->rangep()
                      && (!VN_IS(adtypep->rangep()->leftp(), Const)
                          || !VN_IS(adtypep->rangep()->rightp(), Const))),
                    nodep,
                    "Non-constant variable range; errored earlier");  // in constifyParam(bfdtypep)
                fromRange = adtypep->declRange();
            } else {
                nodep->v3error("Illegal bit or array select; type does not have a bit range, or "
                               << "bad dimension: data type is " << errp->prettyDTypeNameQ());
            }
        } else {
            nodep->v3error("Illegal bit or array select; type already selected, or bad dimension: "
                           << "data type is " << errp->prettyDTypeNameQ());
        }
        return FromData(errp, ddtypep, fromRange);
    }

    AstNodeExpr* newSubNeg(AstNodeExpr* lhsp, int32_t rhs) {
        // Return lhs-rhs, but if rhs is negative use an add, so we won't
        // have to deal with signed math and related 32bit sign extension problems
        if (rhs == 0) {
            return lhsp;
        } else if (VN_IS(lhsp, Const)) {
            // Optional vs just making add/sub below, but saves constification some work
            V3Number num(lhsp, lhsp->width());
            num.opSub(VN_AS(lhsp, Const)->num(), V3Number(lhsp, 32, rhs));
            num.isSigned(lhsp->isSigned());
            return new AstConst{lhsp->fileline(), num};
        } else if (rhs > 0) {
            AstNodeExpr* const newp
                = new AstSub{lhsp->fileline(), lhsp,
                             new AstConst(lhsp->fileline(), AstConst::Unsized32{}, rhs)};
            // We must make sure sub gets sign of original value, not from the constant
            newp->dtypeFrom(lhsp);
            return newp;
        } else {  // rhs < 0;
            AstNodeExpr* const newp
                = new AstAdd{lhsp->fileline(), lhsp,
                             new AstConst(lhsp->fileline(), AstConst::Unsized32{}, -rhs)};
            // We must make sure sub gets sign of original value, not from the constant
            newp->dtypeFrom(lhsp);
            return newp;
        }
    }
    AstNodeExpr* newSubNeg(int32_t lhs, AstNodeExpr* rhsp) {
        // Return lhs-rhs
        // We must make sure sub gets sign of original value
        AstNodeExpr* const newp = new AstSub{
            rhsp->fileline(), new AstConst(rhsp->fileline(), AstConst::Unsized32{}, lhs), rhsp};
        newp->dtypeFrom(rhsp);  // Important as AstSub default is lhs's sign
        return newp;
    }

    AstNodeExpr* newSubLsbOf(AstNodeExpr* underp, const VNumRange& fromRange) {
        // Account for a variable's LSB in bit selections
        // Will likely become SUB(underp, lsb_of_signal).
        // Don't report WIDTH warnings etc here, as may be inside a
        // generate branch that will be deleted.
        // SUB #'s Not needed when LSB==0 and MSB>=0 (ie [0:-13] must still get added!)
        if (!fromRange.ranged()) {
            // vector without range, or 0 lsb is ok, for example a INTEGER x; y = x[21:0];
            return underp;
        } else {
            if (fromRange.ascending()) {
                // reg [1:3] was swapped to [3:1] (lsbEndianedp==3) and needs a SUB(3,under)
                return newSubNeg(fromRange.hi(), underp);
            } else {
                // reg [3:1] needs a SUB(under,1)
                return newSubNeg(underp, fromRange.lo());
            }
        }
    }
    AstNodeExpr* newMulConst(FileLine* fl, uint32_t elwidth, AstNodeExpr* indexp) {
        AstNodeExpr* extendp;
        if (indexp->width() > 32) {
            extendp = new AstSel{fl, indexp, 0, 32};
        } else {
            extendp = new AstExtend{fl, indexp};
        }
        extendp->dtypeSetLogicUnsized(
            32, std::max(V3Number::log2b(elwidth) + 1, indexp->widthMin()), VSigning::UNSIGNED);
        AstNodeExpr* const mulp
            = new AstMul{fl, new AstConst{fl, AstConst::Unsized32{}, elwidth},
                         // Extend needed as index might be e.g. 3 bits but constant e.g. 5 bits
                         extendp};
        return mulp;
    }

    AstNodeDType* sliceDType(AstPackArrayDType* nodep, int msb, int lsb) {
        // Return slice needed for msb/lsb, either as original dtype or a new slice dtype
        if (nodep->declRange().elements() == (msb - lsb + 1)  // Extracting whole of original array
            && nodep->declRange().lo() == lsb) {
            return nodep;
        } else {
            // Need a slice data type, which is an array of the extracted
            // type, but with (presumably) different size
            const VNumRange newRange{msb, lsb, nodep->declRange().ascending()};
            AstNodeDType* const vardtypep
                = new AstPackArrayDType{nodep->fileline(),
                                        nodep->subDTypep(),  // Need to strip off array reference
                                        new AstRange{nodep->fileline(), newRange}};
            v3Global.rootp()->typeTablep()->addTypesp(vardtypep);
            return vardtypep;
        }
    }

    AstNodeExpr* selQueueBackness(AstNode* nodep) {
        if (VN_IS(nodep, Unbounded)) {  // e.g. "[$]"
            return new AstConst{nodep->fileline(), AstConst::Signed32{}, 0};
        } else if (VN_IS(nodep, Sub) && VN_IS(VN_CAST(nodep, Sub)->lhsp(), Unbounded)) {
            // e.g. "q[$ - 1]", where 1 is subnodep
            AstNodeExpr* subrhsp = VN_CAST(nodep, Sub)->rhsp()->unlinkFrBack();
            return subrhsp;
        } else {
            return nullptr;
        }
    }

    void warnTri(AstNode* nodep) {
        if (VN_IS(nodep, Const) && VN_AS(nodep, Const)->num().isFourState()) {
            nodep->v3error(
                "Selection index is constantly unknown or tristated: " << nodep->name());
        }
    }

    // VISITORS
    // If adding new visitors, ensure V3Width's visit(TYPE) calls into here

    void visit(AstSelBit* nodep) override {
        // Select of a non-width specified part of an array, i.e. "array[2]"
        // This select style has a lsb and msb (no user specified width)
        UINFO(6, "SELBIT " << nodep);
        if (debug() >= 9) nodep->backp()->dumpTree("-  SELBT0: ");
        // lhsp/rhsp do not need to be constant
        AstNodeExpr* const fromp = nodep->fromp()->unlinkFrBack();
        AstNodeExpr* const rhsp = nodep->bitp()->unlinkFrBack();  // bit we're extracting
        if (debug() >= 9) nodep->dumpTree("-  SELBT2: ");
        const FromData fromdata = fromDataForArray(nodep, fromp);
        AstNodeDType* const ddtypep = fromdata.m_dtypep;
        const VNumRange fromRange = fromdata.m_fromRange;
        UINFO(6, "  ddtypep " << ddtypep);
        if (const AstUnpackArrayDType* const adtypep = VN_CAST(ddtypep, UnpackArrayDType)) {
            // SELBIT(array, index) -> ARRAYSEL(array, index)
            AstNodeExpr* subp = rhsp;
            if (fromRange.lo() != 0 || fromRange.hi() < 0) {
                subp = newSubNeg(subp, fromRange.lo());
            }
            AstArraySel* const newp = new AstArraySel{nodep->fileline(), fromp, subp};
            newp->dtypeFrom(adtypep->subDTypep());  // Need to strip off array reference
            if (debug() >= 9) newp->dumpTree("-  SELBTn: ");
            nodep->replaceWith(newp);
            VL_DO_DANGLING(pushDeletep(nodep), nodep);
        } else if (const AstPackArrayDType* const adtypep = VN_CAST(ddtypep, PackArrayDType)) {
            // SELBIT(array, index) -> SEL(array, index*width-of-subindex, width-of-subindex)
            AstNodeExpr* subp = rhsp;
            if (fromRange.ascending()) {
                subp = newSubNeg(fromRange.hi(), subp);
            } else {
                subp = newSubNeg(subp, fromRange.lo());
            }
            UASSERT_OBJ(!(!fromRange.elements() || (adtypep->width() % fromRange.elements()) != 0),
                        adtypep,
                        "Array extraction with width miscomputed " << adtypep->width() << "/"
                                                                   << fromRange.elements());
            // cppcheck-suppress zerodivcond
            const int elwidth = adtypep->width() / fromRange.elements();
            AstSel* const newp = new AstSel{
                nodep->fileline(), fromp, newMulConst(nodep->fileline(), elwidth, subp), elwidth};
            newp->declRange(fromRange);
            newp->declElWidth(elwidth);
            newp->dtypeFrom(adtypep->subDTypep());  // Need to strip off array reference
            if (debug() >= 9) newp->dumpTree("-  SELBTn: ");
            nodep->replaceWith(newp);
            VL_DO_DANGLING(pushDeletep(nodep), nodep);
        } else if (const AstAssocArrayDType* const adtypep = VN_CAST(ddtypep, AssocArrayDType)) {
            // SELBIT(array, index) -> ASSOCSEL(array, index)
            AstAssocSel* const newp = new AstAssocSel{nodep->fileline(), fromp, rhsp};
            newp->dtypeFrom(adtypep->subDTypep());  // Need to strip off array reference
            if (debug() >= 9) newp->dumpTree("-  SELBTn: ");
            nodep->replaceWith(newp);
            VL_DO_DANGLING(pushDeletep(nodep), nodep);
        } else if (const AstWildcardArrayDType* const adtypep
                   = VN_CAST(ddtypep, WildcardArrayDType)) {
            // SELBIT(array, index) -> WILDCARDSEL(array, index)
            AstWildcardSel* const newp = new AstWildcardSel{nodep->fileline(), fromp, rhsp};
            newp->dtypeFrom(adtypep->subDTypep());  // Need to strip off array reference
            if (debug() >= 9) newp->dumpTree("-  SELBTn: ");
            nodep->replaceWith(newp);
            VL_DO_DANGLING(pushDeletep(nodep), nodep);
        } else if (const AstDynArrayDType* const adtypep = VN_CAST(ddtypep, DynArrayDType)) {
            // SELBIT(array, index) -> CMETHODCALL(queue, "at", index)
            const char* methodName = nodep->access().isWriteOrRW() ? "atWrite" : "at";
            AstCMethodHard* const newp
                = new AstCMethodHard{nodep->fileline(), fromp, methodName, rhsp};
            newp->dtypeFrom(adtypep->subDTypep());  // Need to strip off queue reference
            if (debug() >= 9) newp->dumpTree("-  SELBTq: ");
            nodep->replaceWith(newp);
            VL_DO_DANGLING(pushDeletep(nodep), nodep);
        } else if (const AstQueueDType* const adtypep = VN_CAST(ddtypep, QueueDType)) {
            // SELBIT(array, index) -> CMETHODCALL(queue, "at", index)
            AstCMethodHard* newp;
            const char* methodName = nodep->access().isWriteOrRW() ? "atWriteAppend" : "at";
            if (AstNodeExpr* const backnessp = selQueueBackness(rhsp)) {
                newp = new AstCMethodHard{nodep->fileline(), fromp,
                                          std::string(methodName) + "Back", backnessp};
            } else {
                newp = new AstCMethodHard{nodep->fileline(), fromp, methodName, rhsp};
            }
            newp->dtypeFrom(adtypep->subDTypep());  // Need to strip off queue reference
            if (debug() >= 9) newp->dumpTree("-  SELBTq: ");
            nodep->replaceWith(newp);
            VL_DO_DANGLING(pushDeletep(nodep), nodep);
        } else if (VN_IS(ddtypep, BasicDType) && ddtypep->isString()) {
            // SELBIT(string, index) -> GETC(string, index)
            AstNodeExpr* exprp = fromp;
            while (true) {
                if (AstMemberSel* const memberselp = VN_CAST(exprp, MemberSel)) {
                    exprp = memberselp->fromp();
                } else if (AstStructSel* const structselp = VN_CAST(exprp, StructSel)) {
                    exprp = structselp->fromp();
                } else {
                    break;
                }
            }
            const AstNodeVarRef* const varrefp = VN_CAST(exprp, NodeVarRef);
            AstNodeExpr* newp;
            if (!varrefp || varrefp->access().isReadOnly()) {
                newp = new AstGetcN{nodep->fileline(), fromp, rhsp};
            } else {
                newp = new AstGetcRefN{nodep->fileline(), fromp, rhsp};
            }
            UINFO(6, "   new " << newp);
            nodep->replaceWith(newp);
            VL_DO_DANGLING(pushDeletep(nodep), nodep);
        } else if (VN_IS(ddtypep, BasicDType)) {
            // SELBIT(range, index) -> SEL(array, index, 1)
            AstSel* const newp
                = new AstSel{nodep->fileline(), fromp, newSubLsbOf(rhsp, fromRange), 1};
            newp->declRange(fromRange);
            UINFO(6, "   new " << newp);
            if (debug() >= 9) newp->dumpTree("-  SELBTn: ");
            nodep->replaceWith(newp);
            VL_DO_DANGLING(pushDeletep(nodep), nodep);
        } else if (VN_IS(ddtypep, NodeUOrStructDType)) {  // A bit from the packed struct
            // SELBIT(range, index) -> SEL(array, index, 1)
            AstSel* const newp
                = new AstSel{nodep->fileline(), fromp, newSubLsbOf(rhsp, fromRange), 1};
            newp->declRange(fromRange);
            UINFO(6, "   new " << newp);
            if (debug() >= 9) newp->dumpTree("-  SELBTn: ");
            nodep->replaceWith(newp);
            VL_DO_DANGLING(pushDeletep(nodep), nodep);
        } else {  // nullptr=bad extract, or unknown node type
            nodep->v3error("Illegal bit or array select; type already selected, or bad dimension: "
                           << "data type is" << fromdata.m_errp->prettyDTypeNameQ());
            // How to recover?  We'll strip a dimension.
            nodep->replaceWith(fromp);
            VL_DO_DANGLING(pushDeletep(nodep), nodep);
        }
        if (!rhsp->backp()) VL_DO_DANGLING(pushDeletep(rhsp), rhsp);
    }
    void visit(AstSelExtract* nodep) override {
        // Select of a range specified part of an array, i.e. "array[2:3]"
        // SELEXTRACT(from,msb,lsb) -> SEL(from, lsb, 1+msb-lsb)
        // This select style has a (msb or lsb) and width
        UINFO(6, "SELEXTRACT " << nodep);
        // if (debug() >= 9) nodep->dumpTree("-  SELEX0: ");
        // Below 2 lines may change nodep->widthp()
        V3Const::constifyParamsNoWarnEdit(nodep->leftp());  // May relink pointed to node
        V3Const::constifyParamsNoWarnEdit(nodep->rightp());  // May relink pointed to node
        // if (debug() >= 9) nodep->dumpTree("-  SELEX3: ");
        AstNodeExpr* const fromp = nodep->fromp()->unlinkFrBack();
        const FromData fromdata = fromDataForArray(nodep, fromp);
        AstNodeDType* const ddtypep = fromdata.m_dtypep;
        const VNumRange fromRange = fromdata.m_fromRange;
        if (VN_IS(ddtypep, QueueDType)) {
            AstNodeExpr* const qleftp = nodep->leftp()->unlinkFrBack();
            AstNodeExpr* const qrightp = nodep->rightp()->unlinkFrBack();
            AstNodeExpr* const qleftBacknessp = selQueueBackness(qleftp);
            AstNodeExpr* const qrightBacknessp = selQueueBackness(qrightp);
            // Use special methods to refer to back rather than math using
            // queue size, this allows a single queue reference, to support
            // for equations in side effects that select the queue to
            // operate upon.
            std::string name = (qleftBacknessp    ? "sliceBackBack"
                                : qrightBacknessp ? "sliceFrontBack"
                                                  : "slice");
            AstCMethodHard* const newp = new AstCMethodHard{
                nodep->fileline(), fromp, name, qleftBacknessp ? qleftBacknessp : qleftp};
            newp->addPinsp(qrightBacknessp ? qrightBacknessp : qrightp);
            newp->dtypep(ddtypep);
            newp->didWidth(true);
            newp->protect(false);
            UINFO(6, "   new " << newp);
            nodep->replaceWith(newp);
            VL_DO_DANGLING(pushDeletep(nodep), nodep);
            return;
        }
        // Non-queue
        checkConstantOrReplace(nodep->leftp(),
                               "First value of [a:b] isn't a constant, maybe you want +: or -:");
        checkConstantOrReplace(nodep->rightp(),
                               "Second value of [a:b] isn't a constant, maybe you want +: or -:");
        AstNodeExpr* const msbp = nodep->leftp()->unlinkFrBack();
        AstNodeExpr* const lsbp = nodep->rightp()->unlinkFrBack();
        int32_t msb = VN_AS(msbp, Const)->toSInt();
        int32_t lsb = VN_AS(lsbp, Const)->toSInt();
        const int32_t elem = (msb > lsb) ? (msb - lsb + 1) : (lsb - msb + 1);
        if (VN_IS(ddtypep, UnpackArrayDType)) {
            // Slice extraction
            if (fromRange.elements() == elem
                && fromRange.lo() == lsb) {  // Extracting whole of original array
                nodep->replaceWith(fromp);
                VL_DO_DANGLING(pushDeletep(nodep), nodep);
            } else if (fromRange.elements() == 1) {  // Extracting single element
                AstArraySel* const newp = new AstArraySel{nodep->fileline(), fromp, lsbp};
                nodep->replaceWith(newp);
                VL_DO_DANGLING(pushDeletep(nodep), nodep);
            } else {  // Slice
                AstSliceSel* const newp
                    = new AstSliceSel{nodep->fileline(), fromp,
                                      VNumRange{msb - fromRange.lo(), lsb - fromRange.lo()}};
                nodep->replaceWith(newp);
                VL_DO_DANGLING(pushDeletep(nodep), nodep);
            }
        } else if (AstPackArrayDType* const adtypep = VN_CAST(ddtypep, PackArrayDType)) {
            // SELEXTRACT(array, msb, lsb) -> SEL(array,
            //             lsb*width-of-subindex, width-of-subindex*(msb-lsb))
            UASSERT_OBJ(!(!fromRange.elements() || (adtypep->width() % fromRange.elements()) != 0),
                        adtypep,
                        "Array extraction with width miscomputed " << adtypep->width() << "/"
                                                                   << fromRange.elements());
            if (fromRange.ascending()) {
                // Below code assumes descending bit range; just works out if we swap
                const int x = msb;
                msb = lsb;
                lsb = x;
            }
            if (lsb > msb) {
                nodep->v3warn(
                    SELRANGE,
                    "[" << msb << ":" << lsb
                        << "] Slice range has ascending bit ordering, perhaps you wanted [" << lsb
                        << ":" << msb << "]");
                const int x = msb;
                msb = lsb;
                lsb = x;
            }
            const int elwidth = adtypep->width() / fromRange.elements();
            AstSel* const newp
                = new AstSel{nodep->fileline(), fromp,
                             newMulConst(nodep->fileline(), elwidth, newSubLsbOf(lsbp, fromRange)),
                             (msb - lsb + 1) * elwidth};
            newp->declRange(fromRange);
            newp->declElWidth(elwidth);
            newp->dtypeFrom(sliceDType(adtypep, msb, lsb));
            // if (debug() >= 9) newp->dumpTree("-  EXTBTn: ");
            UASSERT_OBJ(newp->widthMin() == newp->widthConst(), nodep, "Width mismatch");
            nodep->replaceWith(newp);
            VL_DO_DANGLING(pushDeletep(nodep), nodep);
        } else if (VN_IS(ddtypep, BasicDType)) {
            if (fromRange.ascending()) {
                // Below code assumes descending bit range; just works out if we swap
                const int x = msb;
                msb = lsb;
                lsb = x;
            }
            if (lsb > msb) {
                nodep->v3warn(
                    SELRANGE,
                    "[" << msb << ":" << lsb
                        << "] Slice range has ascending bit ordering, perhaps you wanted [" << lsb
                        << ":" << msb << "]");
                const int x = msb;
                msb = lsb;
                lsb = x;
            }
            AstSel* const newp = new AstSel{nodep->fileline(), fromp, newSubLsbOf(lsbp, fromRange),
                                            msb + 1 - lsb};
            newp->declRange(fromRange);
            UINFO(6, "   new " << newp);
            // if (debug() >= 9) newp->dumpTree("-  SELEXnew: ");
            nodep->replaceWith(newp);
            VL_DO_DANGLING(pushDeletep(nodep), nodep);
        } else if (VN_IS(ddtypep, NodeUOrStructDType)) {
            // Classes don't have an ascending range
            if (lsb > msb) {
                nodep->v3warn(
                    SELRANGE,
                    "[" << msb << ":" << lsb
                        << "] Slice range has ascending bit ordering, perhaps you wanted [" << lsb
                        << ":" << msb << "]");
                const int x = msb;
                msb = lsb;
                lsb = x;
            }
            AstSel* const newp = new AstSel{nodep->fileline(), fromp, newSubLsbOf(lsbp, fromRange),
                                            msb + 1 - lsb};
            newp->declRange(fromRange);
            UINFO(6, "   new " << newp);
            // if (debug() >= 9) newp->dumpTree("-  SELEXnew: ");
            nodep->replaceWith(newp);
            VL_DO_DANGLING(pushDeletep(nodep), nodep);
        } else {  // nullptr=bad extract, or unknown node type
            nodep->v3error("Illegal range select; type already selected, or bad dimension: "
                           << "data type is " << fromdata.m_errp->prettyDTypeNameQ());
            UINFO(1, "    Related ddtype: " << ddtypep);
            // How to recover?  We'll strip a dimension.
            nodep->replaceWith(fromp);
            VL_DO_DANGLING(pushDeletep(nodep), nodep);
        }
        // delete whatever we didn't use in reconstruction
        if (!fromp->backp()) VL_DO_DANGLING(pushDeletep(fromp), fromp);
        if (!msbp->backp()) VL_DO_DANGLING(pushDeletep(msbp), msbp);
        if (!lsbp->backp()) VL_DO_DANGLING(pushDeletep(lsbp), lsbp);
    }

    void replaceSelPlusMinus(AstNodePreSel* nodep) {
        // Select of a range specified with +: or -:, i.e. "array[2+:3], [2-:3]"
        // This select style has a lsb and width
        UINFO(6, "SELPLUS/MINUS " << nodep);
        // Below 2 lines may change nodep->widthp()
        if (debug() >= 9) nodep->dumpTree("-  SELPM0: ");
        V3Width::widthParamsEdit(nodep->rhsp());  // constifyEdit doesn't ensure widths finished
        V3Const::constifyEdit(nodep->rhsp());  // May relink pointed to node, ok if not const
        V3Const::constifyParamsEdit(nodep->thsp());  // May relink pointed to node
        checkConstantOrReplace(nodep->thsp(),
                               "Width of :+ or :- bit slice range isn't a constant");
        if (debug() >= 9) nodep->dumpTree("-  SELPM3: ");
        // Now replace it with an AstSel
        AstNodeExpr* const fromp = nodep->fromp()->unlinkFrBack();
        AstNodeExpr* const rhsp = nodep->rhsp()->unlinkFrBack();
        AstNodeExpr* const widthp = nodep->thsp()->unlinkFrBack();
        warnTri(rhsp);
        const int width = VN_AS(widthp, Const)->toSInt();
        if (width > (1 << 28)) {
            nodep->v3error("Width of :+ or :- is huge; vector of over 1 billion bits: "
                           << widthp->prettyName());
        }
        if (width < 0) nodep->v3error("Width of :+ or :- is < 0: " << widthp->prettyName());
        const FromData fromdata = fromDataForArray(nodep, fromp);
        const AstNodeDType* const ddtypep = fromdata.m_dtypep;
        const VNumRange fromRange = fromdata.m_fromRange;
        if (VN_IS(ddtypep, UnpackArrayDType)) {
            // Slice +: and -: extraction
            if (fromRange.elements() == width && VN_IS(rhsp, Const)
                && VN_AS(rhsp, Const)->toSInt()
                       == fromRange.lo()) {  // Extracting whole of original array
                nodep->replaceWith(fromp);
                VL_DO_DANGLING(pushDeletep(nodep), nodep);
            } else if (fromRange.elements() == 1) {  // Extracting single element
                AstArraySel* const newp = new AstArraySel{nodep->fileline(), fromp, rhsp};
                nodep->replaceWith(newp);
                VL_DO_DANGLING(pushDeletep(nodep), nodep);
            } else if (VN_IS(rhsp, Const)) {  // Slice
                const int32_t rhs = VN_AS(rhsp, Const)->toSInt();
                // down array: lsb/lo +: width
                // down array: msb/hi -: width
                // up array:   msb/lo +: width
                // up array:   lsb/hi -: width
                const int32_t msb
                    = (VN_IS(nodep, SelPlus) ? rhs + width - 1 : rhs) - fromRange.lo();
                const int32_t lsb
                    = (VN_IS(nodep, SelPlus) ? rhs : rhs - width + 1) - fromRange.lo();
                AstSliceSel* const newp = new AstSliceSel{
                    nodep->fileline(), fromp, VNumRange{msb, lsb, fromRange.ascending()}};
                nodep->replaceWith(newp);
                VL_DO_DANGLING(pushDeletep(nodep), nodep);
            } else {
                nodep->v3warn(E_UNSUPPORTED, "Unsupported: Slice of non-constant bounds");
            }
        } else if (VN_IS(ddtypep, BasicDType) || VN_IS(ddtypep, PackArrayDType)
                   || (VN_IS(ddtypep, NodeUOrStructDType)
                       && VN_AS(ddtypep, NodeUOrStructDType)->packedUnsup())) {
            int elwidth = 1;
            int newwidth = width;
            if (const AstPackArrayDType* const adtypep = VN_CAST(ddtypep, PackArrayDType)) {
                elwidth = adtypep->width() / fromRange.elements();
                newwidth = width * elwidth;
            }
            AstNodeExpr* newlsbp = nullptr;
            if (VN_IS(nodep, SelPlus)) {
                if (fromRange.ascending()) {
                    // SELPLUS(from,lsb,width) -> SEL(from, (vector_msb-width+1)-sel, width)
                    newlsbp = newSubNeg((fromRange.hi() - width + 1), rhsp);
                } else {
                    // SELPLUS(from,lsb,width) -> SEL(from, lsb-vector_lsb, width)
                    newlsbp = newSubNeg(rhsp, fromRange.lo());
                }
            } else if (VN_IS(nodep, SelMinus)) {
                if (fromRange.ascending()) {
                    // SELMINUS(from,msb,width) -> SEL(from, msb-[bit])
                    newlsbp = newSubNeg(fromRange.hi(), rhsp);
                } else {
                    // SELMINUS(from,msb,width) -> SEL(from, msb-(width-1)-lsb#)
                    newlsbp = newSubNeg(rhsp, fromRange.lo() + (width - 1));
                }
            } else {
                nodep->v3fatalSrc("Bad Case");
            }
            if (elwidth != 1) newlsbp = newMulConst(nodep->fileline(), elwidth, newlsbp);
            AstSel* const newp = new AstSel{nodep->fileline(), fromp, newlsbp, newwidth};
            newp->declRange(fromRange);
            newp->declElWidth(elwidth);
            UINFO(6, "   new " << newp);
            if (debug() >= 9) newp->dumpTree("-  SELNEW: ");
            nodep->replaceWith(newp);
            VL_DO_DANGLING(pushDeletep(nodep), nodep);
        } else {  // nullptr=bad extract, or unknown node type
            nodep->v3error("Illegal +: or -: select; type already selected, or bad dimension: "
                           << "data type is " << fromdata.m_errp->prettyDTypeNameQ());
            // How to recover?  We'll strip a dimension.
            nodep->replaceWith(fromp);
            VL_DO_DANGLING(pushDeletep(nodep), nodep);
        }
        // delete whatever we didn't use in reconstruction
        if (!fromp->backp()) VL_DO_DANGLING(pushDeletep(fromp), fromp);
        if (!rhsp->backp()) VL_DO_DANGLING(pushDeletep(rhsp), rhsp);
        if (!widthp->backp()) VL_DO_DANGLING(pushDeletep(widthp), widthp);
    }
    void visit(AstSelPlus* nodep) override { replaceSelPlusMinus(nodep); }
    void visit(AstSelMinus* nodep) override { replaceSelPlusMinus(nodep); }
    // If adding new visitors, ensure V3Width's visit(TYPE) calls into here

    //--------------------
    // Default
    void visit(AstNode* nodep) override {  // LCOV_EXCL_LINE
        // See notes above; we never iterate
        nodep->v3fatalSrc("Shouldn't iterate in V3WidthSel");
    }

public:
    // CONSTRUCTORS
    WidthSelVisitor() = default;
    ~WidthSelVisitor() override = default;
    AstNode* mainAcceptEdit(AstNode* nodep) { return iterateSubtreeReturnEdits(nodep); }
};

//######################################################################
// Width class functions

AstNode* V3Width::widthSelNoIterEdit(AstNode* nodep) {
    UINFO(4, __FUNCTION__ << ": " << nodep);
    WidthSelVisitor visitor;
    nodep = visitor.mainAcceptEdit(nodep);
    return nodep;
}

#undef iterateChildren
