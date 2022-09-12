// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Expression width calculations
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
// V3Width's Transformations:
//      Top down traversal:
//          Determine width of sub-expressions
//              width() = # bits upper expression wants, 0 for anything-goes
//              widthUnsized() = # bits for unsized constant, or 0 if it's sized
//              widthMin() = Alternative acceptable width for linting, or width() if sized
//              Determine this subop's width, can be either:
//                  Fixed width X
//                  Unsized, min width X   ('d5 is unsized, min 3 bits.)
//              Pass up:
//                  width() = # bits this expression generates
//                  widthSized() = true if all constants sized, else false
//          Compute size of this expression
//          Lint warn about mismatches
//              If expr size != subop fixed, bad
//              If expr size  < subop unsized minimum, bad
//              If expr size != subop, edit netlist
//                      For == and similar ops, if multibit underneath, add a REDOR
//                      If subop larger, add a EXTRACT
//                      If subop smaller, add a EXTEND
//          Pass size to sub-expressions if required (+/-* etc)
//              FINAL = true.
//              Subexpressions lint and extend as needed
//
//*************************************************************************
// Signedness depends on:
//      Decimal numbers are signed
//      Based numbers are unsigned unless 's' prefix
//      Comparison results are unsigned
//      Bit&Part selects are unsigned, even if whole
//      Concatenates are unsigned
//      Ignore signedness of self-determined:
//              shift rhs, ** rhs, x?: lhs, concat and replicate members
//      Else, if any operand unsigned, output unsigned
//
// Real number rules:
//      Real numbers are real (duh)
//      Reals convert to integers by rounding
//      Reals init to 0.0
//      Logicals convert compared to zero
//      If any operand is real, result is real
//*************************************************************************
// V3Width is the only visitor that uses vup.  We could switch to using userp,
// though note some iterators operate on next() and so would need to pass the
// same value on each nextp().
//*************************************************************************
// See notes in internal.txt about misuse of iterateAndNext and use of
// iterateSubtreeReturnEdits.
//*************************************************************************

#include "config_build.h"
#include "verilatedos.h"

#include "V3Width.h"

#include "V3Const.h"
#include "V3Global.h"
#include "V3Number.h"
#include "V3Randomize.h"
#include "V3String.h"
#include "V3Task.h"

#include <algorithm>

// More code; this file was getting too large; see actions there
#define VERILATOR_V3WIDTH_CPP_
#include "V3WidthCommit.h"

//######################################################################

enum Stage : uint8_t {
    PRELIM = 1,
    FINAL = 2,
    BOTH = 3
};  // Numbers are a bitmask <0>=prelim, <1>=final
std::ostream& operator<<(std::ostream& str, const Stage& rhs) {
    return str << ("-PFB"[static_cast<int>(rhs)]);
}

enum Determ : uint8_t {
    SELF,  // Self-determined
    CONTEXT,  // Context-determined
    ASSIGN  // Assignment-like where sign comes from RHS only
};
std::ostream& operator<<(std::ostream& str, const Determ& rhs) {
    static const char* const s_det[] = {"SELF", "CNTX", "ASSN"};
    return str << s_det[rhs];
}

enum Castable : uint8_t {
    UNSUPPORTED,
    COMPATIBLE,
    ENUM_EXPLICIT,
    ENUM_IMPLICIT,
    DYNAMIC_CLASS,
    INCOMPATIBLE
};
std::ostream& operator<<(std::ostream& str, const Castable& rhs) {
    static const char* const s_det[]
        = {"UNSUP", "COMPAT", "ENUM_EXP", "ENUM_IMP", "DYN_CLS", "INCOMPAT"};
    return str << s_det[rhs];
}

//######################################################################
// Width state, as a visitor of each AstNode

class WidthVP final {
    // Parameters to pass down hierarchy with visit functions.
    AstNodeDType* const m_dtypep;  // Parent's data type to resolve to
    const Stage m_stage;  // If true, report errors
public:
    WidthVP(AstNodeDType* dtypep, Stage stage)
        : m_dtypep{dtypep}
        , m_stage{stage} {
        // Prelim doesn't look at assignments, so shouldn't need a dtype,
        // however AstPattern uses them
    }
    WidthVP(Determ determ, Stage stage)
        : m_dtypep{nullptr}
        , m_stage{stage} {
        if (determ != SELF && stage != PRELIM)
            v3fatalSrc("Context-determined width request only allowed as prelim step");
    }
    WidthVP* p() { return this; }
    bool selfDtm() const { return m_dtypep == nullptr; }
    AstNodeDType* dtypep() const {
        // Detect where overrideDType is probably the intended call
        if (!m_dtypep) v3fatalSrc("Width dtype request on self-determined or preliminary VUP");
        return m_dtypep;
    }
    AstNodeDType* dtypeNullp() const { return m_dtypep; }
    AstNodeDType* dtypeNullSkipRefp() const {
        AstNodeDType* dtp = dtypeNullp();
        if (dtp) dtp = dtp->skipRefp();
        return dtp;
    }
    AstNodeDType* dtypeOverridep(AstNodeDType* defaultp) const {
        if (m_stage == PRELIM) v3fatalSrc("Parent dtype should be a final-stage action");
        return m_dtypep ? m_dtypep : defaultp;
    }
    int width() const {
        if (!m_dtypep) v3fatalSrc("Width request on self-determined or preliminary VUP");
        return m_dtypep->width();
    }
    int widthMin() const {
        if (!m_dtypep) v3fatalSrc("Width request on self-determined or preliminary VUP");
        return m_dtypep->widthMin();
    }
    bool prelim() const { return m_stage & PRELIM; }
    bool final() const { return m_stage & FINAL; }
    void dump(std::ostream& str) const {
        if (!m_dtypep) {
            str << "  VUP(s=" << m_stage << ",self)";
        } else {
            str << "  VUP(s=" << m_stage << ",dt=" << cvtToHex(dtypep());
            dtypep()->dumpSmall(str);
            str << ")";
        }
    }
};
std::ostream& operator<<(std::ostream& str, const WidthVP* vup) {
    if (vup) vup->dump(str);
    return str;
}

//######################################################################

class WidthClearVisitor final {
    // Rather than a VNVisitor, can just quickly touch every node
    void clearWidthRecurse(AstNode* nodep) {
        for (; nodep; nodep = nodep->nextp()) {
            nodep->didWidth(false);
            if (nodep->op1p()) clearWidthRecurse(nodep->op1p());
            if (nodep->op2p()) clearWidthRecurse(nodep->op2p());
            if (nodep->op3p()) clearWidthRecurse(nodep->op3p());
            if (nodep->op4p()) clearWidthRecurse(nodep->op4p());
        }
    }

public:
    // CONSTRUCTORS
    explicit WidthClearVisitor(AstNetlist* nodep) { clearWidthRecurse(nodep); }
    virtual ~WidthClearVisitor() = default;
};

//######################################################################

#define accept in_WidthVisitor_use_AstNode_iterate_instead_of_AstNode_accept

//######################################################################

class WidthVisitor final : public VNVisitor {
private:
    // TYPES
    using TableMap = std::map<std::pair<const AstNodeDType*, VAttrType>, AstVar*>;
    using PatVecMap = std::map<int, AstPatMember*>;
    using DTypeMap = std::map<const std::string, AstPatMember*>;

    // STATE
    WidthVP* m_vup = nullptr;  // Current node state
    const AstCell* m_cellp = nullptr;  // Current cell for arrayed instantiations
    const AstNodeFTask* m_ftaskp = nullptr;  // Current function/task
    const AstNodeProcedure* m_procedurep = nullptr;  // Current final/always
    const AstWith* m_withp = nullptr;  // Current 'with' statement
    const AstFunc* m_funcp = nullptr;  // Current function
    const AstAttrOf* m_attrp = nullptr;  // Current attribute
    const bool m_paramsOnly;  // Computing parameter value; limit operation
    const bool m_doGenerate;  // Do errors later inside generate statement
    int m_dtTables = 0;  // Number of created data type tables
    TableMap m_tableMap;  // Created tables so can remove duplicates
    std::map<const AstNodeDType*, AstQueueDType*>
        m_queueDTypeIndexed;  // Queues with given index type

    static constexpr int ENUM_LOOKUP_BITS = 16;  // Maximum # bits to make enum lookup table

    // ENUMS
    enum ExtendRule : uint8_t {
        EXTEND_EXP,  // Extend if expect sign and node signed, e.g. node=y in ADD(x,y), "x + y"
        EXTEND_ZERO,  // Extend with zeros. e.g. node=y in EQ(x,y), "x == y"
        EXTEND_LHS,  // Extend with sign if node signed. e.g. node=y in ASSIGN(y,x), "x = y"
        EXTEND_OFF  // No extension
    };

    // METHODS
    static int debug() { return V3Width::debug(); }

    // VISITORS
    //   Naming:  width_O{outputtype}_L{lhstype}_R{rhstype}_W{widthing}_S{signing}
    //          Where type:
    //                  _O1=boolean (width 1 unsigned)
    //                  _Ou=unsigned
    //                  _Os=signed
    //                  _Ous=unsigned or signed
    //                  _Or=real
    //                  _Ox=anything

    // Widths: 1 bit out, lhs 1 bit; Real: converts via compare with 0
    virtual void visit(AstLogNot* nodep) override { visit_log_not(nodep); }
    // Widths: 1 bit out, lhs 1 bit, rhs 1 bit; Real: converts via compare with 0
    virtual void visit(AstLogAnd* nodep) override { visit_log_and_or(nodep); }
    virtual void visit(AstLogOr* nodep) override { visit_log_and_or(nodep); }
    virtual void visit(AstLogEq* nodep) override {
        // Conversion from real not in IEEE, but a fallout
        visit_log_and_or(nodep);
    }
    virtual void visit(AstLogIf* nodep) override {
        // Conversion from real not in IEEE, but a fallout
        visit_log_and_or(nodep);
    }

    // Widths: 1 bit out, Any width lhs
    virtual void visit(AstRedAnd* nodep) override { visit_red_and_or(nodep); }
    virtual void visit(AstRedOr* nodep) override { visit_red_and_or(nodep); }
    virtual void visit(AstRedXor* nodep) override { visit_red_and_or(nodep); }
    virtual void visit(AstOneHot* nodep) override { visit_red_and_or(nodep); }
    virtual void visit(AstOneHot0* nodep) override { visit_red_and_or(nodep); }
    virtual void visit(AstIsUnknown* nodep) override {
        visit_red_unknown(nodep);  // Allow real
    }

    // These have different node types, as they operate differently
    // Must add to case statement below,
    // Widths: 1 bit out, lhs width == rhs width.  real if lhs|rhs real
    virtual void visit(AstEq* nodep) override { visit_cmp_eq_gt(nodep, true); }
    virtual void visit(AstNeq* nodep) override { visit_cmp_eq_gt(nodep, true); }
    virtual void visit(AstGt* nodep) override { visit_cmp_eq_gt(nodep, true); }
    virtual void visit(AstGte* nodep) override { visit_cmp_eq_gt(nodep, true); }
    virtual void visit(AstLt* nodep) override { visit_cmp_eq_gt(nodep, true); }
    virtual void visit(AstLte* nodep) override { visit_cmp_eq_gt(nodep, true); }
    virtual void visit(AstGtS* nodep) override { visit_cmp_eq_gt(nodep, true); }
    virtual void visit(AstGteS* nodep) override { visit_cmp_eq_gt(nodep, true); }
    virtual void visit(AstLtS* nodep) override { visit_cmp_eq_gt(nodep, true); }
    virtual void visit(AstLteS* nodep) override { visit_cmp_eq_gt(nodep, true); }
    virtual void visit(AstEqCase* nodep) override { visit_cmp_eq_gt(nodep, true); }
    virtual void visit(AstNeqCase* nodep) override { visit_cmp_eq_gt(nodep, true); }
    // ...    These comparisons don't allow reals
    virtual void visit(AstEqWild* nodep) override { visit_cmp_eq_gt(nodep, false); }
    virtual void visit(AstNeqWild* nodep) override { visit_cmp_eq_gt(nodep, false); }
    // ...    Real compares
    virtual void visit(AstEqD* nodep) override { visit_cmp_real(nodep); }
    virtual void visit(AstNeqD* nodep) override { visit_cmp_real(nodep); }
    virtual void visit(AstLtD* nodep) override { visit_cmp_real(nodep); }
    virtual void visit(AstLteD* nodep) override { visit_cmp_real(nodep); }
    virtual void visit(AstGtD* nodep) override { visit_cmp_real(nodep); }
    virtual void visit(AstGteD* nodep) override { visit_cmp_real(nodep); }
    // ...    String compares
    virtual void visit(AstEqN* nodep) override { visit_cmp_string(nodep); }
    virtual void visit(AstNeqN* nodep) override { visit_cmp_string(nodep); }
    virtual void visit(AstLtN* nodep) override { visit_cmp_string(nodep); }
    virtual void visit(AstLteN* nodep) override { visit_cmp_string(nodep); }
    virtual void visit(AstGtN* nodep) override { visit_cmp_string(nodep); }
    virtual void visit(AstGteN* nodep) override { visit_cmp_string(nodep); }

    // Widths: out width = lhs width = rhs width
    // Signed: Output signed iff LHS & RHS signed.
    // Real: Not allowed
    virtual void visit(AstAnd* nodep) override { visit_boolmath_and_or(nodep); }
    virtual void visit(AstOr* nodep) override { visit_boolmath_and_or(nodep); }
    virtual void visit(AstXor* nodep) override { visit_boolmath_and_or(nodep); }
    virtual void visit(AstBufIf1* nodep) override {
        visit_boolmath_and_or(nodep);
    }  // Signed behavior changing in 3.814
    // Width: Max(Lhs,Rhs) sort of.
    // Real: If either side real
    // Signed: If both sides real
    virtual void visit(AstAdd* nodep) override { visit_add_sub_replace(nodep, true); }
    virtual void visit(AstSub* nodep) override { visit_add_sub_replace(nodep, true); }
    virtual void visit(AstDiv* nodep) override { visit_add_sub_replace(nodep, true); }
    virtual void visit(AstMul* nodep) override { visit_add_sub_replace(nodep, true); }
    // These can't promote to real
    virtual void visit(AstModDiv* nodep) override { visit_add_sub_replace(nodep, false); }
    virtual void visit(AstModDivS* nodep) override { visit_add_sub_replace(nodep, false); }
    virtual void visit(AstMulS* nodep) override { visit_add_sub_replace(nodep, false); }
    virtual void visit(AstDivS* nodep) override { visit_add_sub_replace(nodep, false); }
    // Widths: out width = lhs width, but upper matters
    // Signed: Output signed iff LHS signed; unary operator
    // Unary promote to real
    virtual void visit(AstNegate* nodep) override { visit_negate_not(nodep, true); }
    // Unary never real
    virtual void visit(AstNot* nodep) override { visit_negate_not(nodep, false); }

    // Real: inputs and output real
    virtual void visit(AstAddD* nodep) override { visit_real_add_sub(nodep); }
    virtual void visit(AstSubD* nodep) override { visit_real_add_sub(nodep); }
    virtual void visit(AstDivD* nodep) override { visit_real_add_sub(nodep); }
    virtual void visit(AstMulD* nodep) override { visit_real_add_sub(nodep); }
    virtual void visit(AstPowD* nodep) override { visit_real_add_sub(nodep); }
    virtual void visit(AstNodeSystemBiop* nodep) override { visit_real_add_sub(nodep); }
    // Real: Output real
    virtual void visit(AstNegateD* nodep) override { visit_real_neg_ceil(nodep); }
    virtual void visit(AstNodeSystemUniop* nodep) override { visit_real_neg_ceil(nodep); }

    // Widths: out signed/unsigned width = lhs width, input un|signed
    virtual void visit(AstSigned* nodep) override {
        visit_signed_unsigned(nodep, VSigning::SIGNED);
    }
    virtual void visit(AstUnsigned* nodep) override {
        visit_signed_unsigned(nodep, VSigning::UNSIGNED);
    }

    // Widths: Output width from lhs, rhs<33 bits
    // Signed: If lhs signed
    virtual void visit(AstShiftL* nodep) override { visit_shift(nodep); }
    virtual void visit(AstShiftR* nodep) override { visit_shift(nodep); }
    // ShiftRS converts to ShiftR, but not vice-versa
    virtual void visit(AstShiftRS* nodep) override { visit_shift(nodep); }

    //========
    // Widths: Output real, input integer signed
    virtual void visit(AstBitsToRealD* nodep) override { visit_Or_Lu64(nodep); }

    // Widths: Output integer signed, input real
    virtual void visit(AstRToIS* nodep) override { visit_Os32_Lr(nodep); }
    virtual void visit(AstRToIRoundS* nodep) override {
        // Only created here, size comes from upper expression
        if (m_vup->prelim()) {  // First stage evaluation
            iterateCheckReal(nodep, "LHS", nodep->lhsp(), BOTH);
        }
        if (!nodep->dtypep()->widthSized()) nodep->v3fatalSrc("RToIRoundS should be presized");
    }

    // Widths: Output integer unsigned, input real
    virtual void visit(AstRealToBits* nodep) override { visit_Ou64_Lr(nodep); }

    // Output integer, input string
    virtual void visit(AstLenN* nodep) override { visit_Os32_string(nodep); }
    virtual void visit(AstPutcN* nodep) override {
        // CALLER: str.putc()
        UASSERT_OBJ(nodep->rhsp() && nodep->thsp(), nodep, "For ternary ops only!");
        if (m_vup && m_vup->prelim()) {
            // See similar handling in visit_cmp_eq_gt where created
            iterateCheckString(nodep, "LHS", nodep->lhsp(), BOTH);
            iterateCheckSigned32(nodep, "RHS", nodep->rhsp(), BOTH);
            iterateCheckSigned32(nodep, "THS", nodep->thsp(), BOTH);
            nodep->dtypeSetString();  // AstPutcN returns the new string to be assigned by
                                      // AstAssign
        }
    }
    virtual void visit(AstGetcN* nodep) override {
        // CALLER: str.getc()
        UASSERT_OBJ(nodep->rhsp(), nodep, "For binary ops only!");
        if (m_vup && m_vup->prelim()) {
            // See similar handling in visit_cmp_eq_gt where created
            iterateCheckString(nodep, "LHS", nodep->lhsp(), BOTH);
            iterateCheckSigned32(nodep, "RHS", nodep->rhsp(), BOTH);
            nodep->dtypeSetBitSized(8, VSigning::UNSIGNED);
        }
    }
    virtual void visit(AstGetcRefN* nodep) override {
        // CALLER: str.getc()
        UASSERT_OBJ(nodep->rhsp(), nodep, "For binary ops only!");
        if (m_vup && m_vup->prelim()) {
            // See similar handling in visit_cmp_eq_gt where created
            iterateCheckString(nodep, "LHS", nodep->lhsp(), BOTH);
            iterateCheckSigned32(nodep, "RHS", nodep->rhsp(), BOTH);
            nodep->dtypeSetBitSized(8, VSigning::UNSIGNED);
        }
    }
    virtual void visit(AstSubstrN* nodep) override {
        // CALLER: str.substr()
        UASSERT_OBJ(nodep->rhsp() && nodep->thsp(), nodep, "For ternary ops only!");
        if (m_vup && m_vup->prelim()) {
            // See similar handling in visit_cmp_eq_gt where created
            iterateCheckString(nodep, "LHS", nodep->lhsp(), BOTH);
            iterateCheckSigned32(nodep, "RHS", nodep->rhsp(), BOTH);
            iterateCheckSigned32(nodep, "THS", nodep->thsp(), BOTH);
            nodep->dtypeSetString();
        }
    }
    virtual void visit(AstCompareNN* nodep) override {
        // CALLER: str.compare(), str.icompare()
        // Widths: 32 bit out
        UASSERT_OBJ(nodep->rhsp(), nodep, "For binary ops only!");
        if (m_vup->prelim()) {
            // See similar handling in visit_cmp_eq_gt where created
            iterateCheckString(nodep, "LHS", nodep->lhsp(), BOTH);
            iterateCheckString(nodep, "RHS", nodep->rhsp(), BOTH);
            nodep->dtypeSetSigned32();
        }
    }
    virtual void visit(AstAtoN* nodep) override {
        // CALLER: str.atobin(), atoi(), atohex(), atooct(), atoreal()
        // Width: 64bit floating point for atoreal(), 32bit out for the others
        if (m_vup->prelim()) {
            // See similar handling in visit_cmp_eq_gt where created
            iterateCheckString(nodep, "LHS", nodep->lhsp(), BOTH);
            if (nodep->format() == AstAtoN::ATOREAL) {
                nodep->dtypeSetDouble();
            } else {
                nodep->dtypeSetSigned32();
            }
        }
    }

    // Widths: Constant, terminal
    virtual void visit(AstTime* nodep) override { nodep->dtypeSetUInt64(); }
    virtual void visit(AstTimeD* nodep) override { nodep->dtypeSetDouble(); }
    virtual void visit(AstScopeName* nodep) override {
        nodep->dtypeSetUInt64();  // A pointer, but not that it matters
    }

    virtual void visit(AstNodeCond* nodep) override {
        // op = cond ? expr1 : expr2
        // See IEEE-2012 11.4.11 and Table 11-21.
        //   LHS is self-determined
        //   Width: max(RHS, THS)
        //   Signed: Output signed iff RHS & THS signed  (presumed, not in IEEE)
        //   Real: Output real if either expression is real, non-real argument gets converted
        if (m_vup->prelim()) {  // First stage evaluation
            // Just once, do the conditional, expect one bit out.
            iterateCheckBool(nodep, "Conditional Test", nodep->condp(), BOTH);
            // Determine sub expression widths only relying on what's in the subops
            //  CONTEXT determined, but need data type for pattern assignments
            userIterateAndNext(nodep->expr1p(), WidthVP(m_vup->dtypeNullp(), PRELIM).p());
            userIterateAndNext(nodep->expr2p(), WidthVP(m_vup->dtypeNullp(), PRELIM).p());
            // Calculate width of this expression.
            // First call (prelim()) m_vup->width() is probably zero, so we'll return
            //  the size of this subexpression only.
            // Second call (final()) m_vup->width() is probably the expression size, so
            //  the expression includes the size of the output too.
            if (nodep->expr1p()->isDouble() || nodep->expr2p()->isDouble()) {
                nodep->dtypeSetDouble();
            } else if (nodep->expr1p()->isString() || nodep->expr2p()->isString()) {
                nodep->dtypeSetString();
            } else {
                const int width = std::max(nodep->expr1p()->width(), nodep->expr2p()->width());
                const int mwidth
                    = std::max(nodep->expr1p()->widthMin(), nodep->expr2p()->widthMin());
                const bool issigned = nodep->expr1p()->isSigned() && nodep->expr2p()->isSigned();
                nodep->dtypeSetLogicUnsized(width, mwidth, VSigning::fromBool(issigned));
            }
        }
        if (m_vup->final()) {
            AstNodeDType* const expDTypep = m_vup->dtypeOverridep(nodep->dtypep());
            AstNodeDType* const subDTypep = expDTypep;
            nodep->dtypeFrom(expDTypep);
            // Error report and change sizes for suboperands of this node.
            iterateCheck(nodep, "Conditional True", nodep->expr1p(), CONTEXT, FINAL, subDTypep,
                         EXTEND_EXP);
            iterateCheck(nodep, "Conditional False", nodep->expr2p(), CONTEXT, FINAL, subDTypep,
                         EXTEND_EXP);
        }
    }
    virtual void visit(AstConcat* nodep) override {
        // Real: Not allowed (assumed)
        // Signed: unsigned output, input either (assumed)
        // IEEE-2012 Table 11-21, and 11.8.1:
        //   LHS, RHS is self-determined
        //   signed: Unsigned  (11.8.1)
        //   width: LHS + RHS
        AstNodeDType* const vdtypep = m_vup->dtypeNullSkipRefp();
        userIterate(vdtypep, WidthVP(SELF, BOTH).p());
        // Conversions
        if (VN_IS(vdtypep, QueueDType)) {
            // Queue "element 0" is lhsp, so we need to swap arguments
            auto* const newp = new AstConsQueue(nodep->fileline(), nodep->rhsp()->unlinkFrBack(),
                                                nodep->lhsp()->unlinkFrBack());
            nodep->replaceWith(newp);
            VL_DO_DANGLING(pushDeletep(nodep), nodep);
            userIterateChildren(newp, m_vup);
            return;
        }
        if (VN_IS(vdtypep, DynArrayDType)) {
            auto* const newp = new AstConsDynArray(
                nodep->fileline(), nodep->rhsp()->unlinkFrBack(), nodep->lhsp()->unlinkFrBack());
            nodep->replaceWith(newp);
            VL_DO_DANGLING(pushDeletep(nodep), nodep);
            userIterateChildren(newp, m_vup);
            return;
        }
        if (VN_IS(vdtypep, UnpackArrayDType)) {
            auto* const newp = new AstPattern{nodep->fileline(), nullptr};
            patConcatConvertRecurse(newp, nodep);
            nodep->replaceWith(newp);
            VL_DO_DANGLING(pushDeletep(nodep), nodep);
            userIterate(newp, m_vup);
            return;
        }

        // Concat handling
        if (m_vup->prelim()) {
            if (VN_IS(vdtypep, AssocArrayDType)  //
                || VN_IS(vdtypep, DynArrayDType)  //
                || VN_IS(vdtypep, QueueDType)) {
                nodep->v3warn(E_UNSUPPORTED, "Unsupported: Concatenation to form "
                                                 << vdtypep->prettyDTypeNameQ() << " data type");
            }

            iterateCheckSizedSelf(nodep, "LHS", nodep->lhsp(), SELF, BOTH);
            iterateCheckSizedSelf(nodep, "RHS", nodep->rhsp(), SELF, BOTH);
            nodep->dtypeSetLogicUnsized(nodep->lhsp()->width() + nodep->rhsp()->width(),
                                        nodep->lhsp()->widthMin() + nodep->rhsp()->widthMin(),
                                        VSigning::UNSIGNED);
            // Cleanup zero width Verilog2001 {x,{0{foo}}} now,
            // otherwise having width(0) will cause later assertions to fire
            if (const AstReplicate* const repp = VN_CAST(nodep->lhsp(), Replicate)) {
                if (repp->width() == 0) {  // Keep rhs
                    nodep->replaceWith(nodep->rhsp()->unlinkFrBack());
                    VL_DO_DANGLING(pushDeletep(nodep), nodep);
                    return;
                }
            }
            if (const AstReplicate* const repp = VN_CAST(nodep->rhsp(), Replicate)) {
                if (repp->width() == 0) {  // Keep lhs
                    nodep->replaceWith(nodep->lhsp()->unlinkFrBack());
                    VL_DO_DANGLING(pushDeletep(nodep), nodep);
                    return;
                }
            }
        }
        if (m_vup->final()) {
            if (nodep->lhsp()->isString() || nodep->rhsp()->isString()) {
                AstNode* const newp
                    = new AstConcatN(nodep->fileline(), nodep->lhsp()->unlinkFrBack(),
                                     nodep->rhsp()->unlinkFrBack());
                nodep->replaceWith(newp);
                VL_DO_DANGLING(pushDeletep(nodep), nodep);
                return;
            }
            if (!nodep->dtypep()->widthSized()) {
                // See also error in V3Number
                nodeForUnsizedWarning(nodep)->v3warn(
                    WIDTHCONCAT, "Unsized numbers/parameters not allowed in concatenations.");
            }
        }
    }
    virtual void visit(AstConcatN* nodep) override {
        // String concatenate.
        // Already did AstConcat simplifications
        if (m_vup->prelim()) {
            iterateCheckString(nodep, "LHS", nodep->lhsp(), BOTH);
            iterateCheckString(nodep, "RHS", nodep->rhsp(), BOTH);
            nodep->dtypeSetString();
        }
        if (m_vup->final()) {
            if (!nodep->dtypep()->widthSized()) {
                // See also error in V3Number
                nodeForUnsizedWarning(nodep)->v3warn(
                    WIDTHCONCAT, "Unsized numbers/parameters not allowed in concatenations.");
            }
        }
    }
    virtual void visit(AstDelay* nodep) override {
        if (VN_IS(m_procedurep, Final)) {
            nodep->v3error("Delays are not legal in final blocks (IEEE 1800-2017 9.2.3)");
            VL_DO_DANGLING(pushDeletep(nodep->unlinkFrBack()), nodep);
            return;
        }
        if (VN_IS(m_ftaskp, Func)) {
            nodep->v3error("Delays are not legal in functions. Suggest use a task "
                           "(IEEE 1800-2017 13.4.4)");
            VL_DO_DANGLING(pushDeletep(nodep->unlinkFrBack()), nodep);
            return;
        }
        if (nodep->stmtsp()) nodep->addNextHere(nodep->stmtsp()->unlinkFrBack());
        nodep->v3warn(STMTDLY, "Unsupported: Ignoring delay on this delayed statement.");
        VL_DO_DANGLING(pushDeletep(nodep->unlinkFrBack()), nodep);
    }
    virtual void visit(AstFork* nodep) override {
        if (VN_IS(m_ftaskp, Func) && !nodep->joinType().joinNone()) {
            nodep->v3error("Only fork .. join_none is legal in functions. "
                           "(IEEE 1800-2017 13.4.4)");
            VL_DO_DANGLING(pushDeletep(nodep->unlinkFrBack()), nodep);
            return;
        }
        if (v3Global.opt.bboxUnsup()
            // With no statements, begin is identical
            || !nodep->stmtsp()
            // With one statement, a begin block does as good as a fork/join or join_any
            || (!nodep->stmtsp()->nextp() && !nodep->joinType().joinNone())) {
            AstNode* stmtsp = nullptr;
            if (nodep->stmtsp()) stmtsp = nodep->stmtsp()->unlinkFrBack();
            AstBegin* const newp = new AstBegin{nodep->fileline(), nodep->name(), stmtsp};
            nodep->replaceWith(newp);
            VL_DO_DANGLING(nodep->deleteTree(), nodep);
        } else {
            nodep->v3warn(E_UNSUPPORTED, "Unsupported: fork statements");
            // TBD might support only normal join, if so complain about other join flavors
        }
    }
    virtual void visit(AstDisableFork* nodep) override {
        nodep->v3warn(E_UNSUPPORTED, "Unsupported: disable fork statements");
        VL_DO_DANGLING(nodep->unlinkFrBack()->deleteTree(), nodep);
    }
    virtual void visit(AstWaitFork* nodep) override {
        nodep->v3warn(E_UNSUPPORTED, "Unsupported: wait fork statements");
        VL_DO_DANGLING(nodep->unlinkFrBack()->deleteTree(), nodep);
    }
    virtual void visit(AstToLowerN* nodep) override {
        if (m_vup->prelim()) {
            iterateCheckString(nodep, "LHS", nodep->lhsp(), BOTH);
            nodep->dtypeSetString();
        }
    }
    virtual void visit(AstToUpperN* nodep) override {
        if (m_vup->prelim()) {
            iterateCheckString(nodep, "LHS", nodep->lhsp(), BOTH);
            nodep->dtypeSetString();
        }
    }
    virtual void visit(AstReplicate* nodep) override {
        // IEEE-2012 Table 11-21:
        //   LHS, RHS is self-determined
        //   width: value(LHS) * width(RHS)
        if (m_vup->prelim()) {
            iterateCheckSizedSelf(nodep, "RHS", nodep->rhsp(), SELF, BOTH);
            V3Const::constifyParamsEdit(nodep->rhsp());  // rhsp may change
            const AstConst* const constp = VN_CAST(nodep->rhsp(), Const);
            if (!constp) {
                nodep->v3error("Replication value isn't a constant.");
                return;
            }
            uint32_t times = constp->toUInt();
            if (times == 0
                && !VN_IS(nodep->backp(), Concat)) {  // Concat Visitor will clean it up.
                nodep->v3error("Replication value of 0 is only legal under a concatenation (IEEE "
                               "1800-2017 11.4.12.1)");
                times = 1;
            }

            AstNodeDType* const vdtypep = m_vup->dtypeNullSkipRefp();
            if (VN_IS(vdtypep, QueueDType) || VN_IS(vdtypep, DynArrayDType)
                || VN_IS(vdtypep, UnpackArrayDType)) {
                if (times != 1) {
                    nodep->v3warn(E_UNSUPPORTED, "Unsupported: Non-1 replication to form "
                                                     << vdtypep->prettyDTypeNameQ()
                                                     << " data type");
                }
                // Don't iterate lhsp as SELF, the potential Concat below needs
                // the adtypep passed down to recognize the QueueDType
                userIterateAndNext(nodep->lhsp(), WidthVP(vdtypep, BOTH).p());
                nodep->replaceWith(nodep->lhsp()->unlinkFrBack());
                VL_DO_DANGLING(pushDeletep(nodep), nodep);
                return;
            }
            if (VN_IS(vdtypep, AssocArrayDType)) {
                nodep->v3warn(E_UNSUPPORTED, "Unsupported: Replication to form "
                                                 << vdtypep->prettyDTypeNameQ() << " data type");
            }
            iterateCheckSizedSelf(nodep, "LHS", nodep->lhsp(), SELF, BOTH);
            if (nodep->lhsp()->isString()) {
                AstNode* const newp
                    = new AstReplicateN(nodep->fileline(), nodep->lhsp()->unlinkFrBack(),
                                        nodep->rhsp()->unlinkFrBack());
                nodep->replaceWith(newp);
                VL_DO_DANGLING(pushDeletep(nodep), nodep);
                return;
            } else {
                nodep->dtypeSetLogicUnsized((nodep->lhsp()->width() * times),
                                            (nodep->lhsp()->widthMin() * times),
                                            VSigning::UNSIGNED);
            }
        }
        if (m_vup->final()) {
            if (!nodep->dtypep()->widthSized()) {
                // See also error in V3Number
                nodeForUnsizedWarning(nodep)->v3warn(
                    WIDTHCONCAT, "Unsized numbers/parameters not allowed in replications.");
            }
        }
    }
    virtual void visit(AstReplicateN* nodep) override {
        // Replicate with string
        if (m_vup->prelim()) {
            iterateCheckString(nodep, "LHS", nodep->lhsp(), BOTH);
            iterateCheckSizedSelf(nodep, "RHS", nodep->rhsp(), SELF, BOTH);
            V3Const::constifyParamsEdit(nodep->rhsp());  // rhsp may change
            const AstConst* const constp = VN_CAST(nodep->rhsp(), Const);
            if (!constp) {
                nodep->v3error("Replication value isn't a constant.");
                return;
            }
            const uint32_t times = constp->toUInt();
            if (times == 0
                && !VN_IS(nodep->backp(), Concat)) {  // Concat Visitor will clean it up.
                nodep->v3error("Replication value of 0 is only legal under a concatenation (IEEE "
                               "1800-2017 11.4.12.1)");
            }
            nodep->dtypeSetString();
        }
        if (m_vup->final()) {
            if (!nodep->dtypep()->widthSized()) {
                // See also error in V3Number
                nodeForUnsizedWarning(nodep)->v3warn(
                    WIDTHCONCAT, "Unsized numbers/parameters not allowed in replications.");
            }
        }
    }
    virtual void visit(AstNodeStream* nodep) override {
        if (m_vup->prelim()) {
            iterateCheckSizedSelf(nodep, "LHS", nodep->lhsp(), SELF, BOTH);
            iterateCheckSizedSelf(nodep, "RHS", nodep->rhsp(), SELF, BOTH);
            V3Const::constifyParamsEdit(nodep->rhsp());  // rhsp may change
            const AstConst* const constp = VN_CAST(nodep->rhsp(), Const);
            AstBasicDType* const basicp = VN_CAST(nodep->rhsp(), BasicDType);
            if (!constp && !basicp) {
                nodep->v3error("Slice size isn't a constant or basic data type.");
                return;
            }
            if (basicp) {  // Convert data type to a constant size
                AstConst* const newp = new AstConst(basicp->fileline(), basicp->width());
                nodep->rhsp()->replaceWith(newp);
                pushDeletep(basicp);
            } else {
                const uint32_t sliceSize = constp->toUInt();
                if (!sliceSize) {
                    nodep->v3error("Slice size cannot be zero.");
                    return;
                }
            }
            nodep->dtypeSetLogicUnsized(nodep->lhsp()->width(), nodep->lhsp()->widthMin(),
                                        VSigning::UNSIGNED);
        }
        if (m_vup->final()) {
            if (!nodep->dtypep()->widthSized()) {
                // See also error in V3Number
                nodeForUnsizedWarning(nodep)->v3warn(
                    WIDTHCONCAT, "Unsized numbers/parameters not allowed in streams.");
            }
        }
    }
    virtual void visit(AstRange* nodep) override {
        // Real: Not allowed
        // Signed: unsigned output, input either
        // Convert all range values to constants
        UINFO(6, "RANGE " << nodep << endl);
        V3Const::constifyParamsEdit(nodep->leftp());  // May relink pointed to node
        V3Const::constifyParamsEdit(nodep->rightp());  // May relink pointed to node
        checkConstantOrReplace(nodep->leftp(), "left side of bit range isn't a constant");
        checkConstantOrReplace(nodep->rightp(), "right side of bit range isn't a constant");
        if (m_vup->prelim()) {
            // Don't need to iterate because V3Const already constified
            const int width = nodep->elementsConst();
            if (width > (1 << 28)) {
                nodep->v3error("Width of bit range is huge; vector of over 1billion bits: 0x"
                               << std::hex << width);
            }
            // Note width() not set on range; use elementsConst()
            if (nodep->littleEndian() && !VN_IS(nodep->backp(), UnpackArrayDType)
                && !VN_IS(nodep->backp(), Cell)) {  // For cells we warn in V3Inst
                nodep->v3warn(LITENDIAN, "Little bit endian vector: left < right of bit range: ["
                                             << nodep->leftConst() << ":" << nodep->rightConst()
                                             << "]");
            }
        }
    }

    virtual void visit(AstSel* nodep) override {
        // Signed: always unsigned; Real: Not allowed
        // LSB is self-determined (IEEE 2012 11.5.1)
        // We also use SELs to shorten a signed constant etc, in this case they are signed.
        if (nodep->didWidth()) return;
        UASSERT_OBJ(m_vup, nodep, "Select under an unexpected context");
        if (m_vup->prelim()) {
            if (debug() >= 9) nodep->dumpTree(cout, "-selWidth: ");
            userIterateAndNext(nodep->fromp(), WidthVP(CONTEXT, PRELIM).p());
            userIterateAndNext(nodep->lsbp(), WidthVP(SELF, PRELIM).p());
            checkCvtUS(nodep->fromp());
            iterateCheckSizedSelf(nodep, "Select Width", nodep->widthp(), SELF, BOTH);
            iterateCheckSizedSelf(nodep, "Select LHS", nodep->lhsp(), SELF, BOTH);
            V3Const::constifyParamsEdit(nodep->widthp());  // widthp may change
            const AstConst* const widthConstp = VN_CAST(nodep->widthp(), Const);
            if (!widthConstp) {
                nodep->v3error("Width of bit extract isn't a constant");
                nodep->dtypeSetBit();
                return;
            }
            int width = nodep->widthConst();
            UASSERT_OBJ(nodep->dtypep(), nodep, "dtype wasn't set");  // by V3WidthSel
            if (VN_IS(nodep->lsbp(), Const) && nodep->msbConst() < nodep->lsbConst()) {
                nodep->v3warn(E_UNSUPPORTED, "Unsupported: left < right of bit extract: "
                                                 << nodep->msbConst() << "<" << nodep->lsbConst());
                width = (nodep->lsbConst() - nodep->msbConst() + 1);
                nodep->dtypeSetLogicSized(width, VSigning::UNSIGNED);
                nodep->widthp()->replaceWith(new AstConst(nodep->widthp()->fileline(), width));
                nodep->lsbp()->replaceWith(new AstConst(nodep->lsbp()->fileline(), 0));
            }
            // We're extracting, so just make sure the expression is at least wide enough.
            if (nodep->fromp()->width() < width) {
                nodep->v3warn(SELRANGE, "Extracting " << width << " bits from only "
                                                      << nodep->fromp()->width() << " bit number");
                // Extend it.
                AstNodeDType* const subDTypep
                    = nodep->findLogicDType(width, width, nodep->fromp()->dtypep()->numeric());
                widthCheckSized(nodep, "errorless...", nodep->fromp(), subDTypep, EXTEND_EXP,
                                false /*noerror*/);
            }
            // Check bit indexes.
            // What is the MSB?  We want the true MSB, not one starting at
            // 0, because a 4 bit index is required to look at a one-bit
            // variable[15:15] and 5 bits for [15:-2]
            int frommsb = nodep->fromp()->width() - 1;
            int fromlsb = 0;
            const int elw = nodep->declElWidth();  // Must adjust to tell user bit ranges
            if (nodep->declRange().ranged()) {
                frommsb = nodep->declRange().hiMaxSelect() * elw
                          + (elw - 1);  // Corrected for negative lsb
                fromlsb = nodep->declRange().lo() * elw;
            } else {
                // nodep->v3fatalSrc("Should have been declRanged in V3WidthSel");
            }
            const int selwidth = V3Number::log2b(frommsb + 1 - 1) + 1;  // Width to address a bit
            AstNodeDType* const selwidthDTypep
                = nodep->findLogicDType(selwidth, selwidth, nodep->lsbp()->dtypep()->numeric());
            userIterateAndNext(nodep->fromp(), WidthVP(SELF, FINAL).p());
            userIterateAndNext(nodep->lsbp(), WidthVP(SELF, FINAL).p());
            if (widthBad(nodep->lsbp(), selwidthDTypep) && nodep->lsbp()->width() != 32) {
                if (!nodep->fileline()->warnIsOff(V3ErrorCode::WIDTH)) {
                    nodep->v3warn(WIDTH,
                                  "Bit extraction of var["
                                      << (frommsb / elw) << ":" << (fromlsb / elw) << "] requires "
                                      << (selwidth / elw) << " bit index, not "
                                      << (nodep->lsbp()->width() / elw)
                                      << (nodep->lsbp()->width() != nodep->lsbp()->widthMin()
                                              ? " or " + cvtToStr(nodep->lsbp()->widthMin() / elw)
                                              : "")
                                      << " bits.");
                    UINFO(1, "    Related node: " << nodep << endl);
                }
            }
            if (VN_IS(nodep->lsbp(), Const) && nodep->msbConst() > frommsb) {
                // See also warning in V3Const
                // We need to check here, because the widthCheckSized may silently
                // add another SEL which will lose the out-of-range check
                //
                // We don't want to trigger an error here if we are just
                // evaluating type sizes for a generate block condition. We
                // should only trigger the error if the out-of-range access is
                // actually generated.
                if (m_doGenerate) {
                    UINFO(5, "Selection index out of range inside generate." << endl);
                } else {
                    nodep->v3warn(SELRANGE, "Selection index out of range: "
                                                << nodep->msbConst() << ":" << nodep->lsbConst()
                                                << " outside " << frommsb << ":" << fromlsb);
                    UINFO(1, "    Related node: " << nodep << endl);
                }
            }
            // iterate FINAL is two blocks above
            //
            // If we have a width problem with GENERATE etc, this will reduce
            // it down and mask it, so we have no chance of finding a real
            // error in the future. So don't do this for them.
            if (!m_doGenerate) {
                // lsbp() must be self-determined, however for performance
                // we want the select to be truncated to fit within the
                // maximum select range, e.g. turn Xs outside of the select
                // into something fast which pulls from within the array.
                widthCheckSized(nodep, "Extract Range", nodep->lsbp(), selwidthDTypep, EXTEND_EXP,
                                false /*NOWARN*/);
            }
        }
    }

    virtual void visit(AstArraySel* nodep) override {
        // Signed/Real: Output signed iff LHS signed/real; binary operator
        // Note by contrast, bit extract selects are unsigned
        // LSB is self-determined (IEEE 2012 11.5.1)
        if (m_vup->prelim()) {
            iterateCheckSizedSelf(nodep, "Bit select", nodep->bitp(), SELF, BOTH);
            userIterateAndNext(nodep->fromp(), WidthVP(SELF, BOTH).p());
            //
            int frommsb;
            int fromlsb;
            const AstNodeDType* const fromDtp = nodep->fromp()->dtypep()->skipRefp();
            if (const AstUnpackArrayDType* const adtypep = VN_CAST(fromDtp, UnpackArrayDType)) {
                frommsb = adtypep->hi();
                fromlsb = adtypep->lo();
                if (fromlsb > frommsb) {
                    const int t = frommsb;
                    frommsb = fromlsb;
                    fromlsb = t;
                }
                // However, if the lsb<0 we may go negative, so need more bits!
                if (fromlsb < 0) frommsb += -fromlsb;
                nodep->dtypeFrom(adtypep->subDTypep());  // Need to strip off array reference
            } else {
                // Note PackArrayDType doesn't use an ArraySel but a normal Sel.
                UINFO(1, "    Related dtype: " << fromDtp << endl);
                nodep->v3fatalSrc("Array reference exceeds dimension of array");
                frommsb = fromlsb = 0;
            }
            const int selwidth = V3Number::log2b(frommsb + 1 - 1) + 1;  // Width to address a bit
            AstNodeDType* const selwidthDTypep
                = nodep->findLogicDType(selwidth, selwidth, nodep->bitp()->dtypep()->numeric());
            if (widthBad(nodep->bitp(), selwidthDTypep) && nodep->bitp()->width() != 32) {
                nodep->v3warn(WIDTH, "Bit extraction of array["
                                         << frommsb << ":" << fromlsb << "] requires " << selwidth
                                         << " bit index, not " << nodep->bitp()->width()
                                         << (nodep->bitp()->width() != nodep->bitp()->widthMin()
                                                 ? " or " + cvtToStr(nodep->bitp()->widthMin())
                                                 : "")
                                         << " bits.");
                if (!nodep->fileline()->warnIsOff(V3ErrorCode::WIDTH)) {
                    UINFO(1, "    Related node: " << nodep << endl);
                    UINFO(1, "    Related dtype: " << nodep->dtypep() << endl);
                }
            }
            if (!m_doGenerate) {
                // Must check bounds before adding a select that truncates the bound
                // Note we've already subtracted off LSB
                if (VN_IS(nodep->bitp(), Const)
                    && (VN_AS(nodep->bitp(), Const)->toSInt() > (frommsb - fromlsb)
                        || VN_AS(nodep->bitp(), Const)->toSInt() < 0)) {
                    nodep->v3warn(SELRANGE,
                                  "Selection index out of range: "
                                      << (VN_AS(nodep->bitp(), Const)->toSInt() + fromlsb)
                                      << " outside " << frommsb << ":" << fromlsb);
                    UINFO(1, "    Related node: " << nodep << endl);
                }
                widthCheckSized(nodep, "Extract Range", nodep->bitp(), selwidthDTypep, EXTEND_EXP,
                                false /*NOWARN*/);
            }
        }
    }

    virtual void visit(AstAssocSel* nodep) override {
        // Signed/Real: Output type based on array-declared type; binary operator
        if (m_vup->prelim()) {
            const AstNodeDType* const fromDtp = nodep->fromp()->dtypep()->skipRefp();
            const AstAssocArrayDType* const adtypep = VN_CAST(fromDtp, AssocArrayDType);
            if (!adtypep) {
                UINFO(1, "    Related dtype: " << fromDtp << endl);
                nodep->v3fatalSrc("Associative array reference is not to associative array");
            }
            iterateCheckTyped(nodep, "Associative select", nodep->bitp(), adtypep->keyDTypep(),
                              BOTH);
            nodep->dtypeFrom(adtypep->subDTypep());
        }
    }

    virtual void visit(AstWildcardSel* nodep) override {
        // Signed/Real: Output type based on array-declared type; binary operator
        if (m_vup->prelim()) {
            const AstNodeDType* const fromDtp = nodep->fromp()->dtypep()->skipRefp();
            const AstWildcardArrayDType* const adtypep = VN_CAST(fromDtp, WildcardArrayDType);
            if (!adtypep) {
                UINFO(1, "    Related dtype: " << fromDtp << endl);
                nodep->v3fatalSrc("Wildcard array reference is not to wildcard array");
            }
            const AstBasicDType* const basicp = nodep->bitp()->dtypep()->skipRefp()->basicp();
            if (!basicp
                || (basicp->keyword() != VBasicDTypeKwd::STRING
                    && !basicp->keyword().isIntNumeric())) {
                nodep->v3error("Wildcard index must be integral (IEEE 1800-2017 7.8.1)");
            }
            iterateCheckTyped(nodep, "Wildcard associative select", nodep->bitp(),
                              adtypep->findStringDType(), BOTH);
            nodep->dtypeFrom(adtypep->subDTypep());
        }
    }

    virtual void visit(AstSliceSel* nodep) override {
        // Always creates as output an unpacked array
        if (m_vup->prelim()) {
            userIterateAndNext(nodep->fromp(), WidthVP(SELF, BOTH).p());
            //
            // Array indices are always constant
            const AstNodeDType* const fromDtp = nodep->fromp()->dtypep()->skipRefp();
            const AstUnpackArrayDType* const adtypep = VN_CAST(fromDtp, UnpackArrayDType);
            if (!adtypep) {
                UINFO(1, "    Related dtype: " << fromDtp << endl);
                nodep->v3fatalSrc("Packed array reference exceeds dimension of array");
            }
            // Build new array Dtype based on the original's base type, but with new bounds
            AstNodeDType* const newDtp
                = new AstUnpackArrayDType(nodep->fileline(), adtypep->subDTypep(),
                                          new AstRange(nodep->fileline(), nodep->declRange()));
            v3Global.rootp()->typeTablep()->addTypesp(newDtp);
            nodep->dtypeFrom(newDtp);

            if (!m_doGenerate) {
                // Must check bounds before adding a select that truncates the bound
                // Note we've already subtracted off LSB
                const int subtracted = adtypep->declRange().lo();
                // Add subtracted value to get the original range
                const VNumRange declRange{nodep->declRange().hi() + subtracted,
                                          nodep->declRange().lo() + subtracted,
                                          nodep->declRange().littleEndian()};
                if ((declRange.hi() > adtypep->declRange().hi())
                    || declRange.lo() < adtypep->declRange().lo()) {
                    // Other simulators warn too
                    nodep->v3error("Slice selection index '" << declRange << "'"
                                                             << " outside data type's '"
                                                             << adtypep->declRange() << "'");
                } else if ((declRange.littleEndian() != adtypep->declRange().littleEndian())
                           && declRange.hi() != declRange.lo()) {
                    nodep->v3error("Slice selection '"
                                   << declRange << "'"
                                   << " has backward indexing versus data type's '"
                                   << adtypep->declRange() << "'");
                }
            }
        }
    }

    virtual void visit(AstSelBit* nodep) override {
        // Just a quick check as after V3Param these nodes instead are AstSel's
        userIterateAndNext(nodep->fromp(), WidthVP(CONTEXT, PRELIM).p());  // FINAL in AstSel
        userIterateAndNext(nodep->rhsp(), WidthVP(CONTEXT, PRELIM).p());  // FINAL in AstSel
        userIterateAndNext(nodep->thsp(), WidthVP(CONTEXT, PRELIM).p());  // FINAL in AstSel
        userIterateAndNext(nodep->attrp(), WidthVP(SELF, BOTH).p());
        AstNode* const selp = V3Width::widthSelNoIterEdit(nodep);
        if (selp != nodep) {
            nodep = nullptr;
            userIterate(selp, m_vup);
            return;
        }
        nodep->v3fatalSrc("AstSelBit should disappear after widthSel");
    }
    virtual void visit(AstSelExtract* nodep) override {
        // Just a quick check as after V3Param these nodes instead are AstSel's
        userIterateAndNext(nodep->fromp(), WidthVP(CONTEXT, PRELIM).p());  // FINAL in AstSel
        userIterateAndNext(nodep->rhsp(), WidthVP(CONTEXT, PRELIM).p());  // FINAL in AstSel
        userIterateAndNext(nodep->thsp(), WidthVP(CONTEXT, PRELIM).p());  // FINAL in AstSel
        userIterateAndNext(nodep->attrp(), WidthVP(SELF, BOTH).p());
        AstNode* const selp = V3Width::widthSelNoIterEdit(nodep);
        if (selp != nodep) {
            nodep = nullptr;
            userIterate(selp, m_vup);
            return;
        }
        nodep->v3fatalSrc("AstSelExtract should disappear after widthSel");
    }
    virtual void visit(AstSelPlus* nodep) override {
        userIterateAndNext(nodep->fromp(), WidthVP(CONTEXT, PRELIM).p());  // FINAL in AstSel
        userIterateAndNext(nodep->rhsp(), WidthVP(CONTEXT, PRELIM).p());  // FINAL in AstSel
        userIterateAndNext(nodep->thsp(), WidthVP(CONTEXT, PRELIM).p());  // FINAL in AstSel
        userIterateAndNext(nodep->attrp(), WidthVP(SELF, BOTH).p());
        AstNode* const selp = V3Width::widthSelNoIterEdit(nodep);
        if (selp != nodep) {
            nodep = nullptr;
            userIterate(selp, m_vup);
            return;
        }
        nodep->v3fatalSrc("AstSelPlus should disappear after widthSel");
    }
    virtual void visit(AstSelMinus* nodep) override {
        userIterateAndNext(nodep->fromp(), WidthVP(CONTEXT, PRELIM).p());  // FINAL in AstSel
        userIterateAndNext(nodep->rhsp(), WidthVP(CONTEXT, PRELIM).p());  // FINAL in AstSel
        userIterateAndNext(nodep->thsp(), WidthVP(CONTEXT, PRELIM).p());  // FINAL in AstSel
        userIterateAndNext(nodep->attrp(), WidthVP(SELF, BOTH).p());
        AstNode* const selp = V3Width::widthSelNoIterEdit(nodep);
        if (selp != nodep) {
            nodep = nullptr;
            userIterate(selp, m_vup);
            return;
        }
        nodep->v3fatalSrc("AstSelMinus should disappear after widthSel");
    }

    virtual void visit(AstExtend* nodep) override {
        // Only created by this process, so we know width from here down is correct.
    }
    virtual void visit(AstExtendS* nodep) override {
        // Only created by this process, so we know width from here down is correct.
    }
    virtual void visit(AstConst* nodep) override {
        // The node got setup with the signed/real state of the node.
        // However a later operation may have changed the node->signed w/o changing
        // the number's sign.  So we don't: nodep->dtypeChgSigned(nodep->num().isSigned());
        if (m_vup && m_vup->prelim()) {
            if (nodep->num().isString()) {
                nodep->dtypeSetString();
            } else if (nodep->num().sized()) {
                nodep->dtypeChgWidth(nodep->num().width(), nodep->num().width());
            } else {
                nodep->dtypeChgWidth(nodep->num().width(), nodep->num().widthMin());
            }
        }
        // We don't size the constant until we commit the widths, as need parameters
        // to remain unsized, and numbers to remain unsized to avoid backp() warnings
    }
    virtual void visit(AstEmptyQueue* nodep) override {
        nodep->dtypeSetEmptyQueue();
        if (!VN_IS(nodep->backp(), Assign)) {
            nodep->v3warn(E_UNSUPPORTED,
                          "Unsupported/Illegal: empty queue ('{}') in this context");
        }
    }
    virtual void visit(AstFell* nodep) override {
        if (m_vup->prelim()) {
            iterateCheckSizedSelf(nodep, "LHS", nodep->exprp(), SELF, BOTH);
            nodep->dtypeSetBit();
        }
    }
    virtual void visit(AstPast* nodep) override {
        if (m_vup->prelim()) {
            iterateCheckSizedSelf(nodep, "LHS", nodep->exprp(), SELF, BOTH);
            nodep->dtypeFrom(nodep->exprp());
            if (nodep->ticksp()) {
                iterateCheckSizedSelf(nodep, "Ticks", nodep->ticksp(), SELF, BOTH);
                V3Const::constifyParamsEdit(nodep->ticksp());  // ticksp may change
                const AstConst* const constp = VN_CAST(nodep->ticksp(), Const);
                if (!constp) {
                    nodep->v3error("$past tick value must be constant (IEEE 1800-2017 16.9.3)");
                    nodep->ticksp()->unlinkFrBack()->deleteTree();
                } else if (constp->toSInt() < 1) {
                    constp->v3error("$past tick value must be >= 1 (IEEE 1800-2017 16.9.3)");
                    nodep->ticksp()->unlinkFrBack()->deleteTree();
                } else {
                    if (constp->toSInt() > 10) {
                        constp->v3warn(TICKCOUNT, "$past tick value of "
                                                      << constp->toSInt()
                                                      << " may have a large performance cost");
                    }
                }
            }
        }
    }
    virtual void visit(AstRose* nodep) override {
        if (m_vup->prelim()) {
            iterateCheckSizedSelf(nodep, "LHS", nodep->exprp(), SELF, BOTH);
            nodep->dtypeSetBit();
        }
    }

    virtual void visit(AstSampled* nodep) override {
        if (m_vup->prelim()) {
            iterateCheckSizedSelf(nodep, "LHS", nodep->exprp(), SELF, BOTH);
            nodep->dtypeFrom(nodep->exprp());
        }
    }

    virtual void visit(AstStable* nodep) override {
        if (m_vup->prelim()) {
            iterateCheckSizedSelf(nodep, "LHS", nodep->exprp(), SELF, BOTH);
            nodep->dtypeSetBit();
        }
    }

    virtual void visit(AstImplication* nodep) override {
        if (m_vup->prelim()) {
            iterateCheckBool(nodep, "LHS", nodep->lhsp(), BOTH);
            iterateCheckBool(nodep, "RHS", nodep->rhsp(), BOTH);
            nodep->dtypeSetBit();
        }
    }

    virtual void visit(AstRand* nodep) override {
        if (m_vup->prelim()) {
            if (nodep->urandom()) {
                nodep->dtypeSetUInt32();  // Says the spec
            } else {
                nodep->dtypeSetSigned32();  // Says the spec
            }
            if (nodep->seedp()) iterateCheckSigned32(nodep, "seed", nodep->seedp(), BOTH);
        }
    }
    virtual void visit(AstURandomRange* nodep) override {
        if (m_vup->prelim()) {
            nodep->dtypeSetUInt32();  // Says the spec
            AstNodeDType* const expDTypep = nodep->findUInt32DType();
            userIterateAndNext(nodep->lhsp(), WidthVP(CONTEXT, PRELIM).p());
            userIterateAndNext(nodep->rhsp(), WidthVP(CONTEXT, PRELIM).p());
            iterateCheck(nodep, "LHS", nodep->lhsp(), SELF, FINAL, expDTypep, EXTEND_EXP);
            iterateCheck(nodep, "RHS", nodep->rhsp(), SELF, FINAL, expDTypep, EXTEND_EXP);
        }
    }
    virtual void visit(AstUnbounded* nodep) override {
        nodep->dtypeSetSigned32();  // Used in int context
        if (VN_IS(nodep->backp(), IsUnbounded)) return;  // Ok, leave
        if (VN_IS(nodep->backp(), BracketArrayDType)) return;  // Ok, leave
        if (const auto* const varp = VN_CAST(nodep->backp(), Var)) {
            if (varp->isParam()) return;  // Ok, leave
        }
        // queue_slice[#:$]
        if (const auto* const selp = VN_CAST(nodep->backp(), SelExtract)) {
            if (VN_IS(selp->fromp()->dtypep(), QueueDType)) {
                nodep->replaceWith(
                    new AstConst(nodep->fileline(), AstConst::Signed32(), 0x7FFFFFFF));
                VL_DO_DANGLING(nodep->deleteTree(), nodep);
                return;
            }
        }
        nodep->v3warn(E_UNSUPPORTED, "Unsupported/illegal unbounded ('$') in this context.");
    }
    virtual void visit(AstIsUnbounded* nodep) override {
        if (m_vup->prelim()) {
            userIterateAndNext(nodep->lhsp(), WidthVP(SELF, BOTH).p());
            nodep->dtypeSetBit();
        }
    }
    virtual void visit(AstUCFunc* nodep) override {
        // Give it the size the user wants.
        if (m_vup && m_vup->prelim()) {
            nodep->dtypeSetLogicUnsized(32, 1, VSigning::UNSIGNED);  // We don't care
            // All arguments seek their natural sizes
            userIterateChildren(nodep, WidthVP(SELF, BOTH).p());
        }
        if (m_vup->final()) {
            AstNodeDType* const expDTypep = m_vup->dtypeOverridep(nodep->dtypep());
            nodep->dtypeFrom(expDTypep);  // Assume user knows the rules; go with the flow
            if (nodep->width() > 64) {
                nodep->v3warn(E_UNSUPPORTED, "Unsupported: $c can't generate wider than 64 bits");
            }
        }
    }
    virtual void visit(AstCLog2* nodep) override {
        if (m_vup->prelim()) { iterateCheckSizedSelf(nodep, "LHS", nodep->lhsp(), SELF, BOTH); }
    }
    virtual void visit(AstPow* nodep) override {
        // Pow is special, output sign only depends on LHS sign, but
        // function result depends on both signs
        // RHS is self-determined (IEEE)
        // Real if either side is real (as with AstAdd)
        if (m_vup->prelim()) {
            userIterateAndNext(nodep->lhsp(), WidthVP(CONTEXT, PRELIM).p());
            userIterateAndNext(nodep->rhsp(), WidthVP(CONTEXT, PRELIM).p());
            if (nodep->lhsp()->isDouble() || nodep->rhsp()->isDouble()) {
                spliceCvtD(nodep->lhsp());
                spliceCvtD(nodep->rhsp());
                VL_DO_DANGLING(replaceWithDVersion(nodep), nodep);
                return;
            }

            checkCvtUS(nodep->lhsp());
            iterateCheckSizedSelf(nodep, "RHS", nodep->rhsp(), SELF, BOTH);
            nodep->dtypeFrom(nodep->lhsp());
        }

        if (m_vup->final()) {
            AstNodeDType* const expDTypep = m_vup->dtypeOverridep(nodep->dtypep());
            nodep->dtypeFrom(expDTypep);
            // rhs already finalized in iterate_shift_prelim
            iterateCheck(nodep, "LHS", nodep->lhsp(), SELF, FINAL, nodep->dtypep(), EXTEND_EXP);
            AstNode* newp = nullptr;  // No change
            if (nodep->lhsp()->isSigned() && nodep->rhsp()->isSigned()) {
                newp = new AstPowSS(nodep->fileline(), nodep->lhsp()->unlinkFrBack(),
                                    nodep->rhsp()->unlinkFrBack());
            } else if (nodep->lhsp()->isSigned() && !nodep->rhsp()->isSigned()) {
                newp = new AstPowSU(nodep->fileline(), nodep->lhsp()->unlinkFrBack(),
                                    nodep->rhsp()->unlinkFrBack());
            } else if (!nodep->lhsp()->isSigned() && nodep->rhsp()->isSigned()) {
                newp = new AstPowUS(nodep->fileline(), nodep->lhsp()->unlinkFrBack(),
                                    nodep->rhsp()->unlinkFrBack());
            }
            if (newp) {
                newp->dtypeFrom(nodep);
                UINFO(9, "powOld " << nodep << endl);
                UINFO(9, "powNew " << newp << endl);
                VL_DO_DANGLING(nodep->replaceWith(newp), nodep);
            }
        }
    }
    virtual void visit(AstPowSU* nodep) override {
        // POWSU/SS/US only created here, dtype already determined, so
        // nothing to do in this function
        userIterateAndNext(nodep->lhsp(), WidthVP(SELF, BOTH).p());
        userIterateAndNext(nodep->rhsp(), WidthVP(SELF, BOTH).p());
    }
    virtual void visit(AstPowSS* nodep) override {
        // POWSU/SS/US only created here, dtype already determined, so
        // nothing to do in this function
        userIterateAndNext(nodep->lhsp(), WidthVP(SELF, BOTH).p());
        userIterateAndNext(nodep->rhsp(), WidthVP(SELF, BOTH).p());
    }
    virtual void visit(AstPowUS* nodep) override {
        // POWSU/SS/US only created here, dtype already determined, so
        // nothing to do in this function
        userIterateAndNext(nodep->lhsp(), WidthVP(SELF, BOTH).p());
        userIterateAndNext(nodep->rhsp(), WidthVP(SELF, BOTH).p());
    }
    virtual void visit(AstCountBits* nodep) override {
        if (m_vup->prelim()) {
            iterateCheckSizedSelf(nodep, "LHS", nodep->lhsp(), SELF, BOTH);
            iterateCheckSizedSelf(nodep, "RHS", nodep->rhsp(), SELF, BOTH);
            iterateCheckSizedSelf(nodep, "THS", nodep->thsp(), SELF, BOTH);
            iterateCheckSizedSelf(nodep, "FHS", nodep->fhsp(), SELF, BOTH);
            // If it's a 32 bit number, we need a 6 bit number as we need to return '32'.
            const int selwidth = V3Number::log2b(nodep->lhsp()->width()) + 1;
            nodep->dtypeSetLogicSized(selwidth,
                                      VSigning::UNSIGNED);  // Spec doesn't indicate if an integer
        }
    }
    virtual void visit(AstCountOnes* nodep) override {
        if (m_vup->prelim()) {
            iterateCheckSizedSelf(nodep, "LHS", nodep->lhsp(), SELF, BOTH);
            // If it's a 32 bit number, we need a 6 bit number as we need to return '32'.
            const int selwidth = V3Number::log2b(nodep->lhsp()->width()) + 1;
            nodep->dtypeSetLogicSized(selwidth,
                                      VSigning::UNSIGNED);  // Spec doesn't indicate if an integer
        }
    }
    virtual void visit(AstCvtPackString* nodep) override {
        // Opaque returns, so arbitrary
        userIterateAndNext(nodep->lhsp(), WidthVP(SELF, BOTH).p());
        // Type set in constructor
    }
    virtual void visit(AstTimeImport* nodep) override {
        // LHS is a real number in seconds
        // Need to round to time units and precision
        userIterateAndNext(nodep->lhsp(), WidthVP(SELF, BOTH).p());
        const AstConst* const constp = VN_CAST(nodep->lhsp(), Const);
        if (!constp || !constp->isDouble()) nodep->v3fatalSrc("Times should be doubles");
        if (nodep->timeunit().isNone()) nodep->v3fatalSrc("$time import no units");
        double time = constp->num().toDouble();
        if (v3Global.rootp()->timeprecision().isNone()) nodep->v3fatalSrc("Never set precision?");
        time /= nodep->timeunit().multiplier();
        // IEEE claims you should round to time precision here, but no simulator seems to do this
        AstConst* const newp = new AstConst(nodep->fileline(), AstConst::RealDouble(), time);
        nodep->replaceWith(newp);
        VL_DO_DANGLING(nodep->deleteTree(), nodep);
    }
    virtual void visit(AstEventControl* nodep) override {
        nodep->v3warn(E_UNSUPPORTED, "Unsupported: event control statement in this location\n"
                                         << nodep->warnMore()
                                         << "... Suggest have one event control statement "
                                         << "per procedure, at the top of the procedure");
        VL_DO_DANGLING(nodep->unlinkFrBack()->deleteTree(), nodep);
    }
    virtual void visit(AstAttrOf* nodep) override {
        VL_RESTORER(m_attrp);
        m_attrp = nodep;
        userIterateAndNext(nodep->fromp(), WidthVP(SELF, BOTH).p());
        if (nodep->dimp()) userIterateAndNext(nodep->dimp(), WidthVP(SELF, BOTH).p());
        // Don't iterate children, don't want to lose VarRef.
        switch (nodep->attrType()) {
        case VAttrType::VAR_BASE:
        case VAttrType::MEMBER_BASE:
        case VAttrType::ENUM_BASE:
            // Soon to be handled in V3LinkWidth SEL generation, under attrp() and newSubLsbOf
            break;
        case VAttrType::DIM_DIMENSIONS:
        case VAttrType::DIM_UNPK_DIMENSIONS: {
            UASSERT_OBJ(nodep->fromp() && nodep->fromp()->dtypep(), nodep, "Unsized expression");
            const std::pair<uint32_t, uint32_t> dim = nodep->fromp()->dtypep()->dimensions(true);
            const int val
                = (nodep->attrType() == VAttrType::DIM_UNPK_DIMENSIONS ? dim.second
                                                                       : (dim.first + dim.second));
            nodep->replaceWith(new AstConst(nodep->fileline(), AstConst::Signed32(), val));
            VL_DO_DANGLING(nodep->deleteTree(), nodep);
            break;
        }
        case VAttrType::DIM_BITS:
        case VAttrType::DIM_HIGH:
        case VAttrType::DIM_INCREMENT:
        case VAttrType::DIM_LEFT:
        case VAttrType::DIM_LOW:
        case VAttrType::DIM_RIGHT:
        case VAttrType::DIM_SIZE: {
            UASSERT_OBJ(nodep->fromp() && nodep->fromp()->dtypep(), nodep, "Unsized expression");
            AstNodeDType* const dtypep = nodep->fromp()->dtypep();
            if (VN_IS(dtypep, QueueDType)) {
                switch (nodep->attrType()) {
                case VAttrType::DIM_SIZE: {
                    AstNode* const newp = new AstCMethodHard(
                        nodep->fileline(), nodep->fromp()->unlinkFrBack(), "size");
                    newp->dtypeSetSigned32();
                    newp->didWidth(true);
                    newp->protect(false);
                    nodep->replaceWith(newp);
                    VL_DO_DANGLING(nodep->deleteTree(), nodep);
                    break;
                }
                case VAttrType::DIM_LEFT:
                case VAttrType::DIM_LOW: {
                    AstNode* const newp = new AstConst(nodep->fileline(), AstConst::Signed32(), 0);
                    nodep->replaceWith(newp);
                    VL_DO_DANGLING(nodep->deleteTree(), nodep);
                    break;
                }
                case VAttrType::DIM_RIGHT:
                case VAttrType::DIM_HIGH: {
                    AstNode* const sizep = new AstCMethodHard(
                        nodep->fileline(), nodep->fromp()->unlinkFrBack(), "size");
                    sizep->dtypeSetSigned32();
                    sizep->didWidth(true);
                    sizep->protect(false);
                    AstNode* const newp
                        = new AstSub(nodep->fileline(), sizep,
                                     new AstConst(nodep->fileline(), AstConst::Signed32(), 1));
                    nodep->replaceWith(newp);
                    VL_DO_DANGLING(nodep->deleteTree(), nodep);
                    break;
                }
                case VAttrType::DIM_INCREMENT: {
                    AstNode* const newp
                        = new AstConst(nodep->fileline(), AstConst::Signed32(), -1);
                    nodep->replaceWith(newp);
                    VL_DO_DANGLING(nodep->deleteTree(), nodep);
                    break;
                }
                case VAttrType::DIM_BITS: {
                    nodep->v3warn(E_UNSUPPORTED, "Unsupported: $bits for queue");
                    break;
                }
                default: nodep->v3error("Unhandled attribute type");
                }
            } else {
                const std::pair<uint32_t, uint32_t> dimpair = dtypep->skipRefp()->dimensions(true);
                const uint32_t msbdim = dimpair.first + dimpair.second;
                if (!nodep->dimp() || msbdim < 1) {
                    if (VN_IS(dtypep, BasicDType) && dtypep->basicp()->isString()) {
                        // IEEE undocumented but $bits(string) must give length(string) * 8
                        AstNode* const newp = new AstShiftL{
                            nodep->fileline(),
                            new AstLenN{nodep->fileline(), nodep->fromp()->unlinkFrBack()},
                            new AstConst{nodep->fileline(), 3},  // * 8
                            32};
                        nodep->replaceWith(newp);
                        VL_DO_DANGLING(pushDeletep(nodep), nodep);
                    } else {
                        const int dim = 1;
                        AstConst* const newp
                            = dimensionValue(nodep->fileline(), dtypep, nodep->attrType(), dim);
                        nodep->replaceWith(newp);
                        VL_DO_DANGLING(nodep->deleteTree(), nodep);
                    }
                } else if (VN_IS(nodep->dimp(), Const)) {
                    const int dim = VN_AS(nodep->dimp(), Const)->toSInt();
                    AstConst* const newp
                        = dimensionValue(nodep->fileline(), dtypep, nodep->attrType(), dim);
                    nodep->replaceWith(newp);
                    VL_DO_DANGLING(nodep->deleteTree(), nodep);
                } else {  // Need a runtime lookup table.  Yuk.
                    UASSERT_OBJ(nodep->fromp() && dtypep, nodep, "Unsized expression");
                    AstVar* const varp = dimensionVarp(dtypep, nodep->attrType(), msbdim);
                    AstNode* const dimp = nodep->dimp()->unlinkFrBack();
                    AstNode* const newp
                        = new AstArraySel{nodep->fileline(), newVarRefDollarUnit(varp), dimp};
                    nodep->replaceWith(newp);
                    VL_DO_DANGLING(nodep->deleteTree(), nodep);
                }
            }
            break;
        }
        case VAttrType::TYPENAME: {
            UASSERT_OBJ(nodep->fromp(), nodep, "Unprovided expression");
            const string result = nodep->fromp()->dtypep()->prettyDTypeName();
            AstNode* const newp = new AstConst(nodep->fileline(), AstConst::String(), result);
            nodep->replaceWith(newp);
            VL_DO_DANGLING(nodep->deleteTree(), nodep);
            break;
        }
        default: {
            // Everything else resolved earlier
            nodep->dtypeSetLogicUnsized(32, 1, VSigning::UNSIGNED);  // Approximation, unsized 32
            UINFO(1, "Missing ATTR type case node: " << nodep << endl);
            nodep->v3fatalSrc("Missing ATTR type case");
            break;
        }
        }
    }
    virtual void visit(AstPull* nodep) override {
        // May have select underneath, let seek natural size
        userIterateChildren(nodep, WidthVP(SELF, BOTH).p());
    }
    virtual void visit(AstText* nodep) override {
        // Only used in CStmts which don't care....
    }

    // DTYPES
    virtual void visit(AstNodeArrayDType* nodep) override {
        if (nodep->didWidthAndSet()) return;  // This node is a dtype & not both PRELIMed+FINALed

        if (nodep->subDTypep() == nodep->basicp()) {  // Innermost dimension
            AstBasicDType* const basicp = nodep->basicp();
            // If basic dtype is LOGIC_IMPLICIT, it is actually 1 bit LOGIC
            if (basicp->implicit()) {
                UASSERT_OBJ(basicp->width() <= 1, basicp,
                            "must be 1 bit but actually " << basicp->width() << " bits");
                AstBasicDType* const newp = new AstBasicDType(
                    basicp->fileline(), VBasicDTypeKwd::LOGIC, basicp->numeric());
                newp->widthForce(1, 1);
                basicp->replaceWith(newp);
                VL_DO_DANGLING(pushDeletep(basicp), basicp);
            }
        }
        // Iterate into subDTypep() to resolve that type and update pointer.
        nodep->refDTypep(iterateEditMoveDTypep(nodep, nodep->subDTypep()));
        // Cleanup array size
        userIterateAndNext(nodep->rangep(), WidthVP(SELF, BOTH).p());
        nodep->dtypep(nodep);  // The array itself, not subDtype
        if (auto* const adtypep = VN_CAST(nodep, UnpackArrayDType)) {
            // Historically array elements have width of the ref type not the full array
            nodep->widthFromSub(nodep->subDTypep());
            if (nodep->subDTypep()->skipRefp()->isCompound()) adtypep->isCompound(true);
        } else {
            const int width = nodep->subDTypep()->width() * nodep->rangep()->elementsConst();
            nodep->widthForce(width, width);
        }
        UINFO(4, "dtWidthed " << nodep << endl);
    }
    virtual void visit(AstAssocArrayDType* nodep) override {
        if (nodep->didWidthAndSet()) return;  // This node is a dtype & not both PRELIMed+FINALed
        // Iterate into subDTypep() to resolve that type and update pointer.
        nodep->refDTypep(iterateEditMoveDTypep(nodep, nodep->subDTypep()));
        nodep->keyDTypep(iterateEditMoveDTypep(nodep, nodep->keyDTypep()));
        nodep->dtypep(nodep);  // The array itself, not subDtype
        UINFO(4, "dtWidthed " << nodep << endl);
    }
    virtual void visit(AstBracketArrayDType* nodep) override {
        // Type inserted only because parser didn't know elementsp() type
        // Resolve elementsp's type
        userIterateChildren(nodep, WidthVP(SELF, BOTH).p());
        // We must edit when dtype still under normal nodes and before type table
        // See notes in iterateEditMoveDTypep
        AstNodeDType* const childp = nodep->childDTypep();
        childp->unlinkFrBack();
        AstNode* const elementsp = nodep->elementsp()->unlinkFrBack();
        AstNode* newp;
        if (VN_IS(elementsp, Unbounded)) {
            newp = new AstQueueDType(nodep->fileline(), VFlagChildDType(), childp, nullptr);
            VL_DO_DANGLING(elementsp->deleteTree(), elementsp);
        } else if (AstNodeDType* const keyp = VN_CAST(elementsp, NodeDType)) {
            newp = new AstAssocArrayDType(nodep->fileline(), VFlagChildDType(), childp, keyp);
        } else {
            // Must be expression that is constant, but we'll determine that later
            newp = new AstUnpackArrayDType(
                nodep->fileline(), VFlagChildDType(), childp,
                new AstRange(nodep->fileline(), new AstConst(elementsp->fileline(), 0),
                             new AstSub(elementsp->fileline(), elementsp,
                                        new AstConst(elementsp->fileline(), 1))));
        }
        nodep->replaceWith(newp);
        VL_DO_DANGLING(nodep->deleteTree(), nodep);
        // Normally parent's iteration would cover this, but we might have entered by a specific
        // visit
        VL_DO_DANGLING(userIterate(newp, nullptr), newp);
    }
    virtual void visit(AstDynArrayDType* nodep) override {
        if (nodep->didWidthAndSet()) return;  // This node is a dtype & not both PRELIMed+FINALed
        // Iterate into subDTypep() to resolve that type and update pointer.
        nodep->refDTypep(iterateEditMoveDTypep(nodep, nodep->subDTypep()));
        nodep->dtypep(nodep);  // The array itself, not subDtype
        UINFO(4, "dtWidthed " << nodep << endl);
    }
    virtual void visit(AstQueueDType* nodep) override {
        if (nodep->didWidthAndSet()) return;  // This node is a dtype & not both PRELIMed+FINALed
        // Iterate into subDTypep() to resolve that type and update pointer.
        nodep->refDTypep(iterateEditMoveDTypep(nodep, nodep->subDTypep()));
        nodep->dtypep(nodep);  // The array itself, not subDtype
        if (VN_IS(nodep->boundp(), Unbounded)) {
            nodep->boundp()->unlinkFrBack()->deleteTree();  // nullptr will represent unbounded
        }
        UINFO(4, "dtWidthed " << nodep << endl);
    }
    virtual void visit(AstVoidDType* nodep) override {
        if (nodep->didWidthAndSet()) return;  // This node is a dtype & not both PRELIMed+FINALed
        nodep->dtypep(nodep);
        UINFO(4, "dtWidthed " << nodep << endl);
    }
    virtual void visit(AstUnsizedArrayDType* nodep) override {
        if (nodep->didWidthAndSet()) return;  // This node is a dtype & not both PRELIMed+FINALed
        // Iterate into subDTypep() to resolve that type and update pointer.
        nodep->refDTypep(iterateEditMoveDTypep(nodep, nodep->subDTypep()));
        // Cleanup array size
        nodep->dtypep(nodep);  // The array itself, not subDtype
        UINFO(4, "dtWidthed " << nodep << endl);
    }
    virtual void visit(AstWildcardArrayDType* nodep) override {
        if (nodep->didWidthAndSet()) return;  // This node is a dtype & not both PRELIMed+FINALed
        // Iterate into subDTypep() to resolve that type and update pointer.
        nodep->refDTypep(iterateEditMoveDTypep(nodep, nodep->subDTypep()));
        // Cleanup array size
        nodep->dtypep(nodep);  // The array itself, not subDtype
        UINFO(4, "dtWidthed " << nodep << endl);
    }
    virtual void visit(AstBasicDType* nodep) override {
        if (nodep->didWidthAndSet()) return;  // This node is a dtype & not both PRELIMed+FINALed
        if (nodep->generic()) return;  // Already perfect
        if (nodep->rangep()) {
            userIterateAndNext(nodep->rangep(), WidthVP(SELF, BOTH).p());
            // Because this DType has a unique child range, we know it's not
            // pointed at by other nodes unless they are referencing this type.
            // Furthermore the width() calculation would return identical
            // values.  Therefore we can directly replace the width
            nodep->widthForce(nodep->rangep()->elementsConst(), nodep->rangep()->elementsConst());
        } else if (nodep->isRanged()) {
            nodep->widthForce(nodep->nrange().elements(), nodep->nrange().elements());
        } else if (nodep->implicit()) {
            // Parameters may notice implicitness and change to different dtype
            nodep->widthForce(1, 1);
        }
        // else width in node is correct; it was set based on keyword().width()
        // at construction time.  Ditto signed, so "unsigned byte" etc works right.
        nodep->cvtRangeConst();
        // TODO: If BasicDType now looks like a generic type, we can convert to a real generic
        // dtype Instead for now doing this in V3WidthCommit
        UINFO(4, "dtWidthed " << nodep << endl);
    }
    virtual void visit(AstConstDType* nodep) override {
        if (nodep->didWidthAndSet()) return;  // This node is a dtype & not both PRELIMed+FINALed
        // Iterate into subDTypep() to resolve that type and update pointer.
        nodep->refDTypep(iterateEditMoveDTypep(nodep, nodep->subDTypep()));
        userIterateChildren(nodep, nullptr);
        nodep->dtypep(nodep);  // Should already be set, but be clear it's not the subDType
        nodep->widthFromSub(nodep->subDTypep());
        UINFO(4, "dtWidthed " << nodep << endl);
    }
    virtual void visit(AstRefDType* nodep) override {
        if (nodep->doingWidth()) {  // Early exit if have circular parameter definition
            nodep->v3error("Typedef's type is circular: " << nodep->prettyName());
            nodep->dtypeSetBit();
            nodep->doingWidth(false);
            return;
        }
        if (nodep->didWidthAndSet()) return;  // This node is a dtype & not both PRELIMed+FINALed
        nodep->doingWidth(true);
        if (nodep->typeofp()) {  // type(typeofp_expression)
            // Type comes from expression's type
            userIterateAndNext(nodep->typeofp(), WidthVP(SELF, BOTH).p());
            AstNode* const typeofp = nodep->typeofp();
            nodep->typedefp(nullptr);
            nodep->refDTypep(typeofp->dtypep());
            VL_DO_DANGLING(typeofp->unlinkFrBack()->deleteTree(), typeofp);
            // We had to use AstRefDType for this construct as pointers to this type
            // in type table are still correct (which they wouldn't be if we replaced the node)
        }
        userIterateChildren(nodep, nullptr);
        if (nodep->subDTypep()) {
            // Normally iterateEditMoveDTypep iterate would work, but the refs are under
            // the TypeDef which will upset iterateEditMoveDTypep as it can't find it under
            // this node's childDTypep
            userIterate(nodep->subDTypep(), nullptr);
            nodep->refDTypep(iterateEditMoveDTypep(nodep, nodep->subDTypep()));
            nodep->typedefp(nullptr);  // Note until line above subDTypep() may have followed this
            // Widths are resolved, but special iterate to check for recurstion
            userIterate(nodep->subDTypep(), nullptr);
        }
        // Effectively nodep->dtypeFrom(nodep->dtypeSkipRefp());
        // But might be recursive, so instead manually recurse into the referenced type
        UASSERT_OBJ(nodep->subDTypep(), nodep, "Unlinked");
        nodep->dtypeFrom(nodep->subDTypep());
        nodep->widthFromSub(nodep->subDTypep());
        UINFO(4, "dtWidthed " << nodep << endl);
        nodep->doingWidth(false);
    }
    virtual void visit(AstTypedef* nodep) override {
        if (nodep->didWidthAndSet()) return;  // This node is a dtype & not both PRELIMed+FINALed
        if (auto* const refp = checkRefToTypedefRecurse(nodep, nodep)) {
            nodep->v3error("Typedef has self-reference: " << nodep->prettyNameQ() << '\n'
                                                          << nodep->warnContextPrimary() << '\n'
                                                          << refp->warnOther()
                                                          << "... Location of reference\n"
                                                          << refp->warnContextSecondary());
            // May cause internel error but avoids infinite loop on dump
            refp->typedefp(nullptr);
            VL_DO_DANGLING(pushDeletep(nodep->unlinkFrBack()), nodep);
            return;
        }
        nodep->dtypep(iterateEditMoveDTypep(nodep, nodep->subDTypep()));
        userIterateChildren(nodep, nullptr);
    }
    virtual void visit(AstParamTypeDType* nodep) override {
        if (nodep->didWidthAndSet()) return;  // This node is a dtype & not both PRELIMed+FINALed
        nodep->dtypep(iterateEditMoveDTypep(nodep, nodep->subDTypep()));
        userIterateChildren(nodep, nullptr);
        nodep->widthFromSub(nodep->subDTypep());
    }
    virtual void visit(AstCastDynamic* nodep) override {
        nodep->dtypeChgWidthSigned(32, 1, VSigning::SIGNED);  // Spec says integer return
        userIterateChildren(nodep, WidthVP(SELF, BOTH).p());
        AstNodeDType* const toDtp = nodep->top()->dtypep()->skipRefToEnump();
        AstNodeDType* const fromDtp = nodep->fromp()->dtypep()->skipRefToEnump();
        FileLine* const fl = nodep->fileline();
        const auto castable = computeCastable(toDtp, fromDtp, nodep->fromp());
        AstNode* newp;
        if (castable == DYNAMIC_CLASS) {
            // Keep in place, will compute at runtime
            return;
        } else if (castable == ENUM_EXPLICIT || castable == ENUM_IMPLICIT) {
            // TODO is from is a constant we could simplify, though normal constant
            // elimination should do much the same
            // Form: "( ((v > size) ? false : enum_valid[v[N:0]])
            //          ? ExprStmt(ExprAssign(out, Cast(v, type)), 1) : 0)"
            auto* const enumDtp = VN_AS(toDtp, EnumDType);
            UASSERT_OBJ(enumDtp, nodep, "$cast determined as enum, but not enum type");
            const uint64_t maxval = enumMaxValue(nodep, enumDtp);
            const bool assoc = maxval > ENUM_LOOKUP_BITS;
            AstNode* testp = nullptr;
            if (assoc) {
                AstVar* const varp = enumVarp(enumDtp, VAttrType::ENUM_VALID, true, 0);
                testp = new AstAssocSel{fl, newVarRefDollarUnit(varp),
                                        nodep->fromp()->cloneTree(false)};
            } else {
                const int selwidth = V3Number::log2b(maxval) + 1;  // Width to address a bit
                AstVar* const varp
                    = enumVarp(enumDtp, VAttrType::ENUM_VALID, false, (1ULL << selwidth) - 1);
                FileLine* const fl_nowarn = new FileLine(fl);
                fl_nowarn->warnOff(V3ErrorCode::WIDTH, true);
                testp = new AstCond{
                    fl,
                    new AstGt{fl_nowarn, nodep->fromp()->cloneTree(false),
                              new AstConst{fl_nowarn, AstConst::Unsized64{}, maxval}},
                    new AstConst{fl, AstConst::BitFalse{}},
                    new AstArraySel{
                        fl, newVarRefDollarUnit(varp),
                        new AstSel{fl, nodep->fromp()->cloneTree(false), 0, selwidth}}};
            }
            newp = new AstCond{fl, testp,
                               new AstExprStmt{fl,
                                               new AstAssign{fl, nodep->top()->unlinkFrBack(),
                                                             nodep->fromp()->unlinkFrBack()},
                                               new AstConst{fl, AstConst::Signed32(), 1}},
                               new AstConst{fl, AstConst::Signed32(), 0}};
        } else if (castable == COMPATIBLE) {
            nodep->v3warn(CASTCONST, "$cast will always return one as "
                                         << toDtp->prettyDTypeNameQ()
                                         << " is always castable from "
                                         << fromDtp->prettyDTypeNameQ() << '\n'
                                         << nodep->warnMore() << "... Suggest static cast");
            newp = new AstExprStmt{
                fl,
                new AstAssign{fl, nodep->top()->unlinkFrBack(),
                              new AstCast{fl, nodep->fromp()->unlinkFrBack(), toDtp}},
                new AstConst{fl, AstConst::Signed32(), 1}};
        } else if (castable == INCOMPATIBLE) {
            newp = new AstConst{fl, 0};
            nodep->v3warn(CASTCONST, "$cast will always return zero as "
                                         << toDtp->prettyDTypeNameQ() << " is not castable from "
                                         << fromDtp->prettyDTypeNameQ());
        } else {
            newp = new AstConst{fl, 0};
            nodep->v3warn(E_UNSUPPORTED, "Unsupported: $cast to "
                                             << toDtp->prettyDTypeNameQ() << " from "
                                             << fromDtp->prettyDTypeNameQ() << '\n'
                                             << nodep->warnMore()
                                             << "... Suggest try static cast");
        }
        newp->dtypeFrom(nodep);
        nodep->replaceWith(newp);
        VL_DO_DANGLING(pushDeletep(nodep), nodep);
        userIterate(newp, m_vup);
    }
    virtual void visit(AstCastParse* nodep) override {
        // nodep->dtp could be data type, or a primary_constant
        // Don't iterate lhsp, will deal with that once convert the type
        V3Const::constifyParamsEdit(nodep->dtp());  // itemp may change
        if (AstConst* const constp = VN_CAST(nodep->dtp(), Const)) {
            constp->unlinkFrBack();
            AstNode* const newp
                = new AstCastSize(nodep->fileline(), nodep->lhsp()->unlinkFrBack(), constp);
            nodep->replaceWith(newp);
            VL_DO_DANGLING(pushDeletep(nodep), nodep);
            userIterate(newp, m_vup);
        } else {
            nodep->v3warn(E_UNSUPPORTED,
                          "Unsupported: Cast to " << nodep->dtp()->prettyTypeName());
            nodep->replaceWith(nodep->lhsp()->unlinkFrBack());
        }
    }
    virtual void visit(AstCast* nodep) override {
        nodep->dtypep(iterateEditMoveDTypep(nodep, nodep->subDTypep()));
        if (m_vup->prelim()) {
            // if (debug()) nodep->dumpTree(cout, "  CastPre: ");
            userIterateAndNext(nodep->fromp(), WidthVP(SELF, PRELIM).p());
            AstNodeDType* const toDtp = nodep->dtypep()->skipRefToEnump();
            AstNodeDType* const fromDtp = nodep->fromp()->dtypep()->skipRefToEnump();
            const auto castable = computeCastable(toDtp, fromDtp, nodep->fromp());
            bool bad = false;
            if (castable == UNSUPPORTED) {
                nodep->v3warn(E_UNSUPPORTED, "Unsupported: static cast to "
                                                 << toDtp->prettyDTypeNameQ() << " from "
                                                 << fromDtp->prettyDTypeNameQ());
                bad = true;
            } else if (castable == COMPATIBLE || castable == ENUM_IMPLICIT
                       || castable == ENUM_EXPLICIT) {
                ;  // Continue
            } else if (castable == DYNAMIC_CLASS) {
                nodep->v3error("Dynamic, not static cast, required to cast "
                               << toDtp->prettyDTypeNameQ() << " from "
                               << fromDtp->prettyDTypeNameQ() << '\n'
                               << nodep->warnMore() << "... Suggest dynamic $cast");
                bad = true;
            } else if (castable == INCOMPATIBLE) {
                nodep->v3error("Incompatible types to static cast to "
                               << toDtp->prettyDTypeNameQ() << " from "
                               << fromDtp->prettyDTypeNameQ() << '\n');
                bad = true;
            } else {
                nodep->v3fatalSrc("bad casting case");
            }
            // For now, replace it ASAP, so widthing can propagate easily
            // The cast may change signing, but we don't know the sign yet.  Make it so.
            // Note we don't sign fromp() that would make the algorithm O(n^2) if lots of casting.
            AstNode* newp = nullptr;
            if (bad) {
            } else if (const AstBasicDType* const basicp = toDtp->basicp()) {
                if (!basicp->isDouble() && !fromDtp->isDouble()) {
                    const int width = toDtp->width();
                    castSized(nodep, nodep->fromp(), width);
                    // Note castSized might modify nodep->fromp()
                } else {
                    iterateCheck(nodep, "value", nodep->lhsp(), SELF, FINAL, fromDtp, EXTEND_EXP,
                                 false);
                }
                if (basicp->isDouble() && !nodep->fromp()->isDouble()) {
                    if (nodep->fromp()->isSigned()) {
                        newp = new AstISToRD(nodep->fileline(), nodep->fromp()->unlinkFrBack());
                    } else {
                        newp = new AstIToRD(nodep->fileline(), nodep->fromp()->unlinkFrBack());
                    }
                } else if (!basicp->isDouble() && nodep->fromp()->isDouble()) {
                    if (basicp->isSigned()) {
                        newp
                            = new AstRToIRoundS(nodep->fileline(), nodep->fromp()->unlinkFrBack());
                    } else {
                        newp = new AstUnsigned(
                            nodep->fileline(),
                            new AstRToIS(nodep->fileline(), nodep->fromp()->unlinkFrBack()));
                    }
                } else if (basicp->isSigned() && !nodep->fromp()->isSigned()) {
                    newp = new AstSigned(nodep->fileline(), nodep->fromp()->unlinkFrBack());
                } else if (!basicp->isSigned() && nodep->fromp()->isSigned()) {
                    newp = new AstUnsigned(nodep->fileline(), nodep->fromp()->unlinkFrBack());
                } else {
                    // Can just remove cast
                }
            } else if (VN_IS(toDtp, ClassRefDType)) {
                // Can just remove cast
            } else {
                nodep->v3fatalSrc("Unimplemented: Casting non-simple data type "
                                  << toDtp->prettyDTypeNameQ());
            }
            if (!newp) newp = nodep->fromp()->unlinkFrBack();
            nodep->lhsp(newp);
            // if (debug()) nodep->dumpTree(cout, "  CastOut: ");
            // if (debug()) nodep->backp()->dumpTree(cout, "  CastOutUpUp: ");
        }
        if (m_vup->final()) {
            iterateCheck(nodep, "value", nodep->lhsp(), SELF, FINAL, nodep->lhsp()->dtypep(),
                         EXTEND_EXP, false);
            AstNode* const underp = nodep->lhsp()->unlinkFrBack();
            // if (debug()) underp->dumpTree(cout, "  CastRep: ");
            nodep->replaceWith(underp);
            VL_DO_DANGLING(pushDeletep(nodep), nodep);
        }
    }
    virtual void visit(AstCastSize* nodep) override {
        // IEEE: Signedness of result is same as self-determined signedness
        // However, the result is same as BITSEL, so we do not sign extend the LHS
        UASSERT_OBJ(VN_IS(nodep->rhsp(), Const), nodep, "Unsupported: Non-const cast of size");
        // if (debug()) nodep->dumpTree(cout, "  CastSizePre: ");
        if (m_vup->prelim()) {
            int width = VN_AS(nodep->rhsp(), Const)->toSInt();
            if (width < 1) {
                nodep->v3error("Size-changing cast to zero or negative size");
                width = 1;
            }
            userIterateAndNext(nodep->lhsp(), WidthVP(SELF, PRELIM).p());
            castSized(nodep, nodep->lhsp(), width);  // lhsp may change
        }
        if (m_vup->final()) {
            // CastSize not needed once sizes determined
            AstNode* const underp = nodep->lhsp()->unlinkFrBack();
            underp->dtypeFrom(nodep);
            nodep->replaceWith(underp);
            VL_DO_DANGLING(pushDeletep(nodep), nodep);
        }
        // if (debug()) nodep->dumpTree(cout, "  CastSizeOut: ");
    }
    void castSized(AstNode* nodep, AstNode* underp, int width) {
        const AstBasicDType* underDtp = VN_CAST(underp->dtypep(), BasicDType);
        if (!underDtp) underDtp = underp->dtypep()->basicp();
        if (!underDtp) {
            nodep->v3warn(E_UNSUPPORTED, "Unsupported: Size-changing cast on non-basic data type");
            underDtp = VN_AS(nodep->findBitDType(), BasicDType);
        }
        UASSERT_OBJ(underp == nodep->op1p(), nodep, "Assuming op1 is cast value");
        // A cast propagates its size to the lower expression and is included in the maximum
        // width, so 23'(1'b1 + 1'b1) uses 23-bit math, but 1'(2'h2 * 2'h1) uses two-bit math.
        // However the output width is exactly that requested.
        // So two steps, first do the calculation's width (max of the two widths)
        {
            const int calcWidth = std::max(width, underDtp->width());
            AstNodeDType* const calcDtp
                = (underDtp->isFourstate()
                       ? nodep->findLogicDType(calcWidth, calcWidth, underDtp->numeric())
                       : nodep->findBitDType(calcWidth, calcWidth, underDtp->numeric()));
            nodep->dtypep(calcDtp);
            // We ignore warnings as that is sort of the point of a cast
            iterateCheck(nodep, "Cast expr", underp, CONTEXT, FINAL, calcDtp, EXTEND_EXP, false);
            VL_DANGLING(underp);
            underp = nodep->op1p();  // Above asserts that op1 was underp pre-relink
        }
        // if (debug()) nodep->dumpTree(cout, "  CastSizeClc: ");
        // Next step, make the proper output width
        {
            AstNodeDType* const outDtp
                = (underDtp->isFourstate()
                       ? nodep->findLogicDType(width, width, underDtp->numeric())
                       : nodep->findBitDType(width, width, underDtp->numeric()));
            nodep->dtypep(outDtp);
            // We ignore warnings as that is sort of the point of a cast
            widthCheckSized(nodep, "Cast expr", underp, outDtp, EXTEND_EXP, false);
            VL_DANGLING(underp);
        }
    }
    virtual void visit(AstVar* nodep) override {
        // if (debug()) nodep->dumpTree(cout, "  InitPre: ");
        // Must have deterministic constant width
        // We can't skip this step when width()!=0, as creating a AstVar
        // with non-constant range gets size 1, not size 0.  So use didWidth().
        if (nodep->didWidth()) return;
        if (nodep->doingWidth()) {  // Early exit if have circular parameter definition
            UASSERT_OBJ(nodep->valuep(), nodep, "circular, but without value");
            nodep->v3error("Variable's initial value is circular: " << nodep->prettyNameQ());
            pushDeletep(nodep->valuep()->unlinkFrBack());
            nodep->valuep(new AstConst(nodep->fileline(), AstConst::BitTrue()));
            nodep->dtypeFrom(nodep->valuep());
            nodep->didWidth(true);
            return;
        }
        nodep->doingWidth(true);
        // Make sure dtype is sized
        nodep->dtypep(iterateEditMoveDTypep(nodep, nodep->subDTypep()));
        UASSERT_OBJ(nodep->dtypep(), nodep, "No dtype determined for var");
        if (const AstUnsizedArrayDType* const unsizedp
            = VN_CAST(nodep->dtypeSkipRefp(), UnsizedArrayDType)) {
            if (!(m_ftaskp && m_ftaskp->dpiImport())) {
                UINFO(9, "Unsized becomes dynamic array " << nodep << endl);
                AstDynArrayDType* const newp
                    = new AstDynArrayDType(unsizedp->fileline(), unsizedp->subDTypep());
                nodep->dtypep(newp);
                v3Global.rootp()->typeTablep()->addTypesp(newp);
            }
        }
        if (VN_IS(nodep->dtypep()->skipRefToConstp(), ConstDType)) nodep->isConst(true);
        // Parameters if implicit untyped inherit from what they are assigned to
        const AstBasicDType* const bdtypep = VN_CAST(nodep->dtypep(), BasicDType);
        bool didchk = false;
        const bool implicitParam = nodep->isParam() && bdtypep && bdtypep->implicit();
        if (implicitParam) {
            if (nodep->valuep()) {
                userIterateAndNext(nodep->valuep(), WidthVP(nodep->dtypep(), PRELIM).p());
                UINFO(9, "implicitParamPRELIMIV " << nodep->valuep() << endl);
                // Although nodep will get a different width for parameters
                // just below, we want the init numbers to retain their
                // width/minwidth until parameters are replaced.
                // This prevents width warnings at the location the parameter is substituted in
                if (nodep->valuep()->isDouble()) {
                    nodep->dtypeSetDouble();
                    VL_DANGLING(bdtypep);
                } else {
                    int width = 0;
                    const AstBasicDType* const valueBdtypep = nodep->valuep()->dtypep()->basicp();
                    bool issigned = false;
                    if (bdtypep->isNosign()) {
                        if (valueBdtypep && valueBdtypep->isSigned()) issigned = true;
                    } else {
                        issigned = bdtypep->isSigned();
                    }
                    if (valueBdtypep->isString()) {
                        // parameter X = "str", per IEEE is a number, not a string
                        if (const auto* const constp = VN_CAST(nodep->valuep(), Const)) {
                            if (constp->num().isString()) {
                                width = constp->num().toString().length() * 8;
                            }
                        }
                        if (width < 8) width = 8;
                    } else if (nodep->valuep()->dtypep()->widthSized()) {
                        width = nodep->valuep()->width();
                    } else {
                        if (nodep->valuep()->width() > 32) {
                            nodep->valuep()->v3warn(
                                WIDTH,
                                "Assigning >32 bit to unranged parameter (defaults to 32 bits)");
                        }
                        width = 32;
                    }
                    // Can't just inherit valuep()->dtypep() as mwidth might not equal width
                    if (width == 1) {
                        // one bit parameter is same as "parameter [0] foo",
                        // not "parameter logic foo" as you can extract
                        // "foo[0]" from a parameter but not a wire
                        nodep->dtypeChgWidthSigned(width, nodep->valuep()->widthMin(),
                                                   VSigning::fromBool(issigned));
                        nodep->dtypep(nodep->findLogicRangeDType(VNumRange{0, 0},
                                                                 nodep->valuep()->widthMin(),
                                                                 VSigning::fromBool(issigned)));
                    } else {
                        nodep->dtypeChgWidthSigned(width, nodep->valuep()->widthMin(),
                                                   VSigning::fromBool(issigned));
                    }
                    didchk = true;
                }
                iterateCheckAssign(nodep, "Initial value", nodep->valuep(), FINAL,
                                   nodep->dtypep());
                UINFO(9, "implicitParamFromIV " << nodep->valuep() << endl);
                // UINFO below will print variable nodep
            } else {
                // Or, if nothing assigned, they're integral
                nodep->dtypeSetSigned32();
                VL_DANGLING(bdtypep);
            }
        } else if (bdtypep && bdtypep->implicit()) {  // Implicits get converted to size 1
            nodep->dtypeSetLogicSized(1, bdtypep->numeric());
            VL_DANGLING(bdtypep);
        }
        if (nodep->valuep() && !didchk) {
            // if (debug()) nodep->dumpTree(cout, "  final: ");
            // AstPattern requires assignments to pass datatype on PRELIM
            userIterateAndNext(nodep->valuep(), WidthVP(nodep->dtypep(), PRELIM).p());
            iterateCheckAssign(nodep, "Initial value", nodep->valuep(), FINAL, nodep->dtypep());
        }
        UINFO(4, "varWidthed " << nodep << endl);
        // if (debug()) nodep->dumpTree(cout, "  InitOut: ");
        nodep->didWidth(true);
        nodep->doingWidth(false);
    }
    virtual void visit(AstNodeVarRef* nodep) override {
        if (nodep->didWidth()) return;
        if (!nodep->varp()) {
            if (m_paramsOnly && VN_IS(nodep, VarXRef)) {
                checkConstantOrReplace(
                    nodep, "Parameter-resolved constants must not use dotted references: "
                               + nodep->prettyNameQ());
                VL_DANGLING(nodep);
                return;
            } else {
                nodep->v3fatalSrc("Unlinked varref");
            }
        }
        if (!nodep->varp()->didWidth()) {
            // Var hasn't been widthed, so make it so.
            userIterate(nodep->varp(), nullptr);
        }
        // if (debug()>=9) { nodep->dumpTree(cout, "  VRin  ");
        //  nodep->varp()->dumpTree(cout, " forvar "); }
        // Note genvar's are also entered as integers
        nodep->dtypeFrom(nodep->varp());
        if (VN_IS(nodep->backp(), NodeAssign) && nodep->access().isWriteOrRW()) {  // On LHS
            UASSERT_OBJ(nodep->dtypep(), nodep, "LHS var should be dtype completed");
        }
        // if (debug() >= 9) nodep->dumpTree(cout, "  VRout ");
        if (nodep->access().isWriteOrRW() && nodep->varp()->direction() == VDirection::CONSTREF) {
            nodep->v3error("Assigning to const ref variable: " << nodep->prettyNameQ());
        } else if (nodep->access().isWriteOrRW() && nodep->varp()->isConst() && !m_paramsOnly
                   && (!m_ftaskp || !m_ftaskp->isConstructor())
                   && !VN_IS(m_procedurep, InitialStatic)) {
            // Too loose, but need to allow our generated first assignment
            // Move this to a property of the AstInitial block
            nodep->v3error("Assigning to const variable: " << nodep->prettyNameQ());
        }
        nodep->didWidth(true);
    }

    virtual void visit(AstEnumDType* nodep) override {
        if (nodep->didWidthAndSet()) return;  // This node is a dtype & not both PRELIMed+FINALed
        UINFO(5, "  ENUMDTYPE " << nodep << endl);
        nodep->refDTypep(iterateEditMoveDTypep(nodep, nodep->subDTypep()));
        nodep->dtypep(nodep);
        nodep->widthFromSub(nodep->subDTypep());
        // Assign widths
        userIterateAndNext(nodep->itemsp(), WidthVP(nodep->dtypep(), BOTH).p());
        // Assign missing values
        V3Number num(nodep, nodep->width(), 0);
        const V3Number one{nodep, nodep->width(), 1};
        std::map<const V3Number, AstEnumItem*> inits;
        for (AstEnumItem* itemp = nodep->itemsp(); itemp;
             itemp = VN_AS(itemp->nextp(), EnumItem)) {
            if (itemp->valuep()) {
                if (debug() >= 9) {
                    UINFO(0, "EnumInit " << itemp << endl);
                    itemp->valuep()->dumpTree(cout, "-EnumInit: ");
                }
                V3Const::constifyParamsEdit(itemp->valuep());  // itemp may change
                if (!VN_IS(itemp->valuep(), Const)) {
                    itemp->valuep()->v3error("Enum value isn't a constant");
                    itemp->valuep()->unlinkFrBack()->deleteTree();
                    continue;
                }
                // TODO IEEE says assigning sized number that is not same size as enum is illegal
            }
            if (!itemp->valuep()) {
                if (num.isEqZero() && itemp != nodep->itemsp()) {
                    itemp->v3error("Enum value illegally wrapped around (IEEE 1800-2017 6.19)");
                }
                if (num.isFourState()) {
                    itemp->v3error("Enum value that is unassigned cannot follow value with X/Zs "
                                   "(IEEE 1800-2017 6.19)");
                }
                if (!nodep->dtypep()->basicp()
                    && !nodep->dtypep()->basicp()->keyword().isIntNumeric()) {
                    itemp->v3error("Enum names without values only allowed on numeric types");
                    // as can't +1 to resolve them.
                }
                itemp->valuep(new AstConst(itemp->fileline(), num));
            }

            const AstConst* const constp = VN_AS(itemp->valuep(), Const);
            if (constp->num().isFourState() && nodep->dtypep()->basicp()
                && !nodep->dtypep()->basicp()->isFourstate()) {
                itemp->v3error("Enum value with X/Zs cannot be assigned to non-fourstate type "
                               "(IEEE 1800-2017 6.19)");
            }
            num.opAssign(constp->num());
            // Look for duplicates
            if (inits.find(num) != inits.end()) {  // IEEE says illegal
                const AstNode* const otherp = inits.find(num)->second;
                itemp->v3error("Overlapping enumeration value: "
                               << itemp->prettyNameQ() << '\n'
                               << itemp->warnContextPrimary() << '\n'
                               << otherp->warnOther() << "... Location of original declaration\n"
                               << otherp->warnContextSecondary());
            } else {
                inits.emplace(num, itemp);
            }
            num.opAdd(one, constp->num());
        }
    }
    virtual void visit(AstEnumItem* nodep) override {
        UINFO(5, "   ENUMITEM " << nodep << endl);
        AstNodeDType* const vdtypep = m_vup->dtypep();
        UASSERT_OBJ(vdtypep, nodep, "ENUMITEM not under ENUM");
        nodep->dtypep(vdtypep);
        if (nodep->valuep()) {  // else the value will be assigned sequentially
            // Default type is int, but common to assign narrower values, so minwidth from value
            userIterateAndNext(nodep->valuep(), WidthVP(CONTEXT, PRELIM).p());
            // Minwidth does not come from value, as spec says set based on parent
            // and if we keep minwidth we'll consider it unsized which is incorrect
            iterateCheck(nodep, "Enum value", nodep->valuep(), CONTEXT, FINAL, nodep->dtypep(),
                         EXTEND_EXP);
        }
    }
    virtual void visit(AstEnumItemRef* nodep) override {
        if (!nodep->itemp()->didWidth()) {
            // We need to do the whole enum en-mass
            AstNode* enump = nodep->itemp();
            UASSERT_OBJ(enump, nodep, "EnumItemRef not linked");
            for (; enump; enump = enump->backp()) {
                if (VN_IS(enump, EnumDType)) break;
            }
            UASSERT_OBJ(enump, nodep, "EnumItemRef can't deref back to an Enum");
            VL_DO_DANGLING(userIterate(enump, m_vup), enump);  // Parent enump maybe relinked
        }
        nodep->dtypeFrom(nodep->itemp());
    }
    virtual void visit(AstConsAssoc* nodep) override {
        // Type computed when constructed here
        auto* const vdtypep = VN_AS(m_vup->dtypep()->skipRefp(), AssocArrayDType);
        UASSERT_OBJ(vdtypep, nodep, "ConsAssoc requires assoc upper parent data type");
        if (m_vup->prelim()) {
            nodep->dtypeFrom(vdtypep);
            if (nodep->defaultp()) {
                iterateCheck(nodep, "default", nodep->defaultp(), CONTEXT, FINAL,
                             vdtypep->subDTypep(), EXTEND_EXP);
            }
        }
    }
    virtual void visit(AstSetAssoc* nodep) override {
        // Type computed when constructed here
        auto* const vdtypep = VN_AS(m_vup->dtypep()->skipRefp(), AssocArrayDType);
        UASSERT_OBJ(vdtypep, nodep, "SetsAssoc requires assoc upper parent data type");
        if (m_vup->prelim()) {
            nodep->dtypeFrom(vdtypep);
            userIterateAndNext(nodep->lhsp(), WidthVP(vdtypep, BOTH).p());
            iterateCheck(nodep, "key", nodep->keyp(), CONTEXT, FINAL, vdtypep->keyDTypep(),
                         EXTEND_EXP);
            iterateCheck(nodep, "value", nodep->valuep(), CONTEXT, FINAL, vdtypep->subDTypep(),
                         EXTEND_EXP);
        }
    }
    virtual void visit(AstConsWildcard* nodep) override {
        // Type computed when constructed here
        auto* const vdtypep = VN_AS(m_vup->dtypep()->skipRefp(), WildcardArrayDType);
        UASSERT_OBJ(vdtypep, nodep, "ConsWildcard requires wildcard upper parent data type");
        if (m_vup->prelim()) {
            nodep->dtypeFrom(vdtypep);
            if (nodep->defaultp()) {
                iterateCheck(nodep, "default", nodep->defaultp(), CONTEXT, FINAL,
                             vdtypep->subDTypep(), EXTEND_EXP);
            }
        }
    }
    virtual void visit(AstSetWildcard* nodep) override {
        // Type computed when constructed here
        auto* const vdtypep = VN_AS(m_vup->dtypep()->skipRefp(), WildcardArrayDType);
        UASSERT_OBJ(vdtypep, nodep, "SetWildcard requires wildcard upper parent data type");
        if (m_vup->prelim()) {
            nodep->dtypeFrom(vdtypep);
            userIterateAndNext(nodep->lhsp(), WidthVP{vdtypep, BOTH}.p());
            iterateCheck(nodep, "key", nodep->keyp(), CONTEXT, FINAL, vdtypep->findStringDType(),
                         EXTEND_EXP);
            iterateCheck(nodep, "value", nodep->valuep(), CONTEXT, FINAL, vdtypep->subDTypep(),
                         EXTEND_EXP);
        }
    }
    virtual void visit(AstConsDynArray* nodep) override {
        // Type computed when constructed here
        AstDynArrayDType* const vdtypep = VN_AS(m_vup->dtypep()->skipRefp(), DynArrayDType);
        UASSERT_OBJ(vdtypep, nodep, "ConsDynArray requires queue upper parent data type");
        if (m_vup->prelim()) {
            userIterateAndNext(nodep->lhsp(), WidthVP(vdtypep, PRELIM).p());
            userIterateAndNext(nodep->rhsp(), WidthVP(vdtypep, PRELIM).p());
            nodep->dtypeFrom(vdtypep);
        }
        if (m_vup->final()) {
            // Arguments can be either elements of the queue or a queue itself
            // Concats (part of tree of concats) must always become ConsDynArray's
            if (nodep->lhsp()) {
                if (VN_IS(nodep->lhsp()->dtypep(), DynArrayDType)
                    || VN_IS(nodep->lhsp(), ConsDynArray)) {
                    userIterateAndNext(nodep->lhsp(), WidthVP(vdtypep, FINAL).p());
                } else {
                    // Sub elements are not queues, but concats, must always pass concats down
                    iterateCheckTyped(nodep, "LHS", nodep->lhsp(), vdtypep->subDTypep(), FINAL);
                }
            }
            if (nodep->rhsp()) {
                if (VN_IS(nodep->rhsp()->dtypep(), DynArrayDType)
                    || VN_IS(nodep->rhsp(), ConsDynArray)) {
                    userIterateAndNext(nodep->rhsp(), WidthVP(vdtypep, FINAL).p());
                } else {
                    iterateCheckTyped(nodep, "RHS", nodep->rhsp(), vdtypep->subDTypep(), FINAL);
                }
            }
            nodep->dtypeFrom(vdtypep);
        }
    }
    virtual void visit(AstConsQueue* nodep) override {
        // Type computed when constructed here
        AstQueueDType* const vdtypep = VN_AS(m_vup->dtypep()->skipRefp(), QueueDType);
        UASSERT_OBJ(vdtypep, nodep, "ConsQueue requires queue upper parent data type");
        if (m_vup->prelim()) {
            userIterateAndNext(nodep->lhsp(), WidthVP(vdtypep, PRELIM).p());
            userIterateAndNext(nodep->rhsp(), WidthVP(vdtypep, PRELIM).p());
            nodep->dtypeFrom(vdtypep);
        }
        if (m_vup->final()) {
            // Arguments can be either elements of the queue or a queue itself
            // Concats (part of tree of concats) must always become ConsQueue's
            if (nodep->lhsp()) {
                if (VN_IS(nodep->lhsp()->dtypep(), QueueDType)
                    || VN_IS(nodep->lhsp(), ConsQueue)) {
                    userIterateAndNext(nodep->lhsp(), WidthVP(vdtypep, FINAL).p());
                } else {
                    // Sub elements are not queues, but concats, must always pass concats down
                    iterateCheckTyped(nodep, "LHS", nodep->lhsp(), vdtypep->subDTypep(), FINAL);
                }
            }
            if (nodep->rhsp()) {
                if (VN_IS(nodep->rhsp()->dtypep(), QueueDType)
                    || VN_IS(nodep->rhsp(), ConsQueue)) {
                    userIterateAndNext(nodep->rhsp(), WidthVP(vdtypep, FINAL).p());
                } else {
                    iterateCheckTyped(nodep, "RHS", nodep->rhsp(), vdtypep->subDTypep(), FINAL);
                }
            }
            nodep->dtypeFrom(vdtypep);
        }
    }
    virtual void visit(AstInitItem* nodep) override {  //
        userIterateChildren(nodep, m_vup);
    }
    virtual void visit(AstInitArray* nodep) override {
        // InitArray has type of the array; children are array values
        if (m_vup->prelim()) {  // First stage evaluation
            AstNodeDType* const vdtypep = m_vup->dtypeNullp();
            UASSERT_OBJ(vdtypep, nodep, "InitArray type not assigned by AstPattern/Var visitor");
            nodep->dtypep(vdtypep);
            const AstNodeDType* const arrayp = vdtypep->skipRefp();
            if (VN_IS(arrayp, NodeArrayDType) || VN_IS(arrayp, AssocArrayDType)) {
                userIterateChildren(nodep, WidthVP(arrayp->subDTypep(), BOTH).p());
            } else {
                UINFO(1, "dtype object " << vdtypep->skipRefp() << endl);
                nodep->v3fatalSrc("InitArray on non-array");
            }
        }
    }
    virtual void visit(AstInside* nodep) override {
        userIterateAndNext(nodep->exprp(), WidthVP(CONTEXT, PRELIM).p());
        for (AstNode *nextip, *itemp = nodep->itemsp(); itemp; itemp = nextip) {
            nextip = itemp->nextp();  // Prelim may cause the node to get replaced
            VL_DO_DANGLING(userIterate(itemp, WidthVP(CONTEXT, PRELIM).p()), itemp);
        }
        // Take width as maximum across all items
        int width = nodep->exprp()->width();
        int mwidth = nodep->exprp()->widthMin();
        for (const AstNode* itemp = nodep->itemsp(); itemp; itemp = itemp->nextp()) {
            width = std::max(width, itemp->width());
            mwidth = std::max(mwidth, itemp->widthMin());
        }
        // Apply width
        AstNodeDType* const subDTypep
            = nodep->findLogicDType(width, mwidth, nodep->exprp()->dtypep()->numeric());
        iterateCheck(nodep, "Inside expression", nodep->exprp(), CONTEXT, FINAL, subDTypep,
                     EXTEND_EXP);
        for (AstNode* itemp = nodep->itemsp(); itemp; itemp = itemp->nextp()) {
            iterateCheck(nodep, "Inside Item", itemp, CONTEXT, FINAL, subDTypep, EXTEND_EXP);
        }
        nodep->dtypeSetBit();
        if (debug() >= 9) nodep->dumpTree(cout, "-inside-in: ");
        // Now rip out the inside and replace with simple math
        AstNode* newp = nullptr;
        for (AstNode *nextip, *itemp = nodep->itemsp(); itemp; itemp = nextip) {
            nextip = itemp->nextp();  // Will be unlinking
            AstNode* inewp;
            const AstNodeDType* const itemDtp = itemp->dtypep()->skipRefp();
            if (AstInsideRange* const irangep = VN_CAST(itemp, InsideRange)) {
                // Similar logic in V3Case
                inewp = irangep->newAndFromInside(nodep->exprp(), irangep->lhsp()->unlinkFrBack(),
                                                  irangep->rhsp()->unlinkFrBack());
            } else if (VN_IS(itemDtp, UnpackArrayDType)) {
                nodep->v3error("Unsupported: inside (set membership operator) on unpacked array");
                // Need the AstInside type to persist, then
                // for parameters, need V3Simulate support.
                // For non-parameters, need runtime support.
                continue;
            } else if (VN_IS(itemDtp, AssocArrayDType) || VN_IS(itemDtp, DynArrayDType)
                       || VN_IS(itemDtp, QueueDType)) {
                nodep->v3error(
                    "Inside operator not legal on non-unpacked arrays (IEEE 1800-2017 11.4.13)");
                continue;
            } else {
                inewp = new AstEqWild(itemp->fileline(), nodep->exprp()->cloneTree(true),
                                      itemp->unlinkFrBack());
            }
            if (newp) {
                newp = new AstOr(nodep->fileline(), newp, inewp);
            } else {
                newp = inewp;
            }
        }
        if (!newp) newp = new AstConst(nodep->fileline(), AstConst::BitFalse());
        if (debug() >= 9) newp->dumpTree(cout, "-inside-out: ");
        nodep->replaceWith(newp);
        VL_DO_DANGLING(pushDeletep(nodep), nodep);
    }
    virtual void visit(AstInsideRange* nodep) override {
        // Just do each side; AstInside will rip these nodes out later
        userIterateAndNext(nodep->lhsp(), m_vup);
        userIterateAndNext(nodep->rhsp(), m_vup);
        nodep->dtypeFrom(nodep->lhsp());
    }

    virtual void visit(AstIfaceRefDType* nodep) override {
        if (nodep->didWidthAndSet()) return;  // This node is a dtype & not both PRELIMed+FINALed
        UINFO(5, "   IFACEREF " << nodep << endl);
        userIterateChildren(nodep, m_vup);
        nodep->dtypep(nodep);
        nodep->widthForce(1, 1);  // Not really relevant
        UINFO(4, "dtWidthed " << nodep << endl);
    }
    virtual void visit(AstNodeUOrStructDType* nodep) override {
        if (nodep->didWidthAndSet()) return;  // This node is a dtype & not both PRELIMed+FINALed
        UINFO(5, "   NODECLASS " << nodep << endl);
        // if (debug() >= 9) nodep->dumpTree("-class-in--");
        if (!nodep->packed()) {
            nodep->v3warn(UNPACKED, "Unsupported: Unpacked struct/union");
            if (!v3Global.opt.structsPacked()) {
                nodep->v3warn(UNPACKED, "Unsupported: --no-structs-packed");
            }
        }
        userIterateChildren(nodep, nullptr);  // First size all members
        nodep->repairMemberCache();
        // Determine bit assignments and width
        nodep->dtypep(nodep);
        int lsb = 0;
        int width = 0;
        nodep->isFourstate(false);
        // MSB is first, so go backwards
        AstMemberDType* itemp;
        for (itemp = nodep->membersp(); itemp && itemp->nextp();
             itemp = VN_AS(itemp->nextp(), MemberDType)) {}
        for (AstMemberDType* backip; itemp; itemp = backip) {
            if (itemp->isFourstate()) nodep->isFourstate(true);
            backip = VN_CAST(itemp->backp(), MemberDType);
            itemp->lsb(lsb);
            if (VN_IS(nodep, UnionDType)) {
                width = std::max(width, itemp->width());
            } else {
                lsb += itemp->width();
                width += itemp->width();
            }
        }
        nodep->widthForce(width, width);  // Signing stays as-is, as parsed from declaration
        // if (debug() >= 9) nodep->dumpTree("-class-out-");
    }
    virtual void visit(AstClass* nodep) override {
        if (nodep->didWidthAndSet()) return;
        // Must do extends first, as we may in functions under this class
        // start following a tree of extends that takes us to other classes
        userIterateAndNext(nodep->extendsp(), nullptr);
        userIterateChildren(nodep, nullptr);  // First size all members
        nodep->repairCache();
    }
    virtual void visit(AstClassRefDType* nodep) override {
        if (nodep->didWidthAndSet()) return;
        // TODO this maybe eventually required to properly resolve members,
        // though causes problems with t_class_forward.v, so for now avoided
        // userIterateChildren(nodep->classp(), nullptr);
    }
    virtual void visit(AstClassOrPackageRef* nodep) override {
        if (nodep->didWidthAndSet()) return;
        userIterateChildren(nodep, nullptr);
    }
    virtual void visit(AstDot* nodep) override {
        // We can only reach this from constify called during V3Param (so before linkDotParam)
        // ... #(Cls#(...)::...) ...
        //                ^^~~~ this is our DOT
        nodep->v3warn(E_UNSUPPORTED, "dotted expressions in parameters\n"
                                         << nodep->warnMore() << "... Suggest use a typedef");
    }
    virtual void visit(AstClassExtends* nodep) override {
        if (nodep->didWidthAndSet()) return;
        if (VN_IS(nodep->childDTypep(), ClassRefDType)) {
            nodep->dtypep(iterateEditMoveDTypep(nodep, nodep->childDTypep()));
        }
    }
    virtual void visit(AstMemberDType* nodep) override {
        if (nodep->didWidthAndSet()) return;  // This node is a dtype & not both PRELIMed+FINALed
        // Iterate into subDTypep() to resolve that type and update pointer.
        nodep->refDTypep(iterateEditMoveDTypep(nodep, nodep->subDTypep()));
        nodep->dtypep(nodep);  // The member itself, not subDtype
        nodep->widthFromSub(nodep->subDTypep());
    }
    virtual void visit(AstMemberSel* nodep) override {
        UINFO(5, "   MEMBERSEL " << nodep << endl);
        if (debug() >= 9) nodep->dumpTree("-mbs-in: ");
        userIterateChildren(nodep, WidthVP(SELF, BOTH).p());
        if (debug() >= 9) nodep->dumpTree("-mbs-ic: ");
        // Find the fromp dtype - should be a class
        if (!nodep->fromp()->dtypep()) nodep->fromp()->v3fatalSrc("Unlinked data type");
        AstNodeDType* const fromDtp = nodep->fromp()->dtypep()->skipRefToEnump();
        UINFO(9, "     from dt " << fromDtp << endl);
        if (AstNodeUOrStructDType* const adtypep = VN_CAST(fromDtp, NodeUOrStructDType)) {
            if (memberSelStruct(nodep, adtypep)) return;
        } else if (AstClassRefDType* const adtypep = VN_CAST(fromDtp, ClassRefDType)) {
            if (AstNode* const foundp = memberSelClass(nodep, adtypep)) {
                if (AstVar* const varp = VN_CAST(foundp, Var)) {
                    nodep->dtypep(foundp->dtypep());
                    nodep->varp(varp);
                    return;
                }
                if (AstEnumItemRef* const adfoundp = VN_CAST(foundp, EnumItemRef)) {
                    nodep->replaceWith(adfoundp->cloneTree(false));
                    return;
                }
                UINFO(1, "found object " << foundp << endl);
                nodep->v3fatalSrc("MemberSel of non-variable\n"
                                  << nodep->warnContextPrimary() << '\n'
                                  << foundp->warnOther() << "... Location of found object\n"
                                  << foundp->warnContextSecondary());
            }
        } else if (VN_IS(fromDtp, EnumDType)  //
                   || VN_IS(fromDtp, AssocArrayDType)  //
                   || VN_IS(fromDtp, WildcardArrayDType)  //
                   || VN_IS(fromDtp, UnpackArrayDType)  //
                   || VN_IS(fromDtp, DynArrayDType)  //
                   || VN_IS(fromDtp, QueueDType)  //
                   || VN_IS(fromDtp, BasicDType)) {
            // Method call on enum without following parenthesis, e.g. "ENUM.next"
            // Convert this into a method call, and let that visitor figure out what to do next
            AstNode* const newp = new AstMethodCall(
                nodep->fileline(), nodep->fromp()->unlinkFrBack(), nodep->name(), nullptr);
            nodep->replaceWith(newp);
            VL_DO_DANGLING(pushDeletep(nodep), nodep);
            userIterate(newp, m_vup);
            return;
        } else {
            nodep->v3error("Member selection of non-struct/union object '"
                           << nodep->fromp()->prettyTypeName() << "' which is a '"
                           << nodep->fromp()->dtypep()->prettyTypeName() << "'");
        }
        // Error handling
        nodep->replaceWith(new AstConst(nodep->fileline(), AstConst::BitFalse()));
        VL_DO_DANGLING(pushDeletep(nodep), nodep);
    }
    AstNode* memberSelClass(AstMemberSel* nodep, AstClassRefDType* adtypep) {
        // Returns node if ok
        // No need to width-resolve the class, as it was done when we did the child
        AstClass* const first_classp = adtypep->classp();
        UASSERT_OBJ(first_classp, nodep, "Unlinked");
        for (AstClass* classp = first_classp; classp;) {
            if (AstNode* const foundp = classp->findMember(nodep->name())) return foundp;
            classp = classp->extendsp() ? classp->extendsp()->classp() : nullptr;
        }
        VSpellCheck speller;
        for (AstClass* classp = first_classp; classp;) {
            for (AstNode* itemp = classp->membersp(); itemp; itemp = itemp->nextp()) {
                if (VN_IS(itemp, Var) || VN_IS(itemp, EnumItemRef)) {
                    speller.pushCandidate(itemp->prettyName());
                }
            }
            classp = classp->extendsp() ? classp->extendsp()->classp() : nullptr;
        }
        const string suggest = speller.bestCandidateMsg(nodep->prettyName());
        nodep->v3error(
            "Member " << nodep->prettyNameQ() << " not found in class "
                      << first_classp->prettyNameQ() << "\n"
                      << (suggest.empty() ? "" : nodep->fileline()->warnMore() + suggest));
        return nullptr;  // Caller handles error
    }
    bool memberSelStruct(AstMemberSel* nodep, AstNodeUOrStructDType* adtypep) {
        // Returns true if ok
        if (AstMemberDType* const memberp = adtypep->findMember(nodep->name())) {
            if (m_attrp) {  // Looking for the base of the attribute
                nodep->dtypep(memberp);
                UINFO(9, "   MEMBERSEL(attr) -> " << nodep << endl);
                UINFO(9, "           dt-> " << nodep->dtypep() << endl);
            } else {
                AstSel* const newp = new AstSel(nodep->fileline(), nodep->fromp()->unlinkFrBack(),
                                                memberp->lsb(), memberp->width());
                // Must skip over the member to find the union; as the member may disappear later
                newp->dtypep(memberp->subDTypep()->skipRefToEnump());
                newp->didWidth(true);  // Don't replace dtype with basic type
                UINFO(9, "   MEMBERSEL -> " << newp << endl);
                UINFO(9, "           dt-> " << newp->dtypep() << endl);
                nodep->replaceWith(newp);
                VL_DO_DANGLING(pushDeletep(nodep), nodep);
                // Should be able to treat it as a normal-ish nodesel - maybe.
                // The lhsp() will be strange until this stage; create the number here?
            }
            return true;
        }
        nodep->v3error("Member " << nodep->prettyNameQ() << " not found in structure");
        return false;
    }

    virtual void visit(AstCMethodHard* nodep) override {
        // Never created before V3Width, so no need to redo it
        UASSERT_OBJ(nodep->dtypep(), nodep, "CMETHODCALLs should have already been sized");
    }

    virtual void visit(AstMethodCall* nodep) override {
        UINFO(5, "   METHODCALL " << nodep << endl);
        if (nodep->didWidth()) return;
        if (debug() >= 9) nodep->dumpTree("-mts-in: ");
        // Should check types the method requires, but at present we don't do much
        userIterate(nodep->fromp(), WidthVP(SELF, BOTH).p());
        // Any AstWith is checked later when know types, in methodWithArgument
        for (AstArg* argp = VN_CAST(nodep->pinsp(), Arg); argp; argp = VN_AS(argp->nextp(), Arg)) {
            if (argp->exprp()) userIterate(argp->exprp(), WidthVP(SELF, BOTH).p());
        }
        // Find the fromp dtype - should be a class
        UASSERT_OBJ(nodep->fromp() && nodep->fromp()->dtypep(), nodep, "Unsized expression");
        AstNodeDType* const fromDtp = nodep->fromp()->dtypep()->skipRefToEnump();
        AstBasicDType* const basicp = fromDtp ? fromDtp->basicp() : nullptr;
        UINFO(9, "     from dt " << fromDtp << endl);
        userIterate(fromDtp, WidthVP(SELF, BOTH).p());
        if (AstEnumDType* const adtypep = VN_CAST(fromDtp, EnumDType)) {
            methodCallEnum(nodep, adtypep);
        } else if (AstAssocArrayDType* const adtypep = VN_CAST(fromDtp, AssocArrayDType)) {
            methodCallAssoc(nodep, adtypep);
        } else if (AstWildcardArrayDType* const adtypep = VN_CAST(fromDtp, WildcardArrayDType)) {
            methodCallWildcard(nodep, adtypep);
        } else if (AstDynArrayDType* const adtypep = VN_CAST(fromDtp, DynArrayDType)) {
            methodCallDyn(nodep, adtypep);
        } else if (AstQueueDType* const adtypep = VN_CAST(fromDtp, QueueDType)) {
            methodCallQueue(nodep, adtypep);
        } else if (AstClassRefDType* const adtypep = VN_CAST(fromDtp, ClassRefDType)) {
            methodCallClass(nodep, adtypep);
        } else if (AstUnpackArrayDType* const adtypep = VN_CAST(fromDtp, UnpackArrayDType)) {
            methodCallUnpack(nodep, adtypep);
        } else if (basicp && basicp->isEventValue()) {
            methodCallEvent(nodep, basicp);
        } else if (basicp && basicp->isString()) {
            methodCallString(nodep, basicp);
        } else {
            nodep->v3warn(E_UNSUPPORTED, "Unsupported: Member call on object '"
                                             << nodep->fromp()->prettyTypeName()
                                             << "' which is a '"
                                             << nodep->fromp()->dtypep()->prettyTypeName() << "'");
        }
    }
    AstWith* methodWithArgument(AstMethodCall* nodep, bool required, bool arbReturn,
                                AstNodeDType* returnDtp, AstNodeDType* indexDtp,
                                AstNodeDType* valueDtp) {
        UASSERT_OBJ(arbReturn || returnDtp, nodep, "Null return type");
        if (AstWith* const withp = VN_CAST(nodep->pinsp(), With)) {
            withp->indexArgRefp()->dtypep(indexDtp);
            withp->valueArgRefp()->dtypep(valueDtp);
            userIterate(withp, WidthVP(returnDtp, BOTH).p());
            withp->unlinkFrBack();
            return withp;
        } else if (required) {
            nodep->v3error("'with' statement is required for ." << nodep->prettyName()
                                                                << " method");
        }
        return nullptr;
    }
    void methodOkArguments(AstMethodCall* nodep, int minArg, int maxArg) {
        int narg = 0;
        for (AstNode* argp = nodep->pinsp(); argp; argp = argp->nextp()) {
            if (VN_IS(argp, With)) {
                argp->v3error("'with' not legal on this method");
                // Delete all arguments as nextp() otherwise dangling
                VL_DO_DANGLING(pushDeletep(argp->unlinkFrBackWithNext()), argp);
                break;
            }
            ++narg;
            UASSERT_OBJ(VN_IS(argp, Arg), nodep, "Method arg without Arg type");
        }
        const bool ok = (narg >= minArg) && (narg <= maxArg);
        if (!ok) {
            nodep->v3error("The " << narg << " arguments passed to ." << nodep->prettyName()
                                  << " method does not match its requiring " << cvtToStr(minArg)
                                  << (minArg == maxArg ? "" : " to " + cvtToStr(maxArg))
                                  << " arguments");
            // Adjust to required argument counts, very bogus, but avoids core dump
            for (; narg < minArg; ++narg) {
                nodep->addPinsp(
                    new AstArg(nodep->fileline(), "", new AstConst(nodep->fileline(), 0)));
            }
            for (; narg > maxArg; --narg) {
                AstNode* argp = nodep->pinsp();
                while (argp->nextp()) argp = argp->nextp();
                argp->unlinkFrBack();
                VL_DO_DANGLING(argp->deleteTree(), argp);
            }
        }
    }

    void methodCallEnum(AstMethodCall* nodep, AstEnumDType* adtypep) {
        // Method call on enum without following parenthesis, e.g. "ENUM.next"
        // Convert this into a method call, and let that visitor figure out what to do next
        if (adtypep) {}
        if (nodep->name() == "num"  //
            || nodep->name() == "first"  //
            || nodep->name() == "last") {
            // Constant value
            AstConst* newp = nullptr;
            methodOkArguments(nodep, 0, 0);
            if (nodep->name() == "num") {
                int items = 0;
                for (AstNode* itemp = adtypep->itemsp(); itemp; itemp = itemp->nextp()) ++items;
                newp = new AstConst(nodep->fileline(), AstConst::Signed32(), items);
            } else if (nodep->name() == "first") {
                const AstEnumItem* itemp = adtypep->itemsp();
                if (!itemp) {
                    newp = new AstConst(nodep->fileline(), AstConst::Signed32(),
                                        0);  // Spec doesn't say what to do
                } else {
                    newp = VN_AS(itemp->valuep()->cloneTree(false), Const);  // A const
                }
            } else if (nodep->name() == "last") {
                const AstEnumItem* itemp = adtypep->itemsp();
                while (itemp && itemp->nextp()) itemp = VN_AS(itemp->nextp(), EnumItem);
                if (!itemp) {
                    newp = new AstConst(nodep->fileline(), AstConst::Signed32(),
                                        0);  // Spec doesn't say what to do
                } else {
                    newp = VN_AS(itemp->valuep()->cloneTree(false), Const);  // A const
                }
            }
            UASSERT_OBJ(newp, nodep, "Enum method (perhaps enum item) not const");
            newp->fileline(nodep->fileline());  // Use method's filename/line number to be clearer;
                                                // may have warning disables
            nodep->replaceWith(newp);
            VL_DO_DANGLING(pushDeletep(nodep), nodep);
        } else if (nodep->name() == "name" || nodep->name() == "next" || nodep->name() == "prev") {
            VAttrType attrType;
            if (nodep->name() == "name") {
                attrType = VAttrType::ENUM_NAME;
            } else if (nodep->name() == "next") {
                attrType = VAttrType::ENUM_NEXT;
            } else if (nodep->name() == "prev") {
                attrType = VAttrType::ENUM_PREV;
            } else {
                nodep->v3fatalSrc("Bad case");
            }

            if (nodep->name() == "name") {
                methodOkArguments(nodep, 0, 0);
            } else if (nodep->pinsp() && !(VN_IS(VN_AS(nodep->pinsp(), Arg)->exprp(), Const))) {
                nodep->pinsp()->v3fatalSrc("Unsupported: enum next/prev with non-const argument");
            } else if (nodep->pinsp()
                       && !(VN_IS(VN_AS(nodep->pinsp(), Arg)->exprp(), Const)
                            && VN_AS(VN_AS(nodep->pinsp(), Arg)->exprp(), Const)->toUInt() == 1
                            && !nodep->pinsp()->nextp())) {
                // Unroll of enumVar.next(k) to enumVar.next(1).next(k - 1)
                AstMethodCall* const clonep = nodep->cloneTree(false);
                VN_AS(VN_AS(clonep->pinsp(), Arg)->exprp(), Const)->num().setLong(1);
                const uint32_t stepWidth
                    = VN_AS(VN_AS(nodep->pinsp(), Arg)->exprp(), Const)->toUInt();
                AstConst* const constp = new AstConst(nodep->fileline(), stepWidth - 1);
                AstArg* const argp = new AstArg(nodep->fileline(), "", constp);
                AstMethodCall* const newp
                    = new AstMethodCall(nodep->fileline(), clonep, nodep->name(), argp);
                nodep->replaceWith(newp);
                VL_DO_DANGLING(nodep->deleteTree(), nodep);
                return;
            }
            // Need a runtime lookup table.  Yuk.
            const uint64_t msbdim = enumMaxValue(nodep, adtypep);
            const bool assoc = msbdim > ENUM_LOOKUP_BITS;
            if (assoc) {
                AstVar* const varp = enumVarp(adtypep, attrType, true, 0);
                AstNode* const newp = new AstAssocSel{nodep->fileline(), newVarRefDollarUnit(varp),
                                                      nodep->fromp()->unlinkFrBack()};
                nodep->replaceWith(newp);
            } else {
                const int selwidth = V3Number::log2b(msbdim) + 1;  // Width to address a bit
                AstVar* const varp = enumVarp(adtypep, attrType, false, (1ULL << selwidth) - 1);
                AstNode* const newp = new AstArraySel(
                    nodep->fileline(), newVarRefDollarUnit(varp),
                    // Select in case widths are off due to msblen!=width
                    // We return "random" values if outside the range, which is fine
                    // as next/previous on illegal values just need something good out
                    new AstSel(nodep->fileline(), nodep->fromp()->unlinkFrBack(), 0, selwidth));
                nodep->replaceWith(newp);
            }
            VL_DO_DANGLING(nodep->deleteTree(), nodep);
        } else {
            nodep->v3error("Unknown built-in enum method " << nodep->prettyNameQ());
        }
    }
    void methodCallWildcard(AstMethodCall* nodep, AstWildcardArrayDType* adtypep) {
        AstCMethodHard* newp = nullptr;
        if (nodep->name() == "num"  // function int num()
            || nodep->name() == "size") {
            methodOkArguments(nodep, 0, 0);
            newp = new AstCMethodHard{nodep->fileline(), nodep->fromp()->unlinkFrBack(),
                                      "size"};  // So don't need num()
            newp->dtypeSetSigned32();
        } else if (nodep->name() == "first"  // function int first(ref index)
                   || nodep->name() == "last"  //
                   || nodep->name() == "next"  //
                   || nodep->name() == "prev"  //
                   || nodep->name() == "unique_index"  //
                   || nodep->name() == "find_index" || nodep->name() == "find_first_index"
                   || nodep->name() == "find_last_index") {
            nodep->v3error("Array method " << nodep->prettyNameQ()
                                           << " not legal on wildcard associative arrays");
        } else if (nodep->name() == "exists") {  // function int exists(input index)
            // IEEE really should have made this a "bit" return
            methodOkArguments(nodep, 1, 1);
            AstNode* const index_exprp = methodCallWildcardIndexExpr(nodep, adtypep);
            newp = new AstCMethodHard{nodep->fileline(), nodep->fromp()->unlinkFrBack(), "exists",
                                      index_exprp->unlinkFrBack()};
            newp->dtypeSetSigned32();
            newp->pure(true);
        } else if (nodep->name() == "delete") {  // function void delete([input integer index])
            methodOkArguments(nodep, 0, 1);
            methodCallLValueRecurse(nodep, nodep->fromp(), VAccess::WRITE);
            if (!nodep->pinsp()) {
                newp = new AstCMethodHard{nodep->fileline(), nodep->fromp()->unlinkFrBack(),
                                          "clear"};
                newp->makeStatement();
            } else {
                AstNode* const index_exprp = methodCallWildcardIndexExpr(nodep, adtypep);
                newp = new AstCMethodHard{nodep->fileline(), nodep->fromp()->unlinkFrBack(),
                                          "erase", index_exprp->unlinkFrBack()};
                newp->makeStatement();
            }
        } else if (nodep->name() == "sort" || nodep->name() == "rsort"
                   || nodep->name() == "reverse" || nodep->name() == "shuffle") {
            nodep->v3error("Array method " << nodep->prettyNameQ()
                                           << " not legal on associative arrays");
        } else if (nodep->name() == "and" || nodep->name() == "or" || nodep->name() == "xor"
                   || nodep->name() == "sum" || nodep->name() == "product") {
            // All value return
            AstWith* const withp
                = methodWithArgument(nodep, false, false, adtypep->subDTypep(),
                                     adtypep->findStringDType(), adtypep->subDTypep());
            methodOkArguments(nodep, 0, 0);
            methodCallLValueRecurse(nodep, nodep->fromp(), VAccess::READ);
            newp = new AstCMethodHard{nodep->fileline(), nodep->fromp()->unlinkFrBack(),
                                      "r_" + nodep->name(), withp};
            newp->dtypeFrom(withp ? withp->dtypep() : adtypep->subDTypep());
            if (!nodep->firstAbovep()) newp->makeStatement();
        } else if (nodep->name() == "min" || nodep->name() == "max" || nodep->name() == "unique") {
            methodOkArguments(nodep, 0, 0);
            methodCallLValueRecurse(nodep, nodep->fromp(), VAccess::READ);
            newp = new AstCMethodHard{nodep->fileline(), nodep->fromp()->unlinkFrBack(),
                                      nodep->name()};
            newp->dtypeFrom(adtypep);
            if (!nodep->firstAbovep()) newp->makeStatement();
        } else if (nodep->name() == "find" || nodep->name() == "find_first"
                   || nodep->name() == "find_last") {
            AstWith* const withp
                = methodWithArgument(nodep, true, false, nodep->findBitDType(),
                                     adtypep->findStringDType(), adtypep->subDTypep());
            methodOkArguments(nodep, 0, 0);
            methodCallLValueRecurse(nodep, nodep->fromp(), VAccess::READ);
            newp = new AstCMethodHard{nodep->fileline(), nodep->fromp()->unlinkFrBack(),
                                      nodep->name(), withp};
            newp->dtypeFrom(adtypep);
            if (!nodep->firstAbovep()) newp->makeStatement();
        } else {
            nodep->v3error("Unknown wildcard associative array method " << nodep->prettyNameQ());
            nodep->dtypeFrom(adtypep->subDTypep());  // Best guess
        }
        if (newp) {
            newp->protect(false);
            newp->didWidth(true);
            nodep->replaceWith(newp);
            VL_DO_DANGLING(nodep->deleteTree(), nodep);
        }
    }
    void methodCallAssoc(AstMethodCall* nodep, AstAssocArrayDType* adtypep) {
        AstCMethodHard* newp = nullptr;
        if (nodep->name() == "num"  // function int num()
            || nodep->name() == "size") {
            methodOkArguments(nodep, 0, 0);
            newp = new AstCMethodHard(nodep->fileline(), nodep->fromp()->unlinkFrBack(),
                                      "size");  // So don't need num()
            newp->dtypeSetSigned32();
        } else if (nodep->name() == "first"  // function int first(ref index)
                   || nodep->name() == "last"  //
                   || nodep->name() == "next"  //
                   || nodep->name() == "prev") {
            methodOkArguments(nodep, 1, 1);
            AstNode* const index_exprp = methodCallAssocIndexExpr(nodep, adtypep);
            newp = new AstCMethodHard(nodep->fileline(), nodep->fromp()->unlinkFrBack(),
                                      nodep->name(),  // first/last/next/prev
                                      index_exprp->unlinkFrBack());
            newp->dtypeSetSigned32();
            if (!nodep->firstAbovep()) newp->makeStatement();
        } else if (nodep->name() == "exists") {  // function int exists(input index)
            // IEEE really should have made this a "bit" return
            methodOkArguments(nodep, 1, 1);
            AstNode* const index_exprp = methodCallAssocIndexExpr(nodep, adtypep);
            newp = new AstCMethodHard(nodep->fileline(), nodep->fromp()->unlinkFrBack(), "exists",
                                      index_exprp->unlinkFrBack());
            newp->dtypeSetSigned32();
            newp->pure(true);
        } else if (nodep->name() == "delete") {  // function void delete([input integer index])
            methodOkArguments(nodep, 0, 1);
            methodCallLValueRecurse(nodep, nodep->fromp(), VAccess::WRITE);
            if (!nodep->pinsp()) {
                newp = new AstCMethodHard(nodep->fileline(), nodep->fromp()->unlinkFrBack(),
                                          "clear");
                newp->makeStatement();
            } else {
                AstNode* const index_exprp = methodCallAssocIndexExpr(nodep, adtypep);
                newp = new AstCMethodHard(nodep->fileline(), nodep->fromp()->unlinkFrBack(),
                                          "erase", index_exprp->unlinkFrBack());
                newp->makeStatement();
            }
        } else if (nodep->name() == "sort" || nodep->name() == "rsort"
                   || nodep->name() == "reverse" || nodep->name() == "shuffle") {
            nodep->v3error("Array method " << nodep->prettyNameQ()
                                           << " not legal on associative arrays");
        } else if (nodep->name() == "and" || nodep->name() == "or" || nodep->name() == "xor"
                   || nodep->name() == "sum" || nodep->name() == "product") {
            // All value return
            AstWith* const withp = methodWithArgument(nodep, false, false, adtypep->subDTypep(),
                                                      adtypep->keyDTypep(), adtypep->subDTypep());
            methodOkArguments(nodep, 0, 0);
            methodCallLValueRecurse(nodep, nodep->fromp(), VAccess::READ);
            newp = new AstCMethodHard(nodep->fileline(), nodep->fromp()->unlinkFrBack(),
                                      "r_" + nodep->name(), withp);
            newp->dtypeFrom(withp ? withp->dtypep() : adtypep->subDTypep());
            if (!nodep->firstAbovep()) newp->makeStatement();
        } else if (nodep->name() == "min" || nodep->name() == "max" || nodep->name() == "unique"
                   || nodep->name() == "unique_index") {
            methodOkArguments(nodep, 0, 0);
            methodCallLValueRecurse(nodep, nodep->fromp(), VAccess::READ);
            newp = new AstCMethodHard(nodep->fileline(), nodep->fromp()->unlinkFrBack(),
                                      nodep->name());
            if (nodep->name() == "unique_index") {
                newp->dtypep(queueDTypeIndexedBy(adtypep->keyDTypep()));
            } else {
                newp->dtypeFrom(adtypep);
            }
            if (!nodep->firstAbovep()) newp->makeStatement();
        } else if (nodep->name() == "find" || nodep->name() == "find_first"
                   || nodep->name() == "find_last") {
            AstWith* const withp = methodWithArgument(nodep, true, false, nodep->findBitDType(),
                                                      adtypep->keyDTypep(), adtypep->subDTypep());
            methodOkArguments(nodep, 0, 0);
            methodCallLValueRecurse(nodep, nodep->fromp(), VAccess::READ);
            newp = new AstCMethodHard(nodep->fileline(), nodep->fromp()->unlinkFrBack(),
                                      nodep->name(), withp);
            newp->dtypeFrom(adtypep);
            if (!nodep->firstAbovep()) newp->makeStatement();
        } else if (nodep->name() == "find_index" || nodep->name() == "find_first_index"
                   || nodep->name() == "find_last_index") {
            AstWith* const withp = methodWithArgument(nodep, true, false, nodep->findBitDType(),
                                                      adtypep->keyDTypep(), adtypep->subDTypep());
            methodOkArguments(nodep, 0, 0);
            methodCallLValueRecurse(nodep, nodep->fromp(), VAccess::READ);
            newp = new AstCMethodHard(nodep->fileline(), nodep->fromp()->unlinkFrBack(),
                                      nodep->name(), withp);
            newp->dtypep(queueDTypeIndexedBy(adtypep->keyDTypep()));
            if (!nodep->firstAbovep()) newp->makeStatement();
        } else {
            nodep->v3error("Unknown built-in associative array method " << nodep->prettyNameQ());
            nodep->dtypeFrom(adtypep->subDTypep());  // Best guess
        }
        if (newp) {
            newp->protect(false);
            newp->didWidth(true);
            nodep->replaceWith(newp);
            VL_DO_DANGLING(nodep->deleteTree(), nodep);
        }
    }
    AstNode* methodCallAssocIndexExpr(AstMethodCall* nodep, AstAssocArrayDType* adtypep) {
        AstNode* const index_exprp = VN_CAST(nodep->pinsp(), Arg)->exprp();
        iterateCheck(nodep, "index", index_exprp, CONTEXT, FINAL, adtypep->keyDTypep(),
                     EXTEND_EXP);
        VL_DANGLING(index_exprp);  // May have been edited
        return VN_AS(nodep->pinsp(), Arg)->exprp();
    }
    AstNode* methodCallWildcardIndexExpr(AstMethodCall* nodep, AstWildcardArrayDType* adtypep) {
        AstNode* const index_exprp = VN_CAST(nodep->pinsp(), Arg)->exprp();
        iterateCheck(nodep, "index", index_exprp, CONTEXT, FINAL, adtypep->findStringDType(),
                     EXTEND_EXP);
        VL_DANGLING(index_exprp);  // May have been edited
        return VN_AS(nodep->pinsp(), Arg)->exprp();
    }
    void methodCallLValueRecurse(AstMethodCall* nodep, AstNode* childp, const VAccess& access) {
        if (AstNodeVarRef* const varrefp = VN_CAST(childp, NodeVarRef)) {
            varrefp->access(access);
        } else if (const AstMemberSel* const ichildp = VN_CAST(childp, MemberSel)) {
            methodCallLValueRecurse(nodep, ichildp->fromp(), access);
        } else if (const AstNodeSel* const ichildp = VN_CAST(childp, NodeSel)) {
            methodCallLValueRecurse(nodep, ichildp->fromp(), access);
        } else {
            UINFO(1, "    Related node: " << childp << endl);
            nodep->v3warn(E_UNSUPPORTED, "Unsupported: Non-variable on LHS of built-in method '"
                                             << nodep->prettyName() << "'");
        }
    }
    void methodCallDyn(AstMethodCall* nodep, AstDynArrayDType* adtypep) {
        AstCMethodHard* newp = nullptr;
        if (nodep->name() == "at") {  // Created internally for []
            methodOkArguments(nodep, 1, 1);
            methodCallLValueRecurse(nodep, nodep->fromp(), VAccess::WRITE);
            newp = new AstCMethodHard(nodep->fileline(), nodep->fromp()->unlinkFrBack(), "at");
            newp->dtypeFrom(adtypep->subDTypep());
        } else if (nodep->name() == "size") {
            methodOkArguments(nodep, 0, 0);
            newp = new AstCMethodHard(nodep->fileline(), nodep->fromp()->unlinkFrBack(), "size");
            newp->dtypeSetSigned32();
        } else if (nodep->name() == "delete") {  // function void delete()
            methodOkArguments(nodep, 0, 0);
            methodCallLValueRecurse(nodep, nodep->fromp(), VAccess::WRITE);
            newp = new AstCMethodHard(nodep->fileline(), nodep->fromp()->unlinkFrBack(), "clear");
            newp->makeStatement();
        } else if (nodep->name() == "and" || nodep->name() == "or" || nodep->name() == "xor"
                   || nodep->name() == "sum" || nodep->name() == "product") {
            // All value return
            AstWith* const withp
                = methodWithArgument(nodep, false, false, adtypep->subDTypep(),
                                     nodep->findUInt32DType(), adtypep->subDTypep());
            methodOkArguments(nodep, 0, 0);
            methodCallLValueRecurse(nodep, nodep->fromp(), VAccess::READ);
            newp = new AstCMethodHard(nodep->fileline(), nodep->fromp()->unlinkFrBack(),
                                      "r_" + nodep->name(), withp);
            newp->dtypeFrom(adtypep->subDTypep());
            if (!nodep->firstAbovep()) newp->makeStatement();
        } else if (nodep->name() == "reverse" || nodep->name() == "shuffle"
                   || nodep->name() == "sort" || nodep->name() == "rsort") {
            AstWith* withp = nullptr;
            if (nodep->name() == "sort" || nodep->name() == "rsort") {
                withp = methodWithArgument(nodep, false, true, nullptr, nodep->findUInt32DType(),
                                           adtypep->subDTypep());
            }
            methodOkArguments(nodep, 0, 0);
            methodCallLValueRecurse(nodep, nodep->fromp(), VAccess::WRITE);
            newp = new AstCMethodHard(nodep->fileline(), nodep->fromp()->unlinkFrBack(),
                                      nodep->name(), withp);
            newp->makeStatement();
        } else if (nodep->name() == "min" || nodep->name() == "max" || nodep->name() == "unique"
                   || nodep->name() == "unique_index") {
            methodOkArguments(nodep, 0, 0);
            methodCallLValueRecurse(nodep, nodep->fromp(), VAccess::READ);
            newp = new AstCMethodHard(nodep->fileline(), nodep->fromp()->unlinkFrBack(),
                                      nodep->name());
            if (nodep->name() == "unique_index") {
                newp->dtypep(newp->findQueueIndexDType());
            } else {
                newp->dtypeFrom(adtypep);
            }
            if (!nodep->firstAbovep()) newp->makeStatement();
        } else if (nodep->name() == "find" || nodep->name() == "find_first"
                   || nodep->name() == "find_last" || nodep->name() == "find_index") {
            AstWith* const withp
                = methodWithArgument(nodep, true, false, nodep->findBitDType(),
                                     nodep->findUInt32DType(), adtypep->subDTypep());
            methodOkArguments(nodep, 0, 0);
            methodCallLValueRecurse(nodep, nodep->fromp(), VAccess::READ);
            newp = new AstCMethodHard(nodep->fileline(), nodep->fromp()->unlinkFrBack(),
                                      nodep->name(), withp);
            newp->dtypeFrom(adtypep);
            if (!nodep->firstAbovep()) newp->makeStatement();
        } else if (nodep->name() == "find_index" || nodep->name() == "find_first_index"
                   || nodep->name() == "find_last_index") {
            AstWith* const withp
                = methodWithArgument(nodep, true, false, nodep->findBitDType(),
                                     nodep->findUInt32DType(), adtypep->subDTypep());
            methodOkArguments(nodep, 0, 0);
            methodCallLValueRecurse(nodep, nodep->fromp(), VAccess::READ);
            newp = new AstCMethodHard(nodep->fileline(), nodep->fromp()->unlinkFrBack(),
                                      nodep->name(), withp);
            newp->dtypep(newp->findQueueIndexDType());
            if (!nodep->firstAbovep()) newp->makeStatement();
        } else {
            nodep->v3warn(E_UNSUPPORTED, "Unsupported/unknown built-in dynamic array method "
                                             << nodep->prettyNameQ());
            nodep->dtypeFrom(adtypep->subDTypep());  // Best guess
        }
        if (newp) {
            newp->protect(false);
            newp->didWidth(true);
            nodep->replaceWith(newp);
            VL_DO_DANGLING(nodep->deleteTree(), nodep);
        }
    }
    void methodCallQueue(AstMethodCall* nodep, AstQueueDType* adtypep) {
        AstCMethodHard* newp = nullptr;
        if (nodep->name() == "at") {  // Created internally for []
            methodOkArguments(nodep, 1, 1);
            methodCallLValueRecurse(nodep, nodep->fromp(), VAccess::WRITE);
            newp = new AstCMethodHard(nodep->fileline(), nodep->fromp()->unlinkFrBack(), "at");
            newp->dtypeFrom(adtypep->subDTypep());
        } else if (nodep->name() == "num"  // function int num()
                   || nodep->name() == "size") {
            methodOkArguments(nodep, 0, 0);
            newp = new AstCMethodHard(nodep->fileline(), nodep->fromp()->unlinkFrBack(), "size");
            newp->dtypeSetSigned32();
        } else if (nodep->name() == "delete") {  // function void delete([input integer index])
            methodOkArguments(nodep, 0, 1);
            methodCallLValueRecurse(nodep, nodep->fromp(), VAccess::WRITE);
            if (!nodep->pinsp()) {
                newp = new AstCMethodHard(nodep->fileline(), nodep->fromp()->unlinkFrBack(),
                                          "clear");
                newp->makeStatement();
            } else {
                AstNode* const index_exprp = methodCallQueueIndexExpr(nodep);
                if (index_exprp->isZero()) {  // delete(0) is a pop_front
                    newp = new AstCMethodHard(nodep->fileline(), nodep->fromp()->unlinkFrBack(),
                                              "pop_front");
                    newp->dtypeFrom(adtypep->subDTypep());
                    newp->makeStatement();
                } else {
                    newp = new AstCMethodHard(nodep->fileline(), nodep->fromp()->unlinkFrBack(),
                                              "erase", index_exprp->unlinkFrBack());
                    newp->makeStatement();
                }
            }
        } else if (nodep->name() == "insert") {
            methodOkArguments(nodep, 2, 2);
            methodCallLValueRecurse(nodep, nodep->fromp(), VAccess::WRITE);
            AstNode* const index_exprp = methodCallQueueIndexExpr(nodep);
            AstArg* const argp = VN_AS(nodep->pinsp()->nextp(), Arg);
            iterateCheckTyped(nodep, "insert value", argp->exprp(), adtypep->subDTypep(), BOTH);
            if (index_exprp->isZero()) {  // insert(0, ...) is a push_front
                newp = new AstCMethodHard(nodep->fileline(), nodep->fromp()->unlinkFrBack(),
                                          "push_front", argp->exprp()->unlinkFrBack());
                newp->makeStatement();
            } else {
                newp = new AstCMethodHard(nodep->fileline(), nodep->fromp()->unlinkFrBack(),
                                          nodep->name(), index_exprp->unlinkFrBack());
                newp->addPinsp(argp->exprp()->unlinkFrBack());
                newp->makeStatement();
            }
        } else if (nodep->name() == "pop_front" || nodep->name() == "pop_back") {
            methodOkArguments(nodep, 0, 0);
            // Returns element, so method both consumes (reads) and modifies the queue
            methodCallLValueRecurse(nodep, nodep->fromp(), VAccess::READWRITE);
            newp = new AstCMethodHard(nodep->fileline(), nodep->fromp()->unlinkFrBack(),
                                      nodep->name());
            newp->dtypeFrom(adtypep->subDTypep());
            // Because queue methods pop_front() or pop_back() can be void cast,
            // they use makeStatement to check if they need the c++ ";" added.
            if (nodep->isStandaloneBodyStmt()) newp->makeStatement();
        } else if (nodep->name() == "push_back" || nodep->name() == "push_front") {
            methodOkArguments(nodep, 1, 1);
            methodCallLValueRecurse(nodep, nodep->fromp(), VAccess::WRITE);
            AstArg* const argp = VN_AS(nodep->pinsp(), Arg);
            iterateCheckTyped(nodep, "push value", argp->exprp(), adtypep->subDTypep(), BOTH);
            newp = new AstCMethodHard(nodep->fileline(), nodep->fromp()->unlinkFrBack(),
                                      nodep->name(), argp->exprp()->unlinkFrBack());
            newp->makeStatement();
        } else if (nodep->name() == "and" || nodep->name() == "or" || nodep->name() == "xor"
                   || nodep->name() == "sum" || nodep->name() == "product") {
            AstWith* const withp
                = methodWithArgument(nodep, false, false, adtypep->subDTypep(),
                                     nodep->findUInt32DType(), adtypep->subDTypep());
            methodOkArguments(nodep, 0, 0);
            methodCallLValueRecurse(nodep, nodep->fromp(), VAccess::READ);
            newp = new AstCMethodHard(nodep->fileline(), nodep->fromp()->unlinkFrBack(),
                                      "r_" + nodep->name(), withp);
            newp->dtypeFrom(withp ? withp->dtypep() : adtypep->subDTypep());
            if (!nodep->firstAbovep()) newp->makeStatement();
        } else if (nodep->name() == "reverse" || nodep->name() == "shuffle"
                   || nodep->name() == "sort" || nodep->name() == "rsort") {
            AstWith* withp = nullptr;
            if (nodep->name() == "sort" || nodep->name() == "rsort") {
                withp = methodWithArgument(nodep, false, true, nullptr, nodep->findUInt32DType(),
                                           adtypep->subDTypep());
            }
            methodOkArguments(nodep, 0, 0);
            methodCallLValueRecurse(nodep, nodep->fromp(), VAccess::WRITE);
            newp = new AstCMethodHard(nodep->fileline(), nodep->fromp()->unlinkFrBack(),
                                      nodep->name(), withp);
            newp->makeStatement();
        } else if (nodep->name() == "min" || nodep->name() == "max" || nodep->name() == "unique"
                   || nodep->name() == "unique_index") {
            methodOkArguments(nodep, 0, 0);
            methodCallLValueRecurse(nodep, nodep->fromp(), VAccess::READ);
            newp = new AstCMethodHard(nodep->fileline(), nodep->fromp()->unlinkFrBack(),
                                      nodep->name());
            if (nodep->name() == "unique_index") {
                newp->dtypep(newp->findQueueIndexDType());
            } else {
                newp->dtypeFrom(adtypep);
            }
            if (!nodep->firstAbovep()) newp->makeStatement();
        } else if (nodep->name() == "find" || nodep->name() == "find_first"
                   || nodep->name() == "find_last") {
            AstWith* const withp
                = methodWithArgument(nodep, true, false, nodep->findBitDType(),
                                     nodep->findUInt32DType(), adtypep->subDTypep());
            methodOkArguments(nodep, 0, 0);
            methodCallLValueRecurse(nodep, nodep->fromp(), VAccess::READ);
            newp = new AstCMethodHard(nodep->fileline(), nodep->fromp()->unlinkFrBack(),
                                      nodep->name(), withp);
            newp->dtypeFrom(adtypep);
            if (!nodep->firstAbovep()) newp->makeStatement();
        } else if (nodep->name() == "find_index" || nodep->name() == "find_first_index"
                   || nodep->name() == "find_last_index") {
            AstWith* const withp
                = methodWithArgument(nodep, true, false, nodep->findBitDType(),
                                     nodep->findUInt32DType(), adtypep->subDTypep());
            methodOkArguments(nodep, 0, 0);
            methodCallLValueRecurse(nodep, nodep->fromp(), VAccess::READ);
            newp = new AstCMethodHard(nodep->fileline(), nodep->fromp()->unlinkFrBack(),
                                      nodep->name(), withp);
            newp->dtypep(newp->findQueueIndexDType());
            if (!nodep->firstAbovep()) newp->makeStatement();
        } else {
            nodep->v3warn(E_UNSUPPORTED,
                          "Unsupported/unknown built-in queue method " << nodep->prettyNameQ());
            nodep->dtypeFrom(adtypep->subDTypep());  // Best guess
        }
        if (newp) {
            newp->protect(false);
            newp->didWidth(true);
            nodep->replaceWith(newp);
            VL_DO_DANGLING(nodep->deleteTree(), nodep);
        }
    }
    AstNode* methodCallQueueIndexExpr(AstMethodCall* nodep) {
        AstNode* const index_exprp = VN_AS(nodep->pinsp(), Arg)->exprp();
        iterateCheckSigned32(nodep, "index", index_exprp, BOTH);
        VL_DANGLING(index_exprp);  // May have been edited
        return VN_AS(nodep->pinsp(), Arg)->exprp();
    }
    void methodCallClass(AstMethodCall* nodep, AstClassRefDType* adtypep) {
        // No need to width-resolve the class, as it was done when we did the child
        AstClass* const first_classp = adtypep->classp();
        if (nodep->name() == "randomize") {
            v3Global.useRandomizeMethods(true);
            V3Randomize::newRandomizeFunc(first_classp);
        }
        UASSERT_OBJ(first_classp, nodep, "Unlinked");
        for (AstClass* classp = first_classp; classp;) {
            if (AstNodeFTask* const ftaskp
                = VN_CAST(classp->findMember(nodep->name()), NodeFTask)) {
                userIterate(ftaskp, nullptr);
                if (ftaskp->lifetime().isStatic()) {
                    AstNode* argsp = nullptr;
                    if (nodep->pinsp()) argsp = nodep->pinsp()->unlinkFrBackWithNext();
                    AstNodeFTaskRef* newp = nullptr;
                    if (VN_IS(ftaskp, Task)) {
                        newp = new AstTaskRef(nodep->fileline(), ftaskp->name(), argsp);
                    } else {
                        newp = new AstFuncRef(nodep->fileline(), ftaskp->name(), argsp);
                    }
                    newp->taskp(ftaskp);
                    newp->classOrPackagep(classp);
                    nodep->replaceWith(newp);
                    VL_DO_DANGLING(nodep->deleteTree(), nodep);
                } else {
                    nodep->taskp(ftaskp);
                    nodep->dtypeFrom(ftaskp);
                    nodep->classOrPackagep(classp);
                    if (VN_IS(ftaskp, Task)) nodep->makeStatement();
                    processFTaskRefArgs(nodep);
                }
                return;
            }
            classp = classp->extendsp() ? classp->extendsp()->classp() : nullptr;
        }
        {
            VSpellCheck speller;
            for (AstClass* classp = first_classp; classp;) {
                for (AstNode* itemp = classp->membersp(); itemp; itemp = itemp->nextp()) {
                    if (VN_IS(itemp, NodeFTask)) speller.pushCandidate(itemp->prettyName());
                }
                classp = classp->extendsp() ? classp->extendsp()->classp() : nullptr;
            }
            const string suggest = speller.bestCandidateMsg(nodep->prettyName());
            nodep->v3error("Class method "
                           << nodep->prettyNameQ() << " not found in class "
                           << first_classp->prettyNameQ() << "\n"
                           << (suggest.empty() ? "" : nodep->fileline()->warnMore() + suggest));
        }
        nodep->dtypeSetSigned32();  // Guess on error
    }
    void methodCallUnpack(AstMethodCall* nodep, AstUnpackArrayDType* adtypep) {
        enum : uint8_t {
            UNKNOWN = 0,
            ARRAY_OR,
            ARRAY_AND,
            ARRAY_XOR,
            ARRAY_SUM,
            ARRAY_PRODUCT
        } methodId;

        methodId = UNKNOWN;
        if (nodep->name() == "or") {
            methodId = ARRAY_OR;
        } else if (nodep->name() == "and") {
            methodId = ARRAY_AND;
        } else if (nodep->name() == "xor") {
            methodId = ARRAY_XOR;
        } else if (nodep->name() == "sum") {
            methodId = ARRAY_SUM;
        } else if (nodep->name() == "product") {
            methodId = ARRAY_PRODUCT;
        }

        if (methodId) {
            methodOkArguments(nodep, 0, 0);
            FileLine* const fl = nodep->fileline();
            AstNode* newp = nullptr;
            for (int i = 0; i < adtypep->elementsConst(); ++i) {
                AstNode* const arrayRef = nodep->fromp()->cloneTree(false);
                AstNode* const selector = new AstArraySel(fl, arrayRef, i);
                if (!newp) {
                    newp = selector;
                } else {
                    switch (methodId) {
                    case ARRAY_OR: newp = new AstOr(fl, newp, selector); break;
                    case ARRAY_AND: newp = new AstAnd(fl, newp, selector); break;
                    case ARRAY_XOR: newp = new AstXor(fl, newp, selector); break;
                    case ARRAY_SUM: newp = new AstAdd(fl, newp, selector); break;
                    case ARRAY_PRODUCT: newp = new AstMul(fl, newp, selector); break;
                    default: nodep->v3fatalSrc("bad case");
                    }
                }
            }
            nodep->replaceWith(newp);
            VL_DO_DANGLING(nodep->deleteTree(), nodep);
        } else {
            nodep->v3error("Unknown built-in array method " << nodep->prettyNameQ());
            nodep->dtypeFrom(adtypep->subDTypep());  // Best guess
        }
    }
    void methodCallEvent(AstMethodCall* nodep, AstBasicDType*) {
        // Method call on event
        if (nodep->name() == "triggered") {
            // We represent events as numbers, so can just return number
            methodOkArguments(nodep, 0, 0);
            AstNode* const newp = nodep->fromp()->unlinkFrBack();
            nodep->replaceWith(newp);
            VL_DO_DANGLING(pushDeletep(nodep), nodep);
        } else {
            nodep->v3error("Unknown built-in event method " << nodep->prettyNameQ());
        }
    }
    void methodCallString(AstMethodCall* nodep, AstBasicDType*) {
        // Method call on string
        if (nodep->name() == "len") {
            // Constant value
            methodOkArguments(nodep, 0, 0);
            AstNode* const newp = new AstLenN(nodep->fileline(), nodep->fromp()->unlinkFrBack());
            nodep->replaceWith(newp);
            VL_DO_DANGLING(pushDeletep(nodep), nodep);
        } else if (nodep->name() == "itoa") {
            methodOkArguments(nodep, 1, 1);
            VL_DO_DANGLING(replaceWithSFormat(nodep, "%0d"), nodep);
        } else if (nodep->name() == "hextoa") {
            methodOkArguments(nodep, 1, 1);
            VL_DO_DANGLING(replaceWithSFormat(nodep, "%0x"), nodep);
        } else if (nodep->name() == "octtoa") {
            methodOkArguments(nodep, 1, 1);
            VL_DO_DANGLING(replaceWithSFormat(nodep, "%0o"), nodep);
        } else if (nodep->name() == "bintoa") {
            methodOkArguments(nodep, 1, 1);
            VL_DO_DANGLING(replaceWithSFormat(nodep, "%0b"), nodep);
        } else if (nodep->name() == "realtoa") {
            methodOkArguments(nodep, 1, 1);
            VL_DO_DANGLING(replaceWithSFormat(nodep, "%g"), nodep);
        } else if (nodep->name() == "tolower") {
            methodOkArguments(nodep, 0, 0);
            AstNode* const newp
                = new AstToLowerN(nodep->fileline(), nodep->fromp()->unlinkFrBack());
            nodep->replaceWith(newp);
            VL_DO_DANGLING(nodep->deleteTree(), nodep);
        } else if (nodep->name() == "toupper") {
            methodOkArguments(nodep, 0, 0);
            AstNode* const newp
                = new AstToUpperN(nodep->fileline(), nodep->fromp()->unlinkFrBack());
            nodep->replaceWith(newp);
            VL_DO_DANGLING(nodep->deleteTree(), nodep);
        } else if (nodep->name() == "compare" || nodep->name() == "icompare") {
            const bool ignoreCase = nodep->name()[0] == 'i';
            methodOkArguments(nodep, 1, 1);
            AstArg* const argp = VN_AS(nodep->pinsp(), Arg);
            AstNode* const lhs = nodep->fromp()->unlinkFrBack();
            AstNode* const rhs = argp->exprp()->unlinkFrBack();
            AstNode* const newp = new AstCompareNN(nodep->fileline(), lhs, rhs, ignoreCase);
            nodep->replaceWith(newp);
            VL_DO_DANGLING(nodep->deleteTree(), nodep);
        } else if (nodep->name() == "putc") {
            methodOkArguments(nodep, 2, 2);
            AstArg* const arg0p = VN_AS(nodep->pinsp(), Arg);
            AstArg* const arg1p = VN_AS(arg0p->nextp(), Arg);
            AstNodeVarRef* const fromp = VN_AS(nodep->fromp()->unlinkFrBack(), VarRef);
            AstNode* const rhsp = arg0p->exprp()->unlinkFrBack();
            AstNode* const thsp = arg1p->exprp()->unlinkFrBack();
            AstVarRef* const varrefp
                = new AstVarRef(nodep->fileline(), fromp->varp(), VAccess::READ);
            AstNode* const newp = new AstAssign(
                nodep->fileline(), fromp, new AstPutcN(nodep->fileline(), varrefp, rhsp, thsp));
            fromp->access(VAccess::WRITE);
            nodep->replaceWith(newp);
            VL_DO_DANGLING(nodep->deleteTree(), nodep);
        } else if (nodep->name() == "getc") {
            methodOkArguments(nodep, 1, 1);
            AstArg* const arg0p = VN_AS(nodep->pinsp(), Arg);
            AstNode* const lhsp = nodep->fromp()->unlinkFrBack();
            AstNode* const rhsp = arg0p->exprp()->unlinkFrBack();
            AstNode* const newp = new AstGetcN(nodep->fileline(), lhsp, rhsp);
            nodep->replaceWith(newp);
            VL_DO_DANGLING(nodep->deleteTree(), nodep);
        } else if (nodep->name() == "substr") {
            methodOkArguments(nodep, 2, 2);
            AstArg* const arg0p = VN_AS(nodep->pinsp(), Arg);
            AstArg* const arg1p = VN_AS(arg0p->nextp(), Arg);
            AstNode* const lhsp = nodep->fromp()->unlinkFrBack();
            AstNode* const rhsp = arg0p->exprp()->unlinkFrBack();
            AstNode* const thsp = arg1p->exprp()->unlinkFrBack();
            AstNode* const newp = new AstSubstrN(nodep->fileline(), lhsp, rhsp, thsp);
            nodep->replaceWith(newp);
            VL_DO_DANGLING(nodep->deleteTree(), nodep);
        } else if (nodep->name() == "atobin" || nodep->name() == "atohex"
                   || nodep->name() == "atoi" || nodep->name() == "atooct"
                   || nodep->name() == "atoreal") {
            AstAtoN::FmtType fmt;
            if (nodep->name() == "atobin") {
                fmt = AstAtoN::ATOBIN;
            } else if (nodep->name() == "atohex") {
                fmt = AstAtoN::ATOHEX;
            } else if (nodep->name() == "atoi") {
                fmt = AstAtoN::ATOI;
            } else if (nodep->name() == "atooct") {
                fmt = AstAtoN::ATOOCT;
            } else if (nodep->name() == "atoreal") {
                fmt = AstAtoN::ATOREAL;
            } else {
                V3ERROR_NA;
                fmt = AstAtoN::ATOI;
            }  // dummy assignment to suppress compiler warning
            methodOkArguments(nodep, 0, 0);
            AstNode* const newp
                = new AstAtoN(nodep->fileline(), nodep->fromp()->unlinkFrBack(), fmt);
            nodep->replaceWith(newp);
            VL_DO_DANGLING(nodep->deleteTree(), nodep);
        } else {
            nodep->v3error("Unknown built-in string method " << nodep->prettyNameQ());
        }
    }
    AstQueueDType* queueDTypeIndexedBy(AstNodeDType* indexDTypep) {
        // Return a Queue data type with the specified index, remembering so can use again if
        // needed
        if (AstQueueDType* const queuep = m_queueDTypeIndexed[indexDTypep]) {
            return queuep;
        } else {
            auto* const newp = new AstQueueDType(indexDTypep->fileline(), indexDTypep, nullptr);
            v3Global.rootp()->typeTablep()->addTypesp(newp);
            m_queueDTypeIndexed[indexDTypep] = newp;
            return newp;
        }
    }

    virtual void visit(AstNew* nodep) override {
        if (nodep->didWidth()) return;
        AstClassRefDType* const refp
            = m_vup ? VN_CAST(m_vup->dtypeNullSkipRefp(), ClassRefDType) : nullptr;
        if (!refp) {  // e.g. int a = new;
            nodep->v3error("new() not expected in this context");
            return;
        }
        nodep->dtypep(refp);

        AstClass* const classp = refp->classp();
        UASSERT_OBJ(classp, nodep, "Unlinked");
        if (AstNodeFTask* const ftaskp = VN_CAST(classp->findMember("new"), Func)) {
            nodep->taskp(ftaskp);
            nodep->classOrPackagep(classp);
        } else {
            // Either made explicitly or V3LinkDot made implicitly
            classp->v3fatalSrc("Can't find class's new");
        }
        if (classp->isVirtual()) {
            nodep->v3error(
                "Illegal to call 'new' using an abstract virtual class (IEEE 1800-2017 8.21)");
        }
        userIterate(nodep->taskp(), nullptr);
        processFTaskRefArgs(nodep);
    }
    virtual void visit(AstNewCopy* nodep) override {
        if (nodep->didWidthAndSet()) return;
        AstClassRefDType* const refp = VN_CAST(m_vup->dtypeNullSkipRefp(), ClassRefDType);
        if (!refp) {  // e.g. int a = new;
            nodep->v3error("new() not expected in this context");
            return;
        }
        nodep->dtypep(refp);
        userIterateChildren(nodep, WidthVP(SELF, BOTH).p());
        if (!similarDTypeRecurse(nodep->dtypep(), nodep->rhsp()->dtypep())) {
            nodep->rhsp()->v3error("New-as-copier passed different data type '"
                                   << nodep->dtypep()->prettyTypeName() << "' then expected '"
                                   << nodep->rhsp()->dtypep()->prettyTypeName() << "'");
        }
    }
    virtual void visit(AstNewDynamic* nodep) override {
        if (nodep->didWidthAndSet()) return;
        AstDynArrayDType* const adtypep = VN_CAST(m_vup->dtypeNullSkipRefp(), DynArrayDType);
        if (!adtypep) {  // e.g. int a = new;
            nodep->v3error(
                "dynamic new() not expected in this context (data type must be dynamic array)");
            return;
        }
        // The AstNodeAssign visitor will be soon be replacing this node, make sure it gets it
        if (!VN_IS(nodep->backp(), NodeAssign)) {
            if (adtypep) UINFO(1, "Got backp " << nodep->backp() << endl);
            nodep->v3error(
                "dynamic new() not expected in this context (expected under an assign)");
            return;
        }
        nodep->dtypep(adtypep);
        if (m_vup && m_vup->prelim()) {
            iterateCheckSigned32(nodep, "new() size", nodep->sizep(), BOTH);
        }
        if (nodep->rhsp()) {
            iterateCheckTyped(nodep, "Dynamic array new RHS", nodep->rhsp(), adtypep, BOTH);
        }
    }

    virtual void visit(AstPattern* nodep) override {
        if (nodep->didWidthAndSet()) return;
        UINFO(9, "PATTERN " << nodep << endl);
        if (nodep->childDTypep()) {  // data_type '{ pattern }
            nodep->dtypep(iterateEditMoveDTypep(nodep, nodep->subDTypep()));
        }
        if (!nodep->dtypep() && m_vup->dtypeNullp()) {  // Get it from parent assignment/pin/etc
            nodep->dtypep(m_vup->dtypep());
        }
        AstNodeDType* dtypep = nodep->dtypep();
        if (!dtypep) {
            nodep->v3warn(E_UNSUPPORTED, "Unsupported/Illegal: Assignment pattern"
                                         " member not underneath a supported construct: "
                                             << nodep->backp()->prettyTypeName());
            return;
        }
        {
            dtypep = dtypep->skipRefp();
            nodep->dtypep(dtypep);
            UINFO(9, "  dtypep " << dtypep << endl);
            nodep->dtypep(dtypep);
            // Determine replication count, and replicate initial value as
            // widths need to be individually determined
            for (AstPatMember* patp = VN_AS(nodep->itemsp(), PatMember); patp;
                 patp = VN_AS(patp->nextp(), PatMember)) {
                const int times = visitPatMemberRep(patp);
                for (int i = 1; i < times; i++) {
                    AstNode* const newp = patp->cloneTree(false);
                    patp->addNextHere(newp);
                    // This loop will see the new elements as part of nextp()
                }
            }
            // Convert any PatMember with multiple items to multiple PatMembers
            for (AstPatMember* patp = VN_AS(nodep->itemsp(), PatMember); patp;
                 patp = VN_AS(patp->nextp(), PatMember)) {
                if (patp->lhssp()->nextp()) {
                    // Can't just addNext, as would add to end of all members.
                    // So detach, add next and reattach
                    VNRelinker relinkHandle;
                    patp->unlinkFrBack(&relinkHandle);
                    while (AstNode* const movep = patp->lhssp()->nextp()) {
                        movep->unlinkFrBack();  // Not unlinkFrBackWithNext, just one
                        AstNode* newkeyp = nullptr;
                        if (patp->keyp()) newkeyp = patp->keyp()->cloneTree(true);
                        AstPatMember* const newp
                            = new AstPatMember(patp->fileline(), movep, newkeyp, nullptr);
                        patp->addNext(newp);
                    }
                    relinkHandle.relink(patp);
                }
            }
            AstPatMember* defaultp = nullptr;
            for (AstPatMember* patp = VN_AS(nodep->itemsp(), PatMember); patp;
                 patp = VN_AS(patp->nextp(), PatMember)) {
                if (patp->isDefault()) {
                    if (defaultp) nodep->v3error("Multiple '{ default: } clauses");
                    defaultp = patp;
                    patp->unlinkFrBack();
                }
            }
            while (const AstConstDType* const vdtypep = VN_CAST(dtypep, ConstDType)) {
                dtypep = vdtypep->subDTypep()->skipRefp();
            }

            userIterate(dtypep, WidthVP(SELF, BOTH).p());

            if (auto* const vdtypep = VN_CAST(dtypep, NodeUOrStructDType)) {
                VL_DO_DANGLING(patternUOrStruct(nodep, vdtypep, defaultp), nodep);
            } else if (auto* const vdtypep = VN_CAST(dtypep, NodeArrayDType)) {
                VL_DO_DANGLING(patternArray(nodep, vdtypep, defaultp), nodep);
            } else if (auto* const vdtypep = VN_CAST(dtypep, AssocArrayDType)) {
                VL_DO_DANGLING(patternAssoc(nodep, vdtypep, defaultp), nodep);
            } else if (auto* const vdtypep = VN_CAST(dtypep, WildcardArrayDType)) {
                VL_DO_DANGLING(patternWildcard(nodep, vdtypep, defaultp), nodep);
            } else if (auto* const vdtypep = VN_CAST(dtypep, DynArrayDType)) {
                VL_DO_DANGLING(patternDynArray(nodep, vdtypep, defaultp), nodep);
            } else if (auto* const vdtypep = VN_CAST(dtypep, QueueDType)) {
                VL_DO_DANGLING(patternQueue(nodep, vdtypep, defaultp), nodep);
            } else if (VN_IS(dtypep, BasicDType) && VN_AS(dtypep, BasicDType)->isRanged()) {
                VL_DO_DANGLING(patternBasic(nodep, dtypep, defaultp), nodep);
            } else {
                nodep->v3warn(
                    E_UNSUPPORTED,
                    "Unsupported: Assignment pattern applies against non struct/union data type: "
                        << dtypep->prettyDTypeNameQ());
            }
        }
    }
    void patternUOrStruct(AstPattern* nodep, AstNodeUOrStructDType* vdtypep,
                          AstPatMember* defaultp) {
        // Due to "default" and tagged patterns, we need to determine
        // which member each AstPatMember corresponds to before we can
        // determine the dtypep for that PatMember's value, and then
        // width the initial value appropriately.
        using PatMap = std::map<const AstMemberDType*, AstPatMember*>;
        PatMap patmap;  // Store member: value
        DTypeMap dtypemap;  // Store data_type: default_value
        {
            const AstMemberDType* memp = vdtypep->membersp();
            AstPatMember* patp = VN_CAST(nodep->itemsp(), PatMember);
            while (patp) {
                do {
                    if (patp->keyp()) {
                        // '{member:value} or '{data_type: default_value}
                        if (const AstText* textp = VN_CAST(patp->keyp(), Text)) {
                            // member: value
                            memp = vdtypep->findMember(textp->text());
                            if (!memp) {
                                patp->keyp()->v3error("Assignment pattern key '"
                                                      << textp->text() << "' not found as member");
                                break;
                            } else {
                                const std::pair<PatMap::iterator, bool> ret
                                    = patmap.emplace(memp, patp);
                                if (!ret.second) {
                                    patp->v3error("Assignment pattern contains duplicate entry: "
                                                  << VN_AS(patp->keyp(), Text)->text());
                                }
                                memp = VN_AS(memp->nextp(), MemberDType);
                            }
                        } else if (const AstNodeDType* nodedtypep
                                   = VN_CAST(patp->keyp(), NodeDType)) {
                            // data_type: default_value
                            const string dtype = nodedtypep->dtypep()->prettyDTypeName();
                            auto it = dtypemap.find(dtype);
                            if (it == dtypemap.end()) {
                                dtypemap.emplace(dtype, patp);
                            } else {
                                // Override stored default_value
                                it->second = patp->cloneTree(false);
                            }
                        } else {
                            // Undefined pattern
                            patp->keyp()->v3error(
                                "Assignment pattern key not supported/understood: "
                                << patp->keyp()->prettyTypeName());
                        }
                    } else {
                        // constant expr
                        if (memp) {
                            const std::pair<PatMap::iterator, bool> ret
                                = patmap.emplace(memp, patp);
                            if (!ret.second) {
                                patp->v3error("Assignment pattern contains duplicate entry: "
                                              << VN_AS(patp->keyp(), Text)->text());
                            }
                            memp = VN_AS(memp->nextp(), MemberDType);
                        }
                    }
                } while (false);

                // Next
                if (patp) patp = VN_AS(patp->nextp(), PatMember);
            }
        }
        AstNode* newp = nullptr;
        for (AstMemberDType* memp = vdtypep->membersp(); memp;
             memp = VN_AS(memp->nextp(), MemberDType)) {
            const auto it = patmap.find(memp);
            AstPatMember* patp = nullptr;
            if (it == patmap.end()) {
                // default or deafult_type assignment
                if (AstNodeUOrStructDType* const memp_nested_vdtypep
                    = VN_CAST(memp->virtRefDTypep(), NodeUOrStructDType)) {
                    newp = nestedvalueConcat_patternUOrStruct(memp_nested_vdtypep, defaultp, newp,
                                                              nodep, dtypemap);
                } else {
                    patp = Defaultpatp_patternUOrStruct(nodep, memp, patp, vdtypep, defaultp,
                                                        dtypemap);
                    newp = valueConcat_patternUOrStruct(patp, newp, memp, nodep);
                }
            } else {
                // member assignment
                patp = it->second;
                newp = valueConcat_patternUOrStruct(patp, newp, memp, nodep);
            }
        }
        if (newp) {
            nodep->replaceWith(newp);
        } else {
            nodep->v3error("Assignment pattern with no members");
        }
        VL_DO_DANGLING(pushDeletep(nodep), nodep);  // Deletes defaultp also, if present
    }

    AstNode* nestedvalueConcat_patternUOrStruct(AstNodeUOrStructDType* memp_vdtypep,
                                                AstPatMember* defaultp, AstNode* newp,
                                                AstPattern* nodep, DTypeMap dtypemap) {
        AstPatMember* patp = nullptr;
        for (AstMemberDType* memp_nested = memp_vdtypep->membersp(); memp_nested;
             memp_nested = VN_AS(memp_nested->nextp(), MemberDType)) {
            if (AstNodeUOrStructDType* const memp_multinested_vdtypep
                = VN_CAST(memp_nested->virtRefDTypep(), NodeUOrStructDType)) {
                // When unpacked struct/union is supported this if will need some additional
                // conditions
                newp = nestedvalueConcat_patternUOrStruct(memp_multinested_vdtypep, defaultp, newp,
                                                          nodep, dtypemap);
            } else {
                patp = Defaultpatp_patternUOrStruct(nodep, memp_nested, patp, memp_vdtypep,
                                                    defaultp, dtypemap);
                newp = valueConcat_patternUOrStruct(patp, newp, memp_nested, nodep);
            }
        }
        return newp;
    }

    AstPatMember* Defaultpatp_patternUOrStruct(AstPattern* nodep, AstMemberDType* memp,
                                               AstPatMember* patp,
                                               AstNodeUOrStructDType* memp_vdtypep,
                                               AstPatMember* defaultp, DTypeMap dtypemap) {
        const string memp_DType = memp->virtRefDTypep()->prettyDTypeName();
        const auto it = dtypemap.find(memp_DType);
        if (it != dtypemap.end()) {
            // default_value for data_type
            patp = it->second->cloneTree(false);
        } else if (defaultp) {
            // default_value for any unmatched member yet
            patp = defaultp->cloneTree(false);
        } else {
            if (!VN_IS(memp_vdtypep, UnionDType)) {
                nodep->v3error("Assignment pattern missed initializing elements: "
                               << memp->virtRefDTypep()->prettyDTypeNameQ() << " "
                               << memp->prettyNameQ());
            }
        }
        return patp;
    }

    AstNode* valueConcat_patternUOrStruct(AstPatMember* patp, AstNode* newp, AstMemberDType* memp,
                                          AstPattern* nodep) {
        if (patp) {
            patp->dtypep(memp);
            AstNode* const valuep = patternMemberValueIterate(patp);
            if (!newp) {
                newp = valuep;
            } else {
                AstConcat* const concatp = new AstConcat{patp->fileline(), newp, valuep};
                newp = concatp;
                newp->dtypeSetLogicSized(concatp->lhsp()->width() + concatp->rhsp()->width(),
                                         nodep->dtypep()->numeric());
            }
        }
        return newp;
    }

    void patternArray(AstPattern* nodep, AstNodeArrayDType* arrayDtp, AstPatMember* defaultp) {
        const VNumRange range = arrayDtp->declRange();
        PatVecMap patmap = patVectorMap(nodep, range);
        UINFO(9, "ent " << range.left() << " to " << range.right() << endl);
        AstNode* newp = nullptr;
        for (int entn = 0, ent = range.left(); entn < range.elements();
             ++entn, ent += range.leftToRightInc()) {
            AstPatMember* newpatp = nullptr;
            AstPatMember* patp = nullptr;
            const auto it = patmap.find(ent);
            if (it == patmap.end()) {
                if (defaultp) {
                    newpatp = defaultp->cloneTree(false);
                    patp = newpatp;
                } else {
                    nodep->v3error("Assignment pattern missed initializing elements: " << ent);
                }
            } else {
                patp = it->second;
                patmap.erase(it);
            }

            if (patp) {
                // Don't want the RHS an array
                patp->dtypep(arrayDtp->subDTypep());
                AstNode* const valuep = patternMemberValueIterate(patp);
                if (VN_IS(arrayDtp, UnpackArrayDType)) {
                    if (!newp) {
                        AstInitArray* const newap
                            = new AstInitArray(nodep->fileline(), arrayDtp, nullptr);
                        newp = newap;
                    }
                    VN_AS(newp, InitArray)->addIndexValuep(ent - range.lo(), valuep);
                } else {  // Packed. Convert to concat for now.
                    if (!newp) {
                        newp = valuep;
                    } else {
                        AstConcat* const concatp = new AstConcat(patp->fileline(), newp, valuep);
                        newp = concatp;
                        newp->dtypeSetLogicSized(concatp->lhsp()->width()
                                                     + concatp->rhsp()->width(),
                                                 nodep->dtypep()->numeric());
                    }
                }
            }
            if (newpatp) VL_DO_DANGLING(pushDeletep(newpatp), newpatp);
        }
        if (!patmap.empty()) nodep->v3error("Assignment pattern with too many elements");
        if (newp) {
            nodep->replaceWith(newp);
        } else {
            nodep->v3error("Assignment pattern with no members");
        }
        // if (debug() >= 9) newp->dumpTree("-apat-out: ");
        VL_DO_DANGLING(pushDeletep(nodep), nodep);  // Deletes defaultp also, if present
    }
    void patternAssoc(AstPattern* nodep, AstAssocArrayDType* arrayDtp, AstPatMember* defaultp) {
        AstNode* defaultValuep = nullptr;
        if (defaultp) defaultValuep = defaultp->lhssp()->unlinkFrBack();
        AstNode* newp = new AstConsAssoc(nodep->fileline(), defaultValuep);
        newp->dtypeFrom(arrayDtp);
        for (AstPatMember* patp = VN_AS(nodep->itemsp(), PatMember); patp;
             patp = VN_AS(patp->nextp(), PatMember)) {
            patp->dtypep(arrayDtp->subDTypep());
            AstNode* const valuep = patternMemberValueIterate(patp);
            AstNode* const keyp = patp->keyp();
            auto* const newap
                = new AstSetAssoc(nodep->fileline(), newp, keyp->unlinkFrBack(), valuep);
            newap->dtypeFrom(arrayDtp);
            newp = newap;
        }
        nodep->replaceWith(newp);
        // if (debug() >= 9) newp->dumpTree("-apat-out: ");
        VL_DO_DANGLING(pushDeletep(nodep), nodep);  // Deletes defaultp also, if present
    }
    void patternWildcard(AstPattern* nodep, AstWildcardArrayDType* arrayDtp,
                         AstPatMember* defaultp) {
        AstNode* defaultValuep = nullptr;
        if (defaultp) defaultValuep = defaultp->lhssp()->unlinkFrBack();
        AstNode* newp = new AstConsWildcard{nodep->fileline(), defaultValuep};
        newp->dtypeFrom(arrayDtp);
        for (AstPatMember* patp = VN_AS(nodep->itemsp(), PatMember); patp;
             patp = VN_AS(patp->nextp(), PatMember)) {
            patp->dtypep(arrayDtp->subDTypep());
            AstNode* const valuep = patternMemberValueIterate(patp);
            AstNode* const keyp = patp->keyp();
            auto* const newap
                = new AstSetWildcard{nodep->fileline(), newp, keyp->unlinkFrBack(), valuep};
            newap->dtypeFrom(arrayDtp);
            newp = newap;
        }
        nodep->replaceWith(newp);
        // if (debug() >= 9) newp->dumpTree("-apat-out: ");
        VL_DO_DANGLING(pushDeletep(nodep), nodep);  // Deletes defaultp also, if present
    }
    void patternDynArray(AstPattern* nodep, AstDynArrayDType* arrayp, AstPatMember*) {
        AstNode* newp = new AstConsDynArray(nodep->fileline());
        newp->dtypeFrom(arrayp);
        for (AstPatMember* patp = VN_AS(nodep->itemsp(), PatMember); patp;
             patp = VN_AS(patp->nextp(), PatMember)) {
            patp->dtypep(arrayp->subDTypep());
            AstNode* const valuep = patternMemberValueIterate(patp);
            auto* const newap = new AstConsDynArray(nodep->fileline(), valuep, newp);
            newap->dtypeFrom(arrayp);
            newp = newap;
        }
        nodep->replaceWith(newp);
        // if (debug() >= 9) newp->dumpTree("-apat-out: ");
        VL_DO_DANGLING(pushDeletep(nodep), nodep);  // Deletes defaultp also, if present
    }
    void patternQueue(AstPattern* nodep, AstQueueDType* arrayp, AstPatMember*) {
        AstNode* newp = new AstConsQueue(nodep->fileline());
        newp->dtypeFrom(arrayp);
        for (AstPatMember* patp = VN_AS(nodep->itemsp(), PatMember); patp;
             patp = VN_AS(patp->nextp(), PatMember)) {
            patp->dtypep(arrayp->subDTypep());
            AstNode* const valuep = patternMemberValueIterate(patp);
            auto* const newap = new AstConsQueue(nodep->fileline(), valuep, newp);
            newap->dtypeFrom(arrayp);
            newp = newap;
        }
        nodep->replaceWith(newp);
        // if (debug() >= 9) newp->dumpTree("-apat-out: ");
        VL_DO_DANGLING(pushDeletep(nodep), nodep);  // Deletes defaultp also, if present
    }
    void patternBasic(AstPattern* nodep, AstNodeDType* vdtypep, AstPatMember* defaultp) {
        const AstBasicDType* bdtypep = VN_AS(vdtypep, BasicDType);
        const VNumRange range = bdtypep->declRange();
        PatVecMap patmap = patVectorMap(nodep, range);
        UINFO(9, "ent " << range.hi() << " to " << range.lo() << endl);
        AstNode* newp = nullptr;
        for (int ent = range.hi(); ent >= range.lo(); --ent) {
            AstPatMember* newpatp = nullptr;
            AstPatMember* patp = nullptr;
            const auto it = patmap.find(ent);
            if (it == patmap.end()) {
                if (defaultp) {
                    newpatp = defaultp->cloneTree(false);
                    patp = newpatp;
                } else {
                    nodep->v3error("Assignment pattern missed initializing elements: " << ent);
                }
            } else {
                patp = it->second;
                patmap.erase(it);
            }
            if (patp) {
                // Determine initial values
                vdtypep = nodep->findBitDType();
                patp->dtypep(vdtypep);
                AstNode* const valuep = patternMemberValueIterate(patp);
                {  // Packed. Convert to concat for now.
                    if (!newp) {
                        newp = valuep;
                    } else {
                        AstConcat* const concatp = new AstConcat(patp->fileline(), newp, valuep);
                        newp = concatp;
                        newp->dtypeSetLogicSized(concatp->lhsp()->width()
                                                     + concatp->rhsp()->width(),
                                                 nodep->dtypep()->numeric());
                    }
                }
            }
            if (newpatp) VL_DO_DANGLING(pushDeletep(newpatp), newpatp);
        }
        if (!patmap.empty()) nodep->v3error("Assignment pattern with too many elements");
        if (newp) {
            nodep->replaceWith(newp);
        } else {
            nodep->v3error("Assignment pattern with no members");
        }
        // if (debug() >= 9) newp->dumpTree("-apat-out: ");
        VL_DO_DANGLING(pushDeletep(nodep), nodep);  // Deletes defaultp also, if present
    }
    AstNode* patternMemberValueIterate(AstPatMember* patp) {
        // Determine values - might be another InitArray
        userIterate(patp, WidthVP(patp->dtypep(), BOTH).p());
        // Convert to InitArray or constify immediately
        AstNode* valuep = patp->lhssp()->unlinkFrBack();
        if (VN_IS(valuep, Const)) {
            // Forming a AstConcat will cause problems with
            // unsized (uncommitted sized) constants
            if (AstNode* const newp
                = WidthCommitVisitor::newIfConstCommitSize(VN_AS(valuep, Const))) {
                VL_DO_DANGLING(pushDeletep(valuep), valuep);
                valuep = newp;
            }
        }
        return valuep;
    }

    virtual void visit(AstPatMember* nodep) override {
        AstNodeDType* const vdtypep = m_vup->dtypeNullp();
        UASSERT_OBJ(vdtypep, nodep, "Pattern member type not assigned by AstPattern visitor");
        nodep->dtypep(vdtypep);
        UINFO(9, "   PATMEMBER " << nodep << endl);
        UASSERT_OBJ(!nodep->lhssp()->nextp(), nodep,
                    "PatMember value should be singular w/replicates removed");
        // Need to propagate assignment type downwards, even on prelim
        userIterateChildren(nodep, WidthVP(nodep->dtypep(), PRELIM).p());
        iterateCheck(nodep, "Pattern value", nodep->lhssp(), ASSIGN, FINAL, vdtypep, EXTEND_LHS);
    }
    int visitPatMemberRep(AstPatMember* nodep) {
        uint32_t times = 1;
        if (nodep->repp()) {  // else repp()==nullptr shorthand for rep count 1
            iterateCheckSizedSelf(nodep, "LHS", nodep->repp(), SELF, BOTH);
            V3Const::constifyParamsEdit(nodep->repp());  // repp may change
            const AstConst* const constp = VN_CAST(nodep->repp(), Const);
            if (!constp) {
                nodep->v3error("Replication value isn't a constant.");
                times = 0;
            } else {
                times = constp->toUInt();
            }
            if (times == 0) {
                nodep->v3error("Pattern replication value of 0 is not legal.");
                times = 1;
            }
            nodep->repp()
                ->unlinkFrBackWithNext()
                ->deleteTree();  // Done with replicate before cloning
        }
        return times;
    }

    virtual void visit(AstPropClocked* nodep) override {
        if (m_vup->prelim()) {  // First stage evaluation
            iterateCheckBool(nodep, "Property", nodep->propp(), BOTH);
            userIterateAndNext(nodep->sensesp(), nullptr);
            if (nodep->disablep()) {
                iterateCheckBool(nodep, "Disable", nodep->disablep(),
                                 BOTH);  // it's like an if() condition.
            }
            nodep->dtypeSetBit();
        }
    }

    //--------------------
    // Top levels

    virtual void visit(AstNodeCase* nodep) override {
        // IEEE-2012 12.5:
        //    Width: MAX(expr, all items)
        //    Signed: Only if expr, and all items signed
        assertAtStatement(nodep);
        userIterateAndNext(nodep->exprp(), WidthVP(CONTEXT, PRELIM).p());
        for (AstCaseItem *nextip, *itemp = nodep->itemsp(); itemp; itemp = nextip) {
            nextip = VN_AS(itemp->nextp(), CaseItem);  // Prelim may cause the node to get replaced
            if (!VN_IS(nodep, GenCase)) userIterateAndNext(itemp->bodysp(), nullptr);
            for (AstNode *nextcp, *condp = itemp->condsp(); condp; condp = nextcp) {
                nextcp = condp->nextp();  // Prelim may cause the node to get replaced
                VL_DO_DANGLING(userIterate(condp, WidthVP(CONTEXT, PRELIM).p()), condp);
            }
        }

        // Take width as maximum across all items, if any is real whole thing is real
        AstNodeDType* subDTypep = nodep->exprp()->dtypep();
        for (AstCaseItem* itemp = nodep->itemsp(); itemp;
             itemp = VN_AS(itemp->nextp(), CaseItem)) {
            for (AstNode* condp = itemp->condsp(); condp; condp = condp->nextp()) {
                if (condp->dtypep() != subDTypep) {
                    if (condp->dtypep()->isDouble() || subDTypep->isDouble()) {
                        subDTypep = nodep->findDoubleDType();
                    } else if (condp->dtypep()->isString() || subDTypep->isString()) {
                        subDTypep = nodep->findStringDType();
                    } else {
                        const int width = std::max(subDTypep->width(), condp->width());
                        const int mwidth = std::max(subDTypep->widthMin(), condp->widthMin());
                        const bool issigned = subDTypep->isSigned() && condp->isSigned();
                        subDTypep
                            = nodep->findLogicDType(width, mwidth, VSigning::fromBool(issigned));
                    }
                }
            }
        }
        // Apply width
        iterateCheck(nodep, "Case expression", nodep->exprp(), CONTEXT, FINAL, subDTypep,
                     EXTEND_LHS);
        for (AstCaseItem* itemp = nodep->itemsp(); itemp;
             itemp = VN_AS(itemp->nextp(), CaseItem)) {
            for (AstNode *nextcp, *condp = itemp->condsp(); condp; condp = nextcp) {
                nextcp = condp->nextp();  // Final may cause the node to get replaced
                iterateCheck(nodep, "Case Item", condp, CONTEXT, FINAL, subDTypep, EXTEND_LHS);
            }
        }
    }
    virtual void visit(AstNodeFor* nodep) override {
        assertAtStatement(nodep);
        userIterateAndNext(nodep->initsp(), nullptr);
        iterateCheckBool(nodep, "For Test Condition", nodep->condp(),
                         BOTH);  // it's like an if() condition.
        if (!VN_IS(nodep, GenFor)) userIterateAndNext(nodep->bodysp(), nullptr);
        userIterateAndNext(nodep->incsp(), nullptr);
    }
    virtual void visit(AstRepeat* nodep) override {
        assertAtStatement(nodep);
        userIterateAndNext(nodep->countp(), WidthVP(SELF, BOTH).p());
        userIterateAndNext(nodep->bodysp(), nullptr);
    }
    virtual void visit(AstWhile* nodep) override {
        assertAtStatement(nodep);
        userIterateAndNext(nodep->precondsp(), nullptr);
        iterateCheckBool(nodep, "For Test Condition", nodep->condp(),
                         BOTH);  // it's like an if() condition.
        userIterateAndNext(nodep->bodysp(), nullptr);
        userIterateAndNext(nodep->incsp(), nullptr);
    }
    virtual void visit(AstNodeIf* nodep) override {
        assertAtStatement(nodep);
        // if (debug()) nodep->dumpTree(cout, "  IfPre: ");
        if (!VN_IS(nodep, GenIf)) {  // for m_paramsOnly
            userIterateAndNext(nodep->ifsp(), nullptr);
            userIterateAndNext(nodep->elsesp(), nullptr);
        }
        iterateCheckBool(nodep, "If", nodep->condp(), BOTH);  // it's like an if() condition.
        // if (debug()) nodep->dumpTree(cout, "  IfOut: ");
    }
    virtual void visit(AstExprStmt* nodep) override {
        userIterateAndNext(nodep->stmtsp(), nullptr);
        // expected result is same as parent's expected result
        userIterateAndNext(nodep->resultp(), m_vup);
        nodep->dtypeFrom(nodep->resultp());
    }
    virtual void visit(AstForeach* nodep) override {
        const AstSelLoopVars* const loopsp = VN_CAST(nodep->arrayp(), SelLoopVars);
        UASSERT_OBJ(loopsp, nodep, "No loop variables under foreach");
        // if (debug()) nodep->dumpTree(cout, "-foreach-old: ");
        userIterateAndNext(loopsp->fromp(), WidthVP(SELF, BOTH).p());
        AstNode* const fromp = loopsp->fromp();
        UASSERT_OBJ(fromp->dtypep(), fromp, "Missing data type");
        AstNodeDType* fromDtp = fromp->dtypep()->skipRefp();
        // Split into for loop
        AstNode* bodyp = nodep->bodysp();  // Might be null
        if (bodyp) bodyp->unlinkFrBackWithNext();
        // We record where the body needs to eventually go with bodyPointp
        // (Can't use bodyp as might be null)
        AstNode* lastBodyPointp = nullptr;
        AstNode* newp = nullptr;
        // Major dimension first
        while (AstNode* argsp
               = loopsp->elementsp()) {  // Loop advances due to below varp->unlinkFrBack()
            const bool empty = VN_IS(argsp, Empty);
            AstVar* const varp = VN_CAST(argsp, Var);
            UASSERT_OBJ(varp || empty, argsp, "Missing foreach loop variable");
            if (varp) varp->usedLoopIdx(true);
            argsp->unlinkFrBack();
            if (!fromDtp) {
                argsp->v3error("foreach loop variables exceed number of indices of array");
                VL_DO_DANGLING(nodep->unlinkFrBack()->deleteTree(), nodep);
                return;
            }
            fromDtp = fromDtp->skipRefp();
            UINFO(9, "- foreachArg " << argsp << endl);
            UINFO(9, "-   from on  " << fromp << endl);
            UINFO(9, "-   from dtp " << fromDtp << endl);

            FileLine* const fl = argsp->fileline();
            AstNode* bodyPointp = new AstBegin{fl, "[EditWrapper]", nullptr};
            AstNode* loopp = nullptr;
            if (const AstNodeArrayDType* const adtypep = VN_CAST(fromDtp, NodeArrayDType)) {
                if (varp) {
                    loopp = createForeachLoopRanged(nodep, bodyPointp, varp, adtypep->declRange());
                }
                // Prep for next
                fromDtp = fromDtp->subDTypep();
            } else if (AstBasicDType* const adtypep = VN_CAST(fromDtp, BasicDType)) {
                if (!adtypep->isRanged()) {
                    argsp->v3error("Illegal to foreach loop on basic '" + fromDtp->prettyTypeName()
                                   + "'");
                    VL_DO_DANGLING(nodep->unlinkFrBack()->deleteTree(), nodep);
                    VL_DO_DANGLING(bodyPointp->deleteTree(), bodyPointp);
                    return;
                }
                if (varp) {
                    loopp = createForeachLoopRanged(nodep, bodyPointp, varp, adtypep->declRange());
                }
                // Prep for next
                fromDtp = nullptr;
            } else if (VN_IS(fromDtp, DynArrayDType) || VN_IS(fromDtp, QueueDType)) {
                if (varp) {
                    auto* const leftp = new AstConst{fl, AstConst::Signed32{}, 0};
                    auto* const sizep = new AstCMethodHard{fl, fromp->cloneTree(false), "size"};
                    sizep->dtypeSetSigned32();
                    sizep->didWidth(true);
                    sizep->protect(false);
                    AstNode* const condp
                        = new AstLt{fl, new AstVarRef{fl, varp, VAccess::READ}, sizep};
                    AstNode* const incp = new AstAdd{fl, new AstConst{fl, AstConst::Signed32{}, 1},
                                                     new AstVarRef{fl, varp, VAccess::READ}};
                    loopp = createForeachLoop(nodep, bodyPointp, varp, leftp, condp, incp);
                }
                // Prep for next
                fromDtp = fromDtp->subDTypep();
            } else if (const AstAssocArrayDType* const adtypep
                       = VN_CAST(fromDtp, AssocArrayDType)) {
                // Make this: var KEY_TYPE index;
                //            bit index__Vfirst;
                //            index__Vfirst = 0;
                //            if (0 != array.first(index))
                //                 do body while (index__Vfirst || 0 != array.next(index))
                varp->dtypeFrom(adtypep->keyDTypep());
                AstVar* const first_varp = new AstVar{
                    fl, VVarType::BLOCKTEMP, varp->name() + "__Vfirst", VFlagBitPacked{}, 1};
                first_varp->usedLoopIdx(true);
                AstNode* const firstp = new AstMethodCall{
                    fl, fromp->cloneTree(false), "first",
                    new AstArg{fl, "", new AstVarRef{fl, varp, VAccess::READWRITE}}};
                AstNode* const nextp = new AstMethodCall{
                    fl, fromp->cloneTree(false), "next",
                    new AstArg{fl, "", new AstVarRef{fl, varp, VAccess::READWRITE}}};
                AstNode* const first_clearp
                    = new AstAssign{fl, new AstVarRef{fl, first_varp, VAccess::WRITE},
                                    new AstConst{fl, AstConst::BitFalse{}}};
                auto* const orp = new AstLogOr{fl, new AstVarRef{fl, first_varp, VAccess::READ},
                                               new AstNeq{fl, new AstConst{fl, 0}, nextp}};
                orp->sideEffect(true);
                AstNode* const whilep = new AstWhile{fl, orp, first_clearp};
                first_clearp->addNext(bodyPointp);
                AstNode* const ifbodyp
                    = new AstAssign{fl, new AstVarRef{fl, first_varp, VAccess::WRITE},
                                    new AstConst{fl, AstConst::BitTrue{}}};
                ifbodyp->addNext(whilep);
                AstNode* const stmtsp = varp;  // New statements for under new Begin
                stmtsp->addNext(first_varp);
                stmtsp->addNext(
                    new AstIf{fl, new AstNeq{fl, new AstConst{fl, 0}, firstp}, ifbodyp});
                loopp = new AstBegin{nodep->fileline(), "", stmtsp, false, true};
                // Prep for next
                fromDtp = fromDtp->subDTypep();
            } else {
                argsp->v3error("Illegal to foreach loop on '" + fromDtp->prettyTypeName() + "'");
                VL_DO_DANGLING(nodep->unlinkFrBack()->deleteTree(), nodep);
                return;
            }
            // New loop goes UNDER previous loop
            if (varp) {
                if (!newp) {
                    newp = loopp;
                } else {
                    lastBodyPointp->replaceWith(loopp);
                }
                lastBodyPointp = bodyPointp;
            }
        }
        // The parser validates we don't have "foreach (array[,,,])"
        UASSERT_OBJ(newp, nodep, "foreach has no non-empty loop variable");
        if (bodyp) {
            lastBodyPointp->replaceWith(bodyp);
        } else {
            lastBodyPointp->unlinkFrBack();
        }
        // if (debug()) newp->dumpTreeAndNext(cout, "-foreach-new: ");
        nodep->replaceWith(newp);
        VL_DO_DANGLING(lastBodyPointp->deleteTree(), lastBodyPointp);
        VL_DO_DANGLING(nodep->deleteTree(), nodep);
    }
    AstNode* createForeachLoopRanged(AstForeach* nodep, AstNode* bodysp, AstVar* varp,
                                     const VNumRange& declRange) {
        FileLine* const fl = varp->fileline();
        auto* const leftp = new AstConst{fl, AstConst::Signed32{}, declRange.left()};
        auto* const rightp = new AstConst{fl, AstConst::Signed32{}, declRange.right()};
        AstNode* condp;
        AstNode* incp;
        if (declRange.left() < declRange.right()) {
            condp = new AstLte{fl, new AstVarRef{fl, varp, VAccess::READ}, rightp};
            incp = new AstAdd{fl, new AstConst{fl, AstConst::Signed32{}, 1},
                              new AstVarRef{fl, varp, VAccess::READ}};
        } else {
            condp = new AstGte{fl, new AstVarRef{fl, varp, VAccess::READ}, rightp};
            incp = new AstSub{fl, new AstVarRef{fl, varp, VAccess::READ},
                              new AstConst{fl, AstConst::Signed32{}, 1}};
        }
        return createForeachLoop(nodep, bodysp, varp, leftp, condp, incp);
    }
    AstNode* createForeachLoop(AstForeach* nodep, AstNode* bodysp, AstVar* varp, AstNode* leftp,
                               AstNode* condp, AstNode* incp) {
        FileLine* const fl = varp->fileline();
        auto* const whilep = new AstWhile{
            fl, condp, bodysp, new AstAssign{fl, new AstVarRef{fl, varp, VAccess::WRITE}, incp}};
        AstNode* const stmtsp = varp;  // New statements for under new Begin
        stmtsp->addNext(new AstAssign{fl, new AstVarRef{fl, varp, VAccess::WRITE}, leftp});
        stmtsp->addNext(whilep);
        AstNode* const newp = new AstBegin{nodep->fileline(), "", stmtsp, false, true};
        return newp;
    }

    virtual void visit(AstNodeAssign* nodep) override {
        // IEEE-2012 10.7, 11.8.2, 11.8.3, 11.5:  (Careful of 11.8.1 which is
        //                  only one step; final dtype depends on assign LHS.)
        //    Determine RHS type width and signing
        //    Propagate type down to *non-self-determined* operators
        //       Real propagates only across one operator if one side is real -
        //       handled in each visitor.
        //    Then LHS sign-extends only if *RHS* is signed
        assertAtStatement(nodep);
        // if (debug()) nodep->dumpTree(cout, "  AssignPre: ");
        {
            // if (debug()) nodep->dumpTree(cout, "-    assin:  ");
            userIterateAndNext(nodep->lhsp(), WidthVP(SELF, BOTH).p());
            UASSERT_OBJ(nodep->lhsp()->dtypep(), nodep, "How can LHS be untyped?");
            UASSERT_OBJ(nodep->lhsp()->dtypep()->widthSized(), nodep, "How can LHS be unsized?");
            nodep->dtypeFrom(nodep->lhsp());
            //
            // AstPattern needs to know the proposed data type of the lhs, so pass on the prelim
            userIterateAndNext(nodep->rhsp(), WidthVP(nodep->dtypep(), PRELIM).p());
            //
            // if (debug()) nodep->dumpTree(cout, "-    assign: ");
            AstNodeDType* const lhsDTypep
                = nodep->lhsp()->dtypep();  // Note we use rhsp for context determined
            iterateCheckAssign(nodep, "Assign RHS", nodep->rhsp(), FINAL, lhsDTypep);
            // if (debug()) nodep->dumpTree(cout, "  AssignOut: ");
        }
        if (const AstBasicDType* const basicp = nodep->rhsp()->dtypep()->basicp()) {
            if (basicp->isEventValue()) {
                // see t_event_copy.v for commentary on the mess involved
                nodep->v3warn(E_UNSUPPORTED, "Unsupported: assignment of event data type");
            }
        }
        if (nodep->timingControlp()) {
            nodep->timingControlp()->v3warn(
                ASSIGNDLY, "Unsupported: Ignoring timing control on this assignment.");
            nodep->timingControlp()->unlinkFrBackWithNext()->deleteTree();
        }
        if (VN_IS(nodep->rhsp(), EmptyQueue)) {
            UINFO(9, "= {} -> .delete(): " << nodep);
            if (!VN_IS(nodep->lhsp()->dtypep()->skipRefp(), QueueDType)) {
                nodep->v3warn(E_UNSUPPORTED,
                              "Unsupported/Illegal: empty queue ('{}') in this assign context");
                VL_DO_DANGLING(pushDeletep(nodep->unlinkFrBack()), nodep);
                return;
            }
            AstMethodCall* const newp = new AstMethodCall{
                nodep->fileline(), nodep->lhsp()->unlinkFrBack(), "delete", nullptr};
            newp->makeStatement();
            nodep->replaceWith(newp);
            VL_DO_DANGLING(pushDeletep(nodep), nodep);
            // Need to now convert it
            visit(newp);
            return;
        }
        if (const AstNewDynamic* const dynp = VN_CAST(nodep->rhsp(), NewDynamic)) {
            UINFO(9, "= new[] -> .resize(): " << nodep);
            AstCMethodHard* newp;
            if (!dynp->rhsp()) {
                newp = new AstCMethodHard(nodep->fileline(), nodep->lhsp()->unlinkFrBack(),
                                          "renew", dynp->sizep()->unlinkFrBack());
            } else {
                newp = new AstCMethodHard(nodep->fileline(), nodep->lhsp()->unlinkFrBack(),
                                          "renew_copy", dynp->sizep()->unlinkFrBack());
                newp->addPinsp(dynp->rhsp()->unlinkFrBack());
            }
            newp->didWidth(true);
            newp->protect(false);
            newp->makeStatement();
            nodep->replaceWith(newp);
            VL_DO_DANGLING(pushDeletep(nodep), nodep);
            // return;
        }
    }

    virtual void visit(AstRelease* nodep) override {
        userIterateAndNext(nodep->lhsp(), WidthVP(SELF, BOTH).p());
        UASSERT_OBJ(nodep->lhsp()->dtypep(), nodep, "How can LValue be untyped?");
        UASSERT_OBJ(nodep->lhsp()->dtypep()->widthSized(), nodep, "How can LValue be unsized?");
    }

    virtual void visit(AstSFormatF* nodep) override {
        // Excludes NodeDisplay, see below
        if (m_vup && !m_vup->prelim()) return;  // Can be called as statement or function
        // Just let all arguments seek their natural sizes
        userIterateChildren(nodep, WidthVP(SELF, BOTH).p());
        //
        UINFO(9, "  Display in " << nodep->text() << endl);
        string newFormat;
        bool inPct = false;
        AstNode* argp = nodep->exprsp();
        const string txt = nodep->text();
        string fmt;
        for (char ch : txt) {
            if (!inPct && ch == '%') {
                inPct = true;
                fmt = ch;
            } else if (inPct && (isdigit(ch) || ch == '.' || ch == '-')) {
                fmt += ch;
            } else if (tolower(inPct)) {
                inPct = false;
                bool added = false;
                switch (tolower(ch)) {
                case '%': break;  // %% - just output a %
                case 'm': break;  // %m - auto insert "name"
                case 'l': break;  // %m - auto insert "library"
                case 'd': {  // Convert decimal to either 'd' or '#'
                    if (argp) {
                        AstNode* const nextp = argp->nextp();
                        if (argp->isDouble()) {
                            spliceCvtS(argp, true, 64);
                            ch = '~';
                        } else if (argp->isSigned()) {  // Convert it
                            ch = '~';
                        }
                        argp = nextp;
                    }
                    break;
                }
                case 'p': {  // Pattern
                    const AstNodeDType* const dtypep = argp ? argp->dtypep()->skipRefp() : nullptr;
                    const AstBasicDType* const basicp = dtypep ? dtypep->basicp() : nullptr;
                    if (basicp && basicp->isString()) {
                        added = true;
                        newFormat += "\"%@\"";
                    } else if (basicp && basicp->isDouble()) {
                        added = true;
                        newFormat += "%g";
                    } else if (VN_IS(dtypep, AssocArrayDType)  //
                               || VN_IS(dtypep, WildcardArrayDType)  //
                               || VN_IS(dtypep, ClassRefDType)  //
                               || VN_IS(dtypep, DynArrayDType)  //
                               || VN_IS(dtypep, QueueDType)) {
                        added = true;
                        newFormat += "%@";
                        VNRelinker handle;
                        argp->unlinkFrBack(&handle);
                        AstCMath* const newp
                            = new AstCMath(nodep->fileline(), "VL_TO_STRING(", 0, true);
                        newp->addBodysp(argp);
                        newp->addBodysp(new AstText(nodep->fileline(), ")", true));
                        newp->dtypeSetString();
                        newp->pure(true);
                        newp->protect(false);
                        handle.relink(newp);
                    } else {
                        added = true;
                        if (fmt == "%0") {
                            newFormat += "'h%0h";  // IEEE our choice
                        } else {
                            newFormat += "%d";
                        }
                    }
                    if (argp) argp = argp->nextp();
                    break;
                }
                case 's': {  // Convert string to pack string
                    if (argp && argp->dtypep()->basicp()->isString()) {  // Convert it
                        ch = '@';
                    }
                    if (argp) argp = argp->nextp();
                    break;
                }
                case 't': {  // Convert decimal time to realtime
                    if (argp) {
                        AstNode* const nextp = argp->nextp();
                        if (argp->isDouble()) ch = '^';  // Convert it
                        if (nodep->timeunit().isNone()) {
                            nodep->v3fatalSrc("display %t has no time units");
                        }
                        argp = nextp;
                    }
                    break;
                }
                case 'f':  // FALLTHRU
                case 'g': {
                    if (argp) {
                        AstNode* const nextp = argp->nextp();
                        if (!argp->isDouble()) {
                            iterateCheckReal(nodep, "Display argument", argp, BOTH);
                        }
                        argp = nextp;
                    }
                    break;
                }
                case '?': {  // Unspecified by user, guess
                    if (argp && argp->isDouble()) {
                        ch = 'g';
                    } else if (argp && argp->isString()) {
                        ch = '@';
                    } else if (nodep->missingArgChar() == 'd' && argp->isSigned()) {
                        ch = '~';
                    } else {
                        ch = nodep->missingArgChar();
                    }
                    if (argp) argp = argp->nextp();
                    break;
                }
                default: {  // Most operators, just move to next argument
                    if (argp) argp = argp->nextp();
                    break;
                }
                }  // switch
                if (!added) {
                    fmt += ch;
                    newFormat += fmt;
                }
            } else {
                newFormat += ch;
            }
        }
        nodep->text(newFormat);
        UINFO(9, "  Display out " << nodep->text() << endl);
    }
    virtual void visit(AstDisplay* nodep) override {
        assertAtStatement(nodep);
        if (nodep->filep()) iterateCheckFileDesc(nodep, nodep->filep(), BOTH);
        // Just let all arguments seek their natural sizes
        userIterateChildren(nodep, WidthVP(SELF, BOTH).p());
    }
    virtual void visit(AstElabDisplay* nodep) override {
        assertAtStatement(nodep);
        // Just let all arguments seek their natural sizes
        userIterateChildren(nodep, WidthVP(SELF, BOTH).p());
        if (!m_paramsOnly) {
            V3Const::constifyParamsEdit(nodep->fmtp());  // fmtp may change
            string text = nodep->fmtp()->text();
            if (text.empty()) text = "Elaboration system task message (IEEE 1800-2017 20.11)";
            switch (nodep->displayType()) {
            case VDisplayType::DT_INFO: nodep->v3warn(USERINFO, text); break;
            case VDisplayType::DT_ERROR: nodep->v3warn(USERERROR, text); break;
            case VDisplayType::DT_WARNING: nodep->v3warn(USERWARN, text); break;
            case VDisplayType::DT_FATAL: nodep->v3warn(USERFATAL, text); break;
            default: UASSERT_OBJ(false, nodep, "Unexpected elaboration display type");
            }
            VL_DO_DANGLING(nodep->unlinkFrBack()->deleteTree(), nodep);
        }
    }
    virtual void visit(AstDumpCtl* nodep) override {
        assertAtStatement(nodep);
        // Just let all arguments seek their natural sizes
        userIterateChildren(nodep, WidthVP(SELF, BOTH).p());
    }
    virtual void visit(AstFOpen* nodep) override {
        // Although a system function in IEEE, here a statement which sets the file pointer (MCD)
        assertAtStatement(nodep);
        iterateCheckFileDesc(nodep, nodep->filep(), BOTH);
        userIterateAndNext(nodep->filenamep(), WidthVP(SELF, BOTH).p());
        userIterateAndNext(nodep->modep(), WidthVP(SELF, BOTH).p());
    }
    virtual void visit(AstFOpenMcd* nodep) override {
        assertAtStatement(nodep);
        iterateCheckFileDesc(nodep, nodep->filep(), BOTH);
        userIterateAndNext(nodep->filenamep(), WidthVP(SELF, BOTH).p());
    }
    virtual void visit(AstFClose* nodep) override {
        assertAtStatement(nodep);
        iterateCheckFileDesc(nodep, nodep->filep(), BOTH);
    }
    virtual void visit(AstFError* nodep) override {
        if (m_vup->prelim()) {
            iterateCheckFileDesc(nodep, nodep->filep(), BOTH);
            // We only support string types, not packed array
            iterateCheckString(nodep, "$ferror string result", nodep->strp(), BOTH);
            nodep->dtypeSetLogicUnsized(32, 1, VSigning::SIGNED);  // Spec says integer return
        }
    }
    virtual void visit(AstFEof* nodep) override {
        if (m_vup->prelim()) {
            iterateCheckFileDesc(nodep, nodep->filep(), BOTH);
            nodep->dtypeSetLogicUnsized(32, 1, VSigning::SIGNED);  // Spec says integer return
        }
    }
    virtual void visit(AstFFlush* nodep) override {
        assertAtStatement(nodep);
        if (nodep->filep()) iterateCheckFileDesc(nodep, nodep->filep(), BOTH);
    }
    virtual void visit(AstFRewind* nodep) override {
        iterateCheckFileDesc(nodep, nodep->filep(), BOTH);
        nodep->dtypeSetLogicUnsized(32, 1, VSigning::SIGNED);  // Spec says integer return
    }
    virtual void visit(AstFTell* nodep) override {
        iterateCheckFileDesc(nodep, nodep->filep(), BOTH);
        nodep->dtypeSetLogicUnsized(32, 1, VSigning::SIGNED);  // Spec says integer return
    }
    virtual void visit(AstFSeek* nodep) override {
        iterateCheckFileDesc(nodep, nodep->filep(), BOTH);
        iterateCheckSigned32(nodep, "$fseek offset", nodep->offset(), BOTH);
        iterateCheckSigned32(nodep, "$fseek operation", nodep->operation(), BOTH);
        nodep->dtypeSetLogicUnsized(32, 1, VSigning::SIGNED);  // Spec says integer return
    }
    virtual void visit(AstFGetC* nodep) override {
        if (m_vup->prelim()) {
            iterateCheckFileDesc(nodep, nodep->filep(), BOTH);
            nodep->dtypeSetLogicUnsized(32, 8, VSigning::SIGNED);  // Spec says integer return
        }
    }
    virtual void visit(AstFGetS* nodep) override {
        if (m_vup->prelim()) {
            nodep->dtypeSetSigned32();  // Spec says integer return
            iterateCheckFileDesc(nodep, nodep->filep(), BOTH);
            userIterateAndNext(nodep->strgp(), WidthVP(SELF, BOTH).p());
        }
    }
    virtual void visit(AstFUngetC* nodep) override {
        if (m_vup->prelim()) {
            iterateCheckFileDesc(nodep, nodep->filep(), BOTH);
            iterateCheckSigned32(nodep, "$fungetc character", nodep->charp(), BOTH);
            nodep->dtypeSetLogicUnsized(32, 8, VSigning::SIGNED);  // Spec says integer return
        }
    }
    virtual void visit(AstFRead* nodep) override {
        if (m_vup->prelim()) {
            nodep->dtypeSetSigned32();  // Spec says integer return
            userIterateAndNext(nodep->memp(), WidthVP(SELF, BOTH).p());
            iterateCheckFileDesc(nodep, nodep->filep(), BOTH);
            if (nodep->startp()) {
                iterateCheckSigned32(nodep, "$fread start", nodep->startp(), BOTH);
            }
            if (nodep->countp()) {
                iterateCheckSigned32(nodep, "$fread count", nodep->countp(), BOTH);
            }
        }
    }
    virtual void visit(AstFScanF* nodep) override {
        if (m_vup->prelim()) {
            nodep->dtypeSetSigned32();  // Spec says integer return
            iterateCheckFileDesc(nodep, nodep->filep(), BOTH);
            userIterateAndNext(nodep->exprsp(), WidthVP(SELF, BOTH).p());
        }
    }
    virtual void visit(AstSScanF* nodep) override {
        if (m_vup->prelim()) {
            nodep->dtypeSetSigned32();  // Spec says integer return
            userIterateAndNext(nodep->fromp(), WidthVP(SELF, BOTH).p());
            userIterateAndNext(nodep->exprsp(), WidthVP(SELF, BOTH).p());
        }
    }
    virtual void visit(AstSysIgnore* nodep) override {
        userIterateAndNext(nodep->exprsp(), WidthVP(SELF, BOTH).p());
    }
    virtual void visit(AstSystemF* nodep) override {
        if (m_vup->prelim()) {
            userIterateAndNext(nodep->lhsp(), WidthVP(SELF, BOTH).p());
            nodep->dtypeSetSigned32();  // Spec says integer return
        }
    }
    virtual void visit(AstSysFuncAsTask* nodep) override {
        assertAtStatement(nodep);
        userIterateAndNext(nodep->lhsp(), WidthVP(SELF, BOTH).p());
    }
    virtual void visit(AstSystemT* nodep) override {
        assertAtStatement(nodep);
        userIterateAndNext(nodep->lhsp(), WidthVP(SELF, BOTH).p());
    }
    virtual void visit(AstNodeReadWriteMem* nodep) override {
        assertAtStatement(nodep);
        userIterateAndNext(nodep->filenamep(), WidthVP(SELF, BOTH).p());
        userIterateAndNext(nodep->memp(), WidthVP(SELF, BOTH).p());
        const AstNodeDType* subp = nullptr;
        if (const AstAssocArrayDType* adtypep
            = VN_CAST(nodep->memp()->dtypep()->skipRefp(), AssocArrayDType)) {
            subp = adtypep->subDTypep();
            if (!adtypep->keyDTypep()->skipRefp()->basicp()
                || !adtypep->keyDTypep()->skipRefp()->basicp()->keyword().isIntNumeric()) {
                nodep->memp()->v3error(nodep->verilogKwd()
                                       << " address/key must be integral (IEEE 1800-2017 21.4.1)");
            }
        } else if (const AstUnpackArrayDType* const adtypep
                   = VN_CAST(nodep->memp()->dtypep()->skipRefp(), UnpackArrayDType)) {
            subp = adtypep->subDTypep();
        } else {
            nodep->memp()->v3warn(E_UNSUPPORTED,
                                  "Unsupported: "
                                      << nodep->verilogKwd()
                                      << " into other than unpacked or associative array");
        }
        if (subp
            && (!subp->skipRefp()->basicp()
                || !subp->skipRefp()->basicp()->keyword().isIntNumeric())) {
            nodep->memp()->v3warn(E_UNSUPPORTED,
                                  "Unsupported: " << nodep->verilogKwd()
                                                  << " array values must be integral");
        }
        userIterateAndNext(nodep->lsbp(), WidthVP(SELF, BOTH).p());
        userIterateAndNext(nodep->msbp(), WidthVP(SELF, BOTH).p());
    }
    virtual void visit(AstTestPlusArgs* nodep) override {
        if (m_vup->prelim()) {
            userIterateAndNext(nodep->searchp(), WidthVP{SELF, BOTH}.p());
            nodep->dtypeChgWidthSigned(32, 1, VSigning::SIGNED);  // Spec says integer return
        }
    }
    virtual void visit(AstValuePlusArgs* nodep) override {
        if (m_vup->prelim()) {
            userIterateAndNext(nodep->searchp(), WidthVP(SELF, BOTH).p());
            userIterateAndNext(nodep->outp(), WidthVP(SELF, BOTH).p());
            nodep->dtypeChgWidthSigned(32, 1, VSigning::SIGNED);  // Spec says integer return
        }
    }
    virtual void visit(AstTimeFormat* nodep) override {
        assertAtStatement(nodep);
        iterateCheckSigned32(nodep, "units", nodep->unitsp(), BOTH);
        iterateCheckSigned32(nodep, "precision", nodep->precisionp(), BOTH);
        iterateCheckString(nodep, "suffix", nodep->suffixp(), BOTH);
        iterateCheckSigned32(nodep, "width", nodep->widthp(), BOTH);
    }
    virtual void visit(AstUCStmt* nodep) override {
        // Just let all arguments seek their natural sizes
        assertAtStatement(nodep);
        userIterateChildren(nodep, WidthVP(SELF, BOTH).p());
    }
    virtual void visit(AstAssert* nodep) override {
        assertAtStatement(nodep);
        iterateCheckBool(nodep, "Property", nodep->propp(), BOTH);  // it's like an if() condition.
        userIterateAndNext(nodep->passsp(), nullptr);
        userIterateAndNext(nodep->failsp(), nullptr);
    }
    virtual void visit(AstAssertIntrinsic* nodep) override {
        assertAtStatement(nodep);
        iterateCheckBool(nodep, "Property", nodep->propp(), BOTH);  // it's like an if() condition.
        userIterateAndNext(nodep->passsp(), nullptr);
        userIterateAndNext(nodep->failsp(), nullptr);
    }
    virtual void visit(AstCover* nodep) override {
        assertAtStatement(nodep);
        iterateCheckBool(nodep, "Property", nodep->propp(), BOTH);  // it's like an if() condition.
        userIterateAndNext(nodep->passsp(), nullptr);
    }
    virtual void visit(AstRestrict* nodep) override {
        assertAtStatement(nodep);
        iterateCheckBool(nodep, "Property", nodep->propp(), BOTH);  // it's like an if() condition.
    }
    virtual void visit(AstPin* nodep) override {
        // if (debug()) nodep->dumpTree(cout, "-  PinPre: ");
        // TOP LEVEL NODE
        if (nodep->modVarp() && nodep->modVarp()->isGParam()) {
            // Widthing handled as special init() case
            if (auto* const patternp = VN_CAST(nodep->exprp(), Pattern)) {
                if (const auto* modVarp = nodep->modVarp()) {
                    patternp->childDTypep(modVarp->childDTypep()->cloneTree(false));
                }
            }
            userIterateChildren(nodep, WidthVP(SELF, BOTH).p());
        } else if (!m_paramsOnly) {
            if (!nodep->modVarp()->didWidth()) {
                // Var hasn't been widthed, so make it so.
                userIterate(nodep->modVarp(), nullptr);
            }
            if (!nodep->exprp()) {  // No-connect
                return;
            }
            // Very much like like an assignment, but which side is LH/RHS
            // depends on pin being a in/output/inout.
            userIterateAndNext(nodep->exprp(), WidthVP(nodep->modVarp()->dtypep(), PRELIM).p());
            AstNodeDType* modDTypep = nodep->modVarp()->dtypep();
            AstNodeDType* conDTypep = nodep->exprp()->dtypep();
            if (!modDTypep) nodep->v3fatalSrc("Unlinked pin data type");
            if (!conDTypep) nodep->v3fatalSrc("Unlinked pin data type");
            modDTypep = modDTypep->skipRefp();
            conDTypep = conDTypep->skipRefp();
            AstNodeDType* subDTypep = modDTypep;
            const int modwidth = modDTypep->width();
            const int conwidth = conDTypep->width();
            if (conDTypep == modDTypep  // If match, we're golden
                || similarDTypeRecurse(conDTypep, modDTypep)) {
                userIterateAndNext(nodep->exprp(), WidthVP(subDTypep, FINAL).p());
            } else if (m_cellp->rangep()) {
                const int numInsts = m_cellp->rangep()->elementsConst();
                if (conwidth == modwidth) {
                    // Arrayed instants: widths match so connect to each instance
                    subDTypep = conDTypep;  // = same expr dtype
                } else if (conwidth == numInsts * modwidth) {
                    // Arrayed instants: one bit for each of the instants (each
                    // assign is 1 modwidth wide)
                    subDTypep = conDTypep;  // = same expr dtype (but numInst*pin_dtype)
                } else {
                    // Must be a error according to spec
                    // (Because we need to know if to connect to one or all instants)
                    nodep->v3error(ucfirst(nodep->prettyOperatorName())
                                   << " as part of a module instance array"
                                   << " requires " << modwidth << " or " << modwidth * numInsts
                                   << " bits, but connection's "
                                   << nodep->exprp()->prettyTypeName() << " generates " << conwidth
                                   << " bits. (IEEE 1800-2017 23.3.3)");
                    subDTypep = conDTypep;  // = same expr dtype
                }
                userIterateAndNext(nodep->exprp(), WidthVP(subDTypep, FINAL).p());
            } else {
                if (nodep->modVarp()->direction() == VDirection::REF) {
                    nodep->v3error("Ref connection "
                                   << nodep->modVarp()->prettyNameQ()
                                   << " requires matching types;"
                                   << " ref requires " << modDTypep->prettyDTypeNameQ()
                                   << " data type but connection is "
                                   << conDTypep->prettyDTypeNameQ() << " data type.");
                } else if (nodep->modVarp()->isTristate()) {
                    if (modwidth != conwidth) {
                        // Ideally should call pinReconnectSimple which would tolerate this
                        // then have a conversion warning
                        nodep->v3warn(E_UNSUPPORTED,
                                      "Unsupported: " << ucfirst(nodep->prettyOperatorName())
                                                      << " to inout signal requires " << modwidth
                                                      << " bits, but connection's "
                                                      << nodep->exprp()->prettyTypeName()
                                                      << " generates " << conwidth << " bits.");
                        // otherwise would need some mess to force both sides to proper size
                    }
                } else if (nodep->modVarp()->direction().isWritable()
                           && ((conDTypep->isDouble() && !modDTypep->isDouble())
                               || (!conDTypep->isDouble() && modDTypep->isDouble()))) {
                    nodep->v3warn(E_UNSUPPORTED,
                                  "Unsupported: " << ucfirst(nodep->prettyOperatorName())
                                                  << " connects real to non-real");
                }

                // Check if an interface is connected to a non-interface and vice versa
                if ((VN_IS(modDTypep, IfaceRefDType) && !VN_IS(conDTypep, IfaceRefDType))
                    || (VN_IS(conDTypep, IfaceRefDType) && !VN_IS(modDTypep, IfaceRefDType))) {
                    nodep->v3error("Illegal " << nodep->prettyOperatorName() << ","
                                              << " mismatch between port which is"
                                              << (VN_CAST(modDTypep, IfaceRefDType) ? "" : " not")
                                              << " an interface,"
                                              << " and expression which is"
                                              << (VN_CAST(conDTypep, IfaceRefDType) ? "" : " not")
                                              << " an interface.");
                }

                // TODO Simple dtype checking, should be a more general check
                const AstNodeArrayDType* const exprArrayp = VN_CAST(conDTypep, UnpackArrayDType);
                const AstNodeArrayDType* const modArrayp = VN_CAST(modDTypep, UnpackArrayDType);
                if (exprArrayp && modArrayp && VN_IS(exprArrayp->subDTypep(), IfaceRefDType)
                    && exprArrayp->declRange().elements() != modArrayp->declRange().elements()) {
                    const int exprSize = exprArrayp->declRange().elements();
                    const int modSize = modArrayp->declRange().elements();
                    nodep->v3error("Illegal "
                                   << nodep->prettyOperatorName() << ","
                                   << " mismatch between port which is an interface array of size "
                                   << modSize << ","
                                   << " and expression which is an interface array of size "
                                   << exprSize << ".");
                    UINFO(1, "    Related lo: " << modDTypep << endl);
                    UINFO(1, "    Related hi: " << conDTypep << endl);
                } else if ((exprArrayp && !modArrayp) || (!exprArrayp && modArrayp)) {
                    nodep->v3error("Illegal " << nodep->prettyOperatorName() << ","
                                              << " mismatch between port which is"
                                              << (modArrayp ? "" : " not") << " an array,"
                                              << " and expression which is"
                                              << (exprArrayp ? "" : " not")
                                              << " an array. (IEEE 1800-2017 7.6)");
                    UINFO(1, "    Related lo: " << modDTypep << endl);
                    UINFO(1, "    Related hi: " << conDTypep << endl);
                }
                iterateCheckAssign(nodep, "pin connection", nodep->exprp(), FINAL, subDTypep);
            }
        }
        // if (debug()) nodep->dumpTree(cout, "-  PinOut: ");
    }
    virtual void visit(AstCell* nodep) override {
        VL_RESTORER(m_cellp);
        m_cellp = nodep;
        if (!m_paramsOnly) {
            if (VN_IS(nodep->modp(), NotFoundModule)) {
                // We've resolved parameters and hit a module that we couldn't resolve.  It's
                // finally time to report it.
                // Note only here in V3Width as this is first visitor after V3Dead.
                nodep->modNameFileline()->v3error("Cannot find file containing module: '"
                                                  << nodep->modName() << "'");
                v3Global.opt.filePathLookedMsg(nodep->modNameFileline(), nodep->modName());
            }
            if (nodep->rangep()) userIterateAndNext(nodep->rangep(), WidthVP(SELF, BOTH).p());
            userIterateAndNext(nodep->pinsp(), nullptr);
        }
        userIterateAndNext(nodep->paramsp(), nullptr);
    }
    virtual void visit(AstGatePin* nodep) override {
        if (m_vup->prelim()) {
            userIterateAndNext(nodep->rangep(), WidthVP(SELF, BOTH).p());
            userIterateAndNext(nodep->exprp(), WidthVP(CONTEXT, PRELIM).p());
            nodep->dtypeFrom(nodep->rangep());
            // Very much like like an pin
            const AstNodeDType* const conDTypep = nodep->exprp()->dtypep();
            const int numInsts = nodep->rangep()->elementsConst();
            const int modwidth = numInsts;
            const int conwidth = conDTypep->width();
            if (conwidth == 1 && modwidth > 1) {  // Multiple connections
                AstNodeDType* const subDTypep = nodep->findLogicDType(1, 1, conDTypep->numeric());
                userIterateAndNext(nodep->exprp(), WidthVP(subDTypep, FINAL).p());
                AstNode* const newp = new AstReplicate(nodep->fileline(),
                                                       nodep->exprp()->unlinkFrBack(), numInsts);
                nodep->replaceWith(newp);
            } else {
                // Eliminating so pass down all of vup
                userIterateAndNext(nodep->exprp(), m_vup);
                nodep->replaceWith(nodep->exprp()->unlinkFrBack());
            }
            VL_DO_DANGLING(pushDeletep(nodep), nodep);
        }
    }
    virtual void visit(AstNodeFTask* nodep) override {
        // Grab width from the output variable (if it's a function)
        if (nodep->didWidth()) return;
        if (nodep->doingWidth()) {
            UINFO(5, "Recursive function or task call: " << nodep);
            nodep->v3warn(E_UNSUPPORTED, "Unsupported: Recursive function or task call: "
                                             << nodep->prettyNameQ());
            nodep->recursive(true);
            nodep->didWidth(true);
            return;
        }
        if (nodep->classMethod() && nodep->name() == "rand_mode") {
            nodep->v3error("The 'rand_mode' method is built-in and cannot be overridden"
                           " (IEEE 1800-2017 18.8)");
        } else if (nodep->classMethod() && nodep->name() == "constraint_mode") {
            nodep->v3error("The 'constraint_mode' method is built-in and cannot be overridden"
                           " (IEEE 1800-2017 18.9)");
        }
        // Function hasn't been widthed, so make it so.
        // Would use user1 etc, but V3Width called from too many places to spend a user
        nodep->doingWidth(true);
        m_ftaskp = nodep;
        // First width the function variable, as if is a recursive function we need data type
        if (nodep->fvarp()) userIterate(nodep->fvarp(), nullptr);
        if (nodep->isConstructor()) {
            // Pretend it's void so less special casing needed when look at dtypes
            nodep->dtypeSetVoid();
        } else if (nodep->fvarp()) {
            m_funcp = VN_AS(nodep, Func);
            UASSERT_OBJ(m_funcp, nodep, "FTask with function variable, but isn't a function");
            nodep->dtypeFrom(nodep->fvarp());  // Which will get it from fvarp()->dtypep()
        }
        userIterateChildren(nodep, nullptr);
        nodep->didWidth(true);
        nodep->doingWidth(false);
        m_funcp = nullptr;
        m_ftaskp = nullptr;
        if (nodep->dpiImport() && !nodep->dpiOpenParent() && markHasOpenArray(nodep)) {
            nodep->dpiOpenParentInc();  // Mark so V3Task will wait for a child to build calling
                                        // func
        }
    }
    virtual void visit(AstReturn* nodep) override {
        // IEEE: Assignment-like context
        assertAtStatement(nodep);
        if (!m_funcp) {
            if (nodep->lhsp()) {  // Return w/o value ok other places
                nodep->v3error("Return with return value isn't underneath a function");
            }
        } else {
            if (nodep->lhsp()) {
                // Function hasn't been widthed, so make it so.
                nodep->dtypeFrom(m_funcp->fvarp());
                // AstPattern requires assignments to pass datatype on PRELIM
                userIterateAndNext(nodep->lhsp(), WidthVP(nodep->dtypep(), PRELIM).p());
                iterateCheckAssign(nodep, "Return value", nodep->lhsp(), FINAL, nodep->dtypep());
            }
        }
    }

    virtual void visit(AstFuncRef* nodep) override {
        visit(static_cast<AstNodeFTaskRef*>(nodep));
        nodep->dtypeFrom(nodep->taskp());
        // if (debug()) nodep->dumpTree(cout, "  FuncOut: ");
    }
    // Returns true if dtypep0 and dtypep1 have same dimensions
    static bool areSameSize(AstUnpackArrayDType* dtypep0, AstUnpackArrayDType* dtypep1) {
        const std::vector<AstUnpackArrayDType*> dims0 = dtypep0->unpackDimensions();
        const std::vector<AstUnpackArrayDType*> dims1 = dtypep1->unpackDimensions();
        if (dims0.size() != dims1.size()) return false;
        for (size_t i = 0; i < dims0.size(); ++i) {
            if (dims0[i]->elementsConst() != dims1[i]->elementsConst()) return false;
        }
        return true;
    }
    // Makes sure that port and pin have same size and same datatype
    void checkUnpackedArrayArgs(AstVar* portp, AstNode* pinp) {
        if (AstUnpackArrayDType* const portDtypep
            = VN_CAST(portp->dtypep()->skipRefp(), UnpackArrayDType)) {
            if (AstUnpackArrayDType* const pinDtypep
                = VN_CAST(pinp->dtypep()->skipRefp(), UnpackArrayDType)) {
                if (!areSameSize(portDtypep, pinDtypep)) {
                    pinp->v3warn(E_UNSUPPORTED,
                                 "Shape of the argument does not match the shape of the parameter "
                                     << "(" << pinDtypep->prettyDTypeNameQ() << " v.s. "
                                     << portDtypep->prettyDTypeNameQ() << ")");
                }
                if (portDtypep->basicp()->width() != pinDtypep->basicp()->width()
                    || (portDtypep->basicp()->keyword() != pinDtypep->basicp()->keyword()
                        && !(portDtypep->basicp()->keyword() == VBasicDTypeKwd::LOGIC_IMPLICIT
                             && pinDtypep->basicp()->keyword() == VBasicDTypeKwd::LOGIC)
                        && !(portDtypep->basicp()->keyword() == VBasicDTypeKwd::LOGIC
                             && pinDtypep->basicp()->keyword()
                                    == VBasicDTypeKwd::LOGIC_IMPLICIT))) {
                    pinp->v3warn(E_UNSUPPORTED,
                                 "Shape of the argument does not match the shape of the parameter "
                                     << "(" << pinDtypep->basicp()->prettyDTypeNameQ() << " v.s. "
                                     << portDtypep->basicp()->prettyDTypeNameQ() << ")");
                }
            } else {
                pinp->v3warn(E_UNSUPPORTED, "Argument is not an unpacked array while parameter "
                                                << portp->prettyNameQ() << " is");
            }
        }
    }
    void processFTaskRefArgs(AstNodeFTaskRef* nodep) {
        // For arguments, is assignment-like context; see IEEE rules in AstNodeAssign
        // Function hasn't been widthed, so make it so.
        UINFO(5, "  FTASKREF " << nodep << endl);
        UASSERT_OBJ(nodep->taskp(), nodep, "Unlinked");
        if (nodep->didWidth()) return;
        userIterate(nodep->taskp(), nullptr);
        //
        // And do the arguments to the task/function too
        do {
        reloop:
            const V3TaskConnects tconnects = V3Task::taskConnects(nodep, nodep->taskp()->stmtsp());
            for (const auto& tconnect : tconnects) {
                const AstVar* const portp = tconnect.first;
                AstArg* const argp = tconnect.second;
                AstNode* pinp = argp->exprp();
                if (!pinp) continue;  // Argument error we'll find later
                // Prelim may cause the node to get replaced; we've lost our
                // pointer, so need to iterate separately later
                if (portp->attrSFormat()
                    && (!VN_IS(pinp, SFormatF) || pinp->nextp())) {  // Not already done
                    UINFO(4, "   sformat via metacomment: " << nodep << endl);
                    VNRelinker handle;
                    argp->unlinkFrBackWithNext(&handle);  // Format + additional args, if any
                    AstNode* argsp = nullptr;
                    while (AstArg* const nextargp = VN_AS(argp->nextp(), Arg)) {
                        argsp = AstNode::addNext(
                            argsp, nextargp->exprp()
                                       ->unlinkFrBackWithNext());  // Expression goes to SFormatF
                        nextargp->unlinkFrBack()->deleteTree();  // Remove the call's Arg wrapper
                    }
                    string format;
                    if (VN_IS(pinp, Const)) {
                        format = VN_AS(pinp, Const)->num().toString();
                    } else {
                        pinp->v3error(
                            "Format to $display-like function must have constant format string");
                    }
                    VL_DO_DANGLING(pushDeletep(argp), argp);
                    AstSFormatF* const newp
                        = new AstSFormatF(nodep->fileline(), format, false, argsp);
                    if (!newp->scopeNamep() && newp->formatScopeTracking()) {
                        newp->scopeNamep(new AstScopeName{newp->fileline(), true});
                    }
                    handle.relink(new AstArg(newp->fileline(), "", newp));
                    // Connection list is now incorrect (has extra args in it).
                    goto reloop;  // so exit early; next loop will correct it
                }  //
                else if (portp->basicp() && portp->basicp()->keyword() == VBasicDTypeKwd::STRING
                         && !VN_IS(pinp, CvtPackString)
                         && !VN_IS(pinp, SFormatF)  // Already generates a string
                         && !VN_IS(portp->dtypep(), UnpackArrayDType)  // Unpacked array must match
                         && !(VN_IS(pinp, VarRef)
                              && VN_AS(pinp, VarRef)->varp()->basicp()->keyword()
                                     == VBasicDTypeKwd::STRING)) {
                    UINFO(4, "   Add CvtPackString: " << pinp << endl);
                    VNRelinker handle;
                    pinp->unlinkFrBack(&handle);  // No next, that's the next pin
                    AstNode* const newp = new AstCvtPackString(pinp->fileline(), pinp);
                    handle.relink(newp);
                    pinp = newp;
                }
                // AstPattern requires assignments to pass datatype on PRELIM
                VL_DO_DANGLING(userIterate(pinp, WidthVP(portp->dtypep(), PRELIM).p()), pinp);
            }
        } while (false);
        // Stage 2
        {
            const V3TaskConnects tconnects = V3Task::taskConnects(nodep, nodep->taskp()->stmtsp());
            for (const auto& tconnect : tconnects) {
                AstVar* const portp = tconnect.first;
                const AstArg* const argp = tconnect.second;
                AstNode* const pinp = argp->exprp();
                if (!pinp) continue;  // Argument error we'll find later
                // Change data types based on above accept completion
                if (nodep->taskp()->dpiImport()) checkUnpackedArrayArgs(portp, pinp);
                if (portp->isDouble()) VL_DO_DANGLING(spliceCvtD(pinp), pinp);
            }
        }
        // Stage 3
        {
            const V3TaskConnects tconnects = V3Task::taskConnects(nodep, nodep->taskp()->stmtsp());
            for (const auto& tconnect : tconnects) {
                const AstVar* const portp = tconnect.first;
                const AstArg* const argp = tconnect.second;
                AstNode* const pinp = argp->exprp();
                if (!pinp) continue;  // Argument error we'll find later
                // Do PRELIM again, because above accept may have exited early
                // due to node replacement
                userIterate(pinp, WidthVP(portp->dtypep(), PRELIM).p());
            }
        }
        // Cleanup any open arrays
        if (markHasOpenArray(nodep->taskp())) makeOpenArrayShell(nodep);
        // Stage 4
        {
            const V3TaskConnects tconnects = V3Task::taskConnects(nodep, nodep->taskp()->stmtsp());
            for (const auto& tconnect : tconnects) {
                const AstVar* const portp = tconnect.first;
                const AstArg* const argp = tconnect.second;
                AstNode* const pinp = argp->exprp();
                if (!pinp) continue;  // Argument error we'll find later
                if (portp->direction() == VDirection::REF
                    && !similarDTypeRecurse(portp->dtypep(), pinp->dtypep())) {
                    pinp->v3error("Ref argument requires matching types;"
                                  << " port " << portp->prettyNameQ() << " requires "
                                  << portp->prettyTypeName() << " but connection is "
                                  << pinp->prettyTypeName() << ".");
                } else if (portp->isWritable() && pinp->width() != portp->width()) {
                    pinp->v3warn(E_UNSUPPORTED, "Unsupported: Function output argument "
                                                    << portp->prettyNameQ() << " requires "
                                                    << portp->width() << " bits, but connection's "
                                                    << pinp->prettyTypeName() << " generates "
                                                    << pinp->width() << " bits.");
                    // otherwise would need some mess to force both sides to proper size
                    // (get an ASSIGN with EXTEND on the lhs instead of rhs)
                }
                if (!portp->basicp() || portp->basicp()->isOpaque()) {
                    userIterate(pinp, WidthVP(portp->dtypep(), FINAL).p());
                } else {
                    iterateCheckAssign(nodep, "Function Argument", pinp, FINAL, portp->dtypep());
                }
            }
        }
    }
    virtual void visit(AstNodeFTaskRef* nodep) override {
        // For arguments, is assignment-like context; see IEEE rules in AstNodeAssign
        // Function hasn't been widthed, so make it so.
        UINFO(5, "  FTASKREF " << nodep << endl);
        UASSERT_OBJ(nodep->taskp(), nodep, "Unlinked");
        if (nodep->didWidth()) return;
        userIterate(nodep->taskp(), nullptr);
        // And do the arguments to the task/function too
        processFTaskRefArgs(nodep);
        nodep->didWidth(true);
    }
    virtual void visit(AstNodeProcedure* nodep) override {
        assertAtStatement(nodep);
        m_procedurep = nodep;
        userIterateChildren(nodep, nullptr);
        m_procedurep = nullptr;
    }
    virtual void visit(AstWith* nodep) override {
        // Should otherwise be underneath a method call
        AstNodeDType* const vdtypep = m_vup->dtypeNullSkipRefp();
        {
            VL_RESTORER(m_withp);
            m_withp = nodep;
            userIterateChildren(nodep->indexArgRefp(), nullptr);
            userIterateChildren(nodep->valueArgRefp(), nullptr);
            if (vdtypep) {
                userIterateAndNext(nodep->exprp(), WidthVP(nodep->dtypep(), PRELIM).p());
            } else {  // 'sort with' allows arbitrary type
                userIterateAndNext(nodep->exprp(), WidthVP(SELF, PRELIM).p());
            }
            nodep->dtypeFrom(nodep->exprp());
            iterateCheckAssign(nodep, "'with' return value", nodep->exprp(), FINAL,
                               nodep->dtypep());
        }
    }
    virtual void visit(AstLambdaArgRef* nodep) override {
        UASSERT_OBJ(m_withp, nodep, "LambdaArgRef not underneath 'with' lambda");
        if (nodep->index()) {
            nodep->dtypeFrom(m_withp->indexArgRefp());
        } else {
            nodep->dtypeFrom(m_withp->valueArgRefp());
        }
    }
    virtual void visit(AstNetlist* nodep) override {
        // Iterate modules backwards, in bottom-up order.  That's faster
        userIterateChildrenBackwards(nodep, nullptr);
    }

    //--------------------
    // Default
    virtual void visit(AstNodeMath* nodep) override {
        if (!nodep->didWidth()) {
            nodep->v3fatalSrc(
                "Visit function missing? Widthed function missing for math node: " << nodep);
        }
        userIterateChildren(nodep, nullptr);
    }
    virtual void visit(AstNode* nodep) override {
        // Default: Just iterate
        UASSERT_OBJ(!m_vup, nodep,
                    "Visit function missing? Widthed expectation for this node: " << nodep);
        userIterateChildren(nodep, nullptr);
    }

    //----------------------------------------------------------------------
    // WIDTH METHODs -- all iterate

    void visit_Or_Lu64(AstNodeUniop* nodep) {
        // CALLER: AstBitsToRealD
        // Real: Output real
        // LHS presumed self-determined, then coerced to real
        if (m_vup->prelim()) {  // First stage evaluation
            nodep->dtypeSetDouble();
            AstNodeDType* const subDTypep = nodep->findLogicDType(64, 64, VSigning::UNSIGNED);
            // Self-determined operand
            userIterateAndNext(nodep->lhsp(), WidthVP(SELF, PRELIM).p());
            iterateCheck(nodep, "LHS", nodep->lhsp(), SELF, FINAL, subDTypep, EXTEND_EXP);
        }
    }
    virtual void visit(AstIToRD* nodep) override {
        // Real: Output real
        // LHS presumed self-determined, then coerced to real
        if (m_vup->prelim()) {  // First stage evaluation
            nodep->dtypeSetDouble();
            // Self-determined operand (TODO check if numeric type)
            userIterateAndNext(nodep->lhsp(), WidthVP(SELF, PRELIM).p());
            if (nodep->lhsp()->isSigned()) {
                nodep->replaceWith(
                    new AstISToRD(nodep->fileline(), nodep->lhsp()->unlinkFrBack()));
                VL_DO_DANGLING(nodep->deleteTree(), nodep);
            }
        }
    }
    virtual void visit(AstISToRD* nodep) override {
        // Real: Output real
        // LHS presumed self-determined, then coerced to real
        if (m_vup->prelim()) {  // First stage evaluation
            nodep->dtypeSetDouble();
            // Self-determined operand (TODO check if numeric type)
            userIterateAndNext(nodep->lhsp(), WidthVP(SELF, PRELIM).p());
        }
    }
    void visit_Os32_Lr(AstNodeUniop* nodep) {
        // CALLER: RToI
        // Real: LHS real
        // LHS presumed self-determined, then coerced to real
        if (m_vup->prelim()) {  // First stage evaluation
            iterateCheckReal(nodep, "LHS", nodep->lhsp(), BOTH);
            nodep->dtypeSetSigned32();
        }
    }
    void visit_Ou64_Lr(AstNodeUniop* nodep) {
        // CALLER: RealToBits
        // Real: LHS real
        // LHS presumed self-determined, then coerced to real
        if (m_vup->prelim()) {  // First stage evaluation
            iterateCheckReal(nodep, "LHS", nodep->lhsp(), BOTH);
            nodep->dtypeSetUInt64();
        }
    }

    void visit_log_not(AstNode* nodep) {
        // CALLER: LogNot
        // Width-check: lhs 1 bit
        // Real: Allowed; implicitly compares with zero
        // We calculate the width of the UNDER expression.
        // We then check its width to see if it's legal, and edit if not
        // We finally set the width of our output
        // IEEE-2012: Table 11-21 and 11.8.1 (same as RedAnd):
        //   LHS is self-determined
        //   Width: 1 bit out
        //   Sign: unsigned out (11.8.1)
        UASSERT_OBJ(!nodep->op2p(), nodep, "For unary ops only!");
        if (m_vup->prelim()) {
            iterateCheckBool(nodep, "LHS", nodep->op1p(), BOTH);
            nodep->dtypeSetBit();
        }
    }
    void visit_log_and_or(AstNodeBiop* nodep) {
        // CALLER: LogAnd, LogOr, LogEq, LogIf
        // Widths: 1 bit out, lhs 1 bit, rhs 1 bit
        // IEEE-2012 Table 11-21:
        //   LHS is self-determined
        //   RHS is self-determined
        if (m_vup->prelim()) {
            iterateCheckBool(nodep, "LHS", nodep->lhsp(), BOTH);
            iterateCheckBool(nodep, "RHS", nodep->rhsp(), BOTH);
            nodep->dtypeSetBit();
        }
    }
    void visit_red_and_or(AstNodeUniop* nodep) {
        // CALLER: RedAnd, RedOr, ...
        // Signed: Output unsigned, Lhs/Rhs/etc non-real (presumed, not in IEEE)
        // IEEE-2012: Table 11-21 and 11.8.1:
        //   LHS is self-determined
        //   Width: 1 bit out
        //   Sign: unsigned out (11.8.1)
        if (m_vup->prelim()) {
            iterateCheckSizedSelf(nodep, "LHS", nodep->lhsp(), SELF, BOTH);
            nodep->dtypeSetBit();
        }
    }
    void visit_red_unknown(AstNodeUniop* nodep) {
        // CALLER: IsUnknown
        // Signed: Output unsigned, Lhs/Rhs/etc non-real (presumed, not in IEEE)
        // IEEE-2012: Table 11-21 and 11.8.1:
        //   LHS is self-determined
        //   Width: 1 bit out
        //   Sign: unsigned out (11.8.1)
        if (m_vup->prelim()) {
            userIterateAndNext(nodep->lhsp(), WidthVP(SELF, BOTH).p());
            nodep->dtypeSetBit();
        }
    }

    void visit_cmp_eq_gt(AstNodeBiop* nodep, bool realok) {
        // CALLER: AstEq, AstGt, ..., AstLtS
        // Real allowed if and only if real_lhs set
        // See IEEE-2012 11.4.4, and 11.8.1:
        //   Widths: 1 bit out, width is max of LHS or RHS
        //   Sign:  signed compare (not output) if both signed, compare is signed,
        //             width mismatches sign extend
        //             else, compare is unsigned, **zero-extends**
        //   Real:  If either real, other side becomes real and real compare
        //   TODO: chandle/class handle/iface handle: WildEq/WildNeq same as Eq/Neq
        //   TODO: chandle/class handle/iface handle only allowed to self-compare or against null
        //   TODO: chandle/class handle/iface handle no relational compares
        UASSERT_OBJ(nodep->rhsp(), nodep, "For binary ops only!");
        if (m_vup->prelim()) {
            userIterateAndNext(nodep->lhsp(), WidthVP(CONTEXT, PRELIM).p());
            userIterateAndNext(nodep->rhsp(), WidthVP(CONTEXT, PRELIM).p());
            if (nodep->lhsp()->isDouble() || nodep->rhsp()->isDouble()) {
                if (!realok) nodep->v3error("Real not allowed as operand to in ?== operator");
                if (AstNodeBiop* const newp = replaceWithDVersion(nodep)) {
                    VL_DANGLING(nodep);
                    nodep = newp;  // Process new node instead
                    iterateCheckReal(nodep, "LHS", nodep->lhsp(), FINAL);
                    iterateCheckReal(nodep, "RHS", nodep->rhsp(), FINAL);
                }
            } else if (nodep->lhsp()->isString() || nodep->rhsp()->isString()) {
                if (AstNodeBiop* const newp = replaceWithNVersion(nodep)) {
                    VL_DANGLING(nodep);
                    nodep = newp;  // Process new node instead
                    iterateCheckString(nodep, "LHS", nodep->lhsp(), FINAL);
                    iterateCheckString(nodep, "RHS", nodep->rhsp(), FINAL);
                }
            } else {
                const bool signedFl = nodep->lhsp()->isSigned() && nodep->rhsp()->isSigned();
                if (AstNodeBiop* const newp = replaceWithUOrSVersion(nodep, signedFl)) {
                    VL_DANGLING(nodep);
                    nodep = newp;  // Process new node instead
                }
                const int width = std::max(nodep->lhsp()->width(), nodep->rhsp()->width());
                const int ewidth = std::max(nodep->lhsp()->widthMin(), nodep->rhsp()->widthMin());
                AstNodeDType* const subDTypep
                    = nodep->findLogicDType(width, ewidth, VSigning::fromBool(signedFl));
                bool warnOn = true;
                if (!signedFl && width == 32) {
                    // Waive on unsigned < or <= if RHS is narrower, since can't give wrong answer
                    if ((VN_IS(nodep, Lt) || VN_IS(nodep, Lte))
                        && (nodep->lhsp()->width() >= nodep->rhsp()->widthMin())) {
                        warnOn = false;
                    }
                    // Waive on unsigned > or >= if RHS is wider, since can't give wrong answer
                    if ((VN_IS(nodep, Gt) || VN_IS(nodep, Gte))
                        && (nodep->lhsp()->widthMin() >= nodep->rhsp()->width())) {
                        warnOn = false;
                    }
                }
                iterateCheck(nodep, "LHS", nodep->lhsp(), CONTEXT, FINAL, subDTypep,
                             (signedFl ? EXTEND_LHS : EXTEND_ZERO), warnOn);
                iterateCheck(nodep, "RHS", nodep->rhsp(), CONTEXT, FINAL, subDTypep,
                             (signedFl ? EXTEND_LHS : EXTEND_ZERO), warnOn);
            }
            nodep->dtypeSetBit();
        }
    }
    void visit_cmp_real(AstNodeBiop* nodep) {
        // CALLER: EqD, LtD
        // Widths: 1 bit out, lhs width == rhs width
        // Signed compare (not output) if both sides signed
        // Real if and only if real_allow set
        // IEEE, 11.4.4: relational compares (<,>,<=,>=,==,===,!=,!==) use
        // "zero padding" on unsigned
        UASSERT_OBJ(nodep->rhsp(), nodep, "For binary ops only!");
        if (m_vup->prelim()) {
            // See similar handling in visit_cmp_eq_gt where created
            iterateCheckReal(nodep, "LHS", nodep->lhsp(), BOTH);
            iterateCheckReal(nodep, "RHS", nodep->rhsp(), BOTH);
            nodep->dtypeSetBit();
        }
    }
    void visit_cmp_string(AstNodeBiop* nodep) {
        // CALLER: EqN, LtN
        // Widths: 1 bit out, lhs width == rhs width
        // String compare (not output)
        // Real if and only if real_allow set
        UASSERT_OBJ(nodep->rhsp(), nodep, "For binary ops only!");
        if (m_vup->prelim()) {
            // See similar handling in visit_cmp_eq_gt where created
            iterateCheckString(nodep, "LHS", nodep->lhsp(), BOTH);
            iterateCheckString(nodep, "RHS", nodep->rhsp(), BOTH);
            nodep->dtypeSetBit();
        }
    }

    void visit_Os32_string(AstNodeUniop* nodep) {
        // CALLER: LenN
        // Widths: 32 bit out
        UASSERT_OBJ(nodep->lhsp(), nodep, "For unary ops only!");
        if (m_vup->prelim()) {
            // See similar handling in visit_cmp_eq_gt where created
            iterateCheckString(nodep, "LHS", nodep->lhsp(), BOTH);
            nodep->dtypeSetSigned32();
        }
    }

    void visit_negate_not(AstNodeUniop* nodep, bool real_ok) {
        // CALLER: (real_ok=false) Not
        // CALLER: (real_ok=true) Negate - allow real numbers
        // Signed: From lhs
        // IEEE-2012 Table 11-21:
        //    Widths: out width = lhs width
        UASSERT_OBJ(!nodep->op2p(), nodep, "For unary ops only!");
        if (m_vup->prelim()) {
            userIterateAndNext(nodep->lhsp(), WidthVP(CONTEXT, PRELIM).p());
            if (!real_ok) checkCvtUS(nodep->lhsp());
        }
        if (real_ok && nodep->lhsp()->isDouble()) {
            spliceCvtD(nodep->lhsp());
            if (AstNodeUniop* const newp = replaceWithDVersion(nodep)) {
                VL_DANGLING(nodep);
                nodep = newp;  // Process new node instead
                iterateCheckReal(nodep, "LHS", nodep->lhsp(), BOTH);
                nodep->dtypeSetDouble();
                return;
            }
        } else {
            // Note there aren't yet uniops that need version changes
            // So no need to call replaceWithUOrSVersion(nodep, nodep->isSigned())
        }
        if (m_vup->prelim()) nodep->dtypeFrom(nodep->lhsp());
        if (m_vup->final()) {
            AstNodeDType* const expDTypep = m_vup->dtypeOverridep(nodep->dtypep());
            nodep->dtypep(expDTypep);  // Propagate expression type to negation
            AstNodeDType* const subDTypep = expDTypep;
            // Some warning suppressions
            bool lhsWarn = true;
            if (VN_IS(nodep, Negate)) {
                // Warn if user wants extra bit from carry
                if (subDTypep->widthMin() == (nodep->lhsp()->widthMin() + 1)) lhsWarn = false;
            }
            iterateCheck(nodep, "LHS", nodep->lhsp(), CONTEXT, FINAL, subDTypep, EXTEND_EXP,
                         lhsWarn);
        }
    }

    void visit_signed_unsigned(AstNodeUniop* nodep, VSigning rs_out) {
        // CALLER: Signed, Unsigned
        // Width: lhs is self determined width
        // See IEEE-2012 6.24.1:
        //   Width: Returns packed array, of size $bits(expression).
        //   Sign: Output sign is as specified by operation
        //   TODO: Type: Two-state if input is two-state, else four-state
        UASSERT_OBJ(!nodep->op2p(), nodep, "For unary ops only!");
        if (m_vup->prelim()) {
            userIterateAndNext(nodep->lhsp(), WidthVP(SELF, PRELIM).p());
            checkCvtUS(nodep->lhsp());
            const int width = nodep->lhsp()->width();
            AstNodeDType* const expDTypep = nodep->findLogicDType(width, width, rs_out);
            nodep->dtypep(expDTypep);
            AstNodeDType* const subDTypep = expDTypep;
            // The child's width is self determined
            iterateCheck(nodep, "LHS", nodep->lhsp(), SELF, FINAL, subDTypep, EXTEND_EXP);
        }
    }

    void visit_shift(AstNodeBiop* nodep) {
        // CALLER: ShiftL, ShiftR, ShiftRS
        // Widths: Output width from lhs, rhs<33 bits
        // Signed: Output signed iff LHS signed; unary operator
        // See IEEE 2012 11.4.10:
        //   RHS is self-determined. RHS is always treated as unsigned, has no effect on result.
        iterate_shift_prelim(nodep);
        nodep->dtypeChgSigned(nodep->lhsp()->isSigned());
        const AstNodeBiop* const newp = iterate_shift_final(nodep);
        VL_DANGLING(nodep);
        if (newp) {}  // Ununused
    }
    void iterate_shift_prelim(AstNodeBiop* nodep) {
        // Shifts
        // See IEEE-2012 11.4.10 and Table 11-21.
        //   RHS is self-determined. RHS is always treated as unsigned, has no effect on result.
        if (m_vup->prelim()) {
            userIterateAndNext(nodep->lhsp(), WidthVP(SELF, PRELIM).p());
            checkCvtUS(nodep->lhsp());
            iterateCheckSizedSelf(nodep, "RHS", nodep->rhsp(), SELF, BOTH);
            nodep->dtypeFrom(nodep->lhsp());
        }
    }
    AstNodeBiop* iterate_shift_final(AstNodeBiop* nodep) {
        // Nodep maybe edited
        if (m_vup->final()) {
            AstNodeDType* const expDTypep = m_vup->dtypeOverridep(nodep->dtypep());
            AstNodeDType* const subDTypep = expDTypep;
            nodep->dtypeFrom(expDTypep);
            // ShiftRS converts to ShiftR, but not vice-versa
            if (VN_IS(nodep, ShiftRS)) {
                if (AstNodeBiop* const newp = replaceWithUOrSVersion(nodep, nodep->isSigned())) {
                    VL_DANGLING(nodep);
                    nodep = newp;  // Process new node instead
                }
            }
            bool warnOn = true;
            // No warning if "X = 1'b1<<N"; assume user is doing what they want
            if (nodep->lhsp()->isOne() && VN_IS(nodep->backp(), NodeAssign)) warnOn = false;
            iterateCheck(nodep, "LHS", nodep->lhsp(), CONTEXT, FINAL, subDTypep, EXTEND_EXP,
                         warnOn);
            if (nodep->rhsp()->width() > 32) {
                AstConst* const shiftp = VN_CAST(nodep->rhsp(), Const);
                if (shiftp && shiftp->num().mostSetBitP1() <= 32) {
                    // If (number)<<96'h1, then make it into (number)<<32'h1
                    V3Number num(shiftp, 32, 0);
                    num.opAssign(shiftp->num());
                    AstNode* const shiftrhsp = nodep->rhsp();
                    nodep->rhsp()->replaceWith(new AstConst(shiftrhsp->fileline(), num));
                    VL_DO_DANGLING(shiftrhsp->deleteTree(), shiftrhsp);
                }
            }
        }
        return nodep;  // May edit
    }

    void visit_boolmath_and_or(AstNodeBiop* nodep) {
        // CALLER: And, Or, Xor, ...
        // Lint widths: out width = lhs width = rhs width
        // Signed: if lhs & rhs signed
        // IEEE-2012 Table 11-21:
        //    Width: max(LHS, RHS)
        UASSERT_OBJ(nodep->rhsp(), nodep, "For binary ops only!");
        // If errors are off, we need to follow the spec; thus we really need to do the max()
        // because the rhs could be larger, and we need to have proper editing to get the widths
        // to be the same for our operations.
        if (m_vup->prelim()) {  // First stage evaluation
            // Determine expression widths only relying on what's in the subops
            userIterateAndNext(nodep->lhsp(), WidthVP(CONTEXT, PRELIM).p());
            userIterateAndNext(nodep->rhsp(), WidthVP(CONTEXT, PRELIM).p());
            checkCvtUS(nodep->lhsp());
            checkCvtUS(nodep->rhsp());
            const int width = std::max(nodep->lhsp()->width(), nodep->rhsp()->width());
            const int mwidth = std::max(nodep->lhsp()->widthMin(), nodep->rhsp()->widthMin());
            const bool expSigned = (nodep->lhsp()->isSigned() && nodep->rhsp()->isSigned());
            nodep->dtypeChgWidthSigned(width, mwidth, VSigning::fromBool(expSigned));
        }
        if (m_vup->final()) {
            AstNodeDType* const expDTypep = m_vup->dtypeOverridep(nodep->dtypep());
            AstNodeDType* const subDTypep = expDTypep;
            nodep->dtypeFrom(expDTypep);
            // Error report and change sizes for suboperands of this node.
            iterateCheck(nodep, "LHS", nodep->lhsp(), CONTEXT, FINAL, subDTypep, EXTEND_EXP);
            iterateCheck(nodep, "RHS", nodep->rhsp(), CONTEXT, FINAL, subDTypep, EXTEND_EXP);
        }
    }

    void visit_add_sub_replace(AstNodeBiop* nodep, bool real_ok) {
        // CALLER: (real_ok=false) AddS, SubS, ...
        // CALLER: (real_ok=true) Add, Sub, ...
        // Widths: out width = lhs width = rhs width
        // Signed: Replace operator with signed operator, or signed to unsigned
        // Real: Replace operator with real operator
        // IEEE-2012 Table 11-21:
        //    Width: max(LHS, RHS)
        // If errors are off, we need to follow the spec; thus we really need to do the max()
        // because the rhs could be larger, and we need to have proper editing to get the widths
        // to be the same for our operations.
        //
        // if (debug() >= 9) { UINFO(0,"-rus "<<m_vup<<endl); nodep->dumpTree(cout, "-rusin-"); }
        if (m_vup->prelim()) {  // First stage evaluation
            // Determine expression widths only relying on what's in the subops
            userIterateAndNext(nodep->lhsp(), WidthVP(CONTEXT, PRELIM).p());
            userIterateAndNext(nodep->rhsp(), WidthVP(CONTEXT, PRELIM).p());
            if (!real_ok) {
                checkCvtUS(nodep->lhsp());
                checkCvtUS(nodep->rhsp());
            }
            if (nodep->lhsp()->isDouble() || nodep->rhsp()->isDouble()) {
                spliceCvtD(nodep->lhsp());
                spliceCvtD(nodep->rhsp());
                if (AstNodeBiop* const newp = replaceWithDVersion(nodep)) {
                    VL_DANGLING(nodep);
                    nodep = newp;  // Process new node instead
                }
                nodep->dtypeSetDouble();
                iterateCheckReal(nodep, "LHS", nodep->lhsp(), FINAL);
                iterateCheckReal(nodep, "RHS", nodep->rhsp(), FINAL);
                return;
            } else {
                const int width = std::max(nodep->lhsp()->width(), nodep->rhsp()->width());
                const int mwidth = std::max(nodep->lhsp()->widthMin(), nodep->rhsp()->widthMin());
                const bool expSigned = (nodep->lhsp()->isSigned() && nodep->rhsp()->isSigned());
                nodep->dtypeChgWidthSigned(width, mwidth, VSigning::fromBool(expSigned));
            }
        }
        if (m_vup->final()) {
            // Parent's data type was computed using the max(upper, nodep->dtype)
            AstNodeDType* const expDTypep = m_vup->dtypeOverridep(nodep->dtypep());
            AstNodeDType* const subDTypep = expDTypep;
            nodep->dtypeFrom(expDTypep);
            // We don't use LHS && RHS -- unspecified language corner, see t_math_signed5 test
            // bool expSigned = (nodep->lhsp()->isSigned() && nodep->rhsp()->isSigned());
            if (AstNodeBiop* const newp = replaceWithUOrSVersion(nodep, expDTypep->isSigned())) {
                VL_DANGLING(nodep);
                nodep = newp;  // Process new node instead
            }
            // Some warning suppressions
            bool lhsWarn = true;
            bool rhsWarn = true;
            if (VN_IS(nodep, Add) || VN_IS(nodep, Sub)) {
                // Warn if user wants extra bit from carry
                if (subDTypep->widthMin() == (nodep->lhsp()->widthMin() + 1)) lhsWarn = false;
                if (subDTypep->widthMin() == (nodep->rhsp()->widthMin() + 1)) rhsWarn = false;
            } else if (VN_IS(nodep, Mul) || VN_IS(nodep, MulS)) {
                if (subDTypep->widthMin() >= (nodep->lhsp()->widthMin())) lhsWarn = false;
                if (subDTypep->widthMin() >= (nodep->rhsp()->widthMin())) rhsWarn = false;
            }
            // Final call, so make sure children check their sizes
            // Error report and change sizes for suboperands of this node.
            iterateCheck(nodep, "LHS", nodep->lhsp(), CONTEXT, FINAL, subDTypep, EXTEND_EXP,
                         lhsWarn);
            iterateCheck(nodep, "RHS", nodep->rhsp(), CONTEXT, FINAL, subDTypep, EXTEND_EXP,
                         rhsWarn);
        }
        // if (debug() >= 9) nodep->dumpTree(cout, "-rusou-");
    }
    void visit_real_add_sub(AstNodeBiop* nodep) {
        // CALLER: AddD, MulD, ...
        if (m_vup->prelim()) {  // First stage evaluation
            // Note similar steps in visit_add_sub_replace promotion to double
            iterateCheckReal(nodep, "LHS", nodep->lhsp(), BOTH);
            iterateCheckReal(nodep, "RHS", nodep->rhsp(), BOTH);
            nodep->dtypeSetDouble();
        }
    }
    void visit_real_neg_ceil(AstNodeUniop* nodep) {
        // CALLER: Negate, Ceil, Log, ...
        if (m_vup->prelim()) {  // First stage evaluation
            // See alsl visit_negate_not conversion
            iterateCheckReal(nodep, "LHS", nodep->lhsp(), BOTH);
            nodep->dtypeSetDouble();
        }
    }

    //----------------------------------------------------------------------
    // LOWER LEVEL WIDTH METHODS  (none iterate)

    bool widthBad(AstNode* nodep, AstNodeDType* expDTypep) {
        const int expWidth = expDTypep->width();
        int expWidthMin = expDTypep->widthMin();
        UASSERT_OBJ(nodep->dtypep(), nodep,
                    "Under node " << nodep->prettyTypeName()
                                  << " has no dtype?? Missing Visitor func?");
        UASSERT_OBJ(nodep->width() != 0, nodep,
                    "Under node " << nodep->prettyTypeName()
                                  << " has no expected width?? Missing Visitor func?");
        UASSERT_OBJ(expWidth != 0, nodep,
                    "Node " << nodep->prettyTypeName()
                            << " has no expected width?? Missing Visitor func?");
        if (expWidthMin == 0) expWidthMin = expWidth;
        if (nodep->dtypep()->width() == expWidth) return false;
        if (nodep->dtypep()->widthSized() && nodep->width() != expWidthMin) return true;
        if (!nodep->dtypep()->widthSized() && nodep->widthMin() > expWidthMin) return true;
        return false;
    }

    void fixWidthExtend(AstNode* nodep, AstNodeDType* expDTypep, ExtendRule extendRule) {
        // Fix the width mismatch by extending or truncating bits
        // *ONLY* call this from checkWidth()
        // Truncation is rarer, but can occur:  parameter [3:0] FOO = 64'h12312;
        // A(CONSTwide)+B becomes  A(CONSTwidened)+B
        // A(somewide)+B  becomes  A(TRUNC(somewide,width))+B
        //                    or   A(EXTRACT(somewide,width,0))+B
        // Sign extension depends on the type of the *present*
        // node, while the output dtype is the *expected* sign.
        // It is reasonable to have sign extension with unsigned output,
        // for example $unsigned(a)+$signed(b), the SIGNED(B) will be unsigned dtype out
        UINFO(4, "  widthExtend_(r=" << extendRule << ") old: " << nodep << endl);
        if (extendRule == EXTEND_OFF) return;
        AstConst* const constp = VN_CAST(nodep, Const);
        const int expWidth = expDTypep->width();
        if (constp && !constp->num().isNegative()) {
            // Save later constant propagation work, just right-size it.
            V3Number num(nodep, expWidth);
            num.opAssign(constp->num());
            num.isSigned(false);
            AstNode* const newp = new AstConst(nodep->fileline(), num);
            constp->replaceWith(newp);
            VL_DO_DANGLING(pushDeletep(constp), constp);
            VL_DANGLING(nodep);
            nodep = newp;
        } else if (expWidth < nodep->width()) {
            // Trunc - Extract
            VNRelinker linker;
            nodep->unlinkFrBack(&linker);
            AstNode* const newp = new AstSel(nodep->fileline(), nodep, 0, expWidth);
            newp->didWidth(true);  // Don't replace dtype with unsigned
            linker.relink(newp);
            nodep = newp;
        } else {
            // Extend
            VNRelinker linker;
            nodep->unlinkFrBack(&linker);
            bool doSigned = false;
            switch (extendRule) {
            case EXTEND_ZERO: doSigned = false; break;
            case EXTEND_EXP: doSigned = nodep->isSigned() && expDTypep->isSigned(); break;
            case EXTEND_LHS: doSigned = nodep->isSigned(); break;
            default: nodep->v3fatalSrc("bad case");
            }
            AstNode* const newp
                = (doSigned ? static_cast<AstNode*>(new AstExtendS{nodep->fileline(), nodep})
                            : static_cast<AstNode*>(new AstExtend{nodep->fileline(), nodep}));
            linker.relink(newp);
            nodep = newp;
        }
        if (expDTypep->isDouble() && !nodep->isDouble()) {
            // For AstVar init() among others
            // TODO do all to-real and to-integer conversions in this function
            // rather than in callers
            AstNode* const newp = spliceCvtD(nodep);
            nodep = newp;
        }
        nodep->dtypeFrom(expDTypep);
        UINFO(4, "             _new: " << nodep << endl);
    }

    void fixWidthReduce(AstNode* nodep) {
        // Fix the width mismatch by adding a reduction OR operator
        // IF (A(CONSTwide)) becomes  IF (A(CONSTreduced))
        // IF (A(somewide))  becomes  IF (A(REDOR(somewide)))
        // Attempt to fix it quietly
        const int expWidth = 1;
        const int expSigned = false;
        UINFO(4, "  widthReduce_old: " << nodep << endl);
        AstConst* const constp = VN_CAST(nodep, Const);
        if (constp) {
            V3Number num(nodep, expWidth);
            num.opRedOr(constp->num());
            num.isSigned(expSigned);
            AstNode* const newp = new AstConst(nodep->fileline(), num);
            constp->replaceWith(newp);
            VL_DO_DANGLING(constp->deleteTree(), constp);
            VL_DANGLING(nodep);
            nodep = newp;
        } else {
            VNRelinker linker;
            nodep->unlinkFrBack(&linker);
            AstNode* const newp = new AstRedOr(nodep->fileline(), nodep);
            linker.relink(newp);
            nodep = newp;
        }
        nodep->dtypeChgWidthSigned(expWidth, expWidth, VSigning::fromBool(expSigned));
        UINFO(4, "             _new: " << nodep << endl);
    }

    bool fixAutoExtend(AstNode*& nodepr, int expWidth) {
        // For SystemVerilog '0,'1,'x,'z, autoextend and don't warn
        if (AstConst* const constp = VN_CAST(nodepr, Const)) {
            if (constp->num().autoExtend() && !constp->num().sized() && constp->width() == 1) {
                // Make it the proper size.  Careful of proper extension of 0's/1's
                V3Number num(constp, expWidth);
                num.opRepl(constp->num(), expWidth);  // {width{'1}}
                AstNode* const newp = new AstConst(constp->fileline(), num);
                // Spec says always unsigned with proper width
                if (debug() > 4) constp->dumpTree(cout, "  fixAutoExtend_old: ");
                if (debug() > 4) newp->dumpTree(cout, "               _new: ");
                constp->replaceWith(newp);
                VL_DO_DANGLING(constp->deleteTree(), constp);
                // Tell caller the new constp, and that we changed it.
                nodepr = newp;
                return true;
            }
            // X/Z also upper bit extend.  In pre-SV only to 32-bits, SV forever.
            else if (!constp->num().sized()
                     // Make it the proper size.  Careful of proper extension of 0's/1's
                     && expWidth > 32 && constp->num().isMsbXZ()) {
                constp->v3warn(WIDTH, "Unsized constant being X/Z extended to "
                                          << expWidth << " bits: " << constp->prettyName());
                V3Number num(constp, expWidth);
                num.opExtendXZ(constp->num(), constp->width());
                AstNode* const newp = new AstConst(constp->fileline(), num);
                // Spec says always unsigned with proper width
                if (debug() > 4) constp->dumpTree(cout, "  fixUnszExtend_old: ");
                if (debug() > 4) newp->dumpTree(cout, "               _new: ");
                constp->replaceWith(newp);
                VL_DO_DANGLING(constp->deleteTree(), constp);
                // Tell caller the new constp, and that we changed it.
                nodepr = newp;
                return true;
            }
        }
        return false;  // No change
    }

    static bool similarDTypeRecurse(AstNodeDType* node1p, AstNodeDType* node2p) {
        return node1p->skipRefp()->similarDType(node2p->skipRefp());
    }
    void iterateCheckFileDesc(AstNode* nodep, AstNode* underp, Stage stage) {
        UASSERT_OBJ(stage == BOTH, nodep, "Bad call");
        // underp may change as a result of replacement
        underp = userIterateSubtreeReturnEdits(underp, WidthVP(SELF, PRELIM).p());
        AstNodeDType* const expDTypep = underp->findUInt32DType();
        underp
            = iterateCheck(nodep, "file_descriptor", underp, SELF, FINAL, expDTypep, EXTEND_EXP);
        if (underp) {}  // cppcheck
    }
    void iterateCheckSigned32(AstNode* nodep, const char* side, AstNode* underp, Stage stage) {
        // Coerce child to signed32 if not already. Child is self-determined
        // underp may change as a result of replacement
        if (stage & PRELIM) {
            underp = userIterateSubtreeReturnEdits(underp, WidthVP(SELF, PRELIM).p());
        }
        if (stage & FINAL) {
            AstNodeDType* const expDTypep = nodep->findSigned32DType();
            underp = iterateCheck(nodep, side, underp, SELF, FINAL, expDTypep, EXTEND_EXP);
        }
        if (underp) {}  // cppcheck
    }
    void iterateCheckReal(AstNode* nodep, const char* side, AstNode* underp, Stage stage) {
        // Coerce child to real if not already. Child is self-determined
        // e.g. nodep=ADDD, underp=ADD in ADDD(ADD(a,b), real-CONST)
        // Don't need separate PRELIM and FINAL(double) calls;
        // as if resolves to double, the BOTH correctly resolved double,
        // otherwise self-determined was correct
        // underp may change as a result of replacement
        if (stage & PRELIM) {
            underp = userIterateSubtreeReturnEdits(underp, WidthVP(SELF, PRELIM).p());
        }
        if (stage & FINAL) {
            AstNodeDType* const expDTypep = nodep->findDoubleDType();
            underp = iterateCheck(nodep, side, underp, SELF, FINAL, expDTypep, EXTEND_EXP);
        }
        if (underp) {}  // cppcheck
    }
    void iterateCheckString(AstNode* nodep, const char* side, AstNode* underp, Stage stage) {
        if (stage & PRELIM) {
            underp = userIterateSubtreeReturnEdits(underp, WidthVP(SELF, PRELIM).p());
        }
        if (stage & FINAL) {
            AstNodeDType* const expDTypep = nodep->findStringDType();
            underp = iterateCheck(nodep, side, underp, SELF, FINAL, expDTypep, EXTEND_EXP);
        }
        if (underp) {}  // cppcheck
    }
    void iterateCheckTyped(AstNode* nodep, const char* side, AstNode* underp,
                           AstNodeDType* expDTypep, Stage stage) {
        if (stage & PRELIM) {
            underp = userIterateSubtreeReturnEdits(underp, WidthVP(expDTypep, PRELIM).p());
        }
        if (stage & FINAL) {
            underp = iterateCheck(nodep, side, underp, SELF, FINAL, expDTypep, EXTEND_EXP);
        }
        if (underp) {}  // cppcheck
    }
    void iterateCheckSizedSelf(AstNode* nodep, const char* side, AstNode* underp, Determ determ,
                               Stage stage) {
        // Coerce child to any sized-number data type; child is self-determined
        // i.e. isolated from expected type.
        // e.g. nodep=CONCAT, underp=lhs in CONCAT(lhs,rhs)
        UASSERT_OBJ(determ == SELF, nodep, "Bad call");
        UASSERT_OBJ(stage == FINAL || stage == BOTH, nodep, "Bad call");
        // underp may change as a result of replacement
        if (stage & PRELIM) {
            underp = userIterateSubtreeReturnEdits(underp, WidthVP(SELF, PRELIM).p());
        }
        underp = checkCvtUS(underp);
        AstNodeDType* const expDTypep = underp->dtypep();
        underp = iterateCheck(nodep, side, underp, SELF, FINAL, expDTypep, EXTEND_EXP);
        if (underp) {}  // cppcheck
    }
    void iterateCheckAssign(AstNode* nodep, const char* side, AstNode* rhsp, Stage stage,
                            AstNodeDType* lhsDTypep) {
        // Check using assignment-like context rules
        // if (debug()) nodep->dumpTree(cout, "-checkass: ");
        UASSERT_OBJ(stage == FINAL, nodep, "Bad width call");
        // We iterate and size the RHS based on the result of RHS evaluation
        const bool lhsStream
            = (VN_IS(nodep, NodeAssign) && VN_IS(VN_AS(nodep, NodeAssign)->lhsp(), NodeStream));
        rhsp = iterateCheck(nodep, side, rhsp, ASSIGN, FINAL, lhsDTypep,
                            lhsStream ? EXTEND_OFF : EXTEND_LHS);
        // if (debug()) nodep->dumpTree(cout, "-checkout: ");
        if (rhsp) {}  // cppcheck
    }

    void iterateCheckBool(AstNode* nodep, const char* side, AstNode* underp, Stage stage) {
        UASSERT_OBJ(stage == BOTH, nodep,
                    "Bad call");  // Booleans always self-determined so do BOTH at once
        // Underp is used in a self-determined but boolean context, reduce a
        // multibit number to one bit
        // stage is always BOTH so not passed as argument
        // underp may change as a result of replacement
        UASSERT_OBJ(underp, nodep, "Node has no type");
        underp = userIterateSubtreeReturnEdits(underp, WidthVP(SELF, BOTH).p());
        UASSERT_OBJ(underp && underp->dtypep(), nodep,
                    "Node has no type");  // Perhaps forgot to do a prelim visit on it?
        //
        // For DOUBLE under a logical op, add implied test against zero, never a warning
        AstNodeDType* const underVDTypep = underp ? underp->dtypep()->skipRefp() : nullptr;
        if (underp && underVDTypep->isDouble()) {
            UINFO(6, "   spliceCvtCmpD0: " << underp << endl);
            VNRelinker linker;
            underp->unlinkFrBack(&linker);
            AstNode* const newp
                = new AstNeqD(nodep->fileline(), underp,
                              new AstConst(nodep->fileline(), AstConst::RealDouble(), 0.0));
            linker.relink(newp);
        } else if (VN_IS(underVDTypep, ClassRefDType)
                   || (VN_IS(underVDTypep, BasicDType)
                       && VN_AS(underVDTypep, BasicDType)->keyword() == VBasicDTypeKwd::CHANDLE)) {
            // Allow warning-free "if (handle)"
            VL_DO_DANGLING(fixWidthReduce(underp), underp);  // Changed
        } else if (!underVDTypep->basicp()) {
            nodep->v3error("Logical operator " << nodep->prettyTypeName()
                                               << " expects a non-complex data type on the "
                                               << side << ".");
            underp->replaceWith(new AstConst(nodep->fileline(), AstConst::BitFalse()));
            VL_DO_DANGLING(pushDeletep(underp), underp);
        } else {
            const bool bad = widthBad(underp, nodep->findBitDType());
            if (bad) {
                {  // if (warnOn), but not needed here
                    if (debug() > 4) nodep->backp()->dumpTree(cout, "  back: ");
                    nodep->v3warn(WIDTH, "Logical operator "
                                             << nodep->prettyTypeName() << " expects 1 bit on the "
                                             << side << ", but " << side << "'s "
                                             << underp->prettyTypeName() << " generates "
                                             << underp->width()
                                             << (underp->width() != underp->widthMin()
                                                     ? " or " + cvtToStr(underp->widthMin())
                                                     : "")
                                             << " bits.");
                }
                VL_DO_DANGLING(fixWidthReduce(underp), underp);  // Changed
            }
        }
    }

    AstNode* iterateCheck(AstNode* nodep, const char* side, AstNode* underp, Determ determ,
                          Stage stage, AstNodeDType* expDTypep, ExtendRule extendRule,
                          bool warnOn = true) {
        // Perform data type check on underp, which is underneath nodep used for error reporting
        // Returns the new underp
        // Conversion to/from doubles and integers are before iterating.
        UASSERT_OBJ(stage == FINAL, nodep, "Bad state to iterateCheck");
        UASSERT_OBJ(underp && underp->dtypep(), nodep,
                    "Node has no type");  // Perhaps forgot to do a prelim visit on it?
        if (VN_IS(underp, NodeDType)) {  // Note the node itself, not node's data type
            // Must be near top of these checks as underp->dtypep() will look normal
            underp->v3error(ucfirst(nodep->prettyOperatorName())
                            << " expected non-datatype " << side << " but '" << underp->name()
                            << "' is a datatype.");
        } else if (expDTypep == underp->dtypep()) {  // Perfect
            underp = userIterateSubtreeReturnEdits(underp, WidthVP(expDTypep, FINAL).p());
        } else if (expDTypep->isDouble() && underp->isDouble()) {  // Also good
            underp = userIterateSubtreeReturnEdits(underp, WidthVP(expDTypep, FINAL).p());
        } else if (expDTypep->isDouble() && !underp->isDouble()) {
            AstNode* const oldp
                = underp;  // Need FINAL on children; otherwise splice would block it
            underp = spliceCvtD(underp);
            underp = userIterateSubtreeReturnEdits(oldp, WidthVP(SELF, FINAL).p());
        } else if (!expDTypep->isDouble() && underp->isDouble()) {
            AstNode* const oldp
                = underp;  // Need FINAL on children; otherwise splice would block it
            underp = spliceCvtS(underp, true, expDTypep->width());  // Round RHS
            underp = userIterateSubtreeReturnEdits(oldp, WidthVP(SELF, FINAL).p());
        } else if (expDTypep->isString() && !underp->dtypep()->isString()) {
            AstNode* const oldp
                = underp;  // Need FINAL on children; otherwise splice would block it
            underp = spliceCvtString(underp);
            underp = userIterateSubtreeReturnEdits(oldp, WidthVP(SELF, FINAL).p());
        } else {
            const AstBasicDType* const expBasicp = expDTypep->basicp();
            const AstBasicDType* const underBasicp = underp->dtypep()->basicp();
            if (expBasicp && underBasicp) {
                AstNodeDType* subDTypep = expDTypep;
                // We then iterate FINAL before width fixes, as if the under-operation
                // is e.g. an ADD, the ADD will auto-adjust to the proper data type
                // or if another operation e.g. ATOI will not.
                if (determ == SELF) {
                    underp = userIterateSubtreeReturnEdits(underp, WidthVP(SELF, FINAL).p());
                } else if (determ == ASSIGN) {
                    // IEEE: Signedness is solely determined by the RHS
                    // (underp), not by the LHS (expDTypep)
                    if (underp->isSigned() != subDTypep->isSigned()
                        || underp->width() != subDTypep->width()) {
                        subDTypep = nodep->findLogicDType(
                            std::max(subDTypep->width(), underp->width()),
                            std::max(subDTypep->widthMin(), underp->widthMin()),
                            VSigning::fromBool(underp->isSigned()));
                        UINFO(9, "Assignment of opposite-signed RHS to LHS: " << nodep << endl);
                    }
                    underp = userIterateSubtreeReturnEdits(underp, WidthVP(subDTypep, FINAL).p());
                } else {
                    underp = userIterateSubtreeReturnEdits(underp, WidthVP(subDTypep, FINAL).p());
                }
                // Note the check uses the expected size, not the child's subDTypep as we want the
                // child node's width to end up correct for the assignment (etc)
                widthCheckSized(nodep, side, underp, expDTypep, extendRule, warnOn);
            } else if (!VN_IS(expDTypep, IfaceRefDType)
                       && VN_IS(underp->dtypep(), IfaceRefDType)) {
                underp->v3error(ucfirst(nodep->prettyOperatorName())
                                << " expected non-interface on " << side << " but '"
                                << underp->name() << "' is an interface.");
            } else {
                // Hope it just works out (perhaps a cast will deal with it)
                underp = userIterateSubtreeReturnEdits(underp, WidthVP(expDTypep, FINAL).p());
            }
        }
        return underp;
    }

    void widthCheckSized(AstNode* nodep, const char* side,
                         AstNode* underp,  // Node to be checked or have typecast added in front of
                         AstNodeDType* expDTypep, ExtendRule extendRule, bool warnOn = true) {
        // Issue warnings on sized number width mismatches, then do appropriate size extension
        // Generally iterateCheck is what is wanted instead of this
        // UINFO(9,"wchk "<<side<<endl<<"  "<<nodep<<endl<<"  "<<underp<<endl<<"  e="<<expDTypep<<"
        // i"<<warnOn<<endl);
        const AstBasicDType* const expBasicp = expDTypep->basicp();
        const AstBasicDType* const underBasicp = underp->dtypep()->basicp();
        if (expDTypep == underp->dtypep()) {
            return;  // Same type must match
        } else if (!expBasicp || expBasicp->isDouble() || !underBasicp
                   || underBasicp->isDouble()) {
            // This is perhaps a v3fatalSrc as we should have checked the types
            // before calling widthCheck, but we may have missed a non-sized
            // check in earlier code, so might as well assume it is the users'
            // fault.
            nodep->v3error(ucfirst(nodep->prettyOperatorName())
                           << " expected non-complex non-double " << side << " in width check");
#if VL_DEBUG
            nodep->v3fatalSrc("widthCheckSized should not be called on doubles/complex types");
#endif
            return;
        } else {
            const int expWidth = expDTypep->width();
            int expWidthMin = expDTypep->widthMin();
            if (expWidthMin == 0) expWidthMin = expWidth;
            const bool bad = widthBad(underp, expDTypep);
            if ((bad || underp->width() != expWidth) && fixAutoExtend(underp /*ref*/, expWidth)) {
                underp = nullptr;  // Changes underp
                return;
            }
            if (VN_IS(underp, Const) && VN_AS(underp, Const)->num().isFromString()
                && expWidth > underp->width()
                && (((expWidth - underp->width()) % 8) == 0)) {  // At least it's character sized
                // reg [31:0] == "foo" we'll consider probably fine.
                // Maybe this should be a special warning?  Not for now.
                warnOn = false;
            }
            if ((VN_IS(nodep, Add) && underp->width() == 1 && underp->isOne())
                || (VN_IS(nodep, Sub) && underp->width() == 1 && underp->isOne()
                    && 0 == strcmp(side, "RHS"))) {
                // "foo + 1'b1", or "foo - 1'b1" are very common, people assume
                // they extend correctly
                warnOn = false;
            }
            if (bad && warnOn) {
                if (debug() > 4) nodep->backp()->dumpTree(cout, "  back: ");
                nodep->v3warn(
                    WIDTH, ucfirst(nodep->prettyOperatorName())
                               << " expects " << expWidth
                               << (expWidth != expWidthMin ? " or " + cvtToStr(expWidthMin) : "")
                               << " bits on the " << side << ", but " << side << "'s "
                               << underp->prettyTypeName() << " generates " << underp->width()
                               << (underp->width() != underp->widthMin()
                                       ? " or " + cvtToStr(underp->widthMin())
                                       : "")
                               << " bits.");
            }
            if (bad || underp->width() != expWidth) {
                // If we're in an NodeAssign, don't truncate the RHS if the LHS is
                // a NodeStream. The streaming operator changes the rules regarding
                // which bits to truncate.
                const AstNodeAssign* assignp = VN_CAST(nodep, NodeAssign);
                const AstPin* pinp = VN_CAST(nodep, Pin);
                if (assignp && VN_IS(assignp->lhsp(), NodeStream)) {
                } else if (pinp && pinp->modVarp()->direction() != VDirection::INPUT) {
                    // V3Inst::pinReconnectSimple must deal
                    UINFO(5, "pinInSizeMismatch: " << pinp);
                } else {
                    VL_DO_DANGLING(fixWidthExtend(underp, expDTypep, extendRule), underp);
                }
            }
        }
    }

    //----------------------------------------------------------------------
    // SIGNED/DOUBLE METHODS

    AstNode* checkCvtUS(AstNode* nodep) {
        if (nodep && nodep->isDouble()) {
            nodep->v3error("Expected integral (non-" << nodep->dtypep()->prettyDTypeName()
                                                     << ") input to "
                                                     << nodep->backp()->prettyTypeName());
            nodep = spliceCvtS(nodep, true, 32);
        }
        return nodep;
    }

    AstNode* spliceCvtD(AstNode* nodep) {
        // For integer used in REAL context, convert to real
        // We don't warn here, "2.0 * 2" is common and reasonable
        if (nodep && !nodep->dtypep()->skipRefp()->isDouble()) {
            UINFO(6, "   spliceCvtD: " << nodep << endl);
            VNRelinker linker;
            nodep->unlinkFrBack(&linker);
            AstNode* newp;
            if (nodep->dtypep()->skipRefp()->isSigned()) {
                newp = new AstISToRD(nodep->fileline(), nodep);
            } else {
                newp = new AstIToRD(nodep->fileline(), nodep);
            }
            linker.relink(newp);
            return newp;
        } else {
            return nodep;
        }
    }
    AstNode* spliceCvtS(AstNode* nodep, bool warnOn, int width) {
        // IEEE-2012 11.8.1: Signed: Type coercion creates signed
        // 11.8.2: Argument to convert is self-determined
        if (nodep && nodep->dtypep()->skipRefp()->isDouble()) {
            UINFO(6, "   spliceCvtS: " << nodep << endl);
            VNRelinker linker;
            nodep->unlinkFrBack(&linker);
            if (const AstConst* const constp = VN_CAST(nodep, Const)) {
                // We convert to/from int32_t rather than use floor() as want to make sure is
                // representable in integer's number of bits
                if (constp->isDouble()
                    && v3EpsilonEqual(
                        constp->num().toDouble(),
                        static_cast<double>(static_cast<int32_t>(constp->num().toDouble())))) {
                    warnOn = false;
                }
            }
            if (warnOn) nodep->v3warn(REALCVT, "Implicit conversion of real to integer");
            AstNode* const newp = new AstRToIRoundS(nodep->fileline(), nodep);
            linker.relink(newp);
            newp->dtypeSetBitSized(width, VSigning::SIGNED);
            return newp;
        } else {
            return nodep;
        }
    }
    AstNode* spliceCvtString(AstNode* nodep) {
        // IEEE-2012 11.8.1: Signed: Type coercion creates signed
        // 11.8.2: Argument to convert is self-determined
        if (nodep && !(nodep->dtypep()->basicp() && nodep->dtypep()->basicp()->isString())) {
            UINFO(6, "   spliceCvtString: " << nodep << endl);
            VNRelinker linker;
            nodep->unlinkFrBack(&linker);
            AstNode* const newp = new AstCvtPackString(nodep->fileline(), nodep);
            linker.relink(newp);
            return newp;
        } else {
            return nodep;
        }
    }
    AstNodeBiop* replaceWithUOrSVersion(AstNodeBiop* nodep, bool signedFlavorNeeded) {
        // Given a signed/unsigned node type, create the opposite type
        // Return new node or nullptr if nothing
        if (signedFlavorNeeded == nodep->signedFlavor()) return nullptr;
        if (!nodep->dtypep()) nodep->dtypeFrom(nodep->lhsp());
        // To simplify callers, some node types don't need to change
        switch (nodep->type()) {
        case VNType::atEq: nodep->dtypeChgSigned(signedFlavorNeeded); return nullptr;
        case VNType::atNeq: nodep->dtypeChgSigned(signedFlavorNeeded); return nullptr;
        case VNType::atEqCase: nodep->dtypeChgSigned(signedFlavorNeeded); return nullptr;
        case VNType::atNeqCase: nodep->dtypeChgSigned(signedFlavorNeeded); return nullptr;
        case VNType::atEqWild: nodep->dtypeChgSigned(signedFlavorNeeded); return nullptr;
        case VNType::atNeqWild: nodep->dtypeChgSigned(signedFlavorNeeded); return nullptr;
        case VNType::atAdd: nodep->dtypeChgSigned(signedFlavorNeeded); return nullptr;
        case VNType::atSub: nodep->dtypeChgSigned(signedFlavorNeeded); return nullptr;
        case VNType::atShiftL: nodep->dtypeChgSigned(signedFlavorNeeded); return nullptr;
        default: break;
        }
        FileLine* const fl = nodep->fileline();
        AstNode* const lhsp = nodep->lhsp()->unlinkFrBack();
        AstNode* const rhsp = nodep->rhsp()->unlinkFrBack();
        AstNodeBiop* newp = nullptr;
        switch (nodep->type()) {
        case VNType::atGt: newp = new AstGtS(fl, lhsp, rhsp); break;
        case VNType::atGtS: newp = new AstGt(fl, lhsp, rhsp); break;
        case VNType::atGte: newp = new AstGteS(fl, lhsp, rhsp); break;
        case VNType::atGteS: newp = new AstGte(fl, lhsp, rhsp); break;
        case VNType::atLt: newp = new AstLtS(fl, lhsp, rhsp); break;
        case VNType::atLtS: newp = new AstLt(fl, lhsp, rhsp); break;
        case VNType::atLte: newp = new AstLteS(fl, lhsp, rhsp); break;
        case VNType::atLteS: newp = new AstLte(fl, lhsp, rhsp); break;
        case VNType::atDiv: newp = new AstDivS(fl, lhsp, rhsp); break;
        case VNType::atDivS: newp = new AstDiv(fl, lhsp, rhsp); break;
        case VNType::atModDiv: newp = new AstModDivS(fl, lhsp, rhsp); break;
        case VNType::atModDivS: newp = new AstModDiv(fl, lhsp, rhsp); break;
        case VNType::atMul: newp = new AstMulS(fl, lhsp, rhsp); break;
        case VNType::atMulS: newp = new AstMul(fl, lhsp, rhsp); break;
        case VNType::atShiftR: newp = new AstShiftRS(fl, lhsp, rhsp); break;
        case VNType::atShiftRS: newp = new AstShiftR(fl, lhsp, rhsp); break;
        default:  // LCOV_EXCL_LINE
            nodep->v3fatalSrc("Node needs sign change, but bad case: " << nodep);
            break;
        }
        UINFO(6, "   ReplaceWithUOrSVersion: " << nodep << " w/ " << newp << endl);
        nodep->replaceWith(newp);
        newp->dtypeFrom(nodep);
        VL_DO_DANGLING(pushDeletep(nodep), nodep);
        return newp;
    }
    AstNodeBiop* replaceWithDVersion(AstNodeBiop* nodep) {
        // Given a signed/unsigned node type, create the opposite type
        // Return new node or nullptr if nothing
        if (nodep->doubleFlavor()) return nullptr;
        FileLine* const fl = nodep->fileline();
        AstNode* const lhsp = nodep->lhsp()->unlinkFrBack();
        AstNode* const rhsp = nodep->rhsp()->unlinkFrBack();
        AstNodeBiop* newp = nullptr;
        // No width change on output;...                // All below have bool or double outputs
        switch (nodep->type()) {
        case VNType::atAdd: newp = new AstAddD(fl, lhsp, rhsp); break;
        case VNType::atSub: newp = new AstSubD(fl, lhsp, rhsp); break;
        case VNType::atPow: newp = new AstPowD(fl, lhsp, rhsp); break;
        case VNType::atEq:
        case VNType::atEqCase: newp = new AstEqD(fl, lhsp, rhsp); break;
        case VNType::atNeq:
        case VNType::atNeqCase: newp = new AstNeqD(fl, lhsp, rhsp); break;
        case VNType::atGt:
        case VNType::atGtS: newp = new AstGtD(fl, lhsp, rhsp); break;
        case VNType::atGte:
        case VNType::atGteS: newp = new AstGteD(fl, lhsp, rhsp); break;
        case VNType::atLt:
        case VNType::atLtS: newp = new AstLtD(fl, lhsp, rhsp); break;
        case VNType::atLte:
        case VNType::atLteS: newp = new AstLteD(fl, lhsp, rhsp); break;
        case VNType::atDiv:
        case VNType::atDivS: newp = new AstDivD(fl, lhsp, rhsp); break;
        case VNType::atMul:
        case VNType::atMulS: newp = new AstMulD(fl, lhsp, rhsp); break;
        default:  // LCOV_EXCL_LINE
            nodep->v3fatalSrc("Node needs conversion to double, but bad case: " << nodep);
            break;
        }
        UINFO(6, "   ReplaceWithDVersion: " << nodep << " w/ " << newp << endl);
        nodep->replaceWith(newp);
        // No width change; the default created type (bool or double) is correct
        VL_DO_DANGLING(pushDeletep(nodep), nodep);
        return newp;
    }
    AstNodeBiop* replaceWithNVersion(AstNodeBiop* nodep) {
        // Given a signed/unsigned node type, replace with string version
        // Return new node or nullptr if nothing
        if (nodep->stringFlavor()) return nullptr;
        FileLine* const fl = nodep->fileline();
        AstNode* const lhsp = nodep->lhsp()->unlinkFrBack();
        AstNode* const rhsp = nodep->rhsp()->unlinkFrBack();
        AstNodeBiop* newp = nullptr;
        // No width change on output;...                // All below have bool or double outputs
        switch (nodep->type()) {
        case VNType::atEq:
        case VNType::atEqCase: newp = new AstEqN(fl, lhsp, rhsp); break;
        case VNType::atNeq:
        case VNType::atNeqCase: newp = new AstNeqN(fl, lhsp, rhsp); break;
        case VNType::atGt:
        case VNType::atGtS: newp = new AstGtN(fl, lhsp, rhsp); break;
        case VNType::atGte:
        case VNType::atGteS: newp = new AstGteN(fl, lhsp, rhsp); break;
        case VNType::atLt:
        case VNType::atLtS: newp = new AstLtN(fl, lhsp, rhsp); break;
        case VNType::atLte:
        case VNType::atLteS: newp = new AstLteN(fl, lhsp, rhsp); break;
        default:  // LCOV_EXCL_LINE
            nodep->v3fatalSrc("Node needs conversion to string, but bad case: " << nodep);
            break;
        }
        UINFO(6, "   ReplaceWithNVersion: " << nodep << " w/ " << newp << endl);
        nodep->replaceWith(newp);
        // No width change; the default created type (bool or string) is correct
        VL_DO_DANGLING(pushDeletep(nodep), nodep);
        return newp;
    }
    AstNodeUniop* replaceWithDVersion(AstNodeUniop* nodep) {
        // Given a signed/unsigned node type, create the opposite type
        // Return new node or nullptr if nothing
        if (nodep->doubleFlavor()) return nullptr;
        FileLine* const fl = nodep->fileline();
        AstNode* const lhsp = nodep->lhsp()->unlinkFrBack();
        AstNodeUniop* newp = nullptr;
        switch (nodep->type()) {
        case VNType::atNegate: newp = new AstNegateD(fl, lhsp); break;
        default:  // LCOV_EXCL_LINE
            nodep->v3fatalSrc("Node needs conversion to double, but bad case: " << nodep);
            break;
        }
        UINFO(6, "   ReplaceWithDVersion: " << nodep << " w/ " << newp << endl);
        nodep->replaceWith(newp);
        newp->dtypeFrom(nodep);
        VL_DO_DANGLING(pushDeletep(nodep), nodep);
        return newp;
    }

    //----------------------------------------------------------------------
    // METHODS - strings

    void replaceWithSFormat(AstMethodCall* nodep, const string& format) {
        // For string.itoa and similar, replace with SFormatF
        const AstArg* argp = VN_CAST(nodep->pinsp(), Arg);
        if (!argp) {
            nodep->v3error("Argument needed for string." + nodep->prettyName() + " method");
            return;
        }
        AstNodeVarRef* const fromp = VN_AS(nodep->fromp()->unlinkFrBack(), VarRef);
        AstNode* const newp = new AstAssign(
            nodep->fileline(), fromp,
            new AstSFormatF(nodep->fileline(), format, false, argp->exprp()->unlinkFrBack()));
        fromp->access(VAccess::WRITE);
        nodep->replaceWith(newp);
        VL_DO_DANGLING(pushDeletep(nodep), nodep);
    }

    //----------------------------------------------------------------------
    // METHODS - data types

    AstNodeDType* iterateEditMoveDTypep(AstNode* parentp, AstNodeDType* dtnodep) {
        UASSERT_OBJ(dtnodep, parentp, "Caller should check for nullptr before computing dtype");
        // Iterate into a data type to resolve that type.
        // The data type may either:
        // 1. Be a child (typically getChildDTypep() returns it)
        //    DTypes at parse time get added as these to some node types
        //    such as AstVars.
        //    This function will move it to global scope (that is #2
        //    will now apply).
        // 2. Be under the Netlist and pointed to by an Ast member variable
        //    (typically refDTypep() or dtypep() returns it)
        //    so removing/changing a variable won't lose the dtype

        // Case #1 above applies?
        const bool child1 = (parentp->getChildDTypep() == dtnodep);
        const bool child2 = (parentp->getChild2DTypep() == dtnodep);
        if (child1 || child2) {
            UINFO(9, "iterateEditMoveDTypep child iterating " << dtnodep << endl);
            // Iterate, this might edit the dtypes which means dtnodep now lost
            VL_DO_DANGLING(userIterate(dtnodep, nullptr), dtnodep);
            // Figure out the new dtnodep, remained a child of parent so find it there
            dtnodep = child1 ? parentp->getChildDTypep() : parentp->getChild2DTypep();
            UASSERT_OBJ(dtnodep, parentp, "iterateEditMoveDTypep lost pointer to child");
            UASSERT_OBJ(dtnodep->didWidth(), parentp,
                        "iterateEditMoveDTypep didn't get width resolution of "
                            << dtnodep->prettyTypeName());
            // Move to under netlist
            UINFO(9, "iterateEditMoveDTypep child moving " << dtnodep << endl);
            dtnodep->unlinkFrBack();
            v3Global.rootp()->typeTablep()->addTypesp(dtnodep);
        }
        if (!dtnodep->didWidth()) {
            UINFO(9, "iterateEditMoveDTypep pointer iterating " << dtnodep << endl);
            // See notes in visit(AstBracketArrayDType*)
            UASSERT_OBJ(!VN_IS(dtnodep, BracketArrayDType), parentp,
                        "Brackets should have been iterated as children");
            userIterate(dtnodep, nullptr);
            UASSERT_OBJ(dtnodep->didWidth(), parentp,
                        "iterateEditMoveDTypep didn't get width resolution");
        }
        return dtnodep;
    }

    AstConst* dimensionValue(FileLine* fileline, AstNodeDType* nodep, VAttrType attrType,
                             int dim) {
        // Return the dimension value for the specified attribute and constant dimension
        AstNodeDType* dtypep = nodep->skipRefp();
        VNumRange declRange;  // ranged() set false
        for (int i = 1; i <= dim; ++i) {
            // UINFO(9, "   dim at "<<dim<<"  "<<dtypep<<endl);
            declRange = VNumRange();  // ranged() set false
            if (const AstNodeArrayDType* const adtypep = VN_CAST(dtypep, NodeArrayDType)) {
                declRange = adtypep->declRange();
                if (i < dim) dtypep = adtypep->subDTypep()->skipRefp();
                continue;
            } else if (const AstNodeUOrStructDType* const adtypep
                       = VN_CAST(dtypep, NodeUOrStructDType)) {
                declRange = adtypep->declRange();
                break;  // Sub elements don't look like arrays and can't iterate into
            } else if (const AstBasicDType* const adtypep = VN_CAST(dtypep, BasicDType)) {
                if (adtypep->isRanged()) declRange = adtypep->declRange();
                break;
            }
            break;  // LCOV_EXCL_LINE
        }
        AstConst* valp = nullptr;  // If nullptr, construct from val
        int val = 0;
        switch (attrType) {
        case VAttrType::DIM_BITS: {
            int bits = 1;
            while (dtypep) {
                // UINFO(9, "   bits at "<<bits<<"  "<<dtypep<<endl);
                if (const AstNodeArrayDType* const adtypep = VN_CAST(dtypep, NodeArrayDType)) {
                    bits *= adtypep->declRange().elements();
                    dtypep = adtypep->subDTypep()->skipRefp();
                    continue;
                } else if (const AstNodeUOrStructDType* const adtypep
                           = VN_CAST(dtypep, NodeUOrStructDType)) {
                    bits *= adtypep->width();
                    break;
                } else if (const AstBasicDType* const adtypep = VN_CAST(dtypep, BasicDType)) {
                    bits *= adtypep->width();
                    break;
                }
                break;
            }
            if (dim == 0) {
                val = 0;
            } else if (dim == 1 && !declRange.ranged()
                       && bits == 1) {  // $bits should be sane for non-arrays
                val = nodep->width();
            } else {
                val = bits;
            }
            break;  // LCOV_EXCL_LINE
        }
        case VAttrType::DIM_HIGH: val = !declRange.ranged() ? 0 : declRange.hi(); break;
        case VAttrType::DIM_LEFT: val = !declRange.ranged() ? 0 : declRange.left(); break;
        case VAttrType::DIM_LOW: val = !declRange.ranged() ? 0 : declRange.lo(); break;
        case VAttrType::DIM_RIGHT: val = !declRange.ranged() ? 0 : declRange.right(); break;
        case VAttrType::DIM_INCREMENT:
            val = (declRange.ranged() && declRange.littleEndian()) ? -1 : 1;
            break;
        case VAttrType::DIM_SIZE: val = !declRange.ranged() ? 0 : declRange.elements(); break;
        default: nodep->v3fatalSrc("Missing DIM ATTR type case"); break;
        }
        if (!valp) valp = new AstConst(fileline, AstConst::Signed32(), val);
        UINFO(9, " $dimension " << attrType.ascii() << "(" << cvtToHex(dtypep) << "," << dim
                                << ")=" << valp << endl);
        return valp;
    }
    AstVar* dimensionVarp(AstNodeDType* nodep, VAttrType attrType, uint32_t msbdim) {
        // Return a variable table which has specified dimension properties for this variable
        const auto pos = m_tableMap.find(std::make_pair(nodep, attrType));
        if (pos != m_tableMap.end()) return pos->second;
        AstNodeArrayDType* const vardtypep
            = new AstUnpackArrayDType(nodep->fileline(), nodep->findSigned32DType(),
                                      new AstRange(nodep->fileline(), msbdim, 0));
        AstInitArray* const initp = new AstInitArray(nodep->fileline(), vardtypep, nullptr);
        v3Global.rootp()->typeTablep()->addTypesp(vardtypep);
        AstVar* const varp = new AstVar(nodep->fileline(), VVarType::MODULETEMP,
                                        "__Vdimtab_" + VString::downcase(attrType.ascii())
                                            + cvtToStr(m_dtTables++),
                                        vardtypep);
        varp->isConst(true);
        varp->isStatic(true);
        varp->valuep(initp);
        // Add to root, as don't know module we are in, and aids later structure sharing
        v3Global.rootp()->dollarUnitPkgAddp()->addStmtp(varp);
        // Element 0 is a non-index and has speced values
        initp->addValuep(dimensionValue(nodep->fileline(), nodep, attrType, 0));
        for (unsigned i = 1; i < msbdim + 1; ++i) {
            initp->addValuep(dimensionValue(nodep->fileline(), nodep, attrType, i));
        }
        userIterate(varp, nullptr);  // May have already done $unit so must do this var
        m_tableMap.emplace(std::make_pair(nodep, attrType), varp);
        return varp;
    }
    uint64_t enumMaxValue(const AstNode* errNodep, const AstEnumDType* adtypep) {
        // Most enums unless overridden are 32 bits, so we size array
        // based on max enum value used.
        // Ideally we would have a fast algorithm when a number is
        // of small width and complete and so can use an array, and
        // a map for when the value is many bits and sparse.
        uint64_t maxval = 0;
        for (const AstEnumItem* itemp = adtypep->itemsp(); itemp;
             itemp = VN_AS(itemp->nextp(), EnumItem)) {
            const AstConst* const vconstp = VN_AS(itemp->valuep(), Const);
            UASSERT_OBJ(vconstp, errNodep, "Enum item without constified value");
            if (vconstp->toUQuad() >= maxval) maxval = vconstp->toUQuad();
        }
        if (adtypep->itemsp()->width() > 64) {
            errNodep->v3warn(E_UNSUPPORTED,
                             "Unsupported: enum next/prev/name method on enum with > 64 bits");
            return 64;
        }
        return maxval;
    }
    AstVar* enumVarp(AstEnumDType* nodep, VAttrType attrType, bool assoc, uint32_t msbdim) {
        // Return a variable table which has specified dimension properties for this variable
        const auto pos = m_tableMap.find(std::make_pair(nodep, attrType));
        if (pos != m_tableMap.end()) return pos->second;
        UINFO(9, "Construct Venumtab attr=" << attrType.ascii() << " assoc=" << assoc
                                            << " max=" << msbdim << " for " << nodep << endl);
        AstNodeDType* basep;
        if (attrType == VAttrType::ENUM_NAME) {
            basep = nodep->findStringDType();
        } else if (attrType == VAttrType::ENUM_VALID) {
            // TODO in theory we could bit-pack the bits in the table, but
            // would require additional operations to extract, so only
            // would be worth it for larger tables which perhaps could be
            // better handled with equation generation?
            basep = nodep->findBitDType();
        } else {
            basep = nodep->dtypep();
        }
        AstNodeDType* vardtypep;
        if (assoc) {
            vardtypep = new AstAssocArrayDType{nodep->fileline(), basep, nodep};
        } else {
            vardtypep = new AstUnpackArrayDType{nodep->fileline(), basep,
                                                new AstRange(nodep->fileline(), msbdim, 0)};
        }
        AstInitArray* const initp = new AstInitArray(nodep->fileline(), vardtypep, nullptr);
        v3Global.rootp()->typeTablep()->addTypesp(vardtypep);
        AstVar* const varp = new AstVar(nodep->fileline(), VVarType::MODULETEMP,
                                        "__Venumtab_" + VString::downcase(attrType.ascii())
                                            + cvtToStr(m_dtTables++),
                                        vardtypep);
        varp->isConst(true);
        varp->isStatic(true);
        varp->valuep(initp);
        // Add to root, as don't know module we are in, and aids later structure sharing
        v3Global.rootp()->dollarUnitPkgAddp()->addStmtp(varp);

        // Default for all unspecified values
        if (attrType == VAttrType::ENUM_NAME) {
            initp->defaultp(new AstConst(nodep->fileline(), AstConst::String(), ""));
        } else if (attrType == VAttrType::ENUM_NEXT || attrType == VAttrType::ENUM_PREV) {
            initp->defaultp(new AstConst(nodep->fileline(), V3Number(nodep, nodep->width(), 0)));
        } else if (attrType == VAttrType::ENUM_VALID) {
            initp->defaultp(new AstConst{nodep->fileline(), AstConst::BitFalse{}});
        } else {
            nodep->v3fatalSrc("Bad case");
        }

        // Find valid values and populate
        UASSERT_OBJ(nodep->itemsp(), nodep, "enum without items");
        std::map<uint64_t, AstNode*> values;
        {
            AstEnumItem* const firstp = nodep->itemsp();
            const AstEnumItem* prevp = firstp;  // Prev must start with last item
            while (prevp->nextp()) prevp = VN_AS(prevp->nextp(), EnumItem);
            for (AstEnumItem* itemp = firstp; itemp;) {
                AstEnumItem* const nextp = VN_AS(itemp->nextp(), EnumItem);
                const AstConst* const vconstp = VN_AS(itemp->valuep(), Const);
                UASSERT_OBJ(vconstp, nodep, "Enum item without constified value");
                const uint64_t i = vconstp->toUQuad();
                if (attrType == VAttrType::ENUM_NAME) {
                    values[i] = new AstConst(nodep->fileline(), AstConst::String(), itemp->name());
                } else if (attrType == VAttrType::ENUM_NEXT) {
                    values[i] = (nextp ? nextp : firstp)->valuep()->cloneTree(false);  // A const
                } else if (attrType == VAttrType::ENUM_PREV) {
                    values[i] = prevp->valuep()->cloneTree(false);  // A const
                } else if (attrType == VAttrType::ENUM_VALID) {
                    values[i] = new AstConst(nodep->fileline(), AstConst::BitTrue{});
                } else {
                    nodep->v3fatalSrc("Bad case");
                }
                prevp = itemp;
                itemp = nextp;
            }
        }
        // Add all specified values to table
        if (assoc) {
            for (const auto& itr : values) initp->addIndexValuep(itr.first, itr.second);
        } else {
            for (uint64_t i = 0; i < (msbdim + 1); ++i) {
                if (values[i]) initp->addIndexValuep(i, values[i]);
            }
        }
        userIterate(varp, nullptr);  // May have already done $unit so must do this var
        m_tableMap.emplace(std::make_pair(nodep, attrType), varp);
        return varp;
    }

    PatVecMap patVectorMap(AstPattern* nodep, const VNumRange& range) {
        PatVecMap patmap;
        int element = range.left();
        for (AstPatMember* patp = VN_AS(nodep->itemsp(), PatMember); patp;
             patp = VN_AS(patp->nextp(), PatMember)) {
            if (patp->keyp()) {
                if (const AstConst* const constp = VN_CAST(patp->keyp(), Const)) {
                    element = constp->toSInt();
                } else {
                    patp->keyp()->v3error("Assignment pattern key not supported/understood: "
                                          << patp->keyp()->prettyTypeName());
                }
            }
            if (patmap.find(element) != patmap.end()) {
                patp->v3error("Assignment pattern key used multiple times: " << element);
            } else {
                patmap.emplace(element, patp);
            }
            element += range.leftToRightInc();
        }
        return patmap;
    }

    void patConcatConvertRecurse(AstPattern* patternp, AstConcat* nodep) {
        if (AstConcat* lhsp = VN_CAST(nodep->lhsp(), Concat)) {
            patConcatConvertRecurse(patternp, lhsp);
        } else {
            patternp->addItemsp(new AstPatMember{nodep->lhsp()->fileline(),
                                                 nodep->lhsp()->unlinkFrBack(), nullptr, nullptr});
        }
        if (AstConcat* rhsp = VN_CAST(nodep->rhsp(), Concat)) {
            patConcatConvertRecurse(patternp, rhsp);
        } else {
            patternp->addItemsp(new AstPatMember{nodep->rhsp()->fileline(),
                                                 nodep->rhsp()->unlinkFrBack(), nullptr, nullptr});
        }
    }

    void makeOpenArrayShell(AstNodeFTaskRef* nodep) {
        UINFO(4, "Replicate openarray function " << nodep->taskp() << endl);
        AstNodeFTask* const oldTaskp = nodep->taskp();
        oldTaskp->dpiOpenParentInc();
        UASSERT_OBJ(!oldTaskp->dpiOpenChild(), oldTaskp,
                    "DPI task should be parent or child, not both");
        AstNodeFTask* const newTaskp = oldTaskp->cloneTree(false);
        newTaskp->dpiOpenChild(true);
        newTaskp->dpiOpenParentClear();
        newTaskp->name(newTaskp->name() + "__Vdpioc" + cvtToStr(oldTaskp->dpiOpenParent()));
        oldTaskp->addNextHere(newTaskp);
        // Relink reference to new function
        nodep->taskp(newTaskp);
        nodep->name(nodep->taskp()->name());
        // Replace open array arguments with the callee's task
        const V3TaskConnects tconnects = V3Task::taskConnects(nodep, nodep->taskp()->stmtsp());
        for (const auto& tconnect : tconnects) {
            AstVar* const portp = tconnect.first;
            const AstArg* const argp = tconnect.second;
            const AstNode* const pinp = argp->exprp();
            if (!pinp) continue;  // Argument error we'll find later
            if (hasOpenArrayIterateDType(portp->dtypep())) portp->dtypep(pinp->dtypep());
        }
    }

    bool markHasOpenArray(AstNodeFTask* nodep) {
        bool hasOpen = false;
        for (AstNode* stmtp = nodep->stmtsp(); stmtp; stmtp = stmtp->nextp()) {
            if (AstVar* const portp = VN_CAST(stmtp, Var)) {
                if (portp->isDpiOpenArray() || hasOpenArrayIterateDType(portp->dtypep())) {
                    portp->isDpiOpenArray(true);
                    hasOpen = true;
                }
            }
        }
        return hasOpen;
    }
    bool hasOpenArrayIterateDType(AstNodeDType* nodep) {
        // Return true iff this datatype or child has an openarray
        if (VN_IS(nodep, UnsizedArrayDType)) return true;
        if (nodep->subDTypep()) return hasOpenArrayIterateDType(nodep->subDTypep()->skipRefp());
        return false;
    }

    //----------------------------------------------------------------------
    // METHODS - casting
    static Castable computeCastable(const AstNodeDType* toDtp, const AstNodeDType* fromDtp,
                                    const AstNode* fromConstp) {
        const auto castable = computeCastableImp(toDtp, fromDtp, fromConstp);
        UINFO(9, "  castable=" << castable << "  for " << toDtp << endl);
        UINFO(9, "     =?= " << fromDtp << endl);
        UINFO(9, "     const= " << fromConstp << endl);
        return castable;
    }
    static Castable computeCastableImp(const AstNodeDType* toDtp, const AstNodeDType* fromDtp,
                                       const AstNode* fromConstp) {
        const Castable castable = UNSUPPORTED;
        toDtp = toDtp->skipRefToEnump();
        fromDtp = fromDtp->skipRefToEnump();
        if (toDtp == fromDtp) return COMPATIBLE;
        const AstNodeDType* fromBaseDtp = fromDtp;
        while (const AstPackArrayDType* const packp = VN_CAST(fromBaseDtp, PackArrayDType)) {
            fromBaseDtp = packp->subDTypep();
            while (const AstRefDType* const refp = VN_CAST(fromBaseDtp, RefDType)) {
                fromBaseDtp = refp->refDTypep();
            }
        }
        const bool fromNumericable = VN_IS(fromBaseDtp, BasicDType)
                                     || VN_IS(fromBaseDtp, EnumDType)
                                     || VN_IS(fromBaseDtp, NodeUOrStructDType);

        const AstNodeDType* toBaseDtp = toDtp;
        while (const AstPackArrayDType* const packp = VN_CAST(toBaseDtp, PackArrayDType)) {
            toBaseDtp = packp->subDTypep();
            while (const AstRefDType* const refp = VN_CAST(toBaseDtp, RefDType)) {
                toBaseDtp = refp->refDTypep();
            }
        }
        const bool toNumericable
            = VN_IS(toBaseDtp, BasicDType) || VN_IS(toBaseDtp, NodeUOrStructDType);
        // UNSUP unpacked struct/unions (treated like BasicDType)
        if (toNumericable) {
            if (fromNumericable) return COMPATIBLE;
        } else if (VN_IS(toDtp, EnumDType)) {
            if (VN_IS(fromBaseDtp, EnumDType) && toDtp->sameTree(fromDtp)) return ENUM_IMPLICIT;
            if (fromNumericable) return ENUM_EXPLICIT;
        } else if (VN_IS(toDtp, ClassRefDType) && VN_IS(fromConstp, Const)) {
            if (VN_IS(fromConstp, Const) && VN_AS(fromConstp, Const)->num().isNull())
                return COMPATIBLE;
        } else if (VN_IS(toDtp, ClassRefDType) && VN_IS(fromDtp, ClassRefDType)) {
            const auto toClassp = VN_AS(toDtp, ClassRefDType)->classp();
            const auto fromClassp = VN_AS(fromDtp, ClassRefDType)->classp();
            const bool downcast = AstClass::isClassExtendedFrom(toClassp, fromClassp);
            const bool upcast = AstClass::isClassExtendedFrom(fromClassp, toClassp);
            if (upcast) {
                return COMPATIBLE;
            } else if (downcast) {
                return DYNAMIC_CLASS;
            } else {
                return INCOMPATIBLE;
            }
        }
        return castable;
    }

    //----------------------------------------------------------------------
    // METHODS - special type detection
    void assertAtStatement(AstNode* nodep) {
        if (VL_UNCOVERABLE(m_vup && !m_vup->selfDtm())) {
            UINFO(1, "-: " << m_vup << endl);
            nodep->v3fatalSrc("No dtype expected at statement " << nodep->prettyTypeName());
        }
    }
    void checkConstantOrReplace(AstNode* nodep, const string& message) {
        // See also V3WidthSel::checkConstantOrReplace
        // Note can't call V3Const::constifyParam(nodep) here, as constify may change nodep on us!
        if (!VN_IS(nodep, Const)) {
            nodep->v3error(message);
            nodep->replaceWith(new AstConst(nodep->fileline(), AstConst::Unsized32(), 1));
            VL_DO_DANGLING(pushDeletep(nodep), nodep);
        }
    }
    AstNode* newVarRefDollarUnit(AstVar* nodep) {
        AstVarRef* const varrefp = new AstVarRef{nodep->fileline(), nodep, VAccess::READ};
        varrefp->classOrPackagep(v3Global.rootp()->dollarUnitPkgAddp());
        return varrefp;
    }
    AstNode* nodeForUnsizedWarning(AstNode* nodep) {
        // Return a nodep to use for unsized warnings, reporting on child if can
        if (nodep->op1p() && nodep->op1p()->dtypep() && !nodep->op1p()->dtypep()->widthSized()) {
            return nodep->op1p();
        } else if (nodep->op2p() && nodep->op2p()->dtypep()
                   && !nodep->op2p()->dtypep()->widthSized()) {
            return nodep->op2p();
        }
        return nodep;  // By default return this
    }
    AstRefDType* checkRefToTypedefRecurse(AstNode* nodep, AstTypedef* typedefp) {
        // Recurse all children looking for self reference
        // This avoids iterateEditMoveDTypep going into a hard to resolve loop
        // Only call once for any given typedef, or will become O(n^2)
        if (VL_LIKELY(!nodep)) return nullptr;
        if (auto* const refp = VN_CAST(nodep, RefDType)) {
            if (refp->typedefp() == typedefp) return refp;
        }
        if (auto* const refp = checkRefToTypedefRecurse(nodep->op1p(), typedefp)) return refp;
        if (auto* const refp = checkRefToTypedefRecurse(nodep->op2p(), typedefp)) return refp;
        if (auto* const refp = checkRefToTypedefRecurse(nodep->op3p(), typedefp)) return refp;
        if (auto* const refp = checkRefToTypedefRecurse(nodep->op4p(), typedefp)) return refp;
        return nullptr;
    }

    //----------------------------------------------------------------------
    // METHODS - special iterators
    // These functions save/restore the AstNUser information so it can pass to child nodes.

    AstNode* userIterateSubtreeReturnEdits(AstNode* nodep, WidthVP* vup) {
        if (!nodep) return nullptr;
        AstNode* ret;
        {
            VL_RESTORER(m_vup);
            m_vup = vup;
            ret = iterateSubtreeReturnEdits(nodep);
        }
        return ret;
    }
    void userIterate(AstNode* nodep, WidthVP* vup) {
        if (!nodep) return;
        {
            VL_RESTORER(m_vup);
            m_vup = vup;
            iterate(nodep);
        }
    }
    void userIterateAndNext(AstNode* nodep, WidthVP* vup) {
        if (!nodep) return;
        if (nodep->didWidth()) return;  // Avoid iterating list we have already iterated
        {
            VL_RESTORER(m_vup);
            m_vup = vup;
            iterateAndNextNull(nodep);
        }
    }
    void userIterateChildren(AstNode* nodep, WidthVP* vup) {
        if (!nodep) return;
        {
            VL_RESTORER(m_vup);
            m_vup = vup;
            iterateChildren(nodep);
        }
    }
    void userIterateChildrenBackwards(AstNode* nodep, WidthVP* vup) {
        if (!nodep) return;
        {
            VL_RESTORER(m_vup);
            m_vup = vup;
            iterateChildrenBackwards(nodep);
        }
    }

public:
    // CONSTRUCTORS
    WidthVisitor(bool paramsOnly,  // [in] TRUE if we are considering parameters only.
                 bool doGenerate)  // [in] TRUE if we are inside a generate statement and
        //                           // don't wish to trigger errors
        : m_paramsOnly{paramsOnly}
        , m_doGenerate{doGenerate} {}
    AstNode* mainAcceptEdit(AstNode* nodep) {
        return userIterateSubtreeReturnEdits(nodep, WidthVP(SELF, BOTH).p());
    }
    virtual ~WidthVisitor() override = default;
};

//######################################################################
// Width class functions

int V3Width::debug() {
    static int level = -1;
    if (VL_UNLIKELY(level < 0)) level = v3Global.opt.debugSrcLevel(__FILE__);
    return level;
}

void V3Width::width(AstNetlist* nodep) {
    UINFO(2, __FUNCTION__ << ": " << endl);
    {
        // We should do it in bottom-up module order, but it works in any order.
        const WidthClearVisitor cvisitor{nodep};
        WidthVisitor visitor{false, false};
        (void)visitor.mainAcceptEdit(nodep);
        WidthRemoveVisitor rvisitor;
        (void)rvisitor.mainAcceptEdit(nodep);
    }  // Destruct before checking
    V3Global::dumpCheckGlobalTree("width", 0, v3Global.opt.dumpTreeLevel(__FILE__) >= 3);
}

//! Single node parameter propagation
//! Smaller step... Only do a single node for parameter propagation
AstNode* V3Width::widthParamsEdit(AstNode* nodep) {
    UINFO(4, __FUNCTION__ << ": " << nodep << endl);
    // We should do it in bottom-up module order, but it works in any order.
    WidthVisitor visitor{true, false};
    nodep = visitor.mainAcceptEdit(nodep);
    // No WidthRemoveVisitor, as don't want to drop $signed etc inside gen blocks
    return nodep;
}

//! Single node parameter propagation for generate blocks.
//! Smaller step... Only do a single node for parameter propagation
//! If we are inside a generated "if", "case" or "for", we don't want to
//! trigger warnings when we deal with the width. It is possible that
//! these are spurious, existing within sub-expressions that will not
//! actually be generated. Since such occurrences, must be constant, in
//! order to be something a generate block can depend on, we can wait until
//! later to do the width check.
//! @return  Pointer to the edited node.
AstNode* V3Width::widthGenerateParamsEdit(
    AstNode* nodep) {  //!< [in] AST whose parameters widths are to be analysed.
    UINFO(4, __FUNCTION__ << ": " << nodep << endl);
    // We should do it in bottom-up module order, but it works in any order.
    WidthVisitor visitor{true, true};
    nodep = visitor.mainAcceptEdit(nodep);
    // No WidthRemoveVisitor, as don't want to drop $signed etc inside gen blocks
    return nodep;
}

void V3Width::widthCommit(AstNetlist* nodep) {
    UINFO(2, __FUNCTION__ << ": " << endl);
    { WidthCommitVisitor{nodep}; }  // Destruct before checking
    V3Global::dumpCheckGlobalTree("widthcommit", 0, v3Global.opt.dumpTreeLevel(__FILE__) >= 6);
}
