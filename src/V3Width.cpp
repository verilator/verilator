// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Expression width calculations
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2020 by Wilson Snyder. This program is free software; you
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

#include "V3Global.h"
#include "V3Width.h"
#include "V3Number.h"
#include "V3Const.h"
#include "V3String.h"
#include "V3Task.h"

#include <algorithm>
#include <cstdarg>

// More code; this file was getting too large; see actions there
#define _V3WIDTH_CPP_
#include "V3WidthCommit.h"

//######################################################################

enum Stage { PRELIM = 1, FINAL = 2, BOTH = 3 };  // Numbers are a bitmask <0>=prelim, <1>=final
std::ostream& operator<<(std::ostream& str, const Stage& rhs) {
    return str << ("-PFB"[static_cast<int>(rhs)]);
}

enum Determ {
    SELF,  // Self-determined
    CONTEXT,  // Context-determined
    ASSIGN  // Assignment-like where sign comes from RHS only
};
std::ostream& operator<<(std::ostream& str, const Determ& rhs) {
    static const char* const s_det[] = {"SELF", "CNTX", "ASSN"};
    return str << s_det[rhs];
}

//######################################################################
// Width state, as a visitor of each AstNode

class WidthVP {
    // Parameters to pass down hierarchy with visit functions.
    AstNodeDType* m_dtypep;  // Parent's data type to resolve to
    Stage m_stage;  // If true, report errors
public:
    WidthVP(AstNodeDType* dtypep, Stage stage)
        : m_dtypep(dtypep)
        , m_stage(stage) {
        // Prelim doesn't look at assignments, so shouldn't need a dtype,
        // however AstPattern uses them
    }
    WidthVP(Determ determ, Stage stage)
        : m_dtypep(NULL)
        , m_stage(stage) {
        if (determ != SELF && stage != PRELIM)
            v3fatalSrc("Context-determined width request only allowed as prelim step");
    }
    WidthVP* p() { return this; }
    bool selfDtm() const { return m_dtypep == NULL; }
    AstNodeDType* dtypep() const {
        // Detect where overrideDType is probably the intended call
        if (!m_dtypep) v3fatalSrc("Width dtype request on self-determined or preliminary VUP");
        return m_dtypep;
    }
    AstNodeDType* dtypeNullp() const { return m_dtypep; }
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
            str << "  VUP(s=" << m_stage << ",dt=" << cvtToHex(dtypep()) << ")";
        }
    }
};
std::ostream& operator<<(std::ostream& str, const WidthVP* vup) {
    if (vup) vup->dump(str);
    return str;
}

//######################################################################

class WidthClearVisitor {
    // Rather than a AstNVisitor, can just quickly touch every node
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
    virtual ~WidthClearVisitor() {}
};

//######################################################################

#define accept in_WidthVisitor_use_AstNode_iterate_instead_of_AstNode_accept

//######################################################################

class WidthVisitor : public AstNVisitor {
private:
    // TYPES
    typedef std::map<std::pair<AstNodeDType*, AstAttrType>, AstVar*> TableMap;
    typedef std::map<int, AstPatMember*> PatVecMap;

    // STATE
    WidthVP* m_vup;  // Current node state
    bool m_paramsOnly;  // Computing parameter value; limit operation
    AstRange* m_cellRangep;  // Range for arrayed instantiations, NULL for normal instantiations
    AstNodeFTask* m_ftaskp;  // Current function/task
    AstFunc* m_funcp;  // Current function
    AstInitial* m_initialp;  // Current initial block
    AstAttrOf* m_attrp;  // Current attribute
    bool m_doGenerate;  // Do errors later inside generate statement
    int m_dtTables;  // Number of created data type tables
    TableMap m_tableMap;  // Created tables so can remove duplicates

    // ENUMS
    enum ExtendRule {
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
    virtual void visit(AstLogNot* nodep) VL_OVERRIDE { visit_log_not(nodep); }
    // Widths: 1 bit out, lhs 1 bit, rhs 1 bit; Real: converts via compare with 0
    virtual void visit(AstLogAnd* nodep) VL_OVERRIDE { visit_log_and_or(nodep); }
    virtual void visit(AstLogOr* nodep) VL_OVERRIDE { visit_log_and_or(nodep); }
    virtual void visit(AstLogEq* nodep) VL_OVERRIDE {
        // Conversion from real not in IEEE, but a fallout
        visit_log_and_or(nodep);
    }
    virtual void visit(AstLogIf* nodep) VL_OVERRIDE {
        // Conversion from real not in IEEE, but a fallout
        visit_log_and_or(nodep);
    }

    // Widths: 1 bit out, Any width lhs
    virtual void visit(AstRedAnd* nodep) VL_OVERRIDE { visit_red_and_or(nodep); }
    virtual void visit(AstRedOr* nodep) VL_OVERRIDE { visit_red_and_or(nodep); }
    virtual void visit(AstRedXnor* nodep) VL_OVERRIDE { visit_red_and_or(nodep); }
    virtual void visit(AstRedXor* nodep) VL_OVERRIDE { visit_red_and_or(nodep); }
    virtual void visit(AstOneHot* nodep) VL_OVERRIDE { visit_red_and_or(nodep); }
    virtual void visit(AstOneHot0* nodep) VL_OVERRIDE { visit_red_and_or(nodep); }
    virtual void visit(AstIsUnknown* nodep) VL_OVERRIDE {
        visit_red_unknown(nodep);  // Allow real
    }

    // These have different node types, as they operate differently
    // Must add to case statement below,
    // Widths: 1 bit out, lhs width == rhs width.  real if lhs|rhs real
    virtual void visit(AstEq* nodep) VL_OVERRIDE { visit_cmp_eq_gt(nodep, true); }
    virtual void visit(AstNeq* nodep) VL_OVERRIDE { visit_cmp_eq_gt(nodep, true); }
    virtual void visit(AstGt* nodep) VL_OVERRIDE { visit_cmp_eq_gt(nodep, true); }
    virtual void visit(AstGte* nodep) VL_OVERRIDE { visit_cmp_eq_gt(nodep, true); }
    virtual void visit(AstLt* nodep) VL_OVERRIDE { visit_cmp_eq_gt(nodep, true); }
    virtual void visit(AstLte* nodep) VL_OVERRIDE { visit_cmp_eq_gt(nodep, true); }
    virtual void visit(AstGtS* nodep) VL_OVERRIDE { visit_cmp_eq_gt(nodep, true); }
    virtual void visit(AstGteS* nodep) VL_OVERRIDE { visit_cmp_eq_gt(nodep, true); }
    virtual void visit(AstLtS* nodep) VL_OVERRIDE { visit_cmp_eq_gt(nodep, true); }
    virtual void visit(AstLteS* nodep) VL_OVERRIDE { visit_cmp_eq_gt(nodep, true); }
    virtual void visit(AstEqCase* nodep) VL_OVERRIDE { visit_cmp_eq_gt(nodep, true); }
    virtual void visit(AstNeqCase* nodep) VL_OVERRIDE { visit_cmp_eq_gt(nodep, true); }
    // ...    These comparisons don't allow reals
    virtual void visit(AstEqWild* nodep) VL_OVERRIDE { visit_cmp_eq_gt(nodep, false); }
    virtual void visit(AstNeqWild* nodep) VL_OVERRIDE { visit_cmp_eq_gt(nodep, false); }
    // ...    Real compares
    virtual void visit(AstEqD* nodep) VL_OVERRIDE { visit_cmp_real(nodep); }
    virtual void visit(AstNeqD* nodep) VL_OVERRIDE { visit_cmp_real(nodep); }
    virtual void visit(AstLtD* nodep) VL_OVERRIDE { visit_cmp_real(nodep); }
    virtual void visit(AstLteD* nodep) VL_OVERRIDE { visit_cmp_real(nodep); }
    virtual void visit(AstGtD* nodep) VL_OVERRIDE { visit_cmp_real(nodep); }
    virtual void visit(AstGteD* nodep) VL_OVERRIDE { visit_cmp_real(nodep); }
    // ...    String compares
    virtual void visit(AstEqN* nodep) VL_OVERRIDE { visit_cmp_string(nodep); }
    virtual void visit(AstNeqN* nodep) VL_OVERRIDE { visit_cmp_string(nodep); }
    virtual void visit(AstLtN* nodep) VL_OVERRIDE { visit_cmp_string(nodep); }
    virtual void visit(AstLteN* nodep) VL_OVERRIDE { visit_cmp_string(nodep); }
    virtual void visit(AstGtN* nodep) VL_OVERRIDE { visit_cmp_string(nodep); }
    virtual void visit(AstGteN* nodep) VL_OVERRIDE { visit_cmp_string(nodep); }

    // Widths: out width = lhs width = rhs width
    // Signed: Output signed iff LHS & RHS signed.
    // Real: Not allowed
    virtual void visit(AstAnd* nodep) VL_OVERRIDE { visit_boolmath_and_or(nodep); }
    virtual void visit(AstOr* nodep) VL_OVERRIDE { visit_boolmath_and_or(nodep); }
    virtual void visit(AstXnor* nodep) VL_OVERRIDE { visit_boolmath_and_or(nodep); }
    virtual void visit(AstXor* nodep) VL_OVERRIDE { visit_boolmath_and_or(nodep); }
    virtual void visit(AstBufIf1* nodep) VL_OVERRIDE {
        visit_boolmath_and_or(nodep);
    }  // Signed behavior changing in 3.814
    // Width: Max(Lhs,Rhs) sort of.
    // Real: If either side real
    // Signed: If both sides real
    virtual void visit(AstAdd* nodep) VL_OVERRIDE { visit_add_sub_replace(nodep, true); }
    virtual void visit(AstSub* nodep) VL_OVERRIDE { visit_add_sub_replace(nodep, true); }
    virtual void visit(AstDiv* nodep) VL_OVERRIDE { visit_add_sub_replace(nodep, true); }
    virtual void visit(AstMul* nodep) VL_OVERRIDE { visit_add_sub_replace(nodep, true); }
    // These can't promote to real
    virtual void visit(AstModDiv* nodep) VL_OVERRIDE { visit_add_sub_replace(nodep, false); }
    virtual void visit(AstModDivS* nodep) VL_OVERRIDE { visit_add_sub_replace(nodep, false); }
    virtual void visit(AstMulS* nodep) VL_OVERRIDE { visit_add_sub_replace(nodep, false); }
    virtual void visit(AstDivS* nodep) VL_OVERRIDE { visit_add_sub_replace(nodep, false); }
    // Widths: out width = lhs width, but upper matters
    // Signed: Output signed iff LHS signed; unary operator
    // Unary promote to real
    virtual void visit(AstNegate* nodep) VL_OVERRIDE { visit_negate_not(nodep, true); }
    // Unary never real
    virtual void visit(AstNot* nodep) VL_OVERRIDE { visit_negate_not(nodep, false); }

    // Real: inputs and output real
    virtual void visit(AstAddD* nodep) VL_OVERRIDE { visit_real_add_sub(nodep); }
    virtual void visit(AstSubD* nodep) VL_OVERRIDE { visit_real_add_sub(nodep); }
    virtual void visit(AstDivD* nodep) VL_OVERRIDE { visit_real_add_sub(nodep); }
    virtual void visit(AstMulD* nodep) VL_OVERRIDE { visit_real_add_sub(nodep); }
    virtual void visit(AstPowD* nodep) VL_OVERRIDE { visit_real_add_sub(nodep); }
    virtual void visit(AstNodeSystemBiop* nodep) VL_OVERRIDE { visit_real_add_sub(nodep); }
    // Real: Output real
    virtual void visit(AstNegateD* nodep) VL_OVERRIDE { visit_real_neg_ceil(nodep); }
    virtual void visit(AstNodeSystemUniop* nodep) VL_OVERRIDE { visit_real_neg_ceil(nodep); }

    // Widths: out signed/unsigned width = lhs width, input un|signed
    virtual void visit(AstSigned* nodep) VL_OVERRIDE {
        visit_signed_unsigned(nodep, VSigning::SIGNED);
    }
    virtual void visit(AstUnsigned* nodep) VL_OVERRIDE {
        visit_signed_unsigned(nodep, VSigning::UNSIGNED);
    }

    // Widths: Output width from lhs, rhs<33 bits
    // Signed: If lhs signed
    virtual void visit(AstShiftL* nodep) VL_OVERRIDE { visit_shift(nodep); }
    virtual void visit(AstShiftR* nodep) VL_OVERRIDE { visit_shift(nodep); }
    // ShiftRS converts to ShiftR, but not vice-versa
    virtual void visit(AstShiftRS* nodep) VL_OVERRIDE { visit_shift(nodep); }

    //========
    // Widths: Output real, input integer signed
    virtual void visit(AstBitsToRealD* nodep) VL_OVERRIDE { visit_Or_Lu64(nodep); }
    virtual void visit(AstIToRD* nodep) VL_OVERRIDE { visit_Or_Ls32(nodep); }

    // Widths: Output integer signed, input real
    virtual void visit(AstRToIS* nodep) VL_OVERRIDE { visit_Os32_Lr(nodep); }
    virtual void visit(AstRToIRoundS* nodep) VL_OVERRIDE {
        // Only created here, size comes from upper expression
        if (m_vup->prelim()) {  // First stage evaluation
            iterateCheckReal(nodep, "LHS", nodep->lhsp(), BOTH);
        }
        if (!nodep->dtypep()->widthSized()) nodep->v3fatalSrc("RToIRoundS should be presized");
    }

    // Widths: Output integer unsigned, input real
    virtual void visit(AstRealToBits* nodep) VL_OVERRIDE { visit_Ou64_Lr(nodep); }

    // Output integer, input string
    virtual void visit(AstLenN* nodep) VL_OVERRIDE { visit_Os32_string(nodep); }
    virtual void visit(AstPutcN* nodep) VL_OVERRIDE {
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
    virtual void visit(AstGetcN* nodep) VL_OVERRIDE {
        // CALLER: str.getc()
        UASSERT_OBJ(nodep->rhsp(), nodep, "For binary ops only!");
        if (m_vup && m_vup->prelim()) {
            // See similar handling in visit_cmp_eq_gt where created
            iterateCheckString(nodep, "LHS", nodep->lhsp(), BOTH);
            iterateCheckSigned32(nodep, "RHS", nodep->rhsp(), BOTH);
            nodep->dtypeSetBitSized(8, VSigning::UNSIGNED);
        }
    }
    virtual void visit(AstGetcRefN* nodep) VL_OVERRIDE {
        // CALLER: str.getc()
        UASSERT_OBJ(nodep->rhsp(), nodep, "For binary ops only!");
        if (m_vup && m_vup->prelim()) {
            // See similar handling in visit_cmp_eq_gt where created
            iterateCheckString(nodep, "LHS", nodep->lhsp(), BOTH);
            iterateCheckSigned32(nodep, "RHS", nodep->rhsp(), BOTH);
            nodep->dtypeSetBitSized(8, VSigning::UNSIGNED);
        }
    }
    virtual void visit(AstSubstrN* nodep) VL_OVERRIDE {
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
    virtual void visit(AstCompareNN* nodep) VL_OVERRIDE {
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
    virtual void visit(AstAtoN* nodep) VL_OVERRIDE {
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
    virtual void visit(AstTime* nodep) VL_OVERRIDE { nodep->dtypeSetUInt64(); }
    virtual void visit(AstTimeD* nodep) VL_OVERRIDE { nodep->dtypeSetDouble(); }
    virtual void visit(AstTestPlusArgs* nodep) VL_OVERRIDE { nodep->dtypeSetSigned32(); }
    virtual void visit(AstScopeName* nodep) VL_OVERRIDE {
        nodep->dtypeSetUInt64();  // A pointer, but not that it matters
    }

    // Special cases.  So many....
    virtual void visit(AstNodeCond* nodep) VL_OVERRIDE {
        // op=cond?expr1:expr2
        // Signed: Output signed iff RHS & THS signed  (presumed, not in IEEE)
        // See IEEE-2012 11.4.11 and Table 11-21.
        //   LHS is self-determined
        //   Width: max(RHS,THS)
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
                int width = std::max(nodep->expr1p()->width(), nodep->expr2p()->width());
                int mwidth = std::max(nodep->expr1p()->widthMin(), nodep->expr2p()->widthMin());
                bool issigned = nodep->expr1p()->isSigned() && nodep->expr2p()->isSigned();
                nodep->dtypeSetLogicUnsized(width, mwidth, VSigning::fromBool(issigned));
            }
        }
        if (m_vup->final()) {
            AstNodeDType* expDTypep = m_vup->dtypeOverridep(nodep->dtypep());
            AstNodeDType* subDTypep = expDTypep;
            nodep->dtypeFrom(expDTypep);
            // Error report and change sizes for suboperands of this node.
            iterateCheck(nodep, "Conditional True", nodep->expr1p(), CONTEXT, FINAL, subDTypep,
                         EXTEND_EXP);
            iterateCheck(nodep, "Conditional False", nodep->expr2p(), CONTEXT, FINAL, subDTypep,
                         EXTEND_EXP);
        }
    }
    virtual void visit(AstConcat* nodep) VL_OVERRIDE {
        // Real: Not allowed (assumed)
        // Signed: unsigned output, input either (assumed)
        // IEEE-2012 Table 11-21, and 11.8.1:
        //   LHS, RHS is self-determined
        //   signed: Unsigned  (11.8.1)
        //   width: LHS + RHS
        if (m_vup->prelim()) {
            AstNodeDType* vdtypep = m_vup->dtypeNullp();
            if (vdtypep
                && (VN_IS(vdtypep, AssocArrayDType)  //
                    || VN_IS(vdtypep, DynArrayDType)  //
                    || VN_IS(vdtypep, QueueDType))) {
                nodep->v3error("Unsupported: Concatenation to form " << vdtypep->prettyDTypeNameQ()
                                                                     << "data type");
            }

            iterateCheckSizedSelf(nodep, "LHS", nodep->lhsp(), SELF, BOTH);
            iterateCheckSizedSelf(nodep, "RHS", nodep->rhsp(), SELF, BOTH);
            nodep->dtypeSetLogicUnsized(nodep->lhsp()->width() + nodep->rhsp()->width(),
                                        nodep->lhsp()->widthMin() + nodep->rhsp()->widthMin(),
                                        VSigning::UNSIGNED);
            // Cleanup zero width Verilog2001 {x,{0{foo}}} now,
            // otherwise having width(0) will cause later assertions to fire
            if (AstReplicate* repp = VN_CAST(nodep->lhsp(), Replicate)) {
                if (repp->width() == 0) {  // Keep rhs
                    nodep->replaceWith(nodep->rhsp()->unlinkFrBack());
                    VL_DO_DANGLING(pushDeletep(nodep), nodep);
                    return;
                }
            }
            if (AstReplicate* repp = VN_CAST(nodep->rhsp(), Replicate)) {
                if (repp->width() == 0) {  // Keep lhs
                    nodep->replaceWith(nodep->lhsp()->unlinkFrBack());
                    VL_DO_DANGLING(pushDeletep(nodep), nodep);
                    return;
                }
            }
            if (nodep->lhsp()->isString() || nodep->rhsp()->isString()) {
                AstNode* newp = new AstConcatN(nodep->fileline(), nodep->lhsp()->unlinkFrBack(),
                                               nodep->rhsp()->unlinkFrBack());
                nodep->replaceWith(newp);
                VL_DO_DANGLING(pushDeletep(nodep), nodep);
                return;
            }
        }
        if (m_vup->final()) {
            if (!nodep->dtypep()->widthSized()) {
                // See also error in V3Number
                nodeForUnsizedWarning(nodep)->v3warn(
                    WIDTHCONCAT, "Unsized numbers/parameters not allowed in concatenations.");
            }
        }
    }
    virtual void visit(AstConcatN* nodep) VL_OVERRIDE {
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
    virtual void visit(AstDelay* nodep) VL_OVERRIDE {
        nodep->v3warn(STMTDLY, "Unsupported: Ignoring delay on this delayed statement.");
        VL_DO_DANGLING(pushDeletep(nodep->unlinkFrBack()), nodep);
    }
    virtual void visit(AstToLowerN* nodep) VL_OVERRIDE {
        if (m_vup->prelim()) {
            iterateCheckString(nodep, "LHS", nodep->lhsp(), BOTH);
            nodep->dtypeSetString();
        }
    }
    virtual void visit(AstToUpperN* nodep) VL_OVERRIDE {
        if (m_vup->prelim()) {
            iterateCheckString(nodep, "LHS", nodep->lhsp(), BOTH);
            nodep->dtypeSetString();
        }
    }
    virtual void visit(AstReplicate* nodep) VL_OVERRIDE {
        // IEEE-2012 Table 11-21:
        //   LHS, RHS is self-determined
        //   width: value(LHS) * width(RHS)
        if (m_vup->prelim()) {
            AstNodeDType* vdtypep = m_vup->dtypeNullp();
            if (vdtypep
                && (VN_IS(vdtypep, AssocArrayDType) || VN_IS(vdtypep, DynArrayDType)
                    || VN_IS(vdtypep, QueueDType) || VN_IS(vdtypep, UnpackArrayDType))) {
                nodep->v3error("Unsupported: Replication to form " << vdtypep->prettyDTypeNameQ()
                                                                   << " data type");
            }
            iterateCheckSizedSelf(nodep, "LHS", nodep->lhsp(), SELF, BOTH);
            iterateCheckSizedSelf(nodep, "RHS", nodep->rhsp(), SELF, BOTH);
            V3Const::constifyParamsEdit(nodep->rhsp());  // rhsp may change
            const AstConst* constp = VN_CAST(nodep->rhsp(), Const);
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
            if (nodep->lhsp()->isString()) {
                AstNode* newp = new AstReplicateN(nodep->fileline(), nodep->lhsp()->unlinkFrBack(),
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
    virtual void visit(AstReplicateN* nodep) VL_OVERRIDE {
        // Replicate with string
        if (m_vup->prelim()) {
            iterateCheckString(nodep, "LHS", nodep->lhsp(), BOTH);
            iterateCheckSizedSelf(nodep, "RHS", nodep->rhsp(), SELF, BOTH);
            V3Const::constifyParamsEdit(nodep->rhsp());  // rhsp may change
            const AstConst* constp = VN_CAST(nodep->rhsp(), Const);
            if (!constp) {
                nodep->v3error("Replication value isn't a constant.");
                return;
            }
            uint32_t times = constp->toUInt();
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
    virtual void visit(AstNodeStream* nodep) VL_OVERRIDE {
        if (m_vup->prelim()) {
            iterateCheckSizedSelf(nodep, "LHS", nodep->lhsp(), SELF, BOTH);
            iterateCheckSizedSelf(nodep, "RHS", nodep->rhsp(), SELF, BOTH);
            V3Const::constifyParamsEdit(nodep->rhsp());  // rhsp may change
            const AstConst* constp = VN_CAST(nodep->rhsp(), Const);
            AstBasicDType* basicp = VN_CAST(nodep->rhsp(), BasicDType);
            if (!constp && !basicp) {
                nodep->v3error("Slice size isn't a constant or basic data type.");
                return;
            }
            if (basicp) {  // Convert data type to a constant size
                AstConst* newp = new AstConst(basicp->fileline(), basicp->width());
                nodep->rhsp()->replaceWith(newp);
                pushDeletep(basicp);
            } else {
                uint32_t sliceSize = constp->toUInt();
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
    virtual void visit(AstRange* nodep) VL_OVERRIDE {
        // Real: Not allowed
        // Signed: unsigned output, input either
        // Convert all range values to constants
        UINFO(6, "RANGE " << nodep << endl);
        V3Const::constifyParamsEdit(nodep->msbp());  // May relink pointed to node
        V3Const::constifyParamsEdit(nodep->lsbp());  // May relink pointed to node
        checkConstantOrReplace(nodep->msbp(), "MSB of bit range isn't a constant");
        checkConstantOrReplace(nodep->lsbp(), "LSB of bit range isn't a constant");
        int msb = nodep->msbConst();
        int lsb = nodep->lsbConst();
        if (msb < lsb) {
            // Little endian bits are legal, just remember to swap
            // Warning is in V3Width to avoid false warnings when in "off" generate if's
            nodep->littleEndian(!nodep->littleEndian());
            // Internally we'll always have msb() be the greater number
            // We only need to correct when doing [] AstSel extraction,
            // and when tracing the vector.
            nodep->msbp()->swapWith(nodep->lsbp());
        }
        if (m_vup->prelim()) {
            // Don't need to iterate because V3Const already constified
            int width = nodep->elementsConst();
            if (width > (1 << 28)) {
                nodep->v3error("Width of bit range is huge; vector of over 1billion bits: 0x"
                               << std::hex << width);
            }
            // Note width() not set on range; use elementsConst()
            if (nodep->littleEndian() && !VN_IS(nodep->backp(), UnpackArrayDType)
                && !VN_IS(nodep->backp(), Cell)) {  // For cells we warn in V3Inst
                nodep->v3warn(LITENDIAN, "Little bit endian vector: MSB < LSB of bit range: "
                                             << nodep->lsbConst() << ":" << nodep->msbConst());
            }
        }
    }

    virtual void visit(AstSel* nodep) VL_OVERRIDE {
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
            AstConst* widthConstp = VN_CAST(nodep->widthp(), Const);
            if (!widthConstp) {
                nodep->v3error("Width of bit extract isn't a constant");
                nodep->dtypeSetLogicBool();
                return;
            }
            int width = nodep->widthConst();
            UASSERT_OBJ(nodep->dtypep(), nodep, "dtype wasn't set");  // by V3WidthSel
            if (VN_IS(nodep->lsbp(), Const) && nodep->msbConst() < nodep->lsbConst()) {
                nodep->v3error("Unsupported: MSB < LSB of bit extract: "
                               << nodep->msbConst() << "<" << nodep->lsbConst());
                width = (nodep->lsbConst() - nodep->msbConst() + 1);
                nodep->dtypeSetLogicSized(width, VSigning::UNSIGNED);
                nodep->widthp()->replaceWith(new AstConst(nodep->widthp()->fileline(), width));
                nodep->lsbp()->replaceWith(new AstConst(nodep->lsbp()->fileline(), 0));
            }
            // We're extracting, so just make sure the expression is at least wide enough.
            if (nodep->fromp()->width() < width) {
                nodep->v3error("Extracting " << width << " bits from only "
                                             << nodep->fromp()->width() << " bit number");
                // Extend it.
                AstNodeDType* subDTypep
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
            int elw = nodep->declElWidth();  // Must adjust to tell user bit ranges
            if (nodep->declRange().ranged()) {
                frommsb = nodep->declRange().hiMaxSelect() * elw
                          + (elw - 1);  // Corrected for negative lsb
                fromlsb = nodep->declRange().lo() * elw;
            } else {
                // nodep->v3fatalSrc("Should have been declRanged in V3WidthSel");
            }
            int selwidth = V3Number::log2b(frommsb + 1 - 1) + 1;  // Width to address a bit
            AstNodeDType* selwidthDTypep
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

    virtual void visit(AstArraySel* nodep) VL_OVERRIDE {
        // Signed/Real: Output signed iff LHS signed/real; binary operator
        // Note by contrast, bit extract selects are unsigned
        // LSB is self-determined (IEEE 2012 11.5.1)
        if (m_vup->prelim()) {
            iterateCheckSizedSelf(nodep, "Bit select", nodep->bitp(), SELF, BOTH);
            userIterateAndNext(nodep->fromp(), WidthVP(SELF, BOTH).p());
            //
            int frommsb;
            int fromlsb;
            AstNodeDType* fromDtp = nodep->fromp()->dtypep()->skipRefp();
            if (const AstUnpackArrayDType* adtypep = VN_CAST(fromDtp, UnpackArrayDType)) {
                frommsb = adtypep->msb();
                fromlsb = adtypep->lsb();
                if (fromlsb > frommsb) {
                    int t = frommsb;
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
            int selwidth = V3Number::log2b(frommsb + 1 - 1) + 1;  // Width to address a bit
            AstNodeDType* selwidthDTypep
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
                    && (VN_CAST(nodep->bitp(), Const)->toSInt() > (frommsb - fromlsb)
                        || VN_CAST(nodep->bitp(), Const)->toSInt() < 0)) {
                    nodep->v3warn(SELRANGE,
                                  "Selection index out of range: "
                                      << (VN_CAST(nodep->bitp(), Const)->toSInt() + fromlsb)
                                      << " outside " << frommsb << ":" << fromlsb);
                    UINFO(1, "    Related node: " << nodep << endl);
                }
                widthCheckSized(nodep, "Extract Range", nodep->bitp(), selwidthDTypep, EXTEND_EXP,
                                false /*NOWARN*/);
            }
        }
    }

    virtual void visit(AstAssocSel* nodep) VL_OVERRIDE {
        // Signed/Real: Output type based on array-declared type; binary operator
        if (m_vup->prelim()) {
            AstNodeDType* fromDtp = nodep->fromp()->dtypep()->skipRefp();
            AstAssocArrayDType* adtypep = VN_CAST(fromDtp, AssocArrayDType);
            if (!adtypep) {
                UINFO(1, "    Related dtype: " << fromDtp << endl);
                nodep->v3fatalSrc("Associative array reference is not to associative array");
            }
            iterateCheckTyped(nodep, "Associative select", nodep->bitp(), adtypep->keyDTypep(),
                              BOTH);
            nodep->dtypeFrom(adtypep->subDTypep());
        }
    }

    virtual void visit(AstSliceSel* nodep) VL_OVERRIDE {
        // Always creates as output an unpacked array
        if (m_vup->prelim()) {
            userIterateAndNext(nodep->fromp(), WidthVP(SELF, BOTH).p());
            //
            // Array indices are always constant
            AstNodeDType* fromDtp = nodep->fromp()->dtypep()->skipRefp();
            AstUnpackArrayDType* adtypep = VN_CAST(fromDtp, UnpackArrayDType);
            if (!adtypep) {
                UINFO(1, "    Related dtype: " << fromDtp << endl);
                nodep->v3fatalSrc("Packed array reference exceeds dimension of array");
            }
            // Build new array Dtype based on the original's base type, but with new bounds
            AstNodeDType* newDtp
                = new AstUnpackArrayDType(nodep->fileline(), adtypep->subDTypep(),
                                          new AstRange(nodep->fileline(), nodep->declRange()));
            v3Global.rootp()->typeTablep()->addTypesp(newDtp);
            nodep->dtypeFrom(newDtp);

            if (!m_doGenerate) {
                // Must check bounds before adding a select that truncates the bound
                // Note we've already subtracted off LSB
                if ((nodep->declRange().hi() > adtypep->declRange().hi())
                    || nodep->declRange().lo() < adtypep->declRange().lo()) {
                    // Other simulators warn too
                    nodep->v3error("Slice selection index '" << nodep->declRange() << "'"
                                                             << " outside data type's '"
                                                             << adtypep->declRange() << "'");
                } else if ((nodep->declRange().littleEndian()
                            != adtypep->declRange().littleEndian())
                           && nodep->declRange().hi() != nodep->declRange().lo()) {
                    nodep->v3error("Slice selection '"
                                   << nodep->declRange() << "'"
                                   << " has backward indexing versus data type's '"
                                   << adtypep->declRange() << "'");
                }
            }
        }
    }

    virtual void visit(AstSelBit* nodep) VL_OVERRIDE {
        // Just a quick check as after V3Param these nodes instead are AstSel's
        userIterateAndNext(nodep->fromp(), WidthVP(CONTEXT, PRELIM).p());  // FINAL in AstSel
        userIterateAndNext(nodep->rhsp(), WidthVP(CONTEXT, PRELIM).p());  // FINAL in AstSel
        userIterateAndNext(nodep->thsp(), WidthVP(CONTEXT, PRELIM).p());  // FINAL in AstSel
        userIterateAndNext(nodep->attrp(), WidthVP(SELF, BOTH).p());
        AstNode* selp = V3Width::widthSelNoIterEdit(nodep);
        if (selp != nodep) {
            nodep = NULL;
            userIterate(selp, m_vup);
            return;
        }
        nodep->v3fatalSrc("AstSelBit should disappear after widthSel");
    }
    virtual void visit(AstSelExtract* nodep) VL_OVERRIDE {
        // Just a quick check as after V3Param these nodes instead are AstSel's
        userIterateAndNext(nodep->fromp(), WidthVP(CONTEXT, PRELIM).p());  // FINAL in AstSel
        userIterateAndNext(nodep->rhsp(), WidthVP(CONTEXT, PRELIM).p());  // FINAL in AstSel
        userIterateAndNext(nodep->thsp(), WidthVP(CONTEXT, PRELIM).p());  // FINAL in AstSel
        userIterateAndNext(nodep->attrp(), WidthVP(SELF, BOTH).p());
        AstNode* selp = V3Width::widthSelNoIterEdit(nodep);
        if (selp != nodep) {
            nodep = NULL;
            userIterate(selp, m_vup);
            return;
        }
        nodep->v3fatalSrc("AstSelExtract should disappear after widthSel");
    }
    virtual void visit(AstSelPlus* nodep) VL_OVERRIDE {
        userIterateAndNext(nodep->fromp(), WidthVP(CONTEXT, PRELIM).p());  // FINAL in AstSel
        userIterateAndNext(nodep->rhsp(), WidthVP(CONTEXT, PRELIM).p());  // FINAL in AstSel
        userIterateAndNext(nodep->thsp(), WidthVP(CONTEXT, PRELIM).p());  // FINAL in AstSel
        userIterateAndNext(nodep->attrp(), WidthVP(SELF, BOTH).p());
        AstNode* selp = V3Width::widthSelNoIterEdit(nodep);
        if (selp != nodep) {
            nodep = NULL;
            userIterate(selp, m_vup);
            return;
        }
        nodep->v3fatalSrc("AstSelPlus should disappear after widthSel");
    }
    virtual void visit(AstSelMinus* nodep) VL_OVERRIDE {
        userIterateAndNext(nodep->fromp(), WidthVP(CONTEXT, PRELIM).p());  // FINAL in AstSel
        userIterateAndNext(nodep->rhsp(), WidthVP(CONTEXT, PRELIM).p());  // FINAL in AstSel
        userIterateAndNext(nodep->thsp(), WidthVP(CONTEXT, PRELIM).p());  // FINAL in AstSel
        userIterateAndNext(nodep->attrp(), WidthVP(SELF, BOTH).p());
        AstNode* selp = V3Width::widthSelNoIterEdit(nodep);
        if (selp != nodep) {
            nodep = NULL;
            userIterate(selp, m_vup);
            return;
        }
        nodep->v3fatalSrc("AstSelMinus should disappear after widthSel");
    }

    virtual void visit(AstExtend* nodep) VL_OVERRIDE {
        // Only created by this process, so we know width from here down is correct.
    }
    virtual void visit(AstExtendS* nodep) VL_OVERRIDE {
        // Only created by this process, so we know width from here down is correct.
    }
    virtual void visit(AstConst* nodep) VL_OVERRIDE {
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
    virtual void visit(AstPast* nodep) VL_OVERRIDE {
        if (m_vup->prelim()) {
            iterateCheckSizedSelf(nodep, "LHS", nodep->exprp(), SELF, BOTH);
            nodep->dtypeFrom(nodep->exprp());
            if (nodep->ticksp()) {
                iterateCheckSizedSelf(nodep, "Ticks", nodep->ticksp(), SELF, BOTH);
                V3Const::constifyParamsEdit(nodep->ticksp());  // ticksp may change
                const AstConst* constp = VN_CAST(nodep->ticksp(), Const);
                if (!constp || constp->toSInt() < 1) {
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
    virtual void visit(AstSampled* nodep) VL_OVERRIDE {
        if (m_vup->prelim()) {
            iterateCheckSizedSelf(nodep, "LHS", nodep->exprp(), SELF, BOTH);
            nodep->dtypeFrom(nodep->exprp());
        }
    }
    virtual void visit(AstRand* nodep) VL_OVERRIDE {
        if (m_vup->prelim()) {
            nodep->dtypeSetSigned32();  // Says the spec
        }
    }
    virtual void visit(AstUnbounded* nodep) VL_OVERRIDE {
        nodep->v3error("Unsupported/illegal unbounded ('$') in this context.");
    }
    virtual void visit(AstUCFunc* nodep) VL_OVERRIDE {
        // Give it the size the user wants.
        if (m_vup && m_vup->prelim()) {
            nodep->dtypeSetLogicUnsized(32, 1, VSigning::UNSIGNED);  // We don't care
            // All arguments seek their natural sizes
            userIterateChildren(nodep, WidthVP(SELF, BOTH).p());
        }
        if (m_vup->final()) {
            AstNodeDType* expDTypep = m_vup->dtypeOverridep(nodep->dtypep());
            nodep->dtypeFrom(expDTypep);  // Assume user knows the rules; go with the flow
            if (nodep->width() > 64) {
                nodep->v3error("Unsupported: $c can't generate wider than 64 bits");
            }
        }
    }
    virtual void visit(AstCLog2* nodep) VL_OVERRIDE {
        if (m_vup->prelim()) {
            iterateCheckSizedSelf(nodep, "LHS", nodep->lhsp(), SELF, BOTH);
            nodep->dtypeSetSigned32();
        }
    }
    virtual void visit(AstPow* nodep) VL_OVERRIDE {
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
            AstNodeDType* expDTypep = m_vup->dtypeOverridep(nodep->dtypep());
            nodep->dtypeFrom(expDTypep);
            // rhs already finalized in iterate_shift_prelim
            iterateCheck(nodep, "LHS", nodep->lhsp(), SELF, FINAL, nodep->dtypep(), EXTEND_EXP);
            AstNode* newp = NULL;  // No change
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
    virtual void visit(AstPowSU* nodep) VL_OVERRIDE {
        // POWSU/SS/US only created here, dtype already determined, so
        // nothing to do in this function
        userIterateAndNext(nodep->lhsp(), WidthVP(SELF, BOTH).p());
        userIterateAndNext(nodep->rhsp(), WidthVP(SELF, BOTH).p());
    }
    virtual void visit(AstPowSS* nodep) VL_OVERRIDE {
        // POWSU/SS/US only created here, dtype already determined, so
        // nothing to do in this function
        userIterateAndNext(nodep->lhsp(), WidthVP(SELF, BOTH).p());
        userIterateAndNext(nodep->rhsp(), WidthVP(SELF, BOTH).p());
    }
    virtual void visit(AstPowUS* nodep) VL_OVERRIDE {
        // POWSU/SS/US only created here, dtype already determined, so
        // nothing to do in this function
        userIterateAndNext(nodep->lhsp(), WidthVP(SELF, BOTH).p());
        userIterateAndNext(nodep->rhsp(), WidthVP(SELF, BOTH).p());
    }
    virtual void visit(AstCountOnes* nodep) VL_OVERRIDE {
        if (m_vup->prelim()) {
            iterateCheckSizedSelf(nodep, "LHS", nodep->lhsp(), SELF, BOTH);
            // If it's a 32 bit number, we need a 6 bit number as we need to return '32'.
            int selwidth = V3Number::log2b(nodep->lhsp()->width()) + 1;
            nodep->dtypeSetLogicSized(selwidth,
                                      VSigning::UNSIGNED);  // Spec doesn't indicate if an integer
        }
    }
    virtual void visit(AstCvtPackString* nodep) VL_OVERRIDE {
        // Opaque returns, so arbitrary
        userIterateAndNext(nodep->lhsp(), WidthVP(SELF, BOTH).p());
        // Type set in constructor
    }
    virtual void visit(AstTimeImport* nodep) VL_OVERRIDE {
        // LHS is a real number in seconds
        // Need to round to time units and precision
        userIterateAndNext(nodep->lhsp(), WidthVP(SELF, BOTH).p());
        AstConst* constp = VN_CAST(nodep->lhsp(), Const);
        if (!constp || !constp->isDouble()) nodep->v3fatalSrc("Times should be doubles");
        if (nodep->timeunit().isNone()) nodep->v3fatalSrc("$time import no units");
        double time = constp->num().toDouble();
        if (v3Global.rootp()->timeprecision().isNone()) nodep->v3fatalSrc("Never set precision?");
        time /= nodep->timeunit().multiplier();
        // IEEE claims you should round to time precision here, but no simulator seems to do this
        AstConst* newp = new AstConst(nodep->fileline(), AstConst::RealDouble(), time);
        nodep->replaceWith(newp);
        VL_DO_DANGLING(nodep->deleteTree(), nodep);
    }
    virtual void visit(AstAttrOf* nodep) VL_OVERRIDE {
        AstAttrOf* oldAttr = m_attrp;
        m_attrp = nodep;
        userIterateAndNext(nodep->fromp(), WidthVP(SELF, BOTH).p());
        if (nodep->dimp()) userIterateAndNext(nodep->dimp(), WidthVP(SELF, BOTH).p());
        // Don't iterate children, don't want to lose VarRef.
        switch (nodep->attrType()) {
        case AstAttrType::VAR_BASE:
        case AstAttrType::MEMBER_BASE:
        case AstAttrType::ENUM_BASE:
            // Soon to be handled in V3LinkWidth SEL generation, under attrp() and newSubLsbOf
            break;
        case AstAttrType::DIM_DIMENSIONS:
        case AstAttrType::DIM_UNPK_DIMENSIONS: {
            UASSERT_OBJ(nodep->fromp() && nodep->fromp()->dtypep(), nodep, "Unsized expression");
            std::pair<uint32_t, uint32_t> dim = nodep->fromp()->dtypep()->dimensions(true);
            int val = (nodep->attrType() == AstAttrType::DIM_UNPK_DIMENSIONS
                           ? dim.second
                           : (dim.first + dim.second));
            nodep->replaceWith(new AstConst(nodep->fileline(), AstConst::Signed32(), val));
            VL_DO_DANGLING(nodep->deleteTree(), nodep);
            break;
        }
        case AstAttrType::DIM_BITS:
        case AstAttrType::DIM_HIGH:
        case AstAttrType::DIM_INCREMENT:
        case AstAttrType::DIM_LEFT:
        case AstAttrType::DIM_LOW:
        case AstAttrType::DIM_RIGHT:
        case AstAttrType::DIM_SIZE: {
            UASSERT_OBJ(nodep->fromp() && nodep->fromp()->dtypep(), nodep, "Unsized expression");
            if (VN_IS(nodep->fromp()->dtypep(), QueueDType)) {
                switch (nodep->attrType()) {
                case AstAttrType::DIM_SIZE: {
                    AstNode* newp = new AstCMethodHard(
                        nodep->fileline(), nodep->fromp()->unlinkFrBack(), "size", NULL);
                    newp->dtypeSetSigned32();
                    newp->didWidth(true);
                    newp->protect(false);
                    nodep->replaceWith(newp);
                    VL_DO_DANGLING(nodep->deleteTree(), nodep);
                    break;
                }
                case AstAttrType::DIM_LEFT:
                case AstAttrType::DIM_LOW: {
                    AstNode* newp = new AstConst(nodep->fileline(), AstConst::Signed32(), 0);
                    nodep->replaceWith(newp);
                    VL_DO_DANGLING(nodep->deleteTree(), nodep);
                    break;
                }
                case AstAttrType::DIM_RIGHT:
                case AstAttrType::DIM_HIGH: {
                    AstNode* sizep = new AstCMethodHard(
                        nodep->fileline(), nodep->fromp()->unlinkFrBack(), "size", NULL);
                    sizep->dtypeSetSigned32();
                    sizep->didWidth(true);
                    sizep->protect(false);
                    AstNode* newp
                        = new AstSub(nodep->fileline(), sizep,
                                     new AstConst(nodep->fileline(), AstConst::Signed32(), 1));
                    nodep->replaceWith(newp);
                    VL_DO_DANGLING(nodep->deleteTree(), nodep);
                    break;
                }
                case AstAttrType::DIM_INCREMENT: {
                    AstNode* newp = new AstConst(nodep->fileline(), AstConst::Signed32(), -1);
                    nodep->replaceWith(newp);
                    VL_DO_DANGLING(nodep->deleteTree(), nodep);
                    break;
                }
                case AstAttrType::DIM_BITS: {
                    nodep->v3error("Unsupported: $bits for queue");
                    break;
                }
                default: nodep->v3error("Unhandled attribute type");
                }
            } else {
                std::pair<uint32_t, uint32_t> dimpair
                    = nodep->fromp()->dtypep()->skipRefp()->dimensions(true);
                uint32_t msbdim = dimpair.first + dimpair.second;
                if (!nodep->dimp() || msbdim < 1) {
                    int dim = 1;
                    AstConst* newp = dimensionValue(nodep->fileline(), nodep->fromp()->dtypep(),
                                                    nodep->attrType(), dim);
                    nodep->replaceWith(newp);
                    VL_DO_DANGLING(nodep->deleteTree(), nodep);
                } else if (VN_IS(nodep->dimp(), Const)) {
                    int dim = VN_CAST(nodep->dimp(), Const)->toSInt();
                    AstConst* newp = dimensionValue(nodep->fileline(), nodep->fromp()->dtypep(),
                                                    nodep->attrType(), dim);
                    nodep->replaceWith(newp);
                    VL_DO_DANGLING(nodep->deleteTree(), nodep);
                } else {  // Need a runtime lookup table.  Yuk.
                    UASSERT_OBJ(nodep->fromp() && nodep->fromp()->dtypep(), nodep,
                                "Unsized expression");
                    AstVar* varp
                        = dimensionVarp(nodep->fromp()->dtypep(), nodep->attrType(), msbdim);
                    AstNode* dimp = nodep->dimp()->unlinkFrBack();
                    AstVarRef* varrefp = new AstVarRef(nodep->fileline(), varp, false);
                    varrefp->packagep(v3Global.rootp()->dollarUnitPkgAddp());
                    AstNode* newp = new AstArraySel(nodep->fileline(), varrefp, dimp);
                    nodep->replaceWith(newp);
                    VL_DO_DANGLING(nodep->deleteTree(), nodep);
                }
            }
            break;
        }
        case AstAttrType::TYPENAME: {
            UASSERT_OBJ(nodep->fromp(), nodep, "Unprovided expression");
            string result = nodep->fromp()->dtypep()->prettyDTypeName();
            AstNode* newp = new AstConst(nodep->fileline(), AstConst::String(), result);
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
        m_attrp = oldAttr;
    }
    virtual void visit(AstPull* nodep) VL_OVERRIDE {
        // May have select underneath, let seek natural size
        userIterateChildren(nodep, WidthVP(SELF, BOTH).p());
    }
    virtual void visit(AstText* nodep) VL_OVERRIDE {
        // Only used in CStmts which don't care....
    }

    // DTYPES
    virtual void visit(AstNodeArrayDType* nodep) VL_OVERRIDE {
        if (nodep->didWidthAndSet()) return;  // This node is a dtype & not both PRELIMed+FINALed
        if (nodep->childDTypep()) nodep->refDTypep(moveChildDTypeEdit(nodep));
        // Iterate into subDTypep() to resolve that type and update pointer.
        nodep->refDTypep(iterateEditDTypep(nodep, nodep->subDTypep()));
        // Cleanup array size
        userIterateAndNext(nodep->rangep(), WidthVP(SELF, BOTH).p());
        nodep->dtypep(nodep);  // The array itself, not subDtype
        if (VN_IS(nodep, UnpackArrayDType)) {
            // Historically array elements have width of the ref type not the full array
            nodep->widthFromSub(nodep->subDTypep());
        } else {
            int width = nodep->subDTypep()->width() * nodep->rangep()->elementsConst();
            nodep->widthForce(width, width);
        }
        UINFO(4, "dtWidthed " << nodep << endl);
    }
    virtual void visit(AstAssocArrayDType* nodep) VL_OVERRIDE {
        if (nodep->didWidthAndSet()) return;  // This node is a dtype & not both PRELIMed+FINALed
        if (nodep->childDTypep()) nodep->refDTypep(moveChildDTypeEdit(nodep));
        if (nodep->keyChildDTypep()) {
            nodep->keyDTypep(moveDTypeEdit(nodep, nodep->keyChildDTypep()));
        }
        // Iterate into subDTypep() to resolve that type and update pointer.
        nodep->refDTypep(iterateEditDTypep(nodep, nodep->subDTypep()));
        nodep->keyDTypep(iterateEditDTypep(nodep, nodep->keyDTypep()));
        nodep->dtypep(nodep);  // The array itself, not subDtype
        UINFO(4, "dtWidthed " << nodep << endl);
    }
    virtual void visit(AstDynArrayDType* nodep) VL_OVERRIDE {
        if (nodep->didWidthAndSet()) return;  // This node is a dtype & not both PRELIMed+FINALed
        if (nodep->childDTypep()) nodep->refDTypep(moveChildDTypeEdit(nodep));
        // Iterate into subDTypep() to resolve that type and update pointer.
        nodep->refDTypep(iterateEditDTypep(nodep, nodep->subDTypep()));
        nodep->dtypep(nodep);  // The array itself, not subDtype
        UINFO(4, "dtWidthed " << nodep << endl);
    }
    virtual void visit(AstQueueDType* nodep) VL_OVERRIDE {
        if (nodep->didWidthAndSet()) return;  // This node is a dtype & not both PRELIMed+FINALed
        if (nodep->childDTypep()) nodep->refDTypep(moveChildDTypeEdit(nodep));
        // Iterate into subDTypep() to resolve that type and update pointer.
        nodep->refDTypep(iterateEditDTypep(nodep, nodep->subDTypep()));
        nodep->dtypep(nodep);  // The array itself, not subDtype
        if (VN_IS(nodep->boundp(), Unbounded)) {
            nodep->boundp()->unlinkFrBack()->deleteTree();  // NULL will represent unbounded
        }
        UINFO(4, "dtWidthed " << nodep << endl);
    }
    virtual void visit(AstUnsizedArrayDType* nodep) VL_OVERRIDE {
        if (nodep->didWidthAndSet()) return;  // This node is a dtype & not both PRELIMed+FINALed
        if (nodep->childDTypep()) nodep->refDTypep(moveChildDTypeEdit(nodep));
        // Iterate into subDTypep() to resolve that type and update pointer.
        nodep->refDTypep(iterateEditDTypep(nodep, nodep->subDTypep()));
        // Cleanup array size
        nodep->dtypep(nodep);  // The array itself, not subDtype
        UINFO(4, "dtWidthed " << nodep << endl);
    }
    virtual void visit(AstBasicDType* nodep) VL_OVERRIDE {
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
    virtual void visit(AstConstDType* nodep) VL_OVERRIDE {
        if (nodep->didWidthAndSet()) return;  // This node is a dtype & not both PRELIMed+FINALed
        // Move any childDTypep to instead be in global AstTypeTable.
        // This way if this node gets deleted and some other dtype points to it
        // it won't become a dead pointer.  This doesn't change the object pointed to.
        if (nodep->childDTypep()) nodep->refDTypep(moveChildDTypeEdit(nodep));
        // Iterate into subDTypep() to resolve that type and update pointer.
        nodep->refDTypep(iterateEditDTypep(nodep, nodep->subDTypep()));
        userIterateChildren(nodep, NULL);
        nodep->dtypep(nodep);  // Should already be set, but be clear it's not the subDType
        nodep->widthFromSub(nodep->subDTypep());
        UINFO(4, "dtWidthed " << nodep << endl);
    }
    virtual void visit(AstRefDType* nodep) VL_OVERRIDE {
        if (nodep->doingWidth()) {  // Early exit if have circular parameter definition
            nodep->v3error("Typedef's type is circular: " << nodep->prettyName());
            nodep->dtypeSetLogicBool();
            nodep->doingWidth(false);
            return;
        }
        if (nodep->didWidthAndSet()) return;  // This node is a dtype & not both PRELIMed+FINALed
        nodep->doingWidth(true);
        if (nodep->typeofp()) {  // type(typeofp_expression)
            // Type comes from expression's type
            userIterateAndNext(nodep->typeofp(), WidthVP(SELF, BOTH).p());
            AstNode* typeofp = nodep->typeofp();
            nodep->refDTypep(typeofp->dtypep());
            VL_DO_DANGLING(typeofp->unlinkFrBack()->deleteTree(), typeofp);
            // We had to use AstRefDType for this construct as pointers to this type
            // in type table are still correct (which they wouldn't be if we replaced the node)
        }
        userIterateChildren(nodep, NULL);
        if (nodep->subDTypep()) nodep->refDTypep(iterateEditDTypep(nodep, nodep->subDTypep()));
        // Effectively nodep->dtypeFrom(nodep->dtypeSkipRefp());
        // But might be recursive, so instead manually recurse into the referenced type
        UASSERT_OBJ(nodep->defp(), nodep, "Unlinked");
        nodep->dtypeFrom(nodep->defp());
        userIterate(nodep->defp(), NULL);
        nodep->widthFromSub(nodep->subDTypep());
        UINFO(4, "dtWidthed " << nodep << endl);
        nodep->doingWidth(false);
    }
    virtual void visit(AstTypedef* nodep) VL_OVERRIDE {
        if (nodep->didWidthAndSet()) return;  // This node is a dtype & not both PRELIMed+FINALed
        if (nodep->childDTypep()) nodep->dtypep(moveChildDTypeEdit(nodep));
        userIterateChildren(nodep, NULL);
        nodep->dtypep(iterateEditDTypep(nodep, nodep->subDTypep()));
    }
    virtual void visit(AstParamTypeDType* nodep) VL_OVERRIDE {
        if (nodep->didWidthAndSet()) return;  // This node is a dtype & not both PRELIMed+FINALed
        if (nodep->childDTypep()) nodep->dtypep(moveChildDTypeEdit(nodep));
        userIterateChildren(nodep, NULL);
        nodep->dtypep(iterateEditDTypep(nodep, nodep->subDTypep()));
        nodep->widthFromSub(nodep->subDTypep());
    }
    virtual void visit(AstCastParse* nodep) VL_OVERRIDE {
        // nodep->dtp could be data type, or a primary_constant
        // Don't iterate lhsp, will deal with that once convert the type
        V3Const::constifyParamsEdit(nodep->dtp());  // itemp may change
        if (AstConst* constp = VN_CAST(nodep->dtp(), Const)) {
            constp->unlinkFrBack();
            AstNode* newp
                = new AstCastSize(nodep->fileline(), nodep->lhsp()->unlinkFrBack(), constp);
            nodep->replaceWith(newp);
            VL_DO_DANGLING(pushDeletep(nodep), nodep);
            userIterate(newp, m_vup);
        } else {
            nodep->v3error("Unsupported: Cast to " << nodep->dtp()->prettyTypeName());
            nodep->replaceWith(nodep->lhsp()->unlinkFrBack());
        }
    }
    virtual void visit(AstCast* nodep) VL_OVERRIDE {
        if (nodep->childDTypep()) nodep->dtypep(moveChildDTypeEdit(nodep));
        nodep->dtypep(iterateEditDTypep(nodep, nodep->dtypep()));
        // if (debug()) nodep->dumpTree(cout, "  CastPre: ");
        userIterateAndNext(nodep->lhsp(), WidthVP(SELF, BOTH).p());
        // When more general casts are supported, the cast elimination will be done later.
        // For now, replace it ASAP, so widthing can propagate easily
        // The cast may change signing, but we don't know the sign yet.  Make it so.
        // Note we don't sign lhsp() that would make the algorithm O(n^2) if lots of casting.
        AstBasicDType* basicp = nodep->dtypep()->basicp();
        UASSERT_OBJ(basicp, nodep, "Unimplemented: Casting non-simple data type");
        // When implement more complicated types need to convert childDTypep to
        // dtypep() not as a child
        if (!basicp->isDouble() && !nodep->lhsp()->isDouble()) {
            // Note widthCheckSized might modify nodep->lhsp()
            AstNodeDType* subDTypep = nodep->findLogicDType(nodep->width(), nodep->width(),
                                                            nodep->lhsp()->dtypep()->numeric());
            widthCheckSized(nodep, "Cast", nodep->lhsp(), subDTypep, EXTEND_EXP, false);
        }
        AstNode* newp = nodep->lhsp()->unlinkFrBack();
        if (basicp->isDouble() && !newp->isDouble()) {
            newp = new AstIToRD(nodep->fileline(), newp);
        } else if (!basicp->isDouble() && newp->isDouble()) {
            if (basicp->isSigned()) {
                newp = new AstRToIRoundS(nodep->fileline(), newp);
            } else {
                newp = new AstUnsigned(nodep->fileline(), new AstRToIS(nodep->fileline(), newp));
            }
        } else if (basicp->isSigned() && !newp->isSigned()) {
            newp = new AstSigned(nodep->fileline(), newp);
        } else if (!basicp->isSigned() && newp->isSigned()) {
            newp = new AstUnsigned(nodep->fileline(), newp);
        } else {
            // newp = newp;  // Can just remove cast
        }
        nodep->replaceWith(newp);
        VL_DO_DANGLING(pushDeletep(nodep), nodep);
        // if (debug()) newp->dumpTree(cout, "  CastOut: ");
    }
    virtual void visit(AstCastSize* nodep) VL_OVERRIDE {
        // IEEE: Signedness of result is same as self-determined signedness
        // However, the result is same as BITSEL, so we do not sign extend the LHS
        UASSERT_OBJ(VN_IS(nodep->rhsp(), Const), nodep, "Unsupported: Non-const cast of size");
        // if (debug()) nodep->dumpTree(cout, "  CastSizePre: ");
        if (m_vup->prelim()) {
            int width = VN_CAST(nodep->rhsp(), Const)->toSInt();
            if (width < 1) {
                nodep->v3error("Size-changing cast to zero or negative size");
                width = 1;
            }
            userIterateAndNext(nodep->lhsp(), WidthVP(SELF, PRELIM).p());
            AstBasicDType* underDtp = VN_CAST(nodep->lhsp()->dtypep(), BasicDType);
            if (!underDtp) underDtp = nodep->lhsp()->dtypep()->basicp();
            if (!underDtp) {
                nodep->v3error("Unsupported: Size-changing cast on non-basic data type");
                underDtp = VN_CAST(nodep->findLogicBoolDType(), BasicDType);
            }
            // A cast propagates its size to the lower expression and is included in the maximum
            // width, so 23'(1'b1 + 1'b1) uses 23-bit math, but 1'(2'h2 * 2'h1) uses two-bit math.
            // However the output width is exactly that requested.
            // So two steps, first do the calculation's width (max of the two widths)
            {
                int calcWidth = std::max(width, underDtp->width());
                AstNodeDType* calcDtp
                    = (underDtp->isFourstate()
                           ? nodep->findLogicDType(calcWidth, calcWidth, underDtp->numeric())
                           : nodep->findBitDType(calcWidth, calcWidth, underDtp->numeric()));
                nodep->dtypep(calcDtp);
                // We ignore warnings as that is sort of the point of a cast
                iterateCheck(nodep, "Cast expr", nodep->lhsp(), CONTEXT, FINAL, calcDtp,
                             EXTEND_EXP, false);
            }
            // if (debug()) nodep->dumpTree(cout, "  CastSizeClc: ");
            // Next step, make the proper output width
            {
                AstNodeDType* outDtp
                    = (underDtp->isFourstate()
                           ? nodep->findLogicDType(width, width, underDtp->numeric())
                           : nodep->findBitDType(width, width, underDtp->numeric()));
                nodep->dtypep(outDtp);
                // We ignore warnings as that is sort of the point of a cast
                widthCheckSized(nodep, "Cast expr", nodep->lhsp(), outDtp, EXTEND_EXP, false);
            }
        }
        if (m_vup->final()) {
            // CastSize not needed once sizes determined
            AstNode* underp = nodep->lhsp()->unlinkFrBack();
            nodep->replaceWith(underp);
            VL_DO_DANGLING(pushDeletep(nodep), nodep);
        }
        // if (debug()) nodep->dumpTree(cout, "  CastSizeOut: ");
    }
    virtual void visit(AstVar* nodep) VL_OVERRIDE {
        // if (debug()) nodep->dumpTree(cout, "  InitPre: ");
        // Must have deterministic constant width
        // We can't skip this step when width()!=0, as creating a AstVar
        // with non-constant range gets size 1, not size 0.  So use didWidth().
        if (nodep->didWidth()) return;
        if (nodep->doingWidth()) {  // Early exit if have circular parameter definition
            UASSERT_OBJ(nodep->valuep(), nodep, "circular, but without value");
            nodep->v3error("Variable's initial value is circular: " << nodep->prettyNameQ());
            pushDeletep(nodep->valuep()->unlinkFrBack());
            nodep->valuep(new AstConst(nodep->fileline(), AstConst::LogicTrue()));
            nodep->dtypeFrom(nodep->valuep());
            nodep->didWidth(true);
            return;
        }
        nodep->doingWidth(true);
        // Make sure dtype is sized
        if (nodep->childDTypep()) nodep->dtypep(moveChildDTypeEdit(nodep));
        nodep->dtypep(iterateEditDTypep(nodep, nodep->dtypep()));
        UASSERT_OBJ(nodep->dtypep(), nodep, "No dtype determined for var");
        if (AstUnsizedArrayDType* unsizedp = VN_CAST(nodep->dtypeSkipRefp(), UnsizedArrayDType)) {
            if (!(m_ftaskp && m_ftaskp->dpiImport())) {
                UINFO(9, "Unsized becomes dynamic array " << nodep << endl);
                AstDynArrayDType* newp
                    = new AstDynArrayDType(unsizedp->fileline(), unsizedp->subDTypep());
                nodep->dtypep(newp);
                v3Global.rootp()->typeTablep()->addTypesp(newp);
            }
        } else if (nodep->isIO()
                   && !(VN_IS(nodep->dtypeSkipRefp(), BasicDType)
                        || VN_IS(nodep->dtypeSkipRefp(), NodeArrayDType)
                        || VN_IS(nodep->dtypeSkipRefp(), NodeUOrStructDType))) {
            nodep->v3error("Unsupported: Inputs and outputs must be simple data types");
        }
        if (VN_IS(nodep->dtypep()->skipRefToConstp(), ConstDType)) nodep->isConst(true);
        // Parameters if implicit untyped inherit from what they are assigned to
        AstBasicDType* bdtypep = VN_CAST(nodep->dtypep(), BasicDType);
        bool didchk = false;
        bool implicitParam = nodep->isParam() && bdtypep && bdtypep->implicit();
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
                    AstBasicDType* valueBdtypep = nodep->valuep()->dtypep()->basicp();
                    bool issigned = false;
                    if (bdtypep->isNosign()) {
                        if (valueBdtypep && valueBdtypep->isSigned()) issigned = true;
                    } else {
                        issigned = bdtypep->isSigned();
                    }
                    if (nodep->valuep()->dtypep()->widthSized()) {
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
                        nodep->dtypep(nodep->findLogicRangeDType(VNumRange(0, 0, false),
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
    virtual void visit(AstNodeVarRef* nodep) VL_OVERRIDE {
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
            userIterate(nodep->varp(), NULL);
        }
        // if (debug()>=9) { nodep->dumpTree(cout, "  VRin  ");
        //  nodep->varp()->dumpTree(cout, " forvar "); }
        // Note genvar's are also entered as integers
        nodep->dtypeFrom(nodep->varp());
        if (VN_IS(nodep->backp(), NodeAssign) && nodep->lvalue()) {  // On LHS
            UASSERT_OBJ(nodep->dtypep(), nodep, "LHS var should be dtype completed");
        }
        // if (debug() >= 9) nodep->dumpTree(cout, "  VRout ");
        if (nodep->lvalue() && nodep->varp()->direction() == VDirection::CONSTREF) {
            nodep->v3error("Assigning to const ref variable: " << nodep->prettyNameQ());
        } else if (nodep->lvalue() && nodep->varp()->isConst() && !m_paramsOnly && !m_initialp) {
            // Too loose, but need to allow our generated first assignment
            // Move this to a property of the AstInitial block
            nodep->v3error("Assigning to const variable: " << nodep->prettyNameQ());
        }
        nodep->didWidth(true);
    }

    virtual void visit(AstEnumDType* nodep) VL_OVERRIDE {
        if (nodep->didWidthAndSet()) return;  // This node is a dtype & not both PRELIMed+FINALed
        UINFO(5, "  ENUMDTYPE " << nodep << endl);
        if (nodep->childDTypep()) nodep->refDTypep(moveChildDTypeEdit(nodep));
        nodep->refDTypep(iterateEditDTypep(nodep, nodep->subDTypep()));
        nodep->dtypep(nodep);
        nodep->widthFromSub(nodep->subDTypep());
        // Assign widths
        userIterateAndNext(nodep->itemsp(), WidthVP(nodep->dtypep(), BOTH).p());
        // Assign missing values
        V3Number num(nodep, nodep->width(), 0);
        V3Number one(nodep, nodep->width(), 1);
        std::map<V3Number, AstEnumItem*> inits;
        for (AstEnumItem* itemp = nodep->itemsp(); itemp;
             itemp = VN_CAST(itemp->nextp(), EnumItem)) {
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
                if (num.isEqZero() && itemp != nodep->itemsp())
                    itemp->v3error("Enum value illegally wrapped around (IEEE 1800-2017 6.19)");
                if (num.isFourState())
                    itemp->v3error("Enum value that is unassigned cannot follow value with X/Zs "
                                   "(IEEE 1800-2017 6.19)");
                if (!nodep->dtypep()->basicp()
                    && !nodep->dtypep()->basicp()->keyword().isIntNumeric()) {
                    itemp->v3error("Enum names without values only allowed on numeric types");
                    // as can't +1 to resolve them.
                }
                itemp->valuep(new AstConst(itemp->fileline(), num));
            }

            AstConst* constp = VN_CAST(itemp->valuep(), Const);
            if (constp->num().isFourState() && nodep->dtypep()->basicp()
                && !nodep->dtypep()->basicp()->isFourstate())
                itemp->v3error("Enum value with X/Zs cannot be assigned to non-fourstate type "
                               "(IEEE 1800-2017 6.19)");
            num.opAssign(constp->num());
            // Look for duplicates
            if (inits.find(num) != inits.end()) {  // IEEE says illegal
                AstNode* otherp = inits.find(num)->second;
                itemp->v3error("Overlapping enumeration value: "
                               << itemp->prettyNameQ() << endl
                               << itemp->warnContextPrimary() << endl
                               << otherp->warnOther() << "... Location of original declaration\n"
                               << otherp->warnContextSecondary());
            } else {
                inits.insert(make_pair(num, itemp));
            }
            num.opAdd(one, constp->num());
        }
    }
    virtual void visit(AstEnumItem* nodep) VL_OVERRIDE {
        UINFO(5, "   ENUMITEM " << nodep << endl);
        AstNodeDType* vdtypep = m_vup->dtypep();
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
    virtual void visit(AstEnumItemRef* nodep) VL_OVERRIDE {
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
    virtual void visit(AstInitItem* nodep) VL_OVERRIDE {  //
        userIterateChildren(nodep, m_vup);
    }
    virtual void visit(AstInitArray* nodep) VL_OVERRIDE {
        // InitArray has type of the array; children are array values
        if (m_vup->prelim()) {  // First stage evaluation
            AstNodeDType* vdtypep = m_vup->dtypep();
            UASSERT_OBJ(vdtypep, nodep, "InitArray type not assigned by AstPattern/Var visitor");
            nodep->dtypep(vdtypep);
            if (AstNodeArrayDType* arrayp = VN_CAST(vdtypep->skipRefp(), NodeArrayDType)) {
                userIterateChildren(nodep, WidthVP(arrayp->subDTypep(), BOTH).p());
            } else {
                nodep->v3fatalSrc("InitArray on non-array");
            }
        }
    }
    virtual void visit(AstInside* nodep) VL_OVERRIDE {
        userIterateAndNext(nodep->exprp(), WidthVP(CONTEXT, PRELIM).p());
        for (AstNode *nextip, *itemp = nodep->itemsp(); itemp; itemp = nextip) {
            nextip = itemp->nextp();  // Prelim may cause the node to get replaced
            VL_DO_DANGLING(userIterate(itemp, WidthVP(CONTEXT, PRELIM).p()), itemp);
        }
        // Take width as maximum across all items
        int width = nodep->exprp()->width();
        int mwidth = nodep->exprp()->widthMin();
        for (AstNode* itemp = nodep->itemsp(); itemp; itemp = itemp->nextp()) {
            width = std::max(width, itemp->width());
            mwidth = std::max(mwidth, itemp->widthMin());
        }
        // Apply width
        AstNodeDType* subDTypep
            = nodep->findLogicDType(width, mwidth, nodep->exprp()->dtypep()->numeric());
        iterateCheck(nodep, "Inside expression", nodep->exprp(), CONTEXT, FINAL, subDTypep,
                     EXTEND_EXP);
        for (AstNode* itemp = nodep->itemsp(); itemp; itemp = itemp->nextp()) {
            iterateCheck(nodep, "Inside Item", itemp, CONTEXT, FINAL, subDTypep, EXTEND_EXP);
        }
        nodep->dtypeSetLogicBool();
        if (debug() >= 9) nodep->dumpTree(cout, "-inside-in: ");
        // Now rip out the inside and replace with simple math
        AstNode* newp = NULL;
        for (AstNode *nextip, *itemp = nodep->itemsp(); itemp; itemp = nextip) {
            nextip = itemp->nextp();  // Will be unlinking
            AstNode* inewp;
            if (AstInsideRange* irangep = VN_CAST(itemp, InsideRange)) {
                // Similar logic in V3Case
                inewp = irangep->newAndFromInside(nodep->exprp(), irangep->lhsp()->unlinkFrBack(),
                                                  irangep->rhsp()->unlinkFrBack());
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
        if (!newp) newp = new AstConst(nodep->fileline(), AstConst::LogicFalse());
        if (debug() >= 9) newp->dumpTree(cout, "-inside-out: ");
        nodep->replaceWith(newp);
        VL_DO_DANGLING(pushDeletep(nodep), nodep);
    }
    virtual void visit(AstInsideRange* nodep) VL_OVERRIDE {
        // Just do each side; AstInside will rip these nodes out later
        userIterateAndNext(nodep->lhsp(), m_vup);
        userIterateAndNext(nodep->rhsp(), m_vup);
        nodep->dtypeFrom(nodep->lhsp());
    }

    virtual void visit(AstIfaceRefDType* nodep) VL_OVERRIDE {
        if (nodep->didWidthAndSet()) return;  // This node is a dtype & not both PRELIMed+FINALed
        UINFO(5, "   IFACEREF " << nodep << endl);
        userIterateChildren(nodep, m_vup);
        nodep->dtypep(nodep);
        nodep->widthForce(1, 1);  // Not really relevant
        UINFO(4, "dtWidthed " << nodep << endl);
    }
    virtual void visit(AstNodeUOrStructDType* nodep) VL_OVERRIDE {
        if (nodep->didWidthAndSet()) return;  // This node is a dtype & not both PRELIMed+FINALed
        UINFO(5, "   NODECLASS " << nodep << endl);
        // if (debug() >= 9) nodep->dumpTree("-class-in--");
        if (!nodep->packed()) {
            nodep->v3warn(UNPACKED, "Unsupported: Unpacked struct/union");
            if (!v3Global.opt.structsPacked()) {
                nodep->v3warn(UNPACKED, "Unsupported: --no-structs-packed");
            }
        }
        userIterateChildren(nodep, NULL);  // First size all members
        nodep->repairMemberCache();
        // Determine bit assignments and width
        nodep->dtypep(nodep);
        int lsb = 0;
        int width = 0;
        nodep->isFourstate(false);
        // MSB is first, so go backwards
        AstMemberDType* itemp;
        for (itemp = nodep->membersp(); itemp && itemp->nextp();
             itemp = VN_CAST(itemp->nextp(), MemberDType)) {}
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
    virtual void visit(AstClass* nodep) VL_OVERRIDE {
        if (nodep->didWidthAndSet()) return;
        userIterateChildren(nodep, NULL);  // First size all members
        nodep->repairCache();
    }
    virtual void visit(AstClassExtends* nodep) VL_OVERRIDE {
        if (nodep->didWidthAndSet()) return;
        if (nodep->childDTypep()) {
            nodep->dtypep(moveChildDTypeEdit(nodep));  // data_type '{ pattern }
        }
        nodep->v3error("Unsupported: class extends");  // Member/meth access breaks
        userIterateChildren(nodep, NULL);
    }
    virtual void visit(AstMemberDType* nodep) VL_OVERRIDE {
        if (nodep->didWidthAndSet()) return;  // This node is a dtype & not both PRELIMed+FINALed
        if (nodep->childDTypep()) nodep->refDTypep(moveChildDTypeEdit(nodep));
        // Iterate into subDTypep() to resolve that type and update pointer.
        nodep->refDTypep(iterateEditDTypep(nodep, nodep->subDTypep()));
        nodep->dtypep(nodep);  // The member itself, not subDtype
        nodep->widthFromSub(nodep->subDTypep());
    }
    virtual void visit(AstMemberSel* nodep) VL_OVERRIDE {
        UINFO(5, "   MEMBERSEL " << nodep << endl);
        if (debug() >= 9) nodep->dumpTree("-mbs-in: ");
        userIterateChildren(nodep, WidthVP(SELF, BOTH).p());
        if (debug() >= 9) nodep->dumpTree("-mbs-ic: ");
        // Find the fromp dtype - should be a class
        if (!nodep->fromp()->dtypep()) nodep->fromp()->v3fatalSrc("Unlinked data type");
        AstNodeDType* fromDtp = nodep->fromp()->dtypep()->skipRefToEnump();
        UINFO(9, "     from dt " << fromDtp << endl);
        if (AstNodeUOrStructDType* adtypep = VN_CAST(fromDtp, NodeUOrStructDType)) {
            if (memberSelStruct(nodep, adtypep)) return;
        } else if (AstClassRefDType* adtypep = VN_CAST(fromDtp, ClassRefDType)) {
            if (AstNode* foundp = memberSelClass(nodep, adtypep)) {
                if (AstVar* varp = VN_CAST(foundp, Var)) {
                    nodep->dtypep(foundp->dtypep());
                    nodep->varp(varp);
                    return;
                }
                if (AstEnumItemRef* adfoundp = VN_CAST(foundp, EnumItemRef)) {
                    nodep->replaceWith(adfoundp->cloneTree(false));
                    return;
                }
                UINFO(1, "found object " << foundp << endl);
                nodep->v3fatalSrc("MemberSel of non-variable\n"
                                  << nodep->warnContextPrimary() << endl
                                  << foundp->warnOther() << "... Location of found object\n"
                                  << foundp->warnContextSecondary());
            }
        } else if (VN_IS(fromDtp, EnumDType)  //
                   || VN_IS(fromDtp, AssocArrayDType)  //
                   || VN_IS(fromDtp, DynArrayDType)  //
                   || VN_IS(fromDtp, QueueDType)  //
                   || VN_IS(fromDtp, BasicDType)) {
            // Method call on enum without following parenthesis, e.g. "ENUM.next"
            // Convert this into a method call, and let that visitor figure out what to do next
            AstNode* newp = new AstMethodCall(nodep->fileline(), nodep->fromp()->unlinkFrBack(),
                                              nodep->name(), NULL);
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
        nodep->replaceWith(new AstConst(nodep->fileline(), AstConst::LogicFalse()));
        VL_DO_DANGLING(pushDeletep(nodep), nodep);
    }
    AstNode* memberSelClass(AstMemberSel* nodep, AstClassRefDType* adtypep) {
        // Returns node if ok
        // No need to width-resolve the class, as it was done when we did the child
        AstClass* first_classp = adtypep->classp();
        UASSERT_OBJ(first_classp, nodep, "Unlinked");
        for (AstClass* classp = first_classp; classp;) {
            if (AstNode* foundp = classp->findMember(nodep->name())) return foundp;
            classp = classp->extendsp() ? classp->extendsp()->classp() : NULL;
        }
        VSpellCheck speller;
        for (AstClass* classp = first_classp; classp;) {
            for (AstNode* itemp = classp->membersp(); itemp; itemp = itemp->nextp()) {
                if (VN_IS(itemp, Var) || VN_IS(itemp, EnumItemRef)) {
                    speller.pushCandidate(itemp->prettyName());
                }
            }
            classp = classp->extendsp() ? classp->extendsp()->classp() : NULL;
        }
        string suggest = speller.bestCandidateMsg(nodep->prettyName());
        nodep->v3error(
            "Member " << nodep->prettyNameQ() << " not found in class "
                      << first_classp->prettyNameQ() << "\n"
                      << (suggest.empty() ? "" : nodep->fileline()->warnMore() + suggest));
        return NULL;  // Caller handles error
    }
    bool memberSelStruct(AstMemberSel* nodep, AstNodeUOrStructDType* adtypep) {
        // Returns true if ok
        if (AstMemberDType* memberp = adtypep->findMember(nodep->name())) {
            if (m_attrp) {  // Looking for the base of the attribute
                nodep->dtypep(memberp);
                UINFO(9, "   MEMBERSEL(attr) -> " << nodep << endl);
                UINFO(9, "           dt-> " << nodep->dtypep() << endl);
            } else {
                AstSel* newp = new AstSel(nodep->fileline(), nodep->fromp()->unlinkFrBack(),
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

    virtual void visit(AstCMethodHard* nodep) VL_OVERRIDE {
        // Never created before V3Width, so no need to redo it
        UASSERT_OBJ(nodep->dtypep(), nodep, "CMETHODCALLs should have already been sized");
    }

    virtual void visit(AstMethodCall* nodep) VL_OVERRIDE {
        UINFO(5, "   METHODCALL " << nodep << endl);
        if (nodep->didWidth()) return;
        if (debug() >= 9) nodep->dumpTree("-mts-in: ");
        // Should check types the method requires, but at present we don't do much
        userIterate(nodep->fromp(), WidthVP(SELF, BOTH).p());
        for (AstArg* argp = VN_CAST(nodep->pinsp(), Arg); argp;
             argp = VN_CAST(argp->nextp(), Arg)) {
            if (argp->exprp()) userIterate(argp->exprp(), WidthVP(SELF, BOTH).p());
        }
        // Find the fromp dtype - should be a class
        UASSERT_OBJ(nodep->fromp() && nodep->fromp()->dtypep(), nodep, "Unsized expression");
        AstNodeDType* fromDtp = nodep->fromp()->dtypep()->skipRefToEnump();
        AstBasicDType* basicp = fromDtp ? fromDtp->basicp() : NULL;
        UINFO(9, "     from dt " << fromDtp << endl);
        if (AstEnumDType* adtypep = VN_CAST(fromDtp, EnumDType)) {
            methodCallEnum(nodep, adtypep);
        } else if (AstAssocArrayDType* adtypep = VN_CAST(fromDtp, AssocArrayDType)) {
            methodCallAssoc(nodep, adtypep);
        } else if (AstDynArrayDType* adtypep = VN_CAST(fromDtp, DynArrayDType)) {
            methodCallDyn(nodep, adtypep);
        } else if (AstQueueDType* adtypep = VN_CAST(fromDtp, QueueDType)) {
            methodCallQueue(nodep, adtypep);
        } else if (AstClassRefDType* adtypep = VN_CAST(fromDtp, ClassRefDType)) {
            methodCallClass(nodep, adtypep);
        } else if (AstUnpackArrayDType* adtypep = VN_CAST(fromDtp, UnpackArrayDType)) {
            methodCallUnpack(nodep, adtypep);
        } else if (basicp && basicp->isEventValue()) {
            methodCallEvent(nodep, basicp);
        } else if (basicp && basicp->isString()) {
            methodCallString(nodep, basicp);
        } else {
            nodep->v3error("Unsupported: Member call on object '"
                           << nodep->fromp()->prettyTypeName() << "' which is a '"
                           << nodep->fromp()->dtypep()->prettyTypeName() << "'");
        }
    }
    void methodOkArguments(AstMethodCall* nodep, int minArg, int maxArg) {
        int narg = 0;
        for (AstNode* argp = nodep->pinsp(); argp; argp = argp->nextp()) {
            ++narg;
            UASSERT_OBJ(VN_IS(argp, Arg), nodep, "Method arg without Arg type");
        }
        bool ok = (narg >= minArg) && (narg <= maxArg);
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
            AstConst* newp = NULL;
            methodOkArguments(nodep, 0, 0);
            if (nodep->name() == "num") {
                int items = 0;
                for (AstNode* itemp = adtypep->itemsp(); itemp; itemp = itemp->nextp()) ++items;
                newp = new AstConst(nodep->fileline(), AstConst::Signed32(), items);
            } else if (nodep->name() == "first") {
                AstEnumItem* itemp = adtypep->itemsp();
                if (!itemp) {
                    newp = new AstConst(nodep->fileline(), AstConst::Signed32(),
                                        0);  // Spec doesn't say what to do
                } else {
                    newp = VN_CAST(itemp->valuep()->cloneTree(false), Const);  // A const
                }
            } else if (nodep->name() == "last") {
                AstEnumItem* itemp = adtypep->itemsp();
                while (itemp && itemp->nextp()) itemp = VN_CAST(itemp->nextp(), EnumItem);
                if (!itemp) {
                    newp = new AstConst(nodep->fileline(), AstConst::Signed32(),
                                        0);  // Spec doesn't say what to do
                } else {
                    newp = VN_CAST(itemp->valuep()->cloneTree(false), Const);  // A const
                }
            }
            UASSERT_OBJ(newp, nodep, "Enum method (perhaps enum item) not const");
            newp->fileline(nodep->fileline());  // Use method's filename/line number to be clearer;
                                                // may have warning disables
            nodep->replaceWith(newp);
            VL_DO_DANGLING(pushDeletep(nodep), nodep);
        } else if (nodep->name() == "name" || nodep->name() == "next" || nodep->name() == "prev") {
            AstAttrType attrType;
            if (nodep->name() == "name") {
                attrType = AstAttrType::ENUM_NAME;
            } else if (nodep->name() == "next") {
                attrType = AstAttrType::ENUM_NEXT;
            } else if (nodep->name() == "prev") {
                attrType = AstAttrType::ENUM_PREV;
            } else {
                nodep->v3fatalSrc("Bad case");
            }

            if (nodep->name() == "name") {
                methodOkArguments(nodep, 0, 0);
            } else if (nodep->pinsp() && !(VN_IS(VN_CAST(nodep->pinsp(), Arg)->exprp(), Const))) {
                nodep->pinsp()->v3fatalSrc("Unsupported: enum next/prev with non-const argument");
            } else if (nodep->pinsp()
                       && !(VN_IS(VN_CAST(nodep->pinsp(), Arg)->exprp(), Const)
                            && VN_CAST(VN_CAST(nodep->pinsp(), Arg)->exprp(), Const)->toUInt() == 1
                            && !nodep->pinsp()->nextp())) {
                // Unroll of enumVar.next(k) to enumVar.next(1).next(k - 1)
                AstMethodCall* clonep = nodep->cloneTree(false);
                VN_CAST(VN_CAST(clonep->pinsp(), Arg)->exprp(), Const)->num().setLong(1);
                uint32_t stepWidth
                    = VN_CAST(VN_CAST(nodep->pinsp(), Arg)->exprp(), Const)->toUInt();
                AstConst* constp = new AstConst(nodep->fileline(), stepWidth - 1);
                AstArg* argp = new AstArg(nodep->fileline(), "", constp);
                AstMethodCall* newp
                    = new AstMethodCall(nodep->fileline(), clonep, nodep->name(), argp);
                nodep->replaceWith(newp);
                VL_DO_DANGLING(nodep->deleteTree(), nodep);
                return;
            }
            // Need a runtime lookup table.  Yuk.
            // Most enums unless overridden are 32 bits, so we size array
            // based on max enum value used.
            // Ideally we would have a fast algorithm when a number is
            // of small width and complete and so can use an array, and
            // a map for when the value is many bits and sparse.
            uint64_t msbdim = 0;
            {
                for (AstEnumItem* itemp = adtypep->itemsp(); itemp;
                     itemp = VN_CAST(itemp->nextp(), EnumItem)) {
                    const AstConst* vconstp = VN_CAST(itemp->valuep(), Const);
                    UASSERT_OBJ(vconstp, nodep, "Enum item without constified value");
                    if (vconstp->toUQuad() >= msbdim) msbdim = vconstp->toUQuad();
                }
                if (adtypep->itemsp()->width() > 64 || msbdim >= (1 << 16)) {
                    nodep->v3error("Unsupported: enum next/prev method on enum with > 10 bits");
                    return;
                }
            }
            int selwidth = V3Number::log2b(msbdim) + 1;  // Width to address a bit
            AstVar* varp = enumVarp(adtypep, attrType, (VL_ULL(1) << selwidth) - 1);
            AstVarRef* varrefp = new AstVarRef(nodep->fileline(), varp, false);
            varrefp->packagep(v3Global.rootp()->dollarUnitPkgAddp());
            AstNode* newp = new AstArraySel(
                nodep->fileline(), varrefp,
                // Select in case widths are
                // off due to msblen!=width
                new AstSel(nodep->fileline(), nodep->fromp()->unlinkFrBack(), 0, selwidth));
            nodep->replaceWith(newp);
            VL_DO_DANGLING(nodep->deleteTree(), nodep);
        } else {
            nodep->v3error("Unknown built-in enum method " << nodep->prettyNameQ());
        }
    }
    void methodCallAssoc(AstMethodCall* nodep, AstAssocArrayDType* adtypep) {
        AstCMethodHard* newp = NULL;
        if (nodep->name() == "num"  // function int num()
            || nodep->name() == "size") {
            methodOkArguments(nodep, 0, 0);
            newp = new AstCMethodHard(nodep->fileline(), nodep->fromp()->unlinkFrBack(), "size",
                                      NULL);  // So don't need num()
            newp->dtypeSetSigned32();
            newp->didWidth(true);
            newp->protect(false);
        } else if (nodep->name() == "first"  // function int first(ref index)
                   || nodep->name() == "last"  //
                   || nodep->name() == "next"  //
                   || nodep->name() == "prev") {
            methodOkArguments(nodep, 1, 1);
            AstNode* index_exprp = methodCallAssocIndexExpr(nodep, adtypep);
            newp = new AstCMethodHard(nodep->fileline(), nodep->fromp()->unlinkFrBack(),
                                      nodep->name(),  // first/last/next/prev
                                      index_exprp->unlinkFrBack());
            newp->dtypeSetSigned32();
            newp->protect(false);
            newp->didWidth(true);
        } else if (nodep->name() == "exists") {  // function int exists(input index)
            // IEEE really should have made this a "bit" return
            methodOkArguments(nodep, 1, 1);
            AstNode* index_exprp = methodCallAssocIndexExpr(nodep, adtypep);
            newp = new AstCMethodHard(nodep->fileline(), nodep->fromp()->unlinkFrBack(), "exists",
                                      index_exprp->unlinkFrBack());
            newp->dtypeSetSigned32();
            newp->pure(true);
            newp->protect(false);
            newp->didWidth(true);
        } else if (nodep->name() == "delete") {  // function void delete([input integer index])
            methodOkArguments(nodep, 0, 1);
            methodCallLValue(nodep, nodep->fromp(), true);
            if (!nodep->pinsp()) {
                newp = new AstCMethodHard(nodep->fileline(), nodep->fromp()->unlinkFrBack(),
                                          "clear", NULL);
                newp->protect(false);
                newp->makeStatement();
            } else {
                AstNode* index_exprp = methodCallAssocIndexExpr(nodep, adtypep);
                newp = new AstCMethodHard(nodep->fileline(), nodep->fromp()->unlinkFrBack(),
                                          "erase", index_exprp->unlinkFrBack());
                newp->protect(false);
                newp->makeStatement();
            }
        } else {
            nodep->v3error("Unknown built-in associative array method " << nodep->prettyNameQ());
        }
        if (newp) {
            newp->didWidth(true);
            nodep->replaceWith(newp);
            VL_DO_DANGLING(nodep->deleteTree(), nodep);
        }
    }
    AstNode* methodCallAssocIndexExpr(AstMethodCall* nodep, AstAssocArrayDType* adtypep) {
        AstNode* index_exprp = VN_CAST(nodep->pinsp(), Arg)->exprp();
        iterateCheck(nodep, "index", index_exprp, CONTEXT, FINAL, adtypep->keyDTypep(),
                     EXTEND_EXP);
        VL_DANGLING(index_exprp);  // May have been edited
        return VN_CAST(nodep->pinsp(), Arg)->exprp();
    }
    void methodCallLValue(AstMethodCall* nodep, AstNode* childp, bool lvalue) {
        AstNodeVarRef* varrefp = VN_CAST(childp, NodeVarRef);
        if (!varrefp) {
            nodep->v3error("Unsupported: Non-variable on LHS of built-in method '"
                           << nodep->prettyName() << "'");
        } else {
            if (lvalue) varrefp->lvalue(true);
        }
    }
    void methodCallDyn(AstMethodCall* nodep, AstDynArrayDType* adtypep) {
        AstCMethodHard* newp = NULL;
        if (nodep->name() == "at") {  // Created internally for []
            methodOkArguments(nodep, 1, 1);
            methodCallLValue(nodep, nodep->fromp(), true);
            newp = new AstCMethodHard(nodep->fileline(), nodep->fromp()->unlinkFrBack(), "at",
                                      NULL);
            newp->dtypeFrom(adtypep->subDTypep());
            newp->protect(false);
            newp->didWidth(true);
        } else if (nodep->name() == "size") {
            methodOkArguments(nodep, 0, 0);
            newp = new AstCMethodHard(nodep->fileline(), nodep->fromp()->unlinkFrBack(), "size",
                                      NULL);
            newp->dtypeSetSigned32();
            newp->didWidth(true);
            newp->protect(false);
        } else if (nodep->name() == "delete") {  // function void delete()
            methodOkArguments(nodep, 0, 0);
            methodCallLValue(nodep, nodep->fromp(), true);
            newp = new AstCMethodHard(nodep->fileline(), nodep->fromp()->unlinkFrBack(), "clear",
                                      NULL);
            newp->makeStatement();
        } else {
            nodep->v3error("Unsupported/unknown built-in dynamic array method "
                           << nodep->prettyNameQ());
        }
        if (newp) {
            newp->didWidth(true);
            nodep->replaceWith(newp);
            VL_DO_DANGLING(nodep->deleteTree(), nodep);
        }
    }
    void methodCallQueue(AstMethodCall* nodep, AstQueueDType* adtypep) {
        AstCMethodHard* newp = NULL;
        if (nodep->name() == "at") {  // Created internally for []
            methodOkArguments(nodep, 1, 1);
            methodCallLValue(nodep, nodep->fromp(), true);
            newp = new AstCMethodHard(nodep->fileline(), nodep->fromp()->unlinkFrBack(), "at",
                                      NULL);
            newp->dtypeFrom(adtypep->subDTypep());
            newp->protect(false);
            newp->didWidth(true);
        } else if (nodep->name() == "num"  // function int num()
                   || nodep->name() == "size") {
            methodOkArguments(nodep, 0, 0);
            newp = new AstCMethodHard(nodep->fileline(), nodep->fromp()->unlinkFrBack(), "size",
                                      NULL);
            newp->dtypeSetSigned32();
            newp->didWidth(true);
            newp->protect(false);
        } else if (nodep->name() == "delete") {  // function void delete([input integer index])
            methodOkArguments(nodep, 0, 1);
            methodCallLValue(nodep, nodep->fromp(), true);
            if (!nodep->pinsp()) {
                newp = new AstCMethodHard(nodep->fileline(), nodep->fromp()->unlinkFrBack(),
                                          "clear", NULL);
                newp->protect(false);
                newp->makeStatement();
            } else {
                AstNode* index_exprp = methodCallQueueIndexExpr(nodep);
                if (index_exprp->isZero()) {  // delete(0) is a pop_front
                    newp = new AstCMethodHard(nodep->fileline(), nodep->fromp()->unlinkFrBack(),
                                              "pop_front", NULL);
                    newp->dtypeFrom(adtypep->subDTypep());
                    newp->protect(false);
                    newp->didWidth(true);
                    newp->makeStatement();
                } else {
                    nodep->v3error("Unsupported: Queue .delete(index) method, as is O(n) "
                                   "complexity and slow.");
                    newp = new AstCMethodHard(nodep->fileline(), nodep->fromp()->unlinkFrBack(),
                                              "erase", index_exprp->unlinkFrBack());
                    newp->protect(false);
                    newp->makeStatement();
                }
            }
        } else if (nodep->name() == "insert") {
            methodOkArguments(nodep, 2, 2);
            methodCallLValue(nodep, nodep->fromp(), true);
            AstNode* index_exprp = methodCallQueueIndexExpr(nodep);
            AstArg* argp = VN_CAST(nodep->pinsp()->nextp(), Arg);
            iterateCheckTyped(nodep, "insert value", argp->exprp(), adtypep->subDTypep(), BOTH);
            if (index_exprp->isZero()) {  // insert(0, ...) is a push_front
                newp = new AstCMethodHard(nodep->fileline(), nodep->fromp()->unlinkFrBack(),
                                          "push_front", argp->exprp()->unlinkFrBack());
                newp->protect(false);
                newp->makeStatement();
            } else {
                nodep->v3error(
                    "Unsupported: Queue .insert method, as is O(n) complexity and slow.");
                newp = new AstCMethodHard(nodep->fileline(), nodep->fromp()->unlinkFrBack(),
                                          nodep->name(), index_exprp->unlinkFrBack());
                newp->addPinsp(argp->exprp()->unlinkFrBack());
                newp->protect(false);
                newp->makeStatement();
            }
        } else if (nodep->name() == "pop_front" || nodep->name() == "pop_back") {
            methodOkArguments(nodep, 0, 0);
            methodCallLValue(nodep, nodep->fromp(), true);
            newp = new AstCMethodHard(nodep->fileline(), nodep->fromp()->unlinkFrBack(),
                                      nodep->name(), NULL);
            newp->dtypeFrom(adtypep->subDTypep());
            newp->protect(false);
            newp->didWidth(true);
            if (!nodep->firstAbovep()) { newp->makeStatement(); }
        } else if (nodep->name() == "push_back" || nodep->name() == "push_front") {
            methodOkArguments(nodep, 1, 1);
            methodCallLValue(nodep, nodep->fromp(), true);
            AstArg* argp = VN_CAST(nodep->pinsp(), Arg);
            iterateCheckTyped(nodep, "push value", argp->exprp(), adtypep->subDTypep(), BOTH);
            newp = new AstCMethodHard(nodep->fileline(), nodep->fromp()->unlinkFrBack(),
                                      nodep->name(), argp->exprp()->unlinkFrBack());
            newp->protect(false);
            newp->makeStatement();
        } else {
            nodep->v3error("Unsupported/unknown built-in associative array method "
                           << nodep->prettyNameQ());
        }
        if (newp) {
            newp->didWidth(true);
            nodep->replaceWith(newp);
            VL_DO_DANGLING(nodep->deleteTree(), nodep);
        }
    }
    AstNode* methodCallQueueIndexExpr(AstMethodCall* nodep) {
        AstNode* index_exprp = VN_CAST(nodep->pinsp(), Arg)->exprp();
        iterateCheckSigned32(nodep, "index", index_exprp, BOTH);
        VL_DANGLING(index_exprp);  // May have been edited
        return VN_CAST(nodep->pinsp(), Arg)->exprp();
    }
    void methodCallClass(AstMethodCall* nodep, AstClassRefDType* adtypep) {
        // No need to width-resolve the class, as it was done when we did the child
        AstClass* first_classp = adtypep->classp();
        UASSERT_OBJ(first_classp, nodep, "Unlinked");
        for (AstClass* classp = first_classp; classp;) {
            if (AstNodeFTask* ftaskp = VN_CAST(classp->findMember(nodep->name()), NodeFTask)) {
                nodep->taskp(ftaskp);
                nodep->dtypeFrom(ftaskp);
                if (VN_IS(ftaskp, Task)) nodep->makeStatement();
                return;
            }
            classp = classp->extendsp() ? classp->extendsp()->classp() : NULL;
        }
        {
            VSpellCheck speller;
            for (AstClass* classp = first_classp; classp;) {
                for (AstNode* itemp = classp->membersp(); itemp; itemp = itemp->nextp()) {
                    if (VN_IS(itemp, NodeFTask)) speller.pushCandidate(itemp->prettyName());
                }
                classp = classp->extendsp() ? classp->extendsp()->classp() : NULL;
            }
            string suggest = speller.bestCandidateMsg(nodep->prettyName());
            nodep->v3error("Class method "
                           << nodep->prettyNameQ() << " not found in class "
                           << first_classp->prettyNameQ() << "\n"
                           << (suggest.empty() ? "" : nodep->fileline()->warnMore() + suggest));
        }
        nodep->dtypeSetSigned32();  // Guess on error
    }
    void methodCallUnpack(AstMethodCall* nodep, AstUnpackArrayDType* adtypep) {
        enum { UNKNOWN = 0, ARRAY_OR, ARRAY_AND, ARRAY_XOR } methodId;

        methodId = UNKNOWN;
        if (nodep->name() == "or") {
            methodId = ARRAY_OR;
        } else if (nodep->name() == "and") {
            methodId = ARRAY_AND;
        } else if (nodep->name() == "xor") {
            methodId = ARRAY_XOR;
        }

        if (methodId) {
            methodOkArguments(nodep, 0, 0);
            FileLine* fl = nodep->fileline();
            AstNode* newp = NULL;
            for (int i = 0; i < adtypep->elementsConst(); ++i) {
                AstNode* arrayRef = nodep->fromp()->cloneTree(false);
                AstNode* selector = new AstArraySel(fl, arrayRef, i);
                if (!newp) {
                    newp = selector;
                } else {
                    switch (methodId) {
                    case ARRAY_OR: newp = new AstOr(fl, newp, selector); break;
                    case ARRAY_AND: newp = new AstAnd(fl, newp, selector); break;
                    case ARRAY_XOR: newp = new AstXor(fl, newp, selector); break;
                    default: nodep->v3fatalSrc("bad case");
                    }
                }
            }
            nodep->replaceWith(newp);
            VL_DO_DANGLING(nodep->deleteTree(), nodep);
        } else {
            nodep->v3error("Unknown built-in array method " << nodep->prettyNameQ());
        }
    }
    void methodCallEvent(AstMethodCall* nodep, AstBasicDType* adtypep) {
        // Method call on event
        if (nodep->name() == "triggered") {
            // We represent events as numbers, so can just return number
            methodOkArguments(nodep, 0, 0);
            AstNode* newp = nodep->fromp()->unlinkFrBack();
            nodep->replaceWith(newp);
            VL_DO_DANGLING(pushDeletep(nodep), nodep);
        } else {
            nodep->v3error("Unknown built-in event method " << nodep->prettyNameQ());
        }
    }
    void methodCallString(AstMethodCall* nodep, AstBasicDType* adtypep) {
        // Method call on string
        if (nodep->name() == "len") {
            // Constant value
            methodOkArguments(nodep, 0, 0);
            AstNode* newp = new AstLenN(nodep->fileline(), nodep->fromp()->unlinkFrBack());
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
            AstNode* newp = new AstToLowerN(nodep->fileline(), nodep->fromp()->unlinkFrBack());
            nodep->replaceWith(newp);
            VL_DO_DANGLING(nodep->deleteTree(), nodep);
        } else if (nodep->name() == "toupper") {
            methodOkArguments(nodep, 0, 0);
            AstNode* newp = new AstToUpperN(nodep->fileline(), nodep->fromp()->unlinkFrBack());
            nodep->replaceWith(newp);
            VL_DO_DANGLING(nodep->deleteTree(), nodep);
        } else if (nodep->name() == "compare" || nodep->name() == "icompare") {
            const bool ignoreCase = nodep->name()[0] == 'i';
            methodOkArguments(nodep, 1, 1);
            AstArg* argp = VN_CAST(nodep->pinsp(), Arg);
            AstNode* lhs = nodep->fromp()->unlinkFrBack();
            AstNode* rhs = argp->exprp()->unlinkFrBack();
            AstNode* newp = new AstCompareNN(nodep->fileline(), lhs, rhs, ignoreCase);
            nodep->replaceWith(newp);
            VL_DO_DANGLING(nodep->deleteTree(), nodep);
        } else if (nodep->name() == "putc") {
            methodOkArguments(nodep, 2, 2);
            AstArg* arg0p = VN_CAST(nodep->pinsp(), Arg);
            AstArg* arg1p = VN_CAST(arg0p->nextp(), Arg);
            AstNodeVarRef* fromp = VN_CAST(nodep->fromp()->unlinkFrBack(), VarRef);
            AstNode* rhsp = arg0p->exprp()->unlinkFrBack();
            AstNode* thsp = arg1p->exprp()->unlinkFrBack();
            AstVarRef* varrefp = new AstVarRef(nodep->fileline(), fromp->varp(), false);
            AstNode* newp = new AstAssign(nodep->fileline(), fromp,
                                          new AstPutcN(nodep->fileline(), varrefp, rhsp, thsp));
            fromp->lvalue(true);
            nodep->replaceWith(newp);
            VL_DO_DANGLING(nodep->deleteTree(), nodep);
        } else if (nodep->name() == "getc") {
            methodOkArguments(nodep, 1, 1);
            AstArg* arg0p = VN_CAST(nodep->pinsp(), Arg);
            AstNode* lhsp = nodep->fromp()->unlinkFrBack();
            AstNode* rhsp = arg0p->exprp()->unlinkFrBack();
            AstNode* newp = new AstGetcN(nodep->fileline(), lhsp, rhsp);
            nodep->replaceWith(newp);
            VL_DO_DANGLING(nodep->deleteTree(), nodep);
        } else if (nodep->name() == "substr") {
            methodOkArguments(nodep, 2, 2);
            AstArg* arg0p = VN_CAST(nodep->pinsp(), Arg);
            AstArg* arg1p = VN_CAST(arg0p->nextp(), Arg);
            AstNode* lhsp = nodep->fromp()->unlinkFrBack();
            AstNode* rhsp = arg0p->exprp()->unlinkFrBack();
            AstNode* thsp = arg1p->exprp()->unlinkFrBack();
            AstNode* newp = new AstSubstrN(nodep->fileline(), lhsp, rhsp, thsp);
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
            AstNode* newp = new AstAtoN(nodep->fileline(), nodep->fromp()->unlinkFrBack(), fmt);
            nodep->replaceWith(newp);
            VL_DO_DANGLING(nodep->deleteTree(), nodep);
        } else {
            nodep->v3error("Unknown built-in string method " << nodep->prettyNameQ());
        }
    }

    virtual void visit(AstNew* nodep) VL_OVERRIDE {
        if (nodep->didWidthAndSet()) return;
        AstClassRefDType* refp = VN_CAST(m_vup->dtypeNullp(), ClassRefDType);
        if (!refp) {  // e.g. int a = new;
            nodep->v3error("new() not expected in this context");
            return;
        }
        nodep->dtypep(refp);

        AstClass* classp = refp->classp();
        UASSERT_OBJ(classp, nodep, "Unlinked");
        if (AstNodeFTask* ftaskp = VN_CAST(classp->findMember("new"), Func)) {
            nodep->taskp(ftaskp);
            nodep->packagep(classp);
        } else {
            // Either made explicitly or V3LinkDot made implicitly
            classp->v3fatalSrc("Can't find class's new");
        }

        userIterate(nodep->taskp(), NULL);
        userIterateChildren(nodep, NULL);
        processFTaskRefArgs(nodep);
    }
    virtual void visit(AstNewCopy* nodep) VL_OVERRIDE {
        if (nodep->didWidthAndSet()) return;
        AstClassRefDType* refp = VN_CAST(m_vup->dtypeNullp(), ClassRefDType);
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
    virtual void visit(AstNewDynamic* nodep) VL_OVERRIDE {
        if (nodep->didWidthAndSet()) return;
        AstDynArrayDType* adtypep = VN_CAST(m_vup->dtypeNullp(), DynArrayDType);
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
            iterateCheckTyped(nodep, "Dynamic array new RHS", nodep->rhsp(), adtypep->subDTypep(),
                              BOTH);
        }
    }

    virtual void visit(AstPattern* nodep) VL_OVERRIDE {
        if (nodep->didWidthAndSet()) return;
        UINFO(9, "PATTERN " << nodep << endl);
        if (nodep->childDTypep())
            nodep->dtypep(moveChildDTypeEdit(nodep));  // data_type '{ pattern }
        if (!nodep->dtypep() && m_vup->dtypeNullp()) {  // Get it from parent assignment/pin/etc
            nodep->dtypep(m_vup->dtypep());
        }
        AstNodeDType* dtypep = nodep->dtypep();
        if (!dtypep) {
            nodep->v3error("Unsupported/Illegal: Assignment pattern"
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
            for (AstPatMember* patp = VN_CAST(nodep->itemsp(), PatMember); patp;
                 patp = VN_CAST(patp->nextp(), PatMember)) {
                int times = visitPatMemberRep(patp);
                for (int i = 1; i < times; i++) {
                    AstNode* newp = patp->cloneTree(false);
                    patp->addNextHere(newp);
                    // This loop will see the new elements as part of nextp()
                }
            }
            // Convert any PatMember with multiple items to multiple PatMembers
            for (AstPatMember* patp = VN_CAST(nodep->itemsp(), PatMember); patp;
                 patp = VN_CAST(patp->nextp(), PatMember)) {
                if (patp->lhssp()->nextp()) {
                    // Can't just addNext, as would add to end of all members.
                    // So detach, add next and reattach
                    AstNRelinker relinkHandle;
                    patp->unlinkFrBack(&relinkHandle);
                    while (AstNode* movep = patp->lhssp()->nextp()) {
                        movep->unlinkFrBack();  // Not unlinkFrBackWithNext, just one
                        AstNode* newkeyp = NULL;
                        if (patp->keyp()) newkeyp = patp->keyp()->cloneTree(true);
                        AstPatMember* newp
                            = new AstPatMember(patp->fileline(), movep, newkeyp, NULL);
                        patp->addNext(newp);
                    }
                    relinkHandle.relink(patp);
                }
            }
            AstPatMember* defaultp = NULL;
            for (AstPatMember* patp = VN_CAST(nodep->itemsp(), PatMember); patp;
                 patp = VN_CAST(patp->nextp(), PatMember)) {
                if (patp->isDefault()) {
                    if (defaultp) nodep->v3error("Multiple '{ default: } clauses");
                    defaultp = patp;
                    patp->unlinkFrBack();
                }
            }
            while (const AstConstDType* vdtypep = VN_CAST(dtypep, ConstDType)) {
                dtypep = vdtypep->subDTypep()->skipRefp();
            }
            if (AstNodeUOrStructDType* vdtypep = VN_CAST(dtypep, NodeUOrStructDType)) {
                VL_DO_DANGLING(patternUOrStruct(nodep, vdtypep, defaultp), nodep);
            } else if (AstNodeArrayDType* vdtypep = VN_CAST(dtypep, NodeArrayDType)) {
                VL_DO_DANGLING(patternArray(nodep, vdtypep, defaultp), nodep);
            } else if (VN_IS(dtypep, BasicDType) && VN_CAST(dtypep, BasicDType)->isRanged()) {
                VL_DO_DANGLING(patternBasic(nodep, dtypep, defaultp), nodep);
            } else {
                nodep->v3error(
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
        typedef std::map<AstMemberDType*, AstPatMember*> PatMap;
        PatMap patmap;
        {
            AstMemberDType* memp = vdtypep->membersp();
            AstPatMember* patp = VN_CAST(nodep->itemsp(), PatMember);
            for (; memp || patp;) {
                do {
                    if (patp) {
                        if (patp->keyp()) {
                            if (AstText* textp = VN_CAST(patp->keyp(), Text)) {
                                memp = vdtypep->findMember(textp->text());
                                if (!memp) {
                                    patp->keyp()->v3error("Assignment pattern key '"
                                                          << textp->text()
                                                          << "' not found as member");
                                    break;
                                }
                            } else {
                                patp->keyp()->v3error(
                                    "Assignment pattern key not supported/understood: "
                                    << patp->keyp()->prettyTypeName());
                            }
                        }
                    }
                    if (memp && !patp) {
                        // Missing init elements, warn below
                        memp = NULL;
                        patp = NULL;
                        break;
                    } else if (!memp && patp) {
                        patp->v3error("Assignment pattern contains too many elements");
                        memp = NULL;
                        patp = NULL;
                        break;
                    } else {
                        std::pair<PatMap::iterator, bool> ret
                            = patmap.insert(make_pair(memp, patp));
                        if (!ret.second) {
                            patp->v3error("Assignment pattern contains duplicate entry: "
                                          << VN_CAST(patp->keyp(), Text)->text());
                        }
                    }
                } while (false);
                // Next
                if (memp) memp = VN_CAST(memp->nextp(), MemberDType);
                if (patp) patp = VN_CAST(patp->nextp(), PatMember);
            }
        }
        AstNode* newp = NULL;
        for (AstMemberDType* memp = vdtypep->membersp(); memp;
             memp = VN_CAST(memp->nextp(), MemberDType)) {
            PatMap::iterator it = patmap.find(memp);
            AstPatMember* newpatp = NULL;
            AstPatMember* patp = NULL;
            if (it == patmap.end()) {
                if (defaultp) {
                    newpatp = defaultp->cloneTree(false);
                    patp = newpatp;
                } else {
                    if (!VN_IS(vdtypep, UnionDType)) {
                        nodep->v3error("Assignment pattern missed initializing elements: "
                                       << memp->prettyTypeName());
                    }
                }
            } else {
                patp = it->second;
            }
            if (patp) {
                // Determine initial values
                patp->dtypep(memp);
                AstNode* valuep = patternMemberValueIterate(patp);
                if (!newp) {
                    newp = valuep;
                } else {
                    AstConcat* concatp = new AstConcat(patp->fileline(), newp, valuep);
                    newp = concatp;
                    newp->dtypeSetLogicSized(concatp->lhsp()->width() + concatp->rhsp()->width(),
                                             nodep->dtypep()->numeric());
                }
            }
            if (newpatp) { VL_DO_DANGLING(pushDeletep(newpatp), newpatp); }
        }
        if (newp) {
            nodep->replaceWith(newp);
        } else {
            nodep->v3error("Assignment pattern with no members");
        }
        VL_DO_DANGLING(pushDeletep(nodep), nodep);  // Deletes defaultp also, if present
    }
    void patternArray(AstPattern* nodep, AstNodeArrayDType* vdtypep, AstPatMember* defaultp) {
        AstNodeArrayDType* arrayp = VN_CAST(vdtypep, NodeArrayDType);
        VNumRange range = arrayp->declRange();
        PatVecMap patmap = patVectorMap(nodep, range);
        UINFO(9, "ent " << range.hi() << " to " << range.lo() << endl);
        AstNode* newp = NULL;
        for (int ent = range.hi(); ent >= range.lo(); --ent) {
            AstPatMember* newpatp = NULL;
            AstPatMember* patp = NULL;
            PatVecMap::iterator it = patmap.find(ent);
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
                patp->dtypep(arrayp->subDTypep());
                AstNode* valuep = patternMemberValueIterate(patp);
                if (VN_IS(arrayp, UnpackArrayDType)) {
                    if (!newp) {
                        AstInitArray* newap = new AstInitArray(nodep->fileline(), arrayp, NULL);
                        newp = newap;
                    }
                    VN_CAST(newp, InitArray)->addIndexValuep(ent - range.lo(), valuep);
                } else {  // Packed. Convert to concat for now.
                    if (!newp) {
                        newp = valuep;
                    } else {
                        AstConcat* concatp = new AstConcat(patp->fileline(), newp, valuep);
                        newp = concatp;
                        newp->dtypeSetLogicSized(concatp->lhsp()->width()
                                                     + concatp->rhsp()->width(),
                                                 nodep->dtypep()->numeric());
                    }
                }
            }
            if (newpatp) { VL_DO_DANGLING(pushDeletep(newpatp), newpatp); }
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
    void patternBasic(AstPattern* nodep, AstNodeDType* vdtypep, AstPatMember* defaultp) {
        AstBasicDType* bdtypep = VN_CAST(vdtypep, BasicDType);
        VNumRange range = bdtypep->declRange();
        PatVecMap patmap = patVectorMap(nodep, range);
        UINFO(9, "ent " << range.hi() << " to " << range.lo() << endl);
        AstNode* newp = NULL;
        for (int ent = range.hi(); ent >= range.lo(); --ent) {
            AstPatMember* newpatp = NULL;
            AstPatMember* patp = NULL;
            PatVecMap::iterator it = patmap.find(ent);
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
                vdtypep = nodep->findLogicBoolDType();
                patp->dtypep(vdtypep);
                AstNode* valuep = patternMemberValueIterate(patp);
                {  // Packed. Convert to concat for now.
                    if (!newp) {
                        newp = valuep;
                    } else {
                        AstConcat* concatp = new AstConcat(patp->fileline(), newp, valuep);
                        newp = concatp;
                        newp->dtypeSetLogicSized(concatp->lhsp()->width()
                                                     + concatp->rhsp()->width(),
                                                 nodep->dtypep()->numeric());
                    }
                }
            }
            if (newpatp) { VL_DO_DANGLING(pushDeletep(newpatp), newpatp); }
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
            if (AstNode* newp = WidthCommitVisitor::newIfConstCommitSize(VN_CAST(valuep, Const))) {
                VL_DO_DANGLING(pushDeletep(valuep), valuep);
                valuep = newp;
            }
        }
        return valuep;
    }

    virtual void visit(AstPatMember* nodep) VL_OVERRIDE {
        AstNodeDType* vdtypep = m_vup->dtypeNullp();
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
        if (nodep->repp()) {  // else repp()==NULL shorthand for rep count 1
            iterateCheckSizedSelf(nodep, "LHS", nodep->repp(), SELF, BOTH);
            V3Const::constifyParamsEdit(nodep->repp());  // repp may change
            const AstConst* constp = VN_CAST(nodep->repp(), Const);
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

    virtual void visit(AstPropClocked* nodep) VL_OVERRIDE {
        if (m_vup->prelim()) {  // First stage evaluation
            iterateCheckBool(nodep, "Property", nodep->propp(), BOTH);
            userIterateAndNext(nodep->sensesp(), NULL);
            if (nodep->disablep()) {
                iterateCheckBool(nodep, "Disable", nodep->disablep(),
                                 BOTH);  // it's like an if() condition.
            }
            nodep->dtypeSetLogicBool();
        }
    }

    //--------------------
    // Top levels

    virtual void visit(AstNodeCase* nodep) VL_OVERRIDE {
        // IEEE-2012 12.5:
        //    Width: MAX(expr, all items)
        //    Signed: Only if expr, and all items signed
        assertAtStatement(nodep);
        userIterateAndNext(nodep->exprp(), WidthVP(CONTEXT, PRELIM).p());
        for (AstCaseItem *nextip, *itemp = nodep->itemsp(); itemp; itemp = nextip) {
            nextip
                = VN_CAST(itemp->nextp(), CaseItem);  // Prelim may cause the node to get replaced
            if (!VN_IS(nodep, GenCase)) userIterateAndNext(itemp->bodysp(), NULL);
            for (AstNode *nextcp, *condp = itemp->condsp(); condp; condp = nextcp) {
                nextcp = condp->nextp();  // Prelim may cause the node to get replaced
                VL_DO_DANGLING(userIterate(condp, WidthVP(CONTEXT, PRELIM).p()), condp);
            }
        }

        // Take width as maximum across all items, if any is real whole thing is real
        AstNodeDType* subDTypep = nodep->exprp()->dtypep();
        for (AstCaseItem* itemp = nodep->itemsp(); itemp;
             itemp = VN_CAST(itemp->nextp(), CaseItem)) {
            for (AstNode* condp = itemp->condsp(); condp; condp = condp->nextp()) {
                if (condp->dtypep() != subDTypep) {
                    if (condp->dtypep()->isDouble()) {
                        subDTypep = nodep->findDoubleDType();
                    } else {
                        int width = std::max(subDTypep->width(), condp->width());
                        int mwidth = std::max(subDTypep->widthMin(), condp->widthMin());
                        bool issigned = subDTypep->isSigned() && condp->isSigned();
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
             itemp = VN_CAST(itemp->nextp(), CaseItem)) {
            for (AstNode *nextcp, *condp = itemp->condsp(); condp; condp = nextcp) {
                nextcp = condp->nextp();  // Final may cause the node to get replaced
                iterateCheck(nodep, "Case Item", condp, CONTEXT, FINAL, subDTypep, EXTEND_LHS);
            }
        }
    }
    virtual void visit(AstNodeFor* nodep) VL_OVERRIDE {
        assertAtStatement(nodep);
        userIterateAndNext(nodep->initsp(), NULL);
        iterateCheckBool(nodep, "For Test Condition", nodep->condp(),
                         BOTH);  // it's like an if() condition.
        if (!VN_IS(nodep, GenFor)) userIterateAndNext(nodep->bodysp(), NULL);
        userIterateAndNext(nodep->incsp(), NULL);
    }
    virtual void visit(AstRepeat* nodep) VL_OVERRIDE {
        assertAtStatement(nodep);
        userIterateAndNext(nodep->countp(), WidthVP(SELF, BOTH).p());
        userIterateAndNext(nodep->bodysp(), NULL);
    }
    virtual void visit(AstWhile* nodep) VL_OVERRIDE {
        assertAtStatement(nodep);
        userIterateAndNext(nodep->precondsp(), NULL);
        iterateCheckBool(nodep, "For Test Condition", nodep->condp(),
                         BOTH);  // it's like an if() condition.
        userIterateAndNext(nodep->bodysp(), NULL);
        userIterateAndNext(nodep->incsp(), NULL);
    }
    virtual void visit(AstNodeIf* nodep) VL_OVERRIDE {
        assertAtStatement(nodep);
        // if (debug()) nodep->dumpTree(cout, "  IfPre: ");
        if (!VN_IS(nodep, GenIf)) {  // for m_paramsOnly
            userIterateAndNext(nodep->ifsp(), NULL);
            userIterateAndNext(nodep->elsesp(), NULL);
        }
        iterateCheckBool(nodep, "If", nodep->condp(), BOTH);  // it's like an if() condition.
        // if (debug()) nodep->dumpTree(cout, "  IfOut: ");
    }

    virtual void visit(AstNodeAssign* nodep) VL_OVERRIDE {
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
            AstNodeDType* lhsDTypep
                = nodep->lhsp()->dtypep();  // Note we use rhsp for context determined
            iterateCheckAssign(nodep, "Assign RHS", nodep->rhsp(), FINAL, lhsDTypep);
            // if (debug()) nodep->dumpTree(cout, "  AssignOut: ");
        }
        if (AstBasicDType* basicp = nodep->rhsp()->dtypep()->basicp()) {
            if (basicp->isEventValue()) {
                // see t_event_copy.v for commentary on the mess involved
                nodep->v3error("Unsupported: assignment of event data type");
            }
        }
        if (AstNewDynamic* dynp = VN_CAST(nodep->rhsp(), NewDynamic)) {
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
        }
    }

    virtual void visit(AstSFormatF* nodep) VL_OVERRIDE {
        // Excludes NodeDisplay, see below
        if (m_vup && !m_vup->prelim()) return;  // Can be called as statement or function
        // Just let all arguments seek their natural sizes
        userIterateChildren(nodep, WidthVP(SELF, BOTH).p());
        //
        UINFO(9, "  Display in " << nodep->text() << endl);
        string newFormat;
        bool inPct = false;
        AstNode* argp = nodep->exprsp();
        string txt = nodep->text();
        string fmt;
        for (string::const_iterator it = txt.begin(); it != txt.end(); ++it) {
            char ch = *it;
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
                        AstNode* nextp = argp->nextp();
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
                    AstNodeDType* dtypep = argp ? argp->dtypep()->skipRefp() : NULL;
                    AstBasicDType* basicp = dtypep ? dtypep->basicp() : NULL;
                    if (basicp && basicp->isString()) {
                        added = true;
                        newFormat += "\"%@\"";
                    } else if (basicp && basicp->isDouble()) {
                        added = true;
                        newFormat += "%g";
                    } else if (VN_IS(dtypep, AssocArrayDType)  //
                               || VN_IS(dtypep, ClassRefDType)  //
                               || VN_IS(dtypep, DynArrayDType)  //
                               || VN_IS(dtypep, QueueDType)) {
                        added = true;
                        newFormat += "%@";
                        AstNRelinker handle;
                        argp->unlinkFrBack(&handle);
                        AstCMath* newp = new AstCMath(nodep->fileline(), "VL_TO_STRING(", 0, true);
                        newp->addBodysp(argp);
                        newp->addBodysp(new AstText(nodep->fileline(), ")"));
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
                        AstNode* nextp = argp->nextp();
                        if (argp->isDouble()) ch = '^';  // Convert it
                        if (nodep->timeunit().isNone()) {
                            nodep->v3fatalSrc("display %t has no time units");
                        }
                        double scale = nodep->timeunit().multiplier()
                                       / v3Global.rootp()->timeprecision().multiplier();
                        if (scale != 1.0) {
                            AstNode* newp;
                            AstNRelinker relinkHandle;
                            argp->unlinkFrBack(&relinkHandle);
                            if (argp->isDouble()) {  // Convert it
                                ch = '^';
                                newp = new AstMulD(
                                    argp->fileline(),
                                    new AstConst(argp->fileline(), AstConst::RealDouble(), scale),
                                    argp);
                            } else {
                                newp = new AstMul(argp->fileline(),
                                                  new AstConst(argp->fileline(),
                                                               AstConst::Unsized64(),
                                                               llround(scale)),
                                                  argp);
                            }
                            relinkHandle.relink(newp);
                        }
                        argp = nextp;
                    }
                    break;
                }
                case 'f':  // FALLTHRU
                case 'g': {
                    if (argp) {
                        AstNode* nextp = argp->nextp();
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
    virtual void visit(AstDisplay* nodep) VL_OVERRIDE {
        assertAtStatement(nodep);
        if (nodep->filep()) iterateCheckFileDesc(nodep, nodep->filep(), BOTH);
        // Just let all arguments seek their natural sizes
        userIterateChildren(nodep, WidthVP(SELF, BOTH).p());
    }
    virtual void visit(AstElabDisplay* nodep) VL_OVERRIDE {
        assertAtStatement(nodep);
        // Just let all arguments seek their natural sizes
        userIterateChildren(nodep, WidthVP(SELF, BOTH).p());
        if (!m_paramsOnly) {
            V3Const::constifyParamsEdit(nodep->fmtp());  // fmtp may change
            switch (nodep->displayType()) {
            case AstDisplayType::DT_INFO: nodep->v3warn(USERINFO, nodep->fmtp()->text()); break;
            case AstDisplayType::DT_ERROR: nodep->v3warn(USERERROR, nodep->fmtp()->text()); break;
            case AstDisplayType::DT_WARNING: nodep->v3warn(USERWARN, nodep->fmtp()->text()); break;
            case AstDisplayType::DT_FATAL: nodep->v3warn(USERFATAL, nodep->fmtp()->text()); break;
            default: UASSERT_OBJ(false, nodep, "Unexpected elaboration display type");
            }
            VL_DO_DANGLING(nodep->unlinkFrBack()->deleteTree(), nodep);
        }
    }
    virtual void visit(AstDumpCtl* nodep) VL_OVERRIDE {
        assertAtStatement(nodep);
        // Just let all arguments seek their natural sizes
        userIterateChildren(nodep, WidthVP(SELF, BOTH).p());
    }
    virtual void visit(AstFOpen* nodep) VL_OVERRIDE {
        // Although a system function in IEEE, here a statement which sets the file pointer (MCD)
        assertAtStatement(nodep);
        iterateCheckFileDesc(nodep, nodep->filep(), BOTH);
        userIterateAndNext(nodep->filenamep(), WidthVP(SELF, BOTH).p());
        userIterateAndNext(nodep->modep(), WidthVP(SELF, BOTH).p());
    }
    virtual void visit(AstFClose* nodep) VL_OVERRIDE {
        assertAtStatement(nodep);
        iterateCheckFileDesc(nodep, nodep->filep(), BOTH);
    }
    virtual void visit(AstFError* nodep) VL_OVERRIDE {
        if (m_vup->prelim()) {
            iterateCheckFileDesc(nodep, nodep->filep(), BOTH);
            // We only support string types, not packed array
            iterateCheckString(nodep, "$ferror string result", nodep->strp(), BOTH);
            nodep->dtypeSetLogicUnsized(32, 1, VSigning::SIGNED);  // Spec says integer return
        }
    }
    virtual void visit(AstFEof* nodep) VL_OVERRIDE {
        if (m_vup->prelim()) {
            iterateCheckFileDesc(nodep, nodep->filep(), BOTH);
            nodep->dtypeSetLogicUnsized(32, 1, VSigning::SIGNED);  // Spec says integer return
        }
    }
    virtual void visit(AstFFlush* nodep) VL_OVERRIDE {
        assertAtStatement(nodep);
        if (nodep->filep()) iterateCheckFileDesc(nodep, nodep->filep(), BOTH);
    }
    virtual void visit(AstFRewind* nodep) VL_OVERRIDE {
        iterateCheckFileDesc(nodep, nodep->filep(), BOTH);
        nodep->dtypeSetLogicUnsized(32, 1, VSigning::SIGNED);  // Spec says integer return
    }
    virtual void visit(AstFTell* nodep) VL_OVERRIDE {
        iterateCheckFileDesc(nodep, nodep->filep(), BOTH);
        nodep->dtypeSetLogicUnsized(32, 1, VSigning::SIGNED);  // Spec says integer return
    }
    virtual void visit(AstFSeek* nodep) VL_OVERRIDE {
        iterateCheckFileDesc(nodep, nodep->filep(), BOTH);
        iterateCheckSigned32(nodep, "$fseek offset", nodep->offset(), BOTH);
        iterateCheckSigned32(nodep, "$fseek operation", nodep->operation(), BOTH);
        nodep->dtypeSetLogicUnsized(32, 1, VSigning::SIGNED);  // Spec says integer return
    }
    virtual void visit(AstFGetC* nodep) VL_OVERRIDE {
        if (m_vup->prelim()) {
            iterateCheckFileDesc(nodep, nodep->filep(), BOTH);
            nodep->dtypeSetLogicUnsized(32, 8, VSigning::SIGNED);  // Spec says integer return
        }
    }
    virtual void visit(AstFGetS* nodep) VL_OVERRIDE {
        if (m_vup->prelim()) {
            nodep->dtypeSetSigned32();  // Spec says integer return
            iterateCheckFileDesc(nodep, nodep->filep(), BOTH);
            userIterateAndNext(nodep->strgp(), WidthVP(SELF, BOTH).p());
        }
    }
    virtual void visit(AstFUngetC* nodep) VL_OVERRIDE {
        if (m_vup->prelim()) {
            iterateCheckFileDesc(nodep, nodep->filep(), BOTH);
            iterateCheckSigned32(nodep, "$fungetc character", nodep->charp(), BOTH);
            nodep->dtypeSetLogicUnsized(32, 8, VSigning::SIGNED);  // Spec says integer return
        }
    }
    virtual void visit(AstFRead* nodep) VL_OVERRIDE {
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
    virtual void visit(AstFScanF* nodep) VL_OVERRIDE {
        if (m_vup->prelim()) {
            nodep->dtypeSetSigned32();  // Spec says integer return
            iterateCheckFileDesc(nodep, nodep->filep(), BOTH);
            userIterateAndNext(nodep->exprsp(), WidthVP(SELF, BOTH).p());
        }
    }
    virtual void visit(AstSScanF* nodep) VL_OVERRIDE {
        if (m_vup->prelim()) {
            nodep->dtypeSetSigned32();  // Spec says integer return
            userIterateAndNext(nodep->fromp(), WidthVP(SELF, BOTH).p());
            userIterateAndNext(nodep->exprsp(), WidthVP(SELF, BOTH).p());
        }
    }
    virtual void visit(AstSysIgnore* nodep) VL_OVERRIDE {
        userIterateAndNext(nodep->exprsp(), WidthVP(SELF, BOTH).p());
    }
    virtual void visit(AstSystemF* nodep) VL_OVERRIDE {
        if (m_vup->prelim()) {
            userIterateAndNext(nodep->lhsp(), WidthVP(SELF, BOTH).p());
            nodep->dtypeSetSigned32();  // Spec says integer return
        }
    }
    virtual void visit(AstSysFuncAsTask* nodep) VL_OVERRIDE {
        assertAtStatement(nodep);
        userIterateAndNext(nodep->lhsp(), WidthVP(SELF, BOTH).p());
    }
    virtual void visit(AstSystemT* nodep) VL_OVERRIDE {
        assertAtStatement(nodep);
        userIterateAndNext(nodep->lhsp(), WidthVP(SELF, BOTH).p());
    }
    virtual void visit(AstNodeReadWriteMem* nodep) VL_OVERRIDE {
        assertAtStatement(nodep);
        userIterateAndNext(nodep->filenamep(), WidthVP(SELF, BOTH).p());
        userIterateAndNext(nodep->memp(), WidthVP(SELF, BOTH).p());
        AstNodeDType* subp = NULL;
        if (AstAssocArrayDType* adtypep
            = VN_CAST(nodep->memp()->dtypep()->skipRefp(), AssocArrayDType)) {
            subp = adtypep->subDTypep();
            if (!adtypep->keyDTypep()->skipRefp()->basicp()
                || !adtypep->keyDTypep()->skipRefp()->basicp()->keyword().isIntNumeric()) {
                nodep->memp()->v3error(nodep->verilogKwd()
                                       << " address/key must be integral (IEEE 1800-2017 21.4.1)");
            }
        } else if (AstUnpackArrayDType* adtypep
                   = VN_CAST(nodep->memp()->dtypep()->skipRefp(), UnpackArrayDType)) {
            subp = adtypep->subDTypep();
        } else {
            nodep->memp()->v3error("Unsupported: "
                                   << nodep->verilogKwd()
                                   << " into other than unpacked or associative array");
        }
        if (subp
            && (!subp->skipRefp()->basicp()
                || !subp->skipRefp()->basicp()->keyword().isIntNumeric())) {
            nodep->memp()->v3error("Unsupported: " << nodep->verilogKwd()
                                                   << " array values must be integral");
        }
        userIterateAndNext(nodep->lsbp(), WidthVP(SELF, BOTH).p());
        userIterateAndNext(nodep->msbp(), WidthVP(SELF, BOTH).p());
    }
    virtual void visit(AstValuePlusArgs* nodep) VL_OVERRIDE {
        if (m_vup->prelim()) {
            userIterateAndNext(nodep->searchp(), WidthVP(SELF, BOTH).p());
            userIterateAndNext(nodep->outp(), WidthVP(SELF, BOTH).p());
            nodep->dtypeChgWidthSigned(32, 1, VSigning::SIGNED);  // Spec says integer return
        }
    }
    virtual void visit(AstTimeFormat* nodep) VL_OVERRIDE {
        assertAtStatement(nodep);
        iterateCheckSigned32(nodep, "units", nodep->unitsp(), BOTH);
        iterateCheckSigned32(nodep, "precision", nodep->precisionp(), BOTH);
        iterateCheckString(nodep, "suffix", nodep->suffixp(), BOTH);
        iterateCheckSigned32(nodep, "width", nodep->widthp(), BOTH);
    }
    virtual void visit(AstUCStmt* nodep) VL_OVERRIDE {
        // Just let all arguments seek their natural sizes
        assertAtStatement(nodep);
        userIterateChildren(nodep, WidthVP(SELF, BOTH).p());
    }
    virtual void visit(AstAssert* nodep) VL_OVERRIDE {
        assertAtStatement(nodep);
        iterateCheckBool(nodep, "Property", nodep->propp(), BOTH);  // it's like an if() condition.
        userIterateAndNext(nodep->passsp(), NULL);
        userIterateAndNext(nodep->failsp(), NULL);
    }
    virtual void visit(AstCover* nodep) VL_OVERRIDE {
        assertAtStatement(nodep);
        iterateCheckBool(nodep, "Property", nodep->propp(), BOTH);  // it's like an if() condition.
        userIterateAndNext(nodep->passsp(), NULL);
    }
    virtual void visit(AstRestrict* nodep) VL_OVERRIDE {
        assertAtStatement(nodep);
        iterateCheckBool(nodep, "Property", nodep->propp(), BOTH);  // it's like an if() condition.
    }
    virtual void visit(AstPin* nodep) VL_OVERRIDE {
        // if (debug()) nodep->dumpTree(cout, "-  PinPre: ");
        // TOP LEVEL NODE
        if (nodep->modVarp() && nodep->modVarp()->isGParam()) {
            // Widthing handled as special init() case
            userIterateChildren(nodep, WidthVP(SELF, BOTH).p());
        } else if (!m_paramsOnly) {
            if (!nodep->modVarp()->didWidth()) {
                // Var hasn't been widthed, so make it so.
                userIterate(nodep->modVarp(), NULL);
            }
            if (!nodep->exprp()) {  // No-connect
                return;
            }
            // Very much like like an assignment, but which side is LH/RHS
            // depends on pin being a in/output/inout.
            userIterateAndNext(nodep->exprp(), WidthVP(nodep->modVarp()->dtypep(), PRELIM).p());
            AstNodeDType* pinDTypep = nodep->modVarp()->dtypep();
            AstNodeDType* conDTypep = nodep->exprp()->dtypep();
            if (!conDTypep) nodep->v3fatalSrc("Unlinked pin data type");
            AstNodeDType* subDTypep = pinDTypep;
            int pinwidth = pinDTypep->width();
            int conwidth = conDTypep->width();
            if (conDTypep == pinDTypep  // If match, we're golden
                || similarDTypeRecurse(conDTypep, pinDTypep)) {
                userIterateAndNext(nodep->exprp(), WidthVP(subDTypep, FINAL).p());
            } else if (m_cellRangep) {
                int numInsts = m_cellRangep->elementsConst();
                if (conwidth == pinwidth) {
                    // Arrayed instants: widths match so connect to each instance
                    subDTypep = conDTypep;  // = same expr dtype
                } else if (conwidth == numInsts * pinwidth) {
                    // Arrayed instants: one bit for each of the instants (each
                    // assign is 1 pinwidth wide)
                    subDTypep = conDTypep;  // = same expr dtype (but numInst*pin_dtype)
                } else {
                    // Must be a error according to spec
                    // (Because we need to know if to connect to one or all instants)
                    nodep->v3error(ucfirst(nodep->prettyOperatorName())
                                   << " as part of a module instance array"
                                   << " requires " << pinwidth << " or " << pinwidth * numInsts
                                   << " bits, but connection's "
                                   << nodep->exprp()->prettyTypeName() << " generates " << conwidth
                                   << " bits.");
                    subDTypep = conDTypep;  // = same expr dtype
                }
                userIterateAndNext(nodep->exprp(), WidthVP(subDTypep, FINAL).p());
            } else {
                if (nodep->modVarp()->direction() == VDirection::REF) {
                    nodep->v3error("Ref connection "
                                   << nodep->modVarp()->prettyNameQ()
                                   << " requires matching types;"
                                   << " ref requires " << pinDTypep->prettyDTypeNameQ()
                                   << " data type but connection is "
                                   << conDTypep->prettyDTypeNameQ() << " data type." << endl);
                } else if (nodep->modVarp()->isTristate()) {
                    if (pinwidth != conwidth) {
                        nodep->v3error("Unsupported: " << ucfirst(nodep->prettyOperatorName())
                                                       << " to inout signal requires " << pinwidth
                                                       << " bits, but connection's "
                                                       << nodep->exprp()->prettyTypeName()
                                                       << " generates " << conwidth << " bits.");
                        // otherwise would need some mess to force both sides to proper size
                    }
                }
                // Check if an interface is connected to a non-interface and vice versa
                AstNodeDType* modDTypep = nodep->modVarp()->dtypep();
                AstNodeDType* exprDTypep = nodep->exprp()->dtypep();
                if ((VN_IS(modDTypep, IfaceRefDType) && !VN_IS(exprDTypep, IfaceRefDType))
                    || (VN_IS(exprDTypep, IfaceRefDType) && !VN_IS(modDTypep, IfaceRefDType))) {
                    nodep->v3error("Illegal " << nodep->prettyOperatorName() << ","
                                              << " mismatch between port which is"
                                              << (VN_CAST(modDTypep, IfaceRefDType) ? "" : " not")
                                              << " an interface,"
                                              << " and expression which is"
                                              << (VN_CAST(exprDTypep, IfaceRefDType) ? "" : " not")
                                              << " an interface.");
                }

                // TODO Simple dtype checking, should be a more general check
                AstNodeArrayDType* exprArrayp = VN_CAST(exprDTypep->skipRefp(), UnpackArrayDType);
                AstNodeArrayDType* modArrayp = VN_CAST(modDTypep->skipRefp(), UnpackArrayDType);
                if (exprArrayp && modArrayp
                    && VN_IS(exprArrayp->subDTypep()->skipRefp(), IfaceRefDType)
                    && exprArrayp->declRange().elements() != modArrayp->declRange().elements()) {
                    int exprSize = exprArrayp->declRange().elements();
                    int modSize = modArrayp->declRange().elements();
                    nodep->v3error("Illegal "
                                   << nodep->prettyOperatorName() << ","
                                   << " mismatch between port which is an interface array of size "
                                   << modSize << ","
                                   << " and expression which is an interface array of size "
                                   << exprSize << ".");
                    UINFO(1, "    Related lo: " << modDTypep->skipRefp() << endl);
                    UINFO(1, "    Related hi: " << exprDTypep->skipRefp() << endl);
                } else if ((exprArrayp && !modArrayp) || (!exprArrayp && modArrayp)) {
                    nodep->v3error("Illegal " << nodep->prettyOperatorName() << ","
                                              << " mismatch between port which is"
                                              << (modArrayp ? "" : " not") << " an array,"
                                              << " and expression which is"
                                              << (exprArrayp ? "" : " not")
                                              << " an array. (IEEE 1800-2017 7.6)");
                    UINFO(1, "    Related lo: " << modDTypep->skipRefp() << endl);
                    UINFO(1, "    Related hi: " << exprDTypep->skipRefp() << endl);
                }
                iterateCheckAssign(nodep, "pin connection", nodep->exprp(), FINAL, subDTypep);
            }
        }
        // if (debug()) nodep->dumpTree(cout, "-  PinOut: ");
    }
    virtual void visit(AstCell* nodep) VL_OVERRIDE {
        if (!m_paramsOnly) {
            if (VN_IS(nodep->modp(), NotFoundModule)) {
                // We've resolved parameters and hit a module that we couldn't resolve.  It's
                // finally time to report it.
                // Note only here in V3Width as this is first visitor after V3Dead.
                nodep->modNameFileline()->v3error("Cannot find file containing module: '"
                                                  << nodep->modName() << "'");
                v3Global.opt.filePathLookedMsg(nodep->modNameFileline(), nodep->modName());
            }
            if (nodep->rangep()) {
                m_cellRangep = nodep->rangep();
                userIterateAndNext(nodep->rangep(), WidthVP(SELF, BOTH).p());
            }
            userIterateAndNext(nodep->pinsp(), NULL);
        }
        userIterateAndNext(nodep->paramsp(), NULL);
        m_cellRangep = NULL;
    }
    virtual void visit(AstGatePin* nodep) VL_OVERRIDE {
        if (m_vup->prelim()) {
            userIterateAndNext(nodep->rangep(), WidthVP(SELF, BOTH).p());
            userIterateAndNext(nodep->exprp(), WidthVP(CONTEXT, PRELIM).p());
            nodep->dtypeFrom(nodep->rangep());
            // Very much like like an pin
            AstNodeDType* conDTypep = nodep->exprp()->dtypep();
            int numInsts = nodep->rangep()->elementsConst();
            int pinwidth = numInsts;
            int conwidth = conDTypep->width();
            if (conwidth == 1 && pinwidth > 1) {  // Multiple connections
                AstNodeDType* subDTypep = nodep->findLogicDType(1, 1, conDTypep->numeric());
                userIterateAndNext(nodep->exprp(), WidthVP(subDTypep, FINAL).p());
                AstNode* newp = new AstReplicate(nodep->fileline(), nodep->exprp()->unlinkFrBack(),
                                                 numInsts);
                nodep->replaceWith(newp);
            } else {
                // Eliminating so pass down all of vup
                userIterateAndNext(nodep->exprp(), m_vup);
                nodep->replaceWith(nodep->exprp()->unlinkFrBack());
            }
            VL_DO_DANGLING(pushDeletep(nodep), nodep);
        }
    }
    virtual void visit(AstNodeFTask* nodep) VL_OVERRIDE {
        // Grab width from the output variable (if it's a function)
        if (nodep->didWidth()) return;
        if (nodep->doingWidth()) {
            nodep->v3error("Unsupported: Recursive function or task call");
            nodep->dtypeSetLogicBool();
            nodep->didWidth(true);
            return;
        }
        // Function hasn't been widthed, so make it so.
        // Would use user1 etc, but V3Width called from too many places to spend a user
        nodep->doingWidth(true);
        m_ftaskp = nodep;
        userIterateChildren(nodep, NULL);
        if (nodep->isConstructor()) {
            // Pretend it's void so less special casing needed when look at dtypes
            nodep->dtypeSetVoid();
        } else if (nodep->fvarp()) {
            m_funcp = VN_CAST(nodep, Func);
            UASSERT_OBJ(m_funcp, nodep, "FTask with function variable, but isn't a function");
            nodep->dtypeFrom(nodep->fvarp());  // Which will get it from fvarp()->dtypep()
        }
        nodep->didWidth(true);
        nodep->doingWidth(false);
        m_funcp = NULL;
        m_ftaskp = NULL;
        if (nodep->dpiImport() && !nodep->dpiOpenParent() && markHasOpenArray(nodep)) {
            nodep->dpiOpenParentInc();  // Mark so V3Task will wait for a child to build calling
                                        // func
        }
    }
    virtual void visit(AstReturn* nodep) VL_OVERRIDE {
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

    virtual void visit(AstFuncRef* nodep) VL_OVERRIDE {
        visit(VN_CAST(nodep, NodeFTaskRef));
        nodep->dtypeFrom(nodep->taskp());
        // if (debug()) nodep->dumpTree(cout, "  FuncOut: ");
    }
    void processFTaskRefArgs(AstNodeFTaskRef* nodep) {
        // For arguments, is assignment-like context; see IEEE rules in AstNodeAssign
        // Function hasn't been widthed, so make it so.
        UINFO(5, "  FTASKREF " << nodep << endl);
        UASSERT_OBJ(nodep->taskp(), nodep, "Unlinked");
        if (nodep->didWidth()) return;
        userIterate(nodep->taskp(), NULL);
        //
        // And do the arguments to the task/function too
        do {
        reloop:
            V3TaskConnects tconnects = V3Task::taskConnects(nodep, nodep->taskp()->stmtsp());
            for (V3TaskConnects::iterator it = tconnects.begin(); it != tconnects.end(); ++it) {
                AstVar* portp = it->first;
                AstArg* argp = it->second;
                AstNode* pinp = argp->exprp();
                if (!pinp) continue;  // Argument error we'll find later
                // Prelim may cause the node to get replaced; we've lost our
                // pointer, so need to iterate separately later
                if (portp->attrSFormat()
                    && (!VN_IS(pinp, SFormatF) || pinp->nextp())) {  // Not already done
                    UINFO(4, "   sformat via metacomment: " << nodep << endl);
                    AstNRelinker handle;
                    argp->unlinkFrBackWithNext(&handle);  // Format + additional args, if any
                    AstNode* argsp = NULL;
                    while (AstArg* nextargp = VN_CAST(argp->nextp(), Arg)) {
                        argsp = AstNode::addNext(
                            argsp, nextargp->exprp()
                                       ->unlinkFrBackWithNext());  // Expression goes to SFormatF
                        nextargp->unlinkFrBack()->deleteTree();  // Remove the call's Arg wrapper
                    }
                    string format;
                    if (VN_IS(pinp, Const)) {
                        format = VN_CAST(pinp, Const)->num().toString();
                    } else {
                        pinp->v3error(
                            "Format to $display-like function must have constant format string");
                    }
                    VL_DO_DANGLING(pushDeletep(argp), argp);
                    AstSFormatF* newp = new AstSFormatF(nodep->fileline(), format, false, argsp);
                    if (!newp->scopeNamep() && newp->formatScopeTracking()) {
                        newp->scopeNamep(new AstScopeName(newp->fileline()));
                    }
                    handle.relink(new AstArg(newp->fileline(), "", newp));
                    // Connection list is now incorrect (has extra args in it).
                    goto reloop;  // so exit early; next loop will correct it
                }  //
                else if (portp->basicp() && portp->basicp()->keyword() == AstBasicDTypeKwd::STRING
                         && !VN_IS(pinp, CvtPackString)
                         && !VN_IS(pinp, SFormatF)  // Already generates a string
                         && !(VN_IS(pinp, VarRef)
                              && VN_CAST(pinp, VarRef)->varp()->basicp()->keyword()
                                     == AstBasicDTypeKwd::STRING)) {
                    UINFO(4, "   Add CvtPackString: " << pinp << endl);
                    AstNRelinker handle;
                    pinp->unlinkFrBack(&handle);  // No next, that's the next pin
                    AstNode* newp = new AstCvtPackString(pinp->fileline(), pinp);
                    handle.relink(newp);
                    pinp = newp;
                }
                // AstPattern requires assignments to pass datatype on PRELIM
                VL_DO_DANGLING(userIterate(pinp, WidthVP(portp->dtypep(), PRELIM).p()), pinp);
            }
        } while (false);
        // Stage 2
        {
            V3TaskConnects tconnects = V3Task::taskConnects(nodep, nodep->taskp()->stmtsp());
            for (V3TaskConnects::iterator it = tconnects.begin(); it != tconnects.end(); ++it) {
                AstVar* portp = it->first;
                AstArg* argp = it->second;
                AstNode* pinp = argp->exprp();
                if (!pinp) continue;  // Argument error we'll find later
                // Change data types based on above accept completion
                if (portp->isDouble()) VL_DO_DANGLING(spliceCvtD(pinp), pinp);
            }
        }
        // Stage 3
        {
            V3TaskConnects tconnects = V3Task::taskConnects(nodep, nodep->taskp()->stmtsp());
            for (V3TaskConnects::iterator it = tconnects.begin(); it != tconnects.end(); ++it) {
                AstVar* portp = it->first;
                AstArg* argp = it->second;
                AstNode* pinp = argp->exprp();
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
            V3TaskConnects tconnects = V3Task::taskConnects(nodep, nodep->taskp()->stmtsp());
            for (V3TaskConnects::iterator it = tconnects.begin(); it != tconnects.end(); ++it) {
                AstVar* portp = it->first;
                AstArg* argp = it->second;
                AstNode* pinp = argp->exprp();
                if (!pinp) continue;  // Argument error we'll find later
                if (portp->direction() == VDirection::REF
                    && !similarDTypeRecurse(portp->dtypep(), pinp->dtypep())) {
                    pinp->v3error("Ref argument requires matching types;"
                                  << " port " << portp->prettyNameQ() << " requires "
                                  << portp->prettyTypeName() << " but connection is "
                                  << pinp->prettyTypeName() << ".");
                } else if (portp->isWritable() && pinp->width() != portp->width()) {
                    pinp->v3error("Unsupported: Function output argument "
                                  << portp->prettyNameQ() << " requires " << portp->width()
                                  << " bits, but connection's " << pinp->prettyTypeName()
                                  << " generates " << pinp->width() << " bits.");
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
    virtual void visit(AstNodeFTaskRef* nodep) VL_OVERRIDE {
        // For arguments, is assignment-like context; see IEEE rules in AstNodeAssign
        // Function hasn't been widthed, so make it so.
        UINFO(5, "  FTASKREF " << nodep << endl);
        UASSERT_OBJ(nodep->taskp(), nodep, "Unlinked");
        if (nodep->didWidth()) return;
        userIterate(nodep->taskp(), NULL);
        // And do the arguments to the task/function too
        processFTaskRefArgs(nodep);
        nodep->didWidth(true);
    }
    virtual void visit(AstInitial* nodep) VL_OVERRIDE {
        assertAtStatement(nodep);
        m_initialp = nodep;
        userIterateChildren(nodep, NULL);
        m_initialp = NULL;
    }
    virtual void visit(AstNetlist* nodep) VL_OVERRIDE {
        // Iterate modules backwards, in bottom-up order.  That's faster
        userIterateChildrenBackwards(nodep, NULL);
    }

    //--------------------
    // Default
    virtual void visit(AstNodeMath* nodep) VL_OVERRIDE {
        if (!nodep->didWidth()) {
            nodep->v3fatalSrc(
                "Visit function missing? Widthed function missing for math node: " << nodep);
        }
        userIterateChildren(nodep, NULL);
    }
    virtual void visit(AstNode* nodep) VL_OVERRIDE {
        // Default: Just iterate
        UASSERT_OBJ(!m_vup, nodep,
                    "Visit function missing? Widthed expectation for this node: " << nodep);
        userIterateChildren(nodep, NULL);
    }

    //----------------------------------------------------------------------
    // WIDTH METHODs -- all iterate

    void visit_Or_Lu64(AstNodeUniop* nodep) {
        // CALLER: AstBitsToRealD
        // Real: Output real
        // LHS presumed self-determined, then coerced to real
        if (m_vup->prelim()) {  // First stage evaluation
            nodep->dtypeSetDouble();
            AstNodeDType* subDTypep = nodep->findLogicDType(64, 64, VSigning::UNSIGNED);
            // Self-determined operand
            userIterateAndNext(nodep->lhsp(), WidthVP(SELF, PRELIM).p());
            iterateCheck(nodep, "LHS", nodep->lhsp(), SELF, FINAL, subDTypep, EXTEND_EXP);
        }
    }
    void visit_Or_Ls32(AstNodeUniop* nodep) {
        // CALLER: AstIToRD
        // Real: Output real
        // LHS presumed self-determined, then coerced to real
        if (m_vup->prelim()) {  // First stage evaluation
            nodep->dtypeSetDouble();
            AstNodeDType* subDTypep = nodep->findLogicDType(32, 32, VSigning::SIGNED);
            // Self-determined operand
            userIterateAndNext(nodep->lhsp(), WidthVP(SELF, PRELIM).p());
            iterateCheck(nodep, "LHS", nodep->lhsp(), SELF, FINAL, subDTypep, EXTEND_EXP);
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
            nodep->dtypeSetLogicBool();
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
            nodep->dtypeSetLogicBool();
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
            nodep->dtypeSetLogicBool();
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
            nodep->dtypeSetLogicBool();
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
                if (AstNodeBiop* newp = replaceWithDVersion(nodep)) {
                    VL_DANGLING(nodep);
                    nodep = newp;  // Process new node instead
                    iterateCheckReal(nodep, "LHS", nodep->lhsp(), FINAL);
                    iterateCheckReal(nodep, "RHS", nodep->rhsp(), FINAL);
                }
            } else if (nodep->lhsp()->isString() || nodep->rhsp()->isString()) {
                if (AstNodeBiop* newp = replaceWithNVersion(nodep)) {
                    VL_DANGLING(nodep);
                    nodep = newp;  // Process new node instead
                    iterateCheckString(nodep, "LHS", nodep->lhsp(), FINAL);
                    iterateCheckString(nodep, "RHS", nodep->rhsp(), FINAL);
                }
            } else {
                bool signedFl = nodep->lhsp()->isSigned() && nodep->rhsp()->isSigned();
                if (AstNodeBiop* newp = replaceWithUOrSVersion(nodep, signedFl)) {
                    VL_DANGLING(nodep);
                    nodep = newp;  // Process new node instead
                }
                int width = std::max(nodep->lhsp()->width(), nodep->rhsp()->width());
                int ewidth = std::max(nodep->lhsp()->widthMin(), nodep->rhsp()->widthMin());
                AstNodeDType* subDTypep
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
            nodep->dtypeSetLogicBool();
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
            nodep->dtypeSetLogicBool();
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
            nodep->dtypeSetLogicBool();
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
        // CALLER: (real_ok=true) Negate
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
            if (AstNodeUniop* newp = replaceWithDVersion(nodep)) {
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
            AstNodeDType* expDTypep = m_vup->dtypeOverridep(nodep->dtypep());
            nodep->dtypep(expDTypep);  // Propagate expression type to negation
            AstNodeDType* subDTypep = expDTypep;
            iterateCheck(nodep, "LHS", nodep->lhsp(), CONTEXT, FINAL, subDTypep, EXTEND_EXP);
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
            int width = nodep->lhsp()->width();
            AstNodeDType* expDTypep = nodep->findLogicDType(width, width, rs_out);
            nodep->dtypep(expDTypep);
            AstNodeDType* subDTypep = expDTypep;
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
        AstNodeBiop* newp = iterate_shift_final(nodep);
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
            AstNodeDType* expDTypep = m_vup->dtypeOverridep(nodep->dtypep());
            AstNodeDType* subDTypep = expDTypep;
            nodep->dtypeFrom(expDTypep);
            // ShiftRS converts to ShiftR, but not vice-versa
            if (VN_IS(nodep, ShiftRS)) {
                if (AstNodeBiop* newp = replaceWithUOrSVersion(nodep, nodep->isSigned())) {
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
                AstConst* shiftp = VN_CAST(nodep->rhsp(), Const);
                if (shiftp && shiftp->num().mostSetBitP1() <= 32) {
                    // If (number)<<96'h1, then make it into (number)<<32'h1
                    V3Number num(shiftp, 32, 0);
                    num.opAssign(shiftp->num());
                    AstNode* shiftrhsp = nodep->rhsp();
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
            int width = std::max(nodep->lhsp()->width(), nodep->rhsp()->width());
            int mwidth = std::max(nodep->lhsp()->widthMin(), nodep->rhsp()->widthMin());
            bool expSigned = (nodep->lhsp()->isSigned() && nodep->rhsp()->isSigned());
            nodep->dtypeChgWidthSigned(width, mwidth, VSigning::fromBool(expSigned));
        }
        if (m_vup->final()) {
            AstNodeDType* expDTypep = m_vup->dtypeOverridep(nodep->dtypep());
            AstNodeDType* subDTypep = expDTypep;
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
                if (AstNodeBiop* newp = replaceWithDVersion(nodep)) {
                    VL_DANGLING(nodep);
                    nodep = newp;  // Process new node instead
                }
                nodep->dtypeSetDouble();
                iterateCheckReal(nodep, "LHS", nodep->lhsp(), FINAL);
                iterateCheckReal(nodep, "RHS", nodep->rhsp(), FINAL);
                return;
            } else {
                int width = std::max(nodep->lhsp()->width(), nodep->rhsp()->width());
                int mwidth = std::max(nodep->lhsp()->widthMin(), nodep->rhsp()->widthMin());
                bool expSigned = (nodep->lhsp()->isSigned() && nodep->rhsp()->isSigned());
                nodep->dtypeChgWidthSigned(width, mwidth, VSigning::fromBool(expSigned));
            }
        }
        if (m_vup->final()) {
            // Parent's data type was computed using the max(upper, nodep->dtype)
            AstNodeDType* expDTypep = m_vup->dtypeOverridep(nodep->dtypep());
            AstNodeDType* subDTypep = expDTypep;
            nodep->dtypeFrom(expDTypep);
            // We don't use LHS && RHS -- unspecified language corner, see t_math_signed5 test
            // bool expSigned = (nodep->lhsp()->isSigned() && nodep->rhsp()->isSigned());
            if (AstNodeBiop* newp = replaceWithUOrSVersion(nodep, expDTypep->isSigned())) {
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
        int expWidth = expDTypep->width();
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
        AstConst* constp = VN_CAST(nodep, Const);
        int expWidth = expDTypep->width();
        if (constp && !constp->num().isNegative()) {
            // Save later constant propagation work, just right-size it.
            V3Number num(nodep, expWidth);
            num.opAssign(constp->num());
            num.isSigned(false);
            AstNode* newp = new AstConst(nodep->fileline(), num);
            constp->replaceWith(newp);
            VL_DO_DANGLING(pushDeletep(constp), constp);
            VL_DANGLING(nodep);
            nodep = newp;
        } else if (expWidth < nodep->width()) {
            // Trunc - Extract
            AstNRelinker linker;
            nodep->unlinkFrBack(&linker);
            AstNode* newp = new AstSel(nodep->fileline(), nodep, 0, expWidth);
            newp->didWidth(true);  // Don't replace dtype with unsigned
            linker.relink(newp);
            nodep = newp;
        } else {
            // Extend
            AstNRelinker linker;
            nodep->unlinkFrBack(&linker);
            bool doSigned = false;
            switch (extendRule) {
            case EXTEND_ZERO: doSigned = false; break;
            case EXTEND_EXP: doSigned = nodep->isSigned() && expDTypep->isSigned(); break;
            case EXTEND_LHS: doSigned = nodep->isSigned(); break;
            default: nodep->v3fatalSrc("bad case");
            }
            AstNode* newp
                = (doSigned ? static_cast<AstNode*>(new AstExtendS(nodep->fileline(), nodep))
                            : static_cast<AstNode*>(new AstExtend(nodep->fileline(), nodep)));
            linker.relink(newp);
            nodep = newp;
        }
        if (expDTypep->isDouble() && !nodep->isDouble()) {
            // For AstVar init() among others
            // TODO do all to-real and to-integer conversions in this function
            // rather than in callers
            AstNode* newp = spliceCvtD(nodep);
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
        int expWidth = 1;
        int expSigned = false;
        UINFO(4, "  widthReduce_old: " << nodep << endl);
        AstConst* constp = VN_CAST(nodep, Const);
        if (constp) {
            V3Number num(nodep, expWidth);
            num.opRedOr(constp->num());
            num.isSigned(expSigned);
            AstNode* newp = new AstConst(nodep->fileline(), num);
            constp->replaceWith(newp);
            VL_DO_DANGLING(constp->deleteTree(), constp);
            VL_DANGLING(nodep);
            nodep = newp;
        } else {
            AstNRelinker linker;
            nodep->unlinkFrBack(&linker);
            AstNode* newp = new AstRedOr(nodep->fileline(), nodep);
            linker.relink(newp);
            nodep = newp;
        }
        nodep->dtypeChgWidthSigned(expWidth, expWidth, VSigning::fromBool(expSigned));
        UINFO(4, "             _new: " << nodep << endl);
    }

    bool fixAutoExtend(AstNode*& nodepr, int expWidth) {
        // For SystemVerilog '0,'1,'x,'z, autoextend and don't warn
        if (AstConst* constp = VN_CAST(nodepr, Const)) {
            if (constp->num().autoExtend() && !constp->num().sized() && constp->width() == 1) {
                // Make it the proper size.  Careful of proper extension of 0's/1's
                V3Number num(constp, expWidth);
                num.opRepl(constp->num(), expWidth);  // {width{'1}}
                AstNode* newp = new AstConst(constp->fileline(), num);
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
                AstNode* newp = new AstConst(constp->fileline(), num);
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

    bool similarDTypeRecurse(AstNodeDType* node1p, AstNodeDType* node2p) {
        return node1p->skipRefp()->similarDType(node2p->skipRefp());
    }
    void iterateCheckFileDesc(AstNode* nodep, AstNode* underp, Stage stage) {
        UASSERT_OBJ(stage == BOTH, nodep, "Bad call");
        // underp may change as a result of replacement
        underp = userIterateSubtreeReturnEdits(underp, WidthVP(SELF, PRELIM).p());
        AstNodeDType* expDTypep = underp->findUInt32DType();
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
            AstNodeDType* expDTypep = nodep->findSigned32DType();
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
            AstNodeDType* expDTypep = nodep->findDoubleDType();
            underp = iterateCheck(nodep, side, underp, SELF, FINAL, expDTypep, EXTEND_EXP);
        }
        if (underp) {}  // cppcheck
    }
    void iterateCheckString(AstNode* nodep, const char* side, AstNode* underp, Stage stage) {
        if (stage & PRELIM) {
            underp = userIterateSubtreeReturnEdits(underp, WidthVP(SELF, PRELIM).p());
        }
        if (stage & FINAL) {
            AstNodeDType* expDTypep = nodep->findStringDType();
            underp = iterateCheck(nodep, side, underp, SELF, FINAL, expDTypep, EXTEND_EXP);
        }
        if (underp) {}  // cppcheck
    }
    void iterateCheckTyped(AstNode* nodep, const char* side, AstNode* underp,
                           AstNodeDType* expDTypep, Stage stage) {
        if (stage & PRELIM) {
            underp = userIterateSubtreeReturnEdits(underp, WidthVP(SELF, PRELIM).p());
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
        AstNodeDType* expDTypep = underp->dtypep();
        underp = iterateCheck(nodep, side, underp, SELF, FINAL, expDTypep, EXTEND_EXP);
        if (underp) {}  // cppcheck
    }
    void iterateCheckAssign(AstNode* nodep, const char* side, AstNode* rhsp, Stage stage,
                            AstNodeDType* lhsDTypep) {
        // Check using assignment-like context rules
        // if (debug()) nodep->dumpTree(cout, "-checkass: ");
        UASSERT_OBJ(stage == FINAL, nodep, "Bad width call");
        // We iterate and size the RHS based on the result of RHS evaluation
        bool lhsStream
            = (VN_IS(nodep, NodeAssign) && VN_IS(VN_CAST(nodep, NodeAssign)->lhsp(), NodeStream));
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
        if (underp && underp->isDouble()) {
            UINFO(6, "   spliceCvtCmpD0: " << underp << endl);
            AstNRelinker linker;
            underp->unlinkFrBack(&linker);
            AstNode* newp
                = new AstNeqD(nodep->fileline(), underp,
                              new AstConst(nodep->fileline(), AstConst::RealDouble(), 0.0));
            linker.relink(newp);
        } else if (!underp->dtypep()->basicp()) {
            nodep->v3error("Logical Operator " << nodep->prettyTypeName()
                                               << " expects a non-complex data type on the "
                                               << side << ".");
            underp->replaceWith(new AstConst(nodep->fileline(), AstConst::LogicFalse()));
            VL_DO_DANGLING(pushDeletep(underp), underp);
        } else {
            bool bad = widthBad(underp, nodep->findLogicBoolDType());
            if (bad) {
                {  // if (warnOn), but not needed here
                    if (debug() > 4) nodep->backp()->dumpTree(cout, "  back: ");
                    nodep->v3warn(WIDTH, "Logical Operator "
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
            underp = userIterateSubtreeReturnEdits(underp, WidthVP(SELF, FINAL).p());
        } else if (expDTypep->isDouble() && underp->isDouble()) {  // Also good
            underp = userIterateSubtreeReturnEdits(underp, WidthVP(SELF, FINAL).p());
        } else if (expDTypep->isDouble() && !underp->isDouble()) {
            underp = spliceCvtD(underp);
            underp = userIterateSubtreeReturnEdits(underp, WidthVP(SELF, FINAL).p());
        } else if (!expDTypep->isDouble() && underp->isDouble()) {
            underp = spliceCvtS(underp, true, expDTypep->width());  // Round RHS
            underp = userIterateSubtreeReturnEdits(underp, WidthVP(SELF, FINAL).p());
        } else if (expDTypep->isString() && !underp->dtypep()->isString()) {
            underp = spliceCvtString(underp);
            underp = userIterateSubtreeReturnEdits(underp, WidthVP(SELF, FINAL).p());
        } else {
            AstBasicDType* expBasicp = expDTypep->basicp();
            AstBasicDType* underBasicp = underp->dtypep()->basicp();
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
                // Hope it just works out
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
        AstBasicDType* expBasicp = expDTypep->basicp();
        AstBasicDType* underBasicp = underp->dtypep()->basicp();
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
            int expWidth = expDTypep->width();
            int expWidthMin = expDTypep->widthMin();
            if (expWidthMin == 0) expWidthMin = expWidth;
            bool bad = widthBad(underp, expDTypep);
            if ((bad || underp->width() != expWidth) && fixAutoExtend(underp /*ref*/, expWidth)) {
                underp = NULL;  // Changes underp
                return;
            }
            if (VN_IS(underp, Const) && VN_CAST(underp, Const)->num().isFromString()
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
                AstNodeAssign* assignp = VN_CAST(nodep, NodeAssign);
                AstPin* pinp = VN_CAST(nodep, Pin);
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
            AstNRelinker linker;
            nodep->unlinkFrBack(&linker);
            AstNode* newp = new AstIToRD(nodep->fileline(), nodep);
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
            AstNRelinker linker;
            nodep->unlinkFrBack(&linker);
            if (AstConst* constp = VN_CAST(nodep, Const)) {
                // We convert to/from vlsint32 rather than use floor() as want to make sure is
                // representable in integer's number of bits
                if (constp->isDouble()
                    && v3EpsilonEqual(
                        constp->num().toDouble(),
                        static_cast<double>(static_cast<vlsint32_t>(constp->num().toDouble())))) {
                    warnOn = false;
                }
            }
            if (warnOn) nodep->v3warn(REALCVT, "Implicit conversion of real to integer");
            AstNode* newp = new AstRToIRoundS(nodep->fileline(), nodep);
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
            AstNRelinker linker;
            nodep->unlinkFrBack(&linker);
            AstNode* newp = new AstCvtPackString(nodep->fileline(), nodep);
            linker.relink(newp);
            return newp;
        } else {
            return nodep;
        }
    }
    AstNodeBiop* replaceWithUOrSVersion(AstNodeBiop* nodep, bool signedFlavorNeeded) {
        // Given a signed/unsigned node type, create the opposite type
        // Return new node or NULL if nothing
        if (signedFlavorNeeded == nodep->signedFlavor()) return NULL;
        if (!nodep->dtypep()) nodep->dtypeFrom(nodep->lhsp());
        // To simplify callers, some node types don't need to change
        switch (nodep->type()) {
        case AstType::atEq: nodep->dtypeChgSigned(signedFlavorNeeded); return NULL;
        case AstType::atNeq: nodep->dtypeChgSigned(signedFlavorNeeded); return NULL;
        case AstType::atEqCase: nodep->dtypeChgSigned(signedFlavorNeeded); return NULL;
        case AstType::atNeqCase: nodep->dtypeChgSigned(signedFlavorNeeded); return NULL;
        case AstType::atEqWild: nodep->dtypeChgSigned(signedFlavorNeeded); return NULL;
        case AstType::atNeqWild: nodep->dtypeChgSigned(signedFlavorNeeded); return NULL;
        case AstType::atAdd: nodep->dtypeChgSigned(signedFlavorNeeded); return NULL;
        case AstType::atSub: nodep->dtypeChgSigned(signedFlavorNeeded); return NULL;
        case AstType::atShiftL: nodep->dtypeChgSigned(signedFlavorNeeded); return NULL;
        default: break;
        }
        FileLine* fl = nodep->fileline();
        AstNode* lhsp = nodep->lhsp()->unlinkFrBack();
        AstNode* rhsp = nodep->rhsp()->unlinkFrBack();
        AstNodeBiop* newp = NULL;
        switch (nodep->type()) {
        case AstType::atGt: newp = new AstGtS(fl, lhsp, rhsp); break;
        case AstType::atGtS: newp = new AstGt(fl, lhsp, rhsp); break;
        case AstType::atGte: newp = new AstGteS(fl, lhsp, rhsp); break;
        case AstType::atGteS: newp = new AstGte(fl, lhsp, rhsp); break;
        case AstType::atLt: newp = new AstLtS(fl, lhsp, rhsp); break;
        case AstType::atLtS: newp = new AstLt(fl, lhsp, rhsp); break;
        case AstType::atLte: newp = new AstLteS(fl, lhsp, rhsp); break;
        case AstType::atLteS: newp = new AstLte(fl, lhsp, rhsp); break;
        case AstType::atDiv: newp = new AstDivS(fl, lhsp, rhsp); break;
        case AstType::atDivS: newp = new AstDiv(fl, lhsp, rhsp); break;
        case AstType::atModDiv: newp = new AstModDivS(fl, lhsp, rhsp); break;
        case AstType::atModDivS: newp = new AstModDiv(fl, lhsp, rhsp); break;
        case AstType::atMul: newp = new AstMulS(fl, lhsp, rhsp); break;
        case AstType::atMulS: newp = new AstMul(fl, lhsp, rhsp); break;
        case AstType::atShiftR: newp = new AstShiftRS(fl, lhsp, rhsp); break;
        case AstType::atShiftRS: newp = new AstShiftR(fl, lhsp, rhsp); break;
        default:
            nodep->v3fatalSrc("Node needs sign change, but bad case: " << nodep << endl);
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
        // Return new node or NULL if nothing
        if (nodep->doubleFlavor()) { return NULL; }
        FileLine* fl = nodep->fileline();
        AstNode* lhsp = nodep->lhsp()->unlinkFrBack();
        AstNode* rhsp = nodep->rhsp()->unlinkFrBack();
        AstNodeBiop* newp = NULL;
        // No width change on output;...                // All below have bool or double outputs
        switch (nodep->type()) {
        case AstType::atAdd: newp = new AstAddD(fl, lhsp, rhsp); break;
        case AstType::atSub: newp = new AstSubD(fl, lhsp, rhsp); break;
        case AstType::atPow: newp = new AstPowD(fl, lhsp, rhsp); break;
        case AstType::atEq:
        case AstType::atEqCase: newp = new AstEqD(fl, lhsp, rhsp); break;
        case AstType::atNeq:
        case AstType::atNeqCase: newp = new AstNeqD(fl, lhsp, rhsp); break;
        case AstType::atGt:
        case AstType::atGtS: newp = new AstGtD(fl, lhsp, rhsp); break;
        case AstType::atGte:
        case AstType::atGteS: newp = new AstGteD(fl, lhsp, rhsp); break;
        case AstType::atLt:
        case AstType::atLtS: newp = new AstLtD(fl, lhsp, rhsp); break;
        case AstType::atLte:
        case AstType::atLteS: newp = new AstLteD(fl, lhsp, rhsp); break;
        case AstType::atDiv:
        case AstType::atDivS: newp = new AstDivD(fl, lhsp, rhsp); break;
        case AstType::atMul:
        case AstType::atMulS: newp = new AstMulD(fl, lhsp, rhsp); break;
        default:
            nodep->v3fatalSrc("Node needs conversion to double, but bad case: " << nodep << endl);
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
        // Return new node or NULL if nothing
        if (nodep->stringFlavor()) return NULL;
        FileLine* fl = nodep->fileline();
        AstNode* lhsp = nodep->lhsp()->unlinkFrBack();
        AstNode* rhsp = nodep->rhsp()->unlinkFrBack();
        AstNodeBiop* newp = NULL;
        // No width change on output;...                // All below have bool or double outputs
        switch (nodep->type()) {
        case AstType::atEq:
        case AstType::atEqCase: newp = new AstEqN(fl, lhsp, rhsp); break;
        case AstType::atNeq:
        case AstType::atNeqCase: newp = new AstNeqN(fl, lhsp, rhsp); break;
        case AstType::atGt:
        case AstType::atGtS: newp = new AstGtN(fl, lhsp, rhsp); break;
        case AstType::atGte:
        case AstType::atGteS: newp = new AstGteN(fl, lhsp, rhsp); break;
        case AstType::atLt:
        case AstType::atLtS: newp = new AstLtN(fl, lhsp, rhsp); break;
        case AstType::atLte:
        case AstType::atLteS: newp = new AstLteN(fl, lhsp, rhsp); break;
        default:
            nodep->v3fatalSrc("Node needs conversion to string, but bad case: " << nodep << endl);
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
        // Return new node or NULL if nothing
        if (nodep->doubleFlavor()) return NULL;
        FileLine* fl = nodep->fileline();
        AstNode* lhsp = nodep->lhsp()->unlinkFrBack();
        AstNodeUniop* newp = NULL;
        switch (nodep->type()) {
        case AstType::atNegate: newp = new AstNegateD(fl, lhsp); break;
        default:
            nodep->v3fatalSrc("Node needs conversion to double, but bad case: " << nodep << endl);
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
        AstArg* argp = VN_CAST(nodep->pinsp(), Arg);
        if (!argp) {
            nodep->v3error("Argument needed for string." + nodep->prettyName() + " method");
            return;
        }
        AstNodeVarRef* fromp = VN_CAST(nodep->fromp()->unlinkFrBack(), VarRef);
        AstNode* newp = new AstAssign(
            nodep->fileline(), fromp,
            new AstSFormatF(nodep->fileline(), format, false, argp->exprp()->unlinkFrBack()));
        fromp->lvalue(true);
        nodep->replaceWith(newp);
        VL_DO_DANGLING(pushDeletep(nodep), nodep);
    }

    //----------------------------------------------------------------------
    // METHODS - data types

    AstNodeDType* moveDTypeEdit(AstNode* nodep, AstNodeDType* dtnodep) {
        // DTypes at parse time get added as a e.g. childDType to some node types such as AstVars.
        // Move type to global scope, so removing/changing a variable won't lose the dtype.
        UASSERT_OBJ(dtnodep, nodep, "Caller should check for NULL before calling moveDTypeEdit");
        UINFO(9, "moveDTypeEdit  " << dtnodep << endl);
        dtnodep->unlinkFrBack();  // Make non-child
        v3Global.rootp()->typeTablep()->addTypesp(dtnodep);
        return dtnodep;
    }
    AstNodeDType* moveChildDTypeEdit(AstNode* nodep) {
        return moveDTypeEdit(nodep, nodep->getChildDTypep());
    }
    AstNodeDType* iterateEditDTypep(AstNode* parentp, AstNodeDType* nodep) {
        // Iterate into a data type to resolve that type. This process
        // may eventually create a new data type, but not today
        // it may make a new datatype, need subChildDType() to point to it;
        // maybe we have user5p indicate a "replace me with" pointer.
        // Need to be careful with "implicit" types though.
        //
        // Alternative is to have WidthVP return information.
        // or have a call outside of normal visitor land.
        // or have a m_return type (but need to return if width called multiple times)
        UASSERT_OBJ(nodep, parentp, "Null dtype when widthing dtype");
        userIterate(nodep, NULL);
        return nodep;
    }

    AstConst* dimensionValue(FileLine* fileline, AstNodeDType* nodep, AstAttrType attrType,
                             int dim) {
        // Return the dimension value for the specified attribute and constant dimension
        AstNodeDType* dtypep = nodep->skipRefp();
        VNumRange declRange;  // ranged() set false
        for (int i = 1; i <= dim; ++i) {
            // UINFO(9, "   dim at "<<dim<<"  "<<dtypep<<endl);
            declRange = VNumRange();  // ranged() set false
            if (AstNodeArrayDType* adtypep = VN_CAST(dtypep, NodeArrayDType)) {
                declRange = adtypep->declRange();
                if (i < dim) dtypep = adtypep->subDTypep()->skipRefp();
                continue;
            } else if (AstNodeUOrStructDType* adtypep = VN_CAST(dtypep, NodeUOrStructDType)) {
                declRange = adtypep->declRange();
                break;  // Sub elements don't look like arrays and can't iterate into
            } else if (AstBasicDType* adtypep = VN_CAST(dtypep, BasicDType)) {
                if (adtypep->isRanged()) declRange = adtypep->declRange();
                break;
            }
            break;
        }
        AstConst* valp = NULL;  // If NULL, construct from val
        int val = 0;
        switch (attrType) {
        case AstAttrType::DIM_BITS: {
            int bits = 1;
            while (dtypep) {
                // UINFO(9, "   bits at "<<bits<<"  "<<dtypep<<endl);
                if (AstNodeArrayDType* adtypep = VN_CAST(dtypep, NodeArrayDType)) {
                    bits *= adtypep->declRange().elements();
                    dtypep = adtypep->subDTypep()->skipRefp();
                    continue;
                } else if (AstNodeUOrStructDType* adtypep = VN_CAST(dtypep, NodeUOrStructDType)) {
                    bits *= adtypep->width();
                    break;
                } else if (AstBasicDType* adtypep = VN_CAST(dtypep, BasicDType)) {
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
            break;
        }
        case AstAttrType::DIM_HIGH: val = !declRange.ranged() ? 0 : declRange.hi(); break;
        case AstAttrType::DIM_LEFT: val = !declRange.ranged() ? 0 : declRange.left(); break;
        case AstAttrType::DIM_LOW: val = !declRange.ranged() ? 0 : declRange.lo(); break;
        case AstAttrType::DIM_RIGHT: val = !declRange.ranged() ? 0 : declRange.right(); break;
        case AstAttrType::DIM_INCREMENT:
            val = (declRange.ranged() && declRange.littleEndian()) ? -1 : 1;
            break;
        case AstAttrType::DIM_SIZE: val = !declRange.ranged() ? 0 : declRange.elements(); break;
        default: nodep->v3fatalSrc("Missing DIM ATTR type case"); break;
        }
        if (!valp) valp = new AstConst(fileline, AstConst::Signed32(), val);
        UINFO(9, " $dimension " << attrType.ascii() << "(" << cvtToHex(dtypep) << "," << dim
                                << ")=" << valp << endl);
        return valp;
    }
    AstVar* dimensionVarp(AstNodeDType* nodep, AstAttrType attrType, uint32_t msbdim) {
        // Return a variable table which has specified dimension properties for this variable
        TableMap::iterator pos = m_tableMap.find(make_pair(nodep, attrType));
        if (pos != m_tableMap.end()) return pos->second;
        AstNodeArrayDType* vardtypep
            = new AstUnpackArrayDType(nodep->fileline(), nodep->findSigned32DType(),
                                      new AstRange(nodep->fileline(), msbdim, 0));
        AstInitArray* initp = new AstInitArray(nodep->fileline(), vardtypep, NULL);
        v3Global.rootp()->typeTablep()->addTypesp(vardtypep);
        AstVar* varp = new AstVar(nodep->fileline(), AstVarType::MODULETEMP,
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
        userIterate(varp, NULL);  // May have already done $unit so must do this var
        m_tableMap.insert(make_pair(make_pair(nodep, attrType), varp));
        return varp;
    }
    AstVar* enumVarp(AstEnumDType* nodep, AstAttrType attrType, uint32_t msbdim) {
        // Return a variable table which has specified dimension properties for this variable
        TableMap::iterator pos = m_tableMap.find(make_pair(nodep, attrType));
        if (pos != m_tableMap.end()) return pos->second;
        UINFO(9, "Construct Venumtab attr=" << attrType.ascii() << " max=" << msbdim << " for "
                                            << nodep << endl);
        AstNodeDType* basep;
        if (attrType == AstAttrType::ENUM_NAME) {
            basep = nodep->findStringDType();
        } else {
            basep = nodep->dtypep();
        }
        AstNodeArrayDType* vardtypep = new AstUnpackArrayDType(
            nodep->fileline(), basep, new AstRange(nodep->fileline(), msbdim, 0));
        AstInitArray* initp = new AstInitArray(nodep->fileline(), vardtypep, NULL);
        v3Global.rootp()->typeTablep()->addTypesp(vardtypep);
        AstVar* varp = new AstVar(nodep->fileline(), AstVarType::MODULETEMP,
                                  "__Venumtab_" + VString::downcase(attrType.ascii())
                                      + cvtToStr(m_dtTables++),
                                  vardtypep);
        varp->isConst(true);
        varp->isStatic(true);
        varp->valuep(initp);
        // Add to root, as don't know module we are in, and aids later structure sharing
        v3Global.rootp()->dollarUnitPkgAddp()->addStmtp(varp);

        // Default for all unspecified values
        if (attrType == AstAttrType::ENUM_NAME) {
            initp->defaultp(new AstConst(nodep->fileline(), AstConst::String(), ""));
        } else if (attrType == AstAttrType::ENUM_NEXT || attrType == AstAttrType::ENUM_PREV) {
            initp->defaultp(new AstConst(nodep->fileline(), V3Number(nodep, nodep->width(), 0)));
        } else {
            nodep->v3fatalSrc("Bad case");
        }

        // Find valid values and populate
        UASSERT_OBJ(nodep->itemsp(), nodep, "enum without items");
        std::vector<AstNode*> values;
        values.resize(msbdim + 1);
        for (unsigned i = 0; i < (msbdim + 1); ++i) values[i] = NULL;
        {
            AstEnumItem* firstp = nodep->itemsp();
            AstEnumItem* prevp = firstp;  // Prev must start with last item
            while (prevp->nextp()) prevp = VN_CAST(prevp->nextp(), EnumItem);
            for (AstEnumItem* itemp = firstp; itemp;) {
                AstEnumItem* nextp = VN_CAST(itemp->nextp(), EnumItem);
                const AstConst* vconstp = VN_CAST(itemp->valuep(), Const);
                UASSERT_OBJ(vconstp, nodep, "Enum item without constified value");
                uint32_t i = vconstp->toUInt();
                if (attrType == AstAttrType::ENUM_NAME) {
                    values[i] = new AstConst(nodep->fileline(), AstConst::String(), itemp->name());
                } else if (attrType == AstAttrType::ENUM_NEXT) {
                    values[i] = (nextp ? nextp : firstp)->valuep()->cloneTree(false);  // A const
                } else if (attrType == AstAttrType::ENUM_PREV) {
                    values[i] = prevp->valuep()->cloneTree(false);  // A const
                } else {
                    nodep->v3fatalSrc("Bad case");
                }
                prevp = itemp;
                itemp = nextp;
            }
        }
        // Add all specified values to table
        for (unsigned i = 0; i < (msbdim + 1); ++i) {
            AstNode* valp = values[i];
            if (valp) initp->addIndexValuep(i, valp);
        }
        userIterate(varp, NULL);  // May have already done $unit so must do this var
        m_tableMap.insert(make_pair(make_pair(nodep, attrType), varp));
        return varp;
    }

    PatVecMap patVectorMap(AstPattern* nodep, const VNumRange& range) {
        PatVecMap patmap;
        int element = range.left();
        for (AstPatMember* patp = VN_CAST(nodep->itemsp(), PatMember); patp;
             patp = VN_CAST(patp->nextp(), PatMember)) {
            if (patp->keyp()) {
                if (const AstConst* constp = VN_CAST(patp->keyp(), Const)) {
                    element = constp->toSInt();
                } else {
                    patp->keyp()->v3error("Assignment pattern key not supported/understood: "
                                          << patp->keyp()->prettyTypeName());
                }
            }
            if (patmap.find(element) != patmap.end()) {
                patp->v3error("Assignment pattern key used multiple times: " << element);
            } else {
                patmap.insert(make_pair(element, patp));
            }
            element += range.leftToRightInc();
        }
        return patmap;
    }

    void makeOpenArrayShell(AstNodeFTaskRef* nodep) {
        UINFO(4, "Replicate openarray function " << nodep->taskp() << endl);
        AstNodeFTask* oldTaskp = nodep->taskp();
        oldTaskp->dpiOpenParentInc();
        UASSERT_OBJ(!oldTaskp->dpiOpenChild(), oldTaskp,
                    "DPI task should be parent or child, not both");
        AstNodeFTask* newTaskp = oldTaskp->cloneTree(false);
        newTaskp->dpiOpenChild(true);
        newTaskp->dpiOpenParentClear();
        newTaskp->name(newTaskp->name() + "__Vdpioc" + cvtToStr(oldTaskp->dpiOpenParent()));
        oldTaskp->addNextHere(newTaskp);
        // Relink reference to new function
        nodep->taskp(newTaskp);
        nodep->name(nodep->taskp()->name());
        // Replace open array arguments with the callee's task
        V3TaskConnects tconnects = V3Task::taskConnects(nodep, nodep->taskp()->stmtsp());
        for (V3TaskConnects::iterator it = tconnects.begin(); it != tconnects.end(); ++it) {
            AstVar* portp = it->first;
            AstArg* argp = it->second;
            AstNode* pinp = argp->exprp();
            if (!pinp) continue;  // Argument error we'll find later
            if (hasOpenArrayIterateDType(portp->dtypep())) portp->dtypep(pinp->dtypep());
        }
    }

    bool markHasOpenArray(AstNodeFTask* nodep) {
        bool hasOpen = false;
        for (AstNode* stmtp = nodep->stmtsp(); stmtp; stmtp = stmtp->nextp()) {
            if (AstVar* portp = VN_CAST(stmtp, Var)) {
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

    //----------------------------------------------------------------------
    // METHODS - special iterators
    // These functions save/restore the AstNUser information so it can pass to child nodes.

    AstNode* userIterateSubtreeReturnEdits(AstNode* nodep, WidthVP* vup) {
        if (!nodep) return NULL;
        WidthVP* saveVup = m_vup;
        AstNode* ret;
        {
            m_vup = vup;
            ret = iterateSubtreeReturnEdits(nodep);
        }
        m_vup = saveVup;
        return ret;
    }
    void userIterate(AstNode* nodep, WidthVP* vup) {
        if (!nodep) return;
        WidthVP* saveVup = m_vup;
        {
            m_vup = vup;
            iterate(nodep);
        }
        m_vup = saveVup;
    }
    void userIterateAndNext(AstNode* nodep, WidthVP* vup) {
        if (!nodep) return;
        WidthVP* saveVup = m_vup;
        {
            m_vup = vup;
            iterateAndNextNull(nodep);
        }
        m_vup = saveVup;
    }
    void userIterateChildren(AstNode* nodep, WidthVP* vup) {
        if (!nodep) return;
        WidthVP* saveVup = m_vup;
        {
            m_vup = vup;
            iterateChildren(nodep);
        }
        m_vup = saveVup;
    }
    void userIterateChildrenBackwards(AstNode* nodep, WidthVP* vup) {
        if (!nodep) return;
        WidthVP* saveVup = m_vup;
        {
            m_vup = vup;
            iterateChildrenBackwards(nodep);
        }
        m_vup = saveVup;
    }

public:
    // CONSTRUCTORS
    WidthVisitor(bool paramsOnly,  // [in] TRUE if we are considering parameters only.
                 bool doGenerate) {  // [in] TRUE if we are inside a generate statement and
        //                           // don't wish to trigger errors
        m_paramsOnly = paramsOnly;
        m_cellRangep = NULL;
        m_ftaskp = NULL;
        m_funcp = NULL;
        m_initialp = NULL;
        m_attrp = NULL;
        m_doGenerate = doGenerate;
        m_dtTables = 0;
        m_vup = NULL;
    }
    AstNode* mainAcceptEdit(AstNode* nodep) {
        return userIterateSubtreeReturnEdits(nodep, WidthVP(SELF, BOTH).p());
    }
    virtual ~WidthVisitor() {}
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
        WidthClearVisitor cvisitor(nodep);
        WidthVisitor visitor(false, false);
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
    WidthVisitor visitor(true, false);
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
    WidthVisitor visitor(true, true);
    nodep = visitor.mainAcceptEdit(nodep);
    // No WidthRemoveVisitor, as don't want to drop $signed etc inside gen blocks
    return nodep;
}

void V3Width::widthCommit(AstNetlist* nodep) {
    UINFO(2, __FUNCTION__ << ": " << endl);
    { WidthCommitVisitor visitor(nodep); }  // Destruct before checking
    V3Global::dumpCheckGlobalTree("widthcommit", 0, v3Global.opt.dumpTreeLevel(__FILE__) >= 6);
}
