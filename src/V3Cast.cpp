// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Add C++ casts across expression size changes
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2004-2026 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************
// V3Cast's Transformations:
//
// Each module:
//      For each expression, if above expression requires 32 bits,
//      and this isn't, cast to 32 bits.
//      Likewise for 64 bit expressions.
//
// C++ rules:
//      Integral promotions allow conversion to larger int.  Unsigned is only
//      used if a int would not fit the value.
//
//      Bools converts to int, not unsigned.
//
//      Most operations return unsigned if either operand is unsigned.
//
//      Unsignedness can be lost on results of the below operations, as they
//      may need the sign bit for proper operation:
//              /, %, /=, %=, <, <=, >, or >=
//
//      Signed values are always sign extended on promotion or right shift,
//      even if assigning to a unsigned.
//
//*************************************************************************

#include "V3PchAstNoMT.h"  // VL_MT_DISABLED_CODE_UNIT

#include "V3Cast.h"

VL_DEFINE_DEBUG_FUNCTIONS;

//######################################################################
// Cast state, as a visitor of each AstNode

class CastQuadstateVisitor : public VNVisitor {
    // AstNodeExpr::user1()   -> bool whether it has been visited

    VNUser1InUse m_user1;

    static AstNodeDType* fourStateTypeFromTwoState(AstNodeDType* const nodep) {
        if (nodep->isFourstate()) return nodep;
        if (const AstBasicDType* const basicDTypep = VN_CAST(nodep, BasicDType)) {
            switch (basicDTypep->keyword()) {
            default:
            case VBasicDTypeKwd::BIT:
                return nodep->findLogicDType(basicDTypep->width(), basicDTypep->widthMin(),
                                             basicDTypep->numeric());
            case VBasicDTypeKwd::INT: return nodep->findSigned32DType();
            }
        }
        nodep->v3fatalSrc("Unsupported 2-state type promotion to 4-state - " << nodep);
        return nullptr;
    }

    static AstCFuncHard* wrapExprpInCFuncHard(AstNodeExpr* const exprp, const VCFunc func) {
        VNRelinker relinker;
        exprp->unlinkFrBack(&relinker);
        AstCFuncHard* const newp = new AstCFuncHard{exprp->fileline(), func, exprp};
        relinker.relink(newp);
        newp->user1(1);
        return newp;
    }

    static void castFourToTwo(AstNodeExpr* const exprp) {
        if (const AstConst* const constp = VN_CAST(exprp, Const)) {
            if (!constp->num().isAnyXZ()) return;
        } else if (!exprp->dtypep()->isFourstate()) {
            return;
        }
        VNRelinker relinker;
        exprp->unlinkFrBack(&relinker);
        AstCCast* const newp = new AstCCast{exprp->fileline(), exprp, exprp};
        newp->user1(1);
        relinker.relink(newp);
        newp->dtypeSetBitUnsized(exprp->dtypep()->width(), exprp->dtypep()->widthMin(),
                                 exprp->dtypep()->numeric());
    }

    static void castTwoToFour(AstNodeExpr* const exprp) {
        if (!VN_IS(exprp, Const) && exprp->dtypep()->isFourstate()) return;

        // Casting from four to two and back has some side effects e.g.: x becomes 0
        VNRelinker relinker;
        exprp->unlinkFrBack(&relinker);
        AstCCast* const newp
            = new AstCCast{exprp->fileline(), exprp, fourStateTypeFromTwoState(exprp->dtypep())};
        newp->user1(1);
        relinker.relink(newp);
    }

    static void expectNState(AstNodeExpr* const exprp, bool fourState) {
        if (exprp->dtypep()->isFourstate() == fourState) return;
        if (exprp->dtypep()->isFourstate()) {
            castFourToTwo(exprp);
        } else {
            castTwoToFour(exprp);
        }
    }

    void visit(AstNodeIf* const nodep) override {
        iterateChildren(nodep);
        if (nodep->condp()->dtypep()->isFourstate()) {
            wrapExprpInCFuncHard(nodep->condp(), VCFunc::FOUR_STATE_IS_TRUE);
        }
    }
    void visit(AstCond* const nodep) override {
        iterateChildren(nodep);
        if (nodep->condp()->dtypep()->isFourstate()) {
            wrapExprpInCFuncHard(nodep->condp(), VCFunc::FOUR_STATE_IS_TRUE);
        }
    }
    void visit(AstLoopTest* const nodep) override {
        iterateAndNextNull(nodep->condp());
        if (nodep->condp()->dtypep()->isFourstate()) {
            wrapExprpInCFuncHard(nodep->condp(), VCFunc::FOUR_STATE_IS_TRUE);
        }
    }
    void visit(AstWait* const nodep) override {
        iterateChildren(nodep);
        if (nodep->condp()->dtypep()->isFourstate()) {
            wrapExprpInCFuncHard(nodep->condp(), VCFunc::FOUR_STATE_IS_TRUE);
        }
    }
    void visit(AstDelay* const nodep) override {
        iterateChildren(nodep);
        if (AstConst* const constp = VN_CAST(nodep->lhsp(), Const)) {
            if (!constp->num().isAnyXZ()) constp->dtypeSetUInt64();
        }
        if (nodep->lhsp()->dtypep()->isFourstate()) {
            const AstNodeDType* const dtypep = nodep->lhsp()->dtypep();
            wrapExprpInCFuncHard(nodep->lhsp(), VCFunc::FOUR_STATE_TWO_STATE_VALUE)
                ->dtypeSetBitSized(dtypep->width(), dtypep->numeric());
        }
    }

    void visit(AstNodeAssign* const nodep) override {
        if (nodep->user1SetOnce()) return;
        iterateChildren(nodep);
        expectNState(nodep->rhsp(), nodep->lhsp()->dtypep()->isFourstate());
    }

    void visit(AstNodeBiop* const nodep) override {
        if (nodep->user1SetOnce()) return;
        iterateChildren(nodep);
        expectNState(nodep->lhsp(), nodep->dtypep()->isFourstate());
        expectNState(nodep->rhsp(), nodep->dtypep()->isFourstate());
    }
    void visit(AstCFuncHard* const nodep) override {
        if (nodep->user1SetOnce()) return;
        iterateChildren(nodep);
        switch (nodep->cfunc()) {
        case VCFunc::FOUR_STATE_TRIOR_CONFLICT:
        case VCFunc::FOUR_STATE_TRIOR_OR:
        case VCFunc::FOUR_STATE_TRIAND_AND:
        case VCFunc::FOUR_STATE_HAS_XZ:
        case VCFunc::FOUR_STATE_TWO_STATE_VALUE:
        case VCFunc::FOUR_STATE_TWO_STATE_VALUE_RAW:
        case VCFunc::FOUR_STATE_TWO_STATE_XZ_RAW:
        case VCFunc::FOUR_STATE_IS_TRUE:
        case VCFunc::FOUR_STATE_EXPANDER:
            for (AstNodeExpr* exprp = nodep->pinsp(); exprp;
                 exprp = VN_AS(exprp->nextp(), NodeExpr)) {
                expectNState(exprp, true);
            }
            break;
        case VCFunc::FOUR_STATE_MASK: {
            AstNodeExpr* const pinp = nodep->pinsp();
            UASSERT_OBJ(pinp && pinp->nextp() && !pinp->nextp()->nextp(), nodep,
                        "FOUR_STATE_MASK shall have exactly two arguments");
            expectNState(pinp, true);
            expectNState(VN_AS(pinp->nextp(), NodeExpr), false);
            break;
        }
        default: break;
        }
    }
    void visit(AstConst* const nodep) override {
        if (nodep->user1SetOnce()) return;
        if (nodep->dtypep()->isFourstate() && !nodep->num().isAnyXZ()) {
            castTwoToFour(nodep);
        } else if (!nodep->dtypep()->isFourstate() && nodep->num().isAnyXZ()) {
            nodep->dtypeSetLogicSized(nodep->width(), nodep->dtypep()->numeric());
        }
    }
    void visit(AstTime* const nodep) override {
        if (nodep->user1SetOnce()) return;
        castTwoToFour(nodep);
    }
    void visit(AstNodeExpr* const nodep) override {
        if (nodep->user1SetOnce()) return;
        iterateChildren(nodep);
    }
    void visit(AstNode* const nodep) override { iterateChildren(nodep); }

public:
    // CONSTRUCTORS
    explicit CastQuadstateVisitor(AstNetlist* const nodep) { iterate(nodep); }
    ~CastQuadstateVisitor() override = default;
};

class CastVisitor final : public VNVisitor {
    // NODE STATE
    // Entire netlist:
    //   AstNode::user1()               // bool.  Indicates node is of known size
    const VNUser1InUse m_inuser1;

    // STATE

    // METHODS
    void insertCast(AstNodeExpr* nodep, int needsize) {  // We'll insert ABOVE passed node
        VNRelinker relinkHandle;
        nodep->unlinkFrBack(&relinkHandle);
        //
        AstCCast* const castp = new AstCCast{nodep->fileline(), nodep, needsize,
                                             std::min(needsize, nodep->widthMin())};
        UINFO(4, "  MadeCast " << static_cast<void*>(castp) << " for " << nodep);
        relinkHandle.relink(castp);
        // UINFOTREE(9, castp, "", "castins");
        //
        ensureLower32Cast(castp);
        nodep->user1(1);  // Now must be of known size
    }
    static int castSize(const AstNode* nodep) {
        if (nodep->isQuad()) {
            return VL_QUADSIZE;
        } else if (nodep->width() <= 8) {
            return 8;
        } else if (nodep->width() <= 16) {
            return 16;
        } else {
            return VL_IDATASIZE;
        }
    }
    void ensureCast(AstNodeExpr* nodep) {
        if (castSize(nodep->backp()) != castSize(nodep) || !nodep->user1()) {
            if (!nodep->isNull()) insertCast(nodep, castSize(nodep->backp()));
        }
    }
    // cppcheck-suppress constParameterPointer // lhsp might be changed
    void ensureLower32Cast(AstCCast* nodep) {
        // If we have uint64 = CAST(uint64(x)) then the upcasting
        // really needs to be CAST(uint64(CAST(uint32(x))).
        // Otherwise a (uint64)(a>b) would return wrong value, as
        // less than has nondeterministic signedness.
        if (nodep->isQuad() && !nodep->lhsp()->isQuad() && !VN_IS(nodep->lhsp(), CCast)) {
            insertCast(nodep->lhsp(), VL_IDATASIZE);
        }
    }
    void ensureNullChecked(AstNodeExpr* nodep) {
        // TODO optimize to track null checked values and avoid where possible
        if (!VN_IS(nodep->backp(), NullCheck)) {
            VNRelinker relinkHandle;
            nodep->unlinkFrBack(&relinkHandle);
            relinkHandle.relink(new AstNullCheck{nodep->fileline(), nodep});
        }
    }

    // VISITORS
    void visit(AstNodeUniop* nodep) override {
        iterateChildren(nodep);
        nodep->user1(nodep->lhsp()->user1());
        if (nodep->sizeMattersLhs()) ensureCast(nodep->lhsp());
    }
    void visit(AstNodeBiop* nodep) override {
        iterateChildren(nodep);
        nodep->user1(nodep->lhsp()->user1() | nodep->rhsp()->user1());
        if (nodep->sizeMattersLhs()) ensureCast(nodep->lhsp());
        if (nodep->sizeMattersRhs()) ensureCast(nodep->rhsp());
    }
    void visit(AstCond* nodep) override {
        // All class types are castable to each other. If they are of different types,
        // a compilation error will be thrown, so an explicit cast is required. Types were
        // already checked by V3Width and dtypep of a condition operator is a type of their
        // common base class, so both classes can be safely casted.
        const AstClassRefDType* const thenClassDtypep
            = VN_CAST(nodep->thenp()->dtypep()->skipRefp(), ClassRefDType);
        const AstClassRefDType* const elseClassDtypep
            = VN_CAST(nodep->elsep()->dtypep()->skipRefp(), ClassRefDType);
        const bool castRequired = thenClassDtypep && elseClassDtypep
                                  && (thenClassDtypep->classp() != elseClassDtypep->classp());
        if (castRequired) {
            const AstClass* const commonBaseClassp
                = VN_AS(nodep->dtypep()->skipRefp(), ClassRefDType)->classp();
            if (thenClassDtypep->classp() != commonBaseClassp) {
                AstNodeExpr* thenp = nodep->thenp()->unlinkFrBack();
                nodep->thenp(new AstCCast{thenp->fileline(), thenp, nodep});
            }
            if (elseClassDtypep->classp() != commonBaseClassp) {
                AstNodeExpr* elsep = nodep->elsep()->unlinkFrBack();
                nodep->elsep(new AstCCast{elsep->fileline(), elsep, nodep});
            }
        }
        visit(static_cast<AstNodeTriop*>(nodep));
    }
    void visit(AstNodeTriop* nodep) override {
        iterateChildren(nodep);
        nodep->user1(nodep->lhsp()->user1() | nodep->rhsp()->user1() | nodep->thsp()->user1());
        if (nodep->sizeMattersLhs()) ensureCast(nodep->lhsp());
        if (nodep->sizeMattersRhs()) ensureCast(nodep->rhsp());
        if (nodep->sizeMattersThs()) ensureCast(nodep->thsp());
    }
    void visit(AstNodeQuadop* nodep) override {
        iterateChildren(nodep);
        nodep->user1(nodep->lhsp()->user1() | nodep->rhsp()->user1() | nodep->thsp()->user1()
                     | nodep->fhsp()->user1());
        if (nodep->sizeMattersLhs()) ensureCast(nodep->lhsp());
        if (nodep->sizeMattersRhs()) ensureCast(nodep->rhsp());
        if (nodep->sizeMattersThs()) ensureCast(nodep->thsp());
        if (nodep->sizeMattersFhs()) ensureCast(nodep->fhsp());
    }
    void visit(AstCCast* nodep) override {
        iterateChildren(nodep);
        ensureLower32Cast(nodep);
        nodep->user1(1);
    }
    void visit(AstConsPackMember* nodep) override {
        iterateChildren(nodep);
        if (VN_IS(nodep->rhsp()->dtypep()->skipRefp(), BasicDType)) ensureCast(nodep->rhsp());
        nodep->user1(1);
    }
    void visit(AstExprStmt* nodep) override {
        iterateChildren(nodep);
        nodep->user1(1);
    }
    void visit(AstNegate* nodep) override {
        iterateChildren(nodep);
        nodep->user1(nodep->lhsp()->user1());
        if (nodep->lhsp()->widthMin() == 1 && !nodep->lhsp()->isWide()) {
            // We want to avoid a GCC "converting of negative value" warning
            // from our expansion of
            //    out = {32{a<b}}  =>   out = - (a<b)
            insertCast(nodep->lhsp(), castSize(nodep));
        } else {
            if (nodep->sizeMattersLhs()) ensureCast(nodep->lhsp());
        }
    }
    void visit(AstVarRef* nodep) override {
        const AstNode* const backp = nodep->backp();
        if (nodep->access().isReadOnly() && VN_IS(backp, NodeExpr) && !VN_IS(backp, CCast)
            && !VN_IS(backp, NodeCCall) && !VN_IS(backp, CMethodHard) && !VN_IS(backp, SFormatF)
            && !VN_IS(backp, ArraySel) && !VN_IS(backp, StructSel) && !VN_IS(backp, RedXor)
            && (nodep->varp()->basicp() && !nodep->varp()->basicp()->isForkSync()
                && !nodep->varp()->basicp()->isProcessRef() && !nodep->varp()->basicp()->isEvent())
            && backp->width() && castSize(nodep) != castSize(nodep->varp())) {
            // Cast vars to IData first, else below has upper bits wrongly set
            //  CData x=3; out = (QData)(x<<30);
            insertCast(nodep, castSize(nodep));
        }
        nodep->user1(1);
    }
    void visit(AstConst* nodep) override {
        // Constants are of unknown size if smaller than 33 bits, because
        // we're too lazy to wrap every constant in the universe in
        // ((IData)#).
        nodep->user1(nodep->isQuad() || nodep->isWide() || nodep->isNull());
    }

    // Null dereference protection
    void visit(AstNullCheck* nodep) override {
        iterateChildren(nodep);
        nodep->user1(nodep->lhsp()->user1());
    }
    void visit(AstCMethodCall* nodep) override {
        iterateChildren(nodep);
        ensureNullChecked(nodep->fromp());
        nodep->user1(true);
    }
    void visit(AstCMethodHard* nodep) override {
        iterateChildren(nodep);
        nodep->user1(true);
    }
    void visit(AstMemberSel* nodep) override {
        iterateChildren(nodep);
        ensureNullChecked(nodep->fromp());
        nodep->user1(true);
    }
    void visit(AstStructSel* nodep) override {
        iterateChildren(nodep);
        nodep->user1(true);
    }

    // NOPs
    void visit(AstVar*) override {}

    //--------------------
    void visit(AstNode* nodep) override { iterateChildren(nodep); }

public:
    // CONSTRUCTORS
    explicit CastVisitor(AstNetlist* nodep) { iterate(nodep); }
    ~CastVisitor() override = default;
};

//######################################################################
// Cast class functions

void V3Cast::castAll(AstNetlist* nodep) {
    UINFO(2, __FUNCTION__ << ":");
    if (v3Global.opt.fourstate()) { CastQuadstateVisitor{nodep}; }  // Destruct before checking
    { CastVisitor{nodep}; }  // Destruct before checking
    V3Global::dumpCheckGlobalTree("cast", 0, dumpTreeEitherLevel() >= 3);
}
