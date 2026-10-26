// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Lower increments, decrements and compound assignments
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2003-2026 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************
// V3LinkInc's Transformations:
//
//      lowerIncDec
//        ++/-- used as a value in an expression is replaced in place by an
//        expression statement, so it is evaluated only where and when its
//        expression is, e.g. not when short-circuited by && or ||.
//        A temporary __VincrementN holds the result, as the variable may
//        change again before the result is used, e.g. 'a[++i][--i]'.
//        PREINC/PREDEC
//          '++x' becomes '(x += 1; __Vincrement1 = x; __Vincrement1)'
//        POSTINC/POSTDEC
//          'x++' becomes '(__Vincrement1 = x; x += 1; __Vincrement1)'
//        The temporary is declared in the enclosing function/task, generate
//        block or module, so it is cloned with it.
//
//      lowerCompound
//        A compound assignment 'x op= e' becomes 'x = x op e'.
//
//      hoistIndices
//        Impure index expressions in the lvalue of a compound assignment or ++/--
//        are evaluated once, in order, into temporaries __VtempIndexN:
//          '__VtempIndex1 = something_with_side_eff;
//           array[__VtempIndex1] = array[__VtempIndex1] + e'
//
//*************************************************************************

#include "V3PchAstNoMT.h"  // VL_MT_DISABLED_CODE_UNIT

#include "V3LinkInc.h"

#include "V3LinkLValue.h"

VL_DEFINE_DEBUG_FUNCTIONS;

//######################################################################

class LinkIncVisitor final : public VNVisitor {
    // STATE
    AstNodeModule* m_modp = nullptr;  // Module we're inside
    AstNode* m_containerp = nullptr;  // Module, generate block or function/task to add vars to
    int m_tmpNum = 0;  // Temporary variable name counter
    const char* m_illegalReasonp = nullptr;  // Where ++/-- is illegal, if under such
    bool m_staticTemps = false;  // Temporaries must be static

    // METHODS
    // Return a new temporary of the type of 'typeExprp', declared in the current container
    AstVar* newTempVarp(FileLine* flp, const char* prefixp, AstNodeExpr* typeExprp) {
        const string name = prefixp + cvtToStr(++m_tmpNum);
        AstVar* const varp = new AstVar{
            flp, VVarType::BLOCKTEMP, name, VFlagChildDType{},
            new AstRefDType{flp, AstRefDType::FlagTypeOfExpr{}, typeExprp->cloneTree(true)}};
        // Declare at the top of the container. Must not unlink the statements,
        // as one of them is being iterated.
        if (AstNodeFTask* const ftaskp = VN_CAST(m_containerp, NodeFTask)) {
            varp->lifetime(m_staticTemps ? VLifetime::STATIC_EXPLICIT
                                         : VLifetime::AUTOMATIC_EXPLICIT);
            varp->funcLocal(true);
            ftaskp->prependStmtsp(varp);
        } else if (AstClass* const classp = VN_CAST(m_containerp, Class)) {
            varp->varType(VVarType::MEMBER);
            if (m_staticTemps) varp->lifetime(VLifetime::STATIC_EXPLICIT);
            classp->prependMembersp(varp);
        } else {
            varp->lifetime(VLifetime::STATIC_EXPLICIT);
            if (AstGenBlock* const genBlockp = VN_CAST(m_containerp, GenBlock)) {
                genBlockp->prependItemsp(varp);
            } else if (AstGenFor* const genForp = VN_CAST(m_containerp, GenFor)) {
                genForp->prependItemsp(varp);
            } else {
                VN_AS(m_containerp, NodeModule)->prependStmtsp(varp);
            }
        }
        return varp;
    }
    // '++'/'--' as '+= 1'/'-= 1'
    static AstAssignCompound* newIncAssignp(AstNodeUniop* nodep, AstNodeExpr* lhsp) {
        FileLine* const flp = nodep->fileline();
        AstConst* const onep = new AstConst{flp, AstConst::Unsized32{}, 1};
        return VN_IS(nodep, PreInc) || VN_IS(nodep, PostInc)
                   ? new AstAssignCompound{AstAssignCompound::Add, flp, lhsp, onep}
                   : new AstAssignCompound{AstAssignCompound::Sub, flp, lhsp, onep};
    }
    static AstNodeExpr* newOperationp(AstAssignCompound* nodep, AstNodeExpr* lhsp,
                                      AstNodeExpr* rhsp) {
        FileLine* const flp = nodep->fileline();
        switch (nodep->operation()) {
        case AstAssignCompound::operation::Add: return new AstAdd{flp, lhsp, rhsp};
        case AstAssignCompound::operation::And: return new AstAnd{flp, lhsp, rhsp};
        case AstAssignCompound::operation::Div: return new AstDiv{flp, lhsp, rhsp};
        case AstAssignCompound::operation::ModDiv: return new AstModDiv{flp, lhsp, rhsp};
        case AstAssignCompound::operation::Mul: return new AstMul{flp, lhsp, rhsp};
        case AstAssignCompound::operation::Or: return new AstOr{flp, lhsp, rhsp};
        case AstAssignCompound::operation::ShiftL: return new AstShiftL{flp, lhsp, rhsp};
        case AstAssignCompound::operation::ShiftR: return new AstShiftR{flp, lhsp, rhsp};
        case AstAssignCompound::operation::ShiftRS: return new AstShiftRS{flp, lhsp, rhsp};
        case AstAssignCompound::operation::Sub: return new AstSub{flp, lhsp, rhsp};
        case AstAssignCompound::operation::Xor: return new AstXor{flp, lhsp, rhsp};
        default:;  // Error below  // LCOV_EXCL_LINE
        }
        nodep->v3fatalSrc("Unhandled compound assignment operation");
    }
    AstAssign* hoistIndices(AstNodeExpr* nodep) {
        if (AstMemberSel* const selp = VN_CAST(nodep, MemberSel)) {
            return hoistIndices(selp->fromp());
        }
        if (AstReplicate* const repp = VN_CAST(nodep, Replicate)) {
            return hoistIndices(repp->srcp());
        }
        if (AstConcat* const catp = VN_CAST(nodep, Concat)) {
            return AstNode::addNextNull(hoistIndices(catp->lhsp()), hoistIndices(catp->rhsp()));
        }
        if (AstNodePreSel* const selp = VN_CAST(nodep, NodePreSel)) {
            AstAssign* stmtsp = hoistIndices(selp->fromp());
            for (AstNodeExpr* const exprp : {selp->rhsp(), selp->thsp()}) {
                if (!exprp || exprp->isPure()) continue;
                FileLine* const flp = exprp->fileline();
                AstVar* const varp = newTempVarp(flp, "__VtempIndex", exprp);
                exprp->replaceWith(new AstVarRef{flp, varp, VAccess::READ});
                stmtsp = AstNode::addNext(
                    stmtsp, new AstAssign{flp, new AstVarRef{flp, varp, VAccess::WRITE}, exprp});
            }
            return stmtsp;
        }
        return nullptr;
    }
    void lowerCompound(AstAssignCompound* nodep) {
        AstNodeExpr* const rhsp = nodep->rhsp()->unlinkFrBack();
        AstNodeExpr* const writep = nodep->lhsp()->cloneTreePure(true);
        AstNodeExpr* const readp = nodep->lhsp()->unlinkFrBack();
        V3LinkLValue::linkLValueSet(readp, VAccess::READ);
        AstAssign* const assignp
            = new AstAssign{nodep->fileline(), writep, newOperationp(nodep, readp, rhsp)};
        nodep->replaceWith(assignp);
        VL_DO_DANGLING(pushDeletep(nodep), nodep);
    }
    void lowerIncDec(AstNodeUniop* nodep) {
        iterateChildren(nodep);
        if (m_illegalReasonp) {
            nodep->v3error("Pre/post increment/decrement operator not allowed in "
                           << m_illegalReasonp);
            return;
        }
        AstNode* const hoistedp = hoistIndices(nodep->lhsp());
        AstNodeExpr* const readp = nodep->lhsp();
        AstNodeExpr* const writep = readp->cloneTreePure(true);
        V3LinkLValue::linkLValueSet(writep);
        V3LinkLValue::linkLValueSet(readp, VAccess::READ);

        FileLine* const flp = nodep->fileline();

        // Temporary holding the result
        AstVar* const varp = newTempVarp(flp, "__Vincrement", readp);

        // The increment, and saving the value into the temporary, after it for PreInc/PreDec,
        // before it for PostInc/PostDec
        AstAssignCompound* const incp = newIncAssignp(nodep, writep);
        AstAssign* const savep
            = new AstAssign{flp, new AstVarRef{flp, varp, VAccess::WRITE}, readp->unlinkFrBack()};
        AstNode* stmtsp;
        if (VN_IS(nodep, PreInc) || VN_IS(nodep, PreDec)) {
            stmtsp = incp;
            stmtsp->addNext(savep);
        } else {
            stmtsp = savep;
            stmtsp->addNext(incp);
        }

        // Replace the node with the temporary, after the statements
        stmtsp = AstNode::addNextNull(hoistedp, stmtsp);
        nodep->replaceWith(new AstExprStmt{flp, stmtsp, new AstVarRef{flp, varp, VAccess::READ}});
        VL_DO_DANGLING(pushDeletep(nodep), nodep);
        lowerCompound(incp);
    }

    // VISITORS -- containers
    void visit(AstNodeModule* nodep) override {
        if (nodep->dead()) return;
        VL_RESTORER(m_modp);
        VL_RESTORER(m_containerp);
        VL_RESTORER(m_tmpNum);
        m_modp = nodep;
        m_containerp = nodep;
        m_tmpNum = 0;
        iterateChildren(nodep);
    }
    void visit(AstNodeFTask* nodep) override {
        {
            // Default argument values are evaluated in the scope containing the declaration
            // (IEEE 1800-2023 13.5.3), not in the function, and at a call site maybe without
            // 'this', so use static temporaries there
            VL_RESTORER(m_staticTemps);
            m_staticTemps = true;
            for (AstNode* const stmtp : nodep->stmtspList()) {
                AstVar* const varp = VN_CAST(stmtp, Var);
                if (varp && varp->isIO()) iterateAndNextNull(varp->valuep());
            }
        }
        VL_RESTORER(m_containerp);
        m_containerp = nodep;
        iterateChildren(nodep);
    }
    // V3Covergroup moves a covergroup's expressions to its constructor
    // or sample(), so their variables are members of its class
    void visit(AstNodeFuncCovItem* nodep) override {
        VL_RESTORER(m_containerp);
        m_containerp = m_modp;
        iterateChildren(nodep);
    }
    void visit(AstCgOptionAssign* nodep) override {
        VL_RESTORER(m_containerp);
        m_containerp = m_modp;
        iterateChildren(nodep);
    }
    void visit(AstGenBlock* nodep) override {
        VL_RESTORER(m_containerp);
        m_containerp = nodep;
        iterateChildren(nodep);
    }
    void visit(AstGenFor* nodep) override {
        VL_RESTORER(m_containerp);
        m_containerp = nodep;
        iterateChildren(nodep);
    }
    // Temporaries of static variable initializers must be static
    void visit(AstInitialStatic* nodep) override {
        VL_RESTORER(m_staticTemps);
        m_staticTemps = true;
        iterateChildren(nodep);
    }
    void visit(AstInitialStaticStmt* nodep) override {
        VL_RESTORER(m_staticTemps);
        m_staticTemps = true;
        iterateChildren(nodep);
    }
    // VISITORS -- illegal
    void visit(AstSenTree* nodep) override {
        VL_RESTORER(m_illegalReasonp);
        m_illegalReasonp = "an event expression (IEEE 1800-2023 11.3.6)";
        iterateChildren(nodep);
    }
    void visit(AstPropSpec* nodep) override {
        VL_RESTORER(m_illegalReasonp);
        m_illegalReasonp = "a property (IEEE 1800-2023 16.6)";
        iterateChildren(nodep);
    }
    void visit(AstSequence* nodep) override {
        VL_RESTORER(m_illegalReasonp);
        m_illegalReasonp = "a sequence (IEEE 1800-2023 16.6)";
        iterateChildren(nodep);
    }
    void visit(AstConstraintExpr* nodep) override {
        VL_RESTORER(m_illegalReasonp);
        m_illegalReasonp = "a constraint (IEEE 1800-2023 18.5)";
        iterateChildren(nodep);
    }
    void visit(AstConstraintIf* nodep) override {
        VL_RESTORER(m_illegalReasonp);
        m_illegalReasonp = "a constraint (IEEE 1800-2023 18.5)";
        iterateChildren(nodep);
    }
    // VISITORS -- lowering
    void visit(AstStmtExpr* nodep) override {
        AstNodeExpr* const exprp = nodep->exprp();
        if (!VN_IS(exprp, PostInc) && !VN_IS(exprp, PostDec) && !VN_IS(exprp, PreInc)
            && !VN_IS(exprp, PreDec)) {
            iterateChildren(nodep);
            return;
        }
        // A standalone ++/-- is the same as += 1 or -= 1
        AstNodeUniop* const unip = VN_AS(exprp, NodeUniop);
        AstAssignCompound* const newp = newIncAssignp(unip, unip->lhsp()->unlinkFrBack());
        nodep->replaceWith(newp);
        VL_DO_DANGLING(pushDeletep(nodep), nodep);
        visit(newp);
    }
    void visit(AstPreInc* nodep) override { lowerIncDec(nodep); }
    void visit(AstPostInc* nodep) override { lowerIncDec(nodep); }
    void visit(AstPreDec* nodep) override { lowerIncDec(nodep); }
    void visit(AstPostDec* nodep) override { lowerIncDec(nodep); }
    void visit(AstAssignCompound* nodep) override {
        iterateChildren(nodep);
        if (AstAssign* const stmtsp = hoistIndices(nodep->lhsp())) {
            nodep->addHereThisAsNext(stmtsp);
        }
        lowerCompound(nodep);
    }
    // VISITORS -- recursion
    void visit(AstNode* nodep) override { iterateChildren(nodep); }

public:
    // CONSTRUCTORS
    explicit LinkIncVisitor(AstNetlist* nodep) { iterate(nodep); }
    ~LinkIncVisitor() override = default;
};

//######################################################################
// Task class functions

void V3LinkInc::linkIncrements(AstNetlist* nodep) {
    UINFO(2, __FUNCTION__ << ":");
    { LinkIncVisitor{nodep}; }  // Destruct before checking
    V3Global::dumpCheckGlobalTree("linkinc", 0, dumpTreeEitherLevel() >= 3);
}
