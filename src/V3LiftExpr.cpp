// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Lift expressions out of statements
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
//
// V3LiftExpr's Transformations:
//
// Lift impure sub-expressions and function calls out of expressions,
// turning them into additional statements. This has several benefits
// that enable further downstream optimizations:
// - Impure expressions always appear on the RHS of a simple assignment,
//   reducing the size of impure expressions. This also eliminates
//   later needs for cloning impure expressions, preserving side effects
// - Lifted function calls can be inlined without the use of AstExprStmt,
//   which is poorly handled by optimizations, especially Dfg
// - Reduces complexity of downstream lowering passes as they need to deal
//   with fewer special cases.
//
// The generic transformation applies for all AstNodeStmt. Using AstAssign
// as an example:
//    x[impure_x] = impure_y + func(impure_z);
// is transformed into:
//    __VleImpure_0 = impure_y;
//    __VleImpure_1 = impure_z;
//    __VleCall_0 = func(__VleImpure_1);
//    __VleImpure_2 = impure_x;
//    x[__VleImpure_2] = __VleImpure_0 + __VleCall_0;
// All parts of the assignment is now pure, and the function call can be
// inlined by V3Task without the use of AstExprStmt.
//
// Care must be taken for the 4 short-circuiting operators: && || -> ?:
// For example AstLogAnd:
//    z = x && func(y)
// is transformed into:
//    __VleLogAnd_0 = x;
//    if (__VleLogAnd_0) {
//      __VleCall_0 = func(y);
//      __VleLogAnd_0 = __VleCall_0;
//    }
//    z = __VleLogAnd_1;
// Similar patterns are used for AstLogOr and AstCond to preserve the
// short-circuiting semantics and side effects. All AstLogIf should have
// been converted to AstLogOr earlier by V3Const.
//
// Care must be taken for impure LValues as well. While, all LValue expressions
// permitted by IEEE-1800 are themselves pure (except possibly for the non-lvalue
// sub-expressions like array indices, which are not a problem), we support a
// non-standard but common extension where a function call returning a class
// handle, under a member select can be an LValue, e.g.:
//    'getInstance().member = foo;'
// Fortunately we can discover these via MemberSel, and we can transform them
// to the IEEE-1800 compliant form:
//    __VleLvalCall_0 = getInstance();
//    __VleLvalCall_0.member = foo;
// There are also some other internal LValues represented via CMethodHard that
// return references, and are marked as impure. For this reason only we still
// need to special case their handling via AstNodeExpr::isLValue().
//
//*************************************************************************

#include "V3PchAstNoMT.h"  // VL_MT_DISABLED_CODE_UNIT

#include "verilatedos.h"

#include "V3LiftExpr.h"

#include "V3Ast.h"
#include "V3Error.h"
#include "V3FileLine.h"
#include "V3Inst.h"
#include "V3Stats.h"

VL_DEFINE_DEBUG_FUNCTIONS;

//######################################################################

class LiftExprVisitor final : public VNVisitor {
    // NODE STATE
    // AstNodeStmt::user1()  -> bool. Statement already processed
    // AstVar::user1()       -> bool. Variable is a lifted temporary
    // AstNodeExpr::user1p() -> AstVar*. Existing temporary variable usable for this expression
    const VNUser1InUse m_user1InUse;

    // STATE
    AstNodeModule* m_modp = nullptr;  // Current module
    AstNodeFTask* m_ftaskp = nullptr;  // Current function/task
    bool m_lift = false;  // Lift encountered expressions
    // Statements lifted out of current node. TODO: Make this an AstNodeStmt* after #6280
    AstNode* m_newStmtps = nullptr;
    // Expressions in some special locations need not, or should not be lifted
    AstNodeExpr* m_doNotLiftp = nullptr;
    size_t m_nTmps = 0;  // Sequence numbers for temporary variables
    // Statistics
    VDouble0 m_statLiftedExprs;
    VDouble0 m_statLiftedCalls;
    VDouble0 m_statLiftedLvalCalls;
    VDouble0 m_statLiftedConds;
    VDouble0 m_statLiftedLogAnds;
    VDouble0 m_statLiftedLogOrs;
    VDouble0 m_statLiftedExprStmts;
    VDouble0 m_statTemporariesCreated;
    VDouble0 m_statTemporariesReused;

    // METHODS
    AstVar* newVar(const char* baseName, const AstNodeExpr* exprp,
                   const std::string& suffix = "") {
        // Reuse existing temporary if available
        if (exprp->user1p()) {
            ++m_statTemporariesReused;
            return VN_AS(exprp->user1p(), Var);
        }

        // Need a separate name in functions vs modules, as module inlining
        // can otherwise cause spurious VARHIDDEN warnings
        std::string name = m_ftaskp ? "__Vlef" : "__Vlem";
        name += baseName;
        name += "_" + std::to_string(m_nTmps++);
        if (!suffix.empty()) name += "__" + suffix;

        // Create variable
        ++m_statTemporariesCreated;
        AstVar* const varp = new AstVar{exprp->fileline(), VVarType::MODULETEMP, name,
                                        exprp->dtypep()->skipRefp()};
        varp->isInternal(true);
        varp->noReset(true);
        varp->user1(1);  // Mark as lifted temporary so it can be reused

        if (m_ftaskp) {
            varp->funcLocal(true);
            m_ftaskp->stmtsp()->addHereThisAsNext(varp);
            varp->lifetime(VLifetime::AUTOMATIC_EXPLICIT);
        } else {
            m_modp->stmtsp()->addHereThisAsNext(varp);
            // 'automatic' on a variable inside a class actually means 'member'
            varp->lifetime(VN_IS(m_modp, Class) ? VLifetime::STATIC_EXPLICIT
                                                : VLifetime::AUTOMATIC_EXPLICIT);
        }
        return varp;
    }

    // If the expression is a reference to an existing temporary, return it, otherwise nullptr
    AstVar* getExistingVar(AstNodeExpr* nodep) {
        if (AstVarRef* const refp = VN_CAST(nodep, VarRef)) {
            if (refp->varp()->user1()) return refp->varp();
        }
        return nullptr;
    }

    // Unlink and assign given expression to temporary, unless the expression
    // is a reference to the same temporary
    AstAssign* assignIfDifferent(FileLine* flp, AstVar* varp, AstNodeExpr* nodep) {
        if (AstVarRef* const refp = VN_CAST(nodep, VarRef)) {
            if (refp->varp() == varp) return nullptr;
        }
        return new AstAssign{flp, new AstVarRef{flp, varp, VAccess::WRITE}, nodep->unlinkFrBack()};
    }

    void addStmtps(AstNode* stmtp) {
        if (!stmtp) return;
        // No need to process again, so mark
        for (AstNode* nodep = stmtp; nodep; nodep = nodep->nextp()) nodep->user1(1);
        m_newStmtps = AstNode::addNext(m_newStmtps, stmtp);
    }

    // Lift expressions from expression, return lifted statements
    AstNode* lift(AstNodeExpr* nodep) {
        if (!nodep) return nullptr;
        VL_RESTORER(m_lift);
        VL_RESTORER(m_newStmtps);
        m_lift = true;
        m_newStmtps = nullptr;
        iterate(nodep);
        return m_newStmtps;
    }

    // Lift expressions from children of given statement, return lifted statements
    AstNode* liftChildren(AstNodeStmt* nodep) {
        VL_RESTORER(m_lift);
        VL_RESTORER(m_newStmtps);
        m_lift = true;
        m_newStmtps = nullptr;
        iterateChildren(nodep);
        return m_newStmtps;
    }

    // VISITORS - non-statement, non-expression
    void visit(AstNode* nodep) override {
        VL_RESTORER(m_lift);
        m_lift = false;  // Conservatively do not lift if unknown construct
        iterateChildren(nodep);
    }
    void visit(AstNodeModule* nodep) override {
        // Reset names on root module only (there can be classes nested in modules)
        if (!m_modp) m_nTmps = 0;
        VL_RESTORER(m_modp);
        m_modp = nodep;
        iterateChildren(nodep);
    }
    void visit(AstNodeFTask* nodep) override {
        VL_RESTORER(m_ftaskp);
        VL_RESTORER(m_nTmps);
        m_ftaskp = nodep;
        m_nTmps = 0;
        iterateChildren(nodep);
    }
    void visit(AstCaseItem* nodep) override {
        // Do not lift from the case expressions, there is nowhere to put them
        iterateAndNextNull(nodep->stmtsp());
    }
    void visit(AstCell* nodep) override {
        // No need to fix up port connections, V3Tristate called pinReconnectSimple,
        // so all writes are to simple AstVars, assuming it did it right ...
    }
    void visit(AstAlias* nodep) override {}
    void visit(AstArg* nodep) override {
        // Lift argument expressions
        iterateChildren(nodep);
    }

    // VISITORS - statements
    void visit(AstNodeStmt* nodep) override {
        if (nodep->user1SetOnce()) return;
        VL_RESTORER(m_doNotLiftp);
        m_doNotLiftp = nullptr;
        if (AstNode* const newStmtps = liftChildren(nodep)) nodep->addHereThisAsNext(newStmtps);
    }
    void visit(AstNodeAssign* nodep) override {
        if (nodep->user1SetOnce()) return;
        VL_RESTORER(m_doNotLiftp);
        // Do not lift the RHS if this is already a simple assignment to a variable
        m_doNotLiftp = VN_IS(nodep->lhsp(), NodeVarRef) ? nodep->rhsp() : nullptr;
        if (AstNode* const newStmtps = lift(nodep->rhsp())) {
            nodep->addHereThisAsNext(newStmtps);
        }

        if (nodep->timingControlp()) return;

        if (AstNode* const newStmtps = lift(nodep->lhsp())) {
            nodep->addHereThisAsNext(newStmtps);
        }
    }
    void visit(AstStmtExpr* nodep) override {
        if (nodep->user1SetOnce()) return;
        // Ignore super class constructor calls - can't insert statements before them
        if (VN_IS(nodep->exprp(), New)) return;
        VL_RESTORER(m_doNotLiftp);
        // Do not lift if the expression itself. This AstStmtExpr is required to
        // throw away the return value if any, and V3Task can inline without using
        // AstExprStmt in this case. Can still lift all sub-expressions though.
        m_doNotLiftp = nodep->exprp();
        if (AstNode* const newStmtps = liftChildren(nodep)) nodep->addHereThisAsNext(newStmtps);
    }
    // Don't know whether these are sensitive to lifting, assume so
    void visit(AstCStmt* nodep) override {}
    void visit(AstCStmtUser* nodep) override {}

    // VISITORS - expressions
    void visit(AstNodeExpr* nodep) override {
        if (!m_lift) return;

        iterateChildren(nodep);

        // Do not lift if already in normal form
        if (m_doNotLiftp == nodep) return;
        // No need to lift void expressions, these should be under StmtExpr, but just in case ...
        if (VN_IS(nodep->dtypep()->skipRefp(), VoidDType)) return;
        // Do not lift if pure
        if (nodep->isPure()) return;
        // Do not lift if LValue
        if (nodep->isLValue()) return;

        // Extract expression into a temporary variable
        ++m_statLiftedExprs;
        FileLine* const flp = nodep->fileline();
        AstVar* const varp = newVar("Expr", nodep);
        nodep->replaceWith(new AstVarRef{flp, varp, VAccess::READ});
        addStmtps(new AstAssign{flp, new AstVarRef{flp, varp, VAccess::WRITE}, nodep});
    }
    void visit(AstNodeFTaskRef* nodep) override {
        if (!m_lift) return;

        iterateChildren(nodep);

        // Do not lift if already in normal form
        if (m_doNotLiftp == nodep) return;
        // No need to lift void functions, these should be under StmtExpr, but just in case ...
        if (VN_IS(nodep->dtypep()->skipRefp(), VoidDType)) return;
        // Do not lift Taskref, it's always in statement position and cleanly inlineable.
        if (VN_IS(nodep, TaskRef)) return;

        // Extract expression into a temporary variable
        ++m_statLiftedCalls;
        FileLine* const flp = nodep->fileline();
        AstVar* const varp = newVar("Call", nodep, nodep->taskp()->name());
        nodep->replaceWith(new AstVarRef{flp, varp, VAccess::READ});
        addStmtps(new AstAssign{flp, new AstVarRef{flp, varp, VAccess::WRITE}, nodep});
    }
    void visit(AstMemberSel* nodep) override {
        if (!m_lift) return;
        // MemberSel is special as it can appear as an LValue selecting from a call
        // that returns a class handle. Note this is not in IEEE-1800, but is supported
        // for compatibility. Here we turn it into an IEEE-1800 compliant LValue by
        // lifting the call and use the return value via a temporary variable.

        VL_RESTORER(m_doNotLiftp);
        // If it's an LValue call, do not lift the fromp, will do it explicitly below
        m_doNotLiftp = nodep->access().isWriteOrRW() && VN_IS(nodep->fromp(), NodeFTaskRef)
                           ? nodep->fromp()
                           : nullptr;
        iterateChildren(nodep);
        // Done if not a special case
        if (!m_doNotLiftp) return;

        // Extract LValue call into a temporary variable
        ++m_statLiftedLvalCalls;
        FileLine* const flp = nodep->fileline();
        AstVar* const varp = newVar("LvalCall", nodep->fromp());
        addStmtps(new AstAssign{flp, new AstVarRef{flp, varp, VAccess::WRITE},
                                nodep->fromp()->unlinkFrBack()});
        // This one is a WRITE or READWRITE, same as the MemberSel
        nodep->fromp(new AstVarRef{flp, varp, nodep->access()});
    }

    // VISITORS - RValue expressions
    void visit(AstCond* nodep) override {
        if (!m_lift) return;

        // Lift from condition
        iterate(nodep->condp());

        // Temporary variable to use for this expression
        AstVar* varp = nullptr;

        const bool sameType
            = nodep->thenp()->dtypep()->skipRefp()->sameTree(nodep->elsep()->dtypep()->skipRefp());

        // Lift from the Then branch
        AstNode* const thenStmtps = lift(nodep->thenp());
        // If lifted the Then branch, we can reuse the temporary if same type
        if (sameType) varp = getExistingVar(nodep->thenp());
        if (varp) nodep->elsep()->user1p(varp);

        // Lift from the Else branch
        AstNode* const elseStmtps = lift(nodep->elsep());
        // If lifted the Else branch, we can reuse the temporary if same type
        if (sameType && !varp) varp = getExistingVar(nodep->elsep());

        // If nothing lifted, then nothing to do
        if (!thenStmtps && !elseStmtps) return;

        // Otherwise convert to an AstIf with a temporary variable
        ++m_statLiftedConds;
        FileLine* const flp = nodep->fileline();
        if (!varp) varp = newVar("Cond", nodep);
        // Create the AstIf
        AstIf* const ifp = new AstIf{flp, nodep->condp()->unlinkFrBack()};
        addStmtps(ifp);
        ifp->addThensp(thenStmtps);
        ifp->addThensp(assignIfDifferent(flp, varp, nodep->thenp()));
        ifp->addElsesp(elseStmtps);
        ifp->addElsesp(assignIfDifferent(flp, varp, nodep->elsep()));
        // Replace the expression with a reference to the temporary variable
        nodep->replaceWith(new AstVarRef{flp, varp, VAccess::READ});
        VL_DO_DANGLING(nodep->deleteTree(), nodep);
    }
    void visit(AstLogAnd* nodep) override {
        if (!m_lift) return;

        // Lift from LHS
        iterate(nodep->lhsp());

        // Temporary variable to use for this expression
        AstVar* varp = getExistingVar(nodep->lhsp());
        // If lifted the LHS, we can reuse the temporary
        if (varp) nodep->rhsp()->user1p(varp);

        // Lift from RHS, if nothing lifted, then nothing to do
        AstNode* const rhsStmtps = lift(nodep->rhsp());
        if (!rhsStmtps) return;

        // Otherwise convert to an AstIf with a temporary variable
        ++m_statLiftedLogAnds;
        FileLine* const flp = nodep->fileline();
        if (!varp) varp = getExistingVar(nodep->rhsp());
        if (!varp) varp = newVar("LogAnd", nodep);
        addStmtps(assignIfDifferent(flp, varp, nodep->lhsp()));
        AstIf* const ifp = new AstIf{flp, new AstVarRef{flp, varp, VAccess::READ}};
        addStmtps(ifp);
        ifp->addThensp(rhsStmtps);
        ifp->addThensp(assignIfDifferent(flp, varp, nodep->rhsp()));
        nodep->replaceWith(new AstVarRef{flp, varp, VAccess::READ});
        VL_DO_DANGLING(nodep->deleteTree(), nodep);
    }
    void visit(AstLogOr* nodep) override {
        if (!m_lift) return;

        // Lift from LHS
        iterate(nodep->lhsp());

        // Temporary variable to use for this expression
        AstVar* varp = getExistingVar(nodep->lhsp());
        // If lifted the LHS, we can reuse the temporary
        if (varp) nodep->rhsp()->user1p(varp);

        // Lift from RHS, if nothing lifted, then nothing to do
        AstNode* const rhsStmtps = lift(nodep->rhsp());
        if (!rhsStmtps) return;

        // Otherwise convert to an AstIf with a temporary variable
        ++m_statLiftedLogOrs;
        FileLine* const flp = nodep->fileline();
        if (!varp) varp = getExistingVar(nodep->rhsp());
        if (!varp) varp = newVar("LogOr", nodep);
        addStmtps(assignIfDifferent(flp, varp, nodep->lhsp()));
        AstIf* const ifp = new AstIf{flp, new AstVarRef{flp, varp, VAccess::READ}};
        addStmtps(ifp);
        ifp->addElsesp(rhsStmtps);
        ifp->addElsesp(assignIfDifferent(flp, varp, nodep->rhsp()));
        nodep->replaceWith(new AstVarRef{flp, varp, VAccess::READ});
        VL_DO_DANGLING(nodep->deleteTree(), nodep);
    }
    void visit(AstLogIf* nodep) override {
        if (!m_lift) return;
        nodep->v3fatalSrc("AstLogIf should have been folded by V3Const");
    }
    void visit(AstExprStmt* nodep) override {
        if (!m_lift) return;

        // Eliminate AstExprStmt by lifting the content entirely
        ++m_statLiftedExprStmts;
        iterate(nodep->stmtsp());
        addStmtps(nodep->stmtsp()->unlinkFrBackWithNext());
        iterate(nodep->resultp());
        nodep->replaceWith(nodep->resultp()->unlinkFrBack());
        VL_DO_DANGLING(nodep->deleteTree(), nodep);
    }

    // VISITORS - Accelerate pure leaf expressions
    void visit(AstConst*) override {}
    void visit(AstVarRef*) override {}
    void visit(AstVarXRef*) override {}

    // VISITORS - Expression special cases
    // These return C++ references rather than values, cannot be lifted
    void visit(AstAssocSel* nodep) override { iterateChildren(nodep); }
    void visit(AstCMethodHard* nodep) override { iterateChildren(nodep); }
    // Don't know whether these may return non-values, assume so
    void visit(AstCExpr* nodep) override { iterateChildren(nodep); }
    void visit(AstCExprUser* nodep) override { iterateChildren(nodep); }

public:
    // CONSTRUCTORS
    explicit LiftExprVisitor(AstNetlist* nodep) {
        // Extracting expressions can effect purity
        VIsCached::clearCacheTree();
        iterate(nodep);
        VIsCached::clearCacheTree();
        if (m_newStmtps) m_newStmtps->dumpTreeAndNext(std::cout, "Leftover:");
        UASSERT_OBJ(!m_newStmtps, m_newStmtps, "Failed to insert statements");
    }
    ~LiftExprVisitor() override {
        V3Stats::addStat("LiftExpr, lifted impure expressions", m_statLiftedExprs);
        V3Stats::addStat("LiftExpr, lifted calls", m_statLiftedCalls);
        V3Stats::addStat("LiftExpr, lifted calls as lvalue", m_statLiftedLvalCalls);
        V3Stats::addStat("LiftExpr, lifted Cond", m_statLiftedConds);
        V3Stats::addStat("LiftExpr, lifted LogAnd", m_statLiftedLogAnds);
        V3Stats::addStat("LiftExpr, lifted LogOr", m_statLiftedLogOrs);
        V3Stats::addStat("LiftExpr, lifted ExprStmt", m_statLiftedExprStmts);
        V3Stats::addStat("LiftExpr, temporaries created", m_statTemporariesCreated);
        V3Stats::addStat("LiftExpr, temporaries reused", m_statTemporariesReused);
    }
};

//######################################################################
// Unknown class functions

void V3LiftExpr::liftExprAll(AstNetlist* nodep) {
    UINFO(2, __FUNCTION__ << ":");
    LiftExprVisitor{nodep};
    V3Global::dumpCheckGlobalTree("lift_expr", 0, dumpTreeEitherLevel() >= 3);
}
