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
//    if (__VleLogAnd_0 !== 1'b0) {
//      __VleCall_0 = func(y);
//      __VleLogAnd_0 = __VleLogAnd_0 & __VleCall_0;
//    }
//    z = __VleLogAnd_0;
// Similar patterns are used for AstLogOr, AstLogIf and AstCond to preserve
// the short-circuiting semantics and side effects.
// The guard is '!==' as an X/Z condition must evaluate both sides (IEEE
// 1800-2023 11.4.7, 11.4.11). AstCond is kept for V3Tristate.
//
// Care must be taken for impure LValues as well. While, all LValue expressions
// permitted by IEEE-1800 are themselves pure (except possibly for the non-lvalue
// sub-expressions like array indices, which are not a problem), we support a
// non-standard but common extension where a function call returning a class
// handle, under a member select can be an LValue, e.g.:
//    'getInstance().member = foo;'
// Fortunately we can discover these via MemberRef, and we can transform them
// to the IEEE-1800 compliant form:
//    __VleLvalCall_0 = getInstance();
//    __VleLvalCall_0.member = foo;
// Selects that can insert an element when written (AssocSel, QueueSel and
// WildcardSel) are also impure LValues. For this reason only we still need to
// special case their handling via AstNodeExpr::isLValue().
//
// $fscanf/$sscanf: the call is always lifted into a statement of its own,
// and non-addressable destinations (part-selects, members, array elements)
// are written through a temporary that is written back after the call.
// Calls in contexts that cannot be lifted are rejected.
//
// Temporaries are only live within their statement, so later statements of the
// same procedure or function reuse them, except those of a statement with a fork.
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
    const VNUser1InUse m_user1InUse;

    // STATE
    AstNodeModule* m_modp = nullptr;  // Current module
    AstNodeFTask* m_ftaskp = nullptr;  // Current function/task
    bool m_lift = false;  // Lift encountered expressions
    AstNodeStmt* m_newStmtps = nullptr;  // Statements lifted out of current node
    // Expressions in some special locations need not, or should not be lifted
    AstNodeExpr* m_doNotLiftp = nullptr;
    size_t m_nTmps = 0;  // Sequence numbers for temporary variables
    std::unordered_map<const AstNodeDType*, std::vector<AstVar*>> m_freeTmps;  // Free temporaries
    std::vector<AstVar*> m_usedTmps;  // Temporaries used by the current statement
    bool m_forked = false;  // Current statement contains a fork
    bool m_staticInit = false;  // Under a function's static initializer
    // Statistics
    VDouble0 m_statLiftedExprs;
    VDouble0 m_statLiftedCalls;  // Statistic, calls lifted
    VDouble0 m_statLiftedLvalCalls;  // Statistic, lvalue calls lifted
    VDouble0 m_statLiftedConds;  // Statistic, conditionals lifted
    VDouble0 m_statLiftedLogAnds;  // Statistic, logical ANDs lifted
    VDouble0 m_statLiftedLogOrs;  // Statistic, logical ORs lifted
    VDouble0 m_statLiftedLogIfs;  // Statistic, logical implications lifted
    VDouble0 m_statLiftedExprStmts;  // Statistic, expression statements lifted
    VDouble0 m_statLiftedCaseConds;  // Statistic, case conditions lifted
    VDouble0 m_statScanfDests;  // Statistic, $fscanf/$sscanf destinations rewritten
    VDouble0 m_statTemporariesCreated;  // Statistic, temporaries created
    VDouble0 m_statTemporariesReused;  // Statistic, temporaries reused

    // METHODS
    AstVar* newVar(const char* baseName, const AstNodeExpr* exprp,
                   const std::string& suffix = "") {
        AstNodeDType* const dtypep = exprp->dtypep()->skipRefp();
        // V3Task may use a static function call's temporary as its persistent result variable
        const AstNodeFTaskRef* const callp = VN_CAST(exprp, NodeFTaskRef);
        const bool reusable = !callp || callp->taskp()->lifetime().isAutomatic();
        std::vector<AstVar*>& freeps = m_freeTmps[dtypep];
        if (reusable && !freeps.empty()) {
            ++m_statTemporariesReused;
            AstVar* const varp = freeps.back();
            freeps.pop_back();
            m_usedTmps.push_back(varp);
            return varp;
        }

        // Need a separate name in functions vs modules, as module inlining
        // can otherwise cause spurious VARHIDDEN warnings
        std::string name = m_ftaskp ? "__Vlef" : "__Vlem";
        name += baseName;
        name += "_" + std::to_string(m_nTmps++);
        if (!suffix.empty()) name += "__" + suffix;

        // Create variable
        ++m_statTemporariesCreated;
        AstVar* const varp = new AstVar{exprp->fileline(), VVarType::MODULETEMP, name, dtypep};
        varp->isInternal(true);
        varp->noReset(true);
        varp->user1(1);  // Mark as lifted temporary so it can be reused

        if (m_ftaskp) {
            varp->funcLocal(true);
            m_ftaskp->prependDeclsp(varp);
            varp->lifetime(m_staticInit ? VLifetime::STATIC_EXPLICIT
                                        : VLifetime::AUTOMATIC_EXPLICIT);
        } else {
            m_modp->prependStmtsp(varp);
            // 'automatic' on a variable inside a class actually means 'member'
            varp->lifetime(VN_IS(m_modp, Class) ? VLifetime::STATIC_EXPLICIT
                                                : VLifetime::AUTOMATIC_EXPLICIT);
        }
        if (reusable) m_usedTmps.push_back(varp);
        return varp;
    }

    void iterateStmts(const VNList<AstNodeStmt>& stmtps) {
        VL_RESTORER_CLEAR(m_freeTmps);
        VL_RESTORER_CLEAR(m_usedTmps);
        VL_RESTORER(m_forked);
        iterateSequence(stmtps);
    }
    void iterateSequence(const VNList<AstNodeStmt>& stmtps) {
        for (AstNodeStmt* const stmtp : stmtps) {
            // V3Begin flattens these later
            if (AstBegin* const beginp = VN_CAST(stmtp, Begin)) {
                iterateSequence(beginp->stmtspList());
                continue;
            }
            m_forked = false;
            iterate(stmtp);
            if (!m_forked) {
                for (AstVar* const varp : m_usedTmps) m_freeTmps[varp->dtypep()].push_back(varp);
            }
            m_usedTmps.clear();
        }
    }

    // Also copies user variables, as side effects might change them
    AstAssign* newTemporary(const char* baseName, AstNodeExpr* nodep) {
        if (const AstVarRef* const refp = VN_CAST(nodep, VarRef)) {
            if (refp->varp()->user1()) return nullptr;
        }
        FileLine* const flp = nodep->fileline();
        AstVar* const varp = newVar(baseName, nodep);
        nodep->replaceWith(new AstVarRef{flp, varp, VAccess::READ});
        return new AstAssign{flp, new AstVarRef{flp, varp, VAccess::WRITE}, nodep};
    }

    AstIf* newGuard(AstVar* condVarp, bool skipValue, AstNodeStmt* stmtps) {
        FileLine* const flp = stmtps->fileline();
        AstIf* const ifp
            = new AstIf{flp, new AstNeqCase{flp, new AstVarRef{flp, condVarp, VAccess::READ},
                                            new AstConst{flp, AstConst::BitTrue{}, skipValue}}};
        ifp->addThensp(stmtps);
        return ifp;
    }

    void liftShortCircuit(AstNodeBiop* nodep, bool skipValue, const char* baseName,
                          VDouble0& stat) {
        iterate(nodep->lhsp());
        AstNodeStmt* const rhsStmtps = lift(nodep->rhsp());
        if (!rhsStmtps) return;

        ++stat;
        FileLine* const flp = nodep->fileline();
        AstVar* const varp = newVar(baseName, nodep);
        AstNodeExpr* lhsp = nodep->lhsp()->unlinkFrBack();
        if (VN_IS(nodep, LogIf)) lhsp = new AstLogNot{flp, lhsp};
        addStmtps(new AstAssign{flp, new AstVarRef{flp, varp, VAccess::WRITE}, lhsp});
        // V3Width made the operands 1-bit, so '&' and '|' match '&&' and '||', X/Z included
        AstNodeExpr* const refp = new AstVarRef{flp, varp, VAccess::READ};
        AstNodeExpr* const rhsp = nodep->rhsp()->unlinkFrBack();
        AstNodeExpr* valuep;
        if (skipValue) {
            valuep = new AstOr{flp, refp, rhsp};
        } else {
            valuep = new AstAnd{flp, refp, rhsp};
        }
        AstIf* const ifp = newGuard(varp, skipValue, rhsStmtps);
        ifp->addThensp(new AstAssign{flp, new AstVarRef{flp, varp, VAccess::WRITE}, valuep});
        addStmtps(ifp);
        nodep->replaceWith(new AstVarRef{flp, varp, VAccess::READ});
        VL_DO_DANGLING(pushDeletep(nodep), nodep);
    }

    void addStmtps(AstNodeStmt* stmtp) {
        if (!stmtp) return;
        // No need to process again, so mark
        for (AstNode* const nodep : VNList<AstNode>{stmtp}) nodep->user1(1);
        m_newStmtps = AstNode::addNext(m_newStmtps, stmtp);
    }

    // Lift expressions from expression, return lifted statements
    AstNodeStmt* lift(AstNodeExpr* nodep) {
        if (!nodep) return nullptr;
        VL_RESTORER(m_lift);
        VL_RESTORER(m_newStmtps);
        m_lift = true;
        m_newStmtps = nullptr;
        iterate(nodep);
        return m_newStmtps;
    }

    // Lift expressions from children of given statement, return lifted statements
    AstNodeStmt* liftChildren(AstNodeStmt* nodep) {
        VL_RESTORER(m_lift);
        VL_RESTORER(m_newStmtps);
        m_lift = true;
        m_newStmtps = nullptr;
        iterateChildren(nodep);
        return m_newStmtps;
    }

    template <class T>
    void visitScanf(T* nodep) {
        if (!m_lift) {
            nodep->v3error("Unsupported: $fscanf/$sscanf in this context");
            return;
        }
        iterateChildren(nodep);
        // Lift the call into a statement of its own, ignoring any
        // doNotLift, so the write-backs below can follow it
        ++m_statLiftedExprs;
        FileLine* const flp = nodep->fileline();
        AstVar* const varp = newVar("Expr", nodep);
        nodep->replaceWith(new AstVarRef{flp, varp, VAccess::READ});
        addStmtps(new AstAssign{flp, new AstVarRef{flp, varp, VAccess::WRITE}, nodep});
        // Redirect the non-addressable destinations to temporary variables
        // and write those back to the destinations
        for (AstNodeExpr* const destp : nodep->exprspList()) {
            if (!VN_IS(destp, VarRef)) {
                AstVar* const tmp = newVar("Scanf", destp);
                destp->replaceWith(new AstVarRef{flp, tmp, VAccess::WRITE});
                addStmtps(new AstAssign{flp, destp, new AstVarRef{flp, tmp, VAccess::READ}});
                ++m_statScanfDests;
            }
        }
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
        iterateStmts(nodep->stmtspList());
    }
    void visit(AstNodeProcedure* nodep) override { iterateStmts(nodep->stmtspList()); }
    void visit(AstAlways* nodep) override {
        iterateAndNextNull(nodep->sentreep());
        iterateStmts(nodep->stmtspList());
    }
    void visit(AstCaseItem* nodep) override {
        for (AstNode* const condp : nodep->condspList()) {
            // Lift under the AstExprStmt that will hold the lifted statements, as lifting
            // may replace the condition
            VNRelinker relinker;
            condp->unlinkFrBack(&relinker);
            AstExprStmt* const exprStmtp
                = new AstExprStmt{condp->fileline(), nullptr, VN_AS(condp, NodeExpr)};
            if (AstNodeStmt* const newStmtps = lift(exprStmtp->resultp())) {
                ++m_statLiftedCaseConds;
                exprStmtp->addStmtsp(newStmtps);
                relinker.relink(exprStmtp);
            } else {
                relinker.relink(exprStmtp->resultp()->unlinkFrBack());
                VL_DO_DANGLING(exprStmtp->deleteTree(), exprStmtp);
            }
        }
        iterateAndNextNull(nodep->stmtsp());
    }
    void visit(AstCell* nodep) override {
        // Inouts are reconnected by V3Tristate
        for (AstPin* pinp = nodep->pinsp(); pinp; pinp = VN_AS(pinp->nextp(), Pin)) {
            AstNodeExpr* const exprp = VN_AS(pinp->exprp(), NodeExpr);
            if (!exprp || pinp->modVarp()->isInout()) continue;
            // Also pins with calls, which are lifted even when pure
            if (exprp->isPure() && !exprp->exists([](const AstNodeFTaskRef*) { return true; }))
                continue;
            V3Inst::pinReconnectSimple(pinp, nodep, false);
        }
    }
    void visit(AstAlias* nodep) override {}
    void visit(AstArg* nodep) override {
        // Lift argument expressions
        iterateChildren(nodep);
    }

    // VISITORS - statements
    void visit(AstFork* nodep) override {
        m_forked = true;
        visit(static_cast<AstNodeStmt*>(nodep));
    }
    void visit(AstInitialStaticStmt* nodep) override {
        // V3Begin moves these out of functions, together with static variables
        VL_RESTORER(m_staticInit);
        m_staticInit = true;
        iterateStmts(nodep->stmtspList());
    }
    void visit(AstWait* nodep) override {
        if (nodep->user1SetOnce()) return;
        VL_RESTORER(m_doNotLiftp);
        m_doNotLiftp = nullptr;
        // Keep lifted statements inside the repeatedly evaluated condition.
        if (AstNodeStmt* const newStmtps = lift(nodep->condp())) {
            AstNodeExpr* const condp = nodep->condp()->unlinkFrBack();
            nodep->condp(new AstExprStmt{nodep->fileline(), newStmtps, condp});
        }
        iterateAndNextNull(nodep->stmtsp());
    }
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

        // Lifting from NBA LHS is safe as it evaluates at the same time as the RHS
        if (nodep->timingControlp() && !VN_IS(nodep, AssignDly)) return;

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
    void visit(AstMemberRef* nodep) override {
        if (!m_lift) return;
        // MemberRef is special as it can appear as an LValue selecting from a call
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
        // This one is a WRITE or READWRITE, same as the MemberRef
        nodep->fromp(new AstVarRef{flp, varp, nodep->access()});
    }

    // VISITORS - $fscanf/$sscanf
    void visit(AstFScanF* nodep) override { visitScanf(nodep); }
    void visit(AstSScanF* nodep) override { visitScanf(nodep); }

    // VISITORS - RValue expressions
    void visit(AstCond* nodep) override {
        if (!m_lift) return;

        // Lift from condition
        iterate(nodep->condp());
        AstNodeStmt* const thenStmtps = lift(nodep->thenp());
        AstNodeStmt* const elseStmtps = lift(nodep->elsep());
        if (!thenStmtps && !elseStmtps) return;

        ++m_statLiftedConds;
        addStmtps(newTemporary("Cond", nodep->condp()));
        AstVar* const condVarp = VN_AS(nodep->condp(), VarRef)->varp();
        if (thenStmtps) addStmtps(newGuard(condVarp, false, thenStmtps));
        if (elseStmtps) addStmtps(newGuard(condVarp, true, elseStmtps));
    }
    void visit(AstLogAnd* nodep) override {
        if (!m_lift) return;
        liftShortCircuit(nodep, false, "LogAnd", m_statLiftedLogAnds);
    }
    void visit(AstLogOr* nodep) override {
        if (!m_lift) return;
        liftShortCircuit(nodep, true, "LogOr", m_statLiftedLogOrs);
    }
    void visit(AstLogIf* nodep) override {
        if (!m_lift) return;
        liftShortCircuit(nodep, true, "LogIf", m_statLiftedLogIfs);
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
    void visit(AstDynArraySel* nodep) override { iterateChildren(nodep); }
    void visit(AstQueueSel* nodep) override { iterateChildren(nodep); }
    void visit(AstWildcardSel* nodep) override { iterateChildren(nodep); }
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
        V3Stats::addStat("LiftExpr, lifted LogIf", m_statLiftedLogIfs);
        V3Stats::addStat("LiftExpr, lifted ExprStmt", m_statLiftedExprStmts);
        V3Stats::addStat("LiftExpr, lifted case conditions", m_statLiftedCaseConds);
        V3Stats::addStat("LiftExpr, $fscanf/$sscanf destinations rewritten", m_statScanfDests);
        V3Stats::addStat("LiftExpr, temporaries created", m_statTemporariesCreated);
        V3Stats::addStat("LiftExpr, temporaries reused", m_statTemporariesReused);
    }
};

//######################################################################
// Unknown class functions

void V3LiftExpr::liftExprAll(AstNetlist* nodep) {
    UINFO(2, __FUNCTION__ << ":");
    { LiftExprVisitor{nodep}; }
    V3Global::dumpCheckGlobalTree("lift_expr", 0, dumpTreeEitherLevel() >= 3);
}
