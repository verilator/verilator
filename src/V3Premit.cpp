// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Add temporaries, such as for premit nodes
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2024 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************
// V3Premit's Transformations:
//
// Each module:
//      For each wide OP, make a a temporary variable with the wide value
//      For each deep expression, assign expression to temporary.
//
// Each display (independent transformation; here as Premit is a good point)
//      If autoflush, insert a flush
//
//*************************************************************************

#include "V3PchAstNoMT.h"  // VL_MT_DISABLED_CODE_UNIT

#include "V3Premit.h"

#include "V3Stats.h"
#include "V3UniqueNames.h"

VL_DEFINE_DEBUG_FUNCTIONS;

constexpr int STATIC_CONST_MIN_WIDTH = 256;  // Minimum size to extract to static constant

//######################################################################
// Premit state, as a visitor of each AstNode

class PremitVisitor final : public VNVisitor {
    // NODE STATE
    //  AstNodeExpr::user()     -> bool.  True if iterated already
    //  *::user3()              -> Used when visiting AstNodeAssign
    const VNUser1InUse m_inuser1;

    // STATE - across all visitors
    VDouble0 m_extractedToConstPool;  // Statistic tracking

    // STATE - for current visit position (use VL_RESTORER)
    AstCFunc* m_cfuncp = nullptr;  // Current block
    size_t m_tmpVarCnt = 0;  // Number of temporary variables created inside a function
    AstNode* m_stmtp = nullptr;  // Current statement
    AstWhile* m_inWhileCondp = nullptr;  // Inside condition of this while loop
    bool m_assignLhs = false;  // Inside assignment lhs, don't breakup extracts

    // METHODS
    void checkNode(AstNodeExpr* nodep) {
        // Consider adding a temp for this expression.
        if (!m_stmtp) return;  // Not under a statement
        if (nodep->user1SetOnce()) return;  // Already processed
        if (!nodep->isWide()) return;  // Not wide
        if (m_assignLhs) return;  // This is an lvalue!
        UASSERT_OBJ(!VN_IS(nodep->firstAbovep(), ArraySel), nodep, "Should have been ignored");
        createWideTemp(nodep);
    }

    AstVar* createWideTemp(AstNodeExpr* nodep) {
        UASSERT_OBJ(m_stmtp, nodep, "Attempting to create temporary with no insertion point");
        UINFO(4, "createWideTemp: " << nodep << endl);

        VNRelinker relinker;
        nodep->unlinkFrBack(&relinker);

        FileLine* const flp = nodep->fileline();
        AstConst* const constp = VN_CAST(nodep, Const);
        const bool useConstPool = constp  // Is a constant
                                  && (constp->width() >= STATIC_CONST_MIN_WIDTH)  // Large enough
                                  && !constp->num().isFourState()  // Not four state
                                  && !constp->num().isString();  // Not a string

        AstVar* varp = nullptr;
        AstAssign* assignp = nullptr;

        if (useConstPool) {
            // Extract into constant pool.
            const bool merge = v3Global.opt.fMergeConstPool();
            varp = v3Global.rootp()->constPoolp()->findConst(constp, merge)->varp();
            nodep->deleteTree();
            ++m_extractedToConstPool;
        } else {
            // Keep as local temporary.
            const std::string name = "__Vtemp_" + std::to_string(++m_tmpVarCnt);
            varp = new AstVar{flp, VVarType::STMTTEMP, name, nodep->dtypep()};
            m_cfuncp->addInitsp(varp);

            // Put assignment before the referencing statement
            assignp = new AstAssign{flp, new AstVarRef{flp, varp, VAccess::WRITE}, nodep};
            if (m_inWhileCondp) {
                // Statements that are needed for the 'condition' in a while
                // actually have to be put before & after the loop, since we
                // can't do any statements in a while's (cond).
                m_inWhileCondp->addPrecondsp(assignp);
            } else {
                m_stmtp->addHereThisAsNext(assignp);
            }
        }

        // Replace node with VarRef to new Var
        relinker.relink(new AstVarRef{flp, varp, VAccess::READ});

        // Handle wide expressions inside the expression recursively
        if (assignp) iterate(assignp);

        // Return the temporary variable
        return varp;
    }

    void visitShift(AstNodeBiop* nodep) {
        // Shifts of > 32/64 bits in C++ will wrap-around and generate non-0s
        UINFO(4, "  ShiftFix  " << nodep << endl);
        const AstConst* const shiftp = VN_CAST(nodep->rhsp(), Const);
        if (shiftp && shiftp->num().mostSetBitP1() > 32) {
            shiftp->v3error(
                "Unsupported: Shifting of by over 32-bit number isn't supported."
                << " (This isn't a shift of 32 bits, but a shift of 2^32, or 4 billion!)\n");
        }
        if (nodep->widthMin() <= 64  // Else we'll use large operators which work right
                                     // C operator's width must be < maximum shift which is
                                     // based on Verilog width
            && nodep->width() < (1LL << nodep->rhsp()->widthMin())) {
            AstNode* newp;
            if (VN_IS(nodep, ShiftL)) {
                newp = new AstShiftLOvr{nodep->fileline(), nodep->lhsp()->unlinkFrBack(),
                                        nodep->rhsp()->unlinkFrBack()};
            } else if (VN_IS(nodep, ShiftR)) {
                newp = new AstShiftROvr{nodep->fileline(), nodep->lhsp()->unlinkFrBack(),
                                        nodep->rhsp()->unlinkFrBack()};
            } else {
                UASSERT_OBJ(VN_IS(nodep, ShiftRS), nodep, "Bad case");
                newp = new AstShiftRSOvr{nodep->fileline(), nodep->lhsp()->unlinkFrBack(),
                                         nodep->rhsp()->unlinkFrBack()};
            }
            newp->dtypeFrom(nodep);
            nodep->replaceWith(newp);
            VL_DO_DANGLING(pushDeletep(nodep), nodep);
            return;
        }
        iterateChildren(nodep);
        checkNode(nodep);
    }

    static bool rhsReadsLhs(AstNodeAssign* nodep) {
        const VNUser3InUse user3InUse;
        nodep->lhsp()->foreach([](const AstVarRef* refp) {
            if (refp->access().isWriteOrRW()) refp->varp()->user3(true);
        });
        return nodep->rhsp()->exists([](const AstVarRef* refp) {
            return refp->access().isReadOnly() && refp->varp()->user3();
        });
    }

    // VISITORS
    void visit(AstCFunc* nodep) override {
        UASSERT_OBJ(!m_cfuncp, nodep, "Should not nest");
        VL_RESTORER(m_cfuncp);
        VL_RESTORER(m_tmpVarCnt);
        m_cfuncp = nodep;
        m_tmpVarCnt = 0;
        iterateChildren(nodep);
    }

    // VISITORS - Statements
#define START_STATEMENT_OR_RETURN(stmtp) \
    if (!m_cfuncp) return; \
    if (stmtp->user1SetOnce()) return; \
    VL_RESTORER(m_assignLhs); \
    VL_RESTORER(m_stmtp); \
    VL_RESTORER(m_inWhileCondp); \
    m_assignLhs = false; \
    m_stmtp = stmtp; \
    m_inWhileCondp = nullptr

    void visit(AstWhile* nodep) override {
        UINFO(4, "  WHILE  " << nodep << endl);
        START_STATEMENT_OR_RETURN(nodep);
        iterateAndNextNull(nodep->precondsp());
        {
            VL_RESTORER(m_inWhileCondp);
            m_inWhileCondp = nodep;
            iterateAndNextNull(nodep->condp());
        }
        iterateAndNextNull(nodep->stmtsp());
        iterateAndNextNull(nodep->incsp());
    }
    void visit(AstNodeAssign* nodep) override {
        START_STATEMENT_OR_RETURN(nodep);

        // Direct assignment to a simple variable
        if (VN_IS(nodep->lhsp(), VarRef) && !AstVar::scVarRecurse(nodep->lhsp())) {
            AstNode* const rhsp = nodep->rhsp();
            // Rhs is already a var ref, so nothing to so
            if (VN_IS(rhsp, VarRef) && !AstVar::scVarRecurse(rhsp)) return;
            if (!VN_IS(rhsp, Const)) {
                // Don't replace the rhs, it's already a simple assignment
                rhsp->user1(true);
            } else if (rhsp->width() < STATIC_CONST_MIN_WIDTH) {
                // It's a small constant, so nothing to do, otherwise will be put to const pool
                return;
            }
        }

        if (rhsReadsLhs(nodep)) {
            // Need to do this even if not wide, as e.g. a select may be on a wide operator
            createWideTemp(nodep->rhsp());
        } else {
            iterateAndNextNull(nodep->rhsp());
        }

        m_assignLhs = true;  // Restored by VL_RESTORER in START_STATEMENT_OR_RETURN
        iterateAndNextNull(nodep->lhsp());
    }
    void visit(AstDisplay* nodep) override {
        START_STATEMENT_OR_RETURN(nodep);
        iterateChildren(nodep);
        if (v3Global.opt.autoflush()) {
            const AstNode* searchp = nodep->nextp();
            while (searchp && VN_IS(searchp, Comment)) searchp = searchp->nextp();
            if (searchp && VN_IS(searchp, Display)
                && nodep->filep()->sameGateTree(VN_AS(searchp, Display)->filep())) {
                // There's another display next; we can just wait to flush
            } else {
                UINFO(4, "Autoflush " << nodep << endl);
                nodep->addNextHere(
                    new AstFFlush{nodep->fileline(),
                                  nodep->filep() ? nodep->filep()->cloneTreePure(true) : nullptr});
            }
        }
    }
    void visit(AstNodeStmt* nodep) override {
        START_STATEMENT_OR_RETURN(nodep);
        iterateChildren(nodep);
    }

#undef START_STATEMENT_OR_RETURN

    // VISITORS - Expressions
    void visit(AstShiftL* nodep) override { visitShift(nodep); }
    void visit(AstShiftR* nodep) override { visitShift(nodep); }
    void visit(AstShiftRS* nodep) override { visitShift(nodep); }

    void visit(AstConst* nodep) override { checkNode(nodep); }
    // Operators
    void visit(AstNodeTermop* nodep) override { checkNode(nodep); }
    void visit(AstNodeUniop* nodep) override {
        iterateChildren(nodep);
        checkNode(nodep);
    }
    void visit(AstNodeBiop* nodep) override {
        iterateChildren(nodep);
        checkNode(nodep);
    }
    void visit(AstRand* nodep) override {
        iterateChildren(nodep);
        checkNode(nodep);
    }
    void visit(AstRandRNG* nodep) override {
        iterateChildren(nodep);
        checkNode(nodep);
    }
    void visit(AstUCFunc* nodep) override {
        iterateChildren(nodep);
        checkNode(nodep);
    }
    void visit(AstSel* nodep) override {
        iterateAndNextNull(nodep->fromp());
        {  // Only the 'from' is part of the assignment LHS
            VL_RESTORER(m_assignLhs);
            m_assignLhs = false;
            iterateAndNextNull(nodep->lsbp());
            // AstSel::widthp() must remain a constant, so not iterating
        }
        checkNode(nodep);
    }
    void visit(AstArraySel* nodep) override {
        // Skip straight to children. Don't replace the array
        iterateChildren(nodep->fromp());
        {  // Only the 'from' is part of the assignment LHS
            VL_RESTORER(m_assignLhs);
            m_assignLhs = false;
            // Index is never wide, so skip straight to children
            iterateChildren(nodep->bitp());
        }
        // ArraySel are just pointer arithmetic and should never be replaced
    }
    void visit(AstAssocSel* nodep) override {
        iterateAndNextNull(nodep->fromp());
        {  // Only the 'from' is part of the assignment LHS
            VL_RESTORER(m_assignLhs);
            m_assignLhs = false;
            iterateAndNextNull(nodep->bitp());
        }
        checkNode(nodep);
    }
    void visit(AstNodeCond* nodep) override {
        iterateChildren(nodep);
        if (nodep->thenp()->isWide() && !VN_IS(nodep->condp(), Const)
            && !VN_IS(nodep->condp(), VarRef)) {
            // We're going to need the expression several times in the expanded code,
            // so might as well make it a common expression
            createWideTemp(nodep->condp());
            VIsCached::clearCacheTree();
        }
        checkNode(nodep);
    }
    void visit(AstSFormatF* nodep) override {
        iterateChildren(nodep);
        // Any strings sent to a display must be var of string data type,
        // to avoid passing a pointer to a temporary.
        for (AstNodeExpr *expp = nodep->exprsp(), *nextp; expp; expp = nextp) {
            nextp = VN_AS(expp->nextp(), NodeExpr);
            if (expp->isString() && !VN_IS(expp, VarRef)) {
                AstVar* const varp = createWideTemp(expp);
                // Do not remove VarRefs to this in V3Const
                varp->noSubst(true);
            }
        }
    }

    //--------------------
    // Default: Just iterate
    void visit(AstVar*) override {}  // Don't hit varrefs under vars
    void visit(AstNode* nodep) override { iterateChildren(nodep); }

public:
    // CONSTRUCTORS
    explicit PremitVisitor(AstNetlist* nodep) { iterate(nodep); }
    ~PremitVisitor() override {
        V3Stats::addStat("Optimizations, Prelim extracted value to ConstPool",
                         m_extractedToConstPool);
    }
};

//######################################################################
// Premit class functions

void V3Premit::premitAll(AstNetlist* nodep) {
    UINFO(2, __FUNCTION__ << ": " << endl);
    { PremitVisitor{nodep}; }  // Destruct before checking
    V3Global::dumpCheckGlobalTree("premit", 0, dumpTreeEitherLevel() >= 3);
}
