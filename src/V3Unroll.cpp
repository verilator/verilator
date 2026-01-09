// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Loop unrolling
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2026 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************
//
// Unroll AstLoopStmts
//
//*************************************************************************

#include "V3PchAstNoMT.h"  // VL_MT_DISABLED_CODE_UNIT

#include "V3Unroll.h"

#include "V3Const.h"
#include "V3Stats.h"

VL_DEFINE_DEBUG_FUNCTIONS;

//######################################################################
// Statistics tracking

struct UnrollStats final {
    class Stat final {
        size_t m_value = 0;  // Statistics value
        const char* const m_name;  // Name for stats file and UDEBUG

    public:
        explicit Stat(const char* const name)
            : m_name{name} {}
        ~Stat() { V3Stats::addStat("Optimizations, Loop unrolling, "s + m_name, m_value); }
        const char* name() const { return m_name; }
        Stat& operator++() {
            ++m_value;
            return *this;
        }
        Stat& operator+=(size_t v) {
            m_value += v;
            return *this;
        }
    };

    // STATE - statistics
    Stat m_nFailCall{"Failed - non-inlined call"};
    Stat m_nFailCondition{"Failed - unknown loop condition"};
    Stat m_nFailFork{"Failed - contains fork"};
    Stat m_nFailInfinite{"Failed - infinite loop"};
    Stat m_nFailNestedLoopTest{"Failed - loop test in sub-statement"};
    Stat m_nFailTimingControl{"Failed - contains timing control"};
    Stat m_nFailUnrollCount{"Failed - reached --unroll-count"};
    Stat m_nFailUnrollStmts{"Failed - reached --unroll-stmts"};
    Stat m_nPragmaDisabled{"Pragma unroll_disable"};
    Stat m_nUnrolledLoops{"Unrolled loops"};
    Stat m_nUnrolledIters{"Unrolled iterations"};
};

//######################################################################
// Unroll one AstLoop

class UnrollOneVisitor final : VNVisitor {
    // NODE STATE
    // AstVarScope::user1p()    AstConst: Value of this AstVarScope
    const VNUser1InUse m_user1InUse;

    // STATE
    UnrollStats& m_stats;  // Statistics tracking
    AstLoop* const m_loopp;  // The loop we are trying to unroll
    AstNode* m_stmtsp = nullptr;  // Resulting unrolled statement
    size_t m_unrolledSize = 0;  // Number of nodes in unrolled loop
    // Temporary block needed for iteration of cloned statements
    AstBegin* const m_wrapp = new AstBegin{m_loopp->fileline(), "[EditWrapper]", nullptr, false};
    const bool m_unrollFull = m_loopp->unroll().isSetTrue();  // Completely unroll the loop?
    bool m_ok = true;  // Unrolling successful so far, gave up if false

    // METHODS
    void cantUnroll(AstNode* nodep, UnrollStats::Stat& stat) {
        m_ok = false;
        ++stat;
        UINFO(4, "   Can't Unroll: " << stat.name() << " :" << nodep);
    }

    // Returns false if the loop terminated (or we gave up)
    bool unrollOneIteration(AstNode* stmtsp) {
        // True if the loop contains at least one dependent AstLoopTest
        bool foundLoopTest = false;
        // Process one body statement at a time
        for (AstNode* stmtp = stmtsp; stmtp; stmtp = stmtp->nextp()) {
            // Check if this is a loop test - before substitution
            if (AstLoopTest* const testp = VN_CAST(stmtp, LoopTest)) {
                AstNode* const condp = V3Const::constifyEdit(testp->condp());
                if (condp->isZero()) {
                    // Loop terminates
                    return false;
                } else if (condp->isNeqZero()) {
                    // Loop test is unconditionally true, ignore
                    continue;
                }
            }

            // Clone and iterate one body statement
            m_wrapp->addStmtsp(stmtp->cloneTree(false));
            iterateAndNextNull(m_wrapp->stmtsp());
            // Give up if failed
            if (!m_ok) return false;

            // Add statements to unrolled body
            while (AstNode* const nodep = m_wrapp->stmtsp()) {
                // Check if we reached the size limit, unless full unrolling is requested
                if (!m_unrollFull) {
                    m_unrolledSize += nodep->nodeCount();
                    if (m_unrolledSize > static_cast<size_t>(v3Global.opt.unrollStmts())) {
                        cantUnroll(m_loopp, m_stats.m_nFailUnrollStmts);
                        return false;
                    }
                }

                // Will be adding to results (or deleting)
                nodep->unlinkFrBack();

                // If a LoopTest, check how it resolved
                if (AstLoopTest* const testp = VN_CAST(nodep, LoopTest)) {
                    foundLoopTest = true;
                    // Will not actually need it, nor any subsequent
                    pushDeletep(testp);
                    // Loop continues - add rest of statements
                    if (testp->condp()->isNeqZero()) continue;
                    // Won't need any of the trailing statements
                    if (m_wrapp->stmtsp()) pushDeletep(m_wrapp->stmtsp()->unlinkFrBackWithNext());
                    // Loop terminates
                    if (testp->condp()->isZero()) return false;
                    // Loop condition unknown - cannot unroll
                    cantUnroll(testp->condp(), m_stats.m_nFailCondition);
                    return false;
                }

                // Add this statement to the result list
                m_stmtsp = AstNode::addNext(m_stmtsp, nodep);

                // Check if terminated via JumpGo
                if (VN_IS(nodep, JumpGo)) {
                    UASSERT_OBJ(!m_wrapp->stmtsp(), nodep, "Statements after JumpGo");
                    // This JumpGo is going directly into the body of the unrolled loop.
                    // A JumpGo always redirects to the end of an enclosing JumpBlock,
                    // so this JumpGo must go outside the loop. The loop terminates.
                    return false;
                }
            }
        }
        // If there is no loop test in the body, give up, it's an infinite loop
        if (!foundLoopTest) {
            cantUnroll(m_loopp, m_stats.m_nFailInfinite);
            return false;
        }
        // One iteration done, loop continues
        return true;
    }

    // Substitute all reads of bound variables with their value. If a write is
    // encountered, remove the binding and don't substitute that variable.
    // Returns false if we can't unroll
    bool process(AstNode* nodep) {
        UASSERT_OBJ(m_ok, nodep, "Should not call 'substituteCondVscp' if we gave up");
        if (!nodep) return true;
        // Variable references we should try to substitute
        std::vector<AstVarRef*> toSubstitute;
        // Iterate subtree
        nodep->foreach([&](AstNode* np) {
            // Failed earlier
            if (!m_ok) return;
            // Check for AstLoopTest
            if (AstLoopTest* const testp = VN_CAST(np, LoopTest)) {
                // Nested loop is OK, bail only if the nested LoopTest is for the current loop
                if (testp->loopp() == m_loopp) cantUnroll(np, m_stats.m_nFailNestedLoopTest);
                return;
            }
            // Check for AstFork - can't unroll
            if (VN_IS(np, Fork)) {
                cantUnroll(np, m_stats.m_nFailFork);
                return;
            }
            // Check for calls - can't unroll if not pure might modify bindings
            if (AstNodeCCall* const callp = VN_CAST(np, NodeCCall)) {
                if (!callp->isPure()) {
                    cantUnroll(np, m_stats.m_nFailCall);
                    return;
                }
            }
            // Check for timing control - can't unroll, might modify bindings
            if (np->isTimingControl()) {
                cantUnroll(np, m_stats.m_nFailTimingControl);
                return;
            }
            // Process variable references
            AstVarRef* const refp = VN_CAST(np, VarRef);
            if (!refp) return;
            // Ignore if the referenced variable has no binding
            AstConst* const valp = VN_AS(refp->varScopep()->user1p(), Const);
            if (!valp) return;
            // If writen, remove the binding
            if (refp->access().isWriteOrRW()) {
                refp->varScopep()->user1p(nullptr);
                return;
            }
            // Otherwise add it to the list of variables to substitute
            toSubstitute.push_back(refp);
        });
        // Give up if we have to
        if (!m_ok) return false;
        // Actually substitute the variables that still have bindings
        for (AstVarRef* const refp : toSubstitute) {
            // Pick up bound value
            AstConst* const valp = VN_AS(refp->varScopep()->user1p(), Const);
            // Binding might have been removed after adding to 'toSubstitute'
            if (!valp) continue;
            // Substitute it
            refp->replaceWith(valp->cloneTree(false));
            VL_DO_DANGLING(pushDeletep(refp), refp);
        }
        return true;
    }

    // CONSTRUCTOR
    UnrollOneVisitor(UnrollStats& stats, AstLoop* loopp)
        : m_stats{stats}
        , m_loopp{loopp} {
        UASSERT_OBJ(!loopp->contsp(), loopp, "'contsp' only used before LinkJump");
        // Do not unroll if we are told not to
        if (loopp->unroll().isSetFalse()) {
            cantUnroll(loopp, m_stats.m_nPragmaDisabled);
            return;
        }
        // Gather variable bindings from the preceding statements
        for (AstNode *succp = loopp, *currp = loopp->backp(); currp->nextp() == succp;
             succp = currp, currp = currp->backp()) {
            AstAssign* const assignp = VN_CAST(currp, Assign);
            if (!assignp) break;
            AstConst* const valp = VN_CAST(V3Const::constifyEdit(assignp->rhsp()), Const);
            if (!valp) break;
            AstVarRef* const lhsp = VN_CAST(assignp->lhsp(), VarRef);
            if (!lhsp) break;
            // Don't bind if volatile
            if (lhsp->varp()->isForced() || lhsp->varp()->isSigUserRWPublic()) continue;
            // Don't overwrite a later binding
            if (lhsp->varScopep()->user1p()) continue;
            // Set up the binding
            lhsp->varScopep()->user1p(valp);
        }
        // Attempt to unroll the loop
        const size_t iterLimit
            = m_unrollFull ? v3Global.opt.unrollLimit() : v3Global.opt.unrollCount();
        size_t iterCount = 0;
        do {
            if (iterCount > iterLimit) {
                cantUnroll(m_loopp, m_stats.m_nFailUnrollCount);
                if (m_unrollFull) {
                    loopp->v3error("Unrolling procedural loop with '/* verilator unroll_full */' "
                                   "took too long; probably this is an infinite loop, otherwise "
                                   "set '--unroll-limit' above "
                                   << iterLimit);
                }
                return;
            }
            ++iterCount;
        } while (unrollOneIteration(loopp->stmtsp()));

        if (m_ok) {
            ++m_stats.m_nUnrolledLoops;
            m_stats.m_nUnrolledIters += iterCount;
        }
    }
    ~UnrollOneVisitor() { VL_DO_DANGLING(m_wrapp->deleteTree(), m_wrapp); }

    // VISIT - these are called for the statements directly in the loop body
    void visit(AstNode* nodep) override {
        if (!m_ok) return;
        // Generic body statement, just substitute
        process(nodep);
    }
    void visit(AstLoopTest* nodep) override {
        if (!m_ok) return;
        // If the condition is a ExprStmt, move it before the LoopTest
        if (AstExprStmt* const exprp = VN_CAST(nodep->condp(), ExprStmt)) {
            AstNode* const stmtsp = exprp->stmtsp()->unlinkFrBackWithNext();
            exprp->replaceWith(exprp->resultp()->unlinkFrBack());
            VL_DO_DANGLING(pushDeletep(exprp), exprp);
            VNRelinker relinker;
            nodep->unlinkFrBack(&relinker);
            stmtsp->addNext(nodep);
            relinker.relink(stmtsp);
            return;
        }
        // Substitute the condition only, this is not a nested AstLoopTest
        process(nodep->condp());
        // Also simplify it, it will be checked later
        V3Const::constifyEdit(nodep->condp());
    }
    void visit(AstAssign* nodep) override {
        if (!m_ok) return;
        // Can't do it if delayed
        if (nodep->timingControlp()) {
            cantUnroll(nodep, m_stats.m_nFailTimingControl);
            return;
        }
        if (!process(nodep->rhsp())) return;
        // If a simple variable assignment, update the binding
        AstVarRef* const lhsp = VN_CAST(nodep->lhsp(), VarRef);
        AstConst* const valp = VN_CAST(V3Const::constifyEdit(nodep->rhsp()), Const);
        if (lhsp && valp && !lhsp->varp()->isForced() && !lhsp->varp()->isSigUserRWPublic()) {
            lhsp->varScopep()->user1p(valp);
            return;
        }
        // Otherwise just like a generic statement
        process(nodep->lhsp());
    }
    void visit(AstIf* nodep) override {
        if (!m_ok) return;
        if (!process(nodep->condp())) return;
        // If condition is constant, replce with the relevant branch
        if (AstConst* const condp = VN_CAST(V3Const::constifyEdit(nodep->condp()), Const)) {
            if (AstNode* const bodyp = condp->isNeqZero() ? nodep->thensp() : nodep->elsesp()) {
                nodep->addNextHere(bodyp->unlinkFrBackWithNext());  // This will be iterated next
            }
            VL_DO_DANGLING(pushDeletep(nodep->unlinkFrBack()), nodep);
            return;
        }
        // Otherwise just like a generic statement
        process(nodep);
    }
    void visit(AstJumpGo* nodep) override {
        // Remove trailing dead code
        if (nodep->nextp()) pushDeletep(nodep->nextp()->unlinkFrBackWithNext());
    }

public:
    // Unroll the given loop. Returns the resulting statements and the number of
    // iterations unrolled (0 if unrolling failed);
    static std::pair<AstNode*, bool> apply(UnrollStats& stats, AstLoop* loopp) {
        UnrollOneVisitor visitor{stats, loopp};
        // If successfully unrolled, return the resulting list of statements - might be empty
        if (visitor.m_ok) return {visitor.m_stmtsp, true};
        // Otherwise delete intermediate results
        if (visitor.m_stmtsp) VL_DO_DANGLING(visitor.m_stmtsp->deleteTree(), visitor.m_stmtsp);
        return {nullptr, false};
    }
};

//######################################################################
// Unroll all AstLoop statements

class UnrollAllVisitor final : VNVisitor {
    // STATE - Statistic tracking
    UnrollStats m_stats;

    // VISIT
    void visit(AstLoop* nodep) override {
        // Attempt to unroll this loop
        const std::pair<AstNode*, bool> pair = UnrollOneVisitor::apply(m_stats, nodep);

        // If failed, carry on with nested loop
        if (!pair.second) {
            iterateChildren(nodep);
            return;
        }

        // Otherwise replace the loop with the unrolled code - might be empty
        if (pair.first) {
            nodep->replaceWith(pair.first);
            VL_DO_DANGLING(pushDeletep(nodep), nodep);
        } else {
            VL_DO_DANGLING(pushDeletep(nodep->unlinkFrBack()), nodep);
        }
        // Iteration continues with the unrolled body
    }
    void visit(AstNode* nodep) override { iterateChildren(nodep); }

    // CONSTRUCTOR
    explicit UnrollAllVisitor(AstNetlist* netlistp) { iterate(netlistp); }

public:
    static void apply(AstNetlist* netlistp) { UnrollAllVisitor{netlistp}; }
};

//######################################################################
// V3Unroll class functions

void V3Unroll::unrollAll(AstNetlist* nodep) {
    UINFO(2, __FUNCTION__ << ":");
    UnrollAllVisitor::apply(nodep);
    V3Global::dumpCheckGlobalTree("unroll", 0, dumpTreeEitherLevel() >= 3);
}
