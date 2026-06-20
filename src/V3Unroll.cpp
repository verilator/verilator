// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Loop unrolling
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
    Stat m_bitScanLowered{"Lowered priority-encoder to mostsetbitp1"};
    Stat m_countOnesLowered{"Lowered count-set-bits to countones"};
};

//######################################################################
// Variable bindings
class UnrolllBindings final {
    // NODE STATE
    // AstVarScope::user1()    int: index of the binding in m_bindings
    const VNUser1InUse m_inuser1;

    // STATE
    // Map from AstVarScope::user1() to current variable value, nullptr if not bound - idx 0 unused
    std::vector<AstConst*> m_curr{nullptr};
    // Stack of binding checkpoints
    std::vector<std::vector<AstConst*>> m_checkpoints;

public:
    // CONSTRUCTOR
    UnrolllBindings() = default;
    ~UnrolllBindings() = default;
    VL_UNCOPYABLE(UnrolllBindings);
    VL_UNMOVABLE(UnrolllBindings);

    // METHODS
    void clear() {
        m_curr.resize(1);
        m_checkpoints.clear();
        AstNode::user1ClearTree();
    }

    void checkpoint() { m_checkpoints.push_back(m_curr); }

    void revert() {
        m_curr = std::move(m_checkpoints.back());
        m_checkpoints.pop_back();
    }

    void commit() { m_checkpoints.pop_back(); }

    void set(AstVarScope* vscp, AstConst* valp) {
        if (!vscp->user1()) {
            vscp->user1(m_curr.size());
            m_curr.push_back(nullptr);
        }
        UINFO(6, "Binding SET " << vscp->name() << " / " << vscp->user1() << " := " << valp);
        m_curr[vscp->user1()] = valp;
    }

    AstConst* get(AstVarScope* vscp) {
        // It's possible after a revert that user1 is set, but the vector is shorter, pad up
        if (static_cast<size_t>(vscp->user1()) >= m_curr.size()) {
            m_curr.resize(vscp->user1() + 1, nullptr);
        }
        AstConst* const valp = vscp->user1() ? m_curr[vscp->user1()] : nullptr;
        UINFO(6, "Binding GET " << vscp->name() << " / " << vscp->user1() << " == " << valp);
        return valp;
    }
};

//######################################################################
// Unroll one AstLoop

class UnrollOneVisitor final : VNVisitor {
    // STATE
    UnrollStats& m_stats;  // Statistics tracking
    UnrolllBindings& m_bindings;  // Variable bindings
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
            AstConst* const valp = m_bindings.get(refp->varScopep());
            if (!valp) return;
            // If writen, remove the binding
            if (refp->access().isWriteOrRW()) {
                m_bindings.set(refp->varScopep(), nullptr);
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
            AstConst* const valp = m_bindings.get(refp->varScopep());
            // Binding might have been removed after adding to 'toSubstitute'
            if (!valp) continue;
            // Substitute it
            refp->replaceWith(valp->cloneTree(false));
            VL_DO_DANGLING(pushDeletep(refp), refp);
        }
        return true;
    }

    // CONSTRUCTOR
    UnrollOneVisitor(UnrollStats& stats, UnrolllBindings& bindings, AstLoop* loopp)
        : m_stats{stats}
        , m_bindings{bindings}
        , m_loopp{loopp} {
        UASSERT_OBJ(!loopp->contsp(), loopp, "'contsp' only used before LinkJump");
        // Do not unroll if we are told not to
        if (loopp->unroll().isSetFalse()) {
            cantUnroll(loopp, m_stats.m_nPragmaDisabled);
            return;
        }
        // Attempt to unroll the loop
        const size_t iterLimit = m_unrollFull ? v3Global.opt.unrollLimit()  //
                                              : v3Global.opt.unrollCount();
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
            m_bindings.set(lhsp->varScopep(), valp);
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
    void visit(AstLoop* nodep) override {
        m_bindings.checkpoint();
        std::pair<AstNode*, bool> pair = UnrollOneVisitor::apply(m_stats, m_bindings, nodep);

        // If failed, revert the bindings and process the loop as a generic statement
        if (!pair.second) {
            m_bindings.revert();
            process(nodep);
            return;
        }

        // Commit the bindings and replace the loop with the unrolled code
        m_bindings.commit();
        if (pair.first) {
            nodep->replaceWith(pair.first);
        } else {
            nodep->unlinkFrBack();
        }
        VL_DO_DANGLING(pushDeletep(nodep), nodep);
    }

public:
    // Unroll the given loop. Returns the resulting statements and a flag indicating success
    static std::pair<AstNode*, bool> apply(UnrollStats& stats, UnrolllBindings& bindings,
                                           AstLoop* loopp) {
        UnrollOneVisitor visitor{stats, bindings, loopp};
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
    // STATE
    UnrollStats m_stats;  // Statistic tracking
    UnrolllBindings m_bindings;  // Variable bindings

    // METHODS
    // Peel value-preserving width casts/truncations (Extend/ExtendS, or a low-bits Sel
    // with constant lsb 0) to reach the underlying VarRef; nullptr for anything else
    // (e.g. an arithmetic offset like idx+1 or idx*2).
    static AstVarRef* unwrapToVarRef(AstNodeExpr* nodep) {
        while (nodep) {
            if (AstVarRef* const refp = VN_CAST(nodep, VarRef)) return refp;
            if (AstExtend* const ep = VN_CAST(nodep, Extend)) {
                nodep = ep->lhsp();
            } else if (AstExtendS* const ep = VN_CAST(nodep, ExtendS)) {
                nodep = ep->lhsp();
            } else if (AstSel* const sp = VN_CAST(nodep, Sel)) {
                const AstConst* const lsbp = VN_CAST(sp->lsbp(), Const);
                if (!lsbp || lsbp->toUInt() != 0) return nullptr;
                nodep = sp->fromp();
            } else {
                return nullptr;
            }
        }
        return nullptr;
    }
    // True if 'nodep' is exactly 'var + 1' (commutative), where the var operand is the
    // given variable reached through value-preserving casts only.
    bool isVarPlus1(AstNode* nodep, const AstVarScope* vscp) {
        AstAdd* const addp = VN_CAST(nodep, Add);
        if (!addp) return false;
        const auto isOne = [](AstNodeExpr* p) -> bool {
            const AstConst* const cp = VN_CAST(p, Const);
            return cp && !cp->num().isFourState() && cp->toUInt() == 1;
        };
        const AstVarRef* const l = unwrapToVarRef(addp->lhsp());
        const AstVarRef* const r = unwrapToVarRef(addp->rhsp());
        if (isOne(addp->rhsp()) && l && l->varScopep() == vscp) return true;
        if (isOne(addp->lhsp()) && r && r->varScopep() == vscp) return true;
        return false;
    }
    // Match a strict ascending loop bound 'idx < W', written either way and signed or
    // unsigned:  (W > idx) [Gt/GtS]  or  (idx < W) [Lt/LtS].  Sets wp and idxRefp.
    static bool ascendingBound(AstNodeExpr* condp, AstConst*& wp, AstVarRef*& idxRefp) {
        if (VN_IS(condp, Gt) || VN_IS(condp, GtS)) {
            AstNodeBiop* const bp = VN_AS(condp, NodeBiop);
            wp = VN_CAST(bp->lhsp(), Const);
            idxRefp = VN_CAST(bp->rhsp(), VarRef);
        } else if (VN_IS(condp, Lt) || VN_IS(condp, LtS)) {
            AstNodeBiop* const bp = VN_AS(condp, NodeBiop);
            idxRefp = VN_CAST(bp->lhsp(), VarRef);
            wp = VN_CAST(bp->rhsp(), Const);
        } else {
            return false;
        }
        return wp && idxRefp && !wp->num().isFourState();
    }
    // Recognize a single-bit scan loop over all W bits of 'vec' (idx 0..W-1, target
    // pre-zeroed) and lower it to a bit-reduction primitive.  Two idioms are matched:
    //   target = 0; idx = 0;
    //   loop { looptest(W > idx); if (...vec[idx]...) target = <e>; idx = idx + 1; }
    // where, when W == width(vec):
    //   <e> = idx + 1     => target = $mostsetbitp1(vec)  (leading-one / bit-width)
    //   <e> = target + 1  => target = $countones(vec)     (population count)
    bool tryLowerBitScanLoop(AstLoop* loopp) {
        // Body must be exactly: LoopTest, If, Assign(increment)
        AstLoopTest* const testp = VN_CAST(loopp->stmtsp(), LoopTest);
        if (!testp) return false;
        AstIf* const ifp = VN_CAST(testp->nextp(), If);
        if (!ifp) return false;
        AstAssign* const incp = VN_CAST(ifp->nextp(), Assign);
        if (!incp || incp->nextp()) return false;
        // Loop test: a strict ascending bound 'idx < W' (W > idx), signed or unsigned
        AstConst* wp = nullptr;
        AstVarRef* idxRefp = nullptr;
        if (!ascendingBound(testp->condp(), wp, idxRefp)) return false;
        AstVarScope* const idxVscp = idxRefp->varScopep();
        const uint32_t width = wp->toUInt();
        // Index must start at 0 (so it takes exactly the values 0..W-1)
        const AstConst* const idxInitp = m_bindings.get(idxVscp);
        if (!idxInitp || idxInitp->num().isFourState() || idxInitp->toUInt() != 0) return false;
        // Increment must be exactly:  idx = idx + 1
        AstVarRef* const incLhsp = VN_CAST(incp->lhsp(), VarRef);
        if (!incLhsp || incLhsp->varScopep() != idxVscp) return false;
        if (!isVarPlus1(incp->rhsp(), idxVscp)) return false;
        // If: no else, and 'then' is exactly one assignment 'target = <expr>'
        if (ifp->elsesp()) return false;
        AstAssign* const thenp = VN_CAST(ifp->thensp(), Assign);
        if (!thenp || thenp->nextp()) return false;
        AstVarRef* const targetRefp = VN_CAST(thenp->lhsp(), VarRef);
        if (!targetRefp) return false;
        AstVarScope* const targetVscp = targetRefp->varScopep();
        if (targetVscp == idxVscp) return false;
        const bool isLeadingOne = isVarPlus1(thenp->rhsp(), idxVscp);
        const bool isCountOnes = !isLeadingOne && isVarPlus1(thenp->rhsp(), targetVscp);
        if (!isLeadingOne && !isCountOnes) return false;
        // $countones yields a 32-bit result; only fold when the accumulator fits in 32 bits.
        if (isCountOnes && targetRefp->width() > 32) return false;
        // If-cond must select exactly bit 'idx' of some vector 'vec' (vec != idx/target)
        AstNodeExpr* vecExprp = nullptr;
        ifp->condp()->foreach([&](AstSel* selp) {
            if (vecExprp || selp->width() != 1) return;
            const AstVarRef* const fromp = VN_CAST(selp->fromp(), VarRef);
            if (!fromp) return;
            const AstVarScope* const fromVscp = fromp->varScopep();
            if (fromVscp == idxVscp || fromVscp == targetVscp) return;
            const AstVarRef* const idxInSel = unwrapToVarRef(selp->lsbp());
            if (idxInSel && idxInSel->varScopep() == idxVscp) vecExprp = selp->fromp();
        });
        if (!vecExprp) return false;
        // The loop must scan exactly all bits of 'vec'
        if (static_cast<int>(width) != vecExprp->width()) return false;
        // 'target' must be const-0 immediately before the loop (collected in m_bindings),
        // so that an all-zero 'vec' yields 0, matching $mostsetbitp1's definition.
        const AstConst* const targetInitp = m_bindings.get(targetVscp);
        if (!targetInitp || targetInitp->num().isFourState() || targetInitp->toUInt() != 0) {
            return false;
        }
        // Lower the loop to:  target = <reduction>(vec);  idx = W;
        // The 'idx = W' store preserves the counted loop's exit value, so the rewrite is
        // sound even if idx is read after the loop (dead-code elimination drops it if not).
        FileLine* const flp = loopp->fileline();
        AstNodeExpr* reducep;
        if (isLeadingOne) {
            AstMostSetBitP1* const msbp = new AstMostSetBitP1{flp, vecExprp->cloneTree(false)};
            msbp->dtypeFrom(targetRefp);
            reducep = msbp;
        } else {
            // $countones must yield a 32-bit result (DFG invariant); narrow afterwards to
            // the accumulator width to match the loop's wrap-around behaviour.
            AstCountOnes* const conep = new AstCountOnes{flp, vecExprp->cloneTree(false)};
            conep->dtypeSetInteger2State();
            reducep
                = (targetRefp->width() < 32)
                      ? static_cast<AstNodeExpr*>(new AstSel{flp, conep, 0, targetRefp->width()})
                      : static_cast<AstNodeExpr*>(conep);
        }
        AstAssign* const newp = new AstAssign{flp, targetRefp->cloneTree(false), reducep};
        newp->addNext(new AstAssign{flp, incLhsp->cloneTree(false), wp->cloneTree(false)});
        loopp->replaceWith(newp);
        VL_DO_DANGLING(pushDeletep(loopp), loopp);
        if (isLeadingOne) {
            UINFO(4, "Lowered priority-encoder loop to $mostsetbitp1: " << newp);
            ++m_stats.m_bitScanLowered;
        } else {
            UINFO(4, "Lowered count-set-bits loop to $countones: " << newp);
            ++m_stats.m_countOnesLowered;
        }
        return true;
    }

    // VISIT
    void visit(AstLoop* nodep) override {
        // Gather variable bindings from the preceding statements
        m_bindings.clear();
        for (AstNode *succp = nodep, *currp = nodep->backp(); true;
             succp = currp, currp = currp->backp()) {
            // If the current statement is in higher list, proceed carefully
            if (currp->nextp() != succp) {
                // Jump block is OK, there is only one way to get here
                if (VN_IS(currp, JumpBlock)) continue;
                // TODO: if?
                // Otherwise we dont' know the control flow, give up
                break;
            }
            AstAssign* const assignp = VN_CAST(currp, Assign);
            if (!assignp) break;
            AstConst* const valp = VN_CAST(V3Const::constifyEdit(assignp->rhsp()), Const);
            if (!valp) break;
            AstVarRef* const lhsp = VN_CAST(assignp->lhsp(), VarRef);
            if (!lhsp) break;
            // Don't bind if volatile
            if (lhsp->varp()->isForced() || lhsp->varp()->isSigUserRWPublic()) continue;
            // Don't overwrite a later binding
            if (m_bindings.get(lhsp->varScopep())) continue;
            // Set up the binding
            m_bindings.set(lhsp->varScopep(), valp);
        }

        // Recognize a leading-one / priority-encoder loop and lower it to $mostsetbitp1
        if (v3Global.opt.fBitScanLoops() && tryLowerBitScanLoop(nodep)) return;

        // Attempt to unroll this loop
        const std::pair<AstNode*, bool> pair = UnrollOneVisitor::apply(m_stats, m_bindings, nodep);

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
