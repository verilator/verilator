// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Implementation of assertion properties
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2005-2026 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************
//  Each sequence is translated into a decision tree in form of deterministic
//  finite automaton (DFA) with bipartite structure. Each cycle delay is connected
//  with an expression that depending on an evaluation result, proceeds to the next
//  evaluation state. The structure is rooted with original sequence expression for
//  simplifying further transformation back to AST.
//
//  The graph consists of the following nodes:
//
//  DfaStmtVertex:  Statements to be executed to traverse from one state to another
//  DfaExprVertex:   Property expression that is checked and based on that a branch
//                  is taken.
//  DfaConditionEdge:   Branch edge that connects statements and expressions.
//
//  Properties steps:
//      Ensemble a property decision tree from sequence expressions.
//      Transform property decision tree into AST, remove source sequence expression
//          Property blocks are wrapped with AstPExpr that are transformed
//          further by V3AssertPre and V3Assert.
//
//*************************************************************************

#include "V3PchAstNoMT.h"  // VL_MT_DISABLED_CODE_UNIT

#include "V3AssertProp.h"

#include "V3Const.h"
#include "V3Graph.h"
#include "V3UniqueNames.h"

VL_DEFINE_DEBUG_FUNCTIONS;

//######################################################################
// Data structures (graph types)

class DfaVertex VL_NOT_FINAL : public V3GraphVertex {
    VL_RTTI_IMPL(DfaVertex, V3GraphVertex)
    // STATE
    AstNode* const m_nodep;  // Underlying node

public:
    // CONSTRUCTORS
    explicit DfaVertex(V3Graph* graphp, AstNode* nodep) VL_MT_DISABLED : V3GraphVertex{graphp},
                                                                         m_nodep{nodep} {}
    AstNode* nodep() const { return m_nodep; }
    string name() const override VL_MT_STABLE {
        return cvtToHex(m_nodep) + "\\n " + cvtToStr(m_nodep->typeName()) + "\\n"s
               + m_nodep->fileline()->ascii();
    };
    string dotShape() const override {
        if (inEmpty()) return "tripleoctagon";
        if (outEmpty()) return "doubleoctagon";
        return "oval";
    }
    bool isStart() const { return inEmpty(); }
};

class DfaStmtVertex final : public DfaVertex {
    VL_RTTI_IMPL(DfaStmtVertex, V3GraphEdge)
public:
    // CONSTRUCTORS
    explicit DfaStmtVertex(V3Graph* graphp, AstNodeStmt* stmtp) VL_MT_DISABLED
        : DfaVertex{graphp, stmtp} {}
    string dotColor() const override { return "green"; }
};

class DfaExprVertex final : public DfaVertex {
    VL_RTTI_IMPL(DfaExprVertex, V3GraphEdge)
public:
    // CONSTRUCTORS
    explicit DfaExprVertex(V3Graph* graphp, AstNodeExpr* exprp) VL_MT_DISABLED
        : DfaVertex{graphp, exprp} {}
    string dotColor() const override { return "blue"; }
};

class DfaConditionEdge final : public V3GraphEdge {
    VL_RTTI_IMPL(DfaConditionEdge, V3GraphEdge)
    // STATE
    const bool m_ifBranch;  // Whether this branch is taken for fulfilled condition

public:
    // CONSTRUCTORS
    explicit DfaConditionEdge(V3Graph* graphp, DfaVertex* fromp, DfaVertex* top,
                              bool ifBranch) VL_MT_DISABLED : V3GraphEdge{graphp, fromp, top, 1},
                                                              m_ifBranch{ifBranch} {}
    ~DfaConditionEdge() override = default;

    bool ifBranch() const { return m_ifBranch; }
    string dotColor() const override { return m_ifBranch ? "green" : "red"; }
};

// Check whether a subtree contains any AstSExpr (multi-cycle sequence)
static bool containsSExpr(const AstNode* nodep) {
    return !nodep->forall([](const AstSExpr*) { return false; });
}

// A single step in a sequence timeline: delay cycles followed by an expression check
struct SeqStep final {
    int delayCycles;  // Cycle delay before this check (0 for first step)
    AstNodeExpr* exprp;  // Expression to evaluate at this step
};

// Extract a timeline of (delay, expression) pairs from a sequence expression.
// For a plain expression, returns a single step with delay 0.
// For AstSExpr chains like `a ##1 b ##2 c`, returns [{0,a}, {1,b}, {2,c}].
static std::vector<SeqStep> extractTimeline(AstNodeExpr* nodep) {
    std::vector<SeqStep> timeline;
    if (AstSExpr* const sexprp = VN_CAST(nodep, SExpr)) {
        // Recursively extract from the inner (preExprp) chain first
        if (sexprp->preExprp()) {
            if (AstSExpr* const preSExprp = VN_CAST(sexprp->preExprp(), SExpr)) {
                // preExprp is itself a sequence -- extract its timeline
                timeline = extractTimeline(preSExprp);
            } else {
                // preExprp is a plain expression -- first step at cycle 0
                timeline.push_back({0, sexprp->preExprp()});
            }
        }
        // Get cycle delay from delayp
        int cycles = 0;
        if (AstDelay* const dlyp = VN_CAST(sexprp->delayp(), Delay)) {
            if (AstConst* const constp = VN_CAST(dlyp->lhsp(), Const)) {
                cycles = constp->toSInt();
            } else {
                dlyp->lhsp()->v3warn(
                    E_UNSUPPORTED,
                    "Unsupported: non-constant cycle delay in sequence and/or/intersect");
            }
        }
        // The expression after the delay
        if (AstSExpr* const innerSExprp = VN_CAST(sexprp->exprp(), SExpr)) {
            // Nested SExpr: extract its timeline and offset by current delay
            std::vector<SeqStep> inner = extractTimeline(innerSExprp);
            if (!inner.empty()) {
                inner[0].delayCycles += cycles;
                for (auto& step : inner) timeline.push_back(step);
            }
        } else {
            timeline.push_back({cycles, sexprp->exprp()});
        }
    } else {
        // Plain boolean expression -- single step, no delay
        timeline.push_back({0, nodep});
    }
    return timeline;
}

// True if any AstSExpr in the subtree has a range delay (##[m:n]).
// Uses forall(): predicate returns false when a range delay is found,
// so !forall(...) means "at least one range delay exists".
static bool subtreeHasRangeDelay(const AstNode* nodep) {
    return !nodep->forall([](const AstSExpr* sexprp) {
        if (const AstDelay* const dlyp = VN_CAST(sexprp->delayp(), Delay)) {
            if (dlyp->isRangeDelay()) return false;
        }
        return true;
    });
}

// Lower sequence and/or to AST
class AssertPropLowerVisitor final : public VNVisitor {
    // STATE
    AstNodeModule* m_modp = nullptr;  // Current module
    V3UniqueNames m_seqBrNames{"__VseqBr"};  // Sequence branch dead-tracking name generator

    // Lower a multi-cycle sequence 'and' to an AstPExpr with interleaved if/delay AST.
    void lowerSeqAnd(AstNodeBiop* nodep) {
        FileLine* const flp = nodep->fileline();

        // Extract timelines from both operands
        const std::vector<SeqStep> lhsTimeline = extractTimeline(nodep->lhsp());
        const std::vector<SeqStep> rhsTimeline = extractTimeline(nodep->rhsp());

        // Compute absolute cycle for each step
        struct AbsStep final {
            int cycle;
            AstNodeExpr* exprp;
            int branchId;  // 0=lhs, 1=rhs
        };
        std::vector<AbsStep> allSteps;

        int absCycle = 0;
        for (const auto& step : lhsTimeline) {
            absCycle += step.delayCycles;
            allSteps.push_back({absCycle, step.exprp, 0});
        }
        const int lhsMaxCycle = absCycle;

        absCycle = 0;
        for (const auto& step : rhsTimeline) {
            absCycle += step.delayCycles;
            allSteps.push_back({absCycle, step.exprp, 1});
        }
        const int rhsMaxCycle = absCycle;
        const int maxCycle = std::max(lhsMaxCycle, rhsMaxCycle);

        // Sort by absolute cycle, then by branch id
        std::stable_sort(allSteps.begin(), allSteps.end(), [](const AbsStep& a, const AbsStep& b) {
            if (a.cycle != b.cycle) return a.cycle < b.cycle;
            return a.branchId < b.branchId;
        });

        // Build AstPExprClause terminals
        auto makePass = [&]() -> AstPExprClause* { return new AstPExprClause{flp, true}; };
        auto makeFail = [&]() -> AstPExprClause* { return new AstPExprClause{flp, false}; };

        {
            // AND: all checks must pass. Generate nested if/delay chain.
            // Group steps by cycle, combine same-cycle checks with LogAnd.
            // Build from innermost (last cycle) outward.

            // Group steps by cycle
            std::map<int, std::vector<AstNodeExpr*>> cycleChecks;
            for (const auto& step : allSteps) {
                cycleChecks[step.cycle].push_back(step.exprp->cloneTree(false));
            }

            // Build from the last cycle inward
            AstNode* innerp = makePass();
            int prevCycle = maxCycle;

            for (auto it = cycleChecks.rbegin(); it != cycleChecks.rend(); ++it) {
                const int cycle = it->first;
                auto& exprs = it->second;

                // Combine all expressions at this cycle with LogAnd
                AstNodeExpr* condp = new AstSampled{flp, exprs[0]};
                condp->dtypeSetBit();
                for (size_t i = 1; i < exprs.size(); ++i) {
                    AstNodeExpr* const rp = new AstSampled{flp, exprs[i]};
                    rp->dtypeSetBit();
                    condp = new AstLogAnd{flp, condp, rp};
                    condp->dtypeSetBit();
                }

                // Wrap in if: if (cond) { delay + inner } else { fail }
                AstBegin* const thenp = new AstBegin{flp, "", nullptr, true};
                // Add delay if needed (from this cycle to previous inner cycle)
                if (prevCycle > cycle) {
                    const int delayCycles = prevCycle - cycle;
                    AstDelay* const dlyp = new AstDelay{
                        flp, new AstConst{flp, static_cast<uint32_t>(delayCycles)}, true};
                    thenp->addStmtsp(dlyp);
                    dlyp->addStmtsp(innerp);
                } else {
                    thenp->addStmtsp(innerp);
                }

                AstIf* const ifp = new AstIf{flp, condp, thenp, makeFail()};
                innerp = ifp;
                prevCycle = cycle;
            }

            // Wrap in AstPExpr
            AstBegin* const bodyp = new AstBegin{flp, "", nullptr, true};
            bodyp->addStmtsp(innerp);
            AstPExpr* const pexprp = new AstPExpr{flp, bodyp, nodep->dtypep()};
            nodep->replaceWith(pexprp);
            VL_DO_DANGLING(nodep->deleteTree(), nodep);
        }
    }

    // Lower a multi-cycle sequence 'or' to an AstPExpr with dead-tracking variables.
    // IEEE 1800-2023 16.9.7: composite matches if at least one operand sequence matches.
    // Both branches are evaluated independently from the same start cycle.
    void lowerSeqOr(AstNodeBiop* nodep) {
        UASSERT_OBJ(m_modp, nodep, "SOr not under a module");
        FileLine* const flp = nodep->fileline();

        // Extract timelines from both operands
        const std::vector<SeqStep> lhsTimeline = extractTimeline(nodep->lhsp());
        const std::vector<SeqStep> rhsTimeline = extractTimeline(nodep->rhsp());

        // Compute absolute cycle for each step, mark which is last per branch
        struct AbsStep final {
            int cycle;
            AstNodeExpr* exprp;
            int branchId;
        };
        std::vector<AbsStep> allSteps;

        int absCycle = 0;
        for (const auto& step : lhsTimeline) {
            absCycle += step.delayCycles;
            allSteps.push_back({absCycle, step.exprp, 0});
        }
        const int br0MaxCycle = absCycle;

        absCycle = 0;
        for (const auto& step : rhsTimeline) {
            absCycle += step.delayCycles;
            allSteps.push_back({absCycle, step.exprp, 1});
        }
        const int br1MaxCycle = absCycle;

        // Group by cycle, preserving branch info
        struct CycleEntry final {
            int branchId;
            AstNodeExpr* exprp;
        };
        std::map<int, std::vector<CycleEntry>> cycleChecks;
        for (const auto& step : allSteps) {
            cycleChecks[step.cycle].push_back({step.branchId, step.exprp});
        }

        // Create dead-tracking variables at module level
        AstVar* const br0Deadp = new AstVar{flp, VVarType::MODULETEMP, m_seqBrNames.get("0_dead"),
                                            VFlagBitPacked{}, 1};
        br0Deadp->lifetime(VLifetime::STATIC_EXPLICIT);
        AstVar* const br1Deadp = new AstVar{flp, VVarType::MODULETEMP, m_seqBrNames.get("1_dead"),
                                            VFlagBitPacked{}, 1};
        br1Deadp->lifetime(VLifetime::STATIC_EXPLICIT);
        m_modp->addStmtsp(br0Deadp);
        m_modp->addStmtsp(br1Deadp);

        auto makePass = [&]() -> AstPExprClause* { return new AstPExprClause{flp, true}; };
        auto makeFail = [&]() -> AstPExprClause* { return new AstPExprClause{flp, false}; };

        // Build from innermost (last cycle) outward, same nesting pattern as and
        AstNode* innerp = nullptr;
        int nextCycle = -1;

        for (auto rit = cycleChecks.rbegin(); rit != cycleChecks.rend(); ++rit) {
            const int cycle = rit->first;
            AstBegin* const cycleBlock = new AstBegin{flp, "", nullptr, true};

            // For each branch's check at this cycle
            for (const auto& entry : rit->second) {
                AstVar* const deadVarp = (entry.branchId == 0) ? br0Deadp : br1Deadp;
                const int brMaxCycle = (entry.branchId == 0) ? br0MaxCycle : br1MaxCycle;
                const bool isLast = (cycle == brMaxCycle);

                AstNodeExpr* const sampledp = new AstSampled{flp, entry.exprp->cloneTree(false)};
                sampledp->dtypeSetBit();
                AstNodeExpr* const alivep
                    = new AstLogNot{flp, new AstVarRef{flp, deadVarp, VAccess::READ}};
                alivep->dtypeSetBit();

                if (isLast) {
                    // Last check: alive && passes -> pass
                    AstNodeExpr* const passCond = new AstLogAnd{flp, alivep, sampledp};
                    passCond->dtypeSetBit();
                    cycleBlock->addStmtsp(new AstIf{flp, passCond, makePass()});
                    // alive && fails -> dead
                    AstNodeExpr* const alive2p
                        = new AstLogNot{flp, new AstVarRef{flp, deadVarp, VAccess::READ}};
                    alive2p->dtypeSetBit();
                    AstNodeExpr* const failCond = new AstLogAnd{
                        flp, alive2p, new AstLogNot{flp, sampledp->cloneTree(false)}};
                    failCond->dtypeSetBit();
                    cycleBlock->addStmtsp(
                        new AstIf{flp, failCond,
                                  new AstAssign{flp, new AstVarRef{flp, deadVarp, VAccess::WRITE},
                                                new AstConst{flp, AstConst::BitTrue{}}}});
                } else {
                    // Non-last: alive && fails -> dead
                    AstNodeExpr* const failCond
                        = new AstLogAnd{flp, alivep, new AstLogNot{flp, sampledp}};
                    failCond->dtypeSetBit();
                    cycleBlock->addStmtsp(
                        new AstIf{flp, failCond,
                                  new AstAssign{flp, new AstVarRef{flp, deadVarp, VAccess::WRITE},
                                                new AstConst{flp, AstConst::BitTrue{}}}});
                }
            }

            // Both dead -> fail
            AstNodeExpr* const allDeadp
                = new AstLogAnd{flp, new AstVarRef{flp, br0Deadp, VAccess::READ},
                                new AstVarRef{flp, br1Deadp, VAccess::READ}};
            allDeadp->dtypeSetBit();
            cycleBlock->addStmtsp(new AstIf{flp, allDeadp, makeFail()});

            // Nest delay + inner from later cycles
            if (nextCycle > cycle && innerp) {
                AstDelay* const dlyp = new AstDelay{
                    flp, new AstConst{flp, static_cast<uint32_t>(nextCycle - cycle)}, true};
                cycleBlock->addStmtsp(dlyp);
                dlyp->addStmtsp(innerp);
            }

            innerp = cycleBlock;
            nextCycle = cycle;
        }

        // Wrap in AstPExpr with initialization
        AstBegin* const bodyp = new AstBegin{flp, "", nullptr, true};
        bodyp->addStmtsp(new AstAssign{flp, new AstVarRef{flp, br0Deadp, VAccess::WRITE},
                                       new AstConst{flp, AstConst::BitFalse{}}});
        bodyp->addStmtsp(new AstAssign{flp, new AstVarRef{flp, br1Deadp, VAccess::WRITE},
                                       new AstConst{flp, AstConst::BitFalse{}}});
        bodyp->addStmtsp(innerp);
        AstPExpr* const pexprp = new AstPExpr{flp, bodyp, nodep->dtypep()};
        nodep->replaceWith(pexprp);
        VL_DO_DANGLING(nodep->deleteTree(), nodep);
    }

    // Lower a multi-cycle sequence 'intersect' (IEEE 1800-2023 16.9.6).
    // intersect = and + equal-length constraint: both operands must match with the same duration.
    // When total delays are equal constants, this is identical to 'and'; otherwise constant-false.
    void lowerSeqIntersect(AstNodeBiop* nodep) {
        const std::vector<SeqStep> lhsTimeline = extractTimeline(nodep->lhsp());
        const std::vector<SeqStep> rhsTimeline = extractTimeline(nodep->rhsp());
        int lhsTotal = 0;
        for (const auto& step : lhsTimeline) lhsTotal += step.delayCycles;
        int rhsTotal = 0;
        for (const auto& step : rhsTimeline) rhsTotal += step.delayCycles;
        if (lhsTotal != rhsTotal) {
            // Lengths differ: per IEEE 16.9.6, the match set is empty -- constant-false.
            // Warn the user; mismatched lengths are almost always a mistake.
            // Skip when either operand had a range delay: RangeDelayExpander already
            // replaced it with an FSM expression (containsSExpr returns false) and
            // issued UNSUPPORTED, so no second diagnostic is needed.
            if (containsSExpr(nodep->lhsp()) && containsSExpr(nodep->rhsp())) {
                if (lhsTotal > rhsTotal) {
                    nodep->v3warn(WIDTHEXPAND, "Intersect sequence length mismatch"
                                               " (left "
                                                   << lhsTotal << " cycles, right " << rhsTotal
                                                   << " cycles) -- intersection is always empty");
                } else {
                    nodep->v3warn(WIDTHTRUNC, "Intersect sequence length mismatch"
                                              " (left "
                                                  << lhsTotal << " cycles, right " << rhsTotal
                                                  << " cycles) -- intersection is always empty");
                }
            }
            FileLine* const flp = nodep->fileline();
            AstBegin* const bodyp = new AstBegin{flp, "", nullptr, true};
            bodyp->addStmtsp(new AstPExprClause{flp, false});
            AstPExpr* const pexprp = new AstPExpr{flp, bodyp, nodep->dtypep()};
            nodep->replaceWith(pexprp);
            VL_DO_DANGLING(nodep->deleteTree(), nodep);
            return;
        }
        // Same length: length restriction is trivially satisfied, lower as 'and'.
        lowerSeqAnd(nodep);
    }

    void visit(AstSAnd* nodep) override {
        iterateChildren(nodep);
        if (containsSExpr(nodep->lhsp()) || containsSExpr(nodep->rhsp())) {
            lowerSeqAnd(nodep);
        } else {
            // Pure boolean operands: lower to LogAnd
            AstLogAnd* const newp = new AstLogAnd{nodep->fileline(), nodep->lhsp()->unlinkFrBack(),
                                                  nodep->rhsp()->unlinkFrBack()};
            newp->dtypeFrom(nodep);
            nodep->replaceWith(newp);
            VL_DO_DANGLING(nodep->deleteTree(), nodep);
        }
    }
    void visit(AstSIntersect* nodep) override {
        iterateChildren(nodep);
        if (containsSExpr(nodep->lhsp()) || containsSExpr(nodep->rhsp())) {
            lowerSeqIntersect(nodep);
        } else {
            // Pure boolean operands: length is always 0, lower to LogAnd
            AstLogAnd* const newp = new AstLogAnd{nodep->fileline(), nodep->lhsp()->unlinkFrBack(),
                                                  nodep->rhsp()->unlinkFrBack()};
            newp->dtypeFrom(nodep);
            nodep->replaceWith(newp);
            VL_DO_DANGLING(nodep->deleteTree(), nodep);
        }
    }
    void visit(AstSOr* nodep) override {
        iterateChildren(nodep);
        if (containsSExpr(nodep->lhsp()) || containsSExpr(nodep->rhsp())) {
            lowerSeqOr(nodep);
        } else {
            // Pure boolean operands: lower to LogOr
            AstLogOr* const newp = new AstLogOr{nodep->fileline(), nodep->lhsp()->unlinkFrBack(),
                                                nodep->rhsp()->unlinkFrBack()};
            newp->dtypeFrom(nodep);
            nodep->replaceWith(newp);
            VL_DO_DANGLING(nodep->deleteTree(), nodep);
        }
    }
    void visit(AstSThroughout* nodep) override {
        // IEEE 1800-2023 16.9.9: expr throughout seq
        // Transform by AND-ing cond with every leaf expression in the sequence,
        // and attaching cond to every delay for per-tick checking in V3AssertPre.
        AstNodeExpr* const condp = nodep->lhsp()->unlinkFrBack();
        AstNodeExpr* const seqp = nodep->rhsp()->unlinkFrBack();
        if (AstSExpr* const sexprp = VN_CAST(seqp, SExpr)) {
            // Walk all SExpr nodes: AND cond with leaf expressions, attach to delays
            sexprp->foreach([&](AstSExpr* sp) {
                if (sp->exprp() && !VN_IS(sp->exprp(), SExpr)) {
                    AstNodeExpr* const origp = sp->exprp()->unlinkFrBack();
                    AstLogAnd* const andp
                        = new AstLogAnd{origp->fileline(), condp->cloneTreePure(false), origp};
                    andp->dtypeSetBit();
                    sp->exprp(andp);
                }
                if (sp->preExprp() && !VN_IS(sp->preExprp(), SExpr)) {
                    AstNodeExpr* const origp = sp->preExprp()->unlinkFrBack();
                    AstLogAnd* const andp
                        = new AstLogAnd{origp->fileline(), condp->cloneTreePure(false), origp};
                    andp->dtypeSetBit();
                    sp->preExprp(andp);
                }
                if (AstDelay* const dlyp = VN_CAST(sp->delayp(), Delay)) {
                    dlyp->throughoutp(condp->cloneTreePure(false));
                }
            });
            nodep->replaceWith(sexprp);
            VL_DO_DANGLING(nodep->deleteTree(), nodep);
            VL_DO_DANGLING(condp->deleteTree(), condp);
            visit(sexprp);
        } else {
            // Single expression (no delay): degenerate to cond && seq
            AstLogAnd* const andp = new AstLogAnd{nodep->fileline(), condp, seqp};
            andp->dtypeSetBit();
            nodep->replaceWith(andp);
            VL_DO_DANGLING(nodep->deleteTree(), nodep);
        }
    }
    void visit(AstNodeModule* nodep) override {
        VL_RESTORER(m_modp);
        m_modp = nodep;
        iterateChildren(nodep);
    }
    void visit(AstNode* nodep) override { iterateChildren(nodep); }
    void visit(AstConstPool* nodep) override {}

public:
    explicit AssertPropLowerVisitor(AstNetlist* nodep) { iterate(nodep); }
    ~AssertPropLowerVisitor() override = default;
};

// Parse properties and ensemble a property tree graph
class AssertPropBuildVisitor final : public VNVisitorConst {
    // STATE
    V3Graph& m_graph;  // Property tree
    DfaVertex* m_lastVtxp = nullptr;  // Last encountered vertex
    bool m_underSExpr = false;  // Is under sequence expression, for creating a start node
    size_t m_underLogNots = 0;  // Number of 'not' operators before sequence

    DfaStmtVertex* makeClause(const AstSExpr* nodep, bool pass) {
        return new DfaStmtVertex{
            &m_graph,
            new AstPExprClause{nodep->fileline(), m_underLogNots % 2 == 0 ? pass : !pass}};
    }

    // VISITORS
    void visit(AstNodeCoverOrAssert* nodep) override { iterateChildrenConst(nodep); }
    void visit(AstLogNot* nodep) override {
        VL_RESTORER(m_underLogNots);
        ++m_underLogNots;
        iterateChildrenConst(nodep);
    }
    void visit(AstSExpr* nodep) override {

        if (VN_IS(nodep->exprp(), SExpr)) {
            VL_RESTORER(m_underSExpr);
            m_underSExpr = true;
            iterateConst(nodep->exprp());
        } else {
            DfaExprVertex* const exprVtxp
                = new DfaExprVertex{&m_graph, nodep->exprp()->unlinkFrBack()};
            new DfaConditionEdge{&m_graph, exprVtxp, makeClause(nodep, true), true};
            new DfaConditionEdge{&m_graph, exprVtxp, makeClause(nodep, false), false};
            m_lastVtxp = exprVtxp;
        }

        DfaExprVertex* const startVtxp
            = m_underSExpr ? nullptr : new DfaExprVertex{&m_graph, nodep};

        DfaStmtVertex* const dlyVtxp
            = new DfaStmtVertex{&m_graph, nodep->delayp()->unlinkFrBack()};

        if (AstSExpr* const sexprp = VN_CAST(nodep->preExprp(), SExpr)) {
            UASSERT_OBJ(!sexprp->preExprp() && !VN_IS(sexprp->exprp(), SExpr), sexprp,
                        "Incorrect sexpr tree");
            DfaStmtVertex* const sdlyVtxp
                = new DfaStmtVertex{&m_graph, sexprp->delayp()->unlinkFrBack()};
            DfaExprVertex* const exprVtxp
                = new DfaExprVertex{&m_graph, sexprp->exprp()->unlinkFrBack()};

            if (startVtxp) new DfaConditionEdge{&m_graph, startVtxp, sdlyVtxp, true};
            new DfaConditionEdge{&m_graph, sdlyVtxp, exprVtxp, true};
            new DfaConditionEdge{&m_graph, exprVtxp, dlyVtxp, true};
            new DfaConditionEdge{&m_graph, dlyVtxp, m_lastVtxp, true};
            new DfaConditionEdge{&m_graph, exprVtxp, makeClause(nodep, false), false};

            // This case only occurs when multi-delay sequence starts with an expression,
            // don't set last as this is never a last expression.
        } else if (nodep->preExprp()) {
            DfaExprVertex* const preVtxp
                = new DfaExprVertex{&m_graph, nodep->preExprp()->unlinkFrBack()};
            if (startVtxp) new DfaConditionEdge{&m_graph, startVtxp, preVtxp, true};
            new DfaConditionEdge{&m_graph, preVtxp, dlyVtxp, true};
            new DfaConditionEdge{&m_graph, dlyVtxp, m_lastVtxp, true};
            new DfaConditionEdge{&m_graph, preVtxp, makeClause(nodep, false), false};
            m_lastVtxp = preVtxp;
        } else {
            if (startVtxp) new DfaConditionEdge{&m_graph, startVtxp, dlyVtxp, true};
            new DfaConditionEdge{&m_graph, dlyVtxp, m_lastVtxp, true};
            m_lastVtxp = dlyVtxp;
        }
    }
    void visit(AstSOr* nodep) override {}  // All SOr lowered by AssertPropLowerVisitor
    void visit(AstNode* nodep) override { iterateChildrenConst(nodep); }
    void visit(AstConstPool* nodep) override {}

public:
    // CONSTRUCTORS
    explicit AssertPropBuildVisitor(AstNetlist* nodep, V3Graph& graph)
        : m_graph{graph} {
        iterateConst(nodep);
        if (dumpGraphLevel() >= 6) m_graph.dumpDotFilePrefixedAlways("properties", true);
    }
    ~AssertPropBuildVisitor() override = default;
};

// Transform property graph into AST
class AssertPropTransformer final {
    // STATE
    V3Graph& m_graph;  // Property tree
    AstPExpr* m_pexprp = nullptr;  // Currently built property sequence
    AstBegin* m_current = nullptr;  // Currently built block

    V3GraphVertex* processVtx(V3GraphVertex* vtxp) {
        if (DfaStmtVertex* const stmtp = vtxp->cast<DfaStmtVertex>()) return processVtx(stmtp);
        if (DfaExprVertex* const exprp = vtxp->cast<DfaExprVertex>()) return processVtx(exprp);
        // TODO use C++17 std::variant and std::visit
        v3fatalSrc("Unexpected vertex type");
        return nullptr;
    }
    V3GraphVertex* processVtx(DfaStmtVertex* vtxp) {
        UASSERT_OBJ(!vtxp->isStart(), vtxp->nodep(),
                    "Starting node should be a property expression");
        UASSERT_OBJ(m_current, vtxp->nodep(), "Should be under a block");
        m_current->addStmtsp(vtxp->nodep());
        return processEdge(vtxp->outEdges().frontp());
    }
    V3GraphVertex* processVtx(DfaExprVertex* vtxp) {
        AstNode* const nodep = vtxp->nodep();
        if (vtxp->isStart()) {
            AstBegin* const bodyp = new AstBegin{nodep->fileline(), "", nullptr, true};
            m_pexprp = new AstPExpr{nodep->fileline(), bodyp, nodep->dtypep()};
            UASSERT_OBJ(vtxp->outSize1(), nodep, "Starting node must have one out edge");
            m_current = m_pexprp->bodyp();
            return processEdge(vtxp->outEdges().frontp());
        }
        UASSERT_OBJ(vtxp->outEdges().size() == 2, nodep, "Each expression must have two branches");
        AstBegin* const passsp = new AstBegin{nodep->fileline(), "", nullptr, true};
        AstNode* const failsp = vtxp->outEdges().backp()->top()->as<DfaStmtVertex>()->nodep();

        AstSampled* const sampledp
            = new AstSampled{nodep->fileline(), VN_AS(vtxp->nodep(), NodeExpr)};
        sampledp->dtypeFrom(vtxp->nodep());
        AstIf* const ifp = new AstIf{nodep->fileline(), sampledp, passsp, failsp};
        m_current->addStmtsp(ifp);
        m_current = passsp;
        return processEdge(vtxp->outEdges().frontp());
    }
    V3GraphVertex* processEdge(const V3GraphEdge* edgep) {
        if (edgep) return processVtx(edgep->top());
        return nullptr;
    }

public:
    // CONSTRUCTORS
    explicit AssertPropTransformer(V3Graph& graph)
        : m_graph{graph} {
        for (V3GraphVertex& vtx : m_graph.vertices()) {
            if (DfaVertex* const dVtxp = vtx.cast<DfaExprVertex>()) {
                if (dVtxp->isStart()) {
                    VL_RESTORER(m_pexprp);
                    processVtx(&vtx);
                    AstSExpr* const propp = VN_AS(dVtxp->nodep(), SExpr);
                    propp->replaceWith(m_pexprp);
                    VL_DO_DANGLING(propp->deleteTree(), propp);
                }
            }
        }
    }
};

//######################################################################
// Range delay expansion (runs before DFA builder)
//
// Replaces ##[M:N] range delays with a module-level FSM (always block
// + state/counter vars). No coroutine overhead -- one state advance
// per clock cycle. The SExpr becomes a !fail combinational check.

class RangeDelayExpander final : public VNVisitor {
    // STATE
    V3UniqueNames m_names{"__Vrangedly"};
    AstNodeModule* m_modp = nullptr;  // Current module
    std::vector<AstNode*> m_toDelete;  // Nodes to delete after traversal

    struct SeqStep final {
        AstNodeExpr* exprp;  // Expression to check (nullptr if unary leading delay)
        int delay;  // Fixed delay after this expression (0 for tail)
        bool isRange;  // Step's delay is a range
        bool isUnbounded;  // Range is unbounded (rhs is AstUnbounded)
        int rangeMin;
        int rangeMax;  // -1 for unbounded
    };

    // Extract delay bounds from AstDelay. Clones and constifies (does not modify original AST).
    // For unbounded ranges (rhs is AstUnbounded), maxVal is set to -1; rhsp is not constified.
    bool extractDelayBounds(AstDelay* dlyp, bool& isRange, bool& isUnbounded, int& minVal,
                            int& maxVal) {
        isRange = dlyp->isRangeDelay();
        isUnbounded = dlyp->isUnbounded();
        AstNodeExpr* const minExprp = V3Const::constifyEdit(dlyp->lhsp()->cloneTree(false));
        const AstConst* const minConstp = VN_CAST(minExprp, Const);
        if (isRange) {
            if (isUnbounded) {
                // ##[M:$], ##[*], ##[+]: only min bound; max is open-ended
                if (!minConstp) {
                    dlyp->v3error("Range delay minimum must be an elaboration-time constant"
                                  " (IEEE 1800-2023 16.7)");
                    VL_DO_DANGLING(minExprp->deleteTree(), minExprp);
                    return false;
                }
                minVal = minConstp->toSInt();
                maxVal = -1;
                VL_DO_DANGLING(minExprp->deleteTree(), minExprp);
                if (minVal < 0) {
                    dlyp->v3error("Range delay bounds must be non-negative"
                                  " (IEEE 1800-2023 16.7)");
                    return false;
                }
            } else {
                AstNodeExpr* const maxExprp
                    = V3Const::constifyEdit(dlyp->rhsp()->cloneTree(false));
                const AstConst* const maxConstp = VN_CAST(maxExprp, Const);
                if (!minConstp || !maxConstp) {
                    dlyp->v3error("Range delay bounds must be elaboration-time constants"
                                  " (IEEE 1800-2023 16.7)");
                    VL_DO_DANGLING(minExprp->deleteTree(), minExprp);
                    VL_DO_DANGLING(maxExprp->deleteTree(), maxExprp);
                    return false;
                }
                minVal = minConstp->toSInt();
                maxVal = maxConstp->toSInt();
                VL_DO_DANGLING(minExprp->deleteTree(), minExprp);
                VL_DO_DANGLING(maxExprp->deleteTree(), maxExprp);
                if (minVal < 0 || maxVal < 0) {
                    dlyp->v3error("Range delay bounds must be non-negative"
                                  " (IEEE 1800-2023 16.7)");
                    return false;
                }
                if (maxVal < minVal) {
                    dlyp->v3error("Range delay maximum must be >= minimum"
                                  " (IEEE 1800-2023 16.7)");
                    return false;
                }
                if (minVal == 0) {
                    dlyp->v3warn(E_UNSUPPORTED, "Unsupported: ##0 in bounded range delays");
                    return false;
                }
            }
        } else {
            isUnbounded = false;
            minVal = maxVal = minConstp ? minConstp->toSInt() : 0;
            VL_DO_DANGLING(minExprp->deleteTree(), minExprp);
        }
        return true;
    }

    // Flatten a (possibly nested) SExpr tree into a linear vector of SeqSteps.
    // SExpr trees are left-recursive: (a ##[1:2] b) ##1 c becomes
    //   SExpr(pre=SExpr(a, ##[1:2], b), ##1, c)
    // Output for that example: [{a, range[1:2]}, {b, delay=1}, {c, delay=0}]
    bool linearize(AstSExpr* rootp, std::vector<SeqStep>& steps) {
        bool hasRange = false;
        linearizeImpl(rootp, steps, hasRange /*ref*/);
        return hasRange;
    }

    bool linearizeImpl(AstSExpr* curp, std::vector<SeqStep>& steps, bool& hasRange) {
        if (AstSExpr* const prep = VN_CAST(curp->preExprp(), SExpr)) {
            if (!linearizeImpl(prep, steps, hasRange)) return false;
        }
        AstDelay* const dlyp = VN_CAST(curp->delayp(), Delay);
        UASSERT_OBJ(dlyp, curp, "Expected AstDelay");
        bool isRange = false;
        bool isUnbounded = false;
        int minVal = 0;
        int maxVal = 0;
        if (!extractDelayBounds(dlyp, isRange, isUnbounded, minVal, maxVal)) return false;
        if (isRange) hasRange = true;

        if (curp->preExprp() && !VN_IS(curp->preExprp(), SExpr)) {
            steps.push_back({curp->preExprp(), minVal, isRange, isUnbounded, minVal, maxVal});
        } else {
            steps.push_back({nullptr, minVal, isRange, isUnbounded, minVal, maxVal});
        }

        if (AstSExpr* const nextp = VN_CAST(curp->exprp(), SExpr)) {
            return linearizeImpl(nextp, steps, hasRange);
        }
        steps.push_back({curp->exprp(), 0, false, false, 0, 0});
        return true;
    }

    // Pre-assigned state numbers for one SeqStep.
    // Range steps consume their successor (check target); successor entry is unused.
    struct StepBounds final {
        int waitState;  // WAIT_MIN state, or -1 if not needed
        int checkState;  // CHECK or TAIL state; -1 for fixed-delay steps
    };

    // Assign state numbers to all steps before building FSM bodies.
    //
    // State layout for a ##[M:N] b ##1 c (bounded, M>0):
    //   State 0: IDLE      -- detect trigger, launch FSM
    //   State 1: WAIT_MIN  -- count down M-1 cycles
    //   State 2: CHECK     -- sample b; fail after N-M retries
    //   State 3: WAIT_FIX  -- count down 1 cycle for ##1
    //   State 4: TAIL      -- sample c, report pass/fail
    //
    // For ##[M:$] b ... (unbounded, M>1): same as bounded but CHECK has no timeout.
    // For ##[+] b (unbounded, M=1): WAIT_MIN skipped; CHECK is state 1.
    // For ##[*] b (unbounded, M=0): handled in IDLE directly (no WAIT_MIN).
    //
    // LIMITATION: single-evaluation FSM -- overlapping triggers are ignored
    // while the FSM is active. For ##[M:$], if the consequent never becomes
    // true the FSM remains in CHECK indefinitely, blocking new evaluations.
    std::vector<StepBounds> preAssignStates(const std::vector<SeqStep>& steps) {
        std::vector<StepBounds> bounds(steps.size(), {-1, -1});
        int s = 1;
        for (size_t i = 0; i < steps.size(); ++i) {
            const SeqStep& step = steps[i];
            if (step.isRange) {
                // Unbounded with min<=1: no WAIT_MIN (counter starts at 0 in CHECK).
                const bool needsWait = !step.isUnbounded || step.rangeMin > 1;
                if (needsWait) bounds[i].waitState = s++;
                bounds[i].checkState = s++;
                ++i;  // step[i+1] is the check target, not a separate FSM state
            } else if (step.delay > 0) {
                bounds[i].waitState = s++;
            } else {
                bounds[i].checkState = s++;  // tail check
            }
        }
        return bounds;
    }

    // Build the match action for a range CHECK state.
    // isTail=true: return to IDLE; isTail=false: advance to afterMatchState.
    AstNode* makeOnMatchAction(FileLine* flp, AstVar* stateVarp, AstVar* cntVarp, bool isTail,
                               int afterMatchState, int nextDelay) {
        if (isTail) {
            return new AstAssign{flp, new AstVarRef{flp, stateVarp, VAccess::WRITE},
                                 new AstConst{flp, 0}};
        }
        return makeStateTransition(flp, stateVarp, cntVarp, afterMatchState,
                                   nextDelay > 0 ? nextDelay - 1 : 0);
    }

    // Build the body of a range CHECK state.
    // Bounded: fail on timeout, decrement counter otherwise.
    // Unbounded: stay until match (no timeout).
    AstNode* makeRangeCheckBody(FileLine* flp, AstVar* stateVarp, AstVar* cntVarp,
                                AstVar* failVarp, AstNodeExpr* exprp, AstNode* matchActionp,
                                bool isUnbounded) {
        if (isUnbounded) {
            return new AstIf{flp, new AstSampled{flp, exprp->cloneTree(false)}, matchActionp,
                             nullptr};
        }
        AstBegin* const timeoutp = new AstBegin{flp, "", nullptr, true};
        timeoutp->addStmtsp(new AstAssign{flp, new AstVarRef{flp, failVarp, VAccess::WRITE},
                                          new AstConst{flp, AstConst::BitTrue{}}});
        timeoutp->addStmtsp(new AstAssign{flp, new AstVarRef{flp, stateVarp, VAccess::WRITE},
                                          new AstConst{flp, 0}});
        AstNode* const decrementp = new AstAssign{
            flp, new AstVarRef{flp, cntVarp, VAccess::WRITE},
            new AstSub{flp, new AstVarRef{flp, cntVarp, VAccess::READ}, new AstConst{flp, 1}}};
        AstIf* const failOrRetryp = new AstIf{
            flp, new AstEq{flp, new AstVarRef{flp, cntVarp, VAccess::READ}, new AstConst{flp, 0}},
            timeoutp, decrementp};
        return new AstIf{flp, new AstSampled{flp, exprp->cloneTree(false)}, matchActionp,
                         failOrRetryp};
    }

    AstNode* buildFsmBody(FileLine* flp, AstVar* stateVarp, AstVar* cntVarp, AstVar* failVarp,
                          const std::vector<SeqStep>& steps, AstNodeExpr* antExprp) {

        const std::vector<StepBounds> bounds = preAssignStates(steps);
        AstNode* fsmChainp = nullptr;

        for (size_t i = 0; i < steps.size(); ++i) {
            const SeqStep& step = steps[i];

            if (step.isRange) {
                UASSERT(i + 1 < steps.size(), "Range must have next step");
                const SeqStep& nextStep = steps[i + 1];
                const int afterMatchState = bounds[i].checkState + 1;
                const bool isTail = (i + 2 >= steps.size() && nextStep.delay == 0);

                // WAIT_MIN state: count down rangeMin-1 cycles before entering CHECK
                if (bounds[i].waitState >= 0) {
                    const int initCnt = step.isUnbounded ? 0 : (step.rangeMax - step.rangeMin);
                    AstNode* const waitBodyp = new AstIf{
                        flp,
                        new AstEq{flp, new AstVarRef{flp, cntVarp, VAccess::READ},
                                  new AstConst{flp, 0}},
                        makeStateTransition(flp, stateVarp, cntVarp, bounds[i].checkState,
                                            initCnt),
                        new AstAssign{flp, new AstVarRef{flp, cntVarp, VAccess::WRITE},
                                      new AstSub{flp, new AstVarRef{flp, cntVarp, VAccess::READ},
                                                 new AstConst{flp, 1}}}};
                    fsmChainp
                        = chainState(flp, fsmChainp, stateVarp, bounds[i].waitState, waitBodyp);
                }

                // CHECK state: sample consequent each cycle
                AstNode* const matchActionp = makeOnMatchAction(flp, stateVarp, cntVarp, isTail,
                                                                afterMatchState, nextStep.delay);
                AstNode* const checkBodyp
                    = makeRangeCheckBody(flp, stateVarp, cntVarp, failVarp, nextStep.exprp,
                                         matchActionp, step.isUnbounded);
                fsmChainp
                    = chainState(flp, fsmChainp, stateVarp, bounds[i].checkState, checkBodyp);

                ++i;  // step[i+1] consumed as the CHECK target
                continue;

            } else if (step.delay > 0) {
                // Fixed delay: count down then advance to next state
                const int nextStateNum = bounds[i].waitState + 1;
                AstNode* const bodyp = new AstIf{
                    flp,
                    new AstEq{flp, new AstVarRef{flp, cntVarp, VAccess::READ},
                              new AstConst{flp, 0}},
                    new AstAssign{flp, new AstVarRef{flp, stateVarp, VAccess::WRITE},
                                  new AstConst{flp, static_cast<uint32_t>(nextStateNum)}},
                    new AstAssign{flp, new AstVarRef{flp, cntVarp, VAccess::WRITE},
                                  new AstSub{flp, new AstVarRef{flp, cntVarp, VAccess::READ},
                                             new AstConst{flp, 1}}}};
                fsmChainp = chainState(flp, fsmChainp, stateVarp, bounds[i].waitState, bodyp);

            } else if (i == steps.size() - 1 && step.exprp) {
                // Tail: sample final expression, report pass/fail
                AstNode* const passp = new AstAssign{
                    flp, new AstVarRef{flp, stateVarp, VAccess::WRITE}, new AstConst{flp, 0}};
                AstBegin* const failp = new AstBegin{flp, "", nullptr, true};
                failp->addStmtsp(new AstAssign{flp, new AstVarRef{flp, failVarp, VAccess::WRITE},
                                               new AstConst{flp, AstConst::BitTrue{}}});
                failp->addStmtsp(new AstAssign{flp, new AstVarRef{flp, stateVarp, VAccess::WRITE},
                                               new AstConst{flp, 0}});
                AstIf* const bodyp = new AstIf{
                    flp, new AstSampled{flp, step.exprp->cloneTree(false)}, passp, failp};
                fsmChainp = chainState(flp, fsmChainp, stateVarp, bounds[i].checkState, bodyp);
            }
        }

        // Build IDLE state (state 0)
        AstNode* idleBodyp = nullptr;
        const SeqStep& firstStep = steps[0];

        // Trigger = antecedent AND/OR first step expression
        AstNodeExpr* triggerp = nullptr;
        if (antExprp && firstStep.exprp) {
            triggerp = new AstAnd{flp, new AstSampled{flp, antExprp->cloneTree(false)},
                                  new AstSampled{flp, firstStep.exprp->cloneTree(false)}};
        } else if (antExprp) {
            triggerp = new AstSampled{flp, antExprp->cloneTree(false)};
        } else if (firstStep.exprp) {
            triggerp = new AstSampled{flp, firstStep.exprp->cloneTree(false)};
        }

        if (firstStep.isUnbounded && firstStep.rangeMin == 0 && steps.size() > 1) {
            // ##[*] / ##[0:$]: check consequent immediately in IDLE.
            // On ##0 match: perform match action without entering CHECK.
            // On no match: enter CHECK (state bounds[0].checkState) to wait.
            const SeqStep& nextStep = steps[1];
            const int checkState = bounds[0].checkState;
            const int afterMatch = checkState + 1;
            const bool isTail = (steps.size() == 2 && nextStep.delay == 0);
            AstNodeExpr* const immCheckp = new AstSampled{flp, nextStep.exprp->cloneTree(false)};
            immCheckp->dtypeSetBit();
            AstNode* const immMatchp
                = makeOnMatchAction(flp, stateVarp, cntVarp, isTail, afterMatch, nextStep.delay);
            AstNode* const toCheckp = makeStateTransition(flp, stateVarp, cntVarp, checkState, 0);
            AstIf* const starBodyp = new AstIf{flp, immCheckp, immMatchp, toCheckp};
            if (triggerp) {
                triggerp->dtypeSetBit();
                idleBodyp = new AstIf{flp, triggerp, starBodyp, nullptr};
            } else {
                idleBodyp = starBodyp;
            }
        } else {
            // Standard start: transition to state 1 with appropriate counter
            int initCnt = firstStep.isRange ? firstStep.rangeMin - 1 : firstStep.delay - 1;
            AstNode* const startActionp
                = makeStateTransition(flp, stateVarp, cntVarp, 1, initCnt < 0 ? 0 : initCnt);
            if (triggerp) {
                triggerp->dtypeSetBit();
                idleBodyp = new AstIf{flp, triggerp, startActionp, nullptr};
            } else {
                idleBodyp = startActionp;
            }
        }

        // Chain: if (state == 0) idle else if (state == 1) ... else ...
        AstIf* const idleIfp = new AstIf{
            flp,
            new AstEq{flp, new AstVarRef{flp, stateVarp, VAccess::READ}, new AstConst{flp, 0}},
            idleBodyp, fsmChainp};

        // Reset fail flag at top of each cycle
        AstNode* const resetFailp
            = new AstAssign{flp, new AstVarRef{flp, failVarp, VAccess::WRITE},
                            new AstConst{flp, AstConst::BitFalse{}}};
        resetFailp->addNext(idleIfp);
        return resetFailp;
    }

    // Helper: generate state = newState; cnt = initCnt;
    AstNode* makeStateTransition(FileLine* flp, AstVar* stateVarp, AstVar* cntVarp, int newState,
                                 int initCnt) {
        AstBegin* const blockp = new AstBegin{flp, "", nullptr, true};
        blockp->addStmtsp(new AstAssign{flp, new AstVarRef{flp, stateVarp, VAccess::WRITE},
                                        new AstConst{flp, static_cast<uint32_t>(newState)}});
        blockp->addStmtsp(new AstAssign{flp, new AstVarRef{flp, cntVarp, VAccess::WRITE},
                                        new AstConst{flp, static_cast<uint32_t>(initCnt)}});
        return blockp;
    }

    // Helper: chain a state check into the if/else chain
    // Builds: if (state == stateNum) { body } else { existing chain }
    AstNode* chainState(FileLine* flp, AstNode* existingChainp, AstVar* stateVarp, int stateNum,
                        AstNode* bodyp) {
        AstIf* const ifp = new AstIf{flp,
                                     new AstEq{flp, new AstVarRef{flp, stateVarp, VAccess::READ},
                                               new AstConst{flp, static_cast<uint32_t>(stateNum)}},
                                     bodyp, existingChainp};
        return ifp;
    }

    // Recursively check if any delay in the SExpr tree is a range delay
    static bool containsRangeDelay(AstSExpr* nodep) {
        if (AstDelay* const dlyp = VN_CAST(nodep->delayp(), Delay)) {
            if (dlyp->isRangeDelay()) return true;
        }
        if (AstSExpr* const prep = VN_CAST(nodep->preExprp(), SExpr)) {
            if (containsRangeDelay(prep)) return true;
        }
        if (AstSExpr* const exprp = VN_CAST(nodep->exprp(), SExpr)) {
            if (containsRangeDelay(exprp)) return true;
        }
        return false;
    }

    // Find the clock sensitivity for this SExpr by searching up the tree
    AstSenItem* findClock(AstNode* nodep) {
        for (AstNode* curp = nodep; curp; curp = curp->backp()) {
            if (AstPropSpec* const specp = VN_CAST(curp, PropSpec)) {
                if (specp->sensesp()) return specp->sensesp();
            }
        }
        nodep->v3fatalSrc("Range delay SExpr without clocking event");
        return nullptr;
    }

    // Find implication antecedent if this SExpr is the RHS of |-> or |=>
    // The FSM absorbs the antecedent as its trigger so the implication node
    // can be removed -- otherwise fail timing wouldn't align with the trigger.
    std::pair<AstNodeExpr*, bool> findAntecedent(AstNode* nodep) {
        for (AstNode* curp = nodep; curp; curp = curp->backp()) {
            if (AstImplication* const implp = VN_CAST(curp, Implication)) {
                return {implp->lhsp(), implp->isOverlapped()};
            }
        }
        return {nullptr, false};
    }

    // VISITORS
    void visit(AstNodeModule* nodep) override {
        VL_RESTORER(m_modp);
        m_modp = nodep;
        iterateChildren(nodep);
    }

    void visit(AstSExpr* nodep) override {
        if (!containsRangeDelay(nodep)) {
            iterateChildren(nodep);
            return;
        }
        std::vector<SeqStep> steps;
        if (!linearize(nodep, steps)) {
            nodep->replaceWith(new AstConst{nodep->fileline(), AstConst::BitFalse{}});
            VL_DO_DANGLING(nodep->deleteTree(), nodep);
            return;
        }

        FileLine* const flp = nodep->fileline();

        // Find clock for the FSM (unclocked assertions are caught by V3Assert)
        AstSenItem* const sensesp = findClock(nodep);
        UASSERT_OBJ(sensesp, nodep, "Range delay SExpr without clocking event");

        UASSERT_OBJ(m_modp, nodep, "Range delay SExpr not under a module");

        // Find antecedent (if inside implication)
        const std::pair<AstNodeExpr*, bool> antResult = findAntecedent(nodep);
        AstNodeExpr* const antExprp = antResult.first;
        // const bool isOverlapped = antResult.second;  // Reserved for |=> support

        // Create module-level state variables
        const std::string baseName = m_names.get(nodep);
        AstVar* const stateVarp = new AstVar{flp, VVarType::MODULETEMP, baseName + "__state",
                                             nodep->findBasicDType(VBasicDTypeKwd::UINT32)};
        stateVarp->lifetime(VLifetime::STATIC_EXPLICIT);
        stateVarp->noSample(true);
        AstVar* const cntVarp = new AstVar{flp, VVarType::MODULETEMP, baseName + "__cnt",
                                           nodep->findBasicDType(VBasicDTypeKwd::UINT32)};
        cntVarp->lifetime(VLifetime::STATIC_EXPLICIT);
        cntVarp->noSample(true);
        AstVar* const failVarp = new AstVar{flp, VVarType::MODULETEMP, baseName + "__fail",
                                            nodep->findBasicDType(VBasicDTypeKwd::BIT)};
        failVarp->lifetime(VLifetime::STATIC_EXPLICIT);
        failVarp->noSample(true);

        // Build FSM body
        AstNode* const fsmBodyp = buildFsmBody(flp, stateVarp, cntVarp, failVarp, steps, antExprp);

        // Create Always block for the FSM (same scheduling as assertion always blocks)
        AstAlways* const alwaysp = new AstAlways{
            flp, VAlwaysKwd::ALWAYS, new AstSenTree{flp, sensesp->cloneTree(false)}, fsmBodyp};

        // Add state vars and always block to module
        m_modp->addStmtsp(stateVarp);
        m_modp->addStmtsp(cntVarp);
        m_modp->addStmtsp(failVarp);
        m_modp->addStmtsp(alwaysp);

        // Replace with !fail expression (combinational check).
        // If inside an implication, replace the entire implication since
        // the FSM already handles the antecedent.
        AstNodeExpr* const checkp = new AstNot{flp, new AstVarRef{flp, failVarp, VAccess::READ}};
        checkp->dtypeSetBit();

        if (antExprp) {
            // Find the implication, replace it with the check, defer deletion
            for (AstNode* curp = nodep->backp(); curp; curp = curp->backp()) {
                if (AstImplication* const implp = VN_CAST(curp, Implication)) {
                    implp->replaceWith(checkp);
                    m_toDelete.push_back(implp);
                    break;
                }
            }
        } else {
            nodep->replaceWith(checkp);
            VL_DO_DANGLING(nodep->deleteTree(), nodep);
        }
    }

    void visit(AstSIntersect* nodep) override {
        // intersect with a range-delay operand cannot be lowered: the length-pairing
        // logic requires knowing each operand's concrete length, which is dynamic.
        if (subtreeHasRangeDelay(nodep->lhsp()) || subtreeHasRangeDelay(nodep->rhsp())) {
            nodep->v3warn(E_UNSUPPORTED, "Unsupported: intersect with ranged cycle-delay operand");
        }
        iterateChildren(nodep);
    }

    void visit(AstSThroughout* nodep) override {
        // Reject throughout with range-delay sequences before FSM expansion
        // would silently lose per-tick enforcement (IEEE 1800-2023 16.9.9)
        if (AstSExpr* const sexprp = VN_CAST(nodep->rhsp(), SExpr)) {
            if (containsRangeDelay(sexprp)) {
                nodep->v3warn(E_UNSUPPORTED, "Unsupported: throughout with range delay sequence");
                nodep->replaceWith(new AstConst{nodep->fileline(), AstConst::BitFalse{}});
                VL_DO_DANGLING(nodep->deleteTree(), nodep);
                return;
            }
        }
        // Reject throughout with nested throughout or goto repetition
        if (VN_IS(nodep->rhsp(), SThroughout) || VN_IS(nodep->rhsp(), SGotoRep)) {
            nodep->v3warn(E_UNSUPPORTED, "Unsupported: throughout with complex sequence operator");
            nodep->replaceWith(new AstConst{nodep->fileline(), AstConst::BitFalse{}});
            VL_DO_DANGLING(nodep->deleteTree(), nodep);
            return;
        }
        // Reject throughout with temporal SAnd/SOr (containing SExpr = multi-cycle).
        // Pure boolean SAnd/SOr are OK -- AssertPropLowerVisitor lowers them to LogAnd/LogOr.
        if (VN_IS(nodep->rhsp(), SAnd) || VN_IS(nodep->rhsp(), SOr)) {
            bool hasSExpr = false;
            nodep->rhsp()->foreach([&](const AstSExpr*) { hasSExpr = true; });
            if (hasSExpr) {
                nodep->v3warn(E_UNSUPPORTED,
                              "Unsupported: throughout with complex sequence operator");
                nodep->replaceWith(new AstConst{nodep->fileline(), AstConst::BitFalse{}});
                VL_DO_DANGLING(nodep->deleteTree(), nodep);
                return;
            }
        }
        iterateChildren(nodep);
    }

    void visit(AstNode* nodep) override { iterateChildren(nodep); }

public:
    explicit RangeDelayExpander(AstNetlist* nodep) {
        iterate(nodep);
        for (AstNode* const np : m_toDelete) np->deleteTree();
    }
};

//######################################################################
// Top AssertProp class

void V3AssertProp::assertPropAll(AstNetlist* nodep) {
    UINFO(2, __FUNCTION__ << ":");
    { RangeDelayExpander{nodep}; }
    { AssertPropLowerVisitor{nodep}; }
    {
        V3Graph graph;
        { AssertPropBuildVisitor{nodep, graph}; }
        AssertPropTransformer{graph};
    }
    V3Global::dumpCheckGlobalTree("assertproperties", 0, dumpTreeEitherLevel() >= 3);
}
