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
                dlyp->lhsp()->v3warn(E_UNSUPPORTED,
                                     "Unsupported: non-constant cycle delay in sequence and/or");
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
    void visit(AstSExprThroughout* nodep) override {
        // IEEE 1800-2023 16.9.9: expr throughout seq
        // Transform by AND-ing cond with every leaf expression in the sequence,
        // and attaching cond to every delay for per-tick checking in V3AssertPre.
        AstNodeExpr* const condp = nodep->condp()->unlinkFrBack();
        AstNodeExpr* const seqp = nodep->seqp()->unlinkFrBack();
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
        bool isRange;  // Whether this step's delay is a range
        int rangeMin;
        int rangeMax;
    };

    // Extract delay bounds from AstDelay. Clones and constifies (does not modify original AST).
    bool extractDelayBounds(AstDelay* dlyp, bool& isRange, int& minVal, int& maxVal) {
        isRange = dlyp->isRangeDelay();
        AstNodeExpr* const minExprp = V3Const::constifyEdit(dlyp->lhsp()->cloneTree(false));
        const AstConst* const minConstp = VN_CAST(minExprp, Const);
        if (isRange) {
            AstNodeExpr* const maxExprp = V3Const::constifyEdit(dlyp->rhsp()->cloneTree(false));
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
                dlyp->v3warn(E_UNSUPPORTED, "Unsupported: ##0 in range delays");
                return false;
            }
        } else {
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
        int minVal = 0;
        int maxVal = 0;
        if (!extractDelayBounds(dlyp, isRange, minVal, maxVal)) return false;
        if (isRange) hasRange = true;

        if (curp->preExprp() && !VN_IS(curp->preExprp(), SExpr)) {
            steps.push_back({curp->preExprp(), minVal, isRange, minVal, maxVal});
        } else {
            steps.push_back({nullptr, minVal, isRange, minVal, maxVal});
        }

        if (AstSExpr* const nextp = VN_CAST(curp->exprp(), SExpr)) {
            return linearizeImpl(nextp, steps, hasRange);
        }
        steps.push_back({curp->exprp(), 0, false, 0, 0});
        return true;
    }

    // Build FSM body as if/else chain on state variable.
    // State 0 = IDLE. Each range delay adds 2 states (wait + check),
    // each fixed delay adds 1 (wait), each tail expr adds 1 (check).
    //
    // Example: a ##[M:N] b ##1 c
    //   steps: [{a, range[M:N]}, {b, delay=1}, {c, delay=0}]
    //   State 1: WAIT_MIN (count down M cycles)
    //   State 2: CHECK_RANGE (check b each cycle, up to N-M retries)
    //   State 3: WAIT_FIXED (count down 1 cycle for ##1)
    //   State 4: CHECK_TAIL (check c, report pass/fail)
    AstNode* buildFsmBody(FileLine* flp, AstVar* stateVarp, AstVar* cntVarp, AstVar* failVarp,
                          const std::vector<SeqStep>& steps, AstSenItem* /*sensesp*/,
                          AstNodeExpr* antExprp) {

        AstNode* fsmChainp = nullptr;
        int nextState = 1;

        for (size_t i = 0; i < steps.size(); ++i) {
            const SeqStep& step = steps[i];

            if (step.isRange) {
                // Range delay needs two states: WAIT_MIN and CHECK_RANGE
                UASSERT(i + 1 < steps.size(), "Range must have next step");
                const int waitState = nextState++;
                const int checkState = nextState++;
                const int rangeWidth = step.rangeMax - step.rangeMin;
                const SeqStep& nextStep = steps[i + 1];

                const int afterMatchState = nextState;

                // WAIT_MIN: count down rangeMin cycles
                {
                    AstNode* const bodyp = new AstIf{
                        flp,
                        new AstEq{flp, new AstVarRef{flp, cntVarp, VAccess::READ},
                                  new AstConst{flp, 0}},
                        makeStateTransition(flp, stateVarp, cntVarp, checkState, rangeWidth),
                        new AstAssign{flp, new AstVarRef{flp, cntVarp, VAccess::WRITE},
                                      new AstSub{flp, new AstVarRef{flp, cntVarp, VAccess::READ},
                                                 new AstConst{flp, 1}}}};
                    fsmChainp = chainState(flp, fsmChainp, stateVarp, waitState, bodyp);
                }

                // CHECK_RANGE: check expr each cycle, fail on timeout
                {
                    AstNode* matchActionp = nullptr;
                    AstNode* const timeoutp = new AstBegin{flp, "", nullptr, true};
                    VN_AS(timeoutp, Begin)
                        ->addStmtsp(new AstAssign{flp,
                                                  new AstVarRef{flp, failVarp, VAccess::WRITE},
                                                  new AstConst{flp, AstConst::BitTrue{}}});
                    VN_AS(timeoutp, Begin)
                        ->addStmtsp(new AstAssign{flp,
                                                  new AstVarRef{flp, stateVarp, VAccess::WRITE},
                                                  new AstConst{flp, 0}});
                    AstNode* const decrementp
                        = new AstAssign{flp, new AstVarRef{flp, cntVarp, VAccess::WRITE},
                                        new AstSub{flp, new AstVarRef{flp, cntVarp, VAccess::READ},
                                                   new AstConst{flp, 1}}};

                    AstIf* const failOrRetryp
                        = new AstIf{flp,
                                    new AstEq{flp, new AstVarRef{flp, cntVarp, VAccess::READ},
                                              new AstConst{flp, 0}},
                                    timeoutp, decrementp};

                    if (nextStep.delay > 0) {
                        matchActionp = makeStateTransition(flp, stateVarp, cntVarp,
                                                           afterMatchState, nextStep.delay - 1);
                    } else {
                        matchActionp
                            = makeStateTransition(flp, stateVarp, cntVarp, afterMatchState, 0);
                    }

                    AstIf* const checkp
                        = new AstIf{flp, new AstSampled{flp, nextStep.exprp->cloneTree(false)},
                                    matchActionp, failOrRetryp};

                    fsmChainp = chainState(flp, fsmChainp, stateVarp, checkState, checkp);
                }

                // Skip next step (already consumed as the range check target)
                ++i;
                continue;

            } else if (step.delay > 0) {
                // Fixed delay: count down then advance
                const int waitState = nextState++;
                AstNode* const bodyp = new AstIf{
                    flp,
                    new AstEq{flp, new AstVarRef{flp, cntVarp, VAccess::READ},
                              new AstConst{flp, 0}},
                    new AstAssign{flp, new AstVarRef{flp, stateVarp, VAccess::WRITE},
                                  new AstConst{flp, static_cast<uint32_t>(nextState)}},
                    new AstAssign{flp, new AstVarRef{flp, cntVarp, VAccess::WRITE},
                                  new AstSub{flp, new AstVarRef{flp, cntVarp, VAccess::READ},
                                             new AstConst{flp, 1}}}};

                fsmChainp = chainState(flp, fsmChainp, stateVarp, waitState, bodyp);

            } else if (i == steps.size() - 1 && step.exprp) {
                // Tail: check final expression, pass or fail
                const int checkState = nextState++;
                AstNode* const passp = new AstAssign{
                    flp, new AstVarRef{flp, stateVarp, VAccess::WRITE}, new AstConst{flp, 0}};
                AstBegin* const failp = new AstBegin{flp, "", nullptr, true};
                failp->addStmtsp(new AstAssign{flp, new AstVarRef{flp, failVarp, VAccess::WRITE},
                                               new AstConst{flp, AstConst::BitTrue{}}});
                failp->addStmtsp(new AstAssign{flp, new AstVarRef{flp, stateVarp, VAccess::WRITE},
                                               new AstConst{flp, 0}});

                AstIf* const bodyp = new AstIf{
                    flp, new AstSampled{flp, step.exprp->cloneTree(false)}, passp, failp};

                fsmChainp = chainState(flp, fsmChainp, stateVarp, checkState, bodyp);
            }
        }

        // Build IDLE state (state 0): check trigger and start
        AstNode* idleBodyp = nullptr;
        const SeqStep& firstStep = steps[0];
        int initCnt = 0;
        if (firstStep.isRange) {
            initCnt = firstStep.rangeMin - 1;
        } else {
            initCnt = firstStep.delay - 1;
        }
        AstNode* const startActionp
            = makeStateTransition(flp, stateVarp, cntVarp, 1, initCnt < 0 ? 0 : initCnt);

        // Trigger = antecedent (from implication) AND/OR first step expression
        AstNodeExpr* triggerp = nullptr;
        if (antExprp && firstStep.exprp) {
            triggerp = new AstAnd{flp, new AstSampled{flp, antExprp->cloneTree(false)},
                                  new AstSampled{flp, firstStep.exprp->cloneTree(false)}};
        } else if (antExprp) {
            triggerp = new AstSampled{flp, antExprp->cloneTree(false)};
        } else if (firstStep.exprp) {
            triggerp = new AstSampled{flp, firstStep.exprp->cloneTree(false)};
        }

        if (triggerp) {
            triggerp->dtypeSetBit();
            idleBodyp = new AstIf{flp, triggerp, startActionp, nullptr};
        } else {
            // Unary form with no antecedent: start unconditionally each cycle
            idleBodyp = startActionp;
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
        AstVar* const cntVarp = new AstVar{flp, VVarType::MODULETEMP, baseName + "__cnt",
                                           nodep->findBasicDType(VBasicDTypeKwd::UINT32)};
        cntVarp->lifetime(VLifetime::STATIC_EXPLICIT);
        AstVar* const failVarp = new AstVar{flp, VVarType::MODULETEMP, baseName + "__fail",
                                            nodep->findBasicDType(VBasicDTypeKwd::BIT)};
        failVarp->lifetime(VLifetime::STATIC_EXPLICIT);

        // Build FSM body
        AstNode* const fsmBodyp
            = buildFsmBody(flp, stateVarp, cntVarp, failVarp, steps, sensesp, antExprp);

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

    void visit(AstSExprThroughout* nodep) override {
        // Reject throughout with range-delay sequences before FSM expansion
        // would silently lose per-tick enforcement (IEEE 1800-2023 16.9.9)
        if (AstSExpr* const sexprp = VN_CAST(nodep->seqp(), SExpr)) {
            if (containsRangeDelay(sexprp)) {
                nodep->v3warn(E_UNSUPPORTED, "Unsupported: throughout with range delay sequence");
                nodep->replaceWith(new AstConst{nodep->fileline(), AstConst::BitFalse{}});
                VL_DO_DANGLING(nodep->deleteTree(), nodep);
                return;
            }
        }
        // Reject throughout with nested throughout or goto repetition
        if (VN_IS(nodep->seqp(), SExprThroughout) || VN_IS(nodep->seqp(), SExprGotoRep)) {
            nodep->v3warn(E_UNSUPPORTED, "Unsupported: throughout with complex sequence operator");
            nodep->replaceWith(new AstConst{nodep->fileline(), AstConst::BitFalse{}});
            VL_DO_DANGLING(nodep->deleteTree(), nodep);
            return;
        }
        // Reject throughout with temporal SAnd/SOr (containing SExpr = multi-cycle).
        // Pure boolean SAnd/SOr are OK -- AssertPropLowerVisitor lowers them to LogAnd/LogOr.
        if (VN_IS(nodep->seqp(), SAnd) || VN_IS(nodep->seqp(), SOr)) {
            bool hasSExpr = false;
            nodep->seqp()->foreach([&](const AstSExpr*) { hasSExpr = true; });
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
