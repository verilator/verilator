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
// Expands ##[M:N] range delays by replacing the containing SExpr tree
// with a PExpr that implements the range semantics as an if/delay chain.
// The DFA builder never sees range delays.

class RangeDelayExpander final : public VNVisitor {
    // STATE
    V3UniqueNames m_names{"__Vrangedly"};

    // Linearize an SExpr tree into sequence steps.
    // Returns steps in evaluation order: [(expr, delay, isRange, min, max), ...]
    // The final expression (tail) has delay=0.
    struct SeqStep {
        AstNodeExpr* exprp;  // Expression to check (nullptr if unary leading delay)
        int delay;  // Fixed delay after this expression (0 for tail)
        bool isRange;  // Whether this step's delay is a range
        int rangeMin;
        int rangeMax;
    };

    // Validate and extract delay bounds. Sets minVal/maxVal. Returns false on error.
    bool extractDelayBounds(AstDelay* dlyp, bool& isRange, int& minVal, int& maxVal) {
        isRange = dlyp->isRangeDelay();
        if (isRange) {
            AstNodeExpr* minExprp = V3Const::constifyEdit(dlyp->lhsp()->cloneTree(false));
            AstNodeExpr* maxExprp = V3Const::constifyEdit(dlyp->rhsp()->cloneTree(false));
            const AstConst* const minConstp = VN_CAST(minExprp, Const);
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
            AstNodeExpr* const valp = V3Const::constifyEdit(dlyp->lhsp()->cloneTree(false));
            const AstConst* const constp = VN_CAST(valp, Const);
            minVal = maxVal = constp ? constp->toSInt() : 0;
            VL_DO_DANGLING(valp->deleteTree(), valp);
        }
        return true;
    }

    // Linearize an SExpr tree into steps.
    // Tree structure: SExpr can have preExprp as SExpr (for multi-step from left)
    // or exprp as SExpr (for chained sequences from right).
    //
    // Example: (##[1:2] b) ##1 c → SExpr(pre=SExpr(##[1:2], b), ##1, c)
    //   → steps: [{nullptr, range[1:2]}, {b, delay=1}, {c, delay=0}]
    //
    // Example: a ##[1:2] (b ##1 c) → SExpr(a, ##[1:2], SExpr(b, ##1, c))
    //   → steps: [{a, range[1:2]}, {b, delay=1}, {c, delay=0}]
    bool linearize(AstSExpr* rootp, std::vector<SeqStep>& steps) {
        bool hasRange = false;
        linearizeImpl(rootp, steps, hasRange);
        return hasRange;
    }

    bool linearizeImpl(AstSExpr* curp, std::vector<SeqStep>& steps, bool& hasRange) {
        // If preExprp is an SExpr, linearize it first (handles left-recursive structure)
        if (AstSExpr* const prep = VN_CAST(curp->preExprp(), SExpr)) {
            if (!linearizeImpl(prep, steps, hasRange)) return false;
        }

        // Extract this node's delay
        AstDelay* const dlyp = VN_CAST(curp->delayp(), Delay);
        UASSERT_OBJ(dlyp, curp, "Expected AstDelay");
        bool isRange = false;
        int minVal = 0, maxVal = 0;
        if (!extractDelayBounds(dlyp, isRange, minVal, maxVal)) return false;
        if (isRange) hasRange = true;

        // Add pre-expression step (if binary and preExprp is a simple expression)
        if (curp->preExprp() && !VN_IS(curp->preExprp(), SExpr)) {
            steps.push_back({curp->preExprp(), minVal, isRange, minVal, maxVal});
        } else {
            // Unary form or preExprp was SExpr (already linearized above)
            // The delay is between the last step from preExprp and the exprp
            steps.push_back({nullptr, minVal, isRange, minVal, maxVal});
        }

        // Handle exprp
        if (AstSExpr* const nextp = VN_CAST(curp->exprp(), SExpr)) {
            return linearizeImpl(nextp, steps, hasRange);
        } else {
            // Tail expression
            steps.push_back({curp->exprp(), 0, false, 0, 0});
            return true;
        }
    }

    // Build the continuation PExpr body for steps[idx..end]
    //
    // Each step has (expr, delay). The semantics are:
    //   step[idx]: check expr, then wait delay cycles, then continue to step[idx+1]
    //   For range delay steps: wait rangeMin, check next expr, if fail retry
    //     up to rangeMax cycles, then continue with the rest
    //
    // For range delay at step[idx], the checked expression is step[idx+1].exprp,
    // and on success the continuation is delay(step[idx+1].delay) → steps[idx+2..end].
    AstNode* buildContinuation(FileLine* flp, const std::vector<SeqStep>& steps, size_t idx) {
        if (idx >= steps.size()) return new AstPExprClause{flp, true};

        const SeqStep& step = steps[idx];

        if (step.delay == 0 && !step.isRange) {
            // Tail expression: if (expr) PASS else FAIL
            if (step.exprp) {
                return new AstIf{flp, new AstSampled{flp, step.exprp->cloneTree(false)},
                                 new AstPExprClause{flp, true}, new AstPExprClause{flp, false}};
            }
            return new AstPExprClause{flp, true};
        }

        if (step.isRange) {
            // Range delay at step[idx]:
            //   1. Check step[idx].exprp (if present, i.e. binary form)
            //   2. Wait rangeMin cycles
            //   3. Check step[idx+1].exprp — if pass, go to after-pass continuation
            //      If fail, wait 1 cycle and retry, up to rangeWidth times
            //   4. After-pass continuation = delay(step[idx+1].delay) + steps[idx+2..end]
            UASSERT(idx + 1 < steps.size(), "Range delay must have next step");
            const SeqStep& nextStep = steps[idx + 1];

            // Build after-pass: what happens after the range check succeeds
            AstNode* afterPassp = buildContinuation(flp, steps, idx + 2);
            if (nextStep.delay > 0) {
                AstBegin* const wrapperp = new AstBegin{flp, "", nullptr, true};
                wrapperp->addStmtsp(makeCycleDelay(flp, nextStep.delay));
                wrapperp->addStmtsp(afterPassp);
                afterPassp = wrapperp;
            }

            // Build check chain from innermost to outermost
            AstNode* chainp = nullptr;
            const int rangeWidth = step.rangeMax - step.rangeMin;
            for (int i = rangeWidth; i >= 0; --i) {
                AstNode* const passBranchp = (i == 0) ? afterPassp : afterPassp->cloneTree(false);
                if (i == rangeWidth) {
                    chainp = new AstIf{flp, new AstSampled{flp, nextStep.exprp->cloneTree(false)},
                                       passBranchp, new AstPExprClause{flp, false}};
                } else {
                    AstBegin* const retryBlock = new AstBegin{flp, "", nullptr, true};
                    retryBlock->addStmtsp(makeCycleDelay(flp, 1));
                    retryBlock->addStmtsp(chainp);
                    chainp = new AstIf{flp, new AstSampled{flp, nextStep.exprp->cloneTree(false)},
                                       passBranchp, retryBlock};
                }
            }

            // Add initial delay(rangeMin) before the check chain
            AstBegin* const blockp = new AstBegin{flp, "", nullptr, true};
            if (step.rangeMin > 0) blockp->addStmtsp(makeCycleDelay(flp, step.rangeMin));
            blockp->addStmtsp(chainp);

            // Wrap with pre-expression check if present
            if (step.exprp) {
                return new AstIf{flp, new AstSampled{flp, step.exprp->cloneTree(false)}, blockp,
                                 new AstPExprClause{flp, false}};
            }
            return blockp;
        } else {
            // Fixed delay: check expr, delay(N), then continue
            AstNode* const continuationp = buildContinuation(flp, steps, idx + 1);
            AstBegin* const blockp = new AstBegin{flp, "", nullptr, true};
            if (step.delay > 0) blockp->addStmtsp(makeCycleDelay(flp, step.delay));
            blockp->addStmtsp(continuationp);
            if (step.exprp) {
                return new AstIf{flp, new AstSampled{flp, step.exprp->cloneTree(false)}, blockp,
                                 new AstPExprClause{flp, false}};
            }
            return blockp;
        }
    }

    AstNode* wrapWithDelay(FileLine* flp, int cycles, AstNode* stmtp) {
        if (cycles > 0) {
            AstBegin* const blockp = new AstBegin{flp, "", nullptr, true};
            blockp->addStmtsp(makeCycleDelay(flp, cycles));
            blockp->addStmtsp(stmtp);
            return blockp;
        }
        return stmtp;
    }

    AstDelay* makeCycleDelay(FileLine* flp, int cycles) {
        return new AstDelay{flp, new AstConst{flp, static_cast<uint32_t>(cycles)}, true};
    }

    // Check if an SExpr tree contains any range delays (checks both exprp and preExprp chains)
    static bool containsRangeDelay(AstSExpr* nodep) {
        // Check this node's delay
        if (AstDelay* const dlyp = VN_CAST(nodep->delayp(), Delay)) {
            if (dlyp->isRangeDelay()) return true;
        }
        // Recurse into preExprp (may be SExpr with range delay)
        if (AstSExpr* const prep = VN_CAST(nodep->preExprp(), SExpr)) {
            if (containsRangeDelay(prep)) return true;
        }
        // Recurse into exprp (multi-step chain)
        if (AstSExpr* const exprp = VN_CAST(nodep->exprp(), SExpr)) {
            if (containsRangeDelay(exprp)) return true;
        }
        return false;
    }

    // VISITORS
    void visit(AstSExpr* nodep) override {
        // Only process top-level SExprs that contain range delays
        if (!containsRangeDelay(nodep)) {
            iterateChildren(nodep);
            return;
        }
        // Skip nested SExprs — the outermost SExpr containing a range delay
        // handles the entire tree via linearization
        if (AstSExpr* const parentp = VN_CAST(nodep->backp(), SExpr)) {
            if (parentp->exprp() == nodep || parentp->preExprp() == nodep) {
                // Don't iterate children — parent will linearize the full tree
                return;
            }
        }

        std::vector<SeqStep> steps;
        if (!linearize(nodep, steps)) {
            // Error in range validation — replace with constant to prevent crash
            nodep->replaceWith(new AstConst{nodep->fileline(), AstConst::BitFalse{}});
            VL_DO_DANGLING(nodep->deleteTree(), nodep);
            return;
        }

        FileLine* const flp = nodep->fileline();
        AstNode* const bodyContentp = buildContinuation(flp, steps, 0);
        AstBegin* const bodyp = new AstBegin{flp, "", nullptr, true};
        bodyp->addStmtsp(bodyContentp);
        AstPExpr* const pexprp = new AstPExpr{flp, bodyp, nodep->dtypep()};
        nodep->replaceWith(pexprp);
        VL_DO_DANGLING(nodep->deleteTree(), nodep);
    }
    void visit(AstNode* nodep) override { iterateChildren(nodep); }

public:
    explicit RangeDelayExpander(AstNetlist* nodep) { iterate(nodep); }
};

//######################################################################
// Top AssertProp class

void V3AssertProp::assertPropAll(AstNetlist* nodep) {
    UINFO(2, __FUNCTION__ << ":");
    { RangeDelayExpander{nodep}; }
    {
        V3Graph graph;
        { AssertPropBuildVisitor{nodep, graph}; }
        AssertPropTransformer{graph};
    }
    V3Global::dumpCheckGlobalTree("assertproperties", 0, dumpTreeEitherLevel() >= 3);
}
