// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Transform sequences into properties
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2005-2025 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************
//  Properties steps:
//      Ensemble a property decision tree from sequence expressions.
//          Property decision tree is a tree rooted with source sequence
//          expression. It has a bipartite structure
//          (Expr -> Stmt -> Expr ...).
//      Transform property decision tree into AST, remove source sequence
//      expression
//          Each property is wrapped with AstPExpr that is transformed
//          further by V3AssertPre and V3Assert.
//
//*************************************************************************

#include "V3PchAstNoMT.h"  // VL_MT_DISABLED_CODE_UNIT

#include "V3AssertProperties.h"

#include "V3Graph.h"
#include "V3UniqueNames.h"

VL_DEFINE_DEBUG_FUNCTIONS;

namespace {

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
    // LCOV_EXCL_START // Debug code
    string name() const override VL_MT_STABLE {
        return cvtToHex(m_nodep) + "\\n " + cvtToStr(m_nodep->typeName()) + "\\n"s
               + m_nodep->fileline()->ascii();
    };
    string dotShape() const override {
        if (inEmpty()) return "tripleoctagon";
        if (outEmpty()) return "doubleoctagon";
        return "oval";
    }
    // LCOV_EXCL_STOP
    bool isStart() const { return inEmpty(); }
};

class StmtVertex final : public DfaVertex {
    VL_RTTI_IMPL(StmtVertex, V3GraphEdge)
public:
    // CONSTRUCTORS
    explicit StmtVertex(V3Graph* graphp, AstNodeStmt* stmtp) VL_MT_DISABLED
        : DfaVertex{graphp, stmtp} {}
    // LCOV_EXCL_START // Debug code
    string dotColor() const override { return "green"; }
    // LCOV_EXCL_STOP
};

class ExprVertex final : public DfaVertex {
    VL_RTTI_IMPL(ExprVertex, V3GraphEdge)
public:
    // CONSTRUCTORS
    explicit ExprVertex(V3Graph* graphp, AstNodeExpr* exprp) VL_MT_DISABLED
        : DfaVertex{graphp, exprp} {}
    // LCOV_EXCL_START // Debug code
    string dotColor() const override { return "blue"; }
    // LCOV_EXCL_STOP
};

class ConditionEdge final : public V3GraphEdge {
    VL_RTTI_IMPL(ConditionEdge, V3GraphEdge)
    // STATE
    const bool m_ifBranch;  // Whether this branch is taken for fulfilled condition

public:
    // CONSTRUCTORS
    explicit ConditionEdge(V3Graph* graphp, DfaVertex* fromp, DfaVertex* top,
                           bool ifBranch) VL_MT_DISABLED : V3GraphEdge{graphp, fromp, top, 1},
                                                           m_ifBranch{ifBranch} {}
    ~ConditionEdge() override = default;

    bool ifBranch() const { return m_ifBranch; }
    // LCOV_EXCL_START // Debug code
    string dotColor() const override { return m_ifBranch ? "green" : "red"; }
    // LCOV_EXCL_STOP
};

// Parse properties and ensemble a property tree graph
class AssertPropertiesParser final : public VNVisitorConst {
    // STATE
    std::unique_ptr<V3Graph> m_graphp = std::make_unique<V3Graph>();  // Property tree
    DfaVertex* m_lastp = nullptr;  // Last encountered vertex
    bool m_underSExpr
        = false;  // Whether it is under sequence expression for creating a start node
    size_t m_underLogNots = 0;  // Number of not operators before sequence

    // VISITORS
    void visit(AstNodeCoverOrAssert* nodep) override { iterateChildrenConst(nodep); }
    void visit(AstLogNot* nodep) override {
        VL_RESTORER(m_underLogNots);
        ++m_underLogNots;
        iterateChildrenConst(nodep);
    }
    void visit(AstSExpr* nodep) override {
        const auto makeClause = [this, nodep](bool pass) {
            return new StmtVertex{
                m_graphp.get(),
                new AstPExprClause{nodep->fileline(), m_underLogNots % 2 == 0 ? pass : !pass}};
        };

        if (VN_IS(nodep->exprp(), SExpr)) {
            VL_RESTORER(m_underSExpr);
            m_underSExpr = true;
            iterateConst(nodep->exprp());
        } else {
            ExprVertex* const exprVtxp
                = new ExprVertex{m_graphp.get(), nodep->exprp()->unlinkFrBack()};
            new ConditionEdge{m_graphp.get(), exprVtxp, makeClause(true), true};
            new ConditionEdge{m_graphp.get(), exprVtxp, makeClause(false), false};
            m_lastp = exprVtxp;
        }

        ExprVertex* const startp = m_underSExpr ? nullptr : new ExprVertex{m_graphp.get(), nodep};

        StmtVertex* const dlyVtxp
            = new StmtVertex{m_graphp.get(), nodep->delayp()->unlinkFrBack()};

        if (AstSExpr* const sexprp = VN_CAST(nodep->preExprp(), SExpr)) {
            UASSERT_OBJ(!sexprp->preExprp() && !VN_IS(sexprp->exprp(), SExpr), sexprp,
                        "Incorrect sexpr tree");
            StmtVertex* const sdlyVtxp
                = new StmtVertex{m_graphp.get(), sexprp->delayp()->unlinkFrBack()};
            ExprVertex* const exprVtxp
                = new ExprVertex{m_graphp.get(), sexprp->exprp()->unlinkFrBack()};

            if (startp) new ConditionEdge{m_graphp.get(), startp, sdlyVtxp, true};
            new ConditionEdge{m_graphp.get(), sdlyVtxp, exprVtxp, true};
            new ConditionEdge{m_graphp.get(), exprVtxp, dlyVtxp, true};
            new ConditionEdge{m_graphp.get(), dlyVtxp, m_lastp, true};
            new ConditionEdge{m_graphp.get(), exprVtxp, makeClause(false), false};

            // This case only occurs when multi-delay sequence starts with an expression,
            // don't set last as this is never a last expression.
        } else if (nodep->preExprp()) {
            ExprVertex* const preVtxp
                = new ExprVertex{m_graphp.get(), nodep->preExprp()->unlinkFrBack()};
            if (startp) new ConditionEdge{m_graphp.get(), startp, preVtxp, true};
            new ConditionEdge{m_graphp.get(), preVtxp, dlyVtxp, true};
            new ConditionEdge{m_graphp.get(), dlyVtxp, m_lastp, true};
            new ConditionEdge{m_graphp.get(), preVtxp, makeClause(false), false};
            m_lastp = preVtxp;
        } else {
            if (startp) new ConditionEdge{m_graphp.get(), startp, dlyVtxp, true};
            new ConditionEdge{m_graphp.get(), dlyVtxp, m_lastp, true};
            m_lastp = dlyVtxp;
        }
    }
    void visit(AstNode* nodep) override { iterateChildrenConst(nodep); }
    void visit(AstConstPool* nodep) override {}

public:
    // CONSTRUCTORS
    explicit AssertPropertiesParser(AstNetlist* nodep) {
        iterateConst(nodep);
        if (dumpGraphLevel() >= 6) m_graphp->dumpDotFilePrefixedAlways("properties", true);
    }
    std::unique_ptr<V3Graph> graphp() { return std::move(m_graphp); }
    ~AssertPropertiesParser() override = default;
};

// Transform property graph into AST
class AssertPropertiesTransformer final {
    // STATE
    V3UniqueNames m_assertCycleDelayNames{"__Vassert"};  // Names for assertion properties
    const std::unique_ptr<V3Graph> m_graph;  // Property tree
    AstPExpr* m_pexprp = nullptr;  // Currently built property sequence
    AstBegin* m_current = nullptr;  // Currently built block

    V3GraphVertex* processVtx(V3GraphVertex* vtxp) {
        if (StmtVertex* const stmtp = vtxp->cast<StmtVertex>()) return processVtx(stmtp);
        if (ExprVertex* const exprp = vtxp->cast<ExprVertex>()) return processVtx(exprp);
        // TODO use C++17 std::variant and std::visit
        // LCOV_EXCL_START
        assert(0);
        VL_UNREACHABLE;
        return nullptr;
        // LCOV_EXCL_STOP
    }
    V3GraphVertex* processVtx(StmtVertex* vtxp) {
        UASSERT_OBJ(!vtxp->isStart(), vtxp->nodep(),
                    "Starting node should be a property expression");
        UASSERT_OBJ(m_current, vtxp->nodep(), "Should be under a block");
        m_current->addStmtsp(vtxp->nodep());
        return processEdge(vtxp->outEdges().frontp());
    }
    V3GraphVertex* processVtx(ExprVertex* vtxp) {
        AstNode* const nodep = vtxp->nodep();
        if (vtxp->isStart()) {
            AstBegin* const bodyp = new AstBegin{
                nodep->fileline(), m_assertCycleDelayNames.get(nodep) + "__block", nullptr, true};
            m_pexprp = new AstPExpr{nodep->fileline(), bodyp, nodep->dtypep()};
            UASSERT_OBJ(vtxp->outSize1() && vtxp->outEdges().frontp()->is<ConditionEdge>(), nodep,
                        "Incorrect property graph");
            m_current = m_pexprp->bodyp();
            return processEdge(vtxp->outEdges().frontp());
        }
        UASSERT_OBJ(vtxp->outEdges().size() > 0 && vtxp->outEdges().size() <= 2, nodep,
                    "Incorrect edges");
        AstBegin* const passsp = new AstBegin{
            nodep->fileline(), m_assertCycleDelayNames.get(nodep) + "__block_pass", nullptr, true};
        AstNode* const failsp = [vtxp]() -> AstNode* {
            if (!vtxp->outSize1()) {
                V3GraphVertex* const failVtxp = vtxp->outEdges().backp()->top();
                return failVtxp->as<StmtVertex>()->nodep();
            }
            return nullptr;
        }();

        AstSampled* const sampledp
            = new AstSampled{nodep->fileline(), VN_AS(vtxp->nodep(), NodeExpr)};
        sampledp->dtypeFrom(vtxp->nodep());
        AstIf* const ifp = new AstIf{nodep->fileline(), sampledp, passsp, failsp};
        m_current->addStmtsp(ifp);
        m_current = passsp;
        return processEdge(vtxp->outEdges().frontp());
    }
    V3GraphVertex* processEdge(V3GraphEdge* edgep) {
        if (edgep) return processVtx(edgep->top());
        return nullptr;
    }

public:
    // CONSTRUCTORS
    explicit AssertPropertiesTransformer(std::unique_ptr<V3Graph> graph)
        : m_graph{std::move(graph)} {
        for (V3GraphVertex& vtx : m_graph->vertices()) {
            if (DfaVertex* const dVtxp = vtx.cast<ExprVertex>()) {
                if (dVtxp->isStart()) {
                    VL_RESTORER(m_pexprp);
                    processVtx(&vtx);
                    AstSExpr* const propp = VN_AS(dVtxp->nodep(), SExpr);
                    propp->replaceWith(m_pexprp);
                    propp->deleteTree();
                }
            }
        }
    }
};

}  //namespace

//######################################################################
// Top AssertProperties class

void V3AssertProperties::assertPropertiesAll(AstNetlist* nodep) {
    UINFO(2, __FUNCTION__ << ":");
    {
        std::unique_ptr<V3Graph> graphp = AssertPropertiesParser{nodep}.graphp();
        AssertPropertiesTransformer{std::move(graphp)};
    }
    V3Global::dumpCheckGlobalTree("assertproperties", 0, dumpTreeEitherLevel() >= 3);
}
