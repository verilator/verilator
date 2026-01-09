// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Implementation of assertion properties
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2005-2026 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
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

#include "V3Graph.h"

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
// Top AssertProp class

void V3AssertProp::assertPropAll(AstNetlist* nodep) {
    UINFO(2, __FUNCTION__ << ":");
    {
        V3Graph graph;
        { AssertPropBuildVisitor{nodep, graph}; }
        AssertPropTransformer{graph};
    }
    V3Global::dumpCheckGlobalTree("assertproperties", 0, dumpTreeEitherLevel() >= 3);
}
