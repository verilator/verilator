// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Control flow graph (CFG) builder
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2025 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************
//
// Control flow graph (CFG) builder
//
//*************************************************************************

#include "config_build.h"
#include "verilatedos.h"

#include "V3Ast.h"
#include "V3Cfg.h"
#include "V3EmitV.h"

#include <deque>
#include <unordered_map>
#include <unordered_set>

VL_DEFINE_DEBUG_FUNCTIONS;

class CFGBuilder final : VNVisitorConst {
    using EdgeKind = ControlFlowGraphEdge::Kind;

    // STATE
    // The graph being built, or nullptr if failed to build one
    std::unique_ptr<ControlFlowGraph> m_cfgp{new ControlFlowGraph};
    BasicBlock* m_currBBp = nullptr;  // Current basic block to add statements to
    // Continuation block for given JumpBlock
    std::unordered_map<AstJumpBlock*, BasicBlock*> m_jumpBlockContp;

    // METHODS
    BasicBlock& addBasicBlock() { return *new BasicBlock{m_cfgp.get(), false, false}; }

    void addEdge(BasicBlock& src, BasicBlock& dst, EdgeKind kind) {
        // A block can have at most 2 out edges. We are adding one now, so there should be 0 or 1.
        UASSERT(src.outEmpty() || src.outSize1(), "Too many out edges from block");
        // Shouldn't be adding multiple edges pointing to the same successor block.
        UASSERT(src.outEmpty() || src.outEdges().frontp()->top() != &dst,
                "Adding duplicate edge to ControlFlowGraph");
        new ControlFlowGraphEdge{m_cfgp.get(), &src, &dst, kind};
    }

    void nonRepresentable() {
        if (!m_cfgp) return;
        m_cfgp.reset();
    }

    void simpleStatement(AstNode* nodep, bool representable = true) {
        if (!m_cfgp) return;
        // If non-representable, reset graph
        if (!representable) {
            m_cfgp.reset();
            return;
        }
        // Just add to current block
        m_currBBp->stmtps().emplace_back(nodep);
    }

    // VISITORS

    // Base case, conservatively assume non-representable
    void visit(AstNode* nodep) override {
        if (!m_cfgp) return;
        UINFO(9, "Unhandled AstNode type " << nodep->typeName());
        m_cfgp.reset();
    }

    // Representable control flow statements
    void visit(AstIf* nodep) override {
        if (!m_cfgp) return;

        // Add terminator statement to current block - semantically the condition check only ...
        m_currBBp->stmtps().emplace_back(nodep);

        // Create then/else/continuation blocks
        BasicBlock& thenBB = addBasicBlock();
        BasicBlock& elseBB = addBasicBlock();
        BasicBlock& contBB = addBasicBlock();
        addEdge(*m_currBBp, thenBB, EdgeKind::ConditionTrue);
        addEdge(*m_currBBp, elseBB, EdgeKind::ConditionFalse);

        // Build then branch
        m_currBBp = &thenBB;
        iterateAndNextConstNull(nodep->thensp());
        if (!m_cfgp) return;
        if (m_currBBp) addEdge(*m_currBBp, contBB, EdgeKind::Jump);

        // Build else branch
        m_currBBp = &elseBB;
        iterateAndNextConstNull(nodep->elsesp());
        if (!m_cfgp) return;
        if (m_currBBp) addEdge(*m_currBBp, contBB, EdgeKind::Jump);

        // Set continuation
        m_currBBp = &contBB;
    }
    void visit(AstWhile* nodep) override {
        if (!m_cfgp) return;

        // Create header/body/continuation blocks
        BasicBlock& headBB = addBasicBlock();
        BasicBlock& bodyBB = addBasicBlock();
        BasicBlock& contBB = addBasicBlock();
        addEdge(*m_currBBp, headBB, EdgeKind::Jump);
        addEdge(headBB, bodyBB, EdgeKind::ConditionTrue);
        addEdge(headBB, contBB, EdgeKind::ConditionFalse);

        // The While goes in the header block - semantically the condition check only ...
        headBB.stmtps().emplace_back(nodep);

        // Build the body
        m_currBBp = &bodyBB;
        iterateAndNextConstNull(nodep->stmtsp());
        iterateAndNextConstNull(nodep->incsp());
        if (!m_cfgp) return;
        if (m_currBBp) addEdge(*m_currBBp, headBB, EdgeKind::Jump);

        // Set continuation
        m_currBBp = &contBB;
    }
    void visit(AstJumpBlock* nodep) override {
        if (!m_cfgp) return;

        // Don't acutally need to add this 'nodep' to any block - but we could later if needed

        // Create continuation block
        BasicBlock& contBB = addBasicBlock();
        const bool newEntry = m_jumpBlockContp.emplace(nodep, &contBB).second;
        UASSERT_OBJ(newEntry, nodep, "AstJumpBlock visited twice");

        // Build the body
        iterateAndNextConstNull(nodep->stmtsp());
        if (!m_cfgp) return;
        if (m_currBBp) addEdge(*m_currBBp, contBB, EdgeKind::Jump);

        // Set continuation
        m_currBBp = &contBB;
    }
    void visit(AstJumpGo* nodep) override {
        if (!m_cfgp) return;

        // Non-representable if not last in statement list (V3Const will fix this later)
        if (nodep->nextp()) {
            m_cfgp.reset();
            return;
        }

        // Don't acutally need to add this 'nodep' to any block - but we could later if needed

        // Make current block go to the continuation of the JumpBlock
        addEdge(*m_currBBp, *m_jumpBlockContp.at(nodep->blockp()), EdgeKind::Jump);

        // There should be no statements after a JumpGo!
        m_currBBp = nullptr;
    }

    // Representable non control-flow statements
    void visit(AstAssign* nodep) override { simpleStatement(nodep, !nodep->timingControlp()); }
    void visit(AstComment*) override {}  // ignore entirely
    void visit(AstDisplay* nodep) override { simpleStatement(nodep); }
    void visit(AstFinish* nodep) override { simpleStatement(nodep); }
    void visit(AstStmtExpr* nodep) override { simpleStatement(nodep); }
    void visit(AstStop* nodep) override { simpleStatement(nodep); }

    // Non-representable nodes
    void visit(AstAssignDly* nodep) override { nonRepresentable(); }
    void visit(AstCase* nodep) override { nonRepresentable(); }  // V3Case will eliminate
    void visit(AstCReset* nodep) override { nonRepresentable(); }
    void visit(AstDelay* nodep) override { nonRepresentable(); }

    // CONSTRUCTOR
    CFGBuilder(const AstNodeProcedure* nodep) {
        // Build the graph, starting from the entry block
        m_currBBp = &addBasicBlock();
        addEdge(m_cfgp->enter(), *m_currBBp, EdgeKind::Jump);
        // Visit each statement to build the control flow graph
        iterateAndNextConstNull(nodep->stmtsp());
        if (!m_cfgp) return;
        // Make final block go to the exit block
        addEdge(*m_currBBp, m_cfgp->exit(), EdgeKind::Jump);

        // Remove empty blocks - except enter/exit
        for (V3GraphVertex* const vtxp : m_cfgp->vertices().unlinkable()) {
            if (vtxp == &m_cfgp->enter()) continue;
            if (vtxp == &m_cfgp->exit()) continue;
            BasicBlock* const bbp = vtxp->as<BasicBlock>();
            if (!bbp->stmtps().empty()) continue;
            UASSERT(bbp->outSize1(), "Empty block should have a single successor");
            BasicBlock* const succp = bbp->outEdges().frontp()->top()->as<BasicBlock>();
            for (V3GraphEdge* const edgep : bbp->inEdges().unlinkable()) edgep->relinkTop(succp);
            vtxp->unlinkDelete(m_cfgp.get());
        }
        // Remove redundant entry block
        while (m_cfgp->enter().stmtps().empty() && m_cfgp->enter().outSize1()) {
            BasicBlock* const succp = m_cfgp->enter().outEdges().frontp()->top()->as<BasicBlock>();
            if (!succp->inSize1()) break;
            succp->m_isEnter = true;
            m_cfgp->m_enterp->unlinkDelete(m_cfgp.get());
            m_cfgp->m_enterp = succp;
        }
        // Remove redundant exit block
        while (m_cfgp->exit().stmtps().empty() && m_cfgp->exit().inSize1()) {
            BasicBlock* const prep = m_cfgp->exit().inEdges().frontp()->fromp()->as<BasicBlock>();
            if (!prep->outSize1()) break;
            prep->m_isExit = true;
            m_cfgp->m_exitp->unlinkDelete(m_cfgp.get());
            m_cfgp->m_exitp = prep;
        }

        // Compute reverse post order enumeration and sort blocks
        {
            // Simple recursive algorith will do ...
            std::vector<BasicBlock*> postOrderEnumeration;
            std::unordered_set<BasicBlock*> visited;
            const std::function<void(BasicBlock&)> visit = [&](BasicBlock& bb) -> void {
                // Mark and skip if already visited
                if (!visited.emplace(&bb).second) return;
                // Visit all successors
                for (const V3GraphEdge& edge : bb.outEdges()) visit(*edge.top()->as<BasicBlock>());
                // Add to post order enumeration
                postOrderEnumeration.emplace_back(&bb);
            };
            visit(m_cfgp->enter());
            const uint32_t n = postOrderEnumeration.size();
            UASSERT_OBJ(n == m_cfgp->vertices().size(), nodep, "Inconsisted enumeration size");

            // Set size of graph
            m_cfgp->m_size = n;

            // Assign ids equal to the reverse post order number and sort vertices
            for (uint32_t i = 0; i < postOrderEnumeration.size(); ++i) {
                BasicBlock* const bbp = postOrderEnumeration[n - 1 - i];
                bbp->m_id = i;
                m_cfgp->vertices().unlink(bbp);
                m_cfgp->vertices().linkBack(bbp);
            }
        }

        if (dumpGraphLevel() >= 9) m_cfgp->dumpDotFilePrefixed("cfgbuilder");
    }

public:
    static std::unique_ptr<ControlFlowGraph> apply(const AstNodeProcedure* nodep) {
        return std::move(CFGBuilder{nodep}.m_cfgp);
    }
};

std::unique_ptr<const ControlFlowGraph> V3Cfg::build(const AstNodeProcedure* nodep) {
    return CFGBuilder::apply(nodep);
}
