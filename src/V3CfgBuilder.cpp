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

class CfgBuilder final : VNVisitorConst {
    // STATE
    // The graph being built, or nullptr if failed to build one
    std::unique_ptr<ControlFlowGraph> m_cfgp{new ControlFlowGraph};
    // Current basic block to add statements to
    BasicBlock* m_currBBp = nullptr;
    // Continuation block for given JumpBlock
    std::unordered_map<AstJumpBlock*, BasicBlock*> m_jumpBlockContp;

    // METHODS

    // Create new Basicblock block in the CFG
    BasicBlock& addBasicBlock() { return *new BasicBlock{m_cfgp.get()}; }

    // Create new taken (or unconditional) ControlFlowEdge in the CFG
    void addTakenEdge(BasicBlock& src, BasicBlock& dst) {
        UASSERT_OBJ(src.outEmpty(), &src, "Taken edge should be added first");
        new ControlFlowEdge{m_cfgp.get(), &src, &dst};
    }

    // Create new untaken ControlFlowEdge in the CFG
    void addUntknEdge(BasicBlock& src, BasicBlock& dst) {
        UASSERT_OBJ(src.outSize1(), &src, "Untaken edge shold be added second");
        UASSERT_OBJ(src.outEdges().frontp()->top() != &dst, &src,
                    "Untaken branch targets the same block as the taken branch");
        new ControlFlowEdge{m_cfgp.get(), &src, &dst};
    }

    // Add the given statement to the current BasicBlock
    void addStmt(AstNodeStmt* nodep) { m_currBBp->m_stmtps.emplace_back(nodep); }

    // Used to handle statements not representable in the CFG
    void nonRepresentable(AstNodeStmt*) {
        if (!m_cfgp) return;
        m_cfgp.reset();
    }

    // Used to handle simple (non-branching) statements in the CFG
    void simpleStatement(AstNodeStmt* nodep, bool representable = true) {
        if (!m_cfgp) return;
        // If non-representable, reset graph
        if (!representable) {
            m_cfgp.reset();
            return;
        }
        // Just add to current block
        addStmt(nodep);
    }

    // VISITORS

    // Eventually we should handle all procedural statements, however, what
    // is a procedural statemen is a bit unclear (#6280), so in the first
    // instance we will only handle select statemetns that cover the requied
    // use cases, and in the base case we conservatively assume the statement
    // is non-representable. More visits can be added case by case if needed.
    void visit(AstNode* nodep) override {
        if (!m_cfgp) return;
        UINFO(9, "Unhandled AstNode type " << nodep->typeName());
        m_cfgp.reset();
    }

    // Non-representable statements
    void visit(AstAssignDly* nodep) override { nonRepresentable(nodep); }
    void visit(AstCase* nodep) override { nonRepresentable(nodep); }  // V3Case will eliminate
    void visit(AstCReset* nodep) override { nonRepresentable(nodep); }
    void visit(AstDelay* nodep) override { nonRepresentable(nodep); }

    // Representable non control-flow statements
    void visit(AstAssign* nodep) override { simpleStatement(nodep, !nodep->timingControlp()); }
    void visit(AstComment*) override {}  // ignore entirely
    void visit(AstDisplay* nodep) override { simpleStatement(nodep); }
    void visit(AstFinish* nodep) override { simpleStatement(nodep); }
    void visit(AstStmtExpr* nodep) override { simpleStatement(nodep); }
    void visit(AstStop* nodep) override { simpleStatement(nodep); }

    // Representable control flow statements
    void visit(AstIf* nodep) override {
        if (!m_cfgp) return;

        // Add terminator statement to current block - semantically the condition check only ...
        addStmt(nodep);

        // Create then/else/continuation blocks
        BasicBlock& thenBB = addBasicBlock();
        BasicBlock& elseBB = addBasicBlock();
        BasicBlock& contBB = addBasicBlock();
        addTakenEdge(*m_currBBp, thenBB);
        addUntknEdge(*m_currBBp, elseBB);

        // Build then branch
        m_currBBp = &thenBB;
        iterateAndNextConstNull(nodep->thensp());
        if (!m_cfgp) return;
        if (m_currBBp) addTakenEdge(*m_currBBp, contBB);

        // Build else branch
        m_currBBp = &elseBB;
        iterateAndNextConstNull(nodep->elsesp());
        if (!m_cfgp) return;
        if (m_currBBp) addTakenEdge(*m_currBBp, contBB);

        // Set continuation
        m_currBBp = &contBB;
    }
    void visit(AstWhile* nodep) override {
        if (!m_cfgp) return;

        // Create the header block
        BasicBlock& headBB = addBasicBlock();
        addTakenEdge(*m_currBBp, headBB);

        // The While goes in the header block - semantically the condition check only ...
        m_currBBp = &headBB;
        addStmt(nodep);

        // Create the body/continuation blocks
        BasicBlock& bodyBB = addBasicBlock();
        BasicBlock& contBB = addBasicBlock();
        addTakenEdge(headBB, bodyBB);
        addUntknEdge(headBB, contBB);

        // Build the body
        m_currBBp = &bodyBB;
        iterateAndNextConstNull(nodep->stmtsp());
        iterateAndNextConstNull(nodep->incsp());
        if (!m_cfgp) return;
        if (m_currBBp) addTakenEdge(*m_currBBp, headBB);

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
        if (m_currBBp) addTakenEdge(*m_currBBp, contBB);

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
        addTakenEdge(*m_currBBp, *m_jumpBlockContp.at(nodep->blockp()));

        // There should be no statements after a JumpGo!
        m_currBBp = nullptr;
    }

    // CONSTRUCTOR
    explicit CfgBuilder(const AstNodeProcedure* nodep) {
        // Build the graph, starting from the entry block
        m_currBBp = &addBasicBlock();
        m_cfgp->m_enterp = m_currBBp;
        // Visit each statement to build the control flow graph
        iterateAndNextConstNull(nodep->stmtsp());
        if (!m_cfgp) return;
        // The final block is the exit block
        m_cfgp->m_exitp = m_currBBp;

        // Remove empty blocks - except enter/exit
        for (V3GraphVertex* const vtxp : m_cfgp->vertices().unlinkable()) {
            if (vtxp == &m_cfgp->enter()) continue;
            if (vtxp == &m_cfgp->exit()) continue;
            BasicBlock* const bbp = vtxp->as<BasicBlock>();
            if (!bbp->stmtps().empty()) continue;
            UASSERT(bbp->outSize1(), "Empty block should have a single successor");
            BasicBlock* const succp = const_cast<BasicBlock*>(bbp->takenSuccessorp());
            for (V3GraphEdge* const edgep : bbp->inEdges().unlinkable()) edgep->relinkTop(succp);
            vtxp->unlinkDelete(m_cfgp.get());
        }
        // Remove redundant entry block
        while (m_cfgp->enter().stmtps().empty() && m_cfgp->enter().outSize1()) {
            BasicBlock* const succp = m_cfgp->enter().outEdges().frontp()->top()->as<BasicBlock>();
            if (!succp->inSize1()) break;
            m_cfgp->m_enterp->unlinkDelete(m_cfgp.get());
            m_cfgp->m_enterp = succp;
        }
        // Remove redundant exit block
        while (m_cfgp->exit().stmtps().empty() && m_cfgp->exit().inSize1()) {
            BasicBlock* const prep = m_cfgp->exit().inEdges().frontp()->fromp()->as<BasicBlock>();
            if (!prep->outSize1()) break;
            m_cfgp->m_exitp->unlinkDelete(m_cfgp.get());
            m_cfgp->m_exitp = prep;
        }

        // Compute reverse post-order enumeration and sort blocks, assign IDs
        {
            // Simple recursive algorith will do ...
            std::vector<BasicBlock*> postOrderEnumeration;
            std::unordered_set<BasicBlock*> visited;
            const std::function<void(BasicBlock*)> visitBasicBlock = [&](BasicBlock* bbp) {
                // Mark and skip if already visited
                if (!visited.emplace(bbp).second) return;
                // Visit successors
                for (const V3GraphEdge& e : bbp->outEdges()) {
                    visitBasicBlock(static_cast<BasicBlock*>(e.top()));
                }
                // Add to post order enumeration
                postOrderEnumeration.emplace_back(bbp);
            };
            visitBasicBlock(m_cfgp->m_enterp);
            const uint32_t n = postOrderEnumeration.size();
            UASSERT_OBJ(n == m_cfgp->vertices().size(), nodep, "Inconsistent enumeration size");

            // Set size in graph
            m_cfgp->m_nBasicBlocks = n;

            // Assign ids equal to the reverse post order number and sort vertices
            for (uint32_t i = 0; i < postOrderEnumeration.size(); ++i) {
                BasicBlock* const bbp = postOrderEnumeration[n - 1 - i];
                bbp->user(i);
                m_cfgp->vertices().unlink(bbp);
                m_cfgp->vertices().linkBack(bbp);
            }
        }

        // Assign IDs to edges
        {
            size_t nEdges = 0;
            for (V3GraphVertex& v : m_cfgp->vertices()) {
                for (V3GraphEdge& e : v.outEdges()) e.user(nEdges++);
            }
            // Set size in graph
            m_cfgp->m_nEdges = nEdges;
        }

        if (dumpGraphLevel() >= 9) m_cfgp->dumpDotFilePrefixed("cfgbuilder");
    }

public:
    static std::unique_ptr<ControlFlowGraph> apply(const AstNodeProcedure* nodep) {
        return std::move(CfgBuilder{nodep}.m_cfgp);
    }
};

std::unique_ptr<const ControlFlowGraph> V3Cfg::build(const AstNodeProcedure* nodep) {
    return CfgBuilder::apply(nodep);
}
