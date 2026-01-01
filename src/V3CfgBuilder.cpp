// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Control flow graph (CFG) builder
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

class CfgBuilder final : public VNVisitorConst {
    // STATE
    // The graph being built, or nullptr if failed to build one
    std::unique_ptr<CfgGraph> m_cfgp{new CfgGraph};
    // Current basic block to add statements to
    CfgBlock* m_currBBp = nullptr;
    // Continuation block for given JumpBlock
    std::unordered_map<AstJumpBlock*, CfgBlock*> m_jumpBlockContp;
    // Continuation block for given Loop
    std::unordered_map<AstLoop*, CfgBlock*> m_loopContp;

    // METHODS

    // Add the given statement to the current CfgBlock
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
    void visit(AstAssignW* nodep) override { simpleStatement(nodep, !nodep->timingControlp()); }
    void visit(AstComment*) override {}  // ignore entirely
    void visit(AstDisplay* nodep) override { simpleStatement(nodep); }
    void visit(AstFinish* nodep) override { simpleStatement(nodep); }
    void visit(AstFinishFork* nodep) override { simpleStatement(nodep); }
    void visit(AstStmtExpr* nodep) override { simpleStatement(nodep); }
    void visit(AstStop* nodep) override { simpleStatement(nodep); }

    // Representable control flow statements
    void visit(AstIf* nodep) override {
        if (!m_cfgp) return;

        // Add terminator statement to current block - semantically the condition check only ...
        addStmt(nodep);

        // Create then/else/continuation blocks
        CfgBlock* const thenBBp = m_cfgp->addBlock();
        CfgBlock* const elseBBp = m_cfgp->addBlock();
        CfgBlock* const contBBp = m_cfgp->addBlock();
        m_cfgp->addTakenEdge(m_currBBp, thenBBp);
        m_cfgp->addUntknEdge(m_currBBp, elseBBp);

        // Build then branch
        m_currBBp = thenBBp;
        iterateAndNextConstNull(nodep->thensp());
        if (!m_cfgp) return;
        if (m_currBBp) m_cfgp->addTakenEdge(m_currBBp, contBBp);

        // Build else branch
        m_currBBp = elseBBp;
        iterateAndNextConstNull(nodep->elsesp());
        if (!m_cfgp) return;
        if (m_currBBp) m_cfgp->addTakenEdge(m_currBBp, contBBp);

        // Set continuation
        m_currBBp = contBBp;
    }
    void visit(AstLoop* nodep) override {
        UASSERT_OBJ(!nodep->contsp(), nodep, "'contsp' only used before LinkJump");
        if (!m_cfgp) return;

        // Don't acutally need to add this 'nodep' to any block

        // Create continuation block
        CfgBlock* const contBBp = m_cfgp->addBlock();
        const bool newEntry = m_loopContp.emplace(nodep, contBBp).second;
        UASSERT_OBJ(newEntry, nodep, "AstLoop visited twice");

        // Create the body block
        CfgBlock* const bodyBBp = m_cfgp->addBlock();
        m_cfgp->addTakenEdge(m_currBBp, bodyBBp);

        // Build the body
        m_currBBp = bodyBBp;
        iterateAndNextConstNull(nodep->stmtsp());
        if (!m_cfgp) return;
        if (m_currBBp) m_cfgp->addTakenEdge(m_currBBp, bodyBBp);

        // Set continuation
        m_currBBp = contBBp;
    }
    void visit(AstLoopTest* nodep) override {
        if (!m_cfgp) return;

        // Add terminator statement to current block - semantically the condition check only ...
        addStmt(nodep);

        // Create continuation blocks
        CfgBlock* const contBBp = m_cfgp->addBlock();
        m_cfgp->addTakenEdge(m_currBBp, contBBp);
        m_cfgp->addUntknEdge(m_currBBp, m_loopContp.at(nodep->loopp()));

        // Set continuation
        m_currBBp = contBBp;
    }
    void visit(AstJumpBlock* nodep) override {
        if (!m_cfgp) return;

        // Don't acutally need to add this 'nodep' to any block

        // Create continuation block
        CfgBlock* const contBBp = m_cfgp->addBlock();
        const bool newEntry = m_jumpBlockContp.emplace(nodep, contBBp).second;
        UASSERT_OBJ(newEntry, nodep, "AstJumpBlock visited twice");

        // Build the body
        iterateAndNextConstNull(nodep->stmtsp());
        if (!m_cfgp) return;
        if (m_currBBp) m_cfgp->addTakenEdge(m_currBBp, contBBp);

        // Set continuation
        m_currBBp = contBBp;
    }
    void visit(AstJumpGo* nodep) override {
        if (!m_cfgp) return;

        // Non-representable if not last in statement list (V3Const will fix this later)
        if (nodep->nextp()) {
            m_cfgp.reset();
            return;
        }

        // Don't acutally need to add this 'nodep' to any block

        // Make current block go to the continuation of the JumpBlock
        m_cfgp->addTakenEdge(m_currBBp, m_jumpBlockContp.at(nodep->blockp()));

        // There should be no statements after a JumpGo!
        m_currBBp = nullptr;
    }

    // CONSTRUCTOR
    explicit CfgBuilder(AstNode* stmtsp) {
        // Build the graph, starting from the entry block
        m_currBBp = m_cfgp->addBlock();
        m_cfgp->m_enterp = m_currBBp;
        // Visit each statement to build the control flow graph
        iterateAndNextConstNull(stmtsp);
        // If failed, stop now
        if (!m_cfgp) return;
        // The final block is the exit block
        m_cfgp->m_exitp = m_currBBp;
        // Some blocks might not have predecessors if they are unreachable, remove them
        {
            std::vector<V3GraphVertex*> unreachableps;
            for (V3GraphVertex* const vtxp : m_cfgp->vertices().unlinkable()) {
                if (vtxp == m_cfgp->m_enterp) continue;
                if (vtxp == m_cfgp->m_exitp) continue;
                UASSERT_OBJ(!vtxp->outEmpty(), vtxp, "Block with no successor other than exit");
                if (vtxp->inEmpty()) unreachableps.emplace_back(vtxp);
            }
            while (!unreachableps.empty()) {
                V3GraphVertex* const vtxp = unreachableps.back();
                unreachableps.pop_back();
                for (const V3GraphEdge& edge : vtxp->outEdges()) {
                    --m_cfgp->m_nEdges;
                    if (edge.top()->inSize1()) unreachableps.emplace_back(edge.top());
                }
                --m_cfgp->m_nBlocks;
                VL_DO_DANGLING(vtxp->unlinkDelete(m_cfgp.get()), vtxp);
            }
        }
        // Dump the initial graph
        if (dumpGraphLevel() >= 9) {
            m_cfgp->rpoBlocks();
            m_cfgp->dumpDotFilePrefixed("cfg-builder-initial");
        }
        // Minimize it
        m_cfgp->minimize();
        // Dump the final graph
        if (dumpGraphLevel() >= 8) m_cfgp->dumpDotFilePrefixed("cfg-builder");
    }

public:
    static std::unique_ptr<CfgGraph> apply(AstNode* stmtsp) {
        return std::move(CfgBuilder{stmtsp}.m_cfgp);
    }
};

std::unique_ptr<CfgGraph> CfgGraph::build(AstNode* stmtsp) { return CfgBuilder::apply(stmtsp); }
