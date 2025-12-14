// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Inline small CFuncs into their callers
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
// V3InlineCfuncs's Transformations:
//
// For each CCall to a small CFunc:
//   - Check if function is eligible for inlining (small, no locals, no $c())
//   - Replace CCall with cloned function body statements
//   - Mark inlined functions for later deletion
//
//*************************************************************************

#include "V3PchAstNoMT.h"  // VL_MT_DISABLED_CODE_UNIT

#include "V3InlineCfuncs.h"

#include "V3Stats.h"

#include <unordered_set>

VL_DEFINE_DEBUG_FUNCTIONS;

//######################################################################

class InlineCfuncsVisitor final : public VNVisitor {
    // STATE
    VDouble0 m_statInlined;  // Statistic tracking
    const int m_threshold;  // Inlining threshold from options
    std::unordered_set<AstCFunc*> m_inlinedFuncs;  // Functions that were inlined

    // METHODS

    // Check if a function contains any $c() calls (user or internal)
    static bool containsCStatements(AstCFunc* cfuncp) {
        bool found = false;
        // Check for internal C statements/expressions
        cfuncp->foreach([&](const AstCStmt*) { found = true; });
        if (!found) cfuncp->foreach([&](const AstCExpr*) { found = true; });
        // Check for user $c() statements/expressions
        if (!found) cfuncp->foreach([&](const AstCStmtUser*) { found = true; });
        if (!found) cfuncp->foreach([&](const AstCExprUser*) { found = true; });
        return found;
    }

    // Check if function has local variables
    static bool hasLocalVars(AstCFunc* cfuncp) {
        for (AstNode* nodep = cfuncp->stmtsp(); nodep; nodep = nodep->nextp()) {
            if (VN_IS(nodep, Var)) return true;
        }
        return false;
    }

    // Check if a function is eligible for inlining
    bool isInlineable(AstCFunc* cfuncp) {
        // Check size
        const size_t funcSize = cfuncp->nodeCount();
        if (funcSize > static_cast<size_t>(m_threshold)) return false;

        // Check for local variables
        if (hasLocalVars(cfuncp)) return false;

        // Check for $c() calls that might use 'this'
        if (containsCStatements(cfuncp)) return false;

        // Check it's a void function (not a coroutine)
        if (cfuncp->rtnTypeVoid() != "void") return false;

        // Don't inline functions marked dontCombine (e.g. trace, entryPoint)
        if (cfuncp->dontCombine()) return false;

        // Must have statements to inline
        if (!cfuncp->stmtsp()) return false;

        return true;
    }

    // VISITORS
    void visit(AstCCall* nodep) override {
        iterateChildren(nodep);

        AstCFunc* const cfuncp = nodep->funcp();
        if (!cfuncp) return;

        if (!isInlineable(cfuncp)) return;

        UINFO(6, "Inlining CFunc call: " << nodep << " -> " << cfuncp << endl);
        ++m_statInlined;

        // Clone the function body
        AstNode* const bodyp = cfuncp->stmtsp()->cloneTree(true);

        // Get the statement containing this call
        AstNode* stmtp = nodep;
        while (stmtp && !VN_IS(stmtp->backp(), NodeStmt) && !VN_IS(stmtp->backp(), CFunc)) {
            stmtp = stmtp->backp();
        }

        if (AstStmtExpr* const stmtExprp = VN_CAST(stmtp, StmtExpr)) {
            // Replace the statement with the inlined body
            stmtExprp->addNextHere(bodyp);
            VL_DO_DANGLING(stmtExprp->unlinkFrBack()->deleteTree(), stmtExprp);
        }

        // Track inlined functions for potential cleanup
        m_inlinedFuncs.insert(cfuncp);
    }

    void visit(AstCFunc* nodep) override {
        // Don't recurse into the functions we're potentially inlining from
        iterateChildren(nodep);
    }

    void visit(AstNode* nodep) override { iterateChildren(nodep); }

public:
    // CONSTRUCTORS
    explicit InlineCfuncsVisitor(AstNetlist* nodep)
        : m_threshold{v3Global.opt.inlineCfuncs()} {
        // Don't inline when profiling or tracing
        if (v3Global.opt.profCFuncs() || v3Global.opt.trace()) return;
        iterate(nodep);
    }
    ~InlineCfuncsVisitor() override {
        V3Stats::addStat("Optimizations, Inlined CFuncs", m_statInlined);
    }
};

//######################################################################
// InlineCfuncs class functions

void V3InlineCfuncs::inlineAll(AstNetlist* nodep) {
    UINFO(2, __FUNCTION__ << ":");
    { InlineCfuncsVisitor{nodep}; }  // Destruct before checking
    V3Global::dumpCheckGlobalTree("inlinecfuncs", 0, dumpTreeEitherLevel() >= 6);
}
