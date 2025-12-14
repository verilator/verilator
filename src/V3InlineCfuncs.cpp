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

#include <vector>

VL_DEFINE_DEBUG_FUNCTIONS;

//######################################################################

class InlineCfuncsVisitor final : public VNVisitor {
    // STATE
    VDouble0 m_statInlined;  // Statistic tracking
    const int m_threshold;  // Inlining threshold from options
    AstCFunc* m_callerFuncp = nullptr;  // Current caller function
    // Pairs of (StmtExpr to replace, CFunc to inline from)
    std::vector<std::pair<AstStmtExpr*, AstCFunc*>> m_toInline;

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

    // Check if function has any local variables (anywhere in body, not just top-level)
    static bool hasLocalVars(AstCFunc* cfuncp) {
        bool found = false;
        cfuncp->foreach([&](const AstVar*) { found = true; });
        return found;
    }

    // Check if a function is eligible for inlining into caller
    bool isInlineable(AstCFunc* callerp, AstCFunc* cfuncp) {
        // Check size
        const size_t funcSize = cfuncp->nodeCount();
        if (funcSize > static_cast<size_t>(m_threshold)) return false;

        // Must be in the same scope (same class) to access the same members
        if (callerp->scopep() != cfuncp->scopep()) return false;

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

        // Need a caller context to inline into
        if (!m_callerFuncp) return;

        if (!isInlineable(m_callerFuncp, cfuncp)) return;

        // Walk up to find the containing StmtExpr
        // The CCall should be wrapped in a StmtExpr for standalone calls
        AstNode* stmtp = nodep;
        while (stmtp && !VN_IS(stmtp, StmtExpr) && !VN_IS(stmtp, CFunc)) {
            stmtp = stmtp->backp();
        }

        // Only inline if we found a StmtExpr (standalone function call)
        AstStmtExpr* const stmtExprp = VN_CAST(stmtp, StmtExpr);
        if (!stmtExprp) return;

        // Collect for later processing (can't modify tree during iteration)
        m_toInline.emplace_back(stmtExprp, cfuncp);
    }

    void visit(AstCFunc* nodep) override {
        VL_RESTORER(m_callerFuncp);
        m_callerFuncp = nodep;
        iterateChildren(nodep);
    }

    void visit(AstNode* nodep) override { iterateChildren(nodep); }

    // Perform the actual inlining after iteration is complete
    void doInlining() {
        for (const auto& pair : m_toInline) {
            AstStmtExpr* const stmtExprp = pair.first;
            AstCFunc* const cfuncp = pair.second;

            UINFO(6, "Inlining CFunc call into: " << stmtExprp << " from " << cfuncp << endl);
            ++m_statInlined;

            // Clone the function body
            AstNode* const bodyp = cfuncp->stmtsp()->cloneTree(true);

            // Replace the statement with the inlined body
            stmtExprp->addNextHere(bodyp);
            VL_DO_DANGLING(stmtExprp->unlinkFrBack()->deleteTree(), stmtExprp);
        }
    }

public:
    // CONSTRUCTORS
    explicit InlineCfuncsVisitor(AstNetlist* nodep)
        : m_threshold{v3Global.opt.inlineCfuncs()} {
        // Don't inline when profiling or tracing
        if (v3Global.opt.profCFuncs() || v3Global.opt.trace()) return;
        // Phase 1: Collect CCalls to inline
        iterate(nodep);
        // Phase 2: Perform the inlining
        doInlining();
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
