// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Inline small CFuncs into their callers
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
// V3InlineCFuncs's Transformations:
//
// For each CCall to a small CFunc:
//   - Check if function is eligible for inlining (small enough, same scope)
//   - Clone local variables with unique names to avoid collisions
//   - Replace CCall with cloned function body statements
//
// Two tunables control inlining:
//   --inline-cfuncs <n>         : Always inline if size <= n (default 20)
//   --inline-cfuncs-product <n> : Also inline if size * call_count <= n (default 200)
//
//*************************************************************************

#include "V3PchAstNoMT.h"  // VL_MT_DISABLED_CODE_UNIT

#include "V3InlineCFuncs.h"

#include "V3AstUserAllocator.h"
#include "V3Stats.h"

#include <map>
#include <vector>

VL_DEFINE_DEBUG_FUNCTIONS;

//######################################################################
// Helper visitor to check if a CFunc contains C statements
// Uses clearOptimizable pattern for debugging

class CFuncInlineCheckVisitor final : public VNVisitorConst {
    // STATE
    bool m_optimizable = true;  // True if function can be inlined
    string m_whyNot;  // Reason why not optimizable
    AstNode* m_whyNotNodep = nullptr;  // Node that caused non-optimizable

    // METHODS
    void clearOptimizable(AstNode* nodep, const string& why) {
        if (m_optimizable) {
            m_optimizable = false;
            m_whyNot = why;
            m_whyNotNodep = nodep;
            UINFO(9, "CFunc not inlineable: " << why);
            if (nodep) UINFO(9, ": " << nodep);
            UINFO(9, endl);
        }
    }

    // VISITORS
    void visit(AstCStmt* nodep) override { clearOptimizable(nodep, "contains AstCStmt"); }
    void visit(AstCExpr* nodep) override { clearOptimizable(nodep, "contains AstCExpr"); }
    void visit(AstCStmtUser* nodep) override { clearOptimizable(nodep, "contains AstCStmtUser"); }
    void visit(AstCExprUser* nodep) override { clearOptimizable(nodep, "contains AstCExprUser"); }
    void visit(AstNode* nodep) override { iterateChildrenConst(nodep); }

public:
    // CONSTRUCTORS
    explicit CFuncInlineCheckVisitor(AstCFunc* cfuncp) { iterateConst(cfuncp); }

    // ACCESSORS
    bool optimizable() const { return m_optimizable; }
    string whyNot() const { return m_whyNot; }
    AstNode* whyNotNodep() const { return m_whyNotNodep; }
};

//######################################################################

class InlineCFuncsVisitor final : public VNVisitor {
    // NODE STATE
    // AstCFunc::user1()  ->  vector of AstCCall* pointing to this function
    // AstCFunc::user2()  ->  bool: true if checked for C statements
    // AstCFunc::user3()  ->  bool: true if contains C statements (not inlineable)
    const VNUser1InUse m_user1InUse;
    const VNUser2InUse m_user2InUse;
    const VNUser3InUse m_user3InUse;
    AstUser1Allocator<AstCFunc, std::vector<AstCCall*>> m_callSites;

    // STATE
    VDouble0 m_statInlined;  // Statistic tracking
    const int m_threshold1;  // Size threshold: always inline if size <= this
    const int m_threshold2;  // Product threshold: inline if size * calls <= this
    AstCFunc* m_callerFuncp = nullptr;  // Current caller function
    // Tuples of (StmtExpr to replace, CFunc to inline from, caller func for vars)
    std::vector<std::tuple<AstStmtExpr*, AstCFunc*, AstCFunc*>> m_toInline;

    // METHODS

    // Check if a function contains any $c() calls (user or internal)
    // Results are cached in user2/user3 for efficiency
    bool containsCStatements(AstCFunc* cfuncp) {
        if (!cfuncp->user2()) {
            // Not yet checked - run the check visitor
            cfuncp->user2(true);  // Mark as checked
            const CFuncInlineCheckVisitor checker{cfuncp};
            cfuncp->user3(!checker.optimizable());  // Store result (true = contains C stmts)
        }
        return cfuncp->user3();
    }

    // Check if a function is eligible for inlining into caller
    bool isInlineable(AstCFunc* callerp, AstCFunc* cfuncp) {
        // Must be in the same scope (same class) to access the same members
        if (callerp->scopep() != cfuncp->scopep()) return false;

        // Check for $c() calls that might use 'this'
        if (containsCStatements(cfuncp)) return false;

        // Check it's a void function (not a coroutine)
        if (cfuncp->rtnTypeVoid() != "void") return false;

        // Don't inline functions marked dontCombine (e.g. trace, entryPoint)
        if (cfuncp->dontCombine()) return false;

        // Don't inline entry point functions
        if (cfuncp->entryPoint()) return false;

        // Must have statements to inline
        if (!cfuncp->stmtsp()) return false;

        // Check size thresholds
        const size_t funcSize = cfuncp->nodeCount();

        // Always inline if small enough
        if (funcSize <= static_cast<size_t>(m_threshold1)) return true;

        // Also inline if size * call_count is reasonable
        const size_t callCount = m_callSites(cfuncp).size();
        if (callCount > 0 && funcSize * callCount <= static_cast<size_t>(m_threshold2)) {
            return true;
        }

        return false;
    }

    // VISITORS
    void visit(AstCCall* nodep) override {
        iterateChildren(nodep);

        AstCFunc* const cfuncp = nodep->funcp();
        if (!cfuncp) return;

        // Track call site for call counting
        m_callSites(cfuncp).emplace_back(nodep);
    }

    void visit(AstCFunc* nodep) override {
        VL_RESTORER(m_callerFuncp);
        m_callerFuncp = nodep;
        iterateChildren(nodep);
    }

    void visit(AstNodeModule* nodep) override {
        // Process per module for better cache behavior
        m_toInline.clear();

        // Phase 1: Collect call sites within this module
        iterateChildren(nodep);

        // Phase 2: Determine which calls to inline
        collectInlineCandidates(nodep);

        // Phase 3: Perform inlining for this module
        doInlining();
    }

    void visit(AstNode* nodep) override { iterateChildren(nodep); }

    // Collect calls that should be inlined within this module
    void collectInlineCandidates(AstNodeModule* modp) {
        for (AstNode* stmtp = modp->stmtsp(); stmtp; stmtp = stmtp->nextp()) {
            AstCFunc* const callerp = VN_CAST(stmtp, CFunc);
            if (!callerp) continue;

            callerp->foreach([&](AstCCall* callp) {
                AstCFunc* const cfuncp = callp->funcp();
                if (!cfuncp) return;
                if (!isInlineable(callerp, cfuncp)) return;

                // Walk up to find the containing StmtExpr
                AstNode* stmtNodep = callp;
                while (stmtNodep && !VN_IS(stmtNodep, StmtExpr) && !VN_IS(stmtNodep, CFunc)) {
                    stmtNodep = stmtNodep->backp();
                }

                AstStmtExpr* const stmtExprp = VN_CAST(stmtNodep, StmtExpr);
                if (!stmtExprp) return;

                m_toInline.emplace_back(stmtExprp, cfuncp, callerp);
            });
        }
    }

    // Perform the actual inlining after iteration is complete
    void doInlining() {
        for (const auto& tuple : m_toInline) {
            AstStmtExpr* const stmtExprp = std::get<0>(tuple);
            AstCFunc* const cfuncp = std::get<1>(tuple);
            AstCFunc* const callerp = std::get<2>(tuple);

            UINFO(6, "Inlining CFunc " << cfuncp->name() << " into " << callerp->name() << endl);
            ++m_statInlined;

            // Clone local variables with unique names to avoid collisions
            std::map<AstVar*, AstVar*> varMap;
            for (AstVar* varp = cfuncp->varsp(); varp; varp = VN_AS(varp->nextp(), Var)) {
                const string newName = "__Vinline_" + cfuncp->name() + "_" + varp->name();
                AstVar* const newVarp = varp->cloneTree(false);
                newVarp->name(newName);
                callerp->addVarsp(newVarp);
                varMap[varp] = newVarp;
            }

            // Clone the function body
            AstNode* const bodyp = cfuncp->stmtsp()->cloneTree(true);

            // Retarget variable references to the cloned variables
            // Must iterate all sibling statements, not just the first
            if (!varMap.empty()) {
                for (AstNode* stmtp = bodyp; stmtp; stmtp = stmtp->nextp()) {
                    stmtp->foreach([&](AstVarRef* refp) {
                        auto it = varMap.find(refp->varp());
                        if (it != varMap.end()) refp->varp(it->second);
                    });
                }
            }

            // Replace the statement with the inlined body
            stmtExprp->addNextHere(bodyp);
            VL_DO_DANGLING(stmtExprp->unlinkFrBack()->deleteTree(), stmtExprp);
        }
    }

public:
    // CONSTRUCTORS
    explicit InlineCFuncsVisitor(AstNetlist* nodep)
        : m_threshold1{v3Global.opt.inlineCFuncs()}
        , m_threshold2{v3Global.opt.inlineCFuncsProduct()} {
        // Don't inline when profiling or tracing
        if (v3Global.opt.profCFuncs() || v3Global.opt.trace()) return;
        // Process modules one at a time for better cache behavior
        iterateAndNextNull(nodep->modulesp());
    }
    ~InlineCFuncsVisitor() override {
        V3Stats::addStat("Optimizations, Inlined CFuncs", m_statInlined);
    }
};

//######################################################################
// InlineCFuncs class functions

void V3InlineCFuncs::inlineAll(AstNetlist* nodep) {
    UINFO(2, __FUNCTION__ << ":");
    { InlineCFuncsVisitor{nodep}; }  // Destruct before checking
    V3Global::dumpCheckGlobalTree("inlinecfuncs", 0, dumpTreeEitherLevel() >= 6);
}
