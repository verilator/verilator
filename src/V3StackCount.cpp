// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Estimate stack size to run the AST subtree.
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2003-2026 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#include "V3PchAstNoMT.h"  // VL_MT_DISABLED_CODE_UNIT

#include "V3StackCount.h"

VL_DEFINE_DEBUG_FUNCTIONS;

/// Estimate the stack byte size for executing all logic within and below a
/// given AST node. This is very rough, only for warning when stack is too
/// small.

class StackCountVisitor final : public VNVisitorConst {
    // NODE STATE
    //  AstNode::user2()        -> uint64_t.  Path cost + 1,
    const VNUser2InUse m_inuser2;

    // MEMBERS
    uint64_t m_stackSize = 0;  // Running count of instructions
    uint64_t m_maxLazyCallee = 0;
    bool m_tracingCall = false;  // Iterating into a CCall to a CFunc
    bool m_ignoreRemaining = false;  // Ignore remaining statements in the block
    bool m_inCFunc = false;  // Inside function

    // TYPES
    // Little class to cleanly call startVisitBase/endVisitBase
    class VisitBase final {
        // MEMBERS
        uint64_t m_savedCount;
        AstNode* const m_nodep;
        StackCountVisitor* const m_visitor;

    public:
        // CONSTRUCTORS
        VisitBase(StackCountVisitor* visitor, AstNode* nodep)
            : m_nodep{nodep}
            , m_visitor{visitor} {
            m_savedCount = m_visitor->startVisitBase(nodep);
        }
        ~VisitBase() { m_visitor->endVisitBase(m_savedCount, m_nodep); }

    private:
        VL_UNCOPYABLE(VisitBase);
    };

public:
    // CONSTRUCTORS
    explicit StackCountVisitor(AstNode* nodep) { iterateConstNull(nodep); }
    ~StackCountVisitor() override = default;

    // METHODS
    uint64_t stackSize() const { return m_stackSize + m_maxLazyCallee; }

private:
    void reset() {
        m_stackSize = 0;
        m_ignoreRemaining = false;
    }
    uint64_t startVisitBase(AstNode* nodep) {
        UASSERT_OBJ(!m_ignoreRemaining, nodep, "Should not reach here if ignoring");

        // Save the count, and add it back in during ~VisitBase This allows
        // debug prints to show local cost of each subtree, so we can see a
        // hierarchical view of the cost when in debug mode.
        const uint64_t savedCount = m_stackSize;
        m_stackSize = 0;
        return savedCount;
    }
    void endVisitBase(uint64_t savedCount, const AstNode* nodep) {
        UINFO(8, "cost " << std::setw(6) << std::left << m_stackSize << "  " << nodep);
        if (!m_ignoreRemaining) m_stackSize += savedCount;
    }

    // VISITORS
    void visit(AstNodeIf* nodep) override {
        if (m_ignoreRemaining) return;
        const VisitBase vb{this, nodep};
        iterateAndNextConstNull(nodep->condp());
        const uint64_t savedCount = m_stackSize;

        UINFO(8, "thensp:");
        reset();
        iterateAndNextConstNull(nodep->thensp());
        uint64_t ifCount = m_stackSize;
        if (nodep->branchPred().unlikely()) ifCount = 0;

        UINFO(8, "elsesp:");
        reset();
        iterateAndNextConstNull(nodep->elsesp());
        uint64_t elseCount = m_stackSize;
        if (nodep->branchPred().likely()) elseCount = 0;

        reset();
        if (ifCount >= elseCount) {
            m_stackSize = savedCount + ifCount;
            if (nodep->elsesp()) nodep->elsesp()->user2(0);  // Don't dump it
        } else {
            m_stackSize = savedCount + elseCount;
            if (nodep->thensp()) nodep->thensp()->user2(0);  // Don't dump it
        }
    }
    void visit(AstCond* nodep) override {
        if (m_ignoreRemaining) return;
        // Just like if/else above, the ternary operator only evaluates
        // one of the two expressions, so only count the max.
        const VisitBase vb{this, nodep};
        iterateAndNextConstNull(nodep->condp());
        const uint64_t savedCount = m_stackSize;

        UINFO(8, "?");
        reset();
        iterateAndNextConstNull(nodep->thenp());
        const uint64_t ifCount = m_stackSize;

        UINFO(8, ":");
        reset();
        iterateAndNextConstNull(nodep->elsep());
        const uint64_t elseCount = m_stackSize;

        reset();
        if (ifCount >= elseCount) {
            m_stackSize = savedCount + ifCount;
            if (nodep->elsep()) nodep->elsep()->user2(0);  // Don't dump it
        } else {
            m_stackSize = savedCount + elseCount;
            if (nodep->thenp()) nodep->thenp()->user2(0);  // Don't dump it
        }
    }
    void visit(AstFork* nodep) override {
        if (m_ignoreRemaining) return;
        const VisitBase vb{this, nodep};
        iterateAndNextConstNull(nodep->stmtsp());
        uint64_t totalCount = m_stackSize;
        VL_RESTORER(m_ignoreRemaining);
        // Sum counts in each statement
        for (AstNode* stmtp = nodep->forksp(); stmtp; stmtp = stmtp->nextp()) {
            reset();
            iterateConst(stmtp);
            totalCount += m_stackSize;
        }
        m_stackSize = totalCount;
    }
    void visit(AstNodeCCall* nodep) override {
        if (m_ignoreRemaining) return;
        const VisitBase vb{this, nodep};
        iterateChildrenConst(nodep);
        m_tracingCall = true;
        iterateConst(nodep->funcp());
        UASSERT_OBJ(!m_tracingCall, nodep, "visit(AstCFunc) should have cleared m_tracingCall.");
    }
    void visit(AstCFunc* nodep) override {
        // Don't count a CFunc other than by tracing a call or counting it
        // from the root
        if (!m_tracingCall && !nodep->entryPoint()) return;
        m_tracingCall = false;
        if (nodep->recursive()) return;
        if (!nodep->user2()) {  // Short circuit
            VL_RESTORER(m_ignoreRemaining);
            VL_RESTORER(m_stackSize);
            VL_RESTORER(m_inCFunc);
            VL_RESTORER(m_maxLazyCallee);
            m_tracingCall = false;
            m_stackSize = 0;
            m_maxLazyCallee = 0;
            m_inCFunc = true;
            const VisitBase vb{this, nodep};
            iterateChildrenConst(nodep);
            // Only one reconstruct callee is active at a time.
            nodep->user2(m_stackSize + m_maxLazyCallee + 1);
        }
        const uint64_t cost = nodep->user2() - 1;
        // Shared cone operands make sibling sums incorrect.
        if (nodep->vpiLazyReconstruct()) {
            m_maxLazyCallee = std::max(m_maxLazyCallee, cost);
        } else {
            m_stackSize += cost;
        }
        m_tracingCall = false;
    }
    void visit(AstVar* nodep) override {
        if (!m_inCFunc) return;
        m_stackSize += nodep->isRef() ? sizeof(void*) : nodep->dtypep()->widthTotalBytes();
        iterateChildrenConst(nodep);
    }

    void visit(AstNodeExpr* nodep) override {}  // Short-circuit
    void visit(AstNode* nodep) override {
        if (m_ignoreRemaining) return;
        const VisitBase vb{this, nodep};
        iterateChildrenConst(nodep);
    }

    VL_UNCOPYABLE(StackCountVisitor);
};

uint64_t V3StackCount::count(AstNode* nodep) {
    const StackCountVisitor visitor{nodep};
    return visitor.stackSize();
}
