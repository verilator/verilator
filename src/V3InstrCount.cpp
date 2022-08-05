// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Estimate instruction count to run the logic
//                         we would generate for any given AST subtree.
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2022 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#include "config_build.h"
#include "verilatedos.h"

#include "V3InstrCount.h"

#include "V3Ast.h"

#include <iomanip>

/// Estimate the instruction cost for executing all logic within and below
/// a given AST node. Note this estimates the number of instructions we'll
/// execute, not the number we'll generate. That is, for conditionals,
/// we'll count instructions from either the 'if' or the 'else' branch,
/// whichever is larger. We know we won't run both.

class InstrCountVisitor final : public VNVisitor {
private:
    // NODE STATE
    //  AstNode::user4()        -> int.  Path cost + 1, 0 means don't dump
    //  AstNode::user5()        -> bool. Processed if assertNoDups
    const VNUser4InUse m_inuser4;

    // MEMBERS
    uint32_t m_instrCount = 0;  // Running count of instructions
    const AstNode* const m_startNodep;  // Start node of count
    bool m_tracingCall = false;  // Iterating into a CCall to a CFunc
    bool m_inCFunc = false;  // Inside AstCFunc
    const bool m_assertNoDups;  // Check for duplicates
    const std::ostream* const m_osp;  // Dump file

    // TYPES
    // Little class to cleanly call startVisitBase/endVisitBase
    class VisitBase final {
    private:
        // MEMBERS
        uint32_t m_savedCount;
        AstNode* const m_nodep;
        InstrCountVisitor* const m_visitor;

    public:
        // CONSTRUCTORS
        VisitBase(InstrCountVisitor* visitor, AstNode* nodep)
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
    InstrCountVisitor(AstNode* nodep, bool assertNoDups, std::ostream* osp)
        : m_startNodep{nodep}
        , m_assertNoDups{assertNoDups}
        , m_osp{osp} {
        if (nodep) iterate(nodep);
    }
    virtual ~InstrCountVisitor() override = default;

    // METHODS
    uint32_t instrCount() const { return m_instrCount; }

private:
    uint32_t startVisitBase(AstNode* nodep) {
        if (m_assertNoDups && !m_inCFunc) {
            // Ensure we don't count the same node twice
            //
            // We only enable this assert for the initial LogicMTask counts
            // in V3Order. We can't enable it for the 2nd pass in V3EmitC,
            // as we expect mtasks to contain common logic after V3Combine,
            // so this would fail.
            //
            // Also, we expect some collisions within calls to CFuncs
            // (which at the V3Order stage represent verilog tasks, not to
            // the CFuncs that V3Order will generate.) So don't check for
            // collisions in CFuncs.
            UASSERT_OBJ(!nodep->user5p(), nodep,
                        "Node originally inserted below logic vertex "
                            << static_cast<AstNode*>(nodep->user5p()));
            nodep->user5p(const_cast<void*>(reinterpret_cast<const void*>(m_startNodep)));
        }

        // Save the count, and add it back in during ~VisitBase This allows
        // debug prints to show local cost of each subtree, so we can see a
        // hierarchical view of the cost when in debug mode.
        const uint32_t savedCount = m_instrCount;
        m_instrCount = nodep->instrCount();
        return savedCount;
    }
    void endVisitBase(uint32_t savedCount, AstNode* nodep) {
        UINFO(8, "cost " << std::setw(6) << std::left << m_instrCount << "  " << nodep << endl);
        markCost(nodep);
        m_instrCount += savedCount;
    }
    void markCost(AstNode* nodep) {
        if (m_osp) nodep->user4(m_instrCount + 1);  // Else don't mark to avoid writeback
    }

    // VISITORS
    virtual void visit(AstNodeSel* nodep) override {
        // This covers both AstArraySel and AstWordSel
        //
        // If some vector is a bazillion dwords long, and we're selecting 1
        // dword to read or write from it, our cost should be small.
        //
        // Hence, exclude the child of the AstWordSel from the computation,
        // whose cost scales with the size of the entire (maybe large) vector.
        const VisitBase vb{this, nodep};
        iterateAndNextNull(nodep->bitp());
    }
    virtual void visit(AstSel* nodep) override {
        // Similar to AstNodeSel above, a small select into a large vector
        // is not expensive. Count the cost of the AstSel itself (scales with
        // its width) and the cost of the lsbp() and widthp() nodes, but not
        // the fromp() node which could be disproportionately large.
        const VisitBase vb{this, nodep};
        iterateAndNextNull(nodep->lsbp());
        iterateAndNextNull(nodep->widthp());
    }
    virtual void visit(AstSliceSel* nodep) override {  // LCOV_EXCL_LINE
        nodep->v3fatalSrc("AstSliceSel unhandled");
    }
    virtual void visit(AstMemberSel* nodep) override {  // LCOV_EXCL_LINE
        nodep->v3fatalSrc("AstMemberSel unhandled");
    }
    virtual void visit(AstConcat* nodep) override {
        // Nop.
        //
        // Ignore concat. The problem with counting concat is that when we
        // have many things concatted together, it's not a single
        // operation, but this:
        //
        //  concat(a, concat(b, concat(c, concat(d, ... ))))
        //
        // Then if we account a cost to each 'concat' that scales with its
        // width, this whole operation ends up with a cost accounting that
        // scales with N^2. Of course, the real operation isn't that
        // expensive: we won't copy each element over and over, we'll just
        // copy it once from its origin into its destination, so the actual
        // cost is linear with the size of the data. We don't need to count
        // the concat at all to reflect a linear cost; it's already there
        // in the width of the destination (which we count) and the sum of
        // the widths of the operands (ignored here).
        markCost(nodep);
    }
    virtual void visit(AstNodeIf* nodep) override {
        const VisitBase vb{this, nodep};
        iterateAndNextNull(nodep->condp());
        const uint32_t savedCount = m_instrCount;

        UINFO(8, "ifsp:\n");
        m_instrCount = 0;
        iterateAndNextNull(nodep->ifsp());
        uint32_t ifCount = m_instrCount;
        if (nodep->branchPred().unlikely()) ifCount = 0;

        UINFO(8, "elsesp:\n");
        m_instrCount = 0;
        iterateAndNextNull(nodep->elsesp());
        uint32_t elseCount = m_instrCount;
        if (nodep->branchPred().likely()) elseCount = 0;

        if (ifCount >= elseCount) {
            m_instrCount = savedCount + ifCount;
            if (nodep->elsesp()) nodep->elsesp()->user4(0);  // Don't dump it
        } else {
            m_instrCount = savedCount + elseCount;
            if (nodep->ifsp()) nodep->ifsp()->user4(0);  // Don't dump it
        }
    }
    virtual void visit(AstNodeCond* nodep) override {
        // Just like if/else above, the ternary operator only evaluates
        // one of the two expressions, so only count the max.
        const VisitBase vb{this, nodep};
        iterateAndNextNull(nodep->condp());
        const uint32_t savedCount = m_instrCount;

        UINFO(8, "?\n");
        m_instrCount = 0;
        iterateAndNextNull(nodep->expr1p());
        const uint32_t ifCount = m_instrCount;

        UINFO(8, ":\n");
        m_instrCount = 0;
        iterateAndNextNull(nodep->expr2p());
        const uint32_t elseCount = m_instrCount;

        if (ifCount < elseCount) {
            m_instrCount = savedCount + elseCount;
            if (nodep->expr1p()) nodep->expr1p()->user4(0);  // Don't dump it
        } else {
            m_instrCount = savedCount + ifCount;
            if (nodep->expr2p()) nodep->expr2p()->user4(0);  // Don't dump it
        }
    }
    virtual void visit(AstActive* nodep) override {
        // You'd think that the OrderLogicVertex's would be disjoint trees
        // of stuff in the AST, but it isn't so: V3Order makes an
        // OrderLogicVertex for each ACTIVE, and then also makes an
        // OrderLogicVertex for each statement within the ACTIVE.
        //
        // To avoid double-counting costs, stop recursing and short-circuit
        // the computation for each ACTIVE.
        //
        // Our intent is that this only stops at the root node of the
        // search; there should be no actives beneath the root, as there
        // are no actives-under-actives.  In any case, check that we're at
        // root:
        markCost(nodep);
        UASSERT_OBJ(nodep == m_startNodep, nodep, "Multiple actives, or not start node");
    }
    virtual void visit(AstNodeCCall* nodep) override {
        const VisitBase vb{this, nodep};
        iterateChildren(nodep);
        m_tracingCall = true;
        iterate(nodep->funcp());
        UASSERT_OBJ(!m_tracingCall, nodep, "visit(AstCFunc) should have cleared m_tracingCall.");
    }
    virtual void visit(AstCFunc* nodep) override {
        // Don't count a CFunc other than by tracing a call or counting it
        // from the root
        UASSERT_OBJ(m_tracingCall || nodep == m_startNodep, nodep,
                    "AstCFunc not under AstCCall, or not start node");
        m_tracingCall = false;
        VL_RESTORER(m_inCFunc);
        {
            m_inCFunc = true;
            const VisitBase vb{this, nodep};
            iterateChildren(nodep);
        }
    }
    virtual void visit(AstNode* nodep) override {
        const VisitBase vb{this, nodep};
        iterateChildren(nodep);
    }

    VL_DEBUG_FUNC;  // Declare debug()
    VL_UNCOPYABLE(InstrCountVisitor);
};

// Iterate the graph printing the critical path marked by previous visitation
class InstrCountDumpVisitor final : public VNVisitor {
private:
    // NODE STATE
    //  AstNode::user4()        -> int.  Path cost, 0 means don't dump

    // MEMBERS
    std::ostream* const m_osp;  // Dump file
    unsigned m_depth = 0;  // Current tree depth for printing indent

public:
    // CONSTRUCTORS
    InstrCountDumpVisitor(AstNode* nodep, std::ostream* osp)
        : m_osp{osp} {
        // No check for nullptr output, so...
        UASSERT_OBJ(osp, nodep, "Don't call if not dumping");
        if (nodep) iterate(nodep);
    }
    virtual ~InstrCountDumpVisitor() override = default;

private:
    // METHODS
    string indent() const { return string(m_depth, ':') + " "; }
    virtual void visit(AstNode* nodep) override {
        ++m_depth;
        if (unsigned costPlus1 = nodep->user4()) {
            *m_osp << "  " << indent() << "cost " << std::setw(6) << std::left << (costPlus1 - 1)
                   << "  " << nodep << '\n';
            iterateChildren(nodep);
        }
        --m_depth;
    }
    VL_DEBUG_FUNC;  // Declare debug()
    VL_UNCOPYABLE(InstrCountDumpVisitor);
};

uint32_t V3InstrCount::count(AstNode* nodep, bool assertNoDups, std::ostream* osp) {
    const InstrCountVisitor visitor{nodep, assertNoDups, osp};
    if (osp) InstrCountDumpVisitor dumper(nodep, osp);
    return visitor.instrCount();
}
