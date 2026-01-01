// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: NBA shadow variable assignment elimination
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
// Given a pair of variables 'd' and 'q', where 'd' is the shadow variable
// created by V3Delayed using the ShadowVar scheme. Attemp to turn this code:
//
//      ... reads of 'q' ok here
//  X1:  d = q; // First and complete write of 'd' (the pre-scheduled NBA initial assignment)
//      ... reads of 'q' ok here
//       d = foo; // Second assignment to 'd'
//      ... no reads of 'q' here
//  X2:  q = d; // Only and complete write of 'q', only read of 'd' (the post-scheduled NBA commit)
//      ... reads of 'q' ok here
//
// into:
//
//  X1:  q = q;
//       ...
//       q = foo;
//       ...
//  X2:  q = q;
//
// by replacing 'd' with 'q'. This then allows deletion of 'd' and the two assignments.
//
// More formally, with the non-sequential mtasks graph, we must prove all of these:
//  1) No reads of 'd' anywhere except for the ASSIGNPOST itself
//  2) No write of 'q' anywhere except for the ASSIGNPOST itself
//  3) The first write of 'd' is complete (writes all bits)
//  4) Every read  of 'q' either falls before the second write of 'd', or after only read of 'd'
//
// Notes:
//
// While these rules could be applied to any variables, not just the NBA
// shadow variables. **Proving** that no reads of 'q' happen after the second
// assignment of 'd' is difficult due to the presence of loops (the whole
// eval_nba is inside a loop), virtual methods and other dynamic executions.
// For the NBA shadow variables, we can compute this safely as their use
// is understood as we schedule their first and last assignments specially.
//
// Constraint 2 could be relaxed to "no write of 'q' before the only read of
// 'd', however we only have one write of 'q', created in V3Delayed, so
// trying harder would just be a code coverage hole today.
//
// Constraint 3 should always hold with V3Delayed, will check assert it.
//
//*************************************************************************

#include "V3PchAstNoMT.h"  // VL_MT_DISABLED_CODE_UNIT

#include "V3LifePost.h"

#include "V3ExecGraph.h"
#include "V3GraphPathChecker.h"
#include "V3Stats.h"

#include <algorithm>
#include <memory>
#include <unordered_map>

VL_DEFINE_DEBUG_FUNCTIONS;

//######################################################################
// LifePost delay elimination

class LifePostDlyVisitor final : public VNVisitorConst {
    // TYPES

    // Location of AstNode within the program
    template <typename T_Node>
    class Location final {
        template <typename U_Node>
        friend class Location;

        T_Node* m_nodep;  // The AstNode being recorded
        const AstExecGraph* m_egraphp;  // AstExecTraph location is under, if any
        const ExecMTask* m_mtaskp;  // The ExecMTask location is under, if any
        uint32_t m_seqNum;  // Location counter

    public:
        Location(T_Node* nodep, const AstExecGraph* egp, const ExecMTask* mtaskp, uint32_t seqNum)
            : m_nodep{nodep}
            , m_egraphp{egp}
            , m_mtaskp{mtaskp}
            , m_seqNum{seqNum} {}
        Location() = delete;

        T_Node* const& nodep() const { return m_nodep; }

        // "is before" - Note: Equality (concurrency) is possible iff they are independent mtasks!
        template <typename U_Node>
        bool operator<(const Location<U_Node>& that) const {
            // If they are in different mtasks under the same graph, check for a path in the graph
            if (m_egraphp && m_egraphp == that.m_egraphp && m_mtaskp != that.m_mtaskp) {
                GraphPathChecker* const checkerp = m_egraphp->user1u().to<GraphPathChecker*>();
                return checkerp->pathExistsFrom(m_mtaskp, that.m_mtaskp);
            }
            // Otherwise the sequence numbers work (one/both outside graph, or both in same mtask)
            return m_seqNum < that.m_seqNum;
        }
    };

    // NODE STATE
    // AstVarScope::user1()    -> bool: referenced outside _eval__nba
    // AstVarScope::user4()    -> AstVarScope*: Replacement variable
    // AstExecGraph::user1p()  -> GraphPathChecker*: path checker for this AstExecGraph
    const VNUser1InUse m_inuser1;
    const VNUser4InUse m_inuser4;

    // STATE
    uint32_t m_sequence = 0;  // Sequence number of assigns/varrefs,
    const AstExecGraph* m_execGraphp = nullptr;  // Current AstExecGraph being processed (or null)
    const ExecMTask* m_execMTaskp = nullptr;  // Current ExecMTask being processed (or null)
    VDouble0 m_statAssnDel;  // Statistic tracking
    // Maps from Varscope to all their reads and writes
    using LocMap = std::unordered_map<const AstVarScope*, std::vector<Location<AstVarRef>>>;
    LocMap m_reads;  // VarScope read locations
    LocMap m_writes;  // VarScope write locations
    std::vector<Location<AstNodeAssign>> m_assigns;  // Assignments considered for removal
    std::vector<std::unique_ptr<GraphPathChecker>> m_checkers;  // Storage for exec graph checkers
    const AstCFunc* const m_evalNbap;  // The _eval__nba function
    bool m_inEvalNba = false;  // Traversing under _eval__nba

    // METHODS
    void squashAssignposts() {
        for (const Location<AstNodeAssign>& assign : m_assigns) {
            AstVarScope* const dVscp = VN_AS(assign.nodep()->rhsp(), VarRef)->varScopep();
            AstVarScope* const qVscp = VN_AS(assign.nodep()->lhsp(), VarRef)->varScopep();

            // We are considering deleting 'y', don't do it if referenced external to _eval__nba
            if (dVscp->user1()) continue;

            const std::vector<Location<AstVarRef>>& dWrites = m_writes[dVscp];
            UASSERT_OBJ(!dWrites.empty(), dVscp, "NBA shadow variable read but never written");

            // *** See file header for requirements ***

            // Proof (1) - Only read is on the RHS of this assignment
            if (m_reads[dVscp].size() > 1) continue;

            // Proof (2) - Only write is on the LHS of this assignment
            if (m_writes[qVscp].size() > 1) continue;

            // Proof (3) - Should always hold
            UASSERT_OBJ(VN_IS(dWrites.at(0).nodep()->backp(), NodeAssign), dVscp,
                        "Partial first write to NBA shadow variable");

            // Proof (4)
            if (dWrites.size() > 1) {
                // V3Order always serializes writes so they cannot be concurrent
                UASSERT_OBJ(dWrites[0] < dWrites[1], dVscp, "Concurrent writes");
                const bool qRdOK = [&]() {
                    for (const Location<AstVarRef>& qRead : m_reads[qVscp]) {
                        if (assign < qRead) continue;
                        // Check from 2nd write of 'd'
                        for (size_t i = 1; i < dWrites.size(); ++i) {
                            if (qRead < dWrites[i]) continue;
                            return false;
                        }
                    }
                    return true;
                }();
                if (!qRdOK) continue;
            }

            // Mark variable for replacement
            dVscp->user4p(qVscp);
            // Delete assignment
            UINFO(4, "    DELETE " << assign.nodep());
            VL_DO_DANGLING(assign.nodep()->unlinkFrBack()->deleteTree(), assign.nodep());
            ++m_statAssnDel;
        }
    }

    // Trace code in the given function
    void trace(AstCFunc* nodep) {
        VL_RESTORER(m_inEvalNba);
        if (nodep == m_evalNbap) m_inEvalNba = true;
        iterateChildrenConst(nodep);
    }

    // VISITORS
    void visit(AstNetlist* nodep) override {
        // First, build maps of every location (mtask and sequence
        // within the mtask) where each varscope is read, and written.
        iterateChildrenConst(nodep);

        // We need to be able to pick up the first write of each variable.
        // V3Order serializes all writes, and we trace AstExecGraph in
        // dependency order, so the first one we encounter during tracing should
        // always be the one. It's somewhat expensive to assert so only with debugCheck().
        if (v3Global.opt.debugCheck()) {
            for (auto& pair : m_writes) {
                const std::vector<Location<AstVarRef>>& writes = pair.second;
                const Location<AstVarRef>& first = writes[0];
                for (size_t i = 1; i < writes.size(); ++i) {
                    UASSERT_OBJ(first < writes[i], pair.first, "First write is not the first");
                }
            }
        }

        // Find all assignposts. Determine which ones can be
        // eliminated. Remove those, and mark their dly vars' user4 field
        // to indicate we should replace these dly vars with their original
        // variables.
        squashAssignposts();

        // Apply replacements
        nodep->foreach([](AstVarRef* nodep) {
            const AstVarScope* const vscp = nodep->varScopep();
            AstVarScope* const replacementp = VN_AS(vscp->user4p(), VarScope);
            if (!replacementp) return;
            UINFO(9, "  Replace " << nodep << " target " << vscp << " with " << replacementp);
            nodep->varScopep(replacementp);
            nodep->varp(replacementp->varp());
        });
    }

    void visit(AstVarRef* nodep) override {
        // We only try to optimize NBA shadow variables
        if (!nodep->varScopep()->optimizeLifePost()) return;

        // Mark variables referenced outside _eval__nba
        if (!m_inEvalNba) {
            nodep->varScopep()->user1(true);
            return;
        }

        // Consumption/generation of a variable,
        const AstVarScope* const vscp = nodep->varScopep();
        UASSERT_OBJ(vscp, nodep, "Scope not assigned");

        ++m_sequence;
        if (nodep->access().isWriteOrRW()) {
            m_writes[vscp].emplace_back(nodep, m_execGraphp, m_execMTaskp, m_sequence);
        }
        if (nodep->access().isReadOrRW()) {
            m_reads[vscp].emplace_back(nodep, m_execGraphp, m_execMTaskp, m_sequence);
        }
    }
    void visit(AstNodeAssign* nodep) override {
        // Record RHS before assignment
        iterateConst(nodep->rhsp());
        // If a straight assignment between NBA variables, consider for removal
        if (const AstVarRef* const lhsp = VN_CAST(nodep->lhsp(), VarRef)) {
            if (const AstVarRef* const rhsp = VN_CAST(nodep->rhsp(), VarRef)) {
                if (lhsp->varScopep()->optimizeLifePost()  //
                    && rhsp->varScopep()->optimizeLifePost()) {
                    m_assigns.emplace_back(nodep, m_execGraphp, m_execMTaskp, ++m_sequence);
                }
            }
        }
        // Record LHS after assignment
        iterateConst(nodep->lhsp());
    }
    void visit(AstNodeCCall* nodep) override {
        iterateChildrenConst(nodep);
        // Entry points are roots of the trace, no need to do it here
        if (nodep->funcp()->entryPoint()) return;
        // Trace cellee
        trace(nodep->funcp());
    }
    void visit(AstExecGraph* nodep) override {
        UASSERT_OBJ(!m_execGraphp, nodep, "Nested AstExecGraph");
        VL_RESTORER(m_execGraphp);
        m_execGraphp = nodep;

        // Set up the path checker for this graph
        UASSERT_OBJ(!nodep->user1p(), nodep, "AstExecGraph visited twice");
        m_checkers.emplace_back(new GraphPathChecker{nodep->depGraphp()});
        nodep->user1p(m_checkers.back().get());

        // Trace each mtask body. Note: the vertices are in topological order,
        // and we do not reset m_sequence, so a lower sequence number does
        // guarantee a node is not earlier than a higher sequence number, but
        // might still be concurrent.
        for (V3GraphVertex& mtaskVtx : nodep->depGraphp()->vertices()) {
            const ExecMTask* const mtaskp = mtaskVtx.as<ExecMTask>();
            VL_RESTORER(m_execMTaskp);
            m_execMTaskp = mtaskp;
            trace(mtaskp->funcp());
        }
    }
    void visit(AstCFunc* nodep) override {
        // Start a trace from each entry point
        if (nodep->entryPoint()) trace(nodep);
    }
    //-----
    void visit(AstNode* nodep) override { iterateChildrenConst(nodep); }

public:
    // CONSTRUCTORS
    explicit LifePostDlyVisitor(AstNetlist* netlistp)
        : m_evalNbap{netlistp->evalNbap()} {
        iterateConst(netlistp);
    }
    ~LifePostDlyVisitor() override {
        V3Stats::addStat("Optimizations, Lifetime postassign deletions", m_statAssnDel);
    }
};

//######################################################################
// LifePost class functions

void V3LifePost::lifepostAll(AstNetlist* nodep) {
    UINFO(2, __FUNCTION__ << ":");
    { LifePostDlyVisitor{nodep}; }  // Destruct before checking
    V3Global::dumpCheckGlobalTree("life_post", 0, dumpTreeEitherLevel() >= 3);
}
