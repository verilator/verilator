// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Capture task/function write summaries for undriven checks
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

#include "V3UndrivenCapture.h"

#include "V3Error.h"
#include "V3Global.h"

#include <algorithm>

VL_DEFINE_DEBUG_FUNCTIONS;

namespace {

constexpr int DBG = 9;
struct Stats final {
    uint64_t ftasks = 0;
    uint64_t varWrites = 0;
    uint64_t callEdges = 0;
} g_stats;
static std::string taskNameQ(const AstNodeFTask* taskp) {
    if (!taskp) return "<null>";
    return taskp->prettyNameQ();
}

class CaptureVisitor final : public VNVisitorConst {
    V3UndrivenCapture& m_cap;
    const AstNodeFTask* m_curTaskp = nullptr;

    static void iterateListConst(VNVisitorConst& v, AstNode* nodep) {
        for (AstNode* np = nodep; np; np = np->nextp()) np->accept(v);
    }

    /*
    V3UndrivenCapture::FTaskInfo& infoFor(const AstNodeFTask* taskp) {
        // Ensure entry exists
        return m_cap.writeSummary(taskp), const_cast<V3UndrivenCapture::FTaskInfo&>(
                                           *m_cap.find(taskp));  // not used; see below
    }
    */

public:
    explicit CaptureVisitor(V3UndrivenCapture& cap, AstNetlist* netlistp)
        : m_cap{cap} {
        iterateConst(netlistp);
    }

private:
    // Visit a task/function definition and collect direct writes and direct callees.
    void visit(AstNodeFTask* nodep) override {
        VL_RESTORER(m_curTaskp);
        m_curTaskp = nodep;
        ++g_stats.ftasks;
        UINFO(DBG, "UndrivenCapture: enter ftask " << nodep << " " << nodep->prettyNameQ());
        (void)m_cap.ensureEntry(nodep);  // ensure map entry exists
        iterateListConst(*this, nodep->stmtsp());
    }

    void visit(AstNodeVarRef* nodep) override {
        if (m_curTaskp && nodep->access().isWriteOrRW()) {
            ++g_stats.varWrites;
            UINFO(DBG, "UndrivenCapture: direct write in " << taskNameQ(m_curTaskp) << " var=" << nodep->varp()->prettyNameQ() << " at " << nodep->fileline());
            // Ensure entry exists
            (void)m_cap.ensureEntry(m_curTaskp);
            // Safe: find() must succeed after writeSummary() creates entry
            auto* const infop = const_cast<V3UndrivenCapture::FTaskInfo*>(m_cap.find(m_curTaskp));
            if (infop) infop->directWrites.push_back(nodep->varp());
        }
        iterateChildrenConst(nodep);
    }

    void visit(AstNodeFTaskRef* nodep) override {
        // Record the call edge if resolved
        if (m_curTaskp) {
            if (AstNodeFTask* const calleep = nodep->taskp()) {
                ++g_stats.callEdges;
                UINFO(DBG, "UndrivenCapture: call edge " << taskNameQ(m_curTaskp) << " -> " << taskNameQ(calleep));
                (void)m_cap.ensureEntry(m_curTaskp);
                (void)m_cap.ensureEntry(calleep);
                auto* const infop
                    = const_cast<V3UndrivenCapture::FTaskInfo*>(m_cap.find(m_curTaskp));
                if (infop) infop->callees.push_back(calleep);
            } else {
                UINFO(DBG, "UndrivenCapture: unresolved call in " << taskNameQ(m_curTaskp) << " name=" << nodep->name());
            }
        }
        iterateChildrenConst(nodep);  // still scan pins/args
    }

    void visit(AstNode* nodep) override { iterateChildrenConst(nodep); }
};

}  // namespace

// static
void V3UndrivenCapture::sortUniqueVars(std::vector<Var>& vec) {
    std::sort(vec.begin(), vec.end());
    vec.erase(std::unique(vec.begin(), vec.end()), vec.end());
}

// static
void V3UndrivenCapture::sortUniqueFTasks(std::vector<FTask>& vec) {
    std::sort(vec.begin(), vec.end());
    vec.erase(std::unique(vec.begin(), vec.end()), vec.end());
}

V3UndrivenCapture::V3UndrivenCapture(AstNetlist* netlistp) {
    gather(netlistp);

    // Normalize direct lists
    for (auto& kv : m_info) {
        sortUniqueVars(kv.second.directWrites);
        sortUniqueFTasks(kv.second.callees);
    }

    // Compute summaries for all tasks (MVP: DFS memoization, no SCC yet)
    for (const auto& kv : m_info) (void)computeWriteSummary(kv.first);

    UINFO(DBG, "UndrivenCapture: stats ftasks=" << g_stats.ftasks << " varWrites=" << g_stats.varWrites << " callEdges=" << g_stats.callEdges << " uniqueTasks=" << m_info.size());
}

void V3UndrivenCapture::gather(AstNetlist* netlistp) {
    // Walk netlist and populate m_info with direct writes + call edges
    CaptureVisitor{*this, netlistp};
}

const V3UndrivenCapture::FTaskInfo* V3UndrivenCapture::find(FTask taskp) const {
    const auto it = m_info.find(taskp);
    if (it == m_info.end()) return nullptr;
    return &it->second;
}

const std::vector<V3UndrivenCapture::Var>& V3UndrivenCapture::writeSummary(FTask taskp) {
    // Ensure entry exists even if empty
    (void)m_info[taskp];
    return computeWriteSummary(taskp);
}

const std::vector<V3UndrivenCapture::Var>& V3UndrivenCapture::computeWriteSummary(FTask taskp) {
    FTaskInfo& info = m_info[taskp];

    if (info.state == State::DONE) {
        UINFO(DBG, "UndrivenCapture: writeSummary cached size=" << info.writeSummary.size() << " for " << taskNameQ(taskp));
        return info.writeSummary;
    }
    if (info.state == State::VISITING) {
        UINFO(DBG, "UndrivenCapture: recursion detected at " << taskNameQ(taskp) << " returning directWrites size=" << info.directWrites.size());
        // Cycle detected (recursion/mutual recursion). MVP behavior:
        // return directWrites only to guarantee termination.
        if (info.writeSummary.empty()) info.writeSummary = info.directWrites;
        sortUniqueVars(info.writeSummary);
        return info.writeSummary;
    }

    info.state = State::VISITING;

    // Start with direct writes
    info.writeSummary = info.directWrites;

    // Union in callees
    for (FTask calleep : info.callees) {
        if (m_info.find(calleep) == m_info.end()) continue;
        const std::vector<Var>& sub = computeWriteSummary(calleep);
        info.writeSummary.insert(info.writeSummary.end(), sub.begin(), sub.end());
    }

    sortUniqueVars(info.writeSummary);

    UINFO(DBG, "UndrivenCapture: writeSummary computed size=" << info.writeSummary.size() << " for " << taskNameQ(taskp));

    info.state = State::DONE;
    return info.writeSummary;
}

void V3UndrivenCapture::debugDumpTask(FTask taskp, int level) const {
    const auto* const infop = find(taskp);
    if (!infop) {
        UINFO(level, "UndrivenCapture: no entry for task " << taskp);
        return;
    }
    UINFO(level, "UndrivenCapture: dump task "
        << taskp << " " << taskp->prettyNameQ()
        << " directWrites=" << infop->directWrites.size()
        << " callees=" << infop->callees.size()
        << " writeSummary=" << infop->writeSummary.size());
}

void V3UndrivenCapture::ensureEntry(FTask taskp) { (void)m_info[taskp]; }
