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

VL_DEFINE_DEBUG_FUNCTIONS;

namespace {

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
        UINFO(9, "undriven capture enter ftask " << nodep << " " << nodep->prettyNameQ());
        m_cap.noteTask(nodep);
        iterateListConst(*this, nodep->stmtsp());
    }

    void visit(AstNodeVarRef* nodep) override {
        if (m_curTaskp && nodep->access().isWriteOrRW()) {
            ++g_stats.varWrites;
            UINFO(9, "undriven capture direct write in " << taskNameQ(m_curTaskp)
                                                         << " var=" << nodep->varp()->prettyNameQ()
                                                         << " at " << nodep->fileline());

            m_cap.noteDirectWrite(m_curTaskp, nodep->varp());
        }
        iterateChildrenConst(nodep);
    }

    void visit(AstNodeFTaskRef* nodep) override {
        // Record the call edge if resolved
        if (m_curTaskp) {
            if (AstNodeFTask* const calleep = nodep->taskp()) {
                ++g_stats.callEdges;
                UINFO(9, "undriven capture call edge " << taskNameQ(m_curTaskp) << " -> "
                                                       << taskNameQ(calleep));
                m_cap.noteCallEdge(m_curTaskp, calleep);
            } else {
                UINFO(9, "undriven capture unresolved call in " << taskNameQ(m_curTaskp)
                                                                << " name=" << nodep->name());
            }
        }
        iterateChildrenConst(nodep);  // still scan pins/args
    }

    void visit(AstNode* nodep) override { iterateChildrenConst(nodep); }
};

}  // namespace

V3UndrivenCapture::V3UndrivenCapture(AstNetlist* netlistp) {
    gather(netlistp);

    // Compute summaries for all tasks
    for (const auto& kv : m_info) (void)computeWriteSummary(kv.first);

    // Release the filter memory
    for (auto& kv : m_info) {
        kv.second.calleesSet.clear();
        kv.second.calleesSet.rehash(0);
        kv.second.directWritesSet.clear();
        kv.second.directWritesSet.rehash(0);
    }

    UINFO(9, "undriven capture stats ftasks="
                 << g_stats.ftasks << " varWrites=" << g_stats.varWrites
                 << " callEdges=" << g_stats.callEdges << " uniqueTasks=" << m_info.size());
}

void V3UndrivenCapture::gather(AstNetlist* netlistp) {
    // Walk netlist and populate m_info with direct writes + call edges
    CaptureVisitor{*this, netlistp};
}

const V3UndrivenCapture::FTaskInfo* V3UndrivenCapture::find(const AstNodeFTask* taskp) const {
    const auto it = m_info.find(taskp);
    if (it == m_info.end()) return nullptr;
    return &it->second;
}

const std::vector<AstVar*>& V3UndrivenCapture::writeSummary(const AstNodeFTask* taskp) {
    // Ensure entry exists even if empty
    (void)m_info[taskp];
    return computeWriteSummary(taskp);
}

const std::vector<AstVar*>& V3UndrivenCapture::computeWriteSummary(const AstNodeFTask* taskp) {
    FTaskInfo& info = m_info[taskp];

    if (info.state == State::DONE) {
        UINFO(9, "undriven capture writeSummary cached size=" << info.writeSummary.size()
                                                              << " for " << taskNameQ(taskp));
        return info.writeSummary;
    }
    if (info.state == State::VISITING) {
        UINFO(9, "undriven capture recursion detected at "
                     << taskNameQ(taskp)
                     << " returning directWrites size=" << info.directWrites.size());
        // Cycle detected. return directWrites only to guarantee termination.
        if (info.writeSummary.empty()) info.writeSummary = info.directWrites;
        return info.writeSummary;
    }

    info.state = State::VISITING;

    info.writeSummary.clear();

    // Prevent duplicates across all sources that can contribute to a write summary (direct writes
    // and call chains)
    std::unordered_set<AstVar*> seen;

    // Simple lambda for filtering duplicates
    auto addVar = [&](AstVar* v) {
        if (seen.insert(v).second) info.writeSummary.push_back(v);
    };

    // Start with direct writes
    for (AstVar* v : info.directWrites) addVar(v);

    // Add callee summaries
    for (const AstNodeFTask* calleep : info.callees) {
        if (m_info.find(calleep) == m_info.end()) continue;
        const std::vector<AstVar*>& sub = computeWriteSummary(calleep);
        for (AstVar* v : sub) addVar(v);
    }

    UINFO(9, "undriven capture writeSummary computed size=" << info.writeSummary.size() << " for "
                                                            << taskNameQ(taskp));

    // We are done, so set the m_info state correctly and return the vector of variables
    info.state = State::DONE;
    return info.writeSummary;
}

void V3UndrivenCapture::noteTask(const AstNodeFTask* taskp) { (void)m_info[taskp]; }

void V3UndrivenCapture::noteDirectWrite(const AstNodeFTask* taskp, AstVar* varp) {
    FTaskInfo& info = m_info[taskp];

    // Exclude function return variable (not an externally visible side-effect)
    AstVar* const retVarp = VN_CAST(taskp->fvarp(), Var);
    if (retVarp && varp == retVarp) return;

    // Filter out duplicates.
    if (info.directWritesSet.insert(varp).second) { info.directWrites.push_back(varp); }
}

void V3UndrivenCapture::noteCallEdge(const AstNodeFTask* callerp, const AstNodeFTask* calleep) {
    FTaskInfo& callerInfo = m_info[callerp];
    // Prevents duplicate entries from being appended, if calleep already exists then insert will
    // return false, and then is not inserted into the callees vector.
    if (callerInfo.calleesSet.insert(calleep).second) { callerInfo.callees.push_back(calleep); }
    // Ensure callee entry exists, if already exists then this is a no-op.  unordered_map<> so
    // cheap.
    (void)m_info[calleep];
}

void V3UndrivenCapture::debugDumpTask(const AstNodeFTask* taskp, int level) const {
    const auto* const infop = find(taskp);
    if (!infop) {
        UINFO(level, "undriven capture no entry for task " << taskp);
        return;
    }
    UINFO(level, "undriven capture dump task " << taskp << " " << taskp->prettyNameQ()
                                               << " directWrites=" << infop->directWrites.size()
                                               << " callees=" << infop->callees.size()
                                               << " writeSummary=" << infop->writeSummary.size());
}
