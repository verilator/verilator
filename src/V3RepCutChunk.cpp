// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Bound RepCut compilation chunks with storage spans
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2026-2026 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

// Count conservative first/last-reference spans of written private values at
// each legal statement boundary. A sliding-window dynamic program minimizes
// chunk count first, then summed span bytes, with deterministic tie breaking.
// Each candidate enters/leaves a heap at most once: O(N log N) work and O(N)
// storage. Statements, guards and memory-write order never move or change.
// Generated RepCut callees contribute their access spans under a fixed analysis
// budget. Other opaque statements fall back to the existing greedy split.
//*************************************************************************

#include "V3PchAstNoMT.h"  // VL_MT_DISABLED_CODE_UNIT

#include "V3RepCutChunk.h"

#include <algorithm>
#include <map>
#include <queue>
#include <set>

namespace {

class SpanAnalysis final : public VNVisitorConst {
    struct Span final {
        size_t m_first = 0;  // First statement accessing this variable
        size_t m_last = 0;  // Last statement accessing this variable
        bool m_read = false;  // The access span includes a read
        bool m_write = false;  // The access span includes a write
    };
    std::map<const AstVarScope*, Span> m_spans;
    size_t m_index = 0;
    bool m_safe = true;
    // Bound extra traversal independently of phase size, including nested calls.
    // Exceeding the budget changes only boundary selection, never semantics.
    static constexpr size_t MAX_CALLEE_NODES = 65536;
    size_t m_calleeBudget = MAX_CALLEE_NODES;
    std::set<const AstCFunc*> m_seenCallees;

    void visit(AstVarRef* nodep) override {
        const AstVarScope* const vscp = nodep->varScopep();
        if (!vscp || nodep->classOrPackagep()) {
            m_safe = false;
            return;
        }
        const AstVar* const varp = vscp->varp();
        if (!varp->isInternal() || varp->isSigPublic()
            || !varp->dtypep()->skipRefp()->isIntegralOrPacked())
            return;
        const auto it = m_spans.emplace(vscp, Span{m_index, m_index, false, false}).first;
        Span& span = it->second;
        span.m_last = m_index;
        span.m_read |= nodep->access().isReadOrRW();
        span.m_write |= nodep->access().isWriteOrRW();
    }
    void visit(AstAssign* nodep) override { iterateChildrenConst(nodep); }
    void visit(AstIf* nodep) override { iterateChildrenConst(nodep); }
    void visit(AstStmtExpr* nodep) override {
        if (!VN_IS(nodep->exprp(), CCall)) {
            m_safe = false;
            return;
        }
        iterateChildrenConst(nodep);
    }
    void visit(AstCCall* nodep) override {
        const AstCFunc* const funcp = nodep->funcp();
        if (!funcp->isRepCut()) {
            m_safe = false;
            return;
        }
        iterateChildrenConst(nodep);
        // Repeated/nested references in one statement have the same span index.
        if (!m_seenCallees.insert(funcp).second) return;
        const size_t nodes = funcp->nodeCount();
        if (nodes > m_calleeBudget) {
            m_safe = false;
            return;
        }
        m_calleeBudget -= nodes;
        for (AstNode* stmtp = funcp->stmtsp(); stmtp; stmtp = stmtp->nextp()) iterateConst(stmtp);
    }
    void visit(AstNodeStmt*) override { m_safe = false; }
    void visit(AstNodeExpr* nodep) override {
        if (!nodep->isPure()) m_safe = false;
        iterateChildrenConst(nodep);
    }
    void visit(AstNode* nodep) override { iterateChildrenConst(nodep); }

public:
    SpanAnalysis(const std::vector<AstNodeStmt*>& statements, V3RepCut::ChunkPlan& plan) {
        const size_t n = statements.size();
        plan.m_liveValues.resize(n + 1, 0);
        plan.m_liveBytes.resize(n + 1, 0);
        for (m_index = 0; m_index < n && m_safe; ++m_index) {
            m_seenCallees.clear();
            iterateConst(statements[m_index]);
        }
        plan.m_analyzed = m_safe;
        if (!m_safe) return;
        // Difference arrays avoid visiting each boundary for every long span.
        std::vector<int64_t> values(n + 1, 0);
        std::vector<int64_t> bytes(n + 1, 0);
        for (const auto& pair : m_spans) {
            const Span& span = pair.second;
            if (!span.m_read || !span.m_write || span.m_first == span.m_last) continue;
            const int64_t width = pair.first->dtypep()->widthTotalBytes();
            ++values[span.m_first + 1];
            --values[span.m_last + 1];
            bytes[span.m_first + 1] += width;
            bytes[span.m_last + 1] -= width;
        }
        int64_t liveValues = 0;
        int64_t liveBytes = 0;
        for (size_t i = 0; i <= n; ++i) {
            liveValues += values[i];
            liveBytes += bytes[i];
            UASSERT(liveValues >= 0 && liveBytes >= 0, "Invalid RepCut storage span");
            plan.m_liveValues[i] = liveValues;
            plan.m_liveBytes[i] = liveBytes;
        }
    }
};

struct Choice final {
    size_t m_chunks;  // Number of chunks in this candidate prefix
    uint64_t m_bytes;  // Accumulated live-byte cost at its boundaries
    size_t m_start;  // Start boundary of the last chunk
};
struct LaterChoice final {
    bool operator()(const Choice& a, const Choice& b) const {
        if (a.m_chunks != b.m_chunks) return a.m_chunks > b.m_chunks;
        if (a.m_bytes != b.m_bytes) return a.m_bytes > b.m_bytes;
        // Equal-cost plans prefer filling earlier chunks, as greedy does.
        return a.m_start < b.m_start;
    }
};

std::vector<size_t> selectEnds(const std::vector<size_t>& prefix,
                               const std::vector<uint64_t>& bytes, size_t limit) {
    const size_t n = prefix.size() - 1;
    std::vector<size_t> chunks(n + 1, 0);
    std::vector<uint64_t> costs(n + 1, 0);
    std::vector<size_t> previous(n + 1, 0);
    std::priority_queue<Choice, std::vector<Choice>, LaterChoice> choices;
    size_t first = 0;
    for (size_t end = 1; end <= n; ++end) {
        const size_t start = end - 1;
        choices.push({chunks[start], costs[start] + bytes[start], start});
        while (prefix[end] - prefix[first] > limit) ++first;
        while (!choices.empty() && choices.top().m_start < first) choices.pop();
        UASSERT(!choices.empty(), "RepCut chunk has no legal starting boundary");
        const Choice& best = choices.top();
        chunks[end] = best.m_chunks + 1;
        costs[end] = best.m_bytes;
        previous[end] = best.m_start;
    }
    std::vector<size_t> result;
    for (size_t end = n; end; end = previous[end]) result.push_back(end);
    std::reverse(result.begin(), result.end());
    return result;
}

}  // namespace

V3RepCut::ChunkPlan V3RepCut::planChunks(const std::vector<AstNodeStmt*>& statements,
                                         const std::vector<size_t>& sizes, size_t limit) {
    UASSERT(statements.size() == sizes.size(), "RepCut statement sizes changed");
    ChunkPlan plan;
    plan.m_prefixNodes.push_back(0);
    size_t groupSize = 0;
    for (size_t i = 0; i < sizes.size(); ++i) {
        UASSERT(sizes[i] && sizes[i] <= limit, "RepCut atomic statement exceeds chunk budget");
        plan.m_prefixNodes.push_back(plan.m_prefixNodes.back() + sizes[i]);
        if (groupSize && groupSize + sizes[i] > limit) {
            plan.m_greedyEnds.push_back(i);
            groupSize = 0;
        }
        groupSize += sizes[i];
    }
    if (!sizes.empty()) plan.m_greedyEnds.push_back(sizes.size());
    SpanAnalysis{statements, plan};
    plan.m_ends = plan.m_analyzed ? selectEnds(plan.m_prefixNodes, plan.m_liveBytes, limit)
                                  : plan.m_greedyEnds;
    UASSERT(plan.m_ends.size() == plan.m_greedyEnds.size(), "RepCut increased chunk count");
    return plan;
}

void V3RepCut::selfTestChunks(AstScope& scope) {
    // A zero-cost earlier boundary must win without increasing the chunk count.
    UASSERT(selectEnds({0, 4, 8, 12, 16}, {0, 0, 16, 0, 0}, 12) == std::vector<size_t>({3, 4}),
            "RepCut lost deterministic chunk tie breaking");
    UASSERT(selectEnds({0, 4, 8, 12, 16}, {0, 0, 16, 8, 0}, 12) == std::vector<size_t>({1, 4}),
            "RepCut did not avoid a live chunk boundary");
    // Do not trade an extra compilation call for cheaper boundaries.
    UASSERT(selectEnds({0, 4, 8, 12, 16}, {0, 0, 100, 0, 0}, 8) == std::vector<size_t>({2, 4}),
            "RepCut increased the minimum chunk count");
    UASSERT(selectEnds({0}, {0}, 32).empty(), "RepCut created an empty chunk");

    // Compare with every legal split of small streams, including expired heap
    // entries and equal-cost alternatives. This oracle does not use the DP.
    uint32_t random = 17;
    for (size_t sample = 0; sample < 64; ++sample) {
        std::vector<size_t> prefix{0};
        std::vector<uint64_t> bytes{0};
        for (size_t i = 0; i < 8; ++i) {
            random = random * 1664525U + 1013904223U;
            prefix.push_back(prefix.back() + 1 + random % 5);
            bytes.push_back((random >> 8) % 32);
        }
        bytes.back() = 0;
        const std::vector<size_t> ends = selectEnds(prefix, bytes, 8);
        uint64_t cost = 0;
        for (const size_t end : ends) cost += bytes[end];
        size_t bestCount = 9;
        uint64_t bestCost = 0;
        for (size_t mask = 0; mask < 128; ++mask) {
            size_t begin = 0;
            size_t count = 0;
            uint64_t trialCost = 0;
            bool valid = true;
            for (size_t end = 1; end <= 8; ++end) {
                if (end != 8 && !(mask & (size_t{1} << (end - 1)))) continue;
                valid &= prefix[end] - prefix[begin] <= 8;
                ++count;
                trialCost += bytes[end];
                begin = end;
            }
            if (valid && (count < bestCount || (count == bestCount && trialCost < bestCost))) {
                bestCount = count;
                bestCost = trialCost;
            }
        }
        UASSERT(ends.size() == bestCount && cost == bestCost,
                "RepCut chunk plan differs from exhaustive minimum");
    }

    FileLine* const flp = scope.fileline();
    AstVarScope* const inputp
        = v3Global.rootp()->topScopep()->createTemp("__Vrepcut_chunk_input", 7);
    AstVarScope* const valuep
        = v3Global.rootp()->topScopep()->createTemp("__Vrepcut_chunk_value", 95);
    AstVarScope* const outputp
        = v3Global.rootp()->topScopep()->createTemp("__Vrepcut_chunk_output", 95);
    inputp->varp()->isInternal(true);
    valuep->varp()->isInternal(true);
    outputp->varp()->isInternal(true);
    const auto read = [&](AstVarScope* vscp) { return new AstVarRef{flp, vscp, VAccess::READ}; };
    const auto assign = [&](AstVarScope* dstp, AstNodeExpr* rhsp) {
        return new AstAssign{flp, new AstVarRef{flp, dstp, VAccess::WRITE}, rhsp};
    };
    std::vector<AstNodeStmt*> statements{
        assign(valuep, new AstConst{flp, AstConst::WidthedValue{}, 95, 0}),
        new AstIf{flp, read(inputp),
                  assign(outputp, new AstAdd{flp, read(valuep), read(valuep)})}};
    const ChunkPlan plan = planChunks(statements, {4, 8}, 8);
    UASSERT(plan.m_analyzed && plan.m_liveValues == std::vector<uint64_t>({0, 1, 0})
                && plan.m_liveBytes == std::vector<uint64_t>({0, 12, 0}),
            "RepCut missed a guarded wide-value storage span or counted an unwritten input");
    valuep->varp()->sigPublic(true);
    const ChunkPlan external = planChunks(statements, {4, 8}, 8);
    UASSERT(external.m_liveValues == std::vector<uint64_t>({0, 0, 0}),
            "RepCut counted externally visible state as a private intermediate");
    for (AstNodeStmt* const stmtp : statements) stmtp->deleteTree();
    valuep->varp()->sigPublic(false);
    statements = {assign(inputp, new AstConst{flp, AstConst::WidthedValue{}, 7, 1}),
                  assign(outputp, new AstConst{flp, AstConst::WidthedValue{}, 95, 0}),
                  assign(valuep, new AstConst{flp, AstConst::WidthedValue{}, 95, 2}),
                  assign(outputp, read(valuep))};
    std::vector<size_t> sizes;
    for (const AstNodeStmt* const stmtp : statements) sizes.push_back(stmtp->nodeCount());
    const ChunkPlan measured = planChunks(statements, sizes, sizes[0] + sizes[1] + sizes[2]);
    UASSERT(measured.m_greedyEnds == std::vector<size_t>({3, 4})
                && measured.m_ends == std::vector<size_t>({2, 4}) && measured.m_liveBytes[3] == 12
                && measured.m_liveBytes[2] == 0,
            "RepCut did not use measured storage spans for chunking");
    for (AstNodeStmt* const stmtp : statements) stmtp->deleteTree();
    statements = {new AstCStmt{flp, "opaque();"}};
    const ChunkPlan opaque = planChunks(statements, {2}, 32);
    UASSERT(!opaque.m_analyzed && opaque.m_ends == opaque.m_greedyEnds,
            "RepCut analyzed opaque chunk accesses");
    statements.front()->deleteTree();
    // Outlining an oversized guard must not hide its boundary values from the
    // surrounding phase. Include repeated callees at each statement index.
    AstCFunc* const leafp = new AstCFunc{flp, "__Vrepcut_chunk_leaf", &scope};
    leafp->isRepCut(true);
    leafp->addStmtsp(assign(outputp, read(valuep)));
    const auto call = [&](AstCFunc* funcp) {
        AstCCall* const callp = new AstCCall{flp, funcp};
        callp->dtypeSetVoid();
        return callp->makeStmt();
    };
    AstCFunc* const wrapperp = new AstCFunc{flp, "__Vrepcut_chunk_wrapper", &scope};
    wrapperp->isRepCut(true);
    wrapperp->addStmtsp(call(leafp));
    wrapperp->addStmtsp(call(leafp));
    statements = {assign(valuep, new AstConst{flp, AstConst::WidthedValue{}, 95, 1}),
                  call(wrapperp), new AstIf{flp, read(inputp), call(wrapperp)}};
    const ChunkPlan calls = planChunks(statements, {4, 2, 5}, 8);
    UASSERT(calls.m_analyzed && calls.m_liveValues == std::vector<uint64_t>({0, 1, 1, 0})
                && calls.m_liveBytes == std::vector<uint64_t>({0, 12, 12, 0}),
            "RepCut lost accesses through nested or repeated generated calls");
    leafp->isRepCut(false);
    const ChunkPlan unknown = planChunks(statements, {4, 2, 5}, 8);
    UASSERT(!unknown.m_analyzed && unknown.m_ends == unknown.m_greedyEnds,
            "RepCut followed an opaque callee through a generated wrapper");
    for (AstNodeStmt* const stmtp : statements) stmtp->deleteTree();
    wrapperp->deleteTree();
    leafp->deleteTree();
    VNDeleter deleter;
    for (AstVarScope* const vscp : {inputp, valuep, outputp}) {
        AstVar* const varp = vscp->varp();
        deleter.pushDeletep(vscp->unlinkFrBack());
        deleter.pushDeletep(varp->unlinkFrBack());
    }
}
