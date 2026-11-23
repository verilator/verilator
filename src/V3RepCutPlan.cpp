// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Import and order RepCut partition memberships
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

// Parse external membership without trusting its ordering or completeness. Use
// ownership validation before deriving the exact ancestor closure for each phase.
// Topological sequences are inputs to bounded AST emission, not runtime MTasks.
//*************************************************************************

#include "V3PchAstNoMT.h"  // VL_MT_DISABLED_CODE_UNIT

#include "V3RepCutPlan.h"

#include "V3File.h"
#include "V3Stats.h"

#include <algorithm>
#include <fstream>
#include <memory>
#include <sstream>

VL_DEFINE_DEBUG_FUNCTIONS;

namespace {

bool parseLine(const std::string& line, size_t nodes, std::vector<size_t>& members,
               std::string& error) {
    size_t pos = 0;
    const auto skipSpace = [&]() {
        while (pos < line.size() && (line[pos] == ' ' || line[pos] == '\t' || line[pos] == '\r'))
            ++pos;
    };
    skipSpace();
    while (pos < line.size()) {
        if (line[pos] < '0' || line[pos] > '9') {
            error = "Expected decimal node ID";
            return false;
        }
        size_t id = 0;
        while (pos < line.size() && line[pos] >= '0' && line[pos] <= '9') {
            const size_t digit = line[pos++] - '0';
            if (id > (std::numeric_limits<size_t>::max() - digit) / 10) {
                error = "Node ID overflow";
                return false;
            }
            id = id * 10 + digit;
        }
        if (id >= nodes) {
            error = "Unknown node in membership";
            return false;
        }
        members.push_back(id);
        skipSpace();
        if (pos == line.size()) break;
        if (line[pos++] != ',') {
            error = "Expected comma after node ID";
            return false;
        }
        skipSpace();
    }
    return true;
}

// Finish each sink's dependency cone before starting the next. The global FIFO
// order is useful for closure, but leaves unrelated ready operations between
// producers and consumers. Postorder keeps those cones near each other without
// merging nodes or treating a control region as an indivisible scheduling unit.
// All evaluation nodes are pure; memory publication remains separately ordered.
size_t orderPhase(const V3RepCut::Graph& graph, std::vector<size_t>& sequence,
                  std::vector<bool>& visited) {
    for (const size_t id : sequence) visited[id] = false;
    std::vector<size_t> ordered;
    ordered.reserve(sequence.size());
    std::vector<std::pair<size_t, bool>> pending;
    for (const size_t root : sequence) {
        if (!graph.m_vertexps[root]->isSink()) continue;
        pending.emplace_back(root, false);
        while (!pending.empty()) {
            const size_t id = pending.back().first;
            const bool finish = pending.back().second;
            pending.pop_back();
            if (visited[id]) continue;
            if (finish) {
                visited[id] = true;
                ordered.push_back(id);
                continue;
            }
            pending.emplace_back(id, true);
            const size_t begin = pending.size();
            graph.m_vertexps[id]->foreachPredecessor(
                [&](const V3RepCut::Vertex& input, V3RepCut::DependencyKind) {
                    if (!visited[input.m_id]) pending.emplace_back(input.m_id, false);
                    return false;
                });
            // Visit operands in their stable edge order, including control edges.
            std::reverse(pending.begin() + begin, pending.end());
        }
    }
    UASSERT(ordered.size() == sequence.size(), "RepCut phase is not a sink closure");
    size_t changed = 0;
    for (size_t i = 0; i < sequence.size(); ++i) changed += sequence[i] != ordered[i];
    sequence.swap(ordered);
    return changed;
}

}  // namespace

bool V3RepCut::Plan::read(const Graph& graph, std::istream& input, Plan& result,
                          std::string& error) {
    result = Plan{};
    error.clear();
    std::vector<std::vector<size_t>> partitions;
    std::string line;
    while (std::getline(input, line)) {
        partitions.emplace_back();
        if (!parseLine(line, graph.m_vertexps.size(), partitions.back(), error)) {
            error = "Line " + cvtToStr(partitions.size()) + ": " + error;
            return false;
        }
    }
    if (!input.eof() || input.bad()) {
        error = "Cannot read membership file";
        return false;
    }
    Plan plan;
    if (!graph.ownership(partitions, plan.m_ownership, error)) return false;
    plan.order(graph, partitions);
    result = std::move(plan);
    return true;
}

void V3RepCut::Plan::order(const Graph& graph, std::vector<std::vector<size_t>>& partitions) {
    const std::vector<size_t> topo = graph.topologicalOrder();
    UASSERT(topo.size() == graph.m_vertexps.size(), "Validated graph must be acyclic");
    std::vector<size_t> rank(topo.size());
    for (size_t i = 0; i < topo.size(); ++i) rank[topo[i]] = i;
    std::vector<uint8_t> needed(topo.size(), 0);
    std::vector<bool> visited(topo.size(), false);
    size_t reordered = 0;
    static constexpr uint8_t NEXT_PHASE = 1;
    static constexpr uint8_t OUTPUT_PHASE = 2;
    for (std::vector<size_t>& members : partitions) {
        std::sort(members.begin(), members.end(),
                  [&rank](size_t a, size_t b) { return rank[a] < rank[b]; });
        // Reset only this partition's nodes, avoiding a nodes-by-partitions scan.
        for (const size_t id : members) {
            const Vertex* const vp = graph.m_vertexps[id];
            needed[id] = vp->m_kind == Op::OUTPUT ? OUTPUT_PHASE : vp->isSink() ? NEXT_PHASE : 0;
        }
        for (auto it = members.rbegin(); it != members.rend(); ++it) {
            graph.m_vertexps[*it]->foreachPredecessor([&](const Vertex& input, DependencyKind) {
                needed[input.m_id] |= needed[*it];
                return false;
            });
        }
        m_partitions.emplace_back();
        Partition& part = m_partitions.back();
        for (const size_t id : members) {
            if (needed[id] & NEXT_PHASE) part.m_next.push_back(id);
            if (needed[id] & OUTPUT_PHASE) part.m_output.push_back(id);
        }
        reordered += orderPhase(graph, part.m_next, visited);
        reordered += orderPhase(graph, part.m_output, visited);
    }
    V3Stats::addStat("RepCut plan, reordered phase nodes", reordered);
}

void V3RepCut::Plan::dump(const Graph& graph, const std::string& base) const {
    const std::unique_ptr<std::ofstream> planp{V3File::new_ofstream(base + ".plan.tsv")};
    const std::unique_ptr<std::ofstream> ownersp{V3File::new_ofstream(base + ".owners.tsv")};
    if (planp->fail() || ownersp->fail()) v3fatal("Cannot write RepCut plan files: " << base);
    *planp << "partition\tphase\tordinal\tnode\n";
    size_t nextNodes = 0;
    size_t outputNodes = 0;
    for (size_t p = 0; p < m_partitions.size(); ++p) {
        const Partition& part = m_partitions[p];
        for (size_t i = 0; i < part.m_next.size(); ++i)
            *planp << p << "\tnext\t" << i << '\t' << part.m_next[i] << '\n';
        for (size_t i = 0; i < part.m_output.size(); ++i)
            *planp << p << "\tnative_output_reference\t" << i << '\t' << part.m_output[i] << '\n';
        nextNodes += part.m_next.size();
        outputNodes += part.m_output.size();
    }
    *ownersp << "node\tstorage\tevaluation_owner\tpublication_owner\tpublication_order\n";
    std::vector<size_t> memoryOrder(graph.m_vertexps.size(), NO_ID);
    for (const std::vector<size_t>& writes : m_ownership.m_memoryWrites) {
        for (size_t i = 0; i < writes.size(); ++i) memoryOrder[writes[i]] = i;
    }
    for (const Vertex* const vp : graph.m_vertexps) {
        if (!vp->isSink()) continue;
        *ownersp << vp->m_id << '\t' << vp->m_storage << '\t';
        if (vp->m_kind == Op::OUTPUT)
            *ownersp << "native";
        else
            *ownersp << m_ownership.m_sinkOwners[vp->m_id];
        *ownersp << "\tnative\t";
        if (memoryOrder[vp->m_id] != NO_ID) *ownersp << memoryOrder[vp->m_id];
        *ownersp << '\n';
    }
    V3Stats::addStat("RepCut plan, partitions", m_partitions.size());
    V3Stats::addStat("RepCut plan, next phase nodes", nextNodes);
    V3Stats::addStat("RepCut plan, output phase nodes", outputNodes);
}

void V3RepCut::Plan::selfTest() {
    Graph graph;
    graph.m_storage = {{"input", 8, false, 0}, {"state", 8, false, 0}};
    graph.m_domains = {{"clock"}};
    Vertex* const inputp = graph.make(Op::INPUT, 8, false);
    inputp->m_storage = 0;
    Vertex* const oldp = graph.make(Op::OLD, 8, false);
    oldp->m_storage = 1;
    Vertex* const addp = graph.make(Op::ADD, 8, false, {inputp, oldp});
    Vertex* const nextp = graph.make(Op::NEXT, 8, false, {addp});
    nextp->m_storage = 1;
    nextp->m_domain = 0;
    Vertex* const outputp = graph.make(Op::OUTPUT, 8, false, {addp});
    outputp->m_storage = 1;
    Plan plan;
    std::string error;
    // Unsorted memberships, CRLF, a trailing comma and a truly empty worker.
    std::istringstream input{"3, 2, 1, 0, \r\n\r\n4,2,0,1"};
    UASSERT(read(graph, input, plan, error), error);
    UASSERT(plan.m_partitions.size() == 3 && plan.m_partitions[1].m_next.empty()
                && plan.m_partitions[1].m_output.empty(),
            "Empty partition lost");
    UASSERT(plan.m_partitions[0].m_next == (std::vector<size_t>{0, 1, 2, 3})
                && plan.m_partitions[0].m_output.empty(),
            "Incorrect next phase");
    UASSERT(plan.m_partitions[2].m_output == (std::vector<size_t>{0, 1, 2, 4})
                && plan.m_partitions[2].m_next.empty(),
            "Incorrect output phase");
    for (const char* const textp : {"-1", "+1", "0,,1", ",", "0 1", "1.0", "bogus",
                                    "99999999999999999999999999999999999999999999999999", "5", "",
                                    "0,1,2,3", "0,1,2,3,4,4"}) {
        std::istringstream invalid{textp};
        UASSERT(!read(graph, invalid, plan, error), "Invalid partition file accepted");
        UASSERT(!error.empty() && plan.m_partitions.empty()
                    && plan.m_ownership.m_sinkOwners.empty(),
                "Failed import retained stale plan");
    }
    std::istringstream failed;
    failed.setstate(std::ios::badbit);
    UASSERT(!read(graph, failed, plan, error), "Failed stream accepted");

    // Both phases need this predicate exclusively through a control edge. Its
    // late creation also proves ordering is independent of node IDs/CSV order.
    Vertex* const predicatep = graph.make(Op::INPUT, 1, false);
    graph.setRegion(addp, graph.makeRegion(NO_ID, predicatep, true));
    std::istringstream guarded{"3,2,1,0,5\n4,2,0,1,5"};
    UASSERT(read(graph, guarded, plan, error), error);
    UASSERT(plan.m_partitions[0].m_next == (std::vector<size_t>{0, 1, 5, 2, 3})
                && plan.m_partitions[0].m_output.empty()
                && plan.m_partitions[1].m_output == (std::vector<size_t>{0, 1, 5, 2, 4})
                && plan.m_partitions[1].m_next.empty(),
            "RepCut phase closure omitted a controlling predicate");
    std::istringstream missingGuard{"3,2,1,0\n4,2,0,1,5"};
    UASSERT(!read(graph, missingGuard, plan, error)
                && error == "Control dependency outside partition" && plan.m_partitions.empty(),
            "RepCut import accepted a missing controlling predicate");

    // Two independent cones are interleaved by FIFO readiness. Keep each cone
    // together, including a repeated operand, without changing its dependency.
    Graph local;
    Vertex* const ap = local.make(Op::INPUT, 8, false);
    Vertex* const bp = local.make(Op::INPUT, 8, false);
    Vertex* const twiceAp = local.make(Op::ADD, 8, false, {ap, ap});
    Vertex* const twiceBp = local.make(Op::ADD, 8, false, {bp, bp});
    local.make(Op::NEXT, 8, false, {twiceAp});
    local.make(Op::NEXT, 8, false, {twiceBp});
    std::vector<size_t> sequence = local.topologicalOrder();
    std::vector<bool> visited(sequence.size(), false);
    UASSERT(orderPhase(local, sequence, visited) != 0
                && sequence == (std::vector<size_t>{0, 2, 4, 1, 3, 5}),
            "RepCut local ordering did not finish independent cones");
    UASSERT(orderPhase(local, sequence, visited) == 0,
            "RepCut local ordering is not deterministic");
    sequence.clear();
    UASSERT(orderPhase(local, sequence, visited) == 0, "Empty RepCut phase gained nodes");
}
