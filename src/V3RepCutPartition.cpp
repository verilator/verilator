// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Partition the RepCut graph with the bundled library
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
//
// Automatic partitioning runs while the exported graph still has live AST
// bindings. Use one partition per simulation thread and one partitioner thread.
// A single partition or empty graph needs no hypergraph partitioning. Each
// hierarchical model has its own graph. The linked API exchanges graphs and
// memberships in memory; file exchange is reserved for diagnostics and overrides.
// Never accept stale output from a failed invocation, and validate generated
// membership before emitting code.
//*************************************************************************

#include "V3PchAstNoMT.h"  // VL_MT_DISABLED_CODE_UNIT

#include "V3File.h"
#include "V3Os.h"
#include "V3RepCutPlan.h"
#include "V3Stats.h"
#include "V3String.h"

#include "repcut.h"

#include <algorithm>
#include <cerrno>
#include <cstdio>
#include <fstream>
#include <limits>
#include <memory>

namespace {

// V3Os::system uses the host shell. Quote every path as one literal argument;
// generated model directories and user-selected executables may contain spaces
// or shell metacharacters. Only explicit external overrides use a POSIX shell.
std::string shellArg(const std::string& text) {
    return "'" + VString::replaceSubstr(text, "'", "'\\''") + "'";
}

// With no more sinks than threads, each complete sink cone can have its own
// worker. This also handles empty models and avoids asking the hypergraph
// partitioner to split tiny, edgeless inputs. A generation tag avoids clearing
// a graph-sized membership vector for each worker.
void trivialPartitions(const V3RepCut::Graph& graph, const std::vector<size_t>& sinks,
                       size_t threads, std::vector<std::vector<size_t>>& partitions) {
    partitions.resize(threads);
    if (threads == 1) {
        for (const V3RepCut::Vertex* const vp : graph.m_vertexps)
            partitions[0].push_back(vp->m_id);
        return;
    }
    std::vector<size_t> visited(graph.m_vertexps.size(), V3RepCut::NO_ID);
    for (size_t p = 0; p < threads; ++p) {
        std::vector<size_t> pending;
        std::vector<size_t>& members = partitions[p];
        if (p < sinks.size()) pending.push_back(sinks[p]);
        while (!pending.empty()) {
            const size_t id = pending.back();
            pending.pop_back();
            if (visited[id] == p) continue;
            visited[id] = p;
            members.push_back(id);
            graph.m_vertexps[id]->foreachPredecessor(
                [&](const V3RepCut::Vertex& input, V3RepCut::DependencyKind) {
                    pending.push_back(input.m_id);
                    return false;
                });
        }
        std::sort(members.begin(), members.end());
    }
}

// The callback borrows RCP's result only for this call; copy into the plan input.
int collectPartition(void* userp, uint32_t partition, const uint32_t* membersp, size_t count) {
    auto& partitions = *static_cast<std::vector<std::vector<size_t>>*>(userp);
    if (partition != partitions.size()) return 1;
    partitions.emplace_back();
    if (count) partitions.back().assign(membersp, membersp + count);
    return 0;
}

}  // namespace

bool V3RepCut::Plan::partition(const Graph& graph, const std::string& base, Plan& result,
                               std::string& error) {
    if (graph.m_report.m_failures) {
        error = "Graph is incomplete or cyclic";
        return false;
    }
    const std::string directory = base + ".partition";
    const std::string filename = directory + "/rcp_output.txt";
    const std::string log = base + ".partition.log";
    const int threads = v3Global.opt.threads();
    const bool dump = v3Global.opt.repcutDumpGraph();
    const bool external = !v3Global.opt.repcutPartitioner().empty();
    if (dump || external) V3Os::createDir(directory);
    if ((dump || external) && std::remove(filename.c_str()) != 0 && errno != ENOENT) {
        error = "Cannot remove stale partitioner output '" + filename + "'";
        return false;
    }
    std::vector<size_t> sinks;
    for (const Vertex* const vp : graph.m_vertexps) {
        if (!vp->isSink()) continue;
        sinks.push_back(vp->m_id);
        if (sinks.size() > static_cast<size_t>(threads)) break;
    }
    std::vector<std::vector<size_t>> partitions;
    const bool trivial = threads == 1 || sinks.size() <= static_cast<size_t>(threads);
    if (trivial) {
        trivialPartitions(graph, sinks, threads, partitions);
    } else if (external) {
        const std::string command = shellArg(v3Global.opt.repcutPartitioner()) + " --graph_file "
                                    + shellArg(base + ".graph") + " --work_directory "
                                    + shellArg(directory) + " --nparts " + cvtToStr(threads)
                                    + " --threads 1 --seed " + cvtToStr(v3Global.opt.repcutSeed())
                                    + " --target_ib 0.03 > " + shellArg(log) + " 2>&1";
        const int status = V3Os::system(command);
        if (status) {
            error = "Partitioner exited with status " + cvtToStr(status) + "; see '" + log
                    + "'. Check the executable selected with --repcut-partitioner";
            return false;
        }
        V3File::addTgtDepend(filename);
        V3File::addTgtDepend(log);
    } else {
        if (graph.m_vertexps.size() > std::numeric_limits<uint32_t>::max()) {
            error = "Too many vertices for the bundled partitioner";
            return false;
        }
        std::vector<float> weights;
        weights.reserve(graph.m_vertexps.size());
        std::vector<size_t> offsets{0};
        offsets.reserve(graph.m_vertexps.size() + 1);
        std::vector<uint32_t> neighbors;
        for (const Vertex* const vp : graph.m_vertexps) {
            weights.push_back(vp->zeroCost() ? 0.0F : 1.0F);
            for (const V3GraphEdge& edge : vp->outEdges()) {
                neighbors.push_back(static_cast<const Vertex*>(edge.top())->m_id);
            }
            offsets.push_back(neighbors.size());
        }
        const RepCutGraph input{static_cast<uint32_t>(weights.size()), neighbors.size(),
                                weights.data(), offsets.data(), neighbors.data()};
        RepCutContext context{};
        context.work_directory = directory.c_str();
        context.nparts = threads;
        context.target_ib = 0.03F;
        context.parallel_threads = 1;
        context.seed = v3Global.opt.repcutSeed();
        context.save_intermediate_files = dump;
        const int status
            = repcut_run_graph(&context, &input, collectPartition, &partitions, nullptr);
        if (dump) {
            const std::unique_ptr<std::ofstream> outputp{V3File::new_ofstream(log)};
            *outputp << "Bundled RepCut: seed " << context.seed << ", partitions " << threads
                     << ", partitioner threads 1, status " << status << '\n';
            outputp->close();
            if (outputp->fail()) {
                error = "Cannot write partitioner log '" + log + "'";
                return false;
            }
        }
        if (status) {
            error = "Bundled RepCut failed with status " + cvtToStr(status)
                    + "; see the preceding partitioner diagnostic"
                    + (dump ? " and '" + log + "'" : "");
            return false;
        }
    }
    if ((dump || external) && (trivial || !external)) {
        const std::unique_ptr<std::ofstream> outputp{V3File::new_ofstream(filename)};
        for (const std::vector<size_t>& members : partitions) {
            for (const size_t id : members) *outputp << id << ',';
            *outputp << '\n';
        }
        outputp->close();
        if (outputp->fail()) {
            error = "Cannot write automatic membership '" + filename + "'";
            return false;
        }
    }
    V3Stats::addStat("RepCut, partitioning seed", v3Global.opt.repcutSeed());
    if (external && !trivial) {
        std::ifstream input{filename};
        if (!read(graph, input, result, error)) return false;
    } else if (!build(graph, std::move(partitions), result, error)) {
        return false;
    }
    if (result.m_partitions.size() != static_cast<size_t>(threads)) {
        error = "Partitioner returned " + cvtToStr(result.m_partitions.size()) + " partitions for "
                + cvtToStr(threads) + " threads";
        result = Plan{};
        return false;
    }
    return true;
}
