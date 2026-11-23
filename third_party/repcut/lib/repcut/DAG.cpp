#include "DAG.h"
#include "Log.h"
#include "StringUtils.h"

#include <cassert>
#include <cerrno>
#include <chrono>
#include <cmath>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <fstream>
#include <limits>
#include <string>

using namespace repcut;

// Parse uint32_t from string_view using strto* (no std::string alloc,
// no exceptions).  On failure, logs and returns false; the out-param is
// left untouched.
static bool parse_uint(std::string_view tok, size_t lineno, const char* what, RepCutLogLevel ll, uint32_t& out)
{
    std::string buf(tok); // strto* needs NUL-terminated
    char* end = nullptr;
    errno = 0;
    long v = std::strtol(buf.c_str(), &end, 10);
    if (errno != 0 || end == buf.c_str() || *end != '\0' || v < 0 || static_cast<unsigned long>(v) > UINT32_MAX) {
        rcp_log(ll, REPCUT_LOG_ERROR, "Invalid %s at line %zu: '%.*s'\n", what, lineno, static_cast<int>(tok.size()),
                tok.data());
        return false;
    }
    out = static_cast<uint32_t>(v);
    return true;
}

static bool parse_float(std::string_view tok, size_t lineno, const char* what, RepCutLogLevel ll, float& out)
{
    std::string buf(tok);
    char* end = nullptr;
    errno = 0;
    float v = std::strtof(buf.c_str(), &end);
    if (errno != 0 || end == buf.c_str() || *end != '\0') {
        rcp_log(ll, REPCUT_LOG_ERROR, "Invalid %s at line %zu: '%.*s'\n", what, lineno, static_cast<int>(tok.size()),
                tok.data());
        return false;
    }
    out = v;
    return true;
}

bool DirectedAcyclicGraph::buildFromFile(const char* filename)
{
    rcp_log(log_level, REPCUT_LOG_DEBUG, "Build DAG from file: Start\n");
    auto start = std::chrono::system_clock::now();

    std::ifstream file(filename);
    if (!file) {
        rcp_log(log_level, REPCUT_LOG_ERROR, "Cannot open graph file %s\n", filename);
        return false;
    }
    std::string line;
    size_t lineno = 0;

    while (std::getline(file, line)) {
        TokenView tv(line);

        if (lineno == 0) {
            // header: numEdges numNodes
            auto a = tv.next();
            auto b = tv.next();
            if (a.empty() || b.empty()) {
                rcp_log(log_level, REPCUT_LOG_ERROR, "Incorrect header at line %zu: %s\n", lineno, line.c_str());
                return false;
            }
            uint32_t numEdges = 0, numNodes = 0;
            if (!parse_uint(a, lineno, "numEdges", log_level, numEdges))
                return false;
            if (!parse_uint(b, lineno, "numNodes", log_level, numNodes))
                return false;
            if (numNodes == std::numeric_limits<size_t>::max()) {
                rcp_log(log_level, REPCUT_LOG_ERROR, "Too many vertices for adjacency offsets\n");
                return false;
            }

            weight.assign(numNodes, 0);
            valid.assign(numNodes, false);
            sinkNodes.clear();
            inNeigh.offsets_.assign(static_cast<size_t>(numNodes) + 1, 0);
            outNeigh.offsets_.assign(static_cast<size_t>(numNodes) + 1, 0);
            inNeigh.neighbors_.clear();
            outNeigh.neighbors_.clear();
            // The header count is a capacity hint; actual edges determine the
            // row offsets, including when invalid vertices have ignored edges.
            outNeigh.neighbors_.reserve(numEdges);
        }
        else {
            // line: Label Weight out0 out1 ...
            auto label_tok = tv.next();
            auto weight_tok = tv.next();
            if (label_tok.empty() || weight_tok.empty()) {
                rcp_log(log_level, REPCUT_LOG_ERROR, "Too few token(s) at line %zu: %s\n", lineno, line.c_str());
                return false;
            }

            const size_t node_id = lineno - 1;
            if (node_id >= numVertices()) {
                rcp_log(log_level, REPCUT_LOG_ERROR, "Too many vertices at line %zu\n", lineno);
                return false;
            }
            float node_weight = 0;
            if (!parse_float(weight_tok, lineno, "node weight", log_level, node_weight))
                return false;

            if (node_weight < 0) {
                weight[node_id] = 0;
                valid[node_id] = false;
            }
            else {
                weight[node_id] = node_weight;
                valid[node_id] = true;
                while (!tv.done()) {
                    auto tok = tv.next();
                    uint32_t dst = 0;
                    if (!parse_uint(tok, lineno, "node id", log_level, dst))
                        return false;
                    if (dst >= numVertices()) {
                        rcp_log(log_level, REPCUT_LOG_ERROR, "Node id %u is out of range at line %zu\n", dst, lineno);
                        return false;
                    }
                    outNeigh.neighbors_.push_back(dst);
                    ++inNeigh.offsets_[static_cast<size_t>(dst) + 1];
                }
            }
            outNeigh.offsets_[node_id + 1] = outNeigh.neighbors_.size();
        }

        lineno++;
    }

    if (!file.eof()) {
        rcp_log(log_level, REPCUT_LOG_ERROR, "Cannot read graph file %s\n", filename);
        return false;
    }
    if (lineno == 0 || lineno - 1 != numVertices()) {
        rcp_log(log_level, REPCUT_LOG_ERROR, "Graph vertex count does not match its header\n");
        return false;
    }

    buildIncoming();

    auto stop = std::chrono::system_clock::now();
    auto duration = std::chrono::duration_cast<std::chrono::milliseconds>(stop - start);
    rcp_log(log_level, REPCUT_LOG_DEBUG, "Build DAG from file: Done in %llums\n", duration.count());
    return true;
}

bool DirectedAcyclicGraph::buildFromMemory(const RepCutGraph& graph)
{
    const size_t n = graph.num_vertices;
    if (!graph.offsets || (n && !graph.weights) || (graph.num_edges && !graph.neighbors)
        || n == std::numeric_limits<size_t>::max() || graph.offsets[0] != 0
        || graph.offsets[n] != graph.num_edges) {
        rcp_log(log_level, REPCUT_LOG_ERROR, "Invalid graph arrays\n");
        return false;
    }
    for (size_t i = 0; i < n; ++i) {
        if (!std::isfinite(graph.weights[i]) || graph.offsets[i] > graph.offsets[i + 1]
            || graph.offsets[i + 1] > graph.num_edges) {
            rcp_log(log_level, REPCUT_LOG_ERROR, "Invalid graph weight or offset\n");
            return false;
        }
    }
    for (size_t i = 0; i < graph.num_edges; ++i) {
        if (graph.neighbors[i] >= n) {
            rcp_log(log_level, REPCUT_LOG_ERROR, "Graph neighbor out of range\n");
            return false;
        }
    }
    weight.assign(n, 0);
    valid.assign(n, false);
    sinkNodes.clear();
    inNeigh.offsets_.assign(n + 1, 0);
    outNeigh.offsets_.assign(n + 1, 0);
    outNeigh.neighbors_.clear();
    outNeigh.neighbors_.reserve(graph.num_edges);
    for (size_t src = 0; src < n; ++src) {
        if (graph.weights[src] >= 0) {
            weight[src] = graph.weights[src];
            valid[src] = true;
            for (size_t i = graph.offsets[src]; i < graph.offsets[src + 1]; ++i) {
                const uint32_t dst = graph.neighbors[i];
                outNeigh.neighbors_.push_back(dst);
                ++inNeigh.offsets_[static_cast<size_t>(dst) + 1];
            }
        }
        outNeigh.offsets_[src + 1] = outNeigh.neighbors_.size();
    }
    buildIncoming();
    return true;
}

void DirectedAcyclicGraph::buildIncoming()
{
    const auto n = numVertices();
    for (size_t vertex = 1; vertex <= n; ++vertex) {
        inNeigh.offsets_[vertex] += inNeigh.offsets_[vertex - 1];
    }
    inNeigh.neighbors_.resize(outNeigh.neighbors_.size());
    // Fill incoming rows in source order, matching the file parser's original
    // insertion order. Reuse row starts as cursors, then shift the resulting
    // row ends back into place; no extra per-vertex cursor array is needed.
    for (uint32_t src = 0; src < n; ++src) {
        for (const auto dst : outNeigh[src]) {
            inNeigh.neighbors_[inNeigh.offsets_[dst]++] = src;
        }
    }
    for (size_t vertex = n; vertex > 0; --vertex) {
        inNeigh.offsets_[vertex] = inNeigh.offsets_[vertex - 1];
    }
    inNeigh.offsets_[0] = 0;

}

void DirectedAcyclicGraph::findSinkNodes()
{
    rcp_log(log_level, REPCUT_LOG_DEBUG, "Find all sink vtxs: Start\n");
    auto start = std::chrono::system_clock::now();

    const auto n = numVertices();
    sinkNodes.clear();
    for (uint32_t nid = 0; nid < n; nid++) {
        if (valid[nid] && outNeigh[nid].empty())
            sinkNodes.push_back(nid);
    }
    rcp_log(log_level, REPCUT_LOG_INFO, "Found %zu sink nodes\n", sinkNodes.size());

    auto stop = std::chrono::system_clock::now();
    auto duration = std::chrono::duration_cast<std::chrono::milliseconds>(stop - start);
    rcp_log(log_level, REPCUT_LOG_DEBUG, "Find all sink vtxs: Done in %llums\n", duration.count());
}
