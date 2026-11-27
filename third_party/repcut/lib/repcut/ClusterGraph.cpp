#include "ClusterGraph.h"
#include "ConeTrie.h"
#include "Log.h"

#include <algorithm>
#include <cassert>
#include <chrono>
#include <cmath>
#include <fstream>
#include <limits>
#include <numeric>
#include <stdexcept>
#include <string>
#include <unordered_map>
#include <vector>

using namespace repcut;

// Phase A: for each sink BFS upstream, descending each vertex one level
// deeper in the cone-id trie.  After this pass every vertex stores a
// trie leaf whose path is its cone-id set.  Vertices with the same set of
// cones share the same leaf id.
void ClusterGraph::_mark_cones()
{
    rcp_log(log_level, REPCUT_LOG_DEBUG, "Mark cones: Start\n");
    auto start = std::chrono::system_clock::now();

    const auto numVtxes = dag->numVertices();
    const auto numSinks = dag->sinkNodes.size();
    if (numSinks == 0 && std::any_of(dag->valid.begin(), dag->valid.end(), [](bool valid) { return valid; }))
        throw std::invalid_argument("Graph contains valid nodes but no sinks");

    coneTrie = std::make_unique<ConeTrie>();
    vtxToNode.assign(numVtxes, coneTrie->root());

    std::vector<uint32_t> fringe;
    std::vector<uint32_t> fringeNext;

    // Cones are processed in strictly increasing cone-id order, so each
    // vertex's root-to-leaf trie path is its canonical (sorted, unique)
    // cone-id set.  See the ordering invariant in include/ConeTrie.h.
    // Do not parallelize this loop without re-establishing that invariant.
    for (uint32_t cone_id = 0; cone_id < numSinks; ++cone_id) {
        const uint32_t seed = dag->sinkNodes[cone_id];

        fringe.clear();

        fringe.push_back(seed);
        vtxToNode[seed] = coneTrie->visit(vtxToNode[seed], cone_id);

        while (!fringe.empty()) {
            fringeNext.clear();
            for (const auto vtx : fringe) {
                for (const auto nid : dag->inNeigh[vtx]) {
                    if (!dag->valid[nid])
                        continue;
                    // The trie leaf already records the last cone visited.
                    // An unchanged leaf means this vertex was queued earlier.
                    const auto leaf = coneTrie->visit(vtxToNode[nid], cone_id);
                    if (leaf != vtxToNode[nid]) {
                        vtxToNode[nid] = leaf;
                        fringeNext.push_back(nid);
                    }
                }
            }
            std::swap(fringe, fringeNext);
        }
    }

    auto stop = std::chrono::system_clock::now();
    auto duration = std::chrono::duration_cast<std::chrono::milliseconds>(stop - start);
    rcp_log(log_level, REPCUT_LOG_DEBUG, "Mark cones: Done in %llums (trie nodes = %zu)\n", duration.count(),
            coneTrie->nodeCount());
}

// Phase B: connected components (in+out edges) within each same-leaf group.
// First numSinks clusters are one per sink (preserves cone_id == cluster_id).
void ClusterGraph::_collect_clusters()
{
    rcp_log(log_level, REPCUT_LOG_DEBUG, "Collect clusters: Start\n");
    auto start = std::chrono::system_clock::now();

    const auto numVtxes = dag->numVertices();
    const auto numSinks = dag->sinkNodes.size();

    idToClusterId.assign(numVtxes, -1);
    for (uint32_t nid = 0; nid < numVtxes; ++nid) {
        if (!dag->valid[nid]) {
            idToClusterId[nid] = -2;
        }
    }

    // Flood fill within same-leaf neighbors (explicit stack avoids recursion overflow).
    auto floodFill = [&](uint32_t seed, uint32_t cluster_id) {
        auto& cluster = this->clusters[cluster_id];
        std::vector<uint32_t> stk;
        stk.reserve(64);

        assert(idToClusterId[seed] == -1);
        idToClusterId[seed] = static_cast<int32_t>(cluster_id);
        cluster.push_back(seed);
        stk.push_back(seed);

        while (!stk.empty()) {
            const uint32_t u = stk.back();
            stk.pop_back();
            auto leaf = vtxToNode[u];

            for (const auto w : dag->inNeigh[u]) {
                if (idToClusterId[w] == -1 && vtxToNode[w] == leaf) {
                    idToClusterId[w] = static_cast<int32_t>(cluster_id);
                    cluster.push_back(w);
                    stk.push_back(w);
                }
            }
            for (const auto w : dag->outNeigh[u]) {
                if (idToClusterId[w] == -1 && vtxToNode[w] == leaf) {
                    idToClusterId[w] = static_cast<int32_t>(cluster_id);
                    cluster.push_back(w);
                    stk.push_back(w);
                }
            }
        }
    };

    // 1. Sink first, in sink order (preserves cone_id == cluster_id invariant).
    for (uint32_t i = 0; i < numSinks; ++i) {
        const uint32_t seed = dag->sinkNodes[i];
        uint32_t cluster_id = static_cast<uint32_t>(clusters.size());
        clusters.emplace_back();
        floodFill(seed, cluster_id);
        // First numSinks cluster ids are the sink clusters, by construction.
        assert(cluster_id == i);
        sinkNodes.push_back(cluster_id);
    }

    // 2. Remaining valid, unassigned vertices in vertex-id order.
    for (uint32_t v = 0; v < numVtxes; ++v) {
        if (idToClusterId[v] != -1)
            continue;
        uint32_t cluster_id = static_cast<uint32_t>(clusters.size());
        clusters.emplace_back();
        floodFill(v, cluster_id);
    }

    auto stop = std::chrono::system_clock::now();
    auto duration = std::chrono::duration_cast<std::chrono::milliseconds>(stop - start);
    rcp_log(log_level, REPCUT_LOG_DEBUG, "Collect clusters: Done in %llums (%zu clusters)\n", duration.count(),
            clusters.size());
}

// Weight = 1 + sum of valid member weights (+1 floor for KaHyPar).
void ClusterGraph::_update_cluster_weight()
{
    rcp_log(log_level, REPCUT_LOG_DEBUG, "Update cluster weight: Start\n");
    auto start = std::chrono::system_clock::now();

    const auto numClusters = clusters.size();
    nodeWeight.assign(numClusters, 0.0f);

    for (uint32_t cluster_id = 0; cluster_id < numClusters; ++cluster_id) {
        float cluster_weight = 1; // +1 floor, see comment above
        for (auto& stmt_id : clusters[cluster_id]) {
            if (dag->valid[stmt_id]) {
                assert(dag->weight[stmt_id] >= 0);
                cluster_weight += dag->weight[stmt_id];
            }
        }
        nodeWeight[cluster_id] = cluster_weight;
    }

    auto stop = std::chrono::system_clock::now();
    auto duration = std::chrono::duration_cast<std::chrono::milliseconds>(stop - start);
    rcp_log(log_level, REPCUT_LOG_DEBUG, "Update cluster weight: Done in %llums\n", duration.count());
}

void ClusterGraph::collapseFromDAG(const DirectedAcyclicGraph& dag)
{
    rcp_log(log_level, REPCUT_LOG_INFO, "Collapse cluster graph: Start\n");
    auto start = std::chrono::system_clock::now();

    this->dag = &dag;
    // 1. find sink vtxs — already done in dag

    // 2. mark cones (build persistent cone-id trie + per-vertex ids)
    this->_mark_cones();

    // 3. collect clusters (connected components within same-leaf groups)
    this->_collect_clusters();

    // 4. compute cluster weight
    this->_update_cluster_weight();

    // 5. merge identical hyperedges, preserving per-cluster node-weight rounding
    this->_build_hypergraph();

    auto stop = std::chrono::system_clock::now();
    auto duration = std::chrono::duration_cast<std::chrono::milliseconds>(stop - start);
    uint64_t time_ms = duration.count();
    rcp_log(log_level, REPCUT_LOG_INFO, "Collapse cluster graph: Done in %llums\n", time_ms);
}

uint32_t ClusterGraph::clusterWeight(size_t cluster_id) const
{
    const double weight = nodeWeight[cluster_id];
    if (!std::isfinite(weight) || weight < 1 || weight > std::numeric_limits<uint32_t>::max())
        throw std::overflow_error("Cluster weight is outside uint32_t range");
    return static_cast<uint32_t>(weight);
}

// Equal trie leaves identify equal pin sets exactly. Allocate each pin vector
// once, but keep each cluster's integer conversion and node-weight contribution
// separate: sum(floor(weight / pins)) need not equal floor(sum(weight) / pins).
void ClusterGraph::_build_hypergraph()
{
    const auto numCones = sinkNodes.size();
    nodeWeights.clear();
    nodeWeights.reserve(numCones);
    for (uint32_t cone_id = 0; cone_id < numCones; ++cone_id) {
        nodeWeights.push_back(clusterWeight(cone_id));
    }
    hyperedges.clear();
    std::unordered_map<ConeTrie::NodeId, size_t> leafToEdge;
    leafToEdge.reserve(clusters.size() - numCones);
    size_t originalPins = 0, uniquePins = 0;
    for (uint32_t cluster_id = numCones; cluster_id < clusters.size(); ++cluster_id) {
        const auto leaf = vtxToNode[clusters[cluster_id].front()];
        const auto [entry, inserted] = leafToEdge.emplace(leaf, hyperedges.size());
        if (inserted) {
            hyperedges.push_back({coneTrie->pathConeIds(leaf), 0});
            uniquePins += hyperedges.back().pins.size();
        }
        auto& edge = hyperedges[entry->second];
        const auto& pins = edge.pins;
        originalPins += pins.size();
        const auto cluster_weight = clusterWeight(cluster_id);
        // MtKaHyPar uses signed 32-bit edge weights in both its C API and
        // file reader. Reject an unrepresentable sum instead of wrapping it.
        if (cluster_weight > static_cast<uint32_t>(std::numeric_limits<int32_t>::max()) - edge.weight)
            throw std::overflow_error("Hyperedge weight exceeds MtKaHyPar's signed integer range");
        edge.weight += cluster_weight;
        for (const auto cone_id : pins) {
            const auto share = cluster_weight / pins.size();
            if (share > std::numeric_limits<uint32_t>::max() - nodeWeights[cone_id])
                throw std::overflow_error("Hypergraph node weight exceeds uint32_t range");
            nodeWeights[cone_id] += share;
        }
    }

    rcp_log(log_level, REPCUT_LOG_INFO, "Merged %zu duplicate hyperedges (%zu -> %zu pins)\n",
            clusters.size() - numCones - hyperedges.size(), originalPins, uniquePins);

    // Trie + per-vertex trie ids are no longer needed downstream.
    vtxToNode.clear();
    vtxToNode.shrink_to_fit();
    coneTrie.reset();
}

// Stream cluster graph to hMetis-format file for MtKaHyPar.
// Cone clusters (cone_id in [0, numCones)) = hypergraph vertices.
// Non-cone clusters with identical pin sets share a weighted hyperedge.
// Node weight = own weight + proportional share of connected non-self weights.
void ClusterGraph::writeHMetisFile(const char* filename)
{
    rcp_log(log_level, REPCUT_LOG_DEBUG, "Write to hMetis graph file: Start\n");
    auto start = std::chrono::system_clock::now();

    const auto numCones = dag->sinkNodes.size();
    const auto numEdges = hyperedges.size();
    const auto numNodes = numCones;

    std::ofstream ofs(filename);
    if (!ofs)
        throw std::runtime_error(std::string("Cannot open hypergraph file: ") + filename);

    // header: numEdges numNodes "11"
    ofs << numEdges << " " << numNodes << " 11\n";

    // edges: one line per unique pin set, `weight pin1 pin2 ...` (pins 1-indexed)
    std::string line;
    for (const auto& edge : hyperedges) {
        line.clear();
        line += std::to_string(edge.weight);
        for (const auto pin : edge.pins) {
            line += ' ';
            line += std::to_string(pin + 1);
        }
        line += '\n';
        ofs << line;
    }

    // nodes: one weight per line
    for (auto& w : nodeWeights) {
        ofs << w << "\n";
    }

    ofs.close();
    if (!ofs)
        throw std::runtime_error(std::string("Cannot write hypergraph file: ") + filename);

    auto stop = std::chrono::system_clock::now();
    auto duration = std::chrono::duration_cast<std::chrono::milliseconds>(stop - start);
    rcp_log(log_level, REPCUT_LOG_DEBUG, "Write to hMetis graph file: Done in %llums\n", duration.count());
}
