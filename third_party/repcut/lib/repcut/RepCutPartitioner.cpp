#include "RepCutPartitioner.h"

#include "ClusterGraph.h"
#include "Log.h"
#include "MtKaHyPar.h"

#include <algorithm>
#include <cassert>
#include <chrono>
#include <cstddef>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <exception>
#include <filesystem>
#include <fstream>
#include <limits>
#include <numeric>
#include <queue>
#include <random>
#include <sstream>
#include <stdexcept>
#include <string>
#include <utility>

using namespace repcut;

namespace fs = std::filesystem;

bool RepCutPartitioner::_resolveSeed()
{
    if (kahypar_seed < -1) {
        rcp_log(log_level, REPCUT_LOG_ERROR, "seed must be -1 or nonnegative (got %d)\n", kahypar_seed);
        return false;
    }

    mtkahypar_seed = kahypar_seed;
    if (kahypar_seed == -1) {
        try {
            std::random_device random;
            std::uniform_int_distribution<int32_t> distribution(0, std::numeric_limits<int32_t>::max());
            mtkahypar_seed = distribution(random);
        }
        catch (const std::exception& error) {
            rcp_log(log_level, REPCUT_LOG_ERROR, "Cannot choose a random seed: %s\n", error.what());
            return false;
        }
    }
    rcp_log(log_level, REPCUT_LOG_INFO, "Partition seed: %d%s\n", mtkahypar_seed,
            kahypar_seed == -1 ? " (random)" : "");
    return true;
}

// Select and initialize the backend before any expensive work.
bool RepCutPartitioner::prepareMtKaHyPar(const char* bin)
{
    if (bin != nullptr && bin[0] != '\0') {
        rcp_log(log_level, REPCUT_LOG_ERROR,
                "The bundled RepCut does not support an MtKaHyPar executable override\n");
        return false;
    }
    return MtKaHyPar::initialize(parallel_threads, log_level);
}

// Release the cluster graph once MtKaHyPar owns its hypergraph.
bool RepCutPartitioner::_partitionCones(DirectedAcyclicGraph& dag)
{
    rcp_log(log_level, REPCUT_LOG_INFO, "Collapse into cluster graph\n");
    auto clusters = std::make_unique<ClusterGraph>();
    clusters->log_level = log_level;
    clusters->collapseFromDAG(dag);

    if (save_intermediate_files) {
        hmetis_path = fs::path(work_directory) / "parts.hmetis";
        std::ostringstream oss;
        oss << hmetis_path.filename().string() << ".part" << desired_parts << ".epsilon" << kahypar_imbalance_factor
            << ".seed" << mtkahypar_seed << ".KaHyPar";
        mtkahypar_output_filename = oss.str();
        clusters->writeHMetisFile(hmetis_path.string().c_str());
    }
    if (clusters->hyperedges.empty()) {
        const auto weights = clusters->hypernodeWeights();
        clusters.reset();
        _partitionIndependentCones(weights);
        return !save_intermediate_files || _saveConeAssignment();
    }

    MtKaHyPar backend(desired_parts, kahypar_imbalance_factor, mtkahypar_seed, log_level);
    if (!backend.create(*clusters))
        return false;
    clusters.reset();
    if (!backend.partition(coneIdToPartId))
        return false;
    partIdToConeId.assign(desired_parts, {});
    for (uint32_t cone = 0; cone < coneIdToPartId.size(); ++cone)
        partIdToConeId[coneIdToPartId[cone]].push_back(cone);
    return !save_intermediate_files || _saveConeAssignment();
}

bool RepCutPartitioner::_saveConeAssignment() const
{
    const auto path = fs::path(work_directory) / mtkahypar_output_filename;
    std::ofstream output(path);
    if (output) {
        for (const auto part : coneIdToPartId)
            output << part << '\n';
        output.close();
    }
    if (!output) {
        rcp_log(log_level, REPCUT_LOG_ERROR, "Cannot write cone assignments to %s\n", path.string().c_str());
        return false;
    }
    return true;
}

// An edgeless cone-overlap hypergraph has no replication cost to minimize.
// Balance whole cones using longest-processing-time-first scheduling; splitting
// raw DAG nodes here would break the dependency closure of each partition.
void RepCutPartitioner::_partitionIndependentCones(const std::vector<uint32_t>& weights)
{
    rcp_log(log_level, REPCUT_LOG_INFO, "Balance %zu independent cones across %u partitions\n", weights.size(),
            desired_parts);

    std::vector<uint32_t> order(weights.size());
    std::iota(order.begin(), order.end(), uint32_t{0});
    std::sort(order.begin(), order.end(), [&](uint32_t lhs, uint32_t rhs) {
        return weights[lhs] != weights[rhs] ? weights[lhs] > weights[rhs] : lhs < rhs;
    });

    // Wide loads avoid overflow when summing many node weights. Partition id
    // breaks equal-load ties, keeping assignments deterministic.
    using Load = std::pair<uint64_t, uint32_t>;
    std::priority_queue<Load, std::vector<Load>, std::greater<Load>> loads;
    for (uint32_t pid = 0; pid < desired_parts; ++pid) {
        loads.emplace(0, pid);
    }
    coneIdToPartId.assign(weights.size(), 0);
    partIdToConeId.assign(desired_parts, {});
    for (const uint32_t cone : order) {
        const auto [weight, pid] = loads.top();
        loads.pop();
        coneIdToPartId[cone] = pid;
        partIdToConeId[pid].push_back(cone);
        loads.emplace(weight + weights[cone], pid);
    }
}

bool RepCutPartitioner::_reconstruct(DirectedAcyclicGraph& dag)
{
    rcp_log(log_level, REPCUT_LOG_INFO, "Reconstruct partitions\n");
    auto start = std::chrono::system_clock::now();

    assert(coneIdToPartId.size() == dag.sinkNodes.size());

    partitions.clear();
    partitions.assign(desired_parts, std::vector<uint32_t>());

    std::vector<bool> visited(dag.numVertices(), false);
    std::vector<uint32_t> fringe;
    std::vector<uint32_t> sinksForPart;
    fringe.reserve(1 << 14);

    for (uint32_t pid = 0; pid < desired_parts; ++pid) {
        auto& part = partitions[pid];

        sinksForPart.clear();
        for (uint32_t cone_id = 0; cone_id < coneIdToPartId.size(); ++cone_id) {
            if (coneIdToPartId[cone_id] == pid) {
                sinksForPart.push_back(dag.sinkNodes[cone_id]);
            }
        }

        fringe.clear();
        for (uint32_t s : sinksForPart) {
            if (!visited[s]) {
                visited[s] = true;
                fringe.push_back(s);
            }
        }

        while (!fringe.empty()) {
            const uint32_t v = fringe.back();
            fringe.pop_back();

            // Invalid nodes never contribute to a partition; leave them marked.
            if (!dag.valid[v])
                continue;
            part.push_back(v);

            for (const auto u : dag.inNeigh[v]) {
                if (!visited[u]) {
                    visited[u] = true;
                    fringe.push_back(u);
                }
            }
        }

        // Sort ascending for diffable output.
        std::sort(part.begin(), part.end());

        // Reset only the valid vertices reached in this partition. Clearing
        // the entire bitmap per partition would penalize many small partitions.
        for (const auto v : part) {
            visited[v] = false;
        }
    }

    auto stop = std::chrono::system_clock::now();
    auto duration = std::chrono::duration_cast<std::chrono::milliseconds>(stop - start);
    rcp_log(log_level, REPCUT_LOG_INFO, "Reconstruct: Done in %llums\n", duration.count());
    return true;
}

bool RepCutPartitioner::partition(DirectedAcyclicGraph& dag, const int nparts)
{
    rcp_log(log_level, REPCUT_LOG_INFO, "RepCut Partitioner: Start\n");
    auto start = std::chrono::system_clock::now();

    this->desired_parts = nparts;
    if (!_resolveSeed())
        return false;

    if (!_partitionCones(dag))
        return false;

    // Reconstruct per-partition DAG node sets (upstream BFS).
    if (!_reconstruct(dag))
        return false;

    auto stop = std::chrono::system_clock::now();
    auto duration = std::chrono::duration_cast<std::chrono::milliseconds>(stop - start);
    uint64_t time_ms = duration.count();
    rcp_log(log_level, REPCUT_LOG_INFO, "RepCut Partitioner: Done in %llums\n", time_ms);
    return true;
}

std::unique_ptr<PartitionStatistics> RepCutPartitioner::reportPartitionStatus(DirectedAcyclicGraph& dag)
{
    assert(!this->partitions.empty());

    auto ret = std::make_unique<PartitionStatistics>();
    ret->nparts = this->partitions.size();

    // Whole-design totals (only valid nodes).
    const auto n = dag.numVertices();
    for (uint32_t v = 0; v < n; ++v) {
        if (dag.valid[v]) {
            ret->sg_size++;
            ret->sg_weight += dag.weight[v];
        }
    }

    uint32_t total_part_size = 0;
    float total_part_weight = 0;

    for (auto& part : this->partitions) {
        uint32_t part_size = 0;
        float part_weight = 0;

        for (auto& nid : part) {
            if (dag.valid[nid]) {
                part_size += 1;
                part_weight += dag.weight[nid];
            }
        }

        total_part_size += part_size;
        total_part_weight += part_weight;

        ret->partition_size.push_back(part_size);
        ret->partition_weights.push_back(part_weight);
    }

    ret->total_part_size = total_part_size;
    ret->replication_size = ret->total_part_size - ret->sg_size;
    ret->replication_rate_size =
        (ret->sg_size > 0) ? static_cast<float>(ret->replication_size) * 100.0f / ret->sg_size : 0.0f;
    ret->ib_factor_size = calculate_ib_factor(ret->partition_size);

    ret->total_part_weight = total_part_weight;
    ret->replication_weight = ret->total_part_weight - ret->sg_weight;
    ret->replication_rate_weight =
        (ret->sg_weight != 0.0f) ? static_cast<float>(ret->replication_weight) * 100.0f / ret->sg_weight : 0.0f;
    ret->ib_factor_weight = calculate_ib_factor(ret->partition_weights);

    return ret;
}

void RepCutPartitioner::saveToFile(const char* filename)
{
    rcp_log(log_level, REPCUT_LOG_INFO, "Write to output file: Start\n");
    auto start = std::chrono::system_clock::now();

    auto ofs = std::ofstream(work_directory + "/" + filename);

    // Reuse std::string to avoid per-integer operator<< overhead.
    std::string line;
    for (uint32_t pid = 0; pid < partitions.size(); pid++) {
        line.clear();
        for (auto sg_id : this->partitions[pid]) {
            line += std::to_string(sg_id);
            line += ',';
        }
        line += '\n';
        ofs << line;
    }

    ofs.close();

    auto stop = std::chrono::system_clock::now();
    auto duration = std::chrono::duration_cast<std::chrono::milliseconds>(stop - start);
    rcp_log(log_level, REPCUT_LOG_INFO, "Write to output file: Done in %llums\n", duration.count());
}
