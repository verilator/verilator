#include "MtKaHyPar.h"

#include "Log.h"
#include "MtKaHyParPreset.h"

#include <cmath>
#include <limits>
#include <stdexcept>
#include <string>

using namespace repcut;

mt_kahypar_context_t* repcut::makeMtKaHyParContext()
{
    mt_kahypar_error_t error{};
    const std::unique_ptr<mt_kahypar_error_t, decltype(&mt_kahypar_free_error_content)> error_guard(
        &error, mt_kahypar_free_error_content);
    auto* context = mt_kahypar_context_from_string(mtkahypar_preset, &error);
    if (!context)
        throw std::runtime_error(std::string("Cannot load MtKaHyPar configuration: ") +
                                 (error.msg ? error.msg : "no error description"));
    return context;
}

bool MtKaHyPar::initialize(int threads, RepCutLogLevel log_level)
{
    if (threads != 1) {
        rcp_log(log_level, REPCUT_LOG_ERROR, "The bundled MtKaHyPar requires one thread\n");
        return false;
    }
    // Protected by repcut_run's process-wide guard. Initialize serial state once.
    static bool initialized = false;
    if (!initialized) {
        mt_kahypar_initialize(1, false);
        initialized = true;
    }
    return true;
}

MtKaHyPar::MtKaHyPar(int parts, float imbalance, int32_t seed, RepCutLogLevel log_level)
    : context(makeMtKaHyParContext(), mt_kahypar_free_context), log_level(log_level), num_parts(parts)
{
    if (!context)
        throw std::runtime_error("Cannot create MtKaHyPar context");
    // Match the decimal epsilon passed to the executable backend.
    mt_kahypar_set_partitioning_parameters(context.get(), parts, std::stod(std::to_string(imbalance)), KM1);
    // The public setter seeds MtKaHyPar's global RNG. In 1.7 it does not
    // update the separate context seed used by some algorithms; fixed-seed
    // replay is therefore backend-specific, not necessarily CLI-identical.
    mt_kahypar_set_seed(seed);
    mt_kahypar_set_context_parameter(context.get(), VERBOSE, rcp_should_log(log_level, REPCUT_LOG_INFO) ? "1" : "0",
                                     &error);
}

MtKaHyPar::~MtKaHyPar()
{
    if (partitioned.partitioned_hg)
        mt_kahypar_free_partitioned_hypergraph(partitioned);
    if (graph.hypergraph)
        mt_kahypar_free_hypergraph(graph);
    mt_kahypar_free_error_content(&error);
}

bool MtKaHyPar::failed(const char* operation) const
{
    rcp_log(log_level, REPCUT_LOG_ERROR, "MtKaHyPar %s failed: %s\n", operation,
            error.msg ? error.msg : "no error description");
    return false;
}

bool MtKaHyPar::create(const ClusterGraph& clusters)
{
    if (error.status != SUCCESS)
        return failed("configuration");

    const auto& weights = clusters.hypernodeWeights();
    std::vector<mt_kahypar_hypernode_weight_t> node_weights;
    node_weights.reserve(weights.size());
    uint64_t total_weight = 0;
    for (const auto weight : weights) {
        total_weight += weight;
        if (total_weight > std::numeric_limits<mt_kahypar_hypernode_weight_t>::max()) {
            rcp_log(log_level, REPCUT_LOG_ERROR, "Hypergraph node weight exceeds MtKaHyPar's signed integer range\n");
            return false;
        }
        node_weights.push_back(static_cast<mt_kahypar_hypernode_weight_t>(weight));
    }
    const double max_block_weight =
        (1 + mt_kahypar_get_epsilon(context.get())) * std::ceil(static_cast<double>(total_weight) / num_parts);
    if (max_block_weight > std::numeric_limits<mt_kahypar_hypernode_weight_t>::max()) {
        rcp_log(log_level, REPCUT_LOG_ERROR, "Target block weight exceeds MtKaHyPar's signed integer range\n");
        return false;
    }

    std::vector<size_t> offsets{0};
    std::vector<mt_kahypar_hypernode_id_t> pins;
    std::vector<mt_kahypar_hyperedge_weight_t> edge_weights;
    size_t num_pins = 0;
    for (const auto& edge : clusters.hyperedges) {
        const auto size = edge.pins.size();
        // The executable's file reader drops singleton hyperedges. They do
        // contribute to node weights above, but cannot affect the km1 cut.
        if (size > 1) {
            if (size > pins.max_size() - num_pins)
                throw std::length_error("Too many hypergraph pins");
            num_pins += size;
        }
    }
    pins.reserve(num_pins);
    for (const auto& edge : clusters.hyperedges) {
        if (edge.pins.size() <= 1)
            continue;
        const auto weight = edge.weight;
        if (weight > std::numeric_limits<mt_kahypar_hyperedge_weight_t>::max()) {
            rcp_log(log_level, REPCUT_LOG_ERROR, "Hyperedge weight exceeds MtKaHyPar's signed integer range\n");
            return false;
        }
        edge_weights.push_back(static_cast<mt_kahypar_hyperedge_weight_t>(weight));
        pins.insert(pins.end(), edge.pins.begin(), edge.pins.end());
        offsets.push_back(pins.size());
    }

    rcp_log(log_level, REPCUT_LOG_INFO, "Construct MtKaHyPar hypergraph in memory\n");
    graph = mt_kahypar_create_hypergraph(context.get(), node_weights.size(), edge_weights.size(), offsets.data(),
                                         pins.data(), edge_weights.data(), node_weights.data(), &error);
    // MtKaHyPar copies these buffers. They and the cluster graph can be freed
    // before partitioning, when MtKaHyPar allocates its largest working sets.
    return graph.hypergraph ? true : failed("hypergraph construction");
}

bool MtKaHyPar::partition(std::vector<uint32_t>& assignment)
{
    rcp_log(log_level, REPCUT_LOG_INFO, "Call MtKaHyPar library\n");
    partitioned = mt_kahypar_partition(graph, context.get(), &error);
    if (!partitioned.partitioned_hg)
        return failed("partitioning");

    std::vector<mt_kahypar_partition_id_t> result(mt_kahypar_num_hypernodes(graph));
    mt_kahypar_get_partition(partitioned, result.data());
    assignment.clear();
    assignment.reserve(result.size());
    for (const auto part : result) {
        if (part < 0 || part >= num_parts) {
            rcp_log(log_level, REPCUT_LOG_ERROR, "MtKaHyPar returned invalid partition id %d\n", part);
            return false;
        }
        assignment.push_back(static_cast<uint32_t>(part));
    }
    return true;
}
