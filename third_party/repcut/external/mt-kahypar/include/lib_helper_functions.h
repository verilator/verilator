/*******************************************************************************
 * MIT License
 *
 * This file is part of Mt-KaHyPar.
 *
 * Copyright (C) 2023 Tobias Heuer <tobias.heuer@kit.edu>
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 * AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 * OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
 * SOFTWARE.
 ******************************************************************************/

#pragma once

#include <chrono>
#include <limits>
#include <string>
#include <sstream>
#include <type_traits>

#include "mtkahypartypes.h"

#include "mt-kahypar/definitions.h"
#include "mt-kahypar/macros.h"
#include "mt-kahypar/parallel/thread_management.h"
#include "mt-kahypar/partition/context.h"
#include "mt-kahypar/partition/conversion.h"
#include "mt-kahypar/partition/partitioner_facade.h"
#include "mt-kahypar/partition/mapping/target_graph.h"
#include "mt-kahypar/partition/metrics.h"
#include "mt-kahypar/partition/registries/registry.h"
#include "mt-kahypar/io/hypergraph_factory.h"
#include "mt-kahypar/io/hypergraph_io.h"
#include "mt-kahypar/utils/cast.h"
#include "mt-kahypar/utils/deduplicate.h"
#include "mt-kahypar/utils/exception.h"
#include "mt-kahypar/utils/utilities.h"
#include "mt-kahypar/io/command_line_options.h"
#include "mt-kahypar/io/presets.h"


using namespace mt_kahypar;

namespace lib {
  using StaticGraph = typename StaticGraphTypeTraits::Hypergraph;
  using DynamicGraph = typename DynamicGraphTypeTraits::Hypergraph;
  using StaticHypergraph = typename StaticHypergraphTypeTraits::Hypergraph;
  using DynamicHypergraph = typename DynamicHypergraphTypeTraits::Hypergraph;

  using StaticPartitionedGraph = typename StaticGraphTypeTraits::PartitionedHypergraph;
  using DynamicPartitionedGraph = typename DynamicGraphTypeTraits::PartitionedHypergraph;
  using StaticPartitionedHypergraph = typename StaticHypergraphTypeTraits::PartitionedHypergraph;
  using DynamicPartitionedHypergraph = typename DynamicHypergraphTypeTraits::PartitionedHypergraph;
  using SparsePartitionedHypergraph = typename LargeKHypergraphTypeTraits::PartitionedHypergraph;

  using StaticHypergraphFactory = typename ds::StaticHypergraph::Factory;
  using DynamicHypergraphFactory = typename ds::DynamicHypergraph::Factory;
  using StaticGraphFactory = typename ds::StaticGraph::Factory;
  using DynamicGraphFactory = typename ds::DynamicGraph::Factory;


// ####################### General Helper Functions #######################

void initialize(const size_t num_threads, const bool interleaved_allocations, const bool print_warnings) {
  size_t P = num_threads;
  if constexpr (parallel::provides_hardware_information) {
    size_t num_available_cpus = parallel::num_hardware_cpus();
    if ( num_available_cpus < num_threads ) {
      P = num_available_cpus;
      if (print_warnings) {
        WARNING("There are currently only " << num_available_cpus << " cpus available. "
          << "Setting number of threads from " << num_threads << " to " << num_available_cpus);
      }
    }
  }

  // Initialize TBB task arenas on numa nodes
  parallel::initialize_tbb(P);

  if constexpr (parallel::provides_hardware_information) {
    if ( interleaved_allocations ) {
      // We set the membind policy to interleaved allocations in order to
      // distribute allocations evenly across NUMA nodes
      parallel::activate_interleaved_membind_policy();
    }
  }

  register_algorithms_and_policies();
}

bool is_compatible(mt_kahypar_hypergraph_t hypergraph, mt_kahypar_preset_type_t preset) {
  switch ( preset ) {
    case DEFAULT:
    case QUALITY:
    case DETERMINISTIC:
    case DETERMINISTIC_QUALITY:
    case LARGE_K:
      return hypergraph.type == STATIC_GRAPH || hypergraph.type == STATIC_HYPERGRAPH;
    case HIGHEST_QUALITY:
      return hypergraph.type == DYNAMIC_GRAPH || hypergraph.type == DYNAMIC_HYPERGRAPH;
  }
  return false;
}

bool is_compatible(mt_kahypar_partitioned_hypergraph_t partitioned_hg, mt_kahypar_preset_type_t preset) {
  switch ( preset ) {
    case DEFAULT:
    case QUALITY:
    case DETERMINISTIC:
    case DETERMINISTIC_QUALITY:
      return partitioned_hg.type == MULTILEVEL_GRAPH_PARTITIONING ||
             partitioned_hg.type == MULTILEVEL_HYPERGRAPH_PARTITIONING;
    case LARGE_K:
      return partitioned_hg.type == MULTILEVEL_GRAPH_PARTITIONING ||
             partitioned_hg.type == LARGE_K_PARTITIONING;
    case HIGHEST_QUALITY:
      return partitioned_hg.type == N_LEVEL_GRAPH_PARTITIONING ||
             partitioned_hg.type == N_LEVEL_HYPERGRAPH_PARTITIONING;
  }
  return false;
}

template<typename OutType, typename InType>
void check_overflow(const InType& value, const char* what) {
  if (value > static_cast<InType>(std::numeric_limits<OutType>::max())) {
    std::string msg = std::string(what) + " overflows input range of internal data type: " + STR(value);
    if constexpr (sizeof(OutType) < 8) {
      msg += " (build with -DKAHYPAR_USE_64_BIT_IDS=ON to support larger ID ranges)";
    }
    throw InvalidInputException(msg);
  }
}

void check_if_all_relevant_parameters_are_set(Context& context) {
  bool success = true;
  auto check_parameter = [&](bool is_uninitialized, const char* warning_msg) {
    if (is_uninitialized) {
      success = false;
      if (context.partition.enable_logging) {
        WARNING(warning_msg);
      }
    }
  };

  check_parameter(context.partition.preset_type == PresetType::UNDEFINED, "Preset type not specified.");
  check_parameter(context.partition.k == std::numeric_limits<PartitionID>::max(), "Number of blocks not specified.");
  check_parameter(context.partition.epsilon == std::numeric_limits<double>::max(), "Imbalance not specified.");
  check_parameter(context.partition.objective == Objective::UNDEFINED, "Objective function not specified.");
  if (!success) {
    throw InvalidInputException("A required context parameter is not set. Required are: preset type, k, epsilon, objective");
  }
}

Context context_from_file(const char* ini_file_name) {
  Context context(false);
  parseIniToContext(context, ini_file_name, true);
  return context;
}

Context context_from_preset(PresetType preset) {
  Context context(false);
  presetToContext(context, preset, true);
  return context;
}

void prepare_context(Context& context) {
  context.shared_memory.original_num_threads = parallel::total_number_of_threads();
  context.shared_memory.num_threads = parallel::total_number_of_threads();
  context.utility_id = mt_kahypar::utils::Utilities::instance().registerNewUtilityObjects();

  context.partition.perfect_balance_part_weights.clear();
  if ( !context.partition.use_individual_part_weights ) {
    context.partition.max_part_weights.clear();
  }
}

InstanceType get_instance_type(mt_kahypar_hypergraph_t hypergraph) {
  switch ( hypergraph.type ) {
    case STATIC_GRAPH:
    case DYNAMIC_GRAPH:
      return InstanceType::graph;
    case STATIC_HYPERGRAPH:
    case DYNAMIC_HYPERGRAPH:
      return InstanceType::hypergraph;
    case NULLPTR_HYPERGRAPH:
      return InstanceType::UNDEFINED;
  }
  return InstanceType::UNDEFINED;
}

InstanceType get_instance_type(mt_kahypar_partitioned_hypergraph_t partitioned_hg) {
  switch ( partitioned_hg.type ) {
    case MULTILEVEL_GRAPH_PARTITIONING:
    case N_LEVEL_GRAPH_PARTITIONING:
      return InstanceType::graph;
    case MULTILEVEL_HYPERGRAPH_PARTITIONING:
    case N_LEVEL_HYPERGRAPH_PARTITIONING:
    case LARGE_K_PARTITIONING:
      return InstanceType::hypergraph;
    case NULLPTR_PARTITION:
      return InstanceType::UNDEFINED;
  }
  return InstanceType::UNDEFINED;
}

mt_kahypar_preset_type_t get_preset_c_type(const PresetType preset) {
  switch ( preset ) {
    case PresetType::default_preset: return DEFAULT;
    case PresetType::quality: return QUALITY;
    case PresetType::highest_quality: return HIGHEST_QUALITY;
    case PresetType::deterministic: return DETERMINISTIC;
    case PresetType::deterministic_quality: return DETERMINISTIC_QUALITY;
    case PresetType::large_k: return LARGE_K;
    case PresetType::UNDEFINED: return DEFAULT;
  }
  return DEFAULT;
}

std::string incompatibility_description(mt_kahypar_hypergraph_t hypergraph) {
  std::stringstream ss;
  switch ( hypergraph.type ) {
    case STATIC_GRAPH:
      ss << "The hypergraph uses the static graph data structure which can be only used "
         << "in combination with the following presets: "
         << "DEFAULT, QUALITY, DETERMINISTIC, DETERMINISTIC_QUALITY and LARGE_K"; break;
    case DYNAMIC_GRAPH:
      ss << "The hypergraph uses the dynamic graph data structure which can be only used "
         << "in combination with the following preset: "
         << "HIGHEST_QUALITY"; break;
    case STATIC_HYPERGRAPH:
      ss << "The hypergraph uses the static hypergraph data structure which can be only used "
         << "in combination with the following presets: "
         << "DEFAULT, QUALITY, DETERMINISTIC, DETERMINISTIC_QUALITY and LARGE_K"; break;
    case DYNAMIC_HYPERGRAPH:
      ss << "The hypergraph uses the dynamic hypergraph data structure which can be only used "
         << "in combination with the following preset: "
         << "HIGHEST_QUALITY"; break;
    case NULLPTR_HYPERGRAPH:
      ss << "The hypergraph holds a nullptr. "
         << "Did you forgot to construct or load a hypergraph?"; break;
  }
  return ss.str();
}

void check_compatibility(mt_kahypar_hypergraph_t hypergraph,
                         mt_kahypar_preset_type_t preset) {
  if ( !is_compatible(hypergraph, preset) ) {
    throw UnsupportedOperationException(incompatibility_description(hypergraph));
  }
}

std::string incompatibility_description(mt_kahypar_partitioned_hypergraph_t partitioned_hg) {
  std::stringstream ss;
  switch ( partitioned_hg.type ) {
    case MULTILEVEL_GRAPH_PARTITIONING:
      ss << "The partitioned hypergraph uses the data structures for multilevel graph partitioning "
         << "which can be only used in combination with the following presets: "
         << "DEFAULT, QUALITY, DETERMINISTIC, DETERMINISTIC_QUALITY, and LARGE_K"; break;
    case N_LEVEL_GRAPH_PARTITIONING:
      ss << "The partitioned hypergraph uses the data structures for n-level graph partitioning "
         << "which can be only used in combination with the following preset: "
         << "HIGHEST_QUALITY"; break;
    case MULTILEVEL_HYPERGRAPH_PARTITIONING:
      ss << "The partitioned hypergraph uses the data structures for multilevel hypergraph partitioning "
         << "which can be only used in combination with the following presets: "
         << "DEFAULT, QUALITY, and DETERMINISTIC, DETERMINISTIC_QUALITY"; break;
    case N_LEVEL_HYPERGRAPH_PARTITIONING:
      ss << "The partitioned hypergraph uses the data structures for n-level hypergraph partitioning "
         << "which can be only used in combination with the following preset: "
         << "HIGHEST_QUALITY"; break;
    case LARGE_K_PARTITIONING:
      ss << "The partitioned hypergraph uses the data structures for large k hypergraph partitioning "
         << "which can be only used in combination with the following preset: "
         << "LARGE_K"; break;
    case NULLPTR_PARTITION:
      ss << "The hypergraph holds a nullptr. "
         << "Did you forgot to construct or load a hypergraph?"; break;
  }
  return ss.str();
}

void check_compatibility(mt_kahypar_partitioned_hypergraph_t partitioned_hg,
                         mt_kahypar_preset_type_t preset) {
  if ( !is_compatible(partitioned_hg, preset) ) {
    throw UnsupportedOperationException(incompatibility_description(partitioned_hg));
  }
}

mt_kahypar_hypergraph_t hypergraph_from_file(const std::string& file_name,
                                             const Context& context,
                                             const InstanceType instance_type,
                                             const FileFormat file_format) {
  return io::readInputFile(file_name, context.partition.preset_type, instance_type, file_format,
                           /*stable_construnction=*/true, /*remove_single_pin_hes=*/true, context.partition.enable_logging);
}

mt_kahypar_hypergraph_t create_hypergraph(const Context& context,
                                          const mt_kahypar_hypernode_id_t num_vertices,
                                          const mt_kahypar_hyperedge_id_t num_hyperedges,
                                          const vec<vec<HypernodeID>>& edge_vector,
                                          const mt_kahypar_hyperedge_weight_t* hyperedge_weights,
                                          const mt_kahypar_hypernode_weight_t* vertex_weights) {
  check_overflow<HypernodeID>(num_vertices, "number of vertices");
  check_overflow<HyperedgeID>(num_hyperedges, "number of hyperedges");

  switch ( context.partition.preset_type ) {
    case PresetType::deterministic:
    case PresetType::deterministic_quality:
    case PresetType::large_k:
    case PresetType::default_preset:
    case PresetType::quality:
      return mt_kahypar_hypergraph_t {
        reinterpret_cast<mt_kahypar_hypergraph_s*>(new ds::StaticHypergraph(
          StaticHypergraphFactory::construct(num_vertices, num_hyperedges,
            edge_vector, hyperedge_weights, vertex_weights, true))), STATIC_HYPERGRAPH };
    case PresetType::highest_quality:
      return mt_kahypar_hypergraph_t {
        reinterpret_cast<mt_kahypar_hypergraph_s*>(new ds::DynamicHypergraph(
          DynamicHypergraphFactory::construct(num_vertices, num_hyperedges,
            edge_vector, hyperedge_weights, vertex_weights, true))), DYNAMIC_HYPERGRAPH };
    case PresetType::UNDEFINED:
      break;
  }
  throw InvalidParameterException("Invalid preset type.");
}

mt_kahypar_hypergraph_t create_hypergraph_from_adjacency_array(const Context& context,
                                                               const mt_kahypar_hypernode_id_t num_vertices,
                                                               const mt_kahypar_hyperedge_id_t num_hyperedges,
                                                               const size_t* hyperedge_indices,
                                                               const mt_kahypar_hypernode_id_t* hyperedges,
                                                               const mt_kahypar_hyperedge_weight_t* hyperedge_weights,
                                                               const mt_kahypar_hypernode_weight_t* vertex_weights) {
  check_overflow<HypernodeID>(num_vertices, "number of vertices");
  check_overflow<HyperedgeID>(num_hyperedges, "number of hyperedges");
  if (hyperedge_indices[0] != 0) {
    throw InvalidInputException("First entry in hyperedge indices must be 0, but is: " + STR(hyperedge_indices[0]));
  }

  // Transform adjacence array into adjacency list
  size_t num_duplicated_pins = 0;
  size_t num_hes_with_duplicated_pins = 0;
  vec<vec<HypernodeID>> edge_vector(num_hyperedges);
  tbb::parallel_for<HyperedgeID>(0, num_hyperedges, [&](const mt_kahypar::HyperedgeID& he) {
    const char* help_msg = "(Note: the last element of 'hyperedge_indices' must be a sentinel with value "
      "equal to the number of pins; hyperedge_indices has one more element than the number of hyperedges)";
    if (hyperedge_indices[he + 1] < hyperedge_indices[he]) {
      throw InvalidInputException(std::string("Hyperedge indices must be in ascending order ") + help_msg);
    } else if (hyperedge_indices[he + 1] - hyperedge_indices[he] > num_vertices) {
      throw InvalidInputException("Hyperedge " + STR(he) + " has too many entries " + help_msg);
    }

    const size_t num_pins = hyperedge_indices[he + 1] - hyperedge_indices[he];
    edge_vector[he].resize(num_pins);
    for ( size_t i = 0; i < num_pins; ++i ) {
      mt_kahypar_hypernode_id_t pin = hyperedges[hyperedge_indices[he] + i];
      check_overflow<HypernodeID>(pin, "pin");
      edge_vector[he][i] = pin;
    }

    utils::deduplicateHyperedgePins(edge_vector[he], num_duplicated_pins, num_hes_with_duplicated_pins);
  });

  if ( context.partition.enable_logging && num_hes_with_duplicated_pins > 0 ) {
    WARNING("Removed " << num_duplicated_pins << " duplicated pins in " << num_hes_with_duplicated_pins << " hyperedges!");
  }
  return create_hypergraph(context, num_vertices, num_hyperedges, edge_vector, hyperedge_weights, vertex_weights);
}

mt_kahypar_hypergraph_t create_graph(const Context& context,
                                     const mt_kahypar_hypernode_id_t num_vertices,
                                     const mt_kahypar_hyperedge_id_t num_edges,
                                     const vec<std::pair<HypernodeID, HypernodeID>>& edge_vector,
                                     const mt_kahypar_hyperedge_weight_t* edge_weights,
                                     const mt_kahypar_hypernode_weight_t* vertex_weights) {
  check_overflow<HypernodeID>(num_vertices, "number of nodes");
  check_overflow<HyperedgeID>(num_edges, "number of edges");

  switch ( context.partition.preset_type ) {
    case PresetType::deterministic:
    case PresetType::deterministic_quality:
    case PresetType::large_k:
    case PresetType::default_preset:
    case PresetType::quality:
      return mt_kahypar_hypergraph_t {
        reinterpret_cast<mt_kahypar_hypergraph_s*>(new ds::StaticGraph(
          StaticGraphFactory::construct_from_graph_edges(num_vertices, num_edges,
            edge_vector, edge_weights, vertex_weights, true))), STATIC_GRAPH };
    case PresetType::highest_quality:
      return mt_kahypar_hypergraph_t {
        reinterpret_cast<mt_kahypar_hypergraph_s*>(new ds::DynamicGraph(
          DynamicGraphFactory::construct_from_graph_edges(num_vertices, num_edges,
            edge_vector, edge_weights, vertex_weights, true))), DYNAMIC_GRAPH };
    case PresetType::UNDEFINED:
      break;
  }
  throw InvalidParameterException("Invalid preset type.");
}

template<typename PartitionedHypergraph, typename Hypergraph>
mt_kahypar_partitioned_hypergraph_t create_partitioned_hypergraph(Hypergraph& hg,
                                                                  const mt_kahypar_partition_id_t num_blocks,
                                                                  const mt_kahypar_partition_id_t* partition) {
  PartitionedHypergraph partitioned_hg(num_blocks, hg, parallel_tag_t { });
  const mt_kahypar::HypernodeID num_nodes = hg.initialNumNodes();
  tbb::parallel_for(ID(0), num_nodes, [&](const mt_kahypar::HypernodeID& hn) {
    partitioned_hg.setOnlyNodePart(hn, partition[hn]);
  });
  partitioned_hg.initializePartition();
  return mt_kahypar_partitioned_hypergraph_t { reinterpret_cast<mt_kahypar_partitioned_hypergraph_s*>(
    new PartitionedHypergraph(std::move(partitioned_hg))), PartitionedHypergraph::TYPE };
}

mt_kahypar_partitioned_hypergraph_t create_partitioned_hypergraph(mt_kahypar_hypergraph_t hypergraph,
                                                                  const Context& context,
                                                                  const mt_kahypar_partition_id_t num_blocks,
                                                                  const mt_kahypar_partition_id_t* partition) {
  if ( hypergraph.type == STATIC_GRAPH || hypergraph.type == DYNAMIC_GRAPH ) {
    switch ( context.partition.preset_type ) {
      case PresetType::large_k:
      case PresetType::deterministic:
      case PresetType::deterministic_quality:
      case PresetType::default_preset:
      case PresetType::quality:
        ASSERT(hypergraph.type == STATIC_GRAPH);
        return create_partitioned_hypergraph<StaticPartitionedGraph>(
          utils::cast<ds::StaticGraph>(hypergraph), num_blocks, partition);
      case PresetType::highest_quality:
        ASSERT(hypergraph.type == DYNAMIC_GRAPH);
        return create_partitioned_hypergraph<DynamicPartitionedGraph>(
          utils::cast<ds::DynamicGraph>(hypergraph), num_blocks, partition);
      case PresetType::UNDEFINED: break;
    }
  } else {
    switch ( context.partition.preset_type ) {
      case PresetType::large_k:
        ASSERT(hypergraph.type == STATIC_HYPERGRAPH);
        return create_partitioned_hypergraph<SparsePartitionedHypergraph>(
          utils::cast<ds::StaticHypergraph>(hypergraph), num_blocks, partition);
      case PresetType::deterministic:
      case PresetType::deterministic_quality:
      case PresetType::default_preset:
      case PresetType::quality:
        ASSERT(hypergraph.type == STATIC_HYPERGRAPH);
        return create_partitioned_hypergraph<StaticPartitionedHypergraph>(
          utils::cast<ds::StaticHypergraph>(hypergraph), num_blocks, partition);
      case PresetType::highest_quality:
        ASSERT(hypergraph.type == DYNAMIC_HYPERGRAPH);
        return create_partitioned_hypergraph<DynamicPartitionedHypergraph>(
          utils::cast<ds::DynamicHypergraph>(hypergraph), num_blocks, partition);
      case PresetType::UNDEFINED: break;
    }
  }
  throw InvalidParameterException("Invalid preset type.");
}

void set_individual_block_weights(Context& context,
                                  const mt_kahypar_partition_id_t num_blocks,
                                  const mt_kahypar_hypernode_weight_t* block_weights) {
  context.partition.use_individual_part_weights = true;
  context.partition.max_part_weights.assign(num_blocks, 0);
  for ( mt_kahypar_partition_id_t i = 0; i < num_blocks; ++i ) {
    context.partition.max_part_weights[i] = block_weights[i];
  }
}


// ####################### Partitioning #######################

mt_kahypar_partitioned_hypergraph_t partition_impl(mt_kahypar_hypergraph_t hg, Context& context, TargetGraph* target_graph) {
  check_compatibility(hg, get_preset_c_type(context.partition.preset_type));
  check_if_all_relevant_parameters_are_set(context);
  context.partition.instance_type = get_instance_type(hg);
  context.partition.partition_type = to_partition_c_type(context.partition.preset_type, context.partition.instance_type);
  prepare_context(context);

  HighResClockTimepoint start = std::chrono::high_resolution_clock::now();
  auto phg = PartitionerFacade::partition(hg, context, target_graph);
  HighResClockTimepoint end = std::chrono::high_resolution_clock::now();
  PartitionerFacade::printPartitioningResults(phg, context, end - start);
  return phg;
}

mt_kahypar_partitioned_hypergraph_t partition(mt_kahypar_hypergraph_t hg, const Context& context) {
  Context partition_context(context);
  return partition_impl(hg, partition_context, nullptr);
}

mt_kahypar_partitioned_hypergraph_t map(mt_kahypar_hypergraph_t hg, TargetGraph& target_graph, const Context& context) {
  if (static_cast<PartitionID>(target_graph.graph().initialNumNodes()) != context.partition.k) {
    std::stringstream ss;
    ss << "Mismatched number of blocks: the context specifies " << context.partition.k
        << " blocks, but the target graph has " << target_graph.graph().initialNumNodes() << " blocks";
    throw InvalidInputException(ss.str());
  }
  Context partition_context(context);
  partition_context.partition.objective = Objective::steiner_tree;
  return partition_impl(hg, partition_context, &target_graph);
}


// ####################### V-Cycles #######################

void improve_impl(mt_kahypar_partitioned_hypergraph_t phg,
                  Context& context,
                  const size_t num_vcycles,
                  TargetGraph* target_graph) {
  check_compatibility(phg, get_preset_c_type(context.partition.preset_type));
  check_if_all_relevant_parameters_are_set(context);
  context.partition.instance_type = get_instance_type(phg);
  context.partition.partition_type = to_partition_c_type(context.partition.preset_type, context.partition.instance_type);
  prepare_context(context);
  context.partition.num_vcycles = num_vcycles;

  HighResClockTimepoint start = std::chrono::high_resolution_clock::now();
  PartitionerFacade::improve(phg, context, target_graph);
  HighResClockTimepoint end = std::chrono::high_resolution_clock::now();
  PartitionerFacade::printPartitioningResults(phg, context, end - start);
}

void improve(mt_kahypar_partitioned_hypergraph_t phg, const Context& context, const size_t num_vcycles) {
  Context partition_context(context);
  improve_impl(phg, partition_context, num_vcycles, nullptr);
}

void improve_mapping(mt_kahypar_partitioned_hypergraph_t phg,
                    TargetGraph& target_graph,
                    const Context& context,
                    const size_t num_vcycles) {
  Context partition_context(context);
  partition_context.partition.objective = Objective::steiner_tree;
  improve_impl(phg, partition_context, num_vcycles, &target_graph);
}

} // namespace lib
