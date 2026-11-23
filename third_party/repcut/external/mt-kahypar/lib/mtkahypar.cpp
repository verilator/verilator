/*******************************************************************************
 * MIT License
 *
 * This file is part of Mt-KaHyPar.
 *
 * Copyright (C) 2020 Lars Gottesbüren <lars.gottesbueren@kit.edu>
 * Copyright (C) 2020 Tobias Heuer <tobias.heuer@kit.edu>
 * Copyright (C) 2024 Nikolai Maas <nikolai.maas@kit.edu>
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

#include <algorithm>
#include <cctype>
#include <charconv>
#include <cstring>
#include <memory>
#include <optional>
#include <sstream>
#include <string>
#include <type_traits>

#include "include/mtkahypar.h"
#include "include/mtkahypartypes.h"
#include "include/lib_generic_impls.h"
#include "include/lib_helper_functions.h"

#include "tbb/parallel_for.h"

#include "mt-kahypar/definitions.h"
#include "mt-kahypar/partition/context.h"
#include "mt-kahypar/partition/metrics.h"
#include "mt-kahypar/partition/conversion.h"
#include "mt-kahypar/partition/mapping/target_graph.h"
#include "mt-kahypar/parallel/stl/scalable_vector.h"
#include "mt-kahypar/io/hypergraph_factory.h"
#include "mt-kahypar/io/hypergraph_io.h"
#include "mt-kahypar/macros.h"
#include "mt-kahypar/utils/delete.h"
#include "mt-kahypar/utils/exception.h"
#include "mt-kahypar/utils/randomize.h"

using namespace mt_kahypar;

namespace {
  using StaticHypergraphFactory = typename ds::StaticHypergraph::Factory;
  using DynamicHypergraphFactory = typename ds::DynamicHypergraph::Factory;
  using StaticGraphFactory = typename ds::StaticGraph::Factory;
  using DynamicGraphFactory = typename ds::DynamicGraph::Factory;

  using StaticPartitionedHypergraph = typename StaticHypergraphTypeTraits::PartitionedHypergraph;
  using DynamicPartitionedHypergraph = typename DynamicHypergraphTypeTraits::PartitionedHypergraph;
  using SparsePartitionedHypergraph = typename LargeKHypergraphTypeTraits::PartitionedHypergraph;
  using StaticPartitionedGraph = typename StaticGraphTypeTraits::PartitionedHypergraph;
  using DynamicPartitionedGraph = typename DynamicGraphTypeTraits::PartitionedHypergraph;

  PresetType to_preset_type(mt_kahypar_preset_type_t preset) {
    switch ( preset ) {
      case DETERMINISTIC: return PresetType::deterministic;
      case DETERMINISTIC_QUALITY: return PresetType::deterministic_quality;
      case LARGE_K: return PresetType::large_k;
      case DEFAULT: return PresetType::default_preset;
      case QUALITY: return PresetType::quality;
      case HIGHEST_QUALITY: return PresetType::highest_quality;
    }
    return PresetType::UNDEFINED;
  }

  mt_kahypar_preset_type_t from_preset_type(PresetType preset) {
    switch ( preset ) {
      case PresetType::deterministic: return DETERMINISTIC;
      case PresetType::deterministic_quality: return DETERMINISTIC_QUALITY;
      case PresetType::large_k: return LARGE_K;
      case PresetType::default_preset: return DEFAULT;
      case PresetType::quality: return QUALITY;
      case PresetType::highest_quality: return HIGHEST_QUALITY;
      case PresetType::UNDEFINED: return static_cast<mt_kahypar_preset_type_t>(0);
    }
    return static_cast<mt_kahypar_preset_type_t>(0);
  }

  mt_kahypar_error_t to_error(mt_kahypar_status_t status, const char* msg) {
    mt_kahypar_error_t result;
    result.status = status;
    size_t msg_len = std::strlen(msg);
    char* c_msg = static_cast<char*>(malloc(msg_len + 1));
    if (c_msg != nullptr) {
      std::strcpy(c_msg, msg);
      result.msg = c_msg;
      result.msg_len = msg_len;
    }
    return result;
  }

  mt_kahypar_error_t to_error(const std::exception& ex) {
    if (dynamic_cast<const InvalidInputException*>(&ex) != nullptr) {
      return to_error(mt_kahypar_status_t::INVALID_INPUT, ex.what());
    } else if (dynamic_cast<const InvalidParameterException*>(&ex) != nullptr) {
      return to_error(mt_kahypar_status_t::INVALID_PARAMETER, ex.what());
    } else if (dynamic_cast<const UnsupportedOperationException*>(&ex) != nullptr) {
      return to_error(mt_kahypar_status_t::UNSUPPORTED_OPERATION, ex.what());
    } else if (dynamic_cast<const SystemException*>(&ex) != nullptr) {
      return to_error(mt_kahypar_status_t::SYSTEM_ERROR, ex.what());
    }
    return to_error(mt_kahypar_status_t::OTHER_ERROR, ex.what());
  }

  std::optional<bool> string_to_bool(const char* input) {
    std::string val(input);
    std::transform(val.begin(), val.end(), val.begin(),
      [](unsigned char c){ return std::tolower(c); });
    if (val == "t" || val == "y" || val == "1" || val == "true" || val == "yes") {
      return true;
    } else if (val == "f" || val == "n" || val == "0" || val == "false" || val == "no") {
      return false;
    } else {
      return {};
    }
  }
}


void mt_kahypar_free_context(mt_kahypar_context_t* context) {
  if (context == nullptr) {
    return;
  }
  delete reinterpret_cast<Context*>(context);
}

mt_kahypar_context_t* mt_kahypar_context_from_file(const char* ini_file_name,
                                                   mt_kahypar_error_t* error) {
  try {
    Context* context = new Context(lib::context_from_file(ini_file_name));
    return reinterpret_cast<mt_kahypar_context_t*>(context);
  } catch ( std::exception& ex ) {
    *error = to_error(ex);
    return nullptr;
  }
}

mt_kahypar_context_t* mt_kahypar_context_from_string(const char* ini_text,
                                                     mt_kahypar_error_t* error) {
  try {
    if (!ini_text) {
      throw InvalidInputException("Configuration text must not be NULL");
    }
    auto context = std::make_unique<Context>(false);
    std::istringstream input(ini_text);
    parseIniToContext(*context, input, true);
    return reinterpret_cast<mt_kahypar_context_t*>(context.release());
  } catch ( std::exception& ex ) {
    *error = to_error(ex);
    return nullptr;
  }
}

mt_kahypar_context_t* mt_kahypar_context_from_preset(const mt_kahypar_preset_type_t preset) {
  Context* context = new Context(lib::context_from_preset(to_preset_type(preset)));
  return reinterpret_cast<mt_kahypar_context_t*>(context);
}

mt_kahypar_status_t mt_kahypar_set_context_parameter(mt_kahypar_context_t* context,
                                                     const mt_kahypar_context_parameter_type_t type,
                                                     const char* value,
                                                     mt_kahypar_error_t* error) {
  auto report_conversion_error = [&](const char* expected) {
    std::string msg = std::string("Invalid parameter value \"") + value + "\", expected: " + expected;
    *error = to_error(mt_kahypar_status_t::INVALID_PARAMETER, msg.c_str());
  };
  auto parse_number = [&](auto& context_parameter, const char* expected) {
    try {
      context_parameter = std::stod(value);
      return mt_kahypar_status_t::SUCCESS;
    } catch (const std::exception&) {
      report_conversion_error(expected);
      return mt_kahypar_status_t::INVALID_PARAMETER;
    }
  };

  Context& c = *reinterpret_cast<Context*>(context);
  switch(type) {
    case NUM_BLOCKS: return parse_number(c.partition.k, "positive integer");
    case EPSILON: return parse_number(c.partition.epsilon, "floating point number");
    case NUM_VCYCLES: return parse_number(c.partition.num_vcycles, "positive integer");
    case OBJECTIVE: {
      std::string objective(value);
      if ( objective == "km1" ) {
        c.partition.objective = Objective::km1;
        return mt_kahypar_status_t::SUCCESS;
      } else if ( objective == "cut" ) {
        c.partition.objective = Objective::cut;
        return mt_kahypar_status_t::SUCCESS;
      } else if ( objective == "soed" ) {
        c.partition.objective = Objective::soed;
        return mt_kahypar_status_t::SUCCESS;
      }
      report_conversion_error("one of km1, cut, soed");
      return mt_kahypar_status_t::INVALID_PARAMETER;
    }
    case VERBOSE: {
      std::optional<bool> result = string_to_bool(value);
      if (result.has_value()) {
        c.partition.enable_logging = *result;
        c.partition.verbose_logging = *result;
        return mt_kahypar_status_t::SUCCESS;
      } else {
        report_conversion_error("boolean");
        return mt_kahypar_status_t::INVALID_PARAMETER;
      }
    }
  }
  *error = to_error(mt_kahypar_status_t::INVALID_PARAMETER,
                    "Type must be a valid value of mt_kahypar_context_parameter_type_t");
  return mt_kahypar_status_t::INVALID_PARAMETER;
}

void mt_kahypar_set_partitioning_parameters(mt_kahypar_context_t* context,
                                            const mt_kahypar_partition_id_t num_blocks,
                                            const double epsilon,
                                            const mt_kahypar_objective_t objective) {
  Context& c = *reinterpret_cast<Context*>(context);
  c.partition.k = num_blocks;
  c.partition.epsilon = epsilon;
  switch ( objective ) {
    case CUT:
      c.partition.objective = Objective::cut; break;
    case KM1:
      c.partition.objective = Objective::km1; break;
    case SOED:
      c.partition.objective = Objective::soed; break;
  }
}

mt_kahypar_preset_type_t mt_kahypar_get_preset(const mt_kahypar_context_t* context) {
  return from_preset_type(reinterpret_cast<const Context*>(context)->partition.preset_type);
}

mt_kahypar_partition_id_t mt_kahypar_get_num_blocks(const mt_kahypar_context_t* context) {
  return reinterpret_cast<const Context*>(context)->partition.k;
}

double mt_kahypar_get_epsilon(const mt_kahypar_context_t* context) {
  return reinterpret_cast<const Context*>(context)->partition.epsilon;
}

mt_kahypar_objective_t mt_kahypar_get_objective(const mt_kahypar_context_t* context) {
  switch ( reinterpret_cast<const Context*>(context)->partition.objective) {
    case Objective::cut:
      return CUT;
    case Objective::km1:
      return KM1;
    case Objective::soed:
      return SOED;
    case Objective::steiner_tree:
    case Objective::UNDEFINED:
      return static_cast<mt_kahypar_objective_t>(0);
      // omit default case to trigger compiler warning for missing cases
  }
  return static_cast<mt_kahypar_objective_t>(0);
}

void mt_kahypar_set_seed(const size_t seed) {
  utils::Randomize::instance().setSeed(seed);
}

void mt_kahypar_set_individual_target_block_weights(mt_kahypar_context_t* context,
                                                    const mt_kahypar_partition_id_t num_blocks,
                                                    const mt_kahypar_hypernode_weight_t* block_weights) {
  lib::set_individual_block_weights(reinterpret_cast<Context&>(*context), num_blocks, block_weights);
}

void mt_kahypar_initialize(const size_t num_threads, const bool interleaved_allocations) {
  lib::initialize(num_threads, interleaved_allocations, false);
}

void mt_kahypar_free_error_content(mt_kahypar_error_t* error) {
  free(const_cast<char*>(error->msg));
  error->status = mt_kahypar_status_t::SUCCESS;
  error->msg = nullptr;
  error->msg_len = 0;
}

mt_kahypar_hypergraph_t mt_kahypar_read_hypergraph_from_file(const char* file_name,
                                                             const mt_kahypar_context_t* context,
                                                             const mt_kahypar_file_format_type_t file_format,
                                                             mt_kahypar_error_t* error) {
  const Context& c = *reinterpret_cast<const Context*>(context);
  const InstanceType instance = file_format == HMETIS ? InstanceType::hypergraph : InstanceType::graph;
  const FileFormat format = file_format == HMETIS ? FileFormat::hMetis : FileFormat::Metis;
  try {
    return lib::hypergraph_from_file(file_name, c, instance, format);
  } catch ( std::exception& ex ) {
    *error = to_error(ex);
  }
  return mt_kahypar_hypergraph_t { nullptr, NULLPTR_HYPERGRAPH };
}

mt_kahypar_target_graph_t* mt_kahypar_read_target_graph_from_file(const char* file_name,
                                                                  const mt_kahypar_context_t* context,
                                                                  mt_kahypar_error_t* error) {
  const Context& c = *reinterpret_cast<const Context*>(context);
  TargetGraph* target_graph = nullptr;
  try {
    ds::StaticGraph graph = io::readInputFile<ds::StaticGraph>(file_name, FileFormat::Metis, /*stable_construnction=*/true,
                                                               /*remove_single_pin_hes=*/true, c.partition.enable_logging);
    target_graph = new TargetGraph(std::move(graph));
  } catch ( std::exception& ex ) {
    *error = to_error(ex);
  }
  return reinterpret_cast<mt_kahypar_target_graph_t*>(target_graph);
}


mt_kahypar_hypergraph_t mt_kahypar_create_hypergraph(const mt_kahypar_context_t* context,
                                                     const mt_kahypar_hypernode_id_t num_vertices,
                                                     const mt_kahypar_hyperedge_id_t num_hyperedges,
                                                     const size_t* hyperedge_indices,
                                                     const mt_kahypar_hypernode_id_t* hyperedges,
                                                     const mt_kahypar_hyperedge_weight_t* hyperedge_weights,
                                                     const mt_kahypar_hypernode_weight_t* vertex_weights,
                                                     mt_kahypar_error_t* error) {
  const Context& c = *reinterpret_cast<const Context*>(context);
  try {
    return lib::create_hypergraph_from_adjacency_array(
      c, num_vertices, num_hyperedges, hyperedge_indices, hyperedges, hyperedge_weights, vertex_weights);
  } catch ( std::exception& ex ) {
    *error = to_error(ex);
  }
  return mt_kahypar_hypergraph_t { nullptr, NULLPTR_HYPERGRAPH };
}

mt_kahypar_hypergraph_t mt_kahypar_create_graph(const mt_kahypar_context_t* context,
                                                const mt_kahypar_hypernode_id_t num_vertices,
                                                const mt_kahypar_hyperedge_id_t num_edges,
                                                const mt_kahypar_hypernode_id_t* edges,
                                                const mt_kahypar_hyperedge_weight_t* edge_weights,
                                                const mt_kahypar_hypernode_weight_t* vertex_weights,
                                                mt_kahypar_error_t* error) {
  // Transform adjacence array into adjacence list
  vec<std::pair<mt_kahypar::HypernodeID, mt_kahypar::HypernodeID>> edge_vector(num_edges);

  const Context& c = *reinterpret_cast<const Context*>(context);
  try {
    tbb::parallel_for<mt_kahypar::HyperedgeID>(0, num_edges, [&](const mt_kahypar::HyperedgeID& he) {
      lib::check_overflow<HypernodeID>(edges[2*he], "endpoint of edge");
      lib::check_overflow<HypernodeID>(edges[2*he + 1], "endpoint of edge");
      edge_vector[he] = std::make_pair(edges[2*he], edges[2*he + 1]);
    });
    return lib::create_graph(c, num_vertices, num_edges, edge_vector, edge_weights, vertex_weights);
  } catch ( std::exception& ex ) {
    *error = to_error(ex);
  }
  return mt_kahypar_hypergraph_t { nullptr, NULLPTR_HYPERGRAPH };
}

mt_kahypar_target_graph_t* mt_kahypar_create_target_graph(const mt_kahypar_context_t* context,
                                                          const mt_kahypar_hypernode_id_t num_vertices,
                                                          const mt_kahypar_hyperedge_id_t num_edges,
                                                          const mt_kahypar_hypernode_id_t* edges,
                                                          const mt_kahypar_hyperedge_weight_t* edge_weights,
                                                          mt_kahypar_error_t* error) {
  unused(context);
  // Transform adjacency array into adjacence list
  vec<std::pair<mt_kahypar::HypernodeID, mt_kahypar::HypernodeID>> edge_vector(num_edges);
  tbb::parallel_for<mt_kahypar::HyperedgeID>(0, num_edges, [&](const mt_kahypar::HyperedgeID& he) {
    edge_vector[he] = std::make_pair(edges[2*he], edges[2*he + 1]);
  });

  TargetGraph* target_graph = nullptr;
  try {
    ds::StaticGraph graph = StaticGraphFactory::construct_from_graph_edges(
      num_vertices, num_edges, edge_vector, edge_weights, nullptr, true);
    target_graph = new TargetGraph(std::move(graph));
  } catch ( std::exception& ex ) {
    *error = to_error(ex);
  }
  return reinterpret_cast<mt_kahypar_target_graph_t*>(target_graph);
}


void mt_kahypar_free_hypergraph(mt_kahypar_hypergraph_t hypergraph) {
  utils::delete_hypergraph(hypergraph);
}

void mt_kahypar_free_target_graph(mt_kahypar_target_graph_t* target_graph) {
  if ( target_graph ) {
    delete reinterpret_cast<TargetGraph*>(target_graph);
  }
}

void mt_kahypar_free_partitioned_hypergraph(mt_kahypar_partitioned_hypergraph_t partitioned_hg) {
  utils::delete_partitioned_hypergraph(partitioned_hg);
}

mt_kahypar_hypernode_id_t mt_kahypar_num_hypernodes(mt_kahypar_hypergraph_t hypergraph) {
  return lib::num_nodes<false>(hypergraph);
}

mt_kahypar_hyperedge_id_t mt_kahypar_num_hyperedges(mt_kahypar_hypergraph_t hypergraph) {
  return lib::num_edges<false>(hypergraph);
}

mt_kahypar_hypernode_id_t mt_kahypar_num_pins(mt_kahypar_hypergraph_t hypergraph) {
  return lib::num_pins<false>(hypergraph);
}

mt_kahypar_hypernode_id_t mt_kahypar_hypergraph_weight(mt_kahypar_hypergraph_t hypergraph) {
  return lib::total_weight<false>(hypergraph);
}

mt_kahypar_hyperedge_id_t mt_kahypar_hypernode_degree(mt_kahypar_hypergraph_t hypergraph, mt_kahypar_hypernode_id_t node) {
  return lib::node_degree<false>(hypergraph, node);
}

mt_kahypar_hypernode_weight_t mt_kahypar_hypernode_weight(mt_kahypar_hypergraph_t hypergraph, mt_kahypar_hypernode_id_t node) {
  return lib::node_weight<false>(hypergraph, node);
}

mt_kahypar_hypernode_id_t mt_kahypar_hyperedge_size(mt_kahypar_hypergraph_t hypergraph, mt_kahypar_hyperedge_id_t edge) {
  return lib::edge_size<false>(hypergraph, edge);
}

mt_kahypar_hyperedge_weight_t mt_kahypar_hyperedge_weight(mt_kahypar_hypergraph_t hypergraph, mt_kahypar_hyperedge_id_t edge) {
  return lib::edge_weight<false>(hypergraph, edge);
}

mt_kahypar_hyperedge_id_t mt_kahypar_get_incident_hyperedges(mt_kahypar_hypergraph_t hypergraph,
                                                             mt_kahypar_hypernode_id_t node,
                                                             mt_kahypar_hyperedge_id_t* edge_buffer) {
  return lib::switch_hg<mt_kahypar_hyperedge_id_t, false>(hypergraph, [&](auto& hg) {
    HyperedgeID i = 0;
    for (HypernodeID he: hg.incidentEdges(node)) {
      edge_buffer[i++] = he;
    }
    return i;
  });
}

mt_kahypar_hypernode_id_t mt_kahypar_get_hyperedge_pins(mt_kahypar_hypergraph_t hypergraph,
                                                        mt_kahypar_hyperedge_id_t edge,
                                                        mt_kahypar_hypernode_id_t* pin_buffer) {
  return lib::switch_hg<mt_kahypar_hypernode_id_t, false>(hypergraph, [&](auto& hg) {
    HypernodeID i = 0;
    for (HypernodeID hn: hg.pins(edge)) {
      pin_buffer[i++] = hn;
    }
    return i;
  });
}

bool mt_kahypar_is_graph(mt_kahypar_hypergraph_t hypergraph) {
  return hypergraph.type == STATIC_GRAPH || hypergraph.type == DYNAMIC_GRAPH;
}

mt_kahypar_hypernode_id_t mt_kahypar_edge_source(mt_kahypar_hypergraph_t graph, mt_kahypar_hyperedge_id_t edge) {
  return lib::switch_graph<mt_kahypar_hypernode_id_t, false>(graph, [=](auto& hg) {
    return hg.edgeSource(edge);
  });
}

mt_kahypar_hypernode_id_t mt_kahypar_edge_target(mt_kahypar_hypergraph_t graph, mt_kahypar_hyperedge_id_t edge) {
  return lib::switch_graph<mt_kahypar_hypernode_id_t, false>(graph, [=](auto& hg) {
    return hg.edgeTarget(edge);
  });
}


mt_kahypar_status_t mt_kahypar_add_fixed_vertices(mt_kahypar_hypergraph_t hypergraph,
                                                  const mt_kahypar_partition_id_t* fixed_vertices,
                                                  mt_kahypar_partition_id_t num_blocks,
                                                  mt_kahypar_error_t* error) {
  try {
    io::addFixedVertices(hypergraph, fixed_vertices, num_blocks);
    return mt_kahypar_status_t::SUCCESS;
  } catch ( std::exception& ex ) {
    *error = to_error(ex);
    return error->status;
  }
}

mt_kahypar_status_t mt_kahypar_read_fixed_vertices_from_file(const char* file_name,
                                                             mt_kahypar_hypernode_id_t num_nodes,
                                                             mt_kahypar_partition_id_t* fixed_vertices,
                                                             mt_kahypar_error_t* error) {
  try {
    io::readPartitionFile(file_name, num_nodes, fixed_vertices);
    return mt_kahypar_status_t::SUCCESS;
  } catch ( std::exception& ex ) {
    *error = to_error(ex);
    return error->status;
  }
}


mt_kahypar_status_t mt_kahypar_add_fixed_vertices_from_file(mt_kahypar_hypergraph_t hypergraph,
                                                            const char* file_name,
                                                            mt_kahypar_partition_id_t num_blocks,
                                                            mt_kahypar_error_t* error) {
  try {
    io::addFixedVerticesFromFile(hypergraph, file_name, num_blocks);
    return mt_kahypar_status_t::SUCCESS;
  } catch ( std::exception& ex ) {
    *error = to_error(ex);
    return error->status;
  }
}

void mt_kahypar_remove_fixed_vertices(mt_kahypar_hypergraph_t hypergraph) {
  io::removeFixedVertices(hypergraph);
}

bool mt_kahypar_is_fixed_vertex(mt_kahypar_hypergraph_t hypergraph, mt_kahypar_hypernode_id_t node) {
  return lib::is_fixed<false>(hypergraph, node);
}

mt_kahypar_partition_id_t mt_kahypar_fixed_vertex_block(mt_kahypar_hypergraph_t hypergraph, mt_kahypar_hypernode_id_t node) {
  return lib::fixed_vertex_block<false>(hypergraph, node);
}

bool mt_kahypar_check_compatibility(mt_kahypar_hypergraph_t hypergraph,
                                    mt_kahypar_preset_type_t preset) {
  return lib::is_compatible(hypergraph, preset);
}

mt_kahypar_partitioned_hypergraph_t mt_kahypar_partition(mt_kahypar_hypergraph_t hypergraph,
                                                         const mt_kahypar_context_t* context,
                                                         mt_kahypar_error_t* error) {
  try {
    return lib::partition(hypergraph, reinterpret_cast<const Context&>(*context));
  } catch ( std::exception& ex ) {
    *error = to_error(ex);
  }
  return mt_kahypar_partitioned_hypergraph_t { nullptr, NULLPTR_PARTITION };
}

mt_kahypar_partitioned_hypergraph_t mt_kahypar_map(mt_kahypar_hypergraph_t hypergraph,
                                                   mt_kahypar_target_graph_t* target_graph,
                                                   const mt_kahypar_context_t* context,
                                                   mt_kahypar_error_t* error) {
  try {
    return lib::map(hypergraph,
                    reinterpret_cast<TargetGraph&>(*target_graph),
                    reinterpret_cast<const Context&>(*context));
  } catch ( std::exception& ex ) {
    *error = to_error(ex);
  }
  return mt_kahypar_partitioned_hypergraph_t { nullptr, NULLPTR_PARTITION };
}

MT_KAHYPAR_API bool mt_kahypar_check_partition_compatibility(mt_kahypar_partitioned_hypergraph_t partitioned_hg,
                                                             mt_kahypar_preset_type_t preset) {
  return lib::is_compatible(partitioned_hg, preset);
}

mt_kahypar_status_t mt_kahypar_improve_partition(mt_kahypar_partitioned_hypergraph_t partitioned_hg,
                                                 const mt_kahypar_context_t* context,
                                                 const size_t num_vcycles,
                                                 mt_kahypar_error_t* error) {
  try {
    lib::improve(partitioned_hg, reinterpret_cast<const Context&>(*context), num_vcycles);
    return mt_kahypar_status_t::SUCCESS;
  } catch ( std::exception& ex ) {
    *error = to_error(ex);
    return error->status;
  }
}

mt_kahypar_status_t mt_kahypar_improve_mapping(mt_kahypar_partitioned_hypergraph_t partitioned_hg,
                                               mt_kahypar_target_graph_t* target_graph,
                                               const mt_kahypar_context_t* context,
                                               const size_t num_vcycles,
                                               mt_kahypar_error_t* error) {
  try {
    lib::improve_mapping(partitioned_hg,
                         reinterpret_cast<TargetGraph&>(*target_graph),
                         reinterpret_cast<const Context&>(*context),
                         num_vcycles);
    return mt_kahypar_status_t::SUCCESS;
  } catch ( std::exception& ex ) {
    *error = to_error(ex);
    return error->status;
  }
}

mt_kahypar_partitioned_hypergraph_t mt_kahypar_create_partitioned_hypergraph(mt_kahypar_hypergraph_t hypergraph,
                                                                             const mt_kahypar_context_t* context,
                                                                             const mt_kahypar_partition_id_t num_blocks,
                                                                             const mt_kahypar_partition_id_t* partition,
                                                                             mt_kahypar_error_t* error) {
  const Context& c = reinterpret_cast<const Context&>(*context);
  try {
    return lib::create_partitioned_hypergraph(hypergraph, c, num_blocks, partition);
  } catch ( std::exception& ex ) {
    *error = to_error(ex);
  }
  return mt_kahypar_partitioned_hypergraph_t { nullptr, NULLPTR_PARTITION };
}

mt_kahypar_partitioned_hypergraph_t mt_kahypar_read_partition_from_file(mt_kahypar_hypergraph_t hypergraph,
                                                                        const mt_kahypar_context_t* context,
                                                                        const mt_kahypar_partition_id_t num_blocks,
                                                                        const char* partition_file,
                                                                        mt_kahypar_error_t* error) {
  std::vector<PartitionID> partition;
  const Context& c = reinterpret_cast<const Context&>(*context);
  try {
    io::readPartitionFile(partition_file, mt_kahypar_num_hypernodes(hypergraph), partition);
    return lib::create_partitioned_hypergraph(hypergraph, c, num_blocks, partition.data());
  } catch ( std::exception& ex ) {
    *error = to_error(ex);
  }
  return mt_kahypar_partitioned_hypergraph_t { nullptr, NULLPTR_PARTITION };
}

mt_kahypar_status_t mt_kahypar_write_partition_to_file(const mt_kahypar_partitioned_hypergraph_t partitioned_hg,
                                                       const char* partition_file,
                                                       mt_kahypar_error_t* error) {
  try {
    lib::write_partition_to_file<true>(partitioned_hg, partition_file);
    return mt_kahypar_status_t::SUCCESS;
  } catch ( std::exception& ex ) {
    *error = to_error(ex);
    return error->status;
  }
}


mt_kahypar_partition_id_t mt_kahypar_num_blocks(const mt_kahypar_partitioned_hypergraph_t partitioned_hg) {
  return lib::num_blocks<false>(partitioned_hg);
}

mt_kahypar_hypernode_weight_t mt_kahypar_block_weight(const mt_kahypar_partitioned_hypergraph_t partitioned_hg,
                                                      const mt_kahypar_partition_id_t block) {
  return lib::block_weight<false>(partitioned_hg, block);
}

mt_kahypar_partition_id_t mt_kahypar_block_id(const mt_kahypar_partitioned_hypergraph_t partitioned_hg,
                                              const mt_kahypar_hypernode_id_t node) {
  return lib::block_id<false>(partitioned_hg, node);
}

mt_kahypar_hyperedge_id_t mt_kahypar_num_incident_cut_hyperedges(const mt_kahypar_partitioned_hypergraph_t partitioned_hg,
                                                                 const mt_kahypar_hypernode_id_t node)  {
  return lib::num_incident_cut_edges<false>(partitioned_hg, node);
}

mt_kahypar_partition_id_t mt_kahypar_connectivity(const mt_kahypar_partitioned_hypergraph_t partitioned_hg,
                                                  const mt_kahypar_hyperedge_id_t edge) {
  return lib::connectivity<false>(partitioned_hg, edge);
}

mt_kahypar_hypernode_id_t mt_kahypar_num_pins_in_block(const mt_kahypar_partitioned_hypergraph_t partitioned_hg,
                                                       const mt_kahypar_hyperedge_id_t edge,
                                                       const mt_kahypar_partition_id_t block) {
  return lib::num_pins_in_block<false>(partitioned_hg, edge, block);
}

void mt_kahypar_get_partition(const mt_kahypar_partitioned_hypergraph_t partitioned_hg, mt_kahypar_partition_id_t* partition) {
  lib::get_partition<false>(partitioned_hg, partition);
}

void mt_kahypar_get_block_weights(const mt_kahypar_partitioned_hypergraph_t partitioned_hg, mt_kahypar_hypernode_weight_t* block_weights) {
  lib::get_block_weights<false>(partitioned_hg, block_weights);
}

double mt_kahypar_imbalance(const mt_kahypar_partitioned_hypergraph_t partitioned_hg, const mt_kahypar_context_t* context) {
  return lib::imbalance<false>(partitioned_hg, *reinterpret_cast<const Context*>(context));
}

mt_kahypar_hyperedge_weight_t mt_kahypar_cut(const mt_kahypar_partitioned_hypergraph_t partitioned_hg) {
  return lib::cut<false>(partitioned_hg);
}

mt_kahypar_hyperedge_weight_t mt_kahypar_km1(const mt_kahypar_partitioned_hypergraph_t partitioned_hg) {
  return lib::km1<false>(partitioned_hg);
}

mt_kahypar_hyperedge_weight_t mt_kahypar_soed(const mt_kahypar_partitioned_hypergraph_t partitioned_hg) {
  return lib::soed<false>(partitioned_hg);
}

mt_kahypar_hyperedge_weight_t mt_kahypar_steiner_tree(const mt_kahypar_partitioned_hypergraph_t partitioned_hg,
                                                      mt_kahypar_target_graph_t* target_graph) {
  TargetGraph* target = reinterpret_cast<TargetGraph*>(target_graph);
  if ( !target->isInitialized() ) {
    target->precomputeDistances(4);
  }
  return lib::switch_phg<mt_kahypar_hyperedge_weight_t, false>(partitioned_hg, [&](auto& phg) {
    phg.setTargetGraph(target);
    return metrics::quality(phg, Objective::steiner_tree);
  });
}
