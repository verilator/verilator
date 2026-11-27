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

#include "hypergraph_factory.h"

#include "mt-kahypar/macros.h"
#include "mt-kahypar/definitions.h"
#include "mt-kahypar/io/hypergraph_io.h"
#include "mt-kahypar/datastructures/fixed_vertex_support.h"
#include "mt-kahypar/partition/conversion.h"
#include "mt-kahypar/utils/exception.h"

namespace mt_kahypar {
namespace io {

namespace {

template<typename Hypergraph>
mt_kahypar_hypergraph_t constructHypergraph(const HypernodeID& num_hypernodes,
                                            const HyperedgeID& num_hyperedges,
                                            const HyperedgeVector& hyperedges,
                                            const HyperedgeWeight* hyperedge_weight,
                                            const HypernodeWeight* hypernode_weight,
                                            const HypernodeID num_removed_single_pin_hes,
                                            const bool stable_construction) {
  Hypergraph* hypergraph = new Hypergraph();
  *hypergraph = Hypergraph::Factory::construct(num_hypernodes, num_hyperedges, hyperedges,
    hyperedge_weight, hypernode_weight, stable_construction);
  hypergraph->setNumRemovedHyperedges(num_removed_single_pin_hes);
  return mt_kahypar_hypergraph_t {
    reinterpret_cast<mt_kahypar_hypergraph_s*>(hypergraph), Hypergraph::TYPE };
}

mt_kahypar_hypergraph_t constructHypergraph(const mt_kahypar_hypergraph_type_t& type,
                                            const HypernodeID& num_hypernodes,
                                            const HyperedgeID& num_hyperedges,
                                            const HyperedgeVector& hyperedges,
                                            vec<HyperedgeWeight>& hyperedge_weight,
                                            vec<HypernodeWeight>& hypernode_weight,
                                            const HypernodeID num_removed_single_pin_hes,
                                            const bool stable_construction) {
  switch ( type ) {
    case STATIC_HYPERGRAPH:
      return constructHypergraph<ds::StaticHypergraph>(
        num_hypernodes, num_hyperedges, hyperedges,
        hyperedge_weight.data(), hypernode_weight.data(),
        num_removed_single_pin_hes, stable_construction);
    case STATIC_GRAPH:
      ENABLE_GRAPHS(
        return constructHypergraph<ds::StaticGraph>(
          num_hypernodes, num_hyperedges, hyperedges,
          hyperedge_weight.data(), hypernode_weight.data(),
          num_removed_single_pin_hes, stable_construction);
      )
    case DYNAMIC_HYPERGRAPH:
      ENABLE_HIGHEST_QUALITY(
        return constructHypergraph<ds::DynamicHypergraph>(
          num_hypernodes, num_hyperedges, hyperedges,
          hyperedge_weight.data(), hypernode_weight.data(),
          num_removed_single_pin_hes, stable_construction);
      )
    case DYNAMIC_GRAPH:
      ENABLE_HIGHEST_QUALITY_FOR_GRAPHS(
        return constructHypergraph<ds::DynamicGraph>(
          num_hypernodes, num_hyperedges, hyperedges,
          hyperedge_weight.data(), hypernode_weight.data(),
          num_removed_single_pin_hes, stable_construction);
      )
    case NULLPTR_HYPERGRAPH:
      return mt_kahypar_hypergraph_t { nullptr, NULLPTR_HYPERGRAPH };
  }
  return mt_kahypar_hypergraph_t { nullptr, NULLPTR_HYPERGRAPH };
}

template<typename Hypergraph>
mt_kahypar_hypergraph_t constructGraph(const HypernodeID& num_nodes,
                                       const HyperedgeID& num_edges,
                                       const EdgeVector& edges,
                                       const HyperedgeWeight* edge_weight,
                                       const HypernodeWeight* node_weight,
                                       const bool stable_construction) {
  Hypergraph* graph = new Hypergraph();
  *graph = Hypergraph::Factory::construct_from_graph_edges(num_nodes, num_edges, edges,
    edge_weight, node_weight, stable_construction);
  return mt_kahypar_hypergraph_t {
    reinterpret_cast<mt_kahypar_hypergraph_s*>(graph), Hypergraph::TYPE };
}

mt_kahypar_hypergraph_t constructGraph(const mt_kahypar_hypergraph_type_t& type,
                                            const HypernodeID& num_nodes,
                                            const HyperedgeID& num_edges,
                                            const EdgeVector& edges,
                                            vec<HyperedgeWeight>& edge_weight,
                                            vec<HypernodeWeight>& node_weight,
                                            const bool stable_construction) {
  switch ( type ) {
    case STATIC_GRAPH:
      ENABLE_GRAPHS(
        return constructGraph<ds::StaticGraph>(
          num_nodes, num_edges, edges,
          edge_weight.data(), node_weight.data(), stable_construction);
      )
    case DYNAMIC_GRAPH:
      ENABLE_HIGHEST_QUALITY_FOR_GRAPHS(
        return constructGraph<ds::DynamicGraph>(
          num_nodes, num_edges, edges,
          edge_weight.data(), node_weight.data(), stable_construction);
      )
    case STATIC_HYPERGRAPH:
    case DYNAMIC_HYPERGRAPH:
    case NULLPTR_HYPERGRAPH:
      return mt_kahypar_hypergraph_t { nullptr, NULLPTR_HYPERGRAPH };
  }
  return mt_kahypar_hypergraph_t { nullptr, NULLPTR_HYPERGRAPH };
}

mt_kahypar_hypergraph_t readHMetisFile(const std::string& filename,
                                       const mt_kahypar_hypergraph_type_t& type,
                                       const bool stable_construction,
                                       const bool remove_single_pin_hes,
                                       const bool print_warnings) {
  HyperedgeID num_hyperedges = 0;
  HypernodeID num_hypernodes = 0;
  HyperedgeID num_removed_single_pin_hyperedges = 0;
  HyperedgeVector hyperedges;
  vec<HyperedgeWeight> hyperedges_weight;
  vec<HypernodeWeight> hypernodes_weight;
  readHypergraphFile(filename, num_hyperedges, num_hypernodes,
                     num_removed_single_pin_hyperedges, hyperedges,
                     hyperedges_weight, hypernodes_weight, remove_single_pin_hes, print_warnings);
  return constructHypergraph(type, num_hypernodes, num_hyperedges, hyperedges,
                             hyperedges_weight, hypernodes_weight,
                             num_removed_single_pin_hyperedges, stable_construction);
}

mt_kahypar_hypergraph_t readMetisFile(const std::string& filename,
                                      const mt_kahypar_hypergraph_type_t& type,
                                      const bool stable_construction,
                                      const bool) {
  HyperedgeID num_edges = 0;
  HypernodeID num_vertices = 0;
  vec<HyperedgeWeight> edges_weight;
  vec<HypernodeWeight> nodes_weight;
  if (type == STATIC_GRAPH || type == DYNAMIC_GRAPH) {
    EdgeVector edges;
    readGraphFile(filename, num_edges, num_vertices, edges, edges_weight, nodes_weight);
    return constructGraph(type, num_vertices, num_edges, edges,
                          edges_weight, nodes_weight, stable_construction);
  } else {
    HyperedgeVector edges;
    readGraphFile(filename, num_edges, num_vertices, edges, edges_weight, nodes_weight);
    return constructHypergraph(type, num_vertices, num_edges, edges,
                               edges_weight, nodes_weight, 0, stable_construction);
  }
}

} // namespace

mt_kahypar_hypergraph_t readInputFile(const std::string& filename,
                                      const PresetType& preset,
                                      const InstanceType& instance,
                                      const FileFormat& format,
                                      const bool stable_construction,
                                      const bool remove_single_pin_hes,
                                      const bool print_warnings) {
  mt_kahypar_hypergraph_type_t type = to_hypergraph_c_type(preset, instance);
  switch ( format ) {
    case FileFormat::hMetis: return readHMetisFile(
      filename, type, stable_construction, remove_single_pin_hes, print_warnings);
    case FileFormat::Metis: return readMetisFile(
      filename, type, stable_construction, print_warnings);
  }
  return mt_kahypar_hypergraph_t { nullptr, NULLPTR_HYPERGRAPH };
}

template<typename Hypergraph>
Hypergraph readInputFile(const std::string& filename,
                         const FileFormat& format,
                         const bool stable_construction,
                         const bool remove_single_pin_hes,
                         const bool print_warnings) {
  mt_kahypar_hypergraph_t hypergraph { nullptr, NULLPTR_HYPERGRAPH };
  switch ( format ) {
    case FileFormat::hMetis: hypergraph = readHMetisFile(
      filename, Hypergraph::TYPE, stable_construction, remove_single_pin_hes, print_warnings);
      break;
    case FileFormat::Metis: hypergraph = readMetisFile(
      filename, Hypergraph::TYPE, stable_construction, print_warnings);
  }
  return std::move(utils::cast<Hypergraph>(hypergraph));
}

namespace {

HypernodeID numberOfNodes(mt_kahypar_hypergraph_t hypergraph) {
  switch ( hypergraph.type ) {
    case STATIC_HYPERGRAPH: return utils::cast<ds::StaticHypergraph>(hypergraph).initialNumNodes();
    ENABLE_GRAPHS(case STATIC_GRAPH: return utils::cast<ds::StaticGraph>(hypergraph).initialNumNodes();)
    ENABLE_HIGHEST_QUALITY(case DYNAMIC_HYPERGRAPH: return utils::cast<ds::DynamicHypergraph>(hypergraph).initialNumNodes();)
    ENABLE_HIGHEST_QUALITY_FOR_GRAPHS(case DYNAMIC_GRAPH: return utils::cast<ds::DynamicGraph>(hypergraph).initialNumNodes();)
    case NULLPTR_HYPERGRAPH: return 0;
    default: return 0;
  }
}

template<typename Hypergraph>
void addFixedVertices(Hypergraph& hypergraph,
                      const mt_kahypar_partition_id_t* fixed_vertices,
                      const PartitionID k) {
  ds::FixedVertexSupport<Hypergraph> fixed_vertex_support(
    hypergraph.initialNumNodes(), k);
  fixed_vertex_support.setHypergraph(&hypergraph);
  hypergraph.doParallelForAllNodes([&](const HypernodeID& hn) {
    if ( fixed_vertices[hn] != -1 ) {
      if ( fixed_vertices[hn] < 0 || fixed_vertices[hn] >= k ) {
        throw InvalidInputException(
          "Try to partition hypergraph into " + STR(k) + " blocks, but node " +
           STR(hn) + " is fixed to block " + STR(fixed_vertices[hn]));
      }
      fixed_vertex_support.fixToBlock(hn, fixed_vertices[hn]);
    }
  });
  hypergraph.addFixedVertexSupport(std::move(fixed_vertex_support));
}

template<typename Hypergraph>
void removeFixedVertices(Hypergraph& hypergraph) {
  ds::FixedVertexSupport<Hypergraph> fixed_vertex_support;
  hypergraph.addFixedVertexSupport(std::move(fixed_vertex_support));
}

} // namespace

void addFixedVertices(mt_kahypar_hypergraph_t hypergraph,
                      const mt_kahypar_partition_id_t* fixed_vertices,
                      const PartitionID k) {
  switch ( hypergraph.type ) {
    case STATIC_HYPERGRAPH:
      addFixedVertices(utils::cast<ds::StaticHypergraph>(hypergraph), fixed_vertices, k); break;
    ENABLE_GRAPHS(case STATIC_GRAPH:
      addFixedVertices(utils::cast<ds::StaticGraph>(hypergraph), fixed_vertices, k); break;
    )
    ENABLE_HIGHEST_QUALITY(case DYNAMIC_HYPERGRAPH:
      addFixedVertices(utils::cast<ds::DynamicHypergraph>(hypergraph), fixed_vertices, k); break;
    )
    ENABLE_HIGHEST_QUALITY_FOR_GRAPHS(case DYNAMIC_GRAPH:
      addFixedVertices(utils::cast<ds::DynamicGraph>(hypergraph), fixed_vertices, k); break;
    )
    case NULLPTR_HYPERGRAPH:
    default: break;
  }
}

void addFixedVerticesFromFile(mt_kahypar_hypergraph_t hypergraph,
                              const std::string& filename,
                              const PartitionID k) {
  std::vector<PartitionID> fixed_vertices;
  io::readPartitionFile(filename, numberOfNodes(hypergraph), fixed_vertices);
  addFixedVertices(hypergraph, fixed_vertices.data(), k);
}

void removeFixedVertices(mt_kahypar_hypergraph_t hypergraph) {
  switch ( hypergraph.type ) {
    case STATIC_HYPERGRAPH:
      removeFixedVertices(utils::cast<ds::StaticHypergraph>(hypergraph)); break;
    ENABLE_GRAPHS(case STATIC_GRAPH:
      removeFixedVertices(utils::cast<ds::StaticGraph>(hypergraph)); break;
    )
    ENABLE_HIGHEST_QUALITY(case DYNAMIC_HYPERGRAPH:
      removeFixedVertices(utils::cast<ds::DynamicHypergraph>(hypergraph)); break;
    )
    ENABLE_HIGHEST_QUALITY_FOR_GRAPHS(case DYNAMIC_GRAPH:
      removeFixedVertices(utils::cast<ds::DynamicGraph>(hypergraph)); break;
    )
    case NULLPTR_HYPERGRAPH:
    default: break;
  }
}

namespace {
  #define READ_INPUT_FILE(X) X readInputFile(const std::string& filename,       \
                                             const FileFormat& format,          \
                                             const bool stable_construction,    \
                                             const bool remove_single_pin_hes,  \
                                             const bool logging)
}

INSTANTIATE_FUNC_WITH_HYPERGRAPHS(READ_INPUT_FILE)

#ifndef KAHYPAR_ENABLE_GRAPH_PARTITIONING_FEATURES
template ds::StaticGraph readInputFile(const std::string& filename,
                                       const FileFormat& format,
                                       const bool stable_construction,
                                       const bool remove_single_pin_hes,
                                       const bool logging);
#endif

}  // namespace io
}  // namespace mt_kahypar
