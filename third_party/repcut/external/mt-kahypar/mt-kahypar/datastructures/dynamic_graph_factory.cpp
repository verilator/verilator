/*******************************************************************************
 * MIT License
 *
 * This file is part of Mt-KaHyPar.
 *
 * Copyright (C) 2019 Lars Gottesbüren <lars.gottesbueren@kit.edu>
 * Copyright (C) 2019 Tobias Heuer <tobias.heuer@kit.edu>
 * Copyright (C) 2022 Nikolai Maas <nikolai.maas@student.kit.edu>
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

#include "dynamic_graph_factory.h"

#include <limits>

#include <tbb/parallel_for.h>
#include <tbb/parallel_invoke.h>

#include "mt-kahypar/parallel/parallel_prefix_sum.h"
#include "mt-kahypar/parallel/stl/scalable_vector.h"
#include "mt-kahypar/utils/timer.h"
#include "mt-kahypar/utils/exception.h"

namespace mt_kahypar::ds {

DynamicGraph DynamicGraphFactory::construct(
        const HypernodeID num_nodes,
        const HyperedgeID num_edges,
        const HyperedgeVector& edge_vector,
        const HyperedgeWeight* edge_weight,
        const HypernodeWeight* node_weight,
        const bool stable_construction_of_incident_edges) {
  ASSERT(edge_vector.size() == num_edges);

  EdgeVector edges;
  edges.resize(num_edges);
  tbb::parallel_for(UL(0), edge_vector.size(), [&](const size_t i) {
    const auto& e = edge_vector[i];
    if (e.size() != 2) {
      throw InvalidInputException(
        "Using graph data structure; but the input hypergraph is not a graph.");
    }
    edges[i] = std::make_pair(e[0], e[1]);
  });
  return construct_from_graph_edges(num_nodes, num_edges, edges,
    edge_weight, node_weight, stable_construction_of_incident_edges);
}

DynamicGraph DynamicGraphFactory::construct_from_graph_edges(
        const HypernodeID num_nodes,
        const HyperedgeID num_edges,
        const EdgeVector& edge_vector,
        const HyperedgeWeight* edge_weight,
        const HypernodeWeight* node_weight,
        const bool stable_construction_of_incident_edges) {
  if (num_edges > std::numeric_limits<HyperedgeID>::max() / 2) {
    std::string msg = std::string("number of edges overflows ID range (note: graph edges are duplicated, require +1 bit)");
    if constexpr (sizeof(HyperedgeID) < 8) {
      msg += "; build with -DKAHYPAR_USE_64_BIT_IDS=ON to support larger ID ranges";
    }
    throw InvalidInputException(msg);
  }
  if (edge_vector.size() != num_edges) {
    throw InvalidInputException("Number of edges does not match length of input data!");
  }

  DynamicGraph graph;
  graph._num_edges = 2 * num_edges;

  tbb::parallel_invoke([&] {
    graph._nodes.resize(num_nodes + 1);
    tbb::parallel_for(ID(0), num_nodes, [&](const HypernodeID n) {
      // setup nodes
      DynamicGraph::Node& node = graph._nodes[n];
      node.enable();
      if ( node_weight ) {
        node.setWeight(node_weight[n]);
      }
    });
  }, [&] {
    graph._adjacency_array = DynamicAdjacencyArray(num_nodes, edge_vector, edge_weight);
    if (stable_construction_of_incident_edges) {
      graph._adjacency_array.sortIncidentEdges();
    }
  }, [&] {
    graph._acquired_nodes.assign(
      num_nodes, parallel::IntegralAtomicWrapper<bool>(false));
  }, [&] {
    graph._contraction_tree.initialize(num_nodes);
  });

  // Compute total weight of graph
  graph.computeAndSetTotalNodeWeight(parallel_tag_t());
  return graph;
}


std::pair<DynamicGraph, parallel::scalable_vector<HypernodeID> > DynamicGraphFactory::compactify(const DynamicGraph& graph) {
  HypernodeID num_nodes = 0;
  HyperedgeID num_edges = 0;
  parallel::scalable_vector<HypernodeID> hn_mapping;
  parallel::scalable_vector<HyperedgeID> he_mapping;
  // Computes a mapping for vertices and edges to a consecutive range of IDs
  // in the compactified hypergraph via a parallel prefix sum
  tbb::parallel_invoke([&] {
    hn_mapping.assign(graph.numNodes() + 1, 0);
    graph.doParallelForAllNodes([&](const HypernodeID hn) {
      hn_mapping[hn + 1] = ID(1);
    });

    parallel::TBBPrefixSum<HypernodeID, parallel::scalable_vector> hn_mapping_prefix_sum(hn_mapping);
    tbb::parallel_scan(tbb::blocked_range<size_t>(
      UL(0), graph.numNodes() + 1), hn_mapping_prefix_sum);
    num_nodes = hn_mapping_prefix_sum.total_sum();
  }, [&] {
    he_mapping.assign(graph._num_edges + 1, 0);
    graph.doParallelForAllEdges([&](const HyperedgeID& he) {
      if (graph.edgeSource(he) < graph.edgeTarget(he)) {
        he_mapping[he + 1] = ID(1);
      }
    });

    parallel::TBBPrefixSum<HyperedgeID, parallel::scalable_vector> he_mapping_prefix_sum(he_mapping);
    tbb::parallel_scan(tbb::blocked_range<size_t>(
      UL(0), graph._num_edges + 1), he_mapping_prefix_sum);
    num_edges = he_mapping_prefix_sum.total_sum();
  });

  // Remap pins of each hyperedge
  parallel::scalable_vector<std::pair<HypernodeID, HypernodeID>> edge_vector;
  parallel::scalable_vector<HyperedgeWeight> edge_weights;
  parallel::scalable_vector<HypernodeWeight> node_weights;
  tbb::parallel_invoke([&] {
    node_weights.resize(num_nodes);
    graph.doParallelForAllNodes([&](const HypernodeID hn) {
      const HypernodeID mapped_hn = hn_mapping[hn];
      ASSERT(mapped_hn < num_nodes);
      node_weights[mapped_hn] = graph.nodeWeight(hn);
    });
  }, [&] {
    edge_vector.resize(num_edges);
    edge_weights.resize(num_edges);
    graph.doParallelForAllEdges([&](const HyperedgeID he) {
      if (graph.edgeSource(he) < graph.edgeTarget(he)) {
        const HyperedgeID mapped_he = he_mapping[he];
        ASSERT(mapped_he < num_edges);
        edge_weights[mapped_he] = graph.edgeWeight(he);
        edge_vector[mapped_he] = {hn_mapping[graph.edgeSource(he)], hn_mapping[graph.edgeTarget(he)]};
      }
    });
  });

  // Construct compactified graph
  DynamicGraph compactified_graph = DynamicGraphFactory::construct_from_graph_edges(
    num_nodes, num_edges, edge_vector, edge_weights.data(), node_weights.data());
  compactified_graph._total_weight = graph._total_weight;

  tbb::parallel_invoke([&] {
    // Set community ids
    graph.doParallelForAllNodes([&](const HypernodeID& hn) {
      const HypernodeID mapped_hn = hn_mapping[hn];
      compactified_graph.setCommunityID(mapped_hn, graph.communityID(hn));
    });
  }, [&] {
    if ( graph.hasFixedVertices() ) {
      // Set fixed vertices
      ds::FixedVertexSupport<DynamicGraph> fixed_vertices(
        compactified_graph.initialNumNodes(), graph._fixed_vertices.numBlocks());
      fixed_vertices.setHypergraph(&compactified_graph);
      graph.doParallelForAllNodes([&](const HypernodeID& hn) {
        if ( graph.isFixed(hn) ) {
          const HypernodeID mapped_hn = hn_mapping[hn];
          fixed_vertices.fixToBlock(mapped_hn, graph.fixedVertexBlock(hn));
        }
      });
      compactified_graph.addFixedVertexSupport(std::move(fixed_vertices));
    }
  });

  parallel::parallel_free(he_mapping, edge_weights, node_weights, edge_vector);

  return std::make_pair(std::move(compactified_graph), std::move(hn_mapping));
}

}
