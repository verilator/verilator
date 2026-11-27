/*******************************************************************************
 * MIT License
 *
 * This file is part of Mt-KaHyPar.
 *
 * Copyright (C) 2019 Lars Gottesbüren <lars.gottesbueren@kit.edu>
 * Copyright (C) 2019 Tobias Heuer <tobias.heuer@kit.edu>
 * Copyright (C) 2021 Nikolai Maas <nikolai.maas@student.kit.edu>
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

#include "static_graph_factory.h"

#include <limits>

#include <tbb/parallel_for.h>
#include <tbb/parallel_invoke.h>

#include "mt-kahypar/parallel/parallel_prefix_sum.h"
#include "mt-kahypar/parallel/stl/scalable_vector.h"
#include "mt-kahypar/utils/timer.h"
#include "mt-kahypar/utils/exception.h"

namespace mt_kahypar::ds {
  void StaticGraphFactory::sort_incident_edges(StaticGraph& graph) {
    parallel::scalable_vector<HyperedgeID> edge_ids_of_node;
    edge_ids_of_node.resize(graph._edges.size());
    // sort incident edges of each node, so their ordering is independent of scheduling
    // (and the same as a typical sequential implementation)
    tbb::parallel_for(ID(0), graph._num_nodes, [&](HypernodeID u) {
      const HyperedgeID start = graph.node(u).firstEntry();
      const HyperedgeID end = graph.node(u + 1).firstEntry();
      for (HyperedgeID id = 0; id < end - start; ++id) {
        edge_ids_of_node[start + id] = id;
      }
      std::sort(edge_ids_of_node.begin() + start, edge_ids_of_node.begin() + end, [&](HyperedgeID& a, HyperedgeID& b) {
        return graph.edge(start + a).target() < graph.edge(start + b).target();
      });

      // apply permutation
      // (yes, this applies the permutation defined by edge_ids_of_node, don't think about it)
      for (size_t i = 0; i < end - start; ++i) {
        HyperedgeID target = edge_ids_of_node[start + i];
        while (target < i) {
          target = edge_ids_of_node[start + target];
        }
        std::swap(graph._edges[start + i], graph._edges[start + target]);
        std::swap(graph._unique_edge_ids[start + i], graph._unique_edge_ids[start + target]);
      }
    });
  }

  StaticGraph StaticGraphFactory::construct(
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

  StaticGraph StaticGraphFactory::construct_from_graph_edges(
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

    StaticGraph graph;
    graph._num_nodes = num_nodes;
    graph._num_edges = 2 * num_edges;
    graph._nodes.resize(num_nodes + 1);
    graph._edges.resize(2 * num_edges);
    graph._unique_edge_ids.resize(2 * num_edges);

    // Compute degree for each vertex
    ThreadLocalCounter local_degree_per_vertex(num_nodes);
    tbb::parallel_for(ID(0), num_edges, [&](const size_t pos) {
      Counter& num_degree_per_vertex = local_degree_per_vertex.local();
      const HypernodeID pins[2] = {edge_vector[pos].first, edge_vector[pos].second};
      if (pins[0] == pins[1]) {
        throw InvalidInputException("Edge " + STR(pos) + " has identical source and target: " + STR(pins[0]) + " " + STR(pins[0]));
      }

      for (const HypernodeID& pin : pins) {
        if (pin >= num_nodes) {
          throw InvalidInputException("Edge " + STR(pos) + " points to invalid node: " + STR(pin));
        }
        ++num_degree_per_vertex[pin];
      }
    });

    // We sum up the degree per vertex only thread local. To obtain the
    // global degree, we iterate over each thread local counter and sum it up.
    Counter num_degree_per_vertex(num_nodes, 0);
    for (Counter& c : local_degree_per_vertex) {
      tbb::parallel_for(ID(0), num_nodes, [&](const size_t pos) {
        num_degree_per_vertex[pos] += c[pos];
      });
    }

    // Compute prefix sum over the degrees. The prefix sum is used than
    // as start position for each node in the edge array.
    parallel::TBBPrefixSum<size_t> degree_prefix_sum(num_degree_per_vertex);
    tbb::parallel_scan(tbb::blocked_range<size_t>( UL(0), UI64(num_nodes)), degree_prefix_sum);

    ASSERT(degree_prefix_sum.total_sum() == 2 * num_edges);

    AtomicCounter incident_edges_position(num_nodes,
                                         parallel::IntegralAtomicWrapper<size_t>(0));

    auto setup_edges = [&] {
      tbb::parallel_for(ID(0), num_edges, [&](const size_t pos) {
        const HypernodeID pin0 = edge_vector[pos].first;
        const HyperedgeID incident_edges_pos0 = degree_prefix_sum[pin0] +
                incident_edges_position[pin0].fetch_add(1, std::memory_order_relaxed);
        ASSERT(incident_edges_pos0 < graph._edges.size());
        StaticGraph::Edge& edge0 = graph._edges[incident_edges_pos0];
        const HypernodeID pin1 = edge_vector[pos].second;
        const HyperedgeID incident_edges_pos1 = degree_prefix_sum[pin1] +
                incident_edges_position[pin1].fetch_add(1, std::memory_order_relaxed);
        ASSERT(incident_edges_pos1 < graph._edges.size());
        StaticGraph::Edge& edge1 = graph._edges[incident_edges_pos1];

        edge0.setTarget(pin1);
        edge0.setSource(pin0);
        edge1.setTarget(pin0);
        edge1.setSource(pin1);

        graph._unique_edge_ids[incident_edges_pos0] = pos;
        graph._unique_edge_ids[incident_edges_pos1] = pos;

        if (edge_weight) {
          edge0.setWeight(edge_weight[pos]);
          edge1.setWeight(edge_weight[pos]);
        }
      });
    };

    auto setup_nodes = [&] {
      tbb::parallel_for(ID(0), num_nodes, [&](const size_t pos) {
        StaticGraph::Node& node = graph._nodes[pos];
        node.enable();
        node.setFirstEntry(degree_prefix_sum[pos]);
        if ( node_weight ) {
          node.setWeight(node_weight[pos]);
        }
      });
    };

    auto init_communities = [&] {
      graph._community_ids.resize(num_nodes, 0);
    };

    tbb::parallel_invoke(setup_edges, setup_nodes, init_communities);

    // Add Sentinel
    graph._nodes.back() = StaticGraph::Node(graph._edges.size());
    if (stable_construction_of_incident_edges) {
      sort_incident_edges(graph);
    }
    graph.computeAndSetTotalNodeWeight(parallel_tag_t());
    return graph;
  }
}