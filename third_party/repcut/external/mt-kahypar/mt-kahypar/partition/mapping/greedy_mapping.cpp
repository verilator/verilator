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

#include "mt-kahypar/partition/mapping/greedy_mapping.h"

#include <numeric>
#include <queue>

#include "mt-kahypar/definitions.h"
#include "mt-kahypar/partition/metrics.h"
#include "mt-kahypar/partition/mapping/kerninghan_lin.h"
#include "mt-kahypar/datastructures/static_graph.h"
#include "mt-kahypar/datastructures/static_bitset.h"
#include "mt-kahypar/parallel/atomic_wrapper.h"
#include "mt-kahypar/utils/randomize.h"
#include "mt-kahypar/utils/utilities.h"

namespace mt_kahypar {

namespace {

static constexpr bool debug = false;

struct PQElement {
  HyperedgeWeight rating;
  HypernodeID u;
};

bool operator<(const PQElement& lhs, const PQElement& rhs) {
  return lhs.rating < rhs.rating || (lhs.rating == rhs.rating && lhs.u < rhs.u);
}

bool operator>(const PQElement& lhs, const PQElement& rhs) {
  return lhs.rating > rhs.rating || (lhs.rating == rhs.rating && lhs.u > rhs.u);
}

using PQ = std::priority_queue<PQElement>;


HypernodeID get_node_with_minimum_weighted_degree(const ds::StaticGraph& graph,
                                                  const Context& context,
                                                  bool deterministic,
                                                  const ds::Bitset& unassigned_processors,
                                                  HypernodeWeight required_weight) {
  vec<HypernodeID> min_nodes;
  HyperedgeWeight min_weighted_degree = std::numeric_limits<HypernodeWeight>::max();
  for ( const HypernodeID& hn : graph.nodes() ) {
    if (!unassigned_processors.isSet(hn)) continue;
    if (context.partition.use_individual_part_weights &&
        context.partition.max_part_weights[hn] < required_weight) continue;

    HyperedgeWeight weighted_degree = 0;
    for ( const HyperedgeID he : graph.incidentEdges(hn) ) {
      weighted_degree += graph.edgeWeight(he);
    }
    if ( weighted_degree < min_weighted_degree ) {
      min_nodes.clear();
      min_nodes.push_back(hn);
      min_weighted_degree = weighted_degree;
    } else if ( weighted_degree == min_weighted_degree ) {
      min_nodes.push_back(hn);
    }
  }
  ASSERT(min_nodes.size() > 0);
  return (deterministic || min_nodes.size() == 1) ? min_nodes[0] :
    min_nodes[utils::Randomize::instance().getRandomInt(
      0, static_cast<int>(min_nodes.size() - 1), THREAD_ID)];
}

template<typename CommunicationHypergraph>
void compute_greedy_mapping(CommunicationHypergraph& communication_hg,
                            const TargetGraph& target_graph,
                            const Context& context,
                            const HypernodeID seed_node) {
  // For each node u, the ratings store weight of all incident hyperedges
  // that connect u to partial assignment
  vec<HyperedgeWeight> rating(communication_hg.initialNumNodes(), 0);
  vec<bool> visited_hes(communication_hg.initialNumEdges(), false);
  vec<bool> up_to_date_ratings(communication_hg.initialNumNodes(), true);
  vec<HypernodeID> nodes_to_update;
  // Marks unassigned processors
  ds::Bitset unassigned_processors(target_graph.numBlocks());
  ds::StaticBitset unassigned_processors_view(
    unassigned_processors.numBlocks(), unassigned_processors.data());
  PQ pq;

  auto check_if_all_nodes_are_assigned = [&]() {
    if ( pq.empty() ) {
      // Check if there are still unassigned nodes.
      // This can happen if the communication hypergraph is not connected
      for ( const HypernodeID& hn : communication_hg.nodes() ) {
        if ( communication_hg.partID(hn) == kInvalidPartition ) {
          ASSERT(up_to_date_ratings[hn]);
          ASSERT(!communication_hg.isFixed(hn));
          pq.push( PQElement { rating[hn], hn } );
          break;
        }
      }
    }
  };

  auto assign = [&](const HypernodeID u,
                    const PartitionID process,
                    bool check_unassigned_nodes) {
    ASSERT(process != kInvalidPartition && process < communication_hg.k());
    ASSERT(unassigned_processors.isSet(process));
    ASSERT(!communication_hg.isFixed(u) || communication_hg.fixedVertexBlock(u) == process);
    communication_hg.setNodePart(u, process);
    up_to_date_ratings[u] = false; // This marks u as assigned
    unassigned_processors.unset(process); // This marks the process as assigned

    DBG << "Assign node" << u << "to process" << process;

    // Update ratings
    nodes_to_update.clear();
    for ( const HyperedgeID& he : communication_hg.incidentEdges(u) ) {
      if ( !visited_hes[he] ) {
        const HyperedgeWeight edge_weight = communication_hg.edgeWeight(he);
        for ( const HypernodeID& pin : communication_hg.pins(he) ) {
          rating[pin] += edge_weight;
          if ( up_to_date_ratings[pin] && !communication_hg.isFixed(pin) ) {
            nodes_to_update.push_back(pin);
            up_to_date_ratings[pin] = false;
          }
        }
        visited_hes[he] = true;
      }
    }

    // Update PQ
    for ( const HypernodeID& hn : nodes_to_update ) {
      pq.push(PQElement { rating[hn], hn });
      up_to_date_ratings[hn] = true;
    }
    if (check_unassigned_nodes) {
      check_if_all_nodes_are_assigned();
    }
  };

  communication_hg.resetPartition();
  // Initialize unassigned processors
  for ( PartitionID block = 0; block < target_graph.numBlocks(); ++block ) {
    unassigned_processors.set(block);
  }
  // Preassign fixed vertices
  if ( communication_hg.hasFixedVertices() ) {
    for ( const HypernodeID& hn : communication_hg.nodes() ) {
      if (communication_hg.isFixed(hn)) {
        PartitionID process = communication_hg.fixedVertexBlock(hn);
        assign(hn, process, false);
      }
    }
  }
  // Assign seed node to process with minimum weighted degree
  const bool deterministic = context.partition.deterministic;
  if (!communication_hg.isFixed(seed_node)) {
    PartitionID best_process = get_node_with_minimum_weighted_degree(target_graph.graph(), context, deterministic,
                                                                     unassigned_processors, communication_hg.nodeWeight(seed_node));
    assign(seed_node, best_process, true);
  }

  // Note: it seems metrics::quality actually handles the unassigned nodes correctly
  HyperedgeWeight actual_objective =
    communication_hg.hasFixedVertices() ? metrics::quality(communication_hg, Objective::steiner_tree) : 0;
  vec<PartitionID> tie_breaking;
  vec<HyperedgeWeight> tmp_ratings(communication_hg.initialNumNodes(), 0);
  while ( !pq.empty() ) {
    const PQElement best = pq.top();
    const HypernodeID u = best.u;
    pq.pop();
    ASSERT(!communication_hg.isFixed(u));

    if ( !up_to_date_ratings[u] ) {
      check_if_all_nodes_are_assigned();
      continue;
    }

    ASSERT(communication_hg.partID(u) == kInvalidPartition);
    // Assign node with the strongest connection to the partial assignment
    // to the process that minimizes the steiner tree metric.
    for ( const HyperedgeID& he : communication_hg.incidentEdges(u) ) {
      ds::Bitset& connectivity_set = communication_hg.deepCopyOfConnectivitySet(he);
      const HyperedgeWeight edge_weight = communication_hg.edgeWeight(he);
      const HyperedgeWeight distance_before = communication_hg.connectivity(he) > 0 ?
        target_graph.distance(connectivity_set) : 0;
      for ( const PartitionID process : unassigned_processors_view ) {
        const HyperedgeWeight distance_after =
          target_graph.distanceWithBlock(connectivity_set, process);
        tmp_ratings[process] += (distance_after - distance_before) * edge_weight;
      }
    }

    // Determine processor that would result in the least increase of the
    // steiner tree metric.
    HyperedgeWeight best_rating = std::numeric_limits<HyperedgeWeight>::max();
    bool best_is_balanced = false;
    const HypernodeWeight node_weight = communication_hg.nodeWeight(u);
    for ( const PartitionID process : unassigned_processors_view ) {
      const bool is_balanced = !context.partition.use_individual_part_weights
        || node_weight <= context.partition.max_part_weights[process];
      const bool is_at_least_as_balanced = is_balanced || !best_is_balanced;
      best_is_balanced |= is_balanced;
      if ( (is_balanced && !best_is_balanced) || (is_at_least_as_balanced && tmp_ratings[process] < best_rating) ) {
        tie_breaking.clear();
        tie_breaking.push_back(process);
        best_rating = tmp_ratings[process];
      } else if ( is_at_least_as_balanced && tmp_ratings[process] == best_rating ) {
        tie_breaking.push_back(process);
      }
      tmp_ratings[process] = 0;
    }

    // Assign node to processor that results in the least increase of the objective function
    ASSERT(tie_breaking.size() > 0);
    const PartitionID best_process = (deterministic || tie_breaking.size() == 1) ? tie_breaking[0] :
      tie_breaking[utils::Randomize::instance().getRandomInt(
        0, static_cast<int>(tie_breaking.size() - 1), THREAD_ID)];
    actual_objective += best_rating;
    assign(u, best_process, true);
  }
  ASSERT(actual_objective == metrics::quality(communication_hg, Objective::steiner_tree));
  ASSERT([&] {
    for ( const HypernodeID hn : communication_hg.nodes() ) {
      if ( communication_hg.partID(hn) == kInvalidPartition ) {
        return false;
      }
    }
    return true;
  }(), "There are unassigned nodes");
  DBG << "Greedy mapping algorithm with seed node" << seed_node
      << "produced an mapping with solution quality" << actual_objective;
}

} // namespace

template<typename CommunicationHypergraph>
void GreedyMapping<CommunicationHypergraph>::mapToTargetGraph(CommunicationHypergraph& communication_hg,
                                                              const TargetGraph& target_graph,
                                                              const Context& context) {
  ASSERT(communication_hg.initialNumNodes() == target_graph.graph().initialNumNodes());

  utils::Timer& timer = utils::Utilities::instance().getTimer(context.utility_id);
  SpinLock best_lock;
  Metrics best_metrics;
  best_metrics.quality = metrics::quality(communication_hg, Objective::steiner_tree);
  best_metrics.imbalance = metrics::imbalance(communication_hg, context);
  HypernodeID best_hn_id = kInvalidHypernode;
  vec<PartitionID> best_mapping(communication_hg.initialNumNodes(), 0);
  std::iota(best_mapping.begin(), best_mapping.end(), 0);

  timer.start_timer("initial_mapping", "Initial Mapping");
  communication_hg.doParallelForAllNodes([&](const HypernodeID& hn) {
    // Compute greedy mapping with the current node as seed node
    CommunicationHypergraph tmp_communication_phg(
      target_graph.numBlocks(), communication_hg.hypergraph());
    tmp_communication_phg.setTargetGraph(&target_graph);
    compute_greedy_mapping(tmp_communication_phg, target_graph, context, hn);

    if ( context.mapping.use_local_search ) {
      KerninghanLin<CommunicationHypergraph>::improve(tmp_communication_phg, target_graph, context);
    }

    // Check if new mapping is better than the currently best mapping
    Metrics current_metrics;
    current_metrics.quality = metrics::quality(tmp_communication_phg, Objective::steiner_tree);
    current_metrics.imbalance = metrics::imbalance(tmp_communication_phg, context);
    best_lock.lock();
    if ( current_metrics.isBetter(best_metrics) ||
         (current_metrics.isEqual(best_metrics) && hn > best_hn_id) ) {
      best_metrics = current_metrics;
      best_hn_id = hn;
      for ( const HypernodeID& u : tmp_communication_phg.nodes() ) {
        best_mapping[u] = tmp_communication_phg.partID(u);
      }
    }
    best_lock.unlock();
  });
  timer.stop_timer("initial_mapping");

  // Apply best mapping
  communication_hg.resetPartition();
  for ( const HypernodeID& hn : communication_hg.nodes() ) {
    communication_hg.setOnlyNodePart(hn, best_mapping[hn]);
  }
  communication_hg.initializePartition();
}

INSTANTIATE_CLASS_WITH_PARTITIONED_HG(GreedyMapping)

}  // namespace kahypar
