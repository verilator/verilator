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

#include "mt-kahypar/partition/mapping/kerninghan_lin.h"

#include "mt-kahypar/definitions.h"
#include "mt-kahypar/partition/metrics.h"
#include "mt-kahypar/partition/mapping/target_graph.h"
#include "mt-kahypar/datastructures/static_bitset.h"

namespace mt_kahypar {

namespace {

template<typename CommunicationHypergraph>
MT_KAHYPAR_ATTRIBUTE_ALWAYS_INLINE void vertex_swap(CommunicationHypergraph& communication_hg,
                                             const HypernodeID u,
                                             const HypernodeID v) {
  const PartitionID block_of_u = communication_hg.partID(u);
  const PartitionID block_of_v = communication_hg.partID(v);
  ASSERT(block_of_u != block_of_v);
  communication_hg.changeNodePart(u, block_of_u, block_of_v);
  communication_hg.changeNodePart(v, block_of_v, block_of_u);
}

MT_KAHYPAR_ATTRIBUTE_ALWAYS_INLINE HyperedgeWeight swap_gain(const TargetGraph& target_graph,
                                                             ds::Bitset& connectivity_set,
                                                             const HyperedgeWeight edge_weight,
                                                             const PartitionID removed_block,
                                                             const PartitionID new_block) {
  ASSERT(connectivity_set.isSet(removed_block));
  ASSERT(!connectivity_set.isSet(new_block));
  // Current distance between all nodes in the connectivity set
  const HyperedgeWeight distance_before = target_graph.distance(connectivity_set);
  // Distance between all nodes in the connectivity set after the swap operation
  const HyperedgeWeight distance_after =
    target_graph.distanceAfterExchangingBlocks(connectivity_set, removed_block, new_block);
  return (distance_before - distance_after) * edge_weight;
}

// This function computes the gain of swapping the blocks of node u and v
// in the communication hypergraph for the steiner tree metric.
template<typename CommunicationHypergraph>
MT_KAHYPAR_ATTRIBUTE_ALWAYS_INLINE HyperedgeWeight swap_gain(CommunicationHypergraph& communication_hg,
                                                             const TargetGraph& target_graph,
                                                             const HypernodeID u,
                                                             const HypernodeID v,
                                                             vec<bool>& marked_hes) {
  HyperedgeWeight gain = 0;
  const PartitionID block_of_u = communication_hg.partID(u);
  const PartitionID block_of_v = communication_hg.partID(v);

  // Note that hyperedges that contain u and v have zero gain since their
  // connectivity set does not change due to the swap operation.
  // We therefore mark all incident hyperedges of u and only compute the
  // gain for hyperedges that are not in the intersection of u and v.
  for ( const HyperedgeID& he : communication_hg.incidentEdges(u) ) {
    marked_hes[communication_hg.uniqueEdgeID(he)] = true;
  }

  for ( const HyperedgeID& he : communication_hg.incidentEdges(v) ) {
    const HyperedgeID unique_id = communication_hg.uniqueEdgeID(he);
    if ( !marked_hes[unique_id] ) {
      // Hyperedge only contains v => compute swap gain
      ds::Bitset& connectivity_set = communication_hg.deepCopyOfConnectivitySet(he);
      gain += swap_gain(target_graph, connectivity_set,
        communication_hg.edgeWeight(he), block_of_v, block_of_u);
    } else {
      // Hyperedge contains u and v => unmark hyperedge
      marked_hes[unique_id] = false;
    }
  }

  for ( const HyperedgeID& he : communication_hg.incidentEdges(u) ) {
    const HyperedgeID unique_id = communication_hg.uniqueEdgeID(he);
    if ( marked_hes[unique_id] ) {
      // Hyperedge only contains u => compute swap gain
      ds::Bitset& connectivity_set = communication_hg.deepCopyOfConnectivitySet(he);
      gain += swap_gain(target_graph, connectivity_set,
        communication_hg.edgeWeight(he), block_of_u, block_of_v);
      marked_hes[unique_id] = false;
    }
  }

  return gain;
}

using Swap = std::pair<HypernodeID, HypernodeID>;

struct PQElement {
  HyperedgeWeight gain;
  Swap swap;
};

bool operator<(const PQElement& lhs, const PQElement& rhs) {
  return lhs.gain < rhs.gain || (lhs.gain == rhs.gain && lhs.swap < rhs.swap);
}

bool operator>(const PQElement& lhs, const PQElement& rhs) {
  return lhs.gain > rhs.gain || (lhs.gain == rhs.gain && lhs.swap > rhs.swap);
}

using PQ = std::priority_queue<PQElement>;

}

template<typename CommunicationHypergraph>
void KerninghanLin<CommunicationHypergraph>::improve(CommunicationHypergraph& communication_hg,
                                                     const TargetGraph& target_graph,
                                                     const Context& context) {
  ASSERT(communication_hg.initialNumNodes() == target_graph.graph().initialNumNodes());

  HyperedgeWeight current_objective = metrics::quality(communication_hg, Objective::steiner_tree, false);
  vec<bool> marked_hes(communication_hg.initialNumEdges(), false);
  bool found_improvement = true;
  size_t fruitless_rounds = 0;
  size_t pass_nr = 1;
  while ( found_improvement ) {
    DBG << "Start of pass" << pass_nr << "( Current Objective =" << current_objective << ")";
    found_improvement = false;
    HyperedgeWeight objective_before = current_objective;

    // Initialize priority queue
    PQ pq;
    for ( const HypernodeID& u : communication_hg.nodes() ) {
      if (communication_hg.isFixed(u)) continue;

      for ( const HypernodeID& v : communication_hg.nodes() ) {
        if (communication_hg.isFixed(v)) continue;

        bool weight_is_valid = !context.partition.use_individual_part_weights ||
          (communication_hg.nodeWeight(u) <= context.partition.max_part_weights[communication_hg.partID(v)] &&
           communication_hg.nodeWeight(v) <= context.partition.max_part_weights[communication_hg.partID(u)]);
        if ( u < v && weight_is_valid ) {
          const HyperedgeWeight gain = swap_gain(communication_hg, target_graph, u, v, marked_hes);
          pq.push(PQElement { gain, std::make_pair(u, v) });
        }
      }
    }

    // Perform swap operations
    int best_idx = 0;
    HyperedgeWeight best_objective = current_objective;
    vec<PQElement> performed_swaps;
    vec<bool> already_moved(communication_hg.initialNumNodes(), false);
    while ( !pq.empty() ) {
      const PQElement elem = pq.top();
      pq.pop();
      const HyperedgeWeight gain = elem.gain;
      const HypernodeID u = elem.swap.first;
      const HypernodeID v = elem.swap.second;

      if ( already_moved[u] || already_moved[v] ) {
        // Each node can move at most once in each round
        continue;
      }

      // Recompute gain
      const HyperedgeWeight recomputed_gain = swap_gain(communication_hg, target_graph, u, v, marked_hes);
      if ( gain != recomputed_gain ) {
        // Lazy update of PQ
        // Note that since we do not immediately update the PQ after a swap operation, we may not be
        // able do perform the node swap with highest gain. However, the lazy update strategy ensures
        // that the gains are accurate and give a good estimate.
        pq.push(PQElement { recomputed_gain, elem.swap });
        continue;
      }

      // Perform swap
      vertex_swap(communication_hg, u, v);
      current_objective -= gain;
      performed_swaps.push_back(elem);
      already_moved[u] = true;
      already_moved[v] = true;
      DBG << "Swap block ID of nodes" << u << "and" << v << "with gain" << gain
          << "( New Objective =" << current_objective << ")";
      if ( current_objective <= best_objective ) {
        best_idx = performed_swaps.size();
        best_objective = current_objective;
      }
      ASSERT(current_objective == metrics::quality(communication_hg, Objective::steiner_tree));
    }

    // Rollback to best seen solution
    for ( int i = performed_swaps.size() - 1; i >= best_idx; --i ) {
      const PQElement& elem = performed_swaps[i];
      vertex_swap(communication_hg, elem.swap.first, elem.swap.second);
      current_objective += elem.gain;
    }
    ASSERT(current_objective == metrics::quality(communication_hg, Objective::steiner_tree));
    ASSERT(current_objective == best_objective);

    if ( current_objective == objective_before ) {
      ++fruitless_rounds;
    } else {
      fruitless_rounds = 0;
    }

    found_improvement = best_idx > 0 && fruitless_rounds <= MAX_NUMBER_OF_FRUITLESS_ROUNDS;
    ++pass_nr;
  }
  DBG << "Local Search Result =" << current_objective << "\n";
}

INSTANTIATE_CLASS_WITH_PARTITIONED_HG(KerninghanLin)

}  // namespace kahypar
