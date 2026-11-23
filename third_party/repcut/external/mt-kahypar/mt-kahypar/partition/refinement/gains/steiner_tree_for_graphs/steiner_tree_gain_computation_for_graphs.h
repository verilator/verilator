/*******************************************************************************
 * MIT License
 *
 * This file is part of Mt-KaHyPar.
 *
 * Copyright (C) 2019 Tobias Heuer <tobias.heuer@kit.edu>
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

#include <vector>

#include <tbb/enumerable_thread_specific.h>

#include "mt-kahypar/partition/refinement/gains/gain_computation_base.h"
#include "mt-kahypar/partition/refinement/gains/steiner_tree_for_graphs/steiner_tree_attributed_gains_for_graphs.h"
#include "mt-kahypar/partition/mapping/target_graph.h"
#include "mt-kahypar/datastructures/static_bitset.h"
#include "mt-kahypar/datastructures/sparse_map.h"
#include "mt-kahypar/parallel/stl/scalable_vector.h"

namespace mt_kahypar {

class GraphSteinerTreeGainComputation : public GainComputationBase<GraphSteinerTreeGainComputation, GraphSteinerTreeAttributedGains> {
  using Base = GainComputationBase<GraphSteinerTreeGainComputation, GraphSteinerTreeAttributedGains>;

  static constexpr bool enable_heavy_assert = false;
  static constexpr size_t BITS_PER_BLOCK = ds::StaticBitset::BITS_PER_BLOCK;

 public:
  using RatingMap = typename Base::RatingMap;

  static constexpr bool is_independent_of_block = false;

  GraphSteinerTreeGainComputation(const Context& context,
                                     bool disable_randomization = false) :
    Base(context, disable_randomization),
    _local_adjacent_blocks([&] { return constructBitset(); }),
    _all_blocks(context.partition.k),
    _ets_incident_edge_weights([&] { return constructIncidentEdgeWeightVector(); }) {
    for ( PartitionID to = 0; to < context.partition.k; ++to )  {
      _all_blocks.set(to);
    }
  }

  // ! Precomputes the gain to all adjacent blocks.
  // ! Conceptually, we compute the gain of moving the node to an non-adjacent block
  // ! and the gain to all adjacent blocks assuming the node is in an isolated block.
  // ! The gain of that node to a block to can then be computed by
  // ! 'isolated_block_gain - tmp_scores[to]' (see gain(...))
  template<typename PartitionedHypergraph>
  void precomputeGains(const PartitionedHypergraph& phg,
                       const HypernodeID hn,
                       RatingMap& tmp_scores,
                       Gain&,
                       const bool consider_non_adjacent_blocks) {
    ASSERT(tmp_scores.size() == 0, "Rating map not empty");

    // The gain of moving a node u from its current block Π[u] to target block V_j can
    // be expressed as follows for the steiner tree objective function:
    // g(u, V_j) := \sum_{ {u,v} \in I(u) } ( dist(V_j, Π[v]) - dist(Π[u],Π[v]) ) * w(u,v)
    // Here, dist(V',V'') is the shortest path between block V' and V'' in the target graph.
    // Computing the gain to all adjacent blocks of the nodes has a time complexity of
    // O(|I(u)|*|R(u)|) where R(u) is the set of all adjacent blocks of node u and I(u) is
    // the set of all incident edges of node u.
    // In the following, we use the following reformulation of the gain:
    // gain(u, V_j) := \sum_{V_k \in R(u)} (dist(V_j, V_k) - dist(Π[u], V_k)) * w(u, V_k)
    // Here, w(u, V_k) is the weight of all edges connecting u to block V_k which can be
    // precomputed in O(|I(u)|) time. After precomputation, we can compute the gain
    // to all adjacent blocks in time O(|R(u)|²) => total gain computation complexity than
    // is O(|I(u)| * |R(u)|²) which is faster than the naive approach.

    // Precompute adjacent blocks of node and the w(u, V_k) terms
    const PartitionID from = phg.partID(hn);
    vec<HyperedgeWeight>& incident_edge_weights = _ets_incident_edge_weights.local();
    ds::Bitset& adjacent_blocks = consider_non_adjacent_blocks ?
      _all_blocks : _local_adjacent_blocks.local();
    ds::StaticBitset adjacent_blocks_view(
      adjacent_blocks.numBlocks(), adjacent_blocks.data());
    adjacent_blocks.set(from);
    for (const HyperedgeID& he : phg.incidentEdges(hn)) {
      const PartitionID block_of_target = phg.partID(phg.edgeTarget(he));
      adjacent_blocks.set(block_of_target);
      incident_edge_weights[block_of_target] += phg.edgeWeight(he);
    }

    // Gain computation
    // gain(u, V_j) := \sum_{V_k \in R(u)} (dist(V_j, V_k) - dist(Π[u], V_k)) * w(u, V_k)
    ASSERT(phg.hasTargetGraph());
    const TargetGraph& target_graph = *phg.targetGraph();
    for ( const PartitionID& j : adjacent_blocks_view ) {
      for ( const PartitionID k : adjacent_blocks_view ) {
        tmp_scores[j] -= ( target_graph.distance(from, k) -
          target_graph.distance(j, k) ) * incident_edge_weights[k];
      }
    }

    for ( const PartitionID& to : adjacent_blocks_view ) {
      incident_edge_weights[to] = 0;
    }
  }

  HyperedgeWeight gain(const Gain to_score,
                       const Gain) {
    return to_score;
  }

  void changeNumberOfBlocksImpl(const PartitionID new_k) {
    ASSERT(new_k == _context.partition.k);
    for ( auto& adjacent_blocks : _local_adjacent_blocks ) {
      adjacent_blocks.resize(new_k);
    }
    _all_blocks.resize(new_k);
    for ( PartitionID to = 0; to < new_k; ++to )  {
      _all_blocks.set(to);
    }
    for ( auto& incident_edge_weights : _ets_incident_edge_weights ) {
      incident_edge_weights.assign(new_k, 0);
    }
  }

 private:
  ds::Bitset constructBitset() const {
    return ds::Bitset(_context.partition.k);
  }

  vec<HyperedgeWeight> constructIncidentEdgeWeightVector() const {
    return vec<HyperedgeWeight>(_context.partition.k, 0);
  }

  using Base::_context;

  // ! Before gain computation, we construct a bitset that contains all
  // ! adjacent nodes of a block
  tbb::enumerable_thread_specific<ds::Bitset> _local_adjacent_blocks;
  ds::Bitset _all_blocks;

  // ! Array for precomputing the weight of all edges connecting a node to a particular block
  tbb::enumerable_thread_specific<vec<HyperedgeWeight>> _ets_incident_edge_weights;
};

}  // namespace mt_kahypar
