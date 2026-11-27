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
#include "mt-kahypar/partition/refinement/gains/steiner_tree/steiner_tree_attributed_gains.h"
#include "mt-kahypar/partition/mapping/target_graph.h"
#include "mt-kahypar/datastructures/static_bitset.h"
#include "mt-kahypar/datastructures/sparse_map.h"
#include "mt-kahypar/parallel/stl/scalable_vector.h"

namespace mt_kahypar {

class SteinerTreeGainComputation : public GainComputationBase<SteinerTreeGainComputation, SteinerTreeAttributedGains> {
  using Base = GainComputationBase<SteinerTreeGainComputation, SteinerTreeAttributedGains>;

  static constexpr bool enable_heavy_assert = false;
  static constexpr size_t BITS_PER_BLOCK = ds::StaticBitset::BITS_PER_BLOCK;

 public:
  using RatingMap = typename Base::RatingMap;

  static constexpr bool is_independent_of_block = false;

  SteinerTreeGainComputation(const Context& context,
                                bool disable_randomization = false) :
    Base(context, disable_randomization),
    _local_adjacent_blocks([&] { return constructBitset(); }),
    _all_blocks(context.partition.k) {
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

    // Compute all adjacent blocks of node
    ds::Bitset& adjacent_blocks = consider_non_adjacent_blocks ?
      _all_blocks : _local_adjacent_blocks.local();
    ds::StaticBitset adjacent_blocks_view(
      adjacent_blocks.numBlocks(), adjacent_blocks.data());
    if ( !consider_non_adjacent_blocks ) {
      adjacent_blocks.reset();
      for (const HyperedgeID& he : phg.incidentEdges(hn)) {
        for ( const PartitionID& block : phg.connectivitySet(he) ) {
          adjacent_blocks.set(block);
        }
      }
    }

    // Gain computation
    ASSERT(phg.hasTargetGraph());
    const TargetGraph* target_graph = phg.targetGraph();
    PartitionID from = phg.partID(hn);
    for (const HyperedgeID& he : phg.incidentEdges(hn)) {
      HypernodeID pin_count_in_from_part = phg.pinCountInPart(he, from);
      HyperedgeWeight he_weight = phg.edgeWeight(he);
      ds::Bitset& connectivity_set = phg.deepCopyOfConnectivitySet(he);
      const HyperedgeWeight distance_before = target_graph->distance(connectivity_set);

      if ( pin_count_in_from_part == 1 ) {
        // Moving the node out of its current block removes
        // its block from the connectivity set
        connectivity_set.unset(from);
      }
      // Other gain computation techniques only iterate over the connectivity set
      // of a hyperedge to compute the gain. They assume that the gain is the same
      // for all non-adjacent blocks. However, this is not the case for steiner tree metric.
      // The gain to non-adjacent blocks could be different because they induce different
      // distances in the target graph. We therefore have to consider all adjacent blocks
      // of the node to compute the correct gain.
      for ( const PartitionID to : adjacent_blocks_view ) {
        const HyperedgeWeight distance_after =
          target_graph->distanceWithBlock(connectivity_set, to);
        tmp_scores[to] += (distance_after - distance_before) * he_weight;
      }
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
  }

 private:
  ds::Bitset constructBitset() const {
    return ds::Bitset(_context.partition.k);
  }

  using Base::_context;

  // ! Before gain computation, we construct a bitset that contains all
  // ! adjacent nodes of a block
  tbb::enumerable_thread_specific<ds::Bitset> _local_adjacent_blocks;
  ds::Bitset _all_blocks;
};

}  // namespace mt_kahypar
