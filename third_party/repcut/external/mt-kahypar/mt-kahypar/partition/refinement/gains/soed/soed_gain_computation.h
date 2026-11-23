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

#include "mt-kahypar/partition/refinement/gains/gain_computation_base.h"
#include "mt-kahypar/partition/refinement/gains/soed/soed_attributed_gains.h"
#include "mt-kahypar/datastructures/sparse_map.h"
#include "mt-kahypar/parallel/stl/scalable_vector.h"

namespace mt_kahypar {

class SoedGainComputation : public GainComputationBase<SoedGainComputation, SoedAttributedGains> {
  using Base = GainComputationBase<SoedGainComputation, SoedAttributedGains>;

  static constexpr bool enable_heavy_assert = false;

 public:
  using RatingMap = typename Base::RatingMap;

  static constexpr bool is_independent_of_block = true;

  SoedGainComputation(const Context& context,
                      bool disable_randomization = false) :
    Base(context, disable_randomization) { }

  // ! Precomputes the gain to all adjacent blocks.
  // ! Conceptually, we compute the gain of moving the node to an non-adjacent block
  // ! and the gain to all adjacent blocks assuming the node is in an isolated block.
  // ! The gain of that node to a block to can then be computed by
  // ! 'isolated_block_gain - tmp_scores[to]' (see gain(...))
  template<typename PartitionedHypergraph>
  void precomputeGains(const PartitionedHypergraph& phg,
                       const HypernodeID hn,
                       RatingMap& tmp_scores,
                       Gain& isolated_block_gain,
                       const bool) {
    ASSERT(tmp_scores.size() == 0, "Rating map not empty");
    PartitionID from = phg.partID(hn);
    for (const HyperedgeID& he : phg.incidentEdges(hn)) {
      const HypernodeID edge_size = phg.edgeSize(he);

      if ( edge_size > 1 ) {
        HypernodeID pin_count_in_from_part = phg.pinCountInPart(he, from);
        HyperedgeWeight he_weight = phg.edgeWeight(he);

        // In case, there is more one than one pin left in from part, we would
        // increase the connectivity, if we would move the pin to one block
        // not contained in the connectivity set. In such cases, we can only
        // increase the connectivity of a hyperedge and therefore gather
        // the edge weight of all those edges and add it later to move gain
        // to all other blocks. There is one percularity. If the hyperedge is not
        // a cut edge, we would increase the soed metric by 2 * w(e) where w(e)
        // is the weight of the hyperedge.
        if ( pin_count_in_from_part > 1 ) {
          isolated_block_gain += (pin_count_in_from_part == edge_size ? 2 : 1) * he_weight;
        }

        // Substract edge weight from all incident blocks.
        // If the we would make the hyperedge a non-cut edge, we would improve
        // the objective function by 2 * w(e) where w(e) is the weight of the hyperedge.
        // Note, in case the pin count in from part is greater than one
        // we will later add that edge weight to the gain (see internal_weight).
        for (const PartitionID& to : phg.connectivitySet(he)) {
          if (from != to) {
            tmp_scores[to] += (phg.pinCountInPart(he, to) == edge_size - 1 ? 2 : 1) * he_weight;
          }
        }
      }
    }
  }

  // ! Computes only the gain (cut increase) for moving out of the current block.
  template<typename PartitionedHypergraph>
  static Gain computeIsolatedBlockGain(const PartitionedHypergraph& phg, const HypernodeID hn) {
    Gain isolated_block_gain = 0;
    PartitionID from = phg.partID(hn);
    for (const HyperedgeID& he : phg.incidentEdges(hn)) {
      const HypernodeID edge_size = phg.edgeSize(he);
      HypernodeID pin_count_in_from_part = phg.pinCountInPart(he, from);
      if ( pin_count_in_from_part > 1 ) {
        isolated_block_gain += (pin_count_in_from_part == edge_size ? 2 : 1) * phg.edgeWeight(he);
      }
    }
    return isolated_block_gain;
  }

  HyperedgeWeight gain(const Gain to_score,
                       const Gain isolated_block_gain) {
    return isolated_block_gain - to_score;
  }

  void changeNumberOfBlocksImpl(const PartitionID) {
    // Do nothing
  }
};

}  // namespace mt_kahypar
