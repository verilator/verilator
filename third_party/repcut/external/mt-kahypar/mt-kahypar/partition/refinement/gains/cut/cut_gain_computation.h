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
#include "mt-kahypar/partition/refinement/gains/cut/cut_attributed_gains.h"
#include "mt-kahypar/datastructures/sparse_map.h"
#include "mt-kahypar/parallel/stl/scalable_vector.h"

namespace mt_kahypar {

class CutGainComputation : public GainComputationBase<CutGainComputation, CutAttributedGains> {
  using Base = GainComputationBase<CutGainComputation, CutAttributedGains>;

  static constexpr bool enable_heavy_assert = false;

 public:
  using RatingMap = typename Base::RatingMap;

  static constexpr bool is_independent_of_block = true;

  CutGainComputation(const Context& context,
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
      PartitionID connectivity = phg.connectivity(he);
      HypernodeID pin_count_in_from_part = phg.pinCountInPart(he, from);
      HyperedgeWeight weight = phg.edgeWeight(he);
      if (connectivity == 1 && phg.edgeSize(he) > 1) {
        // In case, the hyperedge is a non-cut hyperedge, we would increase
        // the cut, if we move vertex hn to an other block.
        isolated_block_gain += weight;
      } else if (connectivity == 2 && pin_count_in_from_part == 1) {
        for (const PartitionID& to : phg.connectivitySet(he)) {
          // In case there are only two blocks contained in the current
          // hyperedge and only one pin left in the from part of the hyperedge,
          // we would make the current hyperedge a non-cut hyperedge when moving
          // vertex hn to the other block.
          if (from != to) {
            tmp_scores[to] += weight;
          }
        }
      }
    }
  }

  // ! Computes only the gain (cut increase) for moving out of the current block.
  template<typename PartitionedHypergraph>
  static Gain computeIsolatedBlockGain(const PartitionedHypergraph& phg, const HypernodeID hn) {
    Gain isolated_block_gain = 0;
    for (const HyperedgeID& he : phg.incidentEdges(hn)) {
      PartitionID connectivity = phg.connectivity(he);
      if (connectivity == 1 && phg.edgeSize(he) > 1) {
        // In case, the hyperedge is a non-cut hyperedge, we would increase
        // the cut, if we move vertex hn to an other block.
        isolated_block_gain += phg.edgeWeight(he);
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
