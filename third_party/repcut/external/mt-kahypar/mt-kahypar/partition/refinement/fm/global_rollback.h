/*******************************************************************************
 * MIT License
 *
 * This file is part of Mt-KaHyPar.
 *
 * Copyright (C) 2020 Lars Gottesbüren <lars.gottesbueren@kit.edu>
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

#include <tbb/parallel_invoke.h>

#include "mt-kahypar/partition/refinement/fm/fm_commons.h"


namespace mt_kahypar {

template<typename GraphAndGainTypes>
class GlobalRollback {
  static constexpr bool enable_heavy_assert = false;

  using PartitionedHypergraph = typename GraphAndGainTypes::PartitionedHypergraph;
  using GainCache = typename GraphAndGainTypes::GainCache;
  using AttributedGains = typename GraphAndGainTypes::AttributedGains;
  using Rollback = typename GraphAndGainTypes::Rollback;
  using RecalculationData = typename Rollback::RecalculationData;

public:
  explicit GlobalRollback(const HyperedgeID num_hyperedges,
                          const Context& context,
                          GainCache& gainCache) :
    context(context),
    gain_cache(gainCache),
    max_part_weight_scaling(context.refinement.fm.rollback_balance_violation_factor),
    ets_recalc_data([&] { return vec<RecalculationData>(context.partition.k); }),
    last_recalc_round(),
    round(1) {
    if (context.refinement.fm.iter_moves_on_recalc && context.refinement.fm.rollback_parallel) {
      last_recalc_round.resize(num_hyperedges, CAtomic<uint32_t>(0));
    }
  }

  HyperedgeWeight revertToBestPrefix(PartitionedHypergraph& phg,
                                     FMSharedData& sharedData,
                                     const vec<HypernodeWeight>& partWeights,
                                     const std::vector<HypernodeWeight>& maxPartWeights) {
    if (context.refinement.fm.rollback_parallel) {
      return revertToBestPrefixParallel(phg, sharedData, partWeights, maxPartWeights);
    } else {
      return revertToBestPrefixSequential(phg, sharedData, partWeights, maxPartWeights);
    }
  }

  HyperedgeWeight revertToBestPrefixParallel(PartitionedHypergraph& phg,
                                             FMSharedData& sharedData,
                                             const vec<HypernodeWeight>& partWeights,
                                             const std::vector<HypernodeWeight>& maxPartWeights);

  void recalculateGainForHyperedge(PartitionedHypergraph& phg,
                                   FMSharedData& sharedData,
                                   const HyperedgeID& he);
  void recalculateGainForHyperedgeViaAttributedGains(PartitionedHypergraph& phg,
                                                     FMSharedData& sharedData,
                                                     const HyperedgeID& he);
  void recalculateGainForGraphEdgeViaAttributedGains(PartitionedHypergraph& phg,
                                                     FMSharedData& sharedData,
                                                     const HyperedgeID& he);
  void recalculateGains(PartitionedHypergraph& phg, FMSharedData& sharedData);

  HyperedgeWeight revertToBestPrefixSequential(PartitionedHypergraph& phg,
                                               FMSharedData& sharedData,
                                               const vec<HypernodeWeight>&,
                                               const std::vector<HypernodeWeight>& maxPartWeights);

  MT_KAHYPAR_ATTRIBUTE_ALWAYS_INLINE
  void moveVertex(PartitionedHypergraph& phg, HypernodeID u, PartitionID from, PartitionID to) {
    phg.changeNodePart(gain_cache, u, from, to);
  }

  void changeNumberOfBlocks(const PartitionID new_k) {
    for ( auto& recalc_data : ets_recalc_data ) {
      if ( static_cast<size_t>(new_k) > recalc_data.size() ) {
        recalc_data.resize(new_k);
      }
    }
  }

  bool verifyGains(PartitionedHypergraph& phg, FMSharedData& sharedData);

private:
  const Context& context;

  GainCache& gain_cache;

  // ! Factor to multiply max part weight with, in order to relax or disable the balance criterion. Set to zero for disabling
  double max_part_weight_scaling;

  tbb::enumerable_thread_specific< vec<RecalculationData> > ets_recalc_data;
  vec<CAtomic<uint32_t>> last_recalc_round;
  uint32_t round;
};

}