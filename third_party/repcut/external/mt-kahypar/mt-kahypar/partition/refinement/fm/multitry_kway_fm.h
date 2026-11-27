/*******************************************************************************
 * MIT License
 *
 * This file is part of Mt-KaHyPar.
 *
 * Copyright (C) 2020 Lars Gottesbüren <lars.gottesbueren@kit.edu>
 * Copyright (C) 2020 Tobias Heuer <tobias.heuer@kit.edu>
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

#include <tbb/enumerable_thread_specific.h>

#include "mt-kahypar/partition/context.h"

#include "mt-kahypar/partition/refinement/i_refiner.h"
#include "mt-kahypar/partition/refinement/i_rebalancer.h"
#include "mt-kahypar/partition/refinement/fm/localized_kway_fm_core.h"
#include "mt-kahypar/partition/refinement/fm/global_rollback.h"
#include "mt-kahypar/partition/refinement/fm/strategies/i_fm_strategy.h"
#include "mt-kahypar/partition/refinement/gains/gain_cache_ptr.h"

namespace mt_kahypar {

template<typename GraphAndGainTypes>
class MultiTryKWayFM final : public IRefiner {

  static constexpr bool debug = false;
  static constexpr bool enable_heavy_assert = false;

  using PartitionedHypergraph = typename GraphAndGainTypes::PartitionedHypergraph;
  using GainCache = typename GraphAndGainTypes::GainCache;
  using LocalizedFMSearch = LocalizedKWayFM<GraphAndGainTypes>;
  using Rollback = GlobalRollback<GraphAndGainTypes>;

  static_assert(GainCache::TYPE != GainPolicy::none);

 public:

  MultiTryKWayFM(const HypernodeID num_hypernodes,
                 const HyperedgeID num_hyperedges,
                 const Context& c,
                 GainCache& gainCache,
                 IRebalancer& rb);

  MultiTryKWayFM(const HypernodeID num_hypernodes,
                 const HyperedgeID num_hyperedges,
                 const Context& c,
                 gain_cache_t gainCache,
                 IRebalancer& rb) :
    MultiTryKWayFM(num_hypernodes, num_hyperedges, c,
      GainCachePtr::cast<GainCache>(gainCache), rb) { }

  void printMemoryConsumption();

 private:
  bool refineImpl(mt_kahypar_partitioned_hypergraph_t& phg,
                  const vec<HypernodeID>& refinement_nodes,
                  Metrics& metrics,
                  double time_limit) final ;

  void initializeImpl(mt_kahypar_partitioned_hypergraph_t& phg) final ;

  void roundInitialization(PartitionedHypergraph& phg,
                           const vec<HypernodeID>& refinement_nodes);

  void interleaveMoveSequenceWithRebalancingMoves(const PartitionedHypergraph& phg,
                                                  const vec<HypernodeWeight>& initialPartWeights,
                                                  const std::vector<HypernodeWeight>& max_part_weights,
                                                  vec<vec<Move>>& rebalancing_moves_by_part);

  void insertMovesToBalanceBlock(const PartitionedHypergraph& phg,
                                 const PartitionID block,
                                 const std::vector<HypernodeWeight>& max_part_weights,
                                 const vec<vec<Move>>& rebalancing_moves_by_part,
                                 MoveID& next_move_index,
                                 vec<HypernodeWeight>& current_part_weights,
                                 vec<MoveID>& current_rebalancing_move_index);

  LocalizedFMSearch constructLocalizedKWayFMSearch() {
    return LocalizedFMSearch(context, initial_num_nodes, sharedData, gain_cache);
  }

  static double improvementFraction(Gain gain, HyperedgeWeight old_km1) {
    if (old_km1 == 0)
      return 0;
    else
      return static_cast<double>(gain) / static_cast<double>(old_km1);
  }

  void resizeDataStructuresForCurrentK();

  bool enable_light_fm = false;
  const HypernodeID initial_num_nodes;
  const Context& context;
  GainCache& gain_cache;
  PartitionID current_k;
  FMSharedData sharedData;
  std::unique_ptr<IFMStrategy> fm_strategy;
  Rollback globalRollback;
  tbb::enumerable_thread_specific<LocalizedFMSearch> ets_fm;
  vec<Move> tmp_move_order;
  IRebalancer& rebalancer;
};

} // namespace mt_kahypar
