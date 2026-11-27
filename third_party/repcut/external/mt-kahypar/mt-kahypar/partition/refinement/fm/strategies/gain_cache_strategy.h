/*******************************************************************************
 * MIT License
 *
 * This file is part of Mt-KaHyPar.
 *
 * Copyright (C) 2023 Nikolai Maas <nikolai.maas@kit.edu>
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

#include "mt-kahypar/partition/refinement/fm/fm_commons.h"
#include "mt-kahypar/partition/refinement/fm/localized_kway_fm_core.h"
#include "mt-kahypar/partition/refinement/fm/strategies/i_fm_strategy.h"
#include "mt-kahypar/partition/refinement/fm/strategies/local_gain_cache_strategy.h"


namespace mt_kahypar {

template<typename GraphAndGainTypes>
class GainCacheStrategy: public IFMStrategy {
  using Base = IFMStrategy;

 public:
  using LocalFM = LocalizedKWayFM<GraphAndGainTypes>;
  using PartitionedHypergraph = typename GraphAndGainTypes::PartitionedHypergraph;

  GainCacheStrategy(const Context& context, FMSharedData& sharedData):
      Base(context, sharedData) { }

  bool dispatchedFindMoves(LocalFM& local_fm, PartitionedHypergraph& phg, size_t task_id, size_t num_seeds, size_t) {
    LocalGainCacheStrategy local_strategy = local_fm.template initializeDispatchedStrategy<LocalGainCacheStrategy>();
    return local_fm.findMoves(local_strategy, phg, task_id, num_seeds);
  }

 private:
  virtual void findMovesImpl(localized_k_way_fm_t local_fm, mt_kahypar_partitioned_hypergraph_t& phg,
                             size_t num_tasks, size_t num_seeds, size_t round) final {
    findMovesWithConcreteStrategy(*this, sharedData, local_fm, phg, num_tasks, num_seeds, round);
  }

  virtual bool isUnconstrainedRoundImpl(size_t) const final {
    return false;
  }
};

}
