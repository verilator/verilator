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
#include "mt-kahypar/partition/refinement/fm/strategies/local_unconstrained_strategy.h"
#include "mt-kahypar/utils/utilities.h"


namespace mt_kahypar {

template<typename GraphAndGainTypes>
class UnconstrainedStrategy: public IFMStrategy {
  using Base = IFMStrategy;
  static constexpr bool debug = false;

 public:
  using LocalFM = LocalizedKWayFM<GraphAndGainTypes>;
  using PartitionedHypergraph = typename GraphAndGainTypes::PartitionedHypergraph;

  UnconstrainedStrategy(const Context& context, FMSharedData& sharedData):
      Base(context, sharedData),
      current_penalty(context.refinement.fm.imbalance_penalty_min),
      current_upper_bound(context.refinement.fm.unconstrained_upper_bound),
      absolute_improvement_first_round(kInvalidGain),
      unconstrained_is_enabled(true),
      stats(utils::Utilities::instance().getStats(context.utility_id)) {
        ASSERT(!context.refinement.fm.activate_unconstrained_dynamically
                || context.refinement.fm.multitry_rounds > 2);
  }

  bool dispatchedFindMoves(LocalFM& local_fm, PartitionedHypergraph& phg, size_t task_id, size_t num_seeds, size_t round) {
    if (isUnconstrainedRound(round)) {
      LocalUnconstrainedStrategy local_strategy = local_fm.template initializeDispatchedStrategy<LocalUnconstrainedStrategy>();
      local_strategy.setPenaltyFactor(current_penalty);
      local_strategy.setUpperBound(current_upper_bound);
      return local_fm.findMoves(local_strategy, phg, task_id, num_seeds);
    } else {
      LocalGainCacheStrategy local_strategy = local_fm.template initializeDispatchedStrategy<LocalGainCacheStrategy>();
      return local_fm.findMoves(local_strategy, phg, task_id, num_seeds);
    }
  }

 private:
  virtual void findMovesImpl(localized_k_way_fm_t local_fm, mt_kahypar_partitioned_hypergraph_t& phg,
                             size_t num_tasks, size_t num_seeds, size_t round) final {
    initRound(round);

    findMovesWithConcreteStrategy(*this, sharedData, local_fm, phg, num_tasks, num_seeds, round);
  }

  virtual bool isUnconstrainedRoundImpl(size_t round) const final {
    if (round > 0 && !unconstrained_is_enabled) {
      return false;
    }
    if (context.refinement.fm.activate_unconstrained_dynamically) {
      return round == 1 || (round > 1 && round - 2 < context.refinement.fm.unconstrained_rounds);
    } else {
      return round < context.refinement.fm.unconstrained_rounds;
    }
  }

  virtual void reportImprovementImpl(size_t round, Gain absolute_improvement, double relative_improvement) final {
    if (round == 0) {
      absolute_improvement_first_round = absolute_improvement;
    } else if (round == 1
               && context.refinement.fm.activate_unconstrained_dynamically
               && absolute_improvement < absolute_improvement_first_round) {
        // this is the decision point whether unconstrained or constrained FM is used
        unconstrained_is_enabled = false;
        DBG << "Disabling unconstrained FM after test round: " << V(absolute_improvement) << V(absolute_improvement_first_round);
    } else if (relative_improvement < context.refinement.fm.unconstrained_min_improvement) {
      unconstrained_is_enabled = false;
      DBG << "Disabling unconstrained FM due to too little improvement:" << V(relative_improvement);
    }
    if (round == 1) {
      stats.update_stat("top-level-ufm-active", unconstrained_is_enabled);
      if (unconstrained_is_enabled) {
        stats.update_stat("ufm-active-levels", 1);
      } else {
        stats.update_stat("ufm-inactive-levels", 1);
      }
    }
  }

  void initRound(size_t round) {
    if (round == 0) {
      unconstrained_is_enabled = true;
    }
    if (context.refinement.fm.activate_unconstrained_dynamically) {
      if (round == 1) {
        current_penalty = context.refinement.fm.penalty_for_activation_test;
        current_upper_bound = context.refinement.fm.unconstrained_upper_bound;
      } else if (round > 1 && isUnconstrainedRound(round)) {
        size_t n_rounds = std::min(context.refinement.fm.unconstrained_rounds, context.refinement.fm.multitry_rounds - 2);
        calculateInterpolation(round - 2, n_rounds);
      }
    } else if (isUnconstrainedRound(round)) {
      calculateInterpolation(round, context.refinement.fm.unconstrained_rounds);
    }
  }

  void calculateInterpolation(size_t round, size_t n_rounds) {
    ASSERT(unconstrained_is_enabled && round < context.refinement.fm.multitry_rounds);
    auto interpolate = [&](double start, double end) {
      if (round == 0) {
        return start;
      }
      double summed = (n_rounds - round - 1) * start + round * end;
      return summed / static_cast<double>(n_rounds - 1);
    };

    if (round < n_rounds) {
      // interpolate values for current penalty and upper bound
      current_penalty = interpolate(context.refinement.fm.imbalance_penalty_min,
                                    context.refinement.fm.imbalance_penalty_max);
      if (context.refinement.fm.unconstrained_upper_bound >= 1) {
        if (context.refinement.fm.unconstrained_upper_bound_min >= 1) {
          current_upper_bound = interpolate(context.refinement.fm.unconstrained_upper_bound,
                                            context.refinement.fm.unconstrained_upper_bound_min);
        } else {
          current_upper_bound = context.refinement.fm.unconstrained_upper_bound;
        }
      }
    }
  }

  double current_penalty;
  double current_upper_bound;
  Gain absolute_improvement_first_round;
  bool unconstrained_is_enabled;
  utils::Stats& stats;
};

}
