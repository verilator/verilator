/*******************************************************************************
 * MIT License
 *
 * This file is part of Mt-KaHyPar.
 *
 * Copyright (C) 2021 Tobias Heuer <tobias.heuer@kit.edu>
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

#include <atomic>

#include "mt-kahypar/partition/context.h"
#include "mt-kahypar/partition/refinement/i_refiner.h"
#include "mt-kahypar/partition/refinement/flows/active_block_scheduler.h"
#include "mt-kahypar/partition/refinement/flows/i_flow_refiner.h"
#include "mt-kahypar/partition/refinement/flows/quotient_graph.h"
#include "mt-kahypar/partition/refinement/flows/problem_construction.h"
#include "mt-kahypar/partition/refinement/gains/gain_cache_ptr.h"
#include "mt-kahypar/parallel/atomic_wrapper.h"
#include "mt-kahypar/utils/utilities.h"

namespace mt_kahypar {

struct RefinementStats {
  RefinementStats(utils::Stats& stats);

  void reset();

  void update_global_stats();

  utils::Stats& _stats;
  CAtomic<int64_t> num_refinements;
  CAtomic<int64_t> num_improvements;
  CAtomic<int64_t> num_time_limits;
  CAtomic<int64_t> correct_expected_improvement;
  CAtomic<int64_t> zero_gain_improvement;
  CAtomic<int64_t> failed_updates_due_to_conflicting_moves;
  CAtomic<int64_t> failed_updates_due_to_conflicting_moves_without_rollback;
  CAtomic<int64_t> failed_updates_due_to_balance_constraint;
  CAtomic<HyperedgeWeight> total_improvement;
};

std::ostream & operator<< (std::ostream& str, const RefinementStats& stats);


struct PartWeightUpdateResult {
  bool is_balanced = true;
  PartitionID overloaded_block = kInvalidPartition;
  HypernodeWeight overload_weight = 0;
};


template<typename GraphAndGainTypes>
class FlowRefinementScheduler final : public IRefiner {

  static constexpr bool debug = false;
  static constexpr bool enable_heavy_assert = false;

  using TypeTraits = typename GraphAndGainTypes::TypeTraits;
  using PartitionedHypergraph = typename GraphAndGainTypes::PartitionedHypergraph;
  using GainCache = typename GraphAndGainTypes::GainCache;
  using AttributedGains = typename GraphAndGainTypes::AttributedGains;

public:
  FlowRefinementScheduler(const HypernodeID num_hypernodes,
                          const HyperedgeID num_hyperedges,
                          const Context& context,
                          GainCache& gain_cache);

  FlowRefinementScheduler(const HypernodeID num_hypernodes,
                          const HyperedgeID num_hyperedges,
                          const Context& context,
                          gain_cache_t gain_cache);

  FlowRefinementScheduler(const FlowRefinementScheduler&) = delete;
  FlowRefinementScheduler(FlowRefinementScheduler&&) = delete;

  FlowRefinementScheduler & operator= (const FlowRefinementScheduler &) = delete;
  FlowRefinementScheduler & operator= (FlowRefinementScheduler &&) = delete;

  /**
   * Applies the sequence of vertex moves to the partitioned hypergraph.
   * The method ensures that the move sequence does not violate
   * the balance constaint and not worsen solution quality.
   * Returns, improvement in solution quality.
   */
  HyperedgeWeight applyMoves(const uint32_t search_id, MoveSequence& sequence);

  // ! Only for testing
  const vec<HypernodeWeight>& partWeights() const;

private:
  bool refineImpl(mt_kahypar_partitioned_hypergraph_t& phg,
                  const vec<HypernodeID>& refinement_nodes,
                  Metrics& metrics,
                  double time_limit) final;

  void initializeImpl(mt_kahypar_partitioned_hypergraph_t& phg) final;

  void resizeDataStructuresForCurrentK();

  std::unique_ptr<IFlowRefiner> constructFlowRefiner();

  template<typename F>
  HyperedgeWeight runFlowSearch(PartitionedHypergraph& phg,
                                utils::Timer& timer,
                                size_t refiner_idx,
                                const Subhypergraph& sub_hg,
                                uint32_t search_id,
                                double time_limit,
                                F report_running_time);

  PartWeightUpdateResult partWeightUpdate(const vec<HypernodeWeight>& part_weight_deltas,
                                          const bool rollback);

  PartitionedHypergraph* _phg;
  const Context& _context;
  GainCache& _gain_cache;
  PartitionID _current_k;
  HyperedgeID _num_hyperedges;

  // ! Contains information of all cut hyperedges between the
  // ! blocks of the partition
  QuotientGraph _quotient_graph;

  // ! Block scheduling logic
  ActiveBlockScheduler _active_block_scheduler;

  // ! Available flow refiners
  vec<std::unique_ptr<IFlowRefiner>> _refiner;

  // ! Responsible for construction of an flow problems
  ProblemConstruction<TypeTraits> _constructor;

  // ! For each vertex it store wheather the corresponding vertex
  // ! was moved or not
  vec<uint8_t> _was_moved;

  // ! Maintains the part weights of each block
  SpinLock _part_weights_lock;
  vec<HypernodeWeight> _part_weights;
  vec<HypernodeWeight> _max_part_weights;

  // ! Contains refinement statistics
  RefinementStats _stats;

  SpinLock _apply_moves_lock;
};

}  // namespace kahypar
