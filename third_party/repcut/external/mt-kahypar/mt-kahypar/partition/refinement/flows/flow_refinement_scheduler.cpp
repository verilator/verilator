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

#include "mt-kahypar/partition/refinement/flows/flow_refinement_scheduler.h"

#include <chrono>

#include "mt-kahypar/definitions.h"
#include "mt-kahypar/partition/metrics.h"
#include "mt-kahypar/partition/refinement/flows/flow_refiner.h"
#include "mt-kahypar/partition/refinement/gains/gain_definitions.h"
#include "mt-kahypar/io/partitioning_output.h"
#include "mt-kahypar/utils/utilities.h"
#include "mt-kahypar/utils/cast.h"

namespace mt_kahypar {

class TimeLimitTracker {
 public:
  TimeLimitTracker():
    lock(),
    num_refinements(0),
    average_running_time(0.0) { }

  double timeLimit(const Context& context) const {
    return shouldSetTimeLimit(context) ?
      std::max(context.refinement.flows.time_limit_factor *
        average_running_time, 0.1) : std::numeric_limits<double>::max();
  }

  bool shouldSetTimeLimit(const Context& context) const {
    return num_refinements > static_cast<size_t>(context.partition.k) &&
      context.refinement.flows.time_limit_factor > 1.0;
  }

  void reportRunningTime(double running_time, bool reaches_time_limit) {
    if ( !reaches_time_limit ) {
      lock.lock();
      average_running_time = (running_time + num_refinements *
        average_running_time) / static_cast<double>(num_refinements + 1);
      ++num_refinements;
      lock.unlock();
    }
  }

 private:
  SpinLock lock;
  size_t num_refinements;
  double average_running_time;
};


namespace {

  static constexpr size_t PROGRESS_BAR_SIZE = 50;

  template<typename F>
  std::string progress_bar(const size_t value, const size_t max, const F& f) {
    const double percentage = static_cast<double>(value) / std::max(max,UL(1));
    const size_t ticks = PROGRESS_BAR_SIZE * percentage;
    std::stringstream pbar_str;
    pbar_str << "|"
             << f(percentage) << std::string(ticks, '|') << END
             << std::string(PROGRESS_BAR_SIZE - ticks, ' ')
             << "| " << std::setprecision(2) << (100.0 * percentage) << "% (" << value << ")";
    return pbar_str.str();
  }
}

RefinementStats::RefinementStats(utils::Stats& stats) :
  _stats(stats),
  num_refinements(0),
  num_improvements(0),
  num_time_limits(0),
  correct_expected_improvement(0),
  zero_gain_improvement(0),
  failed_updates_due_to_conflicting_moves(0),
  failed_updates_due_to_conflicting_moves_without_rollback(0),
  failed_updates_due_to_balance_constraint(0),
  total_improvement(0) { }

void RefinementStats::reset() {
  num_refinements.store(0);
  num_improvements.store(0);
  num_time_limits.store(0);
  correct_expected_improvement.store(0);
  zero_gain_improvement.store(0);
  failed_updates_due_to_conflicting_moves.store(0);
  failed_updates_due_to_conflicting_moves_without_rollback.store(0);
  failed_updates_due_to_balance_constraint.store(0);
  total_improvement.store(0);
}

void RefinementStats::update_global_stats() {
  _stats.update_stat("num_flow_refinements",
    num_refinements.load(std::memory_order_relaxed));
  _stats.update_stat("num_flow_improvement",
    num_improvements.load(std::memory_order_relaxed));
  _stats.update_stat("num_time_limits",
    num_time_limits.load(std::memory_order_relaxed));
  _stats.update_stat("correct_expected_improvement",
    correct_expected_improvement.load(std::memory_order_relaxed));
  _stats.update_stat("zero_gain_improvement",
    zero_gain_improvement.load(std::memory_order_relaxed));
  _stats.update_stat("failed_updates_due_to_conflicting_moves",
    failed_updates_due_to_conflicting_moves.load(std::memory_order_relaxed));
  _stats.update_stat("failed_updates_due_to_conflicting_moves_without_rollback",
    failed_updates_due_to_conflicting_moves_without_rollback.load(std::memory_order_relaxed));
  _stats.update_stat("failed_updates_due_to_balance_constraint",
    failed_updates_due_to_balance_constraint.load(std::memory_order_relaxed));
  _stats.update_stat("total_flow_refinement_improvement",
    total_improvement.load(std::memory_order_relaxed));
}

std::ostream & operator<< (std::ostream& str, const RefinementStats& stats) {
  str << "\n";
  str << "Total Improvement                   = " << stats.total_improvement << "\n";
  str << "Number of Flow-Based Refinements    = " << stats.num_refinements << "\n";
  str << "+ No Improvements                   = "
      << progress_bar(stats.num_refinements - stats.num_improvements, stats.num_refinements,
          [&](const double percentage) { return percentage > 0.9 ? RED : percentage > 0.75 ? YELLOW : GREEN; }) << "\n";
  str << "+ Number of Improvements            = "
      << progress_bar(stats.num_improvements, stats.num_refinements,
          [&](const double percentage) { return percentage < 0.05 ? RED : percentage < 0.15 ? YELLOW : GREEN; }) << "\n";
  str << "  + Correct Expected Improvements   = "
      << progress_bar(stats.correct_expected_improvement, stats.num_improvements,
          [&](const double percentage) { return percentage > 0.9 ? GREEN : percentage > 0.75 ? YELLOW : RED; }) << "\n";
  str << "  + Incorrect Expected Improvements = "
      << progress_bar(stats.num_improvements - stats.correct_expected_improvement, stats.num_improvements,
          [&](const double percentage) { return percentage < 0.1 ? GREEN : percentage < 0.25 ? YELLOW : RED; }) << "\n";
  str << "  + Zero-Gain Improvements          = "
      << progress_bar(stats.zero_gain_improvement, stats.num_improvements,
          [&](const double) { return WHITE; }) << "\n";
  str << "+ Failed due to Balance Constraint  = "
      << progress_bar(stats.failed_updates_due_to_balance_constraint, stats.num_refinements,
          [&](const double percentage) { return percentage < 0.01 ? GREEN : percentage < 0.05 ? YELLOW : RED; }) << "\n";
  str << "+ Failed due to Conflicting Moves   = "
      << progress_bar(stats.failed_updates_due_to_conflicting_moves, stats.num_refinements,
          [&](const double percentage) { return percentage < 0.01 ? GREEN : percentage < 0.05 ? YELLOW : RED; }) << "\n";
  str << "+ Time Limits                       = "
      << progress_bar(stats.num_time_limits, stats.num_refinements,
          [&](const double percentage) { return percentage < 0.0025 ? GREEN : percentage < 0.01 ? YELLOW : RED; }) << "\n";
  str << "---------------------------------------------------------------";
  return str;
}

std::string blocksToString(const BlockPair& blocks) {
  return "(" + std::to_string(blocks.i) + "," + std::to_string(blocks.j) + ")";
}

template<typename GraphAndGainTypes>
FlowRefinementScheduler<GraphAndGainTypes>::FlowRefinementScheduler(const HypernodeID num_hypernodes,
                                                                    const HyperedgeID num_hyperedges,
                                                                    const Context& context,
                                                                    GainCache& gain_cache) :
  _phg(nullptr),
  _context(context),
  _gain_cache(gain_cache),
  _current_k(context.partition.k),
  _num_hyperedges(num_hyperedges),
  _quotient_graph(num_hyperedges, context),
  _active_block_scheduler(context, _quotient_graph),
  _refiner(),
  _constructor(num_hypernodes, num_hyperedges, context),
  _was_moved(num_hypernodes, uint8_t(false)),
  _part_weights_lock(),
  _part_weights(context.partition.k, 0),
  _max_part_weights(context.partition.k, 0),
  _stats(utils::Utilities::instance().getStats(context.utility_id)),
  _apply_moves_lock() {
    ASSERT(_context.refinement.flows.num_parallel_searches > 0);
    for ( size_t i = 0; i < _context.refinement.flows.num_parallel_searches; ++i ) {
      _refiner.emplace_back(nullptr);
    }
  }

template<typename GraphAndGainTypes>
FlowRefinementScheduler<GraphAndGainTypes>::FlowRefinementScheduler(const HypernodeID num_hypernodes,
                                                                    const HyperedgeID num_hyperedges,
                                                                    const Context& context,
                                                                    gain_cache_t gain_cache) :
  FlowRefinementScheduler(num_hypernodes, num_hyperedges, context,
    GainCachePtr::cast<GainCache>(gain_cache)) { }

template<typename GraphAndGainTypes>
template<typename F>
HyperedgeWeight FlowRefinementScheduler<GraphAndGainTypes>::runFlowSearch(PartitionedHypergraph& phg,
                                                                          utils::Timer& timer,
                                                                          size_t refiner_idx,
                                                                          const Subhypergraph& sub_hg,
                                                                          uint32_t search_id,
                                                                          double time_limit,
                                                                          F report_running_time) {
  HyperedgeWeight delta = 0;
  bool reaches_time_limit = false;

  auto start = std::chrono::high_resolution_clock::now();
  if ( sub_hg.numNodes() > 0 ) {
    auto partitioned_hg = utils::partitioned_hg_const_cast(phg);

    if (_refiner[refiner_idx] == nullptr) {
      _refiner[refiner_idx] = constructFlowRefiner();
    }
    _refiner[refiner_idx]->initialize(partitioned_hg);
    _refiner[refiner_idx]->updateTimeLimit(time_limit);
    MoveSequence sequence = _refiner[refiner_idx]->refine(partitioned_hg, sub_hg, start);

    // apply moves and update stats
    if ( !sequence.moves.empty() ) {
      timer.start_timer("apply_moves", "Apply Moves", true);
      delta = applyMoves(search_id, sequence);
      timer.stop_timer("apply_moves");
    } else if ( sequence.state == MoveSequenceState::TIME_LIMIT ) {
      reaches_time_limit = true;
      ++_stats.num_time_limits;
      DBG << RED << "Search" << search_id << "reaches the time limit" << END;
    }
    ++_stats.num_refinements;
  }
  double time = std::chrono::duration<double>(std::chrono::high_resolution_clock::now() - start).count();

  report_running_time(time, reaches_time_limit);
  return delta;
}

template<typename GraphAndGainTypes>
bool FlowRefinementScheduler<GraphAndGainTypes>::refineImpl(mt_kahypar_partitioned_hypergraph_t& hypergraph,
                                                            const parallel::scalable_vector<HypernodeID>&,
                                                            Metrics& best_metrics,
                                                            const double)  {
  PartitionedHypergraph& phg = utils::cast<PartitionedHypergraph>(hypergraph);
  ASSERT(_phg == &phg);
  _active_block_scheduler.setObjective(best_metrics.quality);

  TimeLimitTracker tracker;
  std::atomic<HyperedgeWeight> overall_delta(0);
  std::atomic_uint32_t search_id_counter(0);

  utils::Timer& timer = utils::Utilities::instance().getTimer(_context.utility_id);
  tbb::parallel_for(UL(0), _context.refinement.flows.num_parallel_searches, [&](const size_t refiner_idx) {
    while ( refiner_idx < _active_block_scheduler.numRemainingBlocks() ) {
      // fetch next block pair from active block scheduler
      BlockPair blocks;
      size_t round = 0;
      bool success = _active_block_scheduler.popBlockPairFromQueue(blocks, round);

      if (success) {
        success = _quotient_graph.edge(blocks).acquire();
        if (success) {
          uint32_t search_id = search_id_counter.fetch_add(1, std::memory_order_relaxed);

          DBG << "Start search" << search_id
              << "( Blocks =" << blocksToString(blocks)
              << ", Refiner =" << refiner_idx << ")";

          timer.start_timer("region_growing", "Grow Region", true);
          const Subhypergraph sub_hg = _constructor.construct(blocks, _quotient_graph, phg, /*deterministic=*/false);
          timer.stop_timer("region_growing");

          _quotient_graph.edge(blocks).release();

          // run the actual flow computation
          HyperedgeWeight delta = runFlowSearch(phg, timer, refiner_idx, sub_hg, search_id, tracker.timeLimit(_context),
            [&](double time, bool reaches_time_limit) {
              tracker.reportRunningTime(time, reaches_time_limit);
            });
          _quotient_graph.edge(blocks).reportImprovement(delta);
          overall_delta.fetch_sub(delta, std::memory_order_relaxed);

          DBG << "End search" << search_id
              << "( Blocks =" << blocksToString(blocks)
              << ", Refiner =" << refiner_idx
              << ", Running Time =" << time << ")";

          // in case the block pair becomes active, we reinsert it into the queue
          _active_block_scheduler.finalizeSearch(blocks, round, std::max(delta, 0));

          // set time limit if required
          if ( tracker.shouldSetTimeLimit(_context) ) {
            double time_limit = tracker.timeLimit(_context);
            for ( size_t idx = 0; idx < _refiner.size(); ++idx ) {
              if (_refiner[idx] != nullptr) {
                _refiner[idx]->updateTimeLimit(time_limit);
              }
            }
          }
        } else {
          _active_block_scheduler.finalizeSearch(blocks, round, 0);
        }
      }

      if (!success) {
        // terminate thread since there is nothing more to do for it
        break;
      }
    }
    DBG << RED << "Refiner" << refiner_idx << "terminates!" << END;
  });

  DBG << _stats;

  ASSERT([&]() {
    for ( PartitionID i = 0; i < _context.partition.k; ++i ) {
      if ( _part_weights[i] != phg.partWeight(i) ) {
        LOG << V(_part_weights[i]) << V(phg.partWeight(i));
        return false;
      }
    }
    return true;
  }(), "Concurrent part weight updates failed!");

  // Update metrics statistics
  HEAVY_REFINEMENT_ASSERT(best_metrics.quality + overall_delta == metrics::quality(phg, _context),
    V(best_metrics.quality) << V(overall_delta) << V(metrics::quality(phg, _context)));
  best_metrics.quality += overall_delta;
  best_metrics.imbalance = metrics::imbalance(phg, _context);
  _stats.update_global_stats();

  // Update Gain Cache
  if ( _context.forceGainCacheUpdates() && _gain_cache.isInitialized() ) {
    phg.doParallelForAllNodes([&](const HypernodeID& hn) {
      if ( _was_moved[hn] ) {
        _gain_cache.recomputeInvalidTerms(phg, hn);
        _was_moved[hn] = uint8_t(false);
      }
    });
  }

  HEAVY_REFINEMENT_ASSERT(phg.checkTrackedPartitionInformation(_gain_cache));
  _phg = nullptr;
  return overall_delta.load(std::memory_order_relaxed) < 0;
}

template<typename GraphAndGainTypes>
void FlowRefinementScheduler<GraphAndGainTypes>::initializeImpl(mt_kahypar_partitioned_hypergraph_t& hypergraph)  {
  PartitionedHypergraph& phg = utils::cast<PartitionedHypergraph>(hypergraph);
  _phg = &phg;
  resizeDataStructuresForCurrentK();

  // Initialize Part Weights
  for ( PartitionID i = 0; i < _context.partition.k; ++i ) {
    _part_weights[i] = phg.partWeight(i);
    _max_part_weights[i] = std::max(
      phg.partWeight(i), _context.partition.max_part_weights[i]);
  }

  // Initialize Quotient Graph and Scheduler
  _stats.reset();
  utils::Timer& timer = utils::Utilities::instance().getTimer(_context.utility_id);
  timer.start_timer("initialize_quotient_graph", "Initialize Quotient Graph");
  _quotient_graph.initialize(phg);
  _active_block_scheduler.initialize(_quotient_graph.isInputHypergraph());
  timer.stop_timer("initialize_quotient_graph");

  const size_t max_parallism = _context.refinement.flows.num_parallel_searches;
  DBG << "Initial Active Block Pairs =" << _active_block_scheduler.numRemainingBlocks()
      << ", Initial Num Threads =" << max_parallism;
}

template<typename GraphAndGainTypes>
void FlowRefinementScheduler<GraphAndGainTypes>::resizeDataStructuresForCurrentK() {
  if ( _current_k != _context.partition.k ) {
    _current_k = _context.partition.k;
    // Note that in general changing the number of blocks should not resize
    // any data structure as we initialize the scheduler with the final
    // number of blocks. This is just a fallback if someone changes this in the future.
    if ( static_cast<size_t>(_current_k) > _part_weights.size() ) {
      _part_weights.resize(_current_k);
      _max_part_weights.resize(_current_k);
    }
    _quotient_graph.changeNumberOfBlocks(_current_k);
    _constructor.changeNumberOfBlocks(_current_k);
  }
}

template<typename GraphAndGainTypes>
std::unique_ptr<IFlowRefiner> FlowRefinementScheduler<GraphAndGainTypes>::constructFlowRefiner() {
  return std::make_unique<FlowRefiner<GraphAndGainTypes>>(
    _num_hyperedges, _context, false /*deterministic*/);
}

namespace {

template<typename PartitionedHypergraph, typename GainCache, typename F>
bool changeNodePart(PartitionedHypergraph& phg,
                    GainCache& gain_cache,
                    const HypernodeID hn,
                    const PartitionID from,
                    const PartitionID to,
                    const F& objective_delta,
                    const bool gain_cache_update) {
  bool success = false;
  if ( gain_cache_update && gain_cache.isInitialized()) {
    success = phg.changeNodePart(gain_cache, hn, from, to,
      std::numeric_limits<HypernodeWeight>::max(), []{}, objective_delta);
  } else {
    success = phg.changeNodePart(hn, from, to,
      std::numeric_limits<HypernodeWeight>::max(), []{}, objective_delta);
  }
  ASSERT(success);
  return success;
}

template<typename PartitionedHypergraph, typename GainCache, typename F>
void applyMoveSequence(PartitionedHypergraph& phg,
                       GainCache& gain_cache,
                       const MoveSequence& sequence,
                       const F& objective_delta,
                       const bool gain_cache_update,
                       vec<uint8_t>& was_moved,
                       vec<std::pair<HyperedgeID, PartitionID>>& new_cut_hes) {
  for ( const Move& move : sequence.moves ) {
    ASSERT(move.from == phg.partID(move.node));
    if ( move.from != move.to ) {
      changeNodePart(phg, gain_cache, move.node, move.from,
        move.to, objective_delta, gain_cache_update);
      was_moved[move.node] = uint8_t(true);
      // If move increases the pin count of some hyperedges in block 'move.to' to one 1
      // we set the corresponding block here.
      int i = new_cut_hes.size() - 1;
      while ( i >= 0 && new_cut_hes[i].second == kInvalidPartition ) {
        new_cut_hes[i].second = move.to;
        --i;
      }
    }
  }
}

template<typename PartitionedHypergraph, typename GainCache, typename F>
void revertMoveSequence(PartitionedHypergraph& phg,
                        GainCache& gain_cache,
                        const MoveSequence& sequence,
                        const F& objective_delta,
                        const bool gain_cache_update) {
  for ( const Move& move : sequence.moves ) {
    if ( move.from != move.to ) {
      ASSERT(phg.partID(move.node) == move.to);
      changeNodePart(phg, gain_cache, move.node, move.to,
        move.from, objective_delta, gain_cache_update);
    }
  }
}

} // namespace

template<typename GraphAndGainTypes>
HyperedgeWeight FlowRefinementScheduler<GraphAndGainTypes>::applyMoves(const uint32_t search_id,
                                                                       MoveSequence& sequence) {
  unused(search_id);
  ASSERT(_phg);

  // TODO: currently we lock the applyMoves method
  // => find something smarter here
  _apply_moves_lock.lock();

  // Compute Part Weight Deltas
  vec<HypernodeWeight> part_weight_deltas(_context.partition.k, 0);
  for ( Move& move : sequence.moves ) {
    move.from = _phg->partID(move.node);
    if ( move.from != move.to ) {
      const HypernodeWeight node_weight = _phg->nodeWeight(move.node);
      part_weight_deltas[move.from] -= node_weight;
      part_weight_deltas[move.to] += node_weight;
    }
  }

  HyperedgeWeight improvement = 0;
  vec<std::pair<HyperedgeID, PartitionID>> new_cut_hes;
  auto delta_func = [&](const SynchronizedEdgeUpdate& sync_update) {
    improvement -= AttributedGains::gain(sync_update);

    // Collect hyperedges with new blocks in its connectivity set
    if ( sync_update.pin_count_in_to_part_after == 1 ) {
      // the corresponding block will be set in applyMoveSequence(...) function
      new_cut_hes.emplace_back(sync_update.he, kInvalidPartition);
    }
  };

  // Update part weights atomically
  PartWeightUpdateResult update_res = partWeightUpdate(part_weight_deltas, false);
  if ( update_res.is_balanced ) {
    // Apply move sequence to partition
    applyMoveSequence(*_phg, _gain_cache, sequence, delta_func,
      _context.forceGainCacheUpdates(), _was_moved, new_cut_hes);

    if ( improvement < 0 ) {
      update_res = partWeightUpdate(part_weight_deltas, true);
      if ( update_res.is_balanced ) {
        // Move sequence worsen solution quality => Rollback
        DBG << RED << "Move sequence worsen solution quality ("
            << "Expected Improvement =" << sequence.expected_improvement
            << ", Real Improvement =" << improvement
            << ", Search ID =" << search_id << ")" << END;
        revertMoveSequence(*_phg, _gain_cache, sequence, delta_func, _context.forceGainCacheUpdates());
        ++_stats.failed_updates_due_to_conflicting_moves;
        sequence.state = MoveSequenceState::WORSEN_SOLUTION_QUALITY;
      } else {
        // Rollback would violate balance constraint => Worst Case
        ++_stats.failed_updates_due_to_conflicting_moves_without_rollback;
        sequence.state = MoveSequenceState::WORSEN_SOLUTION_QUALITY_WITHOUT_ROLLBACK;
        DBG << RED << "Rollback of move sequence violated balance constraint ( Moved Nodes ="
            << sequence.moves.size()
            << ", Expected Improvement =" << sequence.expected_improvement
            << ", Real Improvement =" << improvement
            << ", Search ID =" << search_id << ")" << END;
      }
    } else {
      ++_stats.num_improvements;
      _stats.correct_expected_improvement += (improvement == sequence.expected_improvement);
      _stats.zero_gain_improvement += (improvement == 0);
      sequence.state = MoveSequenceState::SUCCESS;
      DBG << ( improvement > 0 ? GREEN : "" ) << "SUCCESS -"
          << "Moved Nodes =" << sequence.moves.size()
          << ", Expected Improvement =" << sequence.expected_improvement
          << ", Real Improvement =" << improvement
          << ", Search ID =" << search_id << ( improvement > 0 ? END : "" );
    }
  } else {
    ++_stats.failed_updates_due_to_balance_constraint;
    sequence.state = MoveSequenceState::VIOLATES_BALANCE_CONSTRAINT;
    DBG << RED << "Move sequence violated balance constraint ( Moved Nodes ="
        << sequence.moves.size()
        << ", Expected Improvement =" << sequence.expected_improvement
        << ", Search ID =" << search_id << ")" << END;
  }

  _apply_moves_lock.unlock();

  if ( sequence.state == MoveSequenceState::SUCCESS ) {
    for ( const auto& [he, block] : new_cut_hes ) {
      _quotient_graph.addNewCutHyperedge(*_phg, he, block);
    }
    _stats.total_improvement += improvement;
  }

  return improvement;
}

template<typename GraphAndGainTypes>
const vec<HypernodeWeight>& FlowRefinementScheduler<GraphAndGainTypes>::partWeights() const {
  return _part_weights;
}

template<typename GraphAndGainTypes>
PartWeightUpdateResult FlowRefinementScheduler<GraphAndGainTypes>::partWeightUpdate(const vec<HypernodeWeight>& part_weight_deltas, const bool rollback) {
  const HypernodeWeight multiplier = rollback ? -1 : 1;
  PartWeightUpdateResult res;
  _part_weights_lock.lock();
  PartitionID i = 0;
  for ( ; i < _context.partition.k; ++i ) {
    if ( _part_weights[i] + multiplier * part_weight_deltas[i] > _max_part_weights[i] ) {
      DBG << "Move sequence violated balance constraint of block" << i
          << "(Max =" << _max_part_weights[i]
          << ", Actual =" << (_part_weights[i] + multiplier * part_weight_deltas[i]) << ")";
      res.is_balanced = false;
      res.overloaded_block = i;
      res.overload_weight = ( _part_weights[i] + multiplier *
        part_weight_deltas[i] ) - _max_part_weights[i];
      // Move Sequence Violates Balance Constraint => Rollback
      --i;
      for ( ; i >= 0; --i ) {
        _part_weights[i] -= multiplier * part_weight_deltas[i];
      }
      break;
    }
    _part_weights[i] += multiplier * part_weight_deltas[i];
  }
  _part_weights_lock.unlock();
  return res;
}

namespace {
#define FLOW_REFINEMENT_SCHEDULER(X) FlowRefinementScheduler<X>
}

INSTANTIATE_CLASS_WITH_VALID_TRAITS(FLOW_REFINEMENT_SCHEDULER)

}
