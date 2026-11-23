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

#include <set>

#include "mt-kahypar/partition/refinement/fm/multitry_kway_fm.h"

#include "mt-kahypar/definitions.h"
#include "mt-kahypar/utils/utilities.h"
#include "mt-kahypar/parallel/thread_management.h"
#include "mt-kahypar/partition/factories.h"   // TODO removing this could make compilation a lot faster
#include "mt-kahypar/partition/metrics.h"
#include "mt-kahypar/partition/refinement/gains/gain_definitions.h"
#include "mt-kahypar/utils/memory_tree.h"
#include "mt-kahypar/utils/cast.h"

namespace mt_kahypar {
  using ds::StreamingVector;

  template<typename GraphAndGainTypes>
  MultiTryKWayFM<GraphAndGainTypes>::MultiTryKWayFM(const HypernodeID num_hypernodes,
                                                 const HyperedgeID num_hyperedges,
                                                 const Context& c,
                                                 GainCache& gainCache,
                                                 IRebalancer& rb) :
    initial_num_nodes(num_hypernodes),
    context(c),
    gain_cache(gainCache),
    current_k(c.partition.k),
    sharedData(num_hypernodes),
    fm_strategy(FMStrategyFactory::getInstance().createObject(context.refinement.fm.algorithm, context, sharedData)),
    globalRollback(num_hyperedges, context, gainCache),
    ets_fm([&] { return constructLocalizedKWayFMSearch(); }),
    tmp_move_order(num_hypernodes),
    rebalancer(rb) {
    if (context.refinement.fm.obey_minimal_parallelism) {
      sharedData.finishedTasksLimit = std::min(UL(8), context.shared_memory.num_threads);
    }
  }

  // helper function for rebalancing
  std::vector<HypernodeWeight> setupMaxPartWeights(const Context& context) {
    double max_part_weight_scaling = context.refinement.fm.rollback_balance_violation_factor;
    if (max_part_weight_scaling == 1.0) {
      return context.partition.max_part_weights;
    }

    std::vector<HypernodeWeight> max_part_weights = context.partition.perfect_balance_part_weights;
    if (max_part_weight_scaling == 0.0) {
      for (PartitionID i = 0; i < context.partition.k; ++i) {
        max_part_weights[i] = std::numeric_limits<HypernodeWeight>::max();
      }
    } else {
      for (PartitionID i = 0; i < context.partition.k; ++i) {
        max_part_weights[i] *= ( 1.0 + context.partition.epsilon * max_part_weight_scaling );
      }
    }
    return max_part_weights;
  }

  template<typename GraphAndGainTypes>
  bool MultiTryKWayFM<GraphAndGainTypes>::refineImpl(mt_kahypar_partitioned_hypergraph_t& hypergraph,
                                                  const vec<HypernodeID>& refinement_nodes,
                                                  Metrics& metrics,
                                                  const double time_limit) {
    PartitionedHypergraph& phg = utils::cast<PartitionedHypergraph>(hypergraph);
    resizeDataStructuresForCurrentK();

    Gain overall_improvement = 0;
    size_t consecutive_rounds_with_too_little_improvement = 0;
    enable_light_fm = false;
    sharedData.release_nodes = context.refinement.fm.release_nodes;
    double current_time_limit = time_limit;
    tbb::task_group tg;
    vec<HypernodeWeight> initialPartWeights(size_t(context.partition.k));
    std::vector<HypernodeWeight> max_part_weights = setupMaxPartWeights(context);
    HighResClockTimepoint fm_start = std::chrono::high_resolution_clock::now();
    utils::Timer& timer = utils::Utilities::instance().getTimer(context.utility_id);

    for (size_t round = 0; round < context.refinement.fm.multitry_rounds; ++round) { // global multi try rounds
      for (PartitionID i = 0; i < context.partition.k; ++i) {
        initialPartWeights[i] = phg.partWeight(i);
      }

      const bool is_unconstrained = fm_strategy->isUnconstrainedRound(round);
      if (is_unconstrained) {
        timer.start_timer("initialize_data_unconstrained", "Initialize Data for Unc. FM");
        sharedData.unconstrained.initialize<GraphAndGainTypes>(context, phg, gain_cache);
        timer.stop_timer("initialize_data_unconstrained");
      }

      timer.start_timer("collect_border_nodes", "Collect Border Nodes");
      roundInitialization(phg, refinement_nodes);
      timer.stop_timer("collect_border_nodes");

      size_t num_border_nodes = sharedData.refinementNodes.unsafe_size();
      if (num_border_nodes == 0) {
        break;
      }
      size_t num_seeds = context.refinement.fm.num_seed_nodes;
      if (context.type == ContextType::main
          && !refinement_nodes.empty()  /* n-level */
          && num_border_nodes < 20 * context.shared_memory.num_threads) {
        num_seeds = num_border_nodes / (4 * context.shared_memory.num_threads);
        num_seeds = std::min(num_seeds, context.refinement.fm.num_seed_nodes);
        num_seeds = std::max(num_seeds, UL(1));
      }

      timer.start_timer("find_moves", "Find Moves");
      size_t num_tasks = std::min(num_border_nodes, static_cast<size_t>(parallel::total_number_of_threads()));
      sharedData.finishedTasks.store(0, std::memory_order_relaxed);
      fm_strategy->findMoves(utils::localized_fm_cast(ets_fm), hypergraph,
                             num_tasks, num_seeds, round);
      timer.stop_timer("find_moves");

      if (is_unconstrained && !metrics::imbalance(phg, context, max_part_weights).isValidPartition()) {
        vec<vec<Move>> moves_by_part;

        // compute rebalancing moves
        timer.start_timer("rebalance_fm", "Rebalance");
        Metrics tmp_metrics{0, 0};
        // the correct quality is only required for assertions
        ENABLE_ASSERTIONS(tmp_metrics.quality = metrics::quality(phg, context));

        if constexpr (GainCache::invalidates_entries) {
          tbb::parallel_for(MoveID(0), sharedData.moveTracker.numPerformedMoves(), [&](const MoveID i) {
            gain_cache.recomputeInvalidTerms(phg, sharedData.moveTracker.moveOrder[i].node);
          });
        }
        HEAVY_REFINEMENT_ASSERT(phg.checkTrackedPartitionInformation(gain_cache));

        tmp_metrics.imbalance = metrics::imbalance(phg, context);
        rebalancer.refineAndOutputMoves(hypergraph, {}, moves_by_part, tmp_metrics, current_time_limit);
        timer.stop_timer("rebalance_fm");

        if (!moves_by_part.empty()) {
          // compute new move sequence where each imbalanced move is immediately rebalanced
          interleaveMoveSequenceWithRebalancingMoves(phg, initialPartWeights, max_part_weights, moves_by_part);
        }
      }

      timer.start_timer("rollback", "Rollback to Best Solution");
      HyperedgeWeight improvement = globalRollback.revertToBestPrefix(phg, sharedData, initialPartWeights, max_part_weights);
      timer.stop_timer("rollback");

      const double roundImprovementFraction = improvementFraction(improvement,
        metrics.quality - overall_improvement);
      overall_improvement += improvement;
      if (roundImprovementFraction < context.refinement.fm.min_improvement) {
        consecutive_rounds_with_too_little_improvement++;
      } else {
        consecutive_rounds_with_too_little_improvement = 0;
      }
      fm_strategy->reportImprovement(round, improvement, roundImprovementFraction);

      HighResClockTimepoint fm_timestamp = std::chrono::high_resolution_clock::now();
      const double elapsed_time = std::chrono::duration<double>(fm_timestamp - fm_start).count();
      if (debug && context.type == ContextType::main) {
        LOG << V(round) << V(improvement) << V(metrics::quality(phg, context))
            << V(metrics::imbalance(phg, context)) << V(num_border_nodes) << V(roundImprovementFraction)
            << V(elapsed_time) << V(current_time_limit);
      }

      // Enforce a time limit (based on k and coarsening time).
      // Switch to more "light-weight" FM after reaching it the first time. Abort after second time.
      if ( elapsed_time > current_time_limit ) {
        if ( !enable_light_fm ) {
          DBG << RED << "Multitry FM reached time limit => switch to Light FM Configuration" << END;
          sharedData.release_nodes = false;
          current_time_limit *= 2;
          enable_light_fm = true;
        } else {
          DBG << RED << "Light version of Multitry FM reached time limit => ABORT" << END;
          break;
        }
      }

      if ( (improvement <= 0 && (!context.refinement.fm.activate_unconstrained_dynamically || round > 1))
            || consecutive_rounds_with_too_little_improvement >= 2 ) {
        break;
      }
    }

    if (context.partition.show_memory_consumption
        && context.partition.enable_logging
        && context.type == ContextType::main
        && phg.initialNumNodes() == sharedData.moveTracker.moveOrder.size() /* top level */) {
      printMemoryConsumption();
    }

    metrics.quality -= overall_improvement;
    metrics.imbalance = metrics::imbalance(phg, context);
    HEAVY_REFINEMENT_ASSERT(phg.checkTrackedPartitionInformation(gain_cache));
    ASSERT(metrics.quality == metrics::quality(phg, context),
           V(metrics.quality) << V(metrics::quality(phg, context)));

    return overall_improvement > 0;
  }

  template<typename GraphAndGainTypes>
  void MultiTryKWayFM<GraphAndGainTypes>::roundInitialization(PartitionedHypergraph& phg,
                                                                  const vec<HypernodeID>& refinement_nodes) {
    // clear border nodes
    sharedData.refinementNodes.clear();
    const int total_num_threads = parallel::total_number_of_threads();

    if ( refinement_nodes.empty() ) {
      // log(n) level case
      // iterate over all nodes and insert border nodes into task queue
      tbb::parallel_for(tbb::blocked_range<HypernodeID>(0, phg.initialNumNodes()),
        [&](const tbb::blocked_range<HypernodeID>& r) {
          const int task_id = tbb::this_task_arena::current_thread_index();
          // In really rare cases, the tbb::this_task_arena::current_thread_index()
          // function a thread id greater than max_concurrency which causes an
          // segmentation fault if we do not perform the check here. This is caused by
          // our working queue for border nodes with which we initialize the localized
          // FM searches. For now, we do not know why this occurs but this prevents
          // the segmentation fault.
          if ( task_id >= 0 && task_id < total_num_threads ) {
            for (HypernodeID u = r.begin(); u < r.end(); ++u) {
              if (phg.nodeIsEnabled(u) && phg.isBorderNode(u) && !phg.isFixed(u)) {
                sharedData.refinementNodes.safe_push(u, task_id);
              }
            }
          }
        });
    } else {
      // n-level case
      tbb::parallel_for(UL(0), refinement_nodes.size(), [&](const size_t i) {
        const HypernodeID u = refinement_nodes[i];
        const int task_id = tbb::this_task_arena::current_thread_index();
        if ( task_id >= 0 && task_id < total_num_threads ) {
          if (phg.nodeIsEnabled(u) && phg.isBorderNode(u) && !phg.isFixed(u)) {
            sharedData.refinementNodes.safe_push(u, task_id);
          }
        }
      });
    }

    // shuffle task queue if requested
    if (context.refinement.fm.shuffle) {
      sharedData.refinementNodes.shuffle();
    }

    // requesting new searches activates all nodes by raising the deactivated node marker
    // also clears the array tracking search IDs in case of overflow
    sharedData.nodeTracker.requestNewSearches(static_cast<SearchID>(sharedData.refinementNodes.unsafe_size()));
  }

  template<typename GraphAndGainTypes>
  void MultiTryKWayFM<GraphAndGainTypes>::interleaveMoveSequenceWithRebalancingMoves(
                                                            const PartitionedHypergraph& phg,
                                                            const vec<HypernodeWeight>& initialPartWeights,
                                                            const std::vector<HypernodeWeight>& max_part_weights,
                                                            vec<vec<Move>>& rebalancing_moves_by_part) {
    ASSERT(rebalancing_moves_by_part.size() == static_cast<size_t>(context.partition.k));
    HEAVY_REFINEMENT_ASSERT([&] {
      std::set<HypernodeID> moved_nodes;
      for (PartitionID part = 0; part < context.partition.k; ++part) {
        for (const Move& m: rebalancing_moves_by_part[part]) {
          if (m.from != part || m.to != phg.partID(m.node) || moved_nodes.count(m.node) != 0) {
            return false;
          }
          moved_nodes.insert(m.node);
        }
      }
      return true;
    }());

    GlobalMoveTracker& move_tracker = sharedData.moveTracker;
    // Check the rebalancing moves for nodes that are moved twice. Double moves violate the precondition of the global
    // rollback, which requires that each node is moved at most once. Thus we "merge" the moves of any node
    // that is moved twice (e.g., 0 -> 2 -> 1 becomes 0 -> 1)
    for (PartitionID part = 0; part < context.partition.k; ++part) {
      vec<Move>& moves = rebalancing_moves_by_part[part];
      tbb::parallel_for(UL(0), moves.size(), [&](const size_t i) {
        Move& r_move = moves[i];
        if (r_move.isValid() && move_tracker.wasNodeMovedInThisRound(r_move.node)) {
          ASSERT(r_move.to == phg.partID(r_move.node));
          Move& first_move = move_tracker.getMove(move_tracker.moveOfNode[r_move.node]);
          ASSERT(r_move.node == first_move.node && r_move.from == first_move.to);
          if (first_move.from == r_move.to) {
            // if rebalancing undid the move, we simply delete it
            move_tracker.moveOfNode[r_move.node] = 0;
            first_move.invalidate();
            r_move.invalidate();
          } else {
            // "merge" the moves
            r_move.from = first_move.from;
            first_move.invalidate();
          }
        }
      }, tbb::static_partitioner());
    }

    // NOTE: We re-insert invalid rebalancing moves to ensure the gain cache is updated correctly by the global rollback
    // For now we use a sequential implementation, which is probably fast enough (since this is a single scan trough
    // the move sequence). We might replace it with a parallel implementation later.
    vec<HypernodeWeight> current_part_weights = initialPartWeights;
    vec<MoveID> current_rebalancing_move_index(context.partition.k, 0);
    MoveID next_move_index = 0;

    auto insert_moves_to_balance_part = [&](const PartitionID part) {
      if (current_part_weights[part] > max_part_weights[part]) {
        insertMovesToBalanceBlock(phg, part, max_part_weights, rebalancing_moves_by_part,
                                  next_move_index, current_part_weights, current_rebalancing_move_index);
      }
    };

    // it might be possible that the initial weights are already imbalanced
    for (PartitionID part = 0; part < context.partition.k; ++part) {
      insert_moves_to_balance_part(part);
    }

    const vec<Move>& move_order = move_tracker.moveOrder;
    const MoveID num_moves = move_tracker.numPerformedMoves();
    for (MoveID move_id = 0; move_id < num_moves; ++move_id) {
      const Move& m = move_order[move_id];
      if (m.isValid()) {
        const HypernodeWeight hn_weight = phg.nodeWeight(m.node);
        current_part_weights[m.from] -= hn_weight;
        current_part_weights[m.to] += hn_weight;
        tmp_move_order[next_move_index] = m;
        ++next_move_index;
        // insert rebalancing moves if necessary
        insert_moves_to_balance_part(m.to);
      } else {
        // setting moveOfNode to zero is necessary because, after replacing the move sequence,
        // wasNodeMovedInThisRound() could falsely return true otherwise
        move_tracker.moveOfNode[m.node] = 0;
      }
    }

    // append any remaining rebalancing moves (rollback will decide whether to keep them)
    for (PartitionID part = 0; part < context.partition.k; ++part) {
      while (current_rebalancing_move_index[part] < rebalancing_moves_by_part[part].size()) {
        const MoveID move_index_for_part = current_rebalancing_move_index[part];
        const Move& m = rebalancing_moves_by_part[part][move_index_for_part];
        ++current_rebalancing_move_index[part];
        tmp_move_order[next_move_index] = m;
        ++next_move_index;
      }
    }

    // update sharedData
    const MoveID first_move_id = move_tracker.firstMoveID;
    ASSERT(tmp_move_order.size() == move_tracker.moveOrder.size());

    std::swap(move_tracker.moveOrder, tmp_move_order);
    move_tracker.runningMoveID.store(first_move_id + next_move_index);
    tbb::parallel_for(static_cast<MoveID>(0), next_move_index, [&](const MoveID move_id) {
      const Move& m = move_tracker.moveOrder[move_id];
      if (m.isValid()) {
        move_tracker.moveOfNode[m.node] = first_move_id + move_id;
      }
    }, tbb::static_partitioner());
  }

  template<typename GraphAndGainTypes>
  void MultiTryKWayFM<GraphAndGainTypes>::insertMovesToBalanceBlock(const PartitionedHypergraph& phg,
                                                                        const PartitionID block,
                                                                        const std::vector<HypernodeWeight>& max_part_weights,
                                                                        const vec<vec<Move>>& rebalancing_moves_by_part,
                                                                        MoveID& next_move_index,
                                                                        vec<HypernodeWeight>& current_part_weights,
                                                                        vec<MoveID>& current_rebalancing_move_index) {
    while (current_part_weights[block] > max_part_weights[block]
            && current_rebalancing_move_index[block] < rebalancing_moves_by_part[block].size()) {
      const MoveID move_index_for_block = current_rebalancing_move_index[block];
      const Move& m = rebalancing_moves_by_part[block][move_index_for_block];
      ++current_rebalancing_move_index[block];
      tmp_move_order[next_move_index] = m;
      ++next_move_index;
      if (m.isValid()) {
        const HypernodeWeight hn_weight = phg.nodeWeight(m.node);
        current_part_weights[m.from] -= hn_weight;
        current_part_weights[m.to] += hn_weight;

        if (current_part_weights[m.to] > max_part_weights[m.to]) {
          // edge case: it is possible that the rebalancing move itself causes new imbalance -> call recursively
          insertMovesToBalanceBlock(phg, m.to, max_part_weights, rebalancing_moves_by_part,
                                    next_move_index, current_part_weights, current_rebalancing_move_index);
        }
      }
    }
  }


  template<typename GraphAndGainTypes>
  void MultiTryKWayFM<GraphAndGainTypes>::initializeImpl(mt_kahypar_partitioned_hypergraph_t& hypergraph) {
    PartitionedHypergraph& phg = utils::cast<PartitionedHypergraph>(hypergraph);

    if (!gain_cache.isInitialized()) {
      gain_cache.initializeGainCache(phg);
    }
  }

  template<typename GraphAndGainTypes>
  void MultiTryKWayFM<GraphAndGainTypes>::resizeDataStructuresForCurrentK() {
    // If the number of blocks changes, we resize data structures
    // (can happen during deep multilevel partitioning)
    if ( current_k != context.partition.k ) {
      current_k = context.partition.k;
      // Note that in general changing the number of blocks in the
      // global rollback data structure should not resize any data structure
      // as we initialize them with the final number of blocks. This is just a fallback
      // if someone changes this in the future.
      globalRollback.changeNumberOfBlocks(current_k);
      sharedData.unconstrained.changeNumberOfBlocks(current_k);
      for ( auto& localized_fm : ets_fm ) {
        localized_fm.changeNumberOfBlocks(current_k);
      }
      gain_cache.changeNumberOfBlocks(current_k);
    }
  }

  template<typename GraphAndGainTypes>
  void MultiTryKWayFM<GraphAndGainTypes>::printMemoryConsumption() {
    utils::MemoryTreeNode fm_memory("Multitry k-Way FM", utils::OutputType::MEGABYTE);

    for (const auto& fm : ets_fm) {
      fm.memoryConsumption(&fm_memory);
    }
    sharedData.memoryConsumption(&fm_memory);
    fm_memory.finalize();

    LOG << BOLD << "\n FM Memory Consumption" << END;
    LOG << fm_memory;
  }

  namespace {
  #define MULTITRY_KWAY_FM(X) MultiTryKWayFM<X>
  }

  INSTANTIATE_CLASS_WITH_VALID_TRAITS(MULTITRY_KWAY_FM)
} // namespace mt_kahypar
