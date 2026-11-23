/*******************************************************************************
 * MIT License
 *
 * This file is part of Mt-KaHyPar.
 *
 * Copyright (C) 2020 Lars Gottesbüren <lars.gottesbueren@kit.edu>
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

#include "mt-kahypar/partition/refinement/label_propagation/label_propagation_refiner.h"

#include <tbb/parallel_for.h>

#include "mt-kahypar/definitions.h"
#include "mt-kahypar/partition/refinement/gains/gain_definitions.h"
#include "mt-kahypar/utils/randomize.h"
#include "mt-kahypar/utils/utilities.h"
#include "mt-kahypar/utils/timer.h"
#include "mt-kahypar/utils/cast.h"

namespace mt_kahypar {

  template <typename GraphAndGainTypes>
  template<bool unconstrained, typename F>
  bool LabelPropagationRefiner<GraphAndGainTypes>::moveVertex(PartitionedHypergraph& hypergraph,
                                                              const HypernodeID hn,
                                                              NextActiveNodes& next_active_nodes,
                                                              const F& objective_delta) {
    bool is_moved = false;
    ASSERT(hn != kInvalidHypernode);
    if ( hypergraph.isBorderNode(hn) && !hypergraph.isFixed(hn) ) {
      ASSERT(hypergraph.nodeIsEnabled(hn));

      Move best_move = _gain.computeMaxGainMove(hypergraph, hn, false, false, unconstrained);
      // We perform a move if it either improves the solution quality or, in case of a
      // zero gain move, the balance of the solution.
      const bool positive_gain = best_move.gain < 0;
      const bool zero_gain_move = (_context.refinement.label_propagation.rebalancing &&
                                    best_move.gain == 0 &&
                                    hypergraph.partWeight(best_move.from) - 1 >
                                    hypergraph.partWeight(best_move.to) + 1 &&
                                    hypergraph.partWeight(best_move.to) <
                                    _context.partition.perfect_balance_part_weights[best_move.to]);
      const bool perform_move = positive_gain || zero_gain_move;
      if (best_move.from != best_move.to && perform_move) {
        PartitionID from = best_move.from;
        PartitionID to = best_move.to;

        Gain delta_before = _gain.localDelta();
        bool changed_part = changeNodePart<unconstrained>(hypergraph, hn, from, to, objective_delta);
        ASSERT(!unconstrained || changed_part);
        is_moved = true;
        if (unconstrained || changed_part) {
          // In case the move to block 'to' was successful, we verify that the "real" gain
          // of the move is either equal to our computed gain or if not, still improves
          // the solution quality.
          Gain move_delta = _gain.localDelta() - delta_before;
          bool accept_move = (move_delta == best_move.gain || move_delta <= 0);
          if (accept_move) {
            if constexpr (!unconstrained) {
              // in unconstrained case, we don't want to activate neighbors if the move is undone
              // by the rebalancing
              activateNodeAndNeighbors(hypergraph, next_active_nodes, hn, true);
            }
          } else {
            // If the real gain is not equal with the computed gain and
            // worsens the solution quality we revert the move.
            ASSERT(hypergraph.partID(hn) == to);
            changeNodePart<unconstrained>(hypergraph, hn, to, from, objective_delta);
          }
        }
      }
    }

    return is_moved;
  }

  template <typename GraphAndGainTypes>
  bool LabelPropagationRefiner<GraphAndGainTypes>::refineImpl(mt_kahypar_partitioned_hypergraph_t& phg,
                                                              const vec<HypernodeID>& refinement_nodes,
                                                              Metrics& best_metrics,
                                                              const double)  {
    PartitionedHypergraph& hypergraph = utils::cast<PartitionedHypergraph>(phg);
    resizeDataStructuresForCurrentK();
    _gain.reset();
    _next_active.reset();
    const Gain old_quality = best_metrics.quality;
    ENABLE_ASSERTIONS(
      const bool was_imbalanced = !best_metrics.imbalance.isValidPartition();)

    // Initialize set of active vertices
    initializeActiveNodes(hypergraph, refinement_nodes);

    // Perform Label Propagation
    labelPropagation(hypergraph, best_metrics);

    HEAVY_REFINEMENT_ASSERT(hypergraph.checkTrackedPartitionInformation(_gain_cache));
    ASSERT(best_metrics.quality == metrics::quality(hypergraph, _context,
        !_context.refinement.label_propagation.execute_sequential),
      V(best_metrics.quality) << V(metrics::quality(hypergraph, _context,
          !_context.refinement.label_propagation.execute_sequential)));

    // Update metrics statistics
    Gain delta = old_quality - best_metrics.quality;
    ASSERT(was_imbalanced || delta >= 0, "LP refiner worsened solution quality");
    utils::Utilities::instance().getStats(_context.utility_id).update_stat("lp_improvement", delta);
    return delta > 0;
  }


  template <typename GraphAndGainTypes>
  void LabelPropagationRefiner<GraphAndGainTypes>::labelPropagation(PartitionedHypergraph& hypergraph,
                                                                    Metrics& best_metrics) {
    NextActiveNodes next_active_nodes;
    vec<Move> rebalance_moves;
    bool should_stop = false;
    for (size_t i = 0; i < _context.refinement.label_propagation.maximum_iterations
                       && !should_stop && !_active_nodes.empty(); ++i) {
      should_stop = labelPropagationRound(hypergraph, next_active_nodes, best_metrics, rebalance_moves,
                                          _context.refinement.label_propagation.unconstrained);

      if ( _context.refinement.label_propagation.execute_sequential ) {
        _active_nodes = next_active_nodes.copy_sequential();
      } else {
        _active_nodes = next_active_nodes.copy_parallel();
      }
      next_active_nodes.clear_sequential();
    }
  }

  template <typename GraphAndGainTypes>
  bool LabelPropagationRefiner<GraphAndGainTypes>::labelPropagationRound(PartitionedHypergraph& hypergraph,
                                                                         NextActiveNodes& next_active_nodes,
                                                                         Metrics& best_metrics,
                                                                         vec<Move>& rebalance_moves,
                                                                         bool unconstrained_lp) {
    Metrics current_metrics = best_metrics;
    _visited_he.reset();
    _next_active.reset();
    _gain.reset();

    if (unconstrained_lp) {
      ASSERT(best_metrics.imbalance == metrics::imbalance(hypergraph, _context));
      moveActiveNodes<true>(hypergraph, next_active_nodes);
    } else {
      moveActiveNodes<false>(hypergraph, next_active_nodes);
    }

    current_metrics.imbalance = metrics::imbalance(hypergraph, _context);
    current_metrics.quality += _gain.delta();

    bool should_update_gain_cache = GainCache::invalidates_entries && _gain_cache.isInitialized();
    if ( should_update_gain_cache ) {
      forEachMovedNode([&](size_t j) {
        _gain_cache.recomputeInvalidTerms(hypergraph, _active_nodes[j]);
        if (!unconstrained_lp) { _active_node_was_moved[j] = uint8_t(false); }
      });
    }

    bool did_rebalance = false;
    bool should_stop = false;
    if ( unconstrained_lp ) {
      if (!metrics::isValidPartition(hypergraph, _context)) {
        should_stop = applyRebalancing(hypergraph, best_metrics, current_metrics, rebalance_moves);
        // rebalancer might initialize the gain cache
        should_update_gain_cache = GainCache::invalidates_entries && _gain_cache.isInitialized() && should_stop;
        did_rebalance = true;
      } else {
        should_update_gain_cache = false;
      }

      // store current part of each node (required for rollback)
      if ( !should_stop ) {
        forEachMovedNode([&](size_t j) {
          _old_part[_active_nodes[j]] = hypergraph.partID(_active_nodes[j]);
        });
      }
      // collect activated nodes, update gain cache and reset flags
      forEachMovedNode([&](size_t j) {
        if (!should_stop) {
          activateNodeAndNeighbors(hypergraph, next_active_nodes, _active_nodes[j], false);
        }
        if (should_update_gain_cache) {
          _gain_cache.recomputeInvalidTerms(hypergraph, _active_nodes[j]);
        }
        _active_node_was_moved[j] = uint8_t(false);
      });
    }

    // Unfortunately, in the default case without rebalancing and rollback, we can not guarantee that the quality does
    // not decrease. Race conditions during applying/reverting moves can lead to a situation where reverting some moves
    // looks beneficial but results in a net negative. This is however so rare in practice that we can accept it instead
    // of investing more running time to fix it.
    ASSERT(!did_rebalance || !best_metrics.isBetter(current_metrics));
    unused(did_rebalance);
    const Gain old_quality = best_metrics.quality;
    best_metrics = current_metrics;

    HEAVY_REFINEMENT_ASSERT(hypergraph.checkTrackedPartitionInformation(_gain_cache));
    return should_stop || old_quality - current_metrics.quality <
                          _context.refinement.label_propagation.relative_improvement_threshold * old_quality;
  }

  template <typename GraphAndGainTypes>
  template<bool unconstrained>
  void LabelPropagationRefiner<GraphAndGainTypes>::moveActiveNodes(PartitionedHypergraph& phg,
                                                                   NextActiveNodes& next_active_nodes) {
    // This function is passed as lambda to the changeNodePart function and used
    // to calculate the "real" delta of a move (in terms of the used objective function).
    auto objective_delta = [&](const SynchronizedEdgeUpdate& sync_update) {
      _gain.computeDeltaForHyperedge(sync_update);
    };
    const bool should_update_gain_cache = GainCache::invalidates_entries && _gain_cache.isInitialized();
    const bool should_mark_nodes = unconstrained || should_update_gain_cache;

    if ( _context.refinement.label_propagation.execute_sequential ) {
      utils::Randomize::instance().shuffleVector(
              _active_nodes, UL(0), _active_nodes.size(), THREAD_ID);

      for ( size_t j = 0; j < _active_nodes.size(); ++j ) {
        const HypernodeID hn = _active_nodes[j];
        if ( moveVertex<unconstrained>(phg, hn, next_active_nodes, objective_delta) ) {
          if (should_mark_nodes) { _active_node_was_moved[j] = uint8_t(true); }
        }
      }
    } else {
      utils::Randomize::instance().parallelShuffleVector(
              _active_nodes, UL(0), _active_nodes.size());

      tbb::parallel_for(UL(0), _active_nodes.size(), [&](const size_t& j) {
        const HypernodeID hn = _active_nodes[j];
        if ( moveVertex<unconstrained>(phg, hn, next_active_nodes, objective_delta) ) {
          if (should_mark_nodes) { _active_node_was_moved[j] = uint8_t(true); }
        }
      });
    }
  }


  template <typename GraphAndGainTypes>
  bool LabelPropagationRefiner<GraphAndGainTypes>::applyRebalancing(PartitionedHypergraph& hypergraph,
                                                                    const Metrics& best_metrics,
                                                                    Metrics& current_metrics,
                                                                    vec<Move>& rebalance_moves) {
    utils::Timer& timer = utils::Utilities::instance().getTimer(_context.utility_id);
    timer.start_timer("rebalance_lp", "Rebalance");
    mt_kahypar_partitioned_hypergraph_t phg = utils::partitioned_hg_cast(hypergraph);
    _rebalancer.refineAndOutputMovesLinear(phg, {}, rebalance_moves, current_metrics, 0.0);

    // append to active nodes so they are included for gain cache updates and rollback
    _active_nodes.reserve(_active_nodes.size() + rebalance_moves.size());
    for (const Move& m: rebalance_moves) {
      ASSERT(m.isValid());
      bool old_part_unintialized = _might_be_uninitialized && !_old_part_is_initialized[m.node];
      if (old_part_unintialized || m.from == _old_part[m.node]) {
        size_t i = _active_nodes.size();
        _active_nodes.push_back(m.node);
        _active_node_was_moved[i] = uint8_t(true);
        if (old_part_unintialized) {
          _old_part[m.node] = m.from;
          _old_part_is_initialized.set(m.node, true);
        }
      }
    }
    timer.stop_timer("rebalance_lp");
    DBG << "[LP] Imbalance after rebalancing: " << current_metrics.imbalance << ", quality: " << current_metrics.quality;

    // We consider the new partition an improvement if either
    // (1) the old partiton was imbalanced and balance is improved or
    // (2) the quality is improved while still being balanced
    if ( current_metrics.isBetter(best_metrics) ) {
      return false;
    } else {
      // rollback and stop LP
      auto noop_obj_fn = [](const SynchronizedEdgeUpdate&) { };
      current_metrics = best_metrics;

      forEachMovedNode([&](size_t j) {
        const HypernodeID hn = _active_nodes[j];
        ASSERT(!_might_be_uninitialized || _old_part_is_initialized[hn]);
        if (hypergraph.partID(hn) != _old_part[hn]) {
          changeNodePart<true>(hypergraph, hn, hypergraph.partID(hn), _old_part[hn], noop_obj_fn);
        }
      });
      return true;
    }
  }

  template <typename GraphAndGainTypes>
  template<typename F>
  void LabelPropagationRefiner<GraphAndGainTypes>::forEachMovedNode(F node_fn) {
    if ( _context.refinement.label_propagation.execute_sequential ) {
      for (size_t j = 0; j < _active_nodes.size(); j++) {
        if (_active_node_was_moved[j]) {
          node_fn(j);
        }
      }
    } else {
      tbb::parallel_for(UL(0), _active_nodes.size(), [&](const size_t j) {
        if (_active_node_was_moved[j]) {
          node_fn(j);
        }
      });
    }
  }

  template <typename GraphAndGainTypes>
  void LabelPropagationRefiner<GraphAndGainTypes>::initializeImpl(mt_kahypar_partitioned_hypergraph_t& phg) {
    unused(phg);
  }

  template <typename GraphAndGainTypes>
  void LabelPropagationRefiner<GraphAndGainTypes>::initializeActiveNodes(PartitionedHypergraph& hypergraph,
                                                                         const vec<HypernodeID>& refinement_nodes) {
    _active_nodes.clear();
    if ( refinement_nodes.empty() ) {
      _might_be_uninitialized = false;
      if ( _context.refinement.label_propagation.execute_sequential ) {
        for ( const HypernodeID hn : hypergraph.nodes() ) {
          if ( _context.refinement.label_propagation.rebalancing || hypergraph.isBorderNode(hn) ) {
            _active_nodes.push_back(hn);
          }
          if ( _context.refinement.label_propagation.unconstrained ) {
            _old_part[hn] = hypergraph.partID(hn);
          }
        }
      } else {
        // Setup active nodes in parallel
        // A node is active, if it is a border vertex.
        NextActiveNodes tmp_active_nodes;
        hypergraph.doParallelForAllNodes([&](const HypernodeID& hn) {
          if ( _context.refinement.label_propagation.rebalancing || hypergraph.isBorderNode(hn) ) {
            if ( _next_active.compare_and_set_to_true(hn) ) {
              tmp_active_nodes.stream(hn);
            }
          }
          if ( _context.refinement.label_propagation.unconstrained ) {
            _old_part[hn] = hypergraph.partID(hn);
          }
        });

        _active_nodes = tmp_active_nodes.copy_parallel();
      }
    } else {
      _active_nodes = refinement_nodes;

      if ( _context.refinement.label_propagation.unconstrained ) {
        auto set_old_part = [&](const size_t& i) {
          const HypernodeID hn = refinement_nodes[i];
          _old_part[hn] = hypergraph.partID(hn);
          _old_part_is_initialized.set(hn, true);
        };

        // we don't want to scan the whole graph for localized LP
        _might_be_uninitialized = true;
        _old_part_is_initialized.reset();
        if ( _context.refinement.label_propagation.execute_sequential ) {
          for (size_t i = 0; i < refinement_nodes.size(); ++i) {
            set_old_part(i);
          }
        } else {
          tbb::parallel_for(UL(0), refinement_nodes.size(), set_old_part);
        }
      }
    }

    _next_active.reset();
  }

  namespace {
  #define LABEL_PROPAGATION_REFINER(X) LabelPropagationRefiner<X>
  }

  // explicitly instantiate so the compiler can generate them when compiling this cpp file
  INSTANTIATE_CLASS_WITH_VALID_TRAITS(LABEL_PROPAGATION_REFINER)
}
