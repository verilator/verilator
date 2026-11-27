/*******************************************************************************
 * MIT License
 *
 * This file is part of Mt-KaHyPar.
 *
 * Copyright (C) 2023 Robert Krause <robert.krause@student.kit.edu>
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

#include "mt-kahypar/partition/refinement/rebalancing/deterministic_rebalancer.h"

#include <tbb/parallel_for_each.h>
#include <tbb/enumerable_thread_specific.h>
#include <tbb/parallel_for.h>

#include "mt-kahypar/definitions.h"
#include "mt-kahypar/parallel/scalable_sort.h"
#include "mt-kahypar/partition/metrics.h"
#include "mt-kahypar/partition/refinement/gains/gain_definitions.h"
#include "mt-kahypar/utils/cast.h"

namespace mt_kahypar {
namespace impl {
  // factoring out this function seems to improve compile time, probably
  // because the calling function becomes overly complex if it is inlined
  MT_KAHYPAR_ATTRIBUTE_NO_INLINE void scalableSortMoves(vec<rebalancer::RebalancingMove>& moves) {
    parallel::scalable_sort(moves, [](const rebalancer::RebalancingMove& a, const rebalancer::RebalancingMove& b) {
        return a.priority < b.priority || (a.priority == b.priority && a.hn > b.hn);
      });
  }
}

static constexpr size_t ABSOLUTE_MAX_ROUNDS = 30;

static float transformGain(Gain gain_, HypernodeWeight wu) {
  float gain = gain_;
  if (gain > 0) {
    gain /= wu;
  } else if (gain < 0) {
    gain *= wu;
  }
  return gain;
}

template <typename GraphAndGainTypes>
bool DeterministicRebalancer<GraphAndGainTypes>::refineImpl(mt_kahypar_partitioned_hypergraph_t& hypergraph,
                                                            const vec<HypernodeID>&,
                                                            Metrics& best_metrics,
                                                            double) {
  if (_gain_cache.isInitialized()) {
    throw UnsupportedOperationException("deterministic rebalancer does not support algorithms with gain cache (FM refinement)");
  }

  PartitionedHypergraph& phg = utils::cast<PartitionedHypergraph>(hypergraph);
  resizeDataStructuresForCurrentK();
  _gain_computation.reset();

  _repair_empty_blocks.repairEmptyBlocks(hypergraph, _gain_computation, [&](const Move& m) {
    changeNodePart(phg, m.node, m.from, m.to);
  });
  ASSERT(!metrics::imbalance(phg, _context).violates_non_empty_blocks || phg.initialNumNodes() < ID(_context.partition.k));
  updateImbalance(phg);

  size_t iteration = 0;
  const size_t max_rounds = _context.refinement.rebalancing.det_max_rounds == 0 ? ABSOLUTE_MAX_ROUNDS : std::min(ABSOLUTE_MAX_ROUNDS, _context.refinement.rebalancing.det_max_rounds);
  while (_num_imbalanced_parts > 0 && iteration < max_rounds) {
    weakRebalancingRound(phg);
    ASSERT(checkPreviouslyOverweightParts(phg));
    updateImbalance(phg);
    ++iteration;
  }

  if constexpr (!PartitionedHypergraph::is_graph) {
    Gain delta = _gain_computation.delta();
    HEAVY_REFINEMENT_ASSERT(best_metrics.quality + delta == metrics::quality(phg, _context),
      V(best_metrics.quality) << V(delta) << V(metrics::quality(phg, _context)));
    best_metrics.quality += delta;
  } else {
    // the correct quality is only required for assertions
    ENABLE_ASSERTIONS(best_metrics.quality = metrics::quality(phg, _context));
  }
  phg.resetEdgeSynchronization();
  best_metrics.imbalance = metrics::imbalance(phg, _context);
  return true;
}

template <typename  GraphAndGainTypes>
void DeterministicRebalancer<GraphAndGainTypes>::updateImbalance(const PartitionedHypergraph& phg) {
  _num_imbalanced_parts = 0;
  for (PartitionID part = 0; part < _context.partition.k; ++part) {
    const HypernodeWeight current_imbalance = phg.partWeight(part) - _context.partition.max_part_weights[part];
    _current_imbalance[part] = current_imbalance;
    if (current_imbalance > 0) {
      ++_num_imbalanced_parts;
    }
  }
}

template <typename GraphAndGainTypes>
rebalancer::RebalancingMove DeterministicRebalancer<GraphAndGainTypes>::computeGainAndTargetPart(const PartitionedHypergraph& phg,
                                                                                                 const HypernodeID hn,
                                                                                                 bool non_adjacent_blocks) {
  const HypernodeWeight hn_weight = phg.nodeWeight(hn);
  RatingMap& tmp_scores = _gain_computation.localScores();
  Gain isolated_block_gain = 0;
  _gain_computation.precomputeGains(phg, hn, tmp_scores, isolated_block_gain, true);

  Gain best_gain = isolated_block_gain;
  PartitionID best_target = kInvalidPartition;
  for (const auto& entry : tmp_scores) {
    const PartitionID to = entry.key;
    const Gain gain = _gain_computation.gain(entry.value, isolated_block_gain);
    if (gain <= best_gain && isValidTarget(phg, to, hn_weight)) {
      best_gain = gain;
      best_target = to;
    }
  }

  // if no adjacent block with free capacity exists, we need to consider non-adjacent blocks
  if (non_adjacent_blocks && best_target == kInvalidPartition) {
    // we start with a block that is chosen by random, to ensure a reasonable distribution of nodes
    // to target blocks (note: this does not always result in a uniform distribution since some blocks
    // are not an acceptable target, but it should be good enough)
    const PartitionID start = hn % _current_k;
    PartitionID to = start;
    do {
      if (isValidTarget(phg, to, hn_weight)
        && !tmp_scores.contains(to)) {
        best_target = to;
        break;
      }

      ++to;
      if (to == _current_k) {
        to = 0;
      }
    } while (to != start);
    ASSERT(best_target == kInvalidPartition || (best_target >= 0 && best_target < _current_k));
  }
  tmp_scores.clear();
  return { hn, best_target, transformGain(best_gain, hn_weight), hn_weight };
}

template <typename GraphAndGainTypes>
void DeterministicRebalancer<GraphAndGainTypes>::weakRebalancingRound(PartitionedHypergraph& phg) {
  ASSERT(_current_k == _context.partition.k);
  for (auto& moves : _tmp_potential_moves) {
    moves.clear_sequential();
  }

  // calculate gain and target for each node in a overweight part
  // group moves by source part
  phg.doParallelForAllNodes([&](const HypernodeID hn) {
    const PartitionID from = phg.partID(hn);
    const HypernodeWeight weight = phg.nodeWeight(hn);
    if (_current_imbalance[from] > 0 && mayMoveNode(phg, from, weight) && !phg.isFixed(hn)) {
      const auto triple = computeGainAndTargetPart(phg, hn, true);
      if (from != triple.to && triple.to != kInvalidPartition) {
        _tmp_potential_moves[from].stream(triple);
      }
    }
  });

  tbb::parallel_for(0, _current_k, [&](const PartitionID part) {
    if (_tmp_potential_moves[part].size() > 0) {
      _moves[part] = _tmp_potential_moves[part].copy_parallel();
      ASSERT(_moves[part].size() > 0);

      // sort the moves from each overweight part by priority
      impl::scalableSortMoves(_moves[part]);

      // determine which moves to execute
      size_t last_move_idx = 0;
      HypernodeWeight sum = 0;
      for (; last_move_idx < _moves[part].size() && sum < _current_imbalance[part]; ++last_move_idx) {
        sum += _moves[part][last_move_idx].weight;
      }

      bool success = (sum >= _current_imbalance[part]);
      _block_has_only_heavy_vertices[part] = static_cast<uint8_t>(!success);

      // execute moves in parallel
      tbb::parallel_for(UL(0), last_move_idx, [&](const size_t j) {
        const auto& move = _moves[part][j];
        ASSERT(move.to == kInvalidPartition || (move.to >= 0 && move.to < _current_k));
        changeNodePart(phg, move.hn, part, move.to);
      });
    } else if (_current_imbalance[part] > 0) {
      _block_has_only_heavy_vertices[part] = static_cast<uint8_t>(true);
    }
  });
}


template <typename GraphAndGainTypes>
void DeterministicRebalancer<GraphAndGainTypes>::resizeDataStructuresForCurrentK() {
  // If the number of blocks changes, we resize data structures
  // (can happen during deep multilevel partitioning)
  if (_current_k != _context.partition.k) {
    _current_k = _context.partition.k;
    _gain_computation.changeNumberOfBlocks(_current_k);
    _moves.resize(_current_k);
    _tmp_potential_moves.resize(_current_k);
    _current_imbalance.resize(_current_k);
    _block_has_only_heavy_vertices.resize(_current_k);
  }
}

template <typename GraphAndGainTypes>
bool DeterministicRebalancer<GraphAndGainTypes>::mayMoveNode(const PartitionedHypergraph& phg, PartitionID part, HypernodeWeight hn_weight) const {
  double allowed_weight = phg.partWeight(part) - _context.partition.perfect_balance_part_weights[part];
  allowed_weight *= _context.refinement.rebalancing.det_heavy_vertex_exclusion_factor;
  return hn_weight <= allowed_weight || _block_has_only_heavy_vertices[part];
}

template <typename GraphAndGainTypes>
HypernodeWeight DeterministicRebalancer<GraphAndGainTypes>::deadzoneForPart(PartitionID part) const {
  const HypernodeWeight balanced = _context.partition.perfect_balance_part_weights[part];
  const HypernodeWeight max = _context.partition.max_part_weights[part];
  return max - _context.refinement.rebalancing.det_relative_deadzone_size * (max - balanced);
}

template <typename GraphAndGainTypes>
bool DeterministicRebalancer<GraphAndGainTypes>::isValidTarget(const PartitionedHypergraph& hypergraph, PartitionID part, HypernodeWeight hn_weight) const {
  const HypernodeWeight part_weight = hypergraph.partWeight(part);
  return (part_weight < deadzoneForPart(part)) &&
    part_weight + hn_weight <= _context.partition.max_part_weights[part];
}

template <typename GraphAndGainTypes>
bool DeterministicRebalancer<GraphAndGainTypes>::changeNodePart(PartitionedHypergraph& phg,
                                                                const HypernodeID hn,
                                                                const PartitionID from,
                                                                const PartitionID to) {
  // This function is passed as lambda to the changeNodePart function and used
  // to calculate the "real" delta of a move (in terms of the used objective function).
  auto objective_delta = [&](const SynchronizedEdgeUpdate& sync_update) {
      _gain_computation.computeDeltaForHyperedge(sync_update);
  };

  bool success = false;
  success = PartitionedHypergraph::is_graph ? phg.changeNodePartNoSync(hn, from, to) : phg.changeNodePart(hn, from, to, objective_delta);
  ASSERT(success);
  return success;
}

template <typename GraphAndGainTypes>
bool DeterministicRebalancer<GraphAndGainTypes>::checkPreviouslyOverweightParts(const PartitionedHypergraph& phg) const {
  for (PartitionID i = 0; i < _current_k; ++i) {
    const auto partWeight = phg.partWeight(i);
    unused(partWeight);
    if (_current_imbalance[i] > 0) {
        const auto& max_part_weights = _context.partition.max_part_weights;
        ASSERT(partWeight <= max_part_weights[i] || _block_has_only_heavy_vertices[i], V(partWeight) << V(max_part_weights[i]));
        unused(max_part_weights);
    }
  }
  return true;
}

// explicitly instantiate so the compiler can generate them when compiling this cpp file
namespace {
#define DETERMINISTIC_REBALANCER(X) DeterministicRebalancer<X>
}

// explicitly instantiate so the compiler can generate them when compiling this cpp file
INSTANTIATE_CLASS_WITH_VALID_TRAITS(DETERMINISTIC_REBALANCER)
}
