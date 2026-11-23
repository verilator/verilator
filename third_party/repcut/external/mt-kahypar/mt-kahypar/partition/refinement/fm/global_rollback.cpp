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

#include "repcut_serial.h"

#include "mt-kahypar/partition/refinement/fm/global_rollback.h"

#include <atomic>
#include <tbb/parallel_scan.h>

#include "mt-kahypar/definitions.h"
#include "mt-kahypar/partition/metrics.h"
#include "mt-kahypar/partition/refinement/gains/gain_definitions.h"
#include "mt-kahypar/utils/timer.h"
#include "mt-kahypar/partition/refinement/gains/gain_cache_ptr.h"
#include "mt-kahypar/datastructures/synchronized_edge_update.h"

namespace mt_kahypar {

  template<typename PartitionedHypergraph>
  struct BalanceAndBestIndexScan {
    const PartitionedHypergraph& phg;
    const vec<Move>& moves;

    struct Prefix {
      Gain gain = 0;                           /** gain when using valid moves up to best_index */
      MoveID best_index = 0;                   /** local ID of first move to revert */
      HypernodeWeight heaviest_weight =
              std::numeric_limits<HypernodeWeight>::max();   /** weight of the heaviest part */

      bool operator<(const Prefix& o) const {
        return gain > o.gain ||
               (gain == o.gain && std::tie(heaviest_weight, best_index) < std::tie(o.heaviest_weight, o.best_index));
      }
    };
    std::shared_ptr< tbb::enumerable_thread_specific<Prefix> > local_best;

    Gain gain_sum = 0;

    vec<HypernodeWeight> part_weights;
    const std::vector<HypernodeWeight>& max_part_weights;

    BalanceAndBestIndexScan(BalanceAndBestIndexScan& b, tbb::split) :
            phg(b.phg),
            moves(b.moves),
            local_best(b.local_best),
            gain_sum(0),
            part_weights(b.part_weights.size(), 0),
            max_part_weights(b.max_part_weights) { }


    BalanceAndBestIndexScan(const PartitionedHypergraph& phg,
                            const vec<Move>& moves,
                            const vec<HypernodeWeight>& part_weights,
                            const std::vector<HypernodeWeight>& max_part_weights) :
            phg(phg),
            moves(moves),
            local_best(std::make_shared< tbb::enumerable_thread_specific<Prefix> >()),
            part_weights(part_weights),
            max_part_weights(max_part_weights)
    {
    }


    void operator()(const tbb::blocked_range<MoveID>& r, tbb::pre_scan_tag ) {
      for (MoveID i = r.begin(); i < r.end(); ++i) {
        const Move& m = moves[i];
        if (m.isValid()) {  // skip locally reverted moves
          gain_sum += m.gain;
          part_weights[m.from] -= phg.nodeWeight(m.node);
          part_weights[m.to] += phg.nodeWeight(m.node);
        }
      }
    }

    // subranges a | b | c | d . assuming this ran pre_scan on c,
    // then lhs ran pre_scan on b and final_scan of this will be on d
    void reverse_join(BalanceAndBestIndexScan& lhs) {
      for (size_t i = 0; i < part_weights.size(); ++i) {
        part_weights[i] += lhs.part_weights[i];
      }
      gain_sum += lhs.gain_sum;
    }

    void operator()(const tbb::blocked_range<MoveID>& r, tbb::final_scan_tag ) {
      size_t overloaded = 0;
      for (size_t i = 0; i < part_weights.size(); ++i) {
        if (part_weights[i] > max_part_weights[i]) {
          overloaded++;
        }
      }

      Prefix current;
      for (MoveID i = r.begin(); i < r.end(); ++i) {
        const Move& m = moves[i];

        if (m.isValid()) {  // skip locally reverted moves
          gain_sum += m.gain;

          const bool from_overloaded = part_weights[m.from] > max_part_weights[m.from];
          part_weights[m.from] -= phg.nodeWeight(m.node);
          if (from_overloaded && part_weights[m.from] <= max_part_weights[m.from]) {
            overloaded--;
          }
          const bool to_overloaded = part_weights[m.to] > max_part_weights[m.to];
          part_weights[m.to] += phg.nodeWeight(m.node);
          if (!to_overloaded && part_weights[m.to] > max_part_weights[m.to]) {
            overloaded++;
          }

          if (overloaded == 0 && gain_sum >= current.gain) {
            Prefix new_prefix = { gain_sum, i + 1, *std::max_element(part_weights.begin(), part_weights.end()) };
            current = std::min(current, new_prefix);
          }
        }
      }

      if (current.best_index != 0) {
        Prefix& lb = local_best->local();
        lb = std::min(lb, current);
      }
    }

    void assign(BalanceAndBestIndexScan& b) {
      gain_sum = b.gain_sum;
    }

    Prefix finalize(const vec<HypernodeWeight>& initial_part_weights) {
      Prefix res { 0, 0, *std::max_element(initial_part_weights.begin(), initial_part_weights.end()) };
      for (const Prefix& x : *local_best) {
        res = std::min(res, x);
      }
      return res;
    }
  };

  template<typename GraphAndGainTypes>
  HyperedgeWeight GlobalRollback<GraphAndGainTypes>::revertToBestPrefixParallel(
          PartitionedHypergraph& phg, FMSharedData& sharedData,
          const vec<HypernodeWeight>& partWeights, const std::vector<HypernodeWeight>& maxPartWeights) {
    const MoveID numMoves = sharedData.moveTracker.numPerformedMoves();
    if (numMoves == 0) return 0;

    const vec<Move>& move_order = sharedData.moveTracker.moveOrder;

    recalculateGains(phg, sharedData);
    HEAVY_REFINEMENT_ASSERT(verifyGains(phg, sharedData));

    BalanceAndBestIndexScan<PartitionedHypergraph> s(phg, move_order, partWeights, maxPartWeights);
    // TODO set grain size in blocked_range? to avoid too many copies of part weights array. experiment with different values
    tbb::parallel_scan(tbb::blocked_range<MoveID>(0, numMoves), s);
    typename BalanceAndBestIndexScan<PartitionedHypergraph>::Prefix b = s.finalize(partWeights);

    tbb::parallel_for(b.best_index, numMoves, [&](const MoveID moveID) {
      const Move& m = move_order[moveID];
      if (m.isValid()) {
        moveVertex(phg, m.node, m.to, m.from);
      }
    });

    // recompute penalty term values since they are potentially invalid
    if constexpr (GainCache::invalidates_entries) {
      tbb::parallel_for(MoveID(0), numMoves, [&](const MoveID i) {
        gain_cache.recomputeInvalidTerms(phg, move_order[i].node);
      });
    }

    sharedData.moveTracker.reset();

    HEAVY_REFINEMENT_ASSERT(phg.checkTrackedPartitionInformation(gain_cache));
    return b.gain;
  }

  template<typename GraphAndGainTypes>
  void GlobalRollback<GraphAndGainTypes>::recalculateGainForHyperedge(PartitionedHypergraph& phg,
                                                                   FMSharedData& sharedData,
                                                                   const HyperedgeID& e) {
    GlobalMoveTracker& tracker = sharedData.moveTracker;
    auto& r = ets_recalc_data.local();

    // compute auxiliary data
    for (HypernodeID v : phg.pins(e)) {
      if (tracker.wasNodeMovedInThisRound(v)) {
        const MoveID m_id = tracker.moveOfNode[v];
        const Move& m = tracker.getMove(m_id);
        Rollback::updateMove(m_id, m, r);
        // no change for remaining pins!
      } else {
        Rollback::updateNonMovedPinInBlock(phg.partID(v), r);
      }
    }

    // distribute gains to pins
    for (HypernodeID v : phg.pins(e)) {
      if (tracker.wasNodeMovedInThisRound(v)) {
        const MoveID m_id = tracker.moveOfNode[v];
        Move& m = tracker.getMove(m_id);

        const HyperedgeWeight benefit = Rollback::benefit(phg, e, m_id, m, r);;
        const HyperedgeWeight penalty = Rollback::penalty(phg, e, m_id, m, r);

        if ( benefit > 0 ) {
          // increase gain of v by benefit
          repcut_serial::Ref(m.gain).fetch_add(benefit, std::memory_order_relaxed);
        }

        if ( penalty > 0 ) {
          // decrease gain of v by penalty
          repcut_serial::Ref(m.gain).fetch_sub(penalty, std::memory_order_relaxed);
        }
      }
    }

    if (context.partition.k <= static_cast<int>(2 * phg.edgeSize(e))) {
      // this branch is an optimization. in case it is cheaper to iterate over the parts, do that
      for (PartitionID i = 0; i < context.partition.k; ++i) {
        r[i].reset();
      }
    } else {
      for (HypernodeID v : phg.pins(e)) {
        if (tracker.wasNodeMovedInThisRound(v)) {
          const Move& m = tracker.getMove(tracker.moveOfNode[v]);
          r[m.from].reset();
          r[m.to].reset();
        } else {
          r[phg.partID(v)].reset();
        }
      }
    }
  }

  template<typename GraphAndGainTypes>
  void GlobalRollback<GraphAndGainTypes>::recalculateGainForHyperedgeViaAttributedGains(PartitionedHypergraph& phg,
                                                                                     FMSharedData& sharedData,
                                                                                     const HyperedgeID& e) {
    GlobalMoveTracker& tracker = sharedData.moveTracker;

    // Find all pins of hyperedge that were moved in this round
    vec<HypernodeID> moved_pins;
    for ( const HypernodeID& pin : phg.pins(e) ) {
      if ( tracker.wasNodeMovedInThisRound(pin) ) {
        moved_pins.push_back(pin);
      }
    }

    // Sort moves in decreasing order of execution
    // => first entry is the node that was moved last in the hyperedge
    std::sort(moved_pins.begin(), moved_pins.end(),
      [&](const HypernodeID& lhs, const HypernodeID& rhs) {
        return tracker.moveOfNode[lhs] > tracker.moveOfNode[rhs];
      });

    // Revert moves and compute attributed gain
    SynchronizedEdgeUpdate sync_update = phg.createEdgeUpdate(e);
    for ( const HypernodeID& u : moved_pins ) {
      const MoveID m_id = tracker.moveOfNode[u];
      Move& m = tracker.getMove(m_id);
      sync_update.from = m.to;
      sync_update.to = m.from;
      sync_update.pin_count_in_from_part_after = sync_update.decrementPinCountInPart(sync_update.from);
      sync_update.pin_count_in_to_part_after = sync_update.incrementPinCountInPart(sync_update.to);
      // This is the gain for reverting the move.
      const HyperedgeWeight attributed_gain = AttributedGains::gain(sync_update);
      // For recomputed gains, a postive gain means improvement. However, the opposite
      // is the case for attributed gains.
      repcut_serial::Ref(m.gain).fetch_add(attributed_gain, std::memory_order_relaxed);
    }
  }

  template<typename GraphAndGainTypes>
  void GlobalRollback<GraphAndGainTypes>::recalculateGainForGraphEdgeViaAttributedGains(PartitionedHypergraph& phg,
                                                                                     FMSharedData& sharedData,
                                                                                     const HyperedgeID& e) {
    if ( !phg.isSinglePin(e) ) {
      GlobalMoveTracker& tracker = sharedData.moveTracker;

      HypernodeID first_move = phg.edgeSource(e);
      HypernodeID second_move = phg.edgeTarget(e);
      if ( !tracker.wasNodeMovedInThisRound(first_move) &&
           !tracker.wasNodeMovedInThisRound(second_move) ) {
        // Both nodes were not moved in this round => nothing to do
        return;
      } else if ( tracker.wasNodeMovedInThisRound(first_move) &&
                  tracker.wasNodeMovedInThisRound(second_move) ) {
        if ( tracker.moveOfNode[first_move] > tracker.moveOfNode[second_move] ) {
          std::swap(first_move, second_move);
        }
      } else if ( !tracker.wasNodeMovedInThisRound(first_move) &&
                   tracker.wasNodeMovedInThisRound(second_move) ) {
        std::swap(first_move, second_move);
      }

      ASSERT(tracker.wasNodeMovedInThisRound(first_move));
      ASSERT(!tracker.wasNodeMovedInThisRound(second_move) ||
        (tracker.moveOfNode[first_move] < tracker.moveOfNode[second_move]));
      Move& first_m = tracker.getMove(tracker.moveOfNode[first_move]);
      // sentinel in case second node was not moved
      Move tmp_second_m = Move { phg.partID(second_move),
        phg.partID(second_move), second_move, 0 };
      Move& second_m = tracker.wasNodeMovedInThisRound(second_move) ?
        tracker.getMove(tracker.moveOfNode[second_move]) : tmp_second_m;

      // Compute gain of first move
      SynchronizedEdgeUpdate sync_update = phg.createEdgeUpdate(e);
      sync_update.from = first_m.from;
      sync_update.to = first_m.to;
      sync_update.pin_count_in_from_part_after =
        first_m.from == second_m.from ? 1 : 0;
      sync_update.pin_count_in_to_part_after =
        first_m.to == second_m.from ? 2 : 1;
      sync_update.block_of_other_node = second_m.from;
      const HyperedgeWeight attributed_gain = AttributedGains::gain(sync_update);
      repcut_serial::Ref(first_m.gain).fetch_add(-attributed_gain, std::memory_order_relaxed);

      if ( tracker.wasNodeMovedInThisRound(second_move) )  {
        // Compute gain of second move
        sync_update.from = second_m.from;
        sync_update.to = second_m.to;
        sync_update.pin_count_in_from_part_after =
          first_m.to == second_m.from ? 1 : 0;
        sync_update.pin_count_in_to_part_after =
          first_m.to == second_m.to ? 2 : 1;
        sync_update.block_of_other_node = first_m.to;
        const HyperedgeWeight attributed_gain = AttributedGains::gain(sync_update);
        repcut_serial::Ref(second_m.gain).fetch_add(-attributed_gain, std::memory_order_relaxed);
      }
    }
  }

  template<typename GraphAndGainTypes>
  void GlobalRollback<GraphAndGainTypes>::recalculateGains(PartitionedHypergraph& phg, FMSharedData& sharedData) {
    GlobalMoveTracker& tracker = sharedData.moveTracker;

    auto recalculate_and_distribute_for_hyperedge = [&](const HyperedgeID e) {
      if constexpr ( Rollback::supports_parallel_rollback ) {
        recalculateGainForHyperedge(phg, sharedData, e);
      } else {
        if constexpr ( PartitionedHypergraph::is_graph ) {
          recalculateGainForGraphEdgeViaAttributedGains(phg, sharedData, e);
        } else {
          recalculateGainForHyperedgeViaAttributedGains(phg, sharedData, e);
        }
      }
    };

    tbb::parallel_for(MoveID(0), tracker.numPerformedMoves(), [&](MoveID m_id) {
      tracker.moveOrder[m_id].gain = 0;
    });

    if (context.refinement.fm.iter_moves_on_recalc) {
      tbb::parallel_for(0U, sharedData.moveTracker.numPerformedMoves(), [&](const MoveID local_move_id) {
        const HypernodeID u = sharedData.moveTracker.moveOrder[local_move_id].node;
        if (tracker.wasNodeMovedInThisRound(u)) {
          for (HyperedgeID e : phg.incidentEdges(u)) {
            // test-and-set whether this is the first time this hyperedge is encountered
            uint32_t expected = last_recalc_round[phg.uniqueEdgeID(e)].load(std::memory_order_relaxed);
            if (expected < round && last_recalc_round[phg.uniqueEdgeID(e)].exchange(round, std::memory_order_acquire) == expected) {
              recalculate_and_distribute_for_hyperedge(e);
            }
          }
        }
      });

      // reset bits
      if (++round == std::numeric_limits<uint32_t>::max()) {
        // should never happen on practical inputs.
        last_recalc_round.assign(phg.initialNumEdges(), CAtomic<uint32_t>(0));
      }
    } else{
      tbb::parallel_for(ID(0), phg.initialNumEdges(), recalculate_and_distribute_for_hyperedge);
    }
  }

  template<typename GraphAndGainTypes>
  HyperedgeWeight GlobalRollback<GraphAndGainTypes>::revertToBestPrefixSequential(
    PartitionedHypergraph& phg,
    FMSharedData& sharedData,
    const vec<HypernodeWeight>&,
    const std::vector<HypernodeWeight>& maxPartWeights) {

    GlobalMoveTracker& tracker = sharedData.moveTracker;
    const MoveID numMoves = tracker.numPerformedMoves();
    const vec<Move>& move_order = tracker.moveOrder;

    // revert all moves
    tbb::parallel_for(0U, numMoves, [&](const MoveID localMoveID) {
      const Move& m = move_order[localMoveID];
      if (m.isValid()) {
        moveVertex(phg, m.node, m.to, m.from);
      }
    });

    size_t overloaded = 0;
    for (PartitionID i = 0; i < context.partition.k; ++i) {
      if (phg.partWeight(i) > maxPartWeights[i]) {
        overloaded++;
      }
    }

    // roll forward sequentially
    Gain best_gain = 0, gain_sum = 0;
    MoveID best_index = 0;
    auto attributed_gains = [&](const SynchronizedEdgeUpdate& sync_update) {
      gain_sum -= AttributedGains::gain(sync_update);
    };
    for (MoveID localMoveID = 0; localMoveID < numMoves; ++localMoveID) {
      const Move& m = move_order[localMoveID];
      if (!m.isValid()) continue;

      const bool from_overloaded = phg.partWeight(m.from) > maxPartWeights[m.from];
      const bool to_overloaded = phg.partWeight(m.to) > maxPartWeights[m.to];
      phg.changeNodePart(gain_cache, m.node, m.from, m.to,
        std::numeric_limits<HypernodeWeight>::max(), []{ }, attributed_gains);
      if (from_overloaded && phg.partWeight(m.from) <= maxPartWeights[m.from]) {
        overloaded--;
      }
      if (!to_overloaded && phg.partWeight(m.to) > maxPartWeights[m.to]) {
        overloaded++;
      }

      if (overloaded == 0 && gain_sum > best_gain) {
        best_index = localMoveID + 1;
        best_gain = gain_sum;
      }
    }

    // revert rejected moves again
    tbb::parallel_for(best_index, numMoves, [&](const MoveID i) {
      const Move& m = move_order[i];
      if (m.isValid()) {
        moveVertex(phg, m.node, m.to, m.from);
      }
    });

    if constexpr (GainCache::invalidates_entries) {
      tbb::parallel_for(0U, numMoves, [&](const MoveID i) {
        gain_cache.recomputeInvalidTerms(phg, move_order[i].node);
      });
    }

    tracker.reset();

    return best_gain;
  }


  template<typename GraphAndGainTypes>
  bool GlobalRollback<GraphAndGainTypes>::verifyGains(PartitionedHypergraph& phg, FMSharedData& sharedData) {
    vec<Move>& move_order = sharedData.moveTracker.moveOrder;

    auto recompute_penalty_terms = [&] {
      for (MoveID localMoveID = 0; localMoveID < sharedData.moveTracker.numPerformedMoves(); ++localMoveID) {
        gain_cache.recomputeInvalidTerms(phg, move_order[localMoveID].node);
      }
    };

    recompute_penalty_terms();
    phg.checkTrackedPartitionInformation(gain_cache);

    // revert all moves
    for (MoveID localMoveID = 0; localMoveID < sharedData.moveTracker.numPerformedMoves(); ++localMoveID) {
      const Move& m = sharedData.moveTracker.moveOrder[localMoveID];
      if (m.isValid()) {
        moveVertex(phg, m.node, m.to, m.from);
      }
    }

    recompute_penalty_terms();

    // roll forward sequentially and check gains
    for (MoveID localMoveID = 0; localMoveID < sharedData.moveTracker.numPerformedMoves(); ++localMoveID) {
      const Move& m = sharedData.moveTracker.moveOrder[localMoveID];
      if (!m.isValid())
        continue;

      Gain gain = 0;
      auto attributed_gains = [&](const SynchronizedEdgeUpdate& sync_update) {
        gain -= AttributedGains::gain(sync_update);
      };

      ASSERT(gain_cache.penaltyTerm(m.node, phg.partID(m.node)) == gain_cache.recomputePenaltyTerm(phg, m.node));
      ASSERT(gain_cache.benefitTerm(m.node, m.to) == gain_cache.recomputeBenefitTerm(phg, m.node, m.to));
      const Gain gain_in_cache = gain_cache.gain(m.node, m.from, m.to);
      unused(gain_in_cache);

      // const HyperedgeWeight objective_before_move =
      //   metrics::quality(phg, context, false);
      phg.changeNodePart(gain_cache, m.node, m.from, m.to,
        std::numeric_limits<HypernodeWeight>::max(), []{ }, attributed_gains);
      // const HyperedgeWeight objective_after_move =
      //   metrics::quality(phg, context, false);

      // ASSERT(objective_after_move + gain == objective_before_move,
      //   V(gain) << V(m.gain) << V(objective_after_move) << V(objective_before_move));
      // ASSERT(objective_after_move + m.gain == objective_before_move,
      //   V(gain) << V(m.gain) << V(objective_after_move) << V(objective_before_move));
      ASSERT(gain == gain_in_cache);
      ASSERT(gain == m.gain, V(gain) << V(m.gain));
      unused(gain); // unused(objective_before_move); unused(objective_after_move);  // for release mode
    }

    recompute_penalty_terms();
    return true;
  }

  namespace {
  #define GLOBAL_ROLLBACK(X) GlobalRollback<X>
  }

  INSTANTIATE_CLASS_WITH_VALID_TRAITS(GLOBAL_ROLLBACK)
}
