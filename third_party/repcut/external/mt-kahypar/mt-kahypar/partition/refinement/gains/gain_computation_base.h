/*******************************************************************************
 * MIT License
 *
 * This file is part of Mt-KaHyPar.
 *
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

#pragma once

#include <vector>

#include "kahypar-resources/meta/mandatory.h"

#include <tbb/enumerable_thread_specific.h>

#include "mt-kahypar/datastructures/synchronized_edge_update.h"
#include "mt-kahypar/partition/metrics.h"
#include "mt-kahypar/partition/context.h"
#include "mt-kahypar/utils/randomize.h"
#include "mt-kahypar/datastructures/sparse_map.h"

namespace mt_kahypar {

template <class Derived = Mandatory,
          class AttributedGains = Mandatory>
class GainComputationBase {
  using DeltaGain = tbb::enumerable_thread_specific<Gain>;

 public:
  using RatingMap = ds::SparseMap<PartitionID, Gain>;
  using TmpScores = tbb::enumerable_thread_specific<RatingMap>;
  using Penalty = tbb::enumerable_thread_specific<Gain>;

  GainComputationBase(const Context& context,
                      const bool disable_randomization) :
    _context(context),
    _disable_randomization(disable_randomization),
    _deltas(0),
    _tmp_scores([&] {
      return constructLocalTmpScores();
    }),
    _isolated_block_gain(0) { }

  template<typename PartitionedHypergraph>
  Move computeMaxGainMove(const PartitionedHypergraph& phg,
                          const HypernodeID hn,
                          const bool rebalance = false,
                          const bool consider_non_adjacent_blocks = false,
                          const bool allow_imbalance = false) {
    Derived* derived = static_cast<Derived*>(this);
    RatingMap& tmp_scores = _tmp_scores.local();
    Gain& isolated_block_gain = _isolated_block_gain.local();
    derived->precomputeGains(phg, hn, tmp_scores, isolated_block_gain, consider_non_adjacent_blocks);
    Move best_move = computeMaxGainMoveForScores(phg, tmp_scores, isolated_block_gain, hn,
                        rebalance, consider_non_adjacent_blocks, allow_imbalance);

    isolated_block_gain = 0;
    tmp_scores.clear();
    return best_move;
  }

  template<typename PartitionedHypergraph>
  Move computeMaxGainMoveForScores(const PartitionedHypergraph& phg,
                                   const RatingMap& tmp_scores,
                                   const Gain isolated_block_gain,
                                   const HypernodeID hn,
                                   const bool rebalance = false,
                                   const bool consider_non_adjacent_blocks = false,
                                   const bool allow_imbalance = false) {
    Derived* derived = static_cast<Derived*>(this);

    PartitionID from = phg.partID(hn);
    Move best_move { from, from, hn, rebalance ? std::numeric_limits<Gain>::max() : 0 };
    HypernodeWeight hn_weight = phg.nodeWeight(hn);
    int cpu_id = THREAD_ID;
    utils::Randomize& rand = utils::Randomize::instance();
    auto test_and_apply = [&](const PartitionID to,
                              const Gain score,
                              const bool no_tie_breaking = false) {
      bool new_best_gain = (score < best_move.gain) ||
                            (score == best_move.gain &&
                            !_disable_randomization &&
                            (no_tie_breaking || rand.flipCoin(cpu_id)));
      if (new_best_gain && (allow_imbalance || phg.partWeight(to) + hn_weight <=
          _context.partition.max_part_weights[to])) {
        best_move.to = to;
        best_move.gain = score;
        return true;
      } else {
        return false;
      }
    };

    for ( const auto& entry : tmp_scores ) {
      const PartitionID to = entry.key;
      if (from != to) {
        const Gain score = derived->gain(entry.value, isolated_block_gain);
        test_and_apply(to, score);
      }
    }

    if ( consider_non_adjacent_blocks && best_move.to == from ) {
      // This is important for our rebalancer as the last fallback strategy
      vec<PartitionID> non_adjacent_block;
      for ( PartitionID to = 0; to < _context.partition.k; ++to ) {
        if ( from != to && !tmp_scores.contains(to) ) {
          // This block is not adjacent to the current node
          if ( test_and_apply(to, isolated_block_gain, true /* no tie breaking */ ) ) {
            non_adjacent_block.push_back(to);
          }
        }
      }

      if ( non_adjacent_block.size() > 0 ) {
        // Choose one at random
        const PartitionID to = non_adjacent_block[
          rand.getRandomInt(0, static_cast<int>(non_adjacent_block.size() - 1), cpu_id)];
        best_move.to = to;
        best_move.gain = isolated_block_gain;
      }
    }

    return best_move;
  }

  inline void computeDeltaForHyperedge(const SynchronizedEdgeUpdate& sync_update) {
    _deltas.local() += AttributedGains::gain(sync_update);
  }

  // ! Returns the local rating map for block scores
  RatingMap& localScores() {
    return _tmp_scores.local();
  }

  // ! Returns the delta in the objective function for all moves
  // ! performed by the calling thread relative to the last call
  // ! reset()
  Gain localDelta() {
    return _deltas.local();
  }

  // ! Returns the overall delta of all moves performed by
  // ! all threads relative to the last call of reset()
  Gain delta() const {
    Gain overall_delta = 0;
    for (const Gain& delta : _deltas) {
      overall_delta += delta;
    }
    return overall_delta;
  }

  void reset() {
    for (Gain& delta : _deltas) {
      delta = 0;
    }
  }

  void changeNumberOfBlocks(const PartitionID new_k) {
    ASSERT(new_k == _context.partition.k);
    for ( auto& tmp_score : _tmp_scores ) {
      if ( static_cast<size_t>(new_k) > tmp_score.size() ) {
        tmp_score = RatingMap(new_k);
      }
    }
    static_cast<Derived*>(this)->changeNumberOfBlocksImpl(new_k);
  }

private:
  RatingMap constructLocalTmpScores() const {
    return RatingMap(_context.partition.k);
  }

 protected:
  const Context& _context;
  const bool _disable_randomization;
  DeltaGain _deltas;
  TmpScores _tmp_scores;
  Penalty _isolated_block_gain;
};

}  // namespace mt_kahypar
