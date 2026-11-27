/*******************************************************************************
 * MIT License
 *
 * This file is part of Mt-KaHyPar.
 *
 * Copyright (C) 2025 Nikolai Maas <nikolai.maas@kit.edu>
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

#include "mt-kahypar/partition/refinement/rebalancing/repair_empty_blocks.h"

#include <algorithm>

#include "mt-kahypar/partition/refinement/gains/gain_definitions.h"
#include "mt-kahypar/utils/cast.h"
#include "mt-kahypar/utils/hash.h"

namespace mt_kahypar {

bool moveIsBetter(const Move& lhs, const Move& rhs) {
  ASSERT(lhs.isValid());
  // tie breaking by ID for determinism
  return !rhs.isValid() ||
         lhs.gain < rhs.gain ||
         (lhs.gain == rhs.gain && lhs.node < rhs.node);
}

template <typename GraphAndGainTypes>
RepairEmptyBlocks<GraphAndGainTypes>::RepairEmptyBlocks(const Context& context, GainCache& gain_cache):
  _context(context),
  _gain_cache(gain_cache),
  _is_empty(),
  _empty_parts(),
  _global_best_move_for_part(),
  _local_best_move_for_part(),
  _prng(context.partition.seed) { }

template <typename GraphAndGainTypes>
void RepairEmptyBlocks<GraphAndGainTypes>::computeEmptyParts(PartitionedHypergraph& phg) {
  _is_empty.assign(_context.partition.k, false);
  _empty_parts.clear();
  for (PartitionID block = 0; block < _context.partition.k; ++block) {
    if (phg.partWeight(block) == 0) {
      _is_empty[block] = true;
      _empty_parts.push_back(block);
    }
  }

  const auto& max_weights = _context.partition.max_part_weights;
  if (!_empty_parts.empty() && _context.partition.use_individual_part_weights) {
    // We sort the empty parts, so that
    // (1) we can determine which parts to skip for degree zero nodes
    // (2) computeBestMovesBlockIndependent can maintain the invariant that the last entry
    // of best_move_for_part is the worst move in the list. This invariant could be broken
    // if a node does not fit in a block (unlikely, but possible) and therefore "skips"
    // a part of the list. However, by sorting descending by part weight, this can't happen
    // since a move at position i + 1 is guaranteed to also fit in position i, and thus
    // can not be better than the move at position i (or it would be placed there).
    std::sort(_empty_parts.begin(), _empty_parts.end(), [&](PartitionID lhs, PartitionID rhs) {
      // deterministic tie breaking
      return max_weights[lhs] > max_weights[rhs] || (max_weights[lhs] == max_weights[rhs] && lhs < rhs);
    });
  }

  if (!_empty_parts.empty() && phg.numRemovedHypernodes() > 0) {
    // since some of the blocks can be filled by degree zero nodes at the end, we can throw
    // out all blocks that can be filled in this way
    HypernodeWeight max_removed_weight = phg.maxWeightOfRemovedDegreeZeroNode();
    size_t last_fitting = 0;
    while (last_fitting < _empty_parts.size()
           && max_removed_weight <= max_weights[_empty_parts[last_fitting]]) {
      ++last_fitting;
    }
    size_t start = (phg.numRemovedHypernodes() >= last_fitting) ? 0 : last_fitting - phg.numRemovedHypernodes();
    _empty_parts.erase(_empty_parts.begin() + start, _empty_parts.begin() + last_fitting);
  }
}

template <typename GraphAndGainTypes>
void RepairEmptyBlocks<GraphAndGainTypes>::computeBestMovesBlockIndependent(PartitionedHypergraph& phg) {
  ALWAYS_ASSERT(GainComputation::is_independent_of_block);
  if constexpr (GainComputation::is_independent_of_block) {  // needed to access GainComputation::computeIsolatedBlockGain
    const bool gain_cache_initialized = _gain_cache.isInitialized();

    tbb::enumerable_thread_specific<vec<Move>> local_best_move_for_part(_empty_parts.size(), Move{});
    _global_best_move_for_part.clear();
    _global_best_move_for_part.resize(_empty_parts.size(), Move{});

    auto insert_move_into_list = [&](Move& current_move, vec<Move>& move_for_part) {
      const Move& worst_move = move_for_part.back();
      if (moveIsBetter(current_move, worst_move)) {
        // update moves for all parts by "shifting" them
        for (size_t i = 0; current_move.isValid() && i < _empty_parts.size(); ++i) {
          const PartitionID to = _empty_parts[i];
          if (moveIsBetter(current_move, move_for_part[i])
              && phg.nodeWeight(current_move.node) <= _context.partition.max_part_weights[to]) {
            current_move.to = to;
            std::swap(current_move, move_for_part[i]);
          }
        }
      }
    };

    // find best available moves in parallel, accumulate locally
    phg.doParallelForAllNodes([&](const HypernodeID hn) {
      const PartitionID from = phg.partID(hn);

      // skip weight zero nodes and if it is the only node in the block
      const HypernodeWeight hn_weight = phg.nodeWeight(hn);
      if (hn_weight == 0 || hn_weight == phg.partWeight(from)) return;

      // In case of independent blocks, we only need to compute the isolated block gain,
      // which is equal to the gain for any empty target block.
      Gain isolated_block_gain = gain_cache_initialized ?
        _gain_cache.penaltyTerm(hn, from) : GainComputation::computeIsolatedBlockGain(phg, hn);
      ASSERT(!gain_cache_initialized || _gain_cache.penaltyTerm(hn, from) == GainComputation::computeIsolatedBlockGain(phg, hn));

      Move current_move{from, _empty_parts[0], hn, isolated_block_gain};
      insert_move_into_list(current_move, local_best_move_for_part.local());
    });

    // sort the moves into the global array
    for (auto& best_move_for_part: local_best_move_for_part) {
      for (Move& m: best_move_for_part) {
        if (m.isValid()) {
          insert_move_into_list(m, _global_best_move_for_part);
        }
      }
    }
  }
}

template <typename GraphAndGainTypes>
void RepairEmptyBlocks<GraphAndGainTypes>::computeBestMovesIndividualBlockGains(PartitionedHypergraph& phg,
                                                                                GainComputation& gain_computation) {
  ALWAYS_ASSERT(!GainComputation::is_independent_of_block);

  // If the gain depends on the target block, an equivalent of the "independent"
  // algorithm would involve a lot of gain recomputations. Instead, we hash each
  // node to a random target block and for each block choose the best option out
  // of those nodes.
  tbb::enumerable_thread_specific<vec<Move>> local_best_move_for_part(_empty_parts.size(), Move{});
  _global_best_move_for_part.assign(_empty_parts.size(), Move{});
  const uint32_t rand = std::uniform_int_distribution<uint32_t>(0, 1000)(_prng);
  const uint32_t seed_offset = rand * phg.initialNumNodes();

  // find best available moves in parallel, accumulate locally
  phg.doParallelForAllNodes([&](const HypernodeID hn) {
    const PartitionID from = phg.partID(hn);
    const HypernodeWeight hn_weight = phg.nodeWeight(hn);

    // skip weight zero nodes and if it is the only node in the block
    if (hn_weight == 0 || hn_weight == phg.partWeight(from)) return;

    // deterministically determine a target block for each node by hashing it
    hashing::SimpleIntHash<uint32_t> sih;
    hashing::HashRNG<hashing::SimpleIntHash<uint32_t>> hash_prng(sih, seed_offset + hn);
    const size_t part_idx =
      std::uniform_int_distribution<uint32_t>(0, _empty_parts.size() - 1)(hash_prng);
    const PartitionID to = _empty_parts[part_idx];

    // compute the gain for the target block
    Gain gain;
    if (_gain_cache.isInitialized()) {
      gain = _gain_cache.penaltyTerm(hn, to) - (_gain_cache.blockIsAdjacent(hn, to) ?
              _gain_cache.benefitTerm(hn, to) : _gain_cache.recomputeBenefitTerm(phg, hn, to));
      HEAVY_REFINEMENT_ASSERT([&]{
        RatingMap& tmp_scores = gain_computation.localScores();
        Gain isolated_block_gain = 0;
        gain_computation.precomputeGains(phg, hn, tmp_scores, isolated_block_gain, true);
        Gain tmp_gain = gain_computation.gain(tmp_scores[to], isolated_block_gain);
        tmp_scores.clear();
        return gain == tmp_gain;
      }());
    } else {
      RatingMap& tmp_scores = gain_computation.localScores();
      Gain isolated_block_gain = 0;
      gain_computation.precomputeGains(phg, hn, tmp_scores, isolated_block_gain, true);
      gain = gain_computation.gain(tmp_scores[to], isolated_block_gain);
      tmp_scores.clear();
    }

    // insert move
    auto& best_move_for_part = local_best_move_for_part.local();
    Move current_move{from, to, hn, gain};
    if (moveIsBetter(current_move, best_move_for_part[part_idx])
        && hn_weight <= _context.partition.max_part_weights[to]) {
      best_move_for_part[part_idx] = current_move;
    }
  });

  // insert the moves into the global array
  for (auto& best_move_for_part: local_best_move_for_part) {
    for (size_t i = 0; i < best_move_for_part.size(); ++i) {
      const Move& m = best_move_for_part[i];
      if (m.isValid() && moveIsBetter(m, _global_best_move_for_part[i])) {
        _global_best_move_for_part[i] = m;
      }
    }
  }
}

// explicitly instantiate so the compiler can generate them when compiling this cpp file
namespace {
  #define REPAIR_EMPTY_BLOCKS(X) RepairEmptyBlocks<X>
}

INSTANTIATE_CLASS_WITH_VALID_TRAITS(REPAIR_EMPTY_BLOCKS)

}  // namespace mt_kahypar
