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

#pragma once

#include <tbb/enumerable_thread_specific.h>

#include "mt-kahypar/parallel/atomic_wrapper.h"
#include "mt-kahypar/partition/context.h"
#include "mt-kahypar/partition/refinement/gains/gain_cache_ptr.h"
#include "mt-kahypar/utils/cast.h"

namespace mt_kahypar {

template <typename GraphAndGainTypes>
class RepairEmptyBlocks {
private:
  using PartitionedHypergraph = typename GraphAndGainTypes::PartitionedHypergraph;
  using GainCache = typename GraphAndGainTypes::GainCache;
  using GainComputation = typename GraphAndGainTypes::GainComputation;
  using RatingMap = typename GainComputation::RatingMap;
  using AttributedGains = typename GraphAndGainTypes::AttributedGains;

  static constexpr bool debug = false;
  static constexpr bool enable_heavy_assert = false;

  static constexpr size_t MAX_ROUNDS = 3;

 public:
  explicit RepairEmptyBlocks(const Context& context, GainCache& gain_cache);

  // ! Repairs empty blocks of the partition with a fully deterministic algorithm.
  // ! Receives a lambda to actually apply the provided moves.
  template<typename Func>
  void repairEmptyBlocks(mt_kahypar_partitioned_hypergraph_t& hypergraph,
                         GainComputation& gain_computation,
                         Func&& apply_move_fn) {
    if (_context.partition.allow_empty_blocks) return;

    auto& phg = utils::cast<PartitionedHypergraph>(hypergraph);

    for (size_t i = 0; i < MAX_ROUNDS; ++i) {
      computeEmptyParts(phg);
      if (_empty_parts.empty()) break;

      DBG << "Start repair move computation:" << V(_empty_parts.size());
      if constexpr (GainComputation::is_independent_of_block) {
        computeBestMovesBlockIndependent(phg);
      } else {
        computeBestMovesIndividualBlockGains(phg, gain_computation);
      }

      for (size_t j = 0; j < _global_best_move_for_part.size(); ++j) {
        const Move& m = _global_best_move_for_part[j];
        if (m.isValid()) {
          ASSERT(m.from == phg.partID(m.node) && m.to == _empty_parts[j]);
          DBG << "Apply repair move:" << V(m.node) << V(m.gain) << V(m.from) << V(m.to);
          apply_move_fn(m);
        }
      }
    }
  }

 private:
  void computeEmptyParts(PartitionedHypergraph& phg);

  void computeBestMovesBlockIndependent(PartitionedHypergraph& phg);

  void computeBestMovesIndividualBlockGains(PartitionedHypergraph& phg, GainComputation& gain_computation);

  const Context& _context;
  GainCache& _gain_cache;
  vec<bool> _is_empty;
  vec<PartitionID> _empty_parts;
  vec<Move> _global_best_move_for_part;
  tbb::enumerable_thread_specific<vec<Move>> _local_best_move_for_part;
  std::mt19937 _prng;
};

}  // namespace mt_kahypar
