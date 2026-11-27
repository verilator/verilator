/*******************************************************************************
 * MIT License
 *
 * This file is part of KaHyPar.
 *
 * Copyright (C) 2023 Robert Krause <robert.krause@student.kit.edu>
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

#include <tbb/parallel_for.h>

#include "mt-kahypar/macros.h"
#include "mt-kahypar/parallel/stl/scalable_vector.h"
#include "mt-kahypar/partition/metrics.h"
#include "mt-kahypar/partition/refinement/flows/flow_common.h"
#include "mt-kahypar/partition/refinement/flows/quotient_graph.h"

namespace mt_kahypar {

/**
 * Implements the participation scheduling strategy.
 * The participation block scheduling strategy proceeds in rounds. In each round,
 * all active edges of the quotient graph are scheduled for refinement as a series
 * of matchings. Each matching is determined greedily, where the first criterion is
 * to select a node with maximum participation (i.e., the degree restricted to active
 * edges). Then, the edge with highest previous improvement is selected. Matchings
 * are processed one by one, so that scheduled edges can't interfere with other edges.
 *
 * A edge is called active, if at least one of the blocks is active and a block
 * is called active if a refinement involving that block in the previous round
 * lead to an improvement.
 */
class ParticipationScheduler final {
  static constexpr bool debug = false;

  ParticipationScheduler(const ParticipationScheduler&) = delete;
  ParticipationScheduler(ParticipationScheduler&&) = delete;
  ParticipationScheduler& operator= (const ParticipationScheduler&) = delete;
  ParticipationScheduler& operator= (ParticipationScheduler&&) = delete;

 public:
  explicit ParticipationScheduler(const Context& context, QuotientGraph& quotient_graph);

  void initialize(bool is_input_hypergraph);

  void resetForNewRound();

  size_t getNextMatching(tbb::concurrent_queue<BlockPair>& tasks);

  void reportResults(const BlockPair& blocks, HyperedgeWeight improvement) {
    if (improvement > 0) {
      _active_blocks_next_round[blocks.i] = true;
      _active_blocks_next_round[blocks.j] = true;
    }
  }

 private:
  void resetForNewRoundImpl();

  bool isEligible(const BlockPair& blocks);

  const Context& _context;
  // ! Quotient graph
  QuotientGraph& _quotient_graph;
  // ! Tracked data for the different blocks
  vec<bool> _active_blocks;
  vec<bool> _active_blocks_next_round;
  vec<vec<bool>> _already_processed;
  vec<size_t> _participations;
  vec<vec<PartitionID>> _active_block_pairs;
  // ! If the current hypergraph represents the input hypergraph
  bool _is_input_hypergraph;
  size_t _round;
};

}  // namespace mt_kahypar
