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

#include <tbb/concurrent_queue.h>
#include <tbb/concurrent_vector.h>

#include "mt-kahypar/partition/context.h"
#include "mt-kahypar/partition/refinement/flows/quotient_graph.h"
#include "mt-kahypar/parallel/atomic_wrapper.h"

namespace mt_kahypar {

static constexpr bool debug = false;
static constexpr bool enable_heavy_assert = false;

/**
 * Maintains the block pair of a round of the active block scheduling strategy
 */
class ActiveBlockSchedulingRound {
 public:
  explicit ActiveBlockSchedulingRound(const Context& context, QuotientGraph& quotient_graph);

  // ! Pops a block pair from the queue.
  // ! Returns true, if a block pair was successfully popped from the queue.
  // ! The corresponding block pair will be stored in blocks.
  bool popBlockPairFromQueue(BlockPair& blocks);

  // ! Pushes a block pair into the queue.
  // ! Return true, if the block pair was successfully pushed into the queue.
  // ! Note, that a block pair is only allowed to be contained in one queue
  // ! (there are multiple active rounds).
  bool pushBlockPairIntoQueue(const BlockPair& blocks);

  // ! Signals that the search on the corresponding block pair terminated.
  void finalizeSearch(const BlockPair& blocks,
                      const HyperedgeWeight improvement,
                      bool& block_0_becomes_active,
                      bool& block_1_becomes_active);

  HyperedgeWeight roundImprovement() const {
    return _round_improvement.load(std::memory_order_relaxed);
  }

  bool isActive(const PartitionID block) const {
    ASSERT(block < _context.partition.k);
    return _active_blocks[block];
  }

  size_t numRemainingBlocks() const {
    return _remaining_blocks;
  }

  void decrementRemainingBlocks() {
    --_remaining_blocks;
  }

  const Context& _context;
  // ! Quotient graph
  QuotientGraph& _quotient_graph;
  // ! Queue that contains all unscheduled block pairs of the current round
  tbb::concurrent_queue<BlockPair> _unscheduled_blocks;
  // ! Current improvement made in this round
  CAtomic<HyperedgeWeight> _round_improvement;
  // Active blocks for next round
  SpinLock _active_blocks_lock;
  vec<uint8_t> _active_blocks;
  // Remaining active block pairs in the current round.
  CAtomic<size_t> _remaining_blocks;
};

/**
 * Implements the active block scheduling strategy.
 * The active block scheduling strategy proceeds in rounds. In each round,
 * all active edges of the quotient graph are scheduled for refinement.
 * An edge is called active if at least one of the blocks is active. A block
 * is called active if a refinement involving that block in the previous round
 * leads to an improvement. In a sequential scheduling strategy the rounds act
 * as synchronization barriers. However, to achieve better scalibility we
 * immediatly schedule an edge in the next round once we find an improvement.
 * Thus, there can be multiple active searches that process block pairs from
 * different rounds. However, block pairs from earlier rounds have a higher
 * priority to be scheduled.
 */
class ActiveBlockScheduler {
 public:
  explicit ActiveBlockScheduler(const Context& context,
                                QuotientGraph& quotient_graph);

  ActiveBlockScheduler(const ActiveBlockScheduler&) = delete;
  ActiveBlockScheduler(ActiveBlockScheduler&&) = delete;
  ActiveBlockScheduler & operator= (const ActiveBlockScheduler &) = delete;
  ActiveBlockScheduler & operator= (ActiveBlockScheduler &&) = delete;

  // ! Initialize the first round of the active block scheduling strategy
  void initialize(const bool is_input_hypergraph);

  // ! Pops a block pair from the queue.
  // ! Returns true, if a block pair was successfully popped from the queue.
  // ! The corresponding block pair and the round to which this blocks corresponds
  // ! to are stored in blocks and round.
  bool popBlockPairFromQueue(BlockPair& blocks, size_t& round);

  // ! Signals that the search on the corresponding block pair terminated.
  // ! If one the two blocks become active, we immediatly schedule all edges
  // ! adjacent in the quotient graph in the next round of active block scheduling
  void finalizeSearch(const BlockPair& blocks,
                      const size_t round,
                      const HyperedgeWeight improvement);

  // ! Remaining blocks to be scheduled. Note, if there is a race condition with
  // ! popBlockPairFromQueue, the returned value might be too large by 1.
  size_t numRemainingBlocks() const;

  void setObjective(const HyperedgeWeight objective);

 private:
  void reset();

  bool isActiveBlockPair(const BlockPair& blocks) const;

  const Context& _context;
  // ! Quotient graph
  QuotientGraph& _quotient_graph;
  // Contains all active block scheduling rounds
  CAtomic<size_t> _num_rounds;
  tbb::concurrent_vector<ActiveBlockSchedulingRound> _rounds;
  // ! Minimum improvement per round to continue with next round
  HyperedgeWeight _min_improvement_per_round;
  // ! If true, then search is immediatly terminated
  bool _terminate;
  // ! First Active Round
  SpinLock _round_lock;
  size_t _first_active_round;
  // ! Indicate if the current hypergraph represents the input hypergraph
  bool _is_input_hypergraph;
};

}  // namespace kahypar
