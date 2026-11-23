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


#include "mt-kahypar/partition/refinement/flows/active_block_scheduler.h"

#include "mt-kahypar/definitions.h"


namespace mt_kahypar {

ActiveBlockSchedulingRound::ActiveBlockSchedulingRound(const Context& context,
                                                       QuotientGraph& quotient_graph) :
  _context(context),
  _quotient_graph(quotient_graph),
  _unscheduled_blocks(),
  _round_improvement(0),
  _active_blocks_lock(),
  _active_blocks(context.partition.k, false),
  _remaining_blocks(0) { }

bool ActiveBlockSchedulingRound::popBlockPairFromQueue(BlockPair& blocks) {
  blocks.i = kInvalidPartition;
  blocks.j = kInvalidPartition;
  if ( _unscheduled_blocks.try_pop(blocks) ) {
    _quotient_graph.edge(blocks).markAsNotInQueue();
  }
  return blocks.i != kInvalidPartition && blocks.j != kInvalidPartition;
}

void ActiveBlockSchedulingRound::finalizeSearch(const BlockPair& blocks,
                                                const HyperedgeWeight improvement,
                                                bool& block_0_becomes_active,
                                                bool& block_1_becomes_active) {
  _round_improvement += improvement;
  if ( improvement > 0 ) {
    _active_blocks_lock.lock();
    block_0_becomes_active = !_active_blocks[blocks.i];
    block_1_becomes_active = !_active_blocks[blocks.j];
    _active_blocks[blocks.i] = true;
    _active_blocks[blocks.j] = true;
    _active_blocks_lock.unlock();
  }
}

bool ActiveBlockSchedulingRound::pushBlockPairIntoQueue(const BlockPair& blocks) {
  QuotientGraphEdge& qg_edge = _quotient_graph.edge(blocks);
  if ( qg_edge.markAsInQueue() ) {
    _unscheduled_blocks.push(blocks);
    ++_remaining_blocks;
    return true;
  } else {
    return false;
  }
}

ActiveBlockScheduler::ActiveBlockScheduler(const Context& context,
                                           QuotientGraph& quotient_graph) :
  _context(context),
  _quotient_graph(quotient_graph),
  _num_rounds(0),
  _rounds(),
  _min_improvement_per_round(0),
  _terminate(false),
  _round_lock(),
  _first_active_round(0),
  _is_input_hypergraph(false) { }

void ActiveBlockScheduler::initialize(const bool is_input_hypergraph) {
  reset();
  _is_input_hypergraph = is_input_hypergraph;

  HyperedgeWeight best_total_improvement = 1;
  for ( PartitionID i = 0; i < _context.partition.k; ++i ) {
    for ( PartitionID j = i + 1; j < _context.partition.k; ++j ) {
      const BlockPair blocks{ i, j };
      best_total_improvement = std::max(best_total_improvement,
        _quotient_graph.edge(blocks).totalImprovement());
    }
  }

  vec<BlockPair> active_block_pairs;
  for ( PartitionID i = 0; i < _context.partition.k; ++i ) {
    for ( PartitionID j = i + 1; j < _context.partition.k; ++j ) {
      const BlockPair blocks{ i, j };
      if ( isActiveBlockPair(blocks) ) {
        active_block_pairs.push_back(blocks);
      }
    }
  }

  if ( active_block_pairs.size() > 0 ) {
    std::sort(active_block_pairs.begin(), active_block_pairs.end(),
      [&](const BlockPair& lhs, const BlockPair& rhs) {
        const QuotientGraphEdge& l_edge = _quotient_graph.edge(lhs);
        const QuotientGraphEdge& r_edge = _quotient_graph.edge(rhs);
        return l_edge.totalImprovement() > r_edge.totalImprovement() ||
          ( l_edge.totalImprovement() == r_edge.totalImprovement() &&
            l_edge.weightOfCutHyperedges() > r_edge.weightOfCutHyperedges() );
      });
    _rounds.emplace_back(_context, _quotient_graph);
    ++_num_rounds;
    for ( const BlockPair& blocks : active_block_pairs ) {
      DBG << "Schedule blocks (" << blocks.i << "," << blocks.j << ") in round 1 ("
          << "Total Improvement =" << _quotient_graph.edge(blocks).totalImprovement() << ","
          << "Cut Weight =" << _quotient_graph.edge(blocks).weightOfCutHyperedges() << ")";
      _rounds.back().pushBlockPairIntoQueue(blocks);
    }
  }
}

bool ActiveBlockScheduler::popBlockPairFromQueue(BlockPair& blocks, size_t& round) {
  bool success = false;
  round = _first_active_round;
  while ( !_terminate && round < _num_rounds ) {
    success = _rounds[round].popBlockPairFromQueue(blocks);
    if ( success ) {
      break;
    }
    ++round;
  }

  if ( success && round == _num_rounds - 1 ) {
    _round_lock.lock();
    if ( round == _num_rounds - 1 ) {
      // There must always be a next round available such that we can
      // reschedule block pairs that become active.
      _rounds.emplace_back(_context, _quotient_graph);
      ++_num_rounds;
    }
    _round_lock.unlock();
  }

  return success;
}

void ActiveBlockScheduler::finalizeSearch(const BlockPair& blocks,
                                          const size_t round,
                                          const HyperedgeWeight improvement) {
  ASSERT(round < _rounds.size());
  bool block_0_becomes_active = false;
  bool block_1_becomes_active = false;
  _rounds[round].finalizeSearch(blocks, improvement,
    block_0_becomes_active, block_1_becomes_active);

  auto schedule_adjacent_blocks = [&](PartitionID block_id) {
    ASSERT(round + 1 < _rounds.size());
    for ( PartitionID other = 0; other < _context.partition.k; ++other ) {
      if ( block_id != other ) {
        const BlockPair new_blocks{ std::min(block_id, other), std::max(block_id, other) };
        if ( isActiveBlockPair(new_blocks) ) {
          DBG << "Schedule blocks (" << new_blocks.i << "," << new_blocks.j << ") in round" << (round + 2) << " ("
              << "Total Improvement =" << _quotient_graph.edge(new_blocks).totalImprovement() << ","
              << "Cut Weight =" << _quotient_graph.edge(new_blocks).weightOfCutHyperedges() << ")";
          _rounds[round + 1].pushBlockPairIntoQueue(new_blocks);
        }
      }
    }
  };

  // If one of the blocks becomes active, we push all adjacent blocks into the queue of the next round
  if ( block_0_becomes_active ) {
    schedule_adjacent_blocks(blocks.i);
  }
  if ( block_1_becomes_active ) {
    schedule_adjacent_blocks(blocks.j);
  }

  // Special case
  if ( improvement > 0 && !_quotient_graph.edge(blocks).isInQueue() && isActiveBlockPair(blocks) &&
       ( _rounds[round].isActive(blocks.i) || _rounds[round].isActive(blocks.j) ) ) {
        // The active block scheduling strategy works in multiple rounds and each contain a separate queue
        // to store active block pairs. A block pair is only allowed to be contained in one queue.
        // If a block becomes active, we schedule all quotient graph edges incident to the block in
        // the next round. However, there could be some edges that are already contained in a queue of
        // a previous round, which are then not scheduled in the next round. If this edge is scheduled and
        // leads to an improvement, we schedule it in the next round here.
        DBG << "Schedule blocks (" << blocks.i << "," << blocks.j << ") in round" << (round + 2) << " ("
            << "Total Improvement =" << _quotient_graph.edge(blocks).totalImprovement() << ","
            << "Cut Weight =" << _quotient_graph.edge(blocks).weightOfCutHyperedges() << ")";
        _rounds[round + 1].pushBlockPairIntoQueue(blocks);
  }

  // Note: decrementing the block count must happen after pushing new blocks,
  // otherwise the active block count is temporarily too small
  _rounds[round].decrementRemainingBlocks();
  if ( round == _first_active_round && _rounds[round].numRemainingBlocks() == 0 ) {
    _round_lock.lock();
    // We consider a round as finished, if the previous round is also finished and there
    // are no remaining blocks in the queue of that round.
    while ( _first_active_round < _rounds.size() &&
            _rounds[_first_active_round].numRemainingBlocks() == 0 ) {
      DBG << GREEN << "Round" << (_first_active_round + 1) << "terminates with improvement"
          << _rounds[_first_active_round].roundImprovement() << "("
          << "Minimum Required Improvement =" << _min_improvement_per_round << ")" << END;
      // We require that minimum improvement per round must be greater than a threshold,
      // otherwise we terminate early
      _terminate = _rounds[_first_active_round].roundImprovement() < _min_improvement_per_round;
      ++_first_active_round;
    }
    _round_lock.unlock();
  }
}

size_t ActiveBlockScheduler::numRemainingBlocks() const {
  size_t num_remaining_blocks = 0;
  for ( size_t i = _first_active_round; i < _num_rounds; ++i ) {
    num_remaining_blocks += _rounds[i].numRemainingBlocks();
  }
  return num_remaining_blocks;
}

void ActiveBlockScheduler::setObjective(const HyperedgeWeight objective) {
  _min_improvement_per_round =
    _context.refinement.flows.min_relative_improvement_per_round * objective;
}

void ActiveBlockScheduler::reset() {
  _num_rounds.store(0);
  _rounds.clear();
  _first_active_round = 0;
  _terminate = false;
}

bool ActiveBlockScheduler::isActiveBlockPair(const BlockPair& blocks) const {
  const bool skip_small_cuts = !_is_input_hypergraph &&
    _context.refinement.flows.skip_small_cuts;
  const int cut_he_threshold = skip_small_cuts ? 10 : 0;

  const bool contains_enough_cut_hes = _quotient_graph.edge(blocks).weightOfCutHyperedges() > cut_he_threshold;
  const bool is_promising_blocks_pair =
    !_context.refinement.flows.skip_unpromising_blocks ||
      ( _first_active_round == 0 || _quotient_graph.edge(blocks).numImprovementsFound() > 0 );
  return contains_enough_cut_hes && is_promising_blocks_pair;
}

} // namespace mt_kahypar
