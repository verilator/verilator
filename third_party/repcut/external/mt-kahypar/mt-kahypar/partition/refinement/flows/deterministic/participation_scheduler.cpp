/*******************************************************************************
 * MIT License
 *
 * This file is part of KaHyPar.
 *
 * Copyright (C) 2023 Robert Krause <robert.krause@student.kit.edu>
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

#include "mt-kahypar/partition/refinement/flows/deterministic/participation_scheduler.h"

namespace mt_kahypar {

ParticipationScheduler::ParticipationScheduler(const Context& context, QuotientGraph& quotient_graph) :
  _context(context),
  _quotient_graph(quotient_graph),
  _active_blocks(context.partition.k, true),
  _active_blocks_next_round(context.partition.k, false),
  _already_processed(context.partition.k, vec<bool>{}),
  _participations(context.partition.k, 0),
  _active_block_pairs(context.partition.k),
  _is_input_hypergraph(false),
  _round(0) {}

void ParticipationScheduler::initialize(bool is_input_hypergraph) {
  _is_input_hypergraph = is_input_hypergraph;
  _active_blocks_next_round.assign(_active_blocks_next_round.size(), true);
  _round = 0;
  resetForNewRoundImpl();
}

void ParticipationScheduler::resetForNewRound() {
  _round++;
  resetForNewRoundImpl();
}

void ParticipationScheduler::resetForNewRoundImpl() {
  std::swap(_active_blocks, _active_blocks_next_round);

  // reset data
  _active_blocks_next_round.assign(_active_blocks_next_round.size(), false);
  _participations.assign(_participations.size(), 0);
  for (auto& v : _already_processed) {
    v.assign(_context.partition.k, false);
  }
  for (auto& active_pairs : _active_block_pairs) {
    active_pairs.clear();
  }

  // determine active blocks
  for (PartitionID i = 0; i < _context.partition.k - 1; ++i) {
    for (PartitionID j = i + 1; j < _context.partition.k; ++j) {
      const BlockPair blocks{ i, j };
      if (isEligible(blocks)) {
        _participations[i]++;
        _participations[j]++;
        _active_block_pairs[i].push_back(j);
        _active_block_pairs[j].push_back(i);
      }
    }
  }

  // sort active edges of block by previous improvement, tie break with cut weight
  tbb::parallel_for(PartitionID(0), _context.partition.k, [&](const PartitionID i) {
    auto& active_pairs = _active_block_pairs[i];
    std::sort(active_pairs.begin(), active_pairs.end(), [&](const PartitionID& lhs, const PartitionID& rhs) {
      const auto& l_edge = _quotient_graph.edge(BlockPair{std::min(i, lhs), std::max(i, lhs)});
      const auto& r_edge = _quotient_graph.edge(BlockPair{std::min(i, rhs), std::max(i, rhs)});
      const HyperedgeWeight lImprove = l_edge.totalImprovement();
      const HyperedgeWeight rImprove = r_edge.totalImprovement();
      const HyperedgeWeight lCut = l_edge.weightOfCutHyperedges();
      const HyperedgeWeight rCut = r_edge.weightOfCutHyperedges();

      return std::tie(lImprove, lCut, lhs) > std::tie(rImprove, rCut, rhs);
    });
  });
}

size_t ParticipationScheduler::getNextMatching(tbb::concurrent_queue<BlockPair>& tasks) {
  ASSERT(tasks.empty());

  // initialize sorted blocks
  vec<PartitionID> sorted_blocks;
  sorted_blocks.reserve(_context.partition.k);
  for (PartitionID i = 0; i < _context.partition.k; ++i) {
    if (_participations[i] > 0) {
      sorted_blocks.push_back(i);
    }
  }
  std::sort(sorted_blocks.begin(), sorted_blocks.end(), [&](const PartitionID lhs, const PartitionID rhs) {
    return _participations[lhs] > _participations[rhs]
      || (_participations[lhs] == _participations[rhs] && lhs < rhs);
  });

  // compute greedy matching
  if (sorted_blocks.size() > 0) {
    std::vector<bool> scheduled(_context.partition.k, false);
    for (size_t i = 0; i < sorted_blocks.size(); ++i) {
      const PartitionID block0 = sorted_blocks[i];
      ASSERT(block0 < _context.partition.k);
      if (scheduled[block0]) continue;

      for (PartitionID block1 : _active_block_pairs[block0]) {
        if (scheduled[block1]) continue;

        const BlockPair blocks{std::min(block0, block1), std::max(block0, block1)};
        if (isEligible(blocks) && !_already_processed[blocks.i][blocks.j]) {
          scheduled[block0] = true;
          scheduled[block1] = true;
          _participations[blocks.i]--;
          _participations[blocks.j]--;
          _already_processed[blocks.i][blocks.j] = true;
          tasks.push(blocks);
          break;
        }
      }

      if (tasks.unsafe_size() == static_cast<size_t>(_context.partition.k) / 2) {
        break;
      }
    }
  }
  return tasks.unsafe_size();
}

bool ParticipationScheduler::isEligible(const BlockPair& blocks) {
  const bool skip_small_cuts = !_is_input_hypergraph &&
    _context.refinement.flows.skip_small_cuts;
  const int cut_he_threshold = skip_small_cuts ? 10 : 0;

  const bool contains_enough_cut_hes = _quotient_graph.edge(blocks).weightOfCutHyperedges() > cut_he_threshold;
  const bool is_promising_blocks_pair =
    !_context.refinement.flows.skip_unpromising_blocks ||
      ( _round == 0 || _quotient_graph.edge(blocks).numImprovementsFound() > 0 );
  return (_active_blocks[blocks.i] || _active_blocks[blocks.j]) // at least one block active
    && contains_enough_cut_hes && is_promising_blocks_pair;
}

}  // namespace mt_kahypar
