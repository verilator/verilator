/*******************************************************************************
 * MIT License
 *
 * This file is part of Mt-KaHyPar.
 *
 * Copyright (C) 2021 Tobias Heuer <tobias.heuer@kit.edu>
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


#include "mt-kahypar/partition/refinement/flows/problem_construction.h"

#include <unordered_map>

#include <tbb/parallel_for.h>
#include <tbb/parallel_sort.h>

#include "mt-kahypar/definitions.h"
#include "mt-kahypar/partition/mapping/target_graph.h"

namespace mt_kahypar {

template<typename TypeTraits>
void ProblemConstruction<TypeTraits>::BFSData::clearQueue() {
  while ( !queue.empty() ) queue.pop();
  while ( !next_queue.empty() ) next_queue.pop();
}

template<typename TypeTraits>
void ProblemConstruction<TypeTraits>::BFSData::reset() {
  current_distance = 0;
  queue_weight_block_0 = 0;
  queue_weight_block_1 = 0;
  lock_queue = false;
  clearQueue();
  std::fill(visited_hn.begin(), visited_hn.end(), false);
  std::fill(visited_he.begin(), visited_he.end(), false);
  std::fill(contained_hes.begin(), contained_hes.end(), false);
  std::fill(locked_blocks.begin(), locked_blocks.end(), false);
}

template<typename TypeTraits>
HypernodeID ProblemConstruction<TypeTraits>::BFSData::pop_hypernode() {
  ASSERT(!queue.empty());
  const HypernodeID hn = queue.front();
  queue.pop();
  return hn;
}

template<typename TypeTraits>
void ProblemConstruction<TypeTraits>::BFSData::add_pins_of_hyperedge_to_queue(
  const HyperedgeID& he,
  const PartitionedHypergraph& phg,
  const size_t max_bfs_distance,
  const HypernodeWeight max_weight_block_0,
  const HypernodeWeight max_weight_block_1) {
  if ( current_distance <= max_bfs_distance && !lock_queue ) {
    if ( !visited_he[he] ) {
      for ( const HypernodeID& pin : phg.pins(he) ) {
        if ( !visited_hn[pin] ) {
          const PartitionID block = phg.partID(pin);
          const bool is_block_0 = blocks.i == block;
          const bool is_block_1 = blocks.j == block;
          if ( (is_block_0 || is_block_1) && !locked_blocks[block] ) {
            next_queue.push(pin);
            queue_weight_block_0 += is_block_0 ? phg.nodeWeight(pin) : 0;
            queue_weight_block_1 += is_block_1 ? phg.nodeWeight(pin) : 0;
          }
          visited_hn[pin] = true;
        }
      }
      visited_he[he] = true;
    }
  }

  if ( queue_weight_block_0 >= max_weight_block_0 &&
       queue_weight_block_1 >= max_weight_block_1 ) {
    lock_queue = true;
  }
}

namespace {
  using assert_map = std::unordered_map<HyperedgeID, bool>;
}

template<typename TypeTraits>
Subhypergraph ProblemConstruction<TypeTraits>::construct(const BlockPair& blocks,
                                                         QuotientGraph& quotient_graph,
                                                         const PartitionedHypergraph& phg,
                                                         bool deterministic) {
  Subhypergraph sub_hg;

  auto& cut_hes = quotient_graph.edge(blocks).cut_hes;
  if (deterministic) {
    tbb::parallel_sort(cut_hes.begin(), cut_hes.end());
  } else {
    std::shuffle(cut_hes.begin(), cut_hes.end(), utils::Randomize::instance().getGenerator());
  }

  // NOTE: the BFS initialzation must happen after cut_hes, otherwise tbb::parallel_sort could
  // interfere with the thread local variable (see "Work Isolation" in oneTBB Developer Guide)
  BFSData& bfs = _local_bfs.local();
  bfs.reset();
  bfs.blocks = blocks;
  sub_hg.block_0 = bfs.blocks.i;
  sub_hg.block_1 = bfs.blocks.j;
  sub_hg.weight_of_block_0 = 0;
  sub_hg.weight_of_block_1 = 0;
  sub_hg.num_pins = 0;
  const HypernodeWeight max_weight_block_0 =
    _scaling * _context.partition.perfect_balance_part_weights[sub_hg.block_1] - phg.partWeight(sub_hg.block_1);
  const HypernodeWeight max_weight_block_1 =
    _scaling * _context.partition.perfect_balance_part_weights[sub_hg.block_0] - phg.partWeight(sub_hg.block_0);
  const size_t max_bfs_distance = _context.refinement.flows.max_bfs_distance;

  // We initialize the BFS with all cut hyperedges running
  // between the involved block associated with the search
  bfs.clearQueue();
  const size_t num_cut_hes = cut_hes.size();  // size() is expensive on concurrent_vector
  for ( size_t i = 0; i < num_cut_hes; ++i ) {
    const HyperedgeID he = cut_hes[i];
    if ( phg.pinCountInPart(he, blocks.i) > 0 && phg.pinCountInPart(he, blocks.j) > 0 ) {
      bfs.add_pins_of_hyperedge_to_queue(he, phg, max_bfs_distance,
        max_weight_block_0, max_weight_block_1);
    }
  }
  bfs.swap_with_next_queue();

  // BFS
  while ( !bfs.is_empty() &&
          !isMaximumProblemSizeReached(sub_hg,
            max_weight_block_0, max_weight_block_1, bfs.locked_blocks) ) {
    HypernodeID hn = bfs.pop_hypernode();
    PartitionID block = phg.partID(hn);
    const bool is_block_contained = block == sub_hg.block_0 || block == sub_hg.block_1;
    if ( is_block_contained && !bfs.locked_blocks[block] ) {
      const bool is_fixed = phg.isFixed(hn);
      // We do not add fixed vertices to the flow problem, but still
      // expand the BFS to its neighbors
      if ( !is_fixed ) {
        if ( sub_hg.block_0  == block ) {
          sub_hg.nodes_of_block_0.push_back(hn);
          sub_hg.weight_of_block_0 += phg.nodeWeight(hn);
        } else {
          ASSERT(sub_hg.block_1 == block);
          sub_hg.nodes_of_block_1.push_back(hn);
          sub_hg.weight_of_block_1 += phg.nodeWeight(hn);
        }
        sub_hg.num_pins += phg.nodeDegree(hn);
      }

      // Push all neighbors of the added vertex into the queue
      for ( const HyperedgeID& he : phg.incidentEdges(hn) ) {
        bfs.add_pins_of_hyperedge_to_queue(he, phg, max_bfs_distance,
          max_weight_block_0, max_weight_block_1);
        if ( !is_fixed && !bfs.contained_hes[phg.uniqueEdgeID(he)] ) {
          sub_hg.hes.push_back(he);
          bfs.contained_hes[phg.uniqueEdgeID(he)] = true;
        }
      }
    }

    if ( bfs.is_empty() ) {
      bfs.swap_with_next_queue();
    }
  }
  DBG << V(blocks.i) << V(blocks.j) << "-" << sub_hg;

  // Check if all touched hyperedges are contained in subhypergraph
  ASSERT([&]() {
    assert_map expected_hes;
    for ( const HyperedgeID& he : sub_hg.hes ) {
      const HyperedgeID id = phg.uniqueEdgeID(he);
      if ( expected_hes.count(id) > 0 ) {
        LOG << "Hyperedge" << he << "is contained multiple times in subhypergraph!";
        return false;
      }
      expected_hes[id] = true;
    }

    for ( const HypernodeID& hn : sub_hg.nodes_of_block_0 ) {
      for ( const HyperedgeID& he : phg.incidentEdges(hn) ) {
        const HyperedgeID id = phg.uniqueEdgeID(he);
        if ( expected_hes.count(id) == 0 ) {
          LOG << "Hyperedge" << he << "not contained in subhypergraph!";
          return false;
        }
        expected_hes[id] = false;
      }
    }

    for ( const HypernodeID& hn : sub_hg.nodes_of_block_1 ) {
      for ( const HyperedgeID& he : phg.incidentEdges(hn) ) {
        const HyperedgeID id = phg.uniqueEdgeID(he);
        if ( expected_hes.count(id) == 0 ) {
          LOG << "Hyperedge" << he << "not contained in subhypergraph!";
          return false;
        }
        expected_hes[id] = false;
      }
    }

    for ( const auto& entry : expected_hes ) {
      const HyperedgeID he = entry.first;
      const bool visited = !entry.second;
      if ( !visited ) {
        LOG << "HyperedgeID" << he << "should be not part of subhypergraph!";
        return false;
      }
    }
    return true;
  }(), "Subhypergraph construction failed!");

  return sub_hg;
}

template<typename TypeTraits>
void ProblemConstruction<TypeTraits>::changeNumberOfBlocks(const PartitionID new_k) {
  ASSERT(new_k == _context.partition.k);
  for ( BFSData& data : _local_bfs ) {
    if ( static_cast<size_t>(new_k) > data.locked_blocks.size() ) {
      data.locked_blocks.assign(new_k, false);
    }
  }
}

template<typename TypeTraits>
MT_KAHYPAR_ATTRIBUTE_ALWAYS_INLINE bool ProblemConstruction<TypeTraits>::isMaximumProblemSizeReached(
  const Subhypergraph& sub_hg,
  const HypernodeWeight max_weight_block_0,
  const HypernodeWeight max_weight_block_1,
  vec<bool>& locked_blocks) const {
  if ( sub_hg.weight_of_block_0 >= max_weight_block_0 ) {
    locked_blocks[sub_hg.block_0] = true;
  }
  if ( sub_hg.weight_of_block_1 >= max_weight_block_1 ) {
    locked_blocks[sub_hg.block_1] = true;
  }
  if ( sub_hg.num_pins >= _context.refinement.flows.max_num_pins ) {
    locked_blocks[sub_hg.block_0] = true;
    locked_blocks[sub_hg.block_1] = true;
  }

  return locked_blocks[sub_hg.block_0] && locked_blocks[sub_hg.block_1];
}

INSTANTIATE_CLASS_WITH_TYPE_TRAITS(ProblemConstruction)

} // namespace mt_kahypar