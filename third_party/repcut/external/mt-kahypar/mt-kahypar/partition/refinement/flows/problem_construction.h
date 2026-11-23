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

#pragma once

#include <tbb/enumerable_thread_specific.h>

#include "mt-kahypar/partition/context.h"
#include "mt-kahypar/datastructures/sparse_map.h"
#include "mt-kahypar/partition/refinement/flows/flow_common.h"
#include "mt-kahypar/partition/refinement/flows/quotient_graph.h"
#include "mt-kahypar/parallel/stl/scalable_vector.h"
#include "mt-kahypar/parallel/stl/scalable_queue.h"
#include "mt-kahypar/parallel/atomic_wrapper.h"

namespace mt_kahypar {

template<typename TypeTraits>
class ProblemConstruction {

  static constexpr bool debug = false;

  using PartitionedHypergraph = typename TypeTraits::PartitionedHypergraph;

  /**
   * Contains data required to grow two region around
   * the cut of two blocks of the partition.
   */
  struct BFSData {
    explicit BFSData(const HypernodeID num_nodes,
                     const HyperedgeID num_edges,
                     const PartitionID k) :
      current_distance(0),
      queue(),
      next_queue(),
      visited_hn(num_nodes, false),
      visited_he(num_edges, false),
      contained_hes(num_edges, false),
      locked_blocks(k, false),
      queue_weight_block_0(0),
      queue_weight_block_1(0),
      lock_queue(false)  { }

    void clearQueue();

    void reset();

    HypernodeID pop_hypernode();

    void add_pins_of_hyperedge_to_queue(const HyperedgeID& he,
                                        const PartitionedHypergraph& phg,
                                        const size_t max_bfs_distance,
                                        const HypernodeWeight max_weight_block_0,
                                        const HypernodeWeight max_weight_block_1);

    bool is_empty() const {
      return queue.empty();
    }

    bool is_next_empty() const {
      return next_queue.empty();
    }

    void swap_with_next_queue() {
      if ( !is_next_empty() ) {
        std::swap(queue, next_queue);
        ++current_distance;
      }
    }

    BlockPair blocks;
    size_t current_distance;
    parallel::scalable_queue<HypernodeID> queue;
    parallel::scalable_queue<HypernodeID> next_queue;
    vec<bool> visited_hn;
    vec<bool> visited_he;
    vec<bool> contained_hes;
    vec<bool> locked_blocks;
    HypernodeWeight queue_weight_block_0;
    HypernodeWeight queue_weight_block_1;
    bool lock_queue;
  };

 public:
  explicit ProblemConstruction(const HypernodeID num_hypernodes,
                               const HyperedgeID num_hyperedges,
                               const Context& context) :
    _context(context),
    _scaling(1.0 + _context.refinement.flows.alpha *
      std::min(0.05, _context.partition.epsilon)),
    _num_hypernodes(num_hypernodes),
    _num_hyperedges(num_hyperedges),
    _local_bfs([&] {
        // If the number of blocks changes, BFSData needs to be initialized
        // differently. Thus we use a lambda that reads the current number of
        // blocks from the context
        return constructBFSData();
      }
    ) { }

  ProblemConstruction(const ProblemConstruction&) = delete;
  ProblemConstruction(ProblemConstruction&&) = delete;

  ProblemConstruction & operator= (const ProblemConstruction &) = delete;
  ProblemConstruction & operator= (ProblemConstruction &&) = delete;

  Subhypergraph construct(const BlockPair& blocks,
                          QuotientGraph& quotient_graph,
                          const PartitionedHypergraph& phg,
                          bool deterministic);

  void changeNumberOfBlocks(const PartitionID new_k);

 private:
  BFSData constructBFSData() const {
    return BFSData(_num_hypernodes, _num_hyperedges, _context.partition.k);
  }

  MT_KAHYPAR_ATTRIBUTE_ALWAYS_INLINE bool isMaximumProblemSizeReached(
    const Subhypergraph& sub_hg,
    const HypernodeWeight max_weight_block_0,
    const HypernodeWeight max_weight_block_1,
    vec<bool>& locked_blocks) const;

  const Context& _context;
  double _scaling;
  HypernodeID _num_hypernodes;
  HyperedgeID _num_hyperedges;

  // ! Contains data required for BFS construction algorithm
  tbb::enumerable_thread_specific<BFSData> _local_bfs;
};

}  // namespace kahypar
