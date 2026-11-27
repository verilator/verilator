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

#include <tbb/task.h>

#include "mt-kahypar/parallel/stl/scalable_vector.h"
#include "mt-kahypar/parallel/stl/scalable_queue.h"
#include "mt-kahypar/partition/initial_partitioning/initial_partitioning_data_container.h"
#include "mt-kahypar/utils/randomize.h"

namespace mt_kahypar {

template<typename TypeTraits>
class PseudoPeripheralStartNodes {

  static constexpr bool debug = false;

  using StartNodes = vec<vec<HypernodeID>>;
  using Queue = parallel::scalable_queue<HypernodeID>;
  using PartitionedHypergraph = typename TypeTraits::PartitionedHypergraph;

 public:
  static inline StartNodes computeStartNodes(InitialPartitioningDataContainer<TypeTraits>& ip_data,
                                             const Context& context,
                                             const PartitionID default_block,
                                             std::mt19937& rng) {
    PartitionedHypergraph& hypergraph = ip_data.local_partitioned_hypergraph();
    kahypar::ds::FastResetFlagArray<>& hypernodes_in_queue =
      ip_data.local_hypernode_fast_reset_flag_array();
    kahypar::ds::FastResetFlagArray<>& hyperedges_in_queue =
      ip_data.local_hyperedge_fast_reset_flag_array();

    StartNodes start_nodes(context.partition.k);
    vec<PartitionID> empty_blocks(context.partition.k);
    std::iota(empty_blocks.begin(), empty_blocks.end(), 0);
    bool contains_seed_node = false;
    if ( hypergraph.hasFixedVertices() ) {
      hypernodes_in_queue.reset();
      hyperedges_in_queue.reset();
      // Use all neighbors of fixed vertices as seed nodes
      for ( const HypernodeID& hn : ip_data.fixedVertices() ) {
        ASSERT(hypergraph.isFixed(hn));
        const PartitionID block = hypergraph.fixedVertexBlock(hn);
        for ( const HyperedgeID& he : hypergraph.incidentEdges(hn) ) {
          if ( !hyperedges_in_queue[block * hypergraph.initialNumEdges() + he] ) {
            for ( const HypernodeID& pin : hypergraph.pins(he) ) {
              if ( !hypergraph.isFixed(pin) &&
                   !hypernodes_in_queue[block * hypergraph.initialNumNodes() + pin] ) {
                start_nodes[block].push_back(pin);
                contains_seed_node = true;
                hypernodes_in_queue.set(block * hypergraph.initialNumNodes() + pin, true);
              }
            }
            hyperedges_in_queue.set(block * hypergraph.initialNumEdges() + he, true);
          }
        }
      }

      for ( size_t i = 0; i < empty_blocks.size(); ++i ) {
        // Remove blocks that contain seed nodes from empty blocks
        const PartitionID block = empty_blocks[i];
        if ( !start_nodes[block].empty() ) {
          std::swap(empty_blocks[i--], empty_blocks[empty_blocks.size() - 1]);
          empty_blocks.pop_back();
        }
        std::shuffle(start_nodes[block].begin(), start_nodes[block].end(), rng);
      }
    }

    if ( !contains_seed_node ) {
      HypernodeID start_hn =
        std::uniform_int_distribution<HypernodeID>(0, hypergraph.initialNumNodes() -1 )(rng);
      if ( !hypergraph.nodeIsEnabled(start_hn) || hypergraph.isFixed(start_hn) ) {
        start_hn = ip_data.get_unassigned_hypernode(default_block);
      }

      if ( start_hn != kInvalidHypernode ) {
        ASSERT(hypergraph.nodeIsEnabled(start_hn));
        start_nodes[empty_blocks[0]].push_back(start_hn);
        std::swap(empty_blocks[0], empty_blocks[empty_blocks.size() - 1]);
        empty_blocks.pop_back();
        contains_seed_node = true;
      }
    }

    if ( !empty_blocks.empty() && contains_seed_node ) {
      // We perform k - 1 BFS on the hypergraph to find k vertices that
      // are "far" away from each other. Each BFS adds a new hypernode to
      // list of start nodes. Each entry in start_nodes represents a start
      // node for a specific block of the partition. The new vertex added to
      // the list of start nodes is the one last touched by the current BFS.
      const HypernodeID current_num_nodes =
        hypergraph.initialNumNodes() - hypergraph.numRemovedHypernodes() -
        ip_data.numFixedVertices();
      parallel::scalable_vector<HypernodeID> non_touched_hypernodes;
      for ( const PartitionID block : empty_blocks ) {
        Queue queue;
        hypernodes_in_queue.reset();
        hyperedges_in_queue.reset();
        initializeQueue(queue, start_nodes, ip_data, hypernodes_in_queue);

        HypernodeID last_hypernode_touched = kInvalidHypernode;
        HypernodeID num_touched_hypernodes = 0;
        ASSERT(queue.size() > 0);
        while ( !queue.empty() ) {
          last_hypernode_touched = queue.front();
          queue.pop();
          ++num_touched_hypernodes;

          // Add all adjacent non-visited vertices of the current visited hypernode
          // to queue.
          for ( const HyperedgeID& he : hypergraph.incidentEdges(last_hypernode_touched) ) {
            if ( !hyperedges_in_queue[he] ) {
              if ( hypergraph.edgeSize(he) <= context.partition.ignore_hyperedge_size_threshold ) {
                for ( const HypernodeID& pin : hypergraph.pins(he) ) {
                  if ( !hypernodes_in_queue[pin] ) {
                    queue.push(pin);
                    hypernodes_in_queue.set(pin, true);
                  }
                }
              }
              hyperedges_in_queue.set(he, true);
            }
          }

          // In case the queue is empty and we have not visited all hypernodes.
          // Therefore, we choose one unvisited vertex at random.
          if ( queue.empty() && num_touched_hypernodes < current_num_nodes ) {
            for ( const HypernodeID& hn : hypergraph.nodes() ) {
              if ( !hypernodes_in_queue[hn] ) {
                non_touched_hypernodes.push_back(hn);
                hypernodes_in_queue.set(hn, true);
              }
            }
            const int rand_idx = std::uniform_int_distribution<>(0, non_touched_hypernodes.size() - 1)(rng);
            last_hypernode_touched = non_touched_hypernodes[rand_idx];
          }
        }

        // Add last touched hypernode of the BFS as new start node for block i + 1
        start_nodes[block].push_back(last_hypernode_touched);
        non_touched_hypernodes.clear();
      }
    }

    ASSERT(start_nodes.size() == static_cast<size_t>(context.partition.k));
    return start_nodes;
  }

 private:
  static inline void initializeQueue(Queue& queue,
                                     StartNodes& start_nodes,
                                     InitialPartitioningDataContainer<TypeTraits>& ip_data,
                                     kahypar::ds::FastResetFlagArray<>& hypernodes_in_queue) {
    for ( const HypernodeID& hn : ip_data.fixedVertices() ) {
      hypernodes_in_queue.set(hn, true);
    }
    for ( const vec<HypernodeID>& nodes_of_block : start_nodes ) {
      for ( const HypernodeID& hn : nodes_of_block ) {
        if ( !hypernodes_in_queue[hn] ) {
          queue.push(hn);
          hypernodes_in_queue.set(hn, true);
        }
      }
    }
  }
};


} // namespace mt_kahypar
