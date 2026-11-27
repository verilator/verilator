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

#include "mt-kahypar/partition/initial_partitioning/bfs_initial_partitioner.h"

#include "mt-kahypar/definitions.h"
#include "mt-kahypar/partition/initial_partitioning/policies/pseudo_peripheral_start_nodes.h"
#include "mt-kahypar/utils/randomize.h"

namespace mt_kahypar {

template<typename TypeTraits>
void BFSInitialPartitioner<TypeTraits>::partitionImpl() {
  if ( _ip_data.should_initial_partitioner_run(InitialPartitioningAlgorithm::bfs) ) {
    HighResClockTimepoint start = std::chrono::high_resolution_clock::now();
    PartitionedHypergraph& hypergraph = _ip_data.local_partitioned_hypergraph();
    kahypar::ds::FastResetFlagArray<>& hypernodes_in_queue =
            _ip_data.local_hypernode_fast_reset_flag_array();
    kahypar::ds::FastResetFlagArray<>& hyperedges_in_queue =
            _ip_data.local_hyperedge_fast_reset_flag_array();

    _ip_data.reset_unassigned_hypernodes(_rng);
    _ip_data.preassignFixedVertices(hypergraph);
    vec<vec<HypernodeID>> start_nodes =
      PseudoPeripheralStartNodes<TypeTraits>::computeStartNodes(_ip_data, _context, kInvalidPartition, _rng);

    // Insert each start node for each block into its corresponding queue
    hypernodes_in_queue.reset();
    hyperedges_in_queue.reset();
    parallel::scalable_vector<Queue> queues(_context.partition.k);

    for (PartitionID block = 0; block < _context.partition.k; ++block) {
      for ( const HypernodeID& hn : start_nodes[block] ) {
        queues[block].push(hn);
        markHypernodeAsInQueue(hypergraph, hypernodes_in_queue, hn, block);
      }
    }

    // We grow the k blocks of the partition starting from each start node in
    // a BFS-fashion. The BFS queues for each block are visited in round-robin-fashion.
    // Once a block is on turn, it pops it first hypernode and pushes
    // all adjacent vertices into its queue.
    HypernodeID num_assigned_hypernodes = _ip_data.numFixedVertices();
    const HypernodeID current_num_nodes =
            hypergraph.initialNumNodes() - hypergraph.numRemovedHypernodes();
    while (num_assigned_hypernodes < current_num_nodes) {
      for (PartitionID block = 0; block < _context.partition.k; ++block) {
        HypernodeID hn = kInvalidHypernode;

        bool fits_into_block = false;
        while (!queues[block].empty()) {
          const HypernodeID next_hn = queues[block].front();
          ASSERT(!hypergraph.isFixed(next_hn));
          queues[block].pop();

          if (hypergraph.partID(next_hn) == kInvalidPartition) {
            // Hypernode is assigned to the current block, if it is not
            // assigned to an other block and if the assignment does not
            // violate the balanced constraint.
            // In case, there is no hypernode that fits into the current block,
            // we take the last unassigned hypernode popped from the queue.
            // Note, in that case the balanced constraint will be violated.
            hn = next_hn;
            if (fitsIntoBlock(hypergraph, hn, block)) {
              fits_into_block = true;
              break;
            }
          }
        }

        if (hn == kInvalidHypernode) {
          // Special case, in case all hypernodes in the queue are already
          // assigned to an other block or the hypergraph is unconnected, we
          // choose an new unassigned hypernode (if one exists)
          hn = _ip_data.get_unassigned_hypernode();
          if ( hn != kInvalidHypernode && fitsIntoBlock(hypergraph, hn, block) ) {
            fits_into_block = true;
          }
        }

        if ( hn != kInvalidHypernode && !fits_into_block ) {
          // The node does not fit into the block. Thus, we quickly
          // check if there is another block to which we can assign the node
          for ( PartitionID other_block = 0; other_block < _context.partition.k; ++other_block ) {
            if ( other_block != block && fitsIntoBlock(hypergraph, hn, other_block) ) {
              // There is another block to which we can assign the node
              // => ignore the node for now
              hn = kInvalidHypernode;
              break;
            }
          }
        }

        if (hn != kInvalidHypernode) {
          ASSERT(hypergraph.partID(hn) == kInvalidPartition, V(block) << V(hypergraph.partID(hn)));
          hypergraph.setNodePart(hn, block);
          ++num_assigned_hypernodes;
          pushIncidentHypernodesIntoQueue(hypergraph, _context, queues[block],
                                          hypernodes_in_queue, hyperedges_in_queue, hn, block);
        } else {
          ASSERT(queues[block].empty());
        }
      }
    }

    HighResClockTimepoint end = std::chrono::high_resolution_clock::now();
    double time = std::chrono::duration<double>(end - start).count();
    _ip_data.commit(InitialPartitioningAlgorithm::bfs, _rng, _tag, time);
  }
}

// ! Pushes all adjacent hypernodes (not visited before) of hypernode hn
// ! into the BFS queue of the corresponding block.
template<typename TypeTraits>
inline void BFSInitialPartitioner<TypeTraits>::pushIncidentHypernodesIntoQueue(const PartitionedHypergraph& hypergraph,
                                                                               const Context& context,
                                                                               Queue& queue,
                                                                               kahypar::ds::FastResetFlagArray<>& hypernodes_in_queue,
                                                                               kahypar::ds::FastResetFlagArray<>& hyperedges_in_queue,
                                                                               const HypernodeID hn,
                                                                               const PartitionID block) {
  ASSERT(hn != kInvalidHypernode && block != kInvalidPartition);
  for ( const HyperedgeID& he : hypergraph.incidentEdges(hn) ) {
    if ( !hyperedges_in_queue[block * hypergraph.initialNumEdges() + he] ) {
      if ( hypergraph.edgeSize(he) <= context.partition.ignore_hyperedge_size_threshold ) {
        for ( const HypernodeID& pin : hypergraph.pins(he) ) {
          if ( !hypernodes_in_queue[block * hypergraph.initialNumNodes() + pin] &&
                hypergraph.partID(pin) == kInvalidPartition ) {
            queue.push(pin);
            markHypernodeAsInQueue(hypergraph, hypernodes_in_queue, pin, block);
          }
        }
      }
      markHyperedgeAsInQueue(hypergraph, hyperedges_in_queue, he, block);
    }
  }
}

INSTANTIATE_CLASS_WITH_TYPE_TRAITS(BFSInitialPartitioner)

} // namespace mt_kahypar
