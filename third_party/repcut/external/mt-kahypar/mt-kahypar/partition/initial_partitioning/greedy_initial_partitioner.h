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

#include "mt-kahypar/partition/initial_partitioning/i_initial_partitioner.h"
#include "mt-kahypar/partition/initial_partitioning/initial_partitioning_data_container.h"
#include "mt-kahypar/partition/initial_partitioning/policies/pseudo_peripheral_start_nodes.h"

namespace mt_kahypar {
template<typename TypeTraits, template<typename> typename GainPolicyT>
class GreedyInitialPartitionerBase {

  using PartitionedHypergraph = typename TypeTraits::PartitionedHypergraph;
  using GainComputationPolicy = GainPolicyT<TypeTraits>;

  static constexpr bool debug = false;
  static constexpr bool enable_heavy_assert = false;

 public:
  GreedyInitialPartitionerBase(const InitialPartitioningAlgorithm algorithm,
                               ip_data_container_t* ip_data,
                               const Context& context,
                               const PartitionID default_block,
                               const int seed, const int tag) :
    _algorithm(algorithm),
    _ip_data(ip::to_reference<TypeTraits>(ip_data)),
    _context(context),
    _default_block(default_block),
    _rng(seed),
    _tag(tag)
    { }

  template<typename PQSelectionPolicy>
  void partitionWithSelectionPolicy() {
    if ( _ip_data.should_initial_partitioner_run(_algorithm) ) {
      HighResClockTimepoint start = std::chrono::high_resolution_clock::now();
      PartitionedHypergraph& hg = _ip_data.local_partitioned_hypergraph();
      KWayPriorityQueue& kway_pq = _ip_data.local_kway_priority_queue();
      kahypar::ds::FastResetFlagArray<>& hyperedges_in_queue =
        _ip_data.local_hyperedge_fast_reset_flag_array();

      initializeVertices();

      PartitionID to = kInvalidPartition;
      bool use_perfect_balanced_as_upper_bound = true;
      bool allow_overfitting = false;
      while (true) {
        // If our default block has a weight less than the perfect balanced block weight
        // we terminate greedy initial partitioner in order to prevent that the default block
        // becomes underloaded.
        if ( _default_block != kInvalidPartition &&
            hg.partWeight(_default_block) <
            _context.partition.perfect_balance_part_weights[_default_block] ) {
          break;
        }

        HypernodeID hn = kInvalidHypernode;
        Gain gain = kInvalidGain;

        // The greedy initial partitioner has 3 different stages. In the first, we use the perfect
        // balanced part weight as upper bound for the block weights. Once we reach the block weight
        // limit, we release the upper bound and use the maximum allowed block weight as new upper bound.
        // Once we are not able to assign any vertex to a block, we allow overfitting, which effectively
        // allows to violate the balance constraint.
        if ( !PQSelectionPolicy::pop(hg, kway_pq, hn, to, gain, use_perfect_balanced_as_upper_bound) ) {
          if ( use_perfect_balanced_as_upper_bound ) {
            enableAllPQs(_context.partition.k, kway_pq);
            use_perfect_balanced_as_upper_bound = false;
            continue;
          } else if ( !allow_overfitting ) {
            enableAllPQs(_context.partition.k, kway_pq);
            allow_overfitting = true;
            continue;
          } else {
            break;
          }
        }

        ASSERT(hn != kInvalidHypernode);
        ASSERT(to != kInvalidPartition);
        ASSERT(to != _default_block);
        ASSERT(hg.partID(hn) == _default_block);

        if ( allow_overfitting || fitsIntoBlock(hg, hn, to, use_perfect_balanced_as_upper_bound) ) {
          if ( _default_block != kInvalidPartition ) {
            hg.changeNodePartNoSync(hn, _default_block, to);
          } else {
            hg.setNodePart(hn, to);
          }
          insertAndUpdateVerticesAfterMove(hg, kway_pq, hyperedges_in_queue, hn, _default_block, to);
        } else {
          kway_pq.insert(hn, to, gain);
          kway_pq.disablePart(to);
        }
      }
      hg.resetEdgeSynchronization();

      HighResClockTimepoint end = std::chrono::high_resolution_clock::now();
      double time = std::chrono::duration<double>(end - start).count();
      _ip_data.commit(_algorithm, _rng, _tag, time);
    }
  }

 private:
  void initializeVertices() {
    PartitionedHypergraph& hg = _ip_data.local_partitioned_hypergraph();
    KWayPriorityQueue& kway_pq = _ip_data.local_kway_priority_queue();

    // Experiments have shown that some pq selection policies work better
    // if we preassign all vertices to a block and than execute the greedy
    // initial partitioner. E.g. the round-robin variant leaves the hypernode
    // unassigned, but the global and sequential strategy both preassign
    // all vertices to block 1 before initial partitioning.
    _ip_data.preassignFixedVertices(hg);
    if ( _default_block != kInvalidPartition ) {
      ASSERT(_default_block < _context.partition.k);
      kway_pq.disablePart(_default_block);
      for ( const HypernodeID& hn : hg.nodes() ) {
        if ( !hg.isFixed(hn) ) {
          hg.setNodePart(hn, _default_block);
        }
      }
    }

    // Insert start vertices into its corresponding PQs
    _ip_data.reset_unassigned_hypernodes(_rng);
    vec<vec<HypernodeID>> start_nodes =
      PseudoPeripheralStartNodes<TypeTraits>::computeStartNodes(_ip_data, _context, _default_block, _rng);
    ASSERT(static_cast<size_t>(_context.partition.k) == start_nodes.size());
    kway_pq.clear();
    for ( PartitionID block = 0; block < _context.partition.k; ++block ) {
      if ( block != _default_block ) {
        for ( const HypernodeID& hn : start_nodes[block] ) {
          insertVertexIntoPQ(hg, kway_pq, hn, block);
        }
      }
    }

    _ip_data.local_hyperedge_fast_reset_flag_array().reset();
  }

  bool fitsIntoBlock(PartitionedHypergraph& hypergraph,
                     const HypernodeID hn,
                     const PartitionID block,
                     const bool use_perfect_balanced_as_upper_bound) const {
    ASSERT(block != kInvalidPartition && block < _context.partition.k);
    const HypernodeWeight upper_bound = use_perfect_balanced_as_upper_bound ?
      _context.partition.perfect_balance_part_weights[block] : _context.partition.max_part_weights[block];
    return hypergraph.partWeight(block) + hypergraph.nodeWeight(hn) <=
      upper_bound;
  }

  void insertVertexIntoPQ(const PartitionedHypergraph& hypergraph,
                          KWayPriorityQueue& pq,
                          const HypernodeID hn,
                          const PartitionID to) {
    ASSERT(to != kInvalidPartition && to < _context.partition.k);
    ASSERT(hypergraph.partID(hn) == _default_block, V(hypergraph.partID(hn)) << V(_default_block));
    ASSERT(!pq.contains(hn, to));

    const Gain gain = GainComputationPolicy::calculateGain(hypergraph, hn, to);
    pq.insert(hn, to, gain);
    if ( !pq.isEnabled(to) ) {
      pq.enablePart(to);
    }

    ASSERT(pq.contains(hn, to));
    ASSERT(pq.isEnabled(to));
  }

  void insertUnassignedVertexIntoPQ(const PartitionedHypergraph& hypergraph,
                                    KWayPriorityQueue& pq,
                                    const PartitionID to) {
    ASSERT(to != _default_block);
    const HypernodeID unassigned_hn = _ip_data.get_unassigned_hypernode(_default_block);
    if ( unassigned_hn != kInvalidHypernode ) {
      insertVertexIntoPQ(hypergraph, pq, unassigned_hn, to);
    }
  }

  void insertAndUpdateVerticesAfterMove(const PartitionedHypergraph& hypergraph,
                                        KWayPriorityQueue& pq,
                                        kahypar::ds::FastResetFlagArray<>& hyperedges_in_queue,
                                        const HypernodeID hn,
                                        const PartitionID from,
                                        const PartitionID to) {
    ASSERT(to != kInvalidPartition && to < _context.partition.k);
    ASSERT(hypergraph.partID(hn) == to);

    // Perform delta gain updates
    GainComputationPolicy::deltaGainUpdate(hypergraph, pq, hn, from, to);

    // Remove moved hypernode hn from all PQs
    for ( PartitionID block = 0; block < hypergraph.k(); ++block ) {
      if ( pq.contains(hn, block) ) {

        // Prevent that PQ becomes empty
        if ( to != block && pq.size(block) == 1 ) {
          insertUnassignedVertexIntoPQ(hypergraph, pq, block);
        }

        pq.remove(hn, block);
      }
    }

    // Insert all adjacent hypernodes of the moved vertex into PQ of block to
    for ( const HyperedgeID& he : hypergraph.incidentEdges(hn)) {
      if ( !hyperedges_in_queue[to * hypergraph.initialNumEdges() + he] ) {
        for ( const HypernodeID& pin : hypergraph.pins(he) ) {
          if ( hypergraph.partID(pin) == _default_block &&
               !pq.contains(pin, to) && !hypergraph.isFixed(pin) ) {
            insertVertexIntoPQ(hypergraph, pq, pin, to);
          }
        }
        hyperedges_in_queue.set(to * hypergraph.initialNumEdges() + he, true);
      }
    }

    // Prevent that PQ becomes empty
    if ( pq.size(to) == 0 ) {
      insertUnassignedVertexIntoPQ(hypergraph, pq, to);
    }
  }

  void enableAllPQs(const PartitionID k, KWayPriorityQueue& pq) {
    for ( PartitionID block = 0; block < k; ++block ) {
      if ( block != _default_block ) {
        pq.enablePart(block);
      }
    }
  }

  const InitialPartitioningAlgorithm _algorithm;
  InitialPartitioningDataContainer<TypeTraits>& _ip_data;
  const Context& _context;
  const PartitionID _default_block;
  std::mt19937 _rng;
  const int _tag;
};


// the split into base and subclass serves to reduce the compile time, since the base class
// is only instantiated once for all PQ selection policies
template<typename TypeTraits,
         template<typename> typename GainPolicyT,
         template<typename> typename PQSelectionPolicyT>
class GreedyInitialPartitioner : public IInitialPartitioner, GreedyInitialPartitionerBase<TypeTraits, GainPolicyT> {

  using Base = GreedyInitialPartitionerBase<TypeTraits, GainPolicyT>;
  using PartitionedHypergraph = typename TypeTraits::PartitionedHypergraph;
  using PQSelectionPolicy = PQSelectionPolicyT<TypeTraits>;

 public:
  GreedyInitialPartitioner(const InitialPartitioningAlgorithm algorithm,
                           ip_data_container_t* ip_data,
                           const Context& context,
                           const int seed, const int tag) :
    Base(algorithm, ip_data, context, PQSelectionPolicy::getDefaultBlock(), seed, tag) { }

 private:
  void partitionImpl() final {
    Base::template partitionWithSelectionPolicy<PQSelectionPolicy>();
  }
};

} // namespace mt_kahypar
