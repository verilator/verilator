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

#include "mt-kahypar/partition/initial_partitioning/initial_partitioning_commons.h"

namespace mt_kahypar {

// ! Selects the PQs in a round-robin fashion.
template<typename TypeTraits>
class RoundRobinPQSelectionPolicy {

  using PartitionedHypergraph = typename TypeTraits::PartitionedHypergraph;

 public:
  static inline bool pop(const PartitionedHypergraph& hypergraph,
                         KWayPriorityQueue& pq,
                         HypernodeID& hn,
                         PartitionID& to,
                         Gain& gain,
                         const bool) {
    ASSERT(to >= kInvalidPartition && to < hypergraph.k());
    hn = kInvalidHypernode;
    gain = kInvalidGain;

    to = (to + 1) % hypergraph.k();
    const PartitionID start_block = to;
    while ( !pq.isEnabled(to) ) {
      to = (to + 1) % hypergraph.k();
      if ( start_block == to ) {
        to = kInvalidPartition;
        return false;
      }
    }

    ASSERT(to != kInvalidPartition && to < hypergraph.k());
    ASSERT(pq.isEnabled(to));
    pq.deleteMaxFromPartition(hn, gain, to);
    ASSERT(hn != kInvalidHypernode);
    return true;
  }

  // As default block we define the block to which all vertices are assigned to
  // before greedy initial partitioning. Experiments have shown that the greedy
  // round robin variant performs best if we leave all vertices unassigned before
  // greedy initial partitioning.
  static inline PartitionID getDefaultBlock() {
    return kInvalidPartition;
  }
};


// ! Selects the PQ which contains the maximum gain move
template<typename TypeTraits>
class GlobalPQSelectionPolicy {

  using PartitionedHypergraph = typename TypeTraits::PartitionedHypergraph;

 public:
  static inline bool pop(const PartitionedHypergraph&,
                         KWayPriorityQueue& pq,
                         HypernodeID& hn,
                         PartitionID& to,
                         Gain& gain,
                         const bool) {
    hn = kInvalidHypernode;
    to = kInvalidPartition;
    gain = kInvalidGain;

    if ( pq.numNonEmptyParts() > 0 && pq.numEnabledParts() > 0 ) {
      pq.deleteMax(hn, gain, to);
      ASSERT(hn != kInvalidHypernode);
      return true;
    } else {
      return false;
    }
  }

  // As default block we define the block to which all vertices are assigned to
  // before greedy initial partitioning. Experiments have shown that the greedy
  // global variant performs best if we assign all vertices to block 1 before
  // greedy initial partitioning.
  static inline PartitionID getDefaultBlock() {
    return 1;
  }
};


// ! Selects the PQs one by one until they are disabled
template<typename TypeTraits>
class SequentialPQSelectionPolicy {

  using PartitionedHypergraph = typename TypeTraits::PartitionedHypergraph;

 public:
  static inline bool pop(const PartitionedHypergraph& hypergraph,
                         KWayPriorityQueue& pq,
                         HypernodeID& hn,
                         PartitionID& to,
                         Gain& gain,
                         const bool use_perfect_balanced_as_upper_bound) {
    hn = kInvalidHypernode;
    gain = kInvalidGain;

    if ( use_perfect_balanced_as_upper_bound ) {
      if ( to == kInvalidPartition ) {
        to = 0;
      }

      while ( to < hypergraph.k() && !pq.isEnabled(to) ) {
        ++to;
      }

      if ( to < hypergraph.k() ) {
        ASSERT(pq.size(to) > 0);
        pq.deleteMaxFromPartition(hn, gain, to);
        ASSERT(hn != kInvalidHypernode);
        return true;
      } else {
        return false;
      }
    } else {
      return GlobalPQSelectionPolicy<TypeTraits>::pop(hypergraph,
        pq, hn, to, gain, use_perfect_balanced_as_upper_bound);
    }
  }

  // As default block we define the block to which all vertices are assigned to
  // before greedy initial partitioning. Experiments have shown that the greedy
  // sequential variant performs best if we assign all vertices to block 1 before
  // greedy initial partitioning.
  static inline PartitionID getDefaultBlock() {
    return 1;
  }
};

} // namespace mt_kahypar
