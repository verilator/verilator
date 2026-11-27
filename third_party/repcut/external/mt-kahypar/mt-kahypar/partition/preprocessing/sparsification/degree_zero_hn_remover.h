/*******************************************************************************
 * MIT License
 *
 * This file is part of Mt-KaHyPar.
 *
 * Copyright (C) 2020 Tobias Heuer <tobias.heuer@kit.edu>
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

#include <tbb/parallel_sort.h>

#include "mt-kahypar/partition/context.h"
#include "mt-kahypar/datastructures/streaming_vector.h"

namespace mt_kahypar {

template<typename TypeTraits>
class DegreeZeroHypernodeRemover {

  using Hypergraph = typename TypeTraits::Hypergraph;
  using PartitionedHypergraph = typename TypeTraits::PartitionedHypergraph;

 public:
  DegreeZeroHypernodeRemover(const Context& context) :
    _context(context),
    _removed_hns() { }

  DegreeZeroHypernodeRemover(const DegreeZeroHypernodeRemover&) = delete;
  DegreeZeroHypernodeRemover & operator= (const DegreeZeroHypernodeRemover &) = delete;

  DegreeZeroHypernodeRemover(DegreeZeroHypernodeRemover&&) = delete;
  DegreeZeroHypernodeRemover & operator= (DegreeZeroHypernodeRemover &&) = delete;

  // ! Remove all degree zero vertices
  HypernodeID removeDegreeZeroHypernodes(Hypergraph& hypergraph) {
    const HypernodeID current_num_nodes =
      hypergraph.initialNumNodes() - hypergraph.numRemovedHypernodes();
    HypernodeID num_removed_degree_zero_hypernodes = 0;
    for ( const HypernodeID& hn : hypergraph.nodes()  ) {
      if ( current_num_nodes - num_removed_degree_zero_hypernodes <= _context.coarsening.contraction_limit) {
        break;
      }
      if ( hypergraph.nodeDegree(hn) == 0 && !hypergraph.isFixed(hn) ) {
        hypergraph.removeDegreeZeroHypernode(hn);
        _removed_hns.push_back(hn);
        ++num_removed_degree_zero_hypernodes;
      }
    }
    return num_removed_degree_zero_hypernodes;
  }

  // ! Restore degree-zero vertices
  void restoreDegreeZeroHypernodes(PartitionedHypergraph& hypergraph) {
    // Sort degree-zero vertices in decreasing order of their weight
    tbb::parallel_sort(_removed_hns.begin(), _removed_hns.end(),
      [&](const HypernodeID& lhs, const HypernodeID& rhs) {
        return hypergraph.nodeWeight(lhs) > hypergraph.nodeWeight(rhs)
                || (hypergraph.nodeWeight(lhs) == hypergraph.nodeWeight(rhs) && lhs > rhs);
      });
    // Sort blocks of partition in increasing order of their weight
    auto distance_to_max = [&](const PartitionID block) {
      if (!_context.partition.allow_empty_blocks && hypergraph.partWeight(block) == 0) {
        // repairing empty blocks gets highest priority
        return -(_context.partition.max_part_weights[block] + hypergraph.totalWeight());
      } else {
        return hypergraph.partWeight(block) - _context.partition.max_part_weights[block];
      }
    };
    parallel::scalable_vector<PartitionID> blocks(_context.partition.k, 0);
    std::iota(blocks.begin(), blocks.end(), 0);
    std::sort(blocks.begin(), blocks.end(),
      [&](const PartitionID& lhs, const PartitionID& rhs) {
        return distance_to_max(lhs) < distance_to_max(rhs);
      });

    // Perform Bin-Packing
    for ( const HypernodeID& hn : _removed_hns ) {
      PartitionID to = blocks.front();
      hypergraph.restoreDegreeZeroHypernode(hn, to);
      PartitionID i = 0;
      while ( i + 1 < _context.partition.k &&
              distance_to_max(blocks[i]) > distance_to_max(blocks[i + 1]) ) {
        std::swap(blocks[i], blocks[i + 1]);
        ++i;
      }
    }
    _removed_hns.clear();
  }

 private:
  const Context& _context;
  parallel::scalable_vector<HypernodeID> _removed_hns;
};

}  // namespace mt_kahypar
