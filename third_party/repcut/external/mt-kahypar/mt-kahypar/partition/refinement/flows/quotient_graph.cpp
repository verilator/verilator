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


#include "mt-kahypar/partition/refinement/flows/quotient_graph.h"

#include <queue>

#include <tbb/parallel_sort.h>

#include "mt-kahypar/definitions.h"
#include "mt-kahypar/datastructures/sparse_map.h"


namespace mt_kahypar {

void QuotientGraphEdge::addHyperedge(const HyperedgeID he, const HyperedgeWeight weight) {
  cut_hes.push_back(he);
  cut_he_weight.fetch_add(weight, std::memory_order_relaxed);
}

void QuotientGraphEdge::reset() {
  cut_hes.clear();
  ownership.store(false, std::memory_order_relaxed);
  is_in_queue.store(false, std::memory_order_relaxed);
  cut_he_weight.store(0, std::memory_order_relaxed);
}


QuotientGraph::QuotientGraph(const HyperedgeID num_hyperedges, const Context& context) :
  _initial_num_edges(num_hyperedges),
  _current_num_edges(kInvalidHyperedge),
  _quotient_graph(context.partition.k,
    vec<QuotientGraphEdge>(context.partition.k)) {
  for ( PartitionID i = 0; i < context.partition.k; ++i ) {
    for ( PartitionID j = i + 1; j < context.partition.k; ++j ) {
      _quotient_graph[i][j].blocks.i = i;
      _quotient_graph[i][j].blocks.j = j;
    }
  }
}

template<typename PartitionedHypergraph>
void QuotientGraph::addNewCutHyperedge(const PartitionedHypergraph& phg, HyperedgeID he, PartitionID block) {
  ASSERT(block != kInvalidPartition);
  // assertion might not hold due to race condition between flow computations
  // ASSERT(phg.pinCountInPart(he, block) > 0);

  // Add hyperedge he as a cut hyperedge to each block pair that contains 'block'.
  // Note, hyperedges might be added twice to a block pair or might be wrongly added
  // to a block pair (due to races). This should not be a problem in practice since
  // adding new hyperedges is rare, the BFS deduplicates the hyperedges anyways and
  // additional edges only increase the size of the flow problem.
  for ( const PartitionID& other_block : phg.connectivitySet(he) ) {
    if ( other_block != block ) {
      _quotient_graph[std::min(block, other_block)][std::max(block, other_block)]
        .addHyperedge(he, phg.edgeWeight(he));
    }
  }
}

template<typename PartitionedHypergraph>
void QuotientGraph::initialize(const PartitionedHypergraph& phg) {
  // Reset quotient graph edges
  for ( size_t i = 0; i < _quotient_graph.size(); ++i ) {
    for ( size_t j = i + 1; j < _quotient_graph[i].size(); ++j ) {
      _quotient_graph[i][j].reset();
    }
  }

  // Find all cut hyperedges between the blocks
  tbb::enumerable_thread_specific<HyperedgeID> local_num_hes(0);
  phg.doParallelForAllEdges([&](const HyperedgeID he) {
    ++local_num_hes.local();
    const HyperedgeWeight edge_weight = phg.edgeWeight(he);
    for ( const PartitionID i : phg.connectivitySet(he) ) {
      for ( const PartitionID j : phg.connectivitySet(he) ) {
        if ( i < j ) {
          _quotient_graph[i][j].addHyperedge(he, edge_weight);
        }
      }
    }
  });
  _current_num_edges = local_num_hes.combine(std::plus<HyperedgeID>());
}

void QuotientGraph::changeNumberOfBlocks(const PartitionID new_k) {
  // Reset improvement history as the number of blocks had changed
  for ( size_t i = 0; i < _quotient_graph.size(); ++i ) {
    for ( size_t j = 0; j < _quotient_graph.size(); ++j ) {
      _quotient_graph[i][j].num_improvements_found.store(0, std::memory_order_relaxed);
      _quotient_graph[i][j].total_improvement.store(0, std::memory_order_relaxed);
    }
  }

  if ( static_cast<size_t>(new_k) > _quotient_graph.size() ) {
    _quotient_graph.clear();
    _quotient_graph.assign(new_k, vec<QuotientGraphEdge>(new_k));
  }
}

bool QuotientGraph::isInputHypergraph() const {
  return _current_num_edges == _initial_num_edges;
}


namespace {
#define ADD_NEW_CUT_HYPEREDGE(X) void QuotientGraph::addNewCutHyperedge(const X& phg, HyperedgeID he, PartitionID block)
#define INITIALIZE(X) void QuotientGraph::initialize(const X& phg)
}

INSTANTIATE_FUNC_WITH_PARTITIONED_HG(ADD_NEW_CUT_HYPEREDGE)
INSTANTIATE_FUNC_WITH_PARTITIONED_HG(INITIALIZE)

} // namespace mt_kahypar
