/*******************************************************************************
 * MIT License
 *
 * This file is part of Mt-KaHyPar.
 *
 * Copyright (C) 2021 Tobias Heuer <tobias.heuer@kit.edu>
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

#pragma once

#include <tbb/concurrent_queue.h>
#include <tbb/concurrent_vector.h>
#include <tbb/enumerable_thread_specific.h>

#include "mt-kahypar/partition/context.h"
#include "mt-kahypar/parallel/atomic_wrapper.h"
#include "mt-kahypar/utils/randomize.h"

namespace mt_kahypar {

struct BlockPair {
  BlockPair() = default;

  BlockPair(PartitionID i, PartitionID j): i(i), j(j) {
    ASSERT(i < j);
  }

  PartitionID i = kInvalidPartition;
  PartitionID j = kInvalidPartition;
};


// ! Represents an edge of the quotient graph
struct QuotientGraphEdge {
  QuotientGraphEdge() :
    blocks(),
    ownership(false),
    is_in_queue(false),
    cut_hes(),
    cut_he_weight(0),
    num_improvements_found(0),
    total_improvement(0) { }

  // ! Adds a cut hyperedge to this quotient graph edge
  void addHyperedge(const HyperedgeID he, const HyperedgeWeight weight);

  void reset();

  // ! Positive sign means improvement
  void reportImprovement(const HyperedgeWeight delta) {
    if (delta > 0) {
      num_improvements_found.fetch_add(1, std::memory_order_relaxed);
      total_improvement.fetch_add(delta, std::memory_order_relaxed);
    }
  }

  // ! Returns true, if quotient graph edge is acquired by a search
  bool isAcquired() const {
    return ownership.load(std::memory_order_relaxed);
  }

  // ! Tries to acquire quotient graph edge
  bool acquire() {
    bool expected = false;
    return ownership.compare_exchange_strong(expected, true, std::memory_order_acquire);
  }

  // ! Releases quotient graph edge
  void release() {
    ASSERT(isAcquired());
    ownership.store(false, std::memory_order_release);
  }

  bool isInQueue() const {
    return is_in_queue.load(std::memory_order_relaxed);
  }

  // ! Marks quotient graph edge as in queue. Queued edges are scheduled
  // ! for refinement.
  bool markAsInQueue() {
    bool expected = false;
    bool desired = true;
    return is_in_queue.compare_exchange_strong(expected, desired);
  }

  // ! Marks quotient graph edge as not in queue
  bool markAsNotInQueue() {
    bool expected = true;
    bool desired = false;
    return is_in_queue.compare_exchange_strong(expected, desired);
  }

  HyperedgeWeight weightOfCutHyperedges() const {
    return cut_he_weight.load(std::memory_order_relaxed);
  }

  HyperedgeWeight numImprovementsFound() const {
    return num_improvements_found.load(std::memory_order_relaxed);
  }

  HyperedgeWeight totalImprovement() const {
    return total_improvement.load(std::memory_order_relaxed);
  }

  // ! Block pair this quotient graph edge represents
  BlockPair blocks;
  // ! Ture, if there is an active search on this block pair
  CAtomic<bool> ownership;
  // ! True, if block is contained in block scheduler queue
  CAtomic<bool> is_in_queue;
  // ! Cut hyperedges of block pair
  tbb::concurrent_vector<HyperedgeID> cut_hes;
  // ! Current weight of all cut hyperedges
  CAtomic<HyperedgeWeight> cut_he_weight;
  // ! Number of improvements found on this block pair
  CAtomic<size_t> num_improvements_found;
  // ! Total improvement found on this block pair
  CAtomic<HyperedgeWeight> total_improvement;
};


class QuotientGraph {

  static constexpr bool debug = false;
  static constexpr bool enable_heavy_assert = false;

public:
  explicit QuotientGraph(const HyperedgeID num_hyperedges, const Context& context);

  QuotientGraph(const QuotientGraph&) = delete;
  QuotientGraph(QuotientGraph&&) = delete;

  QuotientGraph & operator= (const QuotientGraph &) = delete;
  QuotientGraph & operator= (QuotientGraph &&) = delete;

  QuotientGraphEdge& edge(const BlockPair& blocks) {
    ASSERT(blocks.i < blocks.j);
    ASSERT(0 <= blocks.i && static_cast<size_t>(blocks.i) < _quotient_graph.size());
    ASSERT(0 <= blocks.j && static_cast<size_t>(blocks.j) < _quotient_graph[blocks.i].size());
    return _quotient_graph[blocks.i][blocks.j];
  }

  const QuotientGraphEdge& edge(const BlockPair& blocks) const {
    ASSERT(blocks.i < blocks.j);
    ASSERT(0 <= blocks.i && static_cast<size_t>(blocks.i) < _quotient_graph.size());
    ASSERT(0 <= blocks.j && static_cast<size_t>(blocks.j) < _quotient_graph[blocks.i].size());
    return _quotient_graph[blocks.i][blocks.j];
  }

  /**
   * Notifies the quotient graph that hyperedge he contains a new
   * block, which was previously not contained. Might be called directly
   * by the thread that increases the pin count of the hyperedges to 1,
   * or in bulk after multiple flow computations are processed.
   */
  template<typename PartitionedHypergraph>
  void addNewCutHyperedge(const PartitionedHypergraph& phg, HyperedgeID he, PartitionID block);

  // ! Initializes the quotient graph. This includes to find
  // ! all cut hyperedges between all block pairs
  template<typename PartitionedHypergraph>
  void initialize(const PartitionedHypergraph& phg);

  void changeNumberOfBlocks(const PartitionID new_k);

  bool isInputHypergraph() const;

 private:
  HypernodeID _initial_num_edges;
  HypernodeID _current_num_edges;

  // ! Each edge contains stats and the cut hyperedges
  // ! of the block pair which its represents.
  vec<vec<QuotientGraphEdge>> _quotient_graph;
};

}  // namespace kahypar
