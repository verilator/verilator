/*******************************************************************************
 * MIT License
 *
 * This file is part of Mt-KaHyPar.
 *
 * Copyright (C) 2020 Lars Gottesbüren <lars.gottesbueren@kit.edu>
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

#include <tbb/parallel_for.h>

#include "mt-kahypar/parallel/stl/scalable_vector.h"
#include "mt-kahypar/parallel/atomic_wrapper.h"
#include "mt-kahypar/datastructures/array.h"
#include "mt-kahypar/utils/memory_tree.h"
#include "mt-kahypar/datastructures/hypergraph_common.h"
#include "mt-kahypar/utils/range.h"

namespace mt_kahypar {
namespace ds {

// Represents a uncontraction that is assigned to a certain batch
// and within that batch to a certain position.
struct BatchAssignment {
  HypernodeID u;
  HypernodeID v;
  size_t batch_index;
  size_t batch_pos;
};

/*!
  * Helper class that synchronizes assignements of uncontractions
  * to batches. A batch has a certain maximum allowed batch size. The
  * class provides functionality to compute such an assignment in a
  * thread-safe manner. Several threads can request a batch index
  * and a position within that batch for its uncontraction it wants
  * to assign. The class guarantees that each combination of
  * (batch_index, batch_position) is unique and consecutive.
  * Furthermore, it is ensured that batch_position is always
  * smaller than max_batch_size.
  */
class BatchIndexAssigner {

  using AtomicCounter = parallel::IntegralAtomicWrapper<size_t>;

  public:
  explicit BatchIndexAssigner(const HypernodeID num_hypernodes,
                              const size_t max_batch_size) :
    _max_batch_size(max_batch_size),
    _high_water_mark(0),
    _current_batch_counter(num_hypernodes, AtomicCounter(0)),
    _current_batch_sizes(num_hypernodes, AtomicCounter(0)) { }

  BatchAssignment getBatchIndex(const size_t min_required_batch,
                                const size_t num_uncontractions = 1) {
    if ( min_required_batch <= _high_water_mark ) {
      size_t current_high_water_mark = _high_water_mark.load();
      const BatchAssignment assignment = findBatchAssignment(
        current_high_water_mark, num_uncontractions);

      // Update high water mark in case batch index is greater than
      // current high water mark
      size_t current_batch_index = assignment.batch_index;
      increaseHighWaterMark(current_batch_index);
      return assignment;
    } else {
      return findBatchAssignment(min_required_batch, num_uncontractions);
    }
  }

  size_t batchSize(const size_t batch_index) const {
    ASSERT(batch_index < _current_batch_sizes.size());
    return _current_batch_sizes[batch_index];
  }

  void increaseHighWaterMark(size_t new_high_water_mark) {
    size_t current_high_water_mark = _high_water_mark.load();
    while ( new_high_water_mark > current_high_water_mark ) {
      _high_water_mark.compare_exchange_strong(
        current_high_water_mark, new_high_water_mark);
    }
  }

  size_t numberOfNonEmptyBatches() {
    size_t current_batch = _high_water_mark;
    if ( _current_batch_sizes[_high_water_mark] == 0 )  {
      while ( current_batch > 0 && _current_batch_sizes[current_batch] == 0 ) {
        --current_batch;
      }
      if ( _current_batch_sizes[current_batch] > 0 ) {
        ++current_batch;
      }
    } else {
      while ( _current_batch_sizes[current_batch] > 0 ) {
        ++current_batch;
      }
    }
    return current_batch;
  }

  void reset(const size_t num_batches) {
    ASSERT(num_batches <= _current_batch_sizes.size());
    _high_water_mark = 0;
    tbb::parallel_for(UL(0), num_batches, [&](const size_t i) {
      _current_batch_counter[i] = 0;
      _current_batch_sizes[i] = 0;
    });
  }

  private:
  BatchAssignment findBatchAssignment(const size_t start_batch_index,
                                      const size_t num_uncontractions) {
    size_t current_batch_index = start_batch_index;
    size_t batch_pos = _current_batch_counter[current_batch_index].fetch_add(
      num_uncontractions, std::memory_order_relaxed);
    // Search for batch in which atomic update of the batch counter
    // return a position smaller than max_batch_size.
    while ( batch_pos >= _max_batch_size ) {
      ++current_batch_index;
      ASSERT(current_batch_index < _current_batch_counter.size());
      batch_pos = _current_batch_counter[current_batch_index].fetch_add(
        num_uncontractions, std::memory_order_relaxed);
    }
    ASSERT(batch_pos < _max_batch_size);
    _current_batch_sizes[current_batch_index] += num_uncontractions;
    return BatchAssignment { kInvalidHypernode,
      kInvalidHypernode, current_batch_index, batch_pos };
  }

  const size_t _max_batch_size;
  AtomicCounter _high_water_mark;
  parallel::scalable_vector<AtomicCounter> _current_batch_counter;
  parallel::scalable_vector<AtomicCounter> _current_batch_sizes;
};

class ContractionTree {

  static constexpr bool debug = false;
  static constexpr bool enable_heavy_assert = false;
  static constexpr size_t kInvalidVersion = std::numeric_limits<size_t>::max();

  using Timepoint = HypernodeID;

 public:
  struct Interval {
    explicit Interval() :
      start(kInvalidHypernode),
      end(kInvalidHypernode) { }

    Timepoint start;
    Timepoint end;
  };

 private:
  /**
   * Represents a node in contraction tree and contains all information
   * associated with that node.
   */
  class Node {
    public:
      Node() :
        _parent(0),
        _pending_contractions(0),
        _subtree_size(0),
        _version(kInvalidVersion),
        _interval() { }

      inline HypernodeID parent() const {
        return _parent;
      }

      inline void setParent(const HypernodeID parent) {
        _parent = parent;
      }

      inline HypernodeID pendingContractions() const {
        return _pending_contractions;
      }

      inline void incrementPendingContractions() {
        ++_pending_contractions;
      }

      inline void decrementPendingContractions() {
        --_pending_contractions;
      }

      inline HypernodeID subtreeSize() const {
        return _subtree_size;
      }

      inline void setSubtreeSize(const HypernodeID subtree_size) {
        _subtree_size = subtree_size;
      }

      inline size_t version() const {
        return _version;
      }

      inline void setVersion(const size_t version) {
        _version = version;
      }

      inline Interval interval() const {
        return _interval;
      }

      inline void setInterval(const Timepoint start, const Timepoint end) {
        ASSERT(start < end);
        _interval.start = start;
        _interval.end = end;
      }

      inline void reset(const HypernodeID u) {
        _parent = u;
        _pending_contractions = 0;
        _subtree_size = 0;
        _version = kInvalidVersion;
        _interval.start = kInvalidHypernode;
        _interval.end = kInvalidHypernode;
      }

    private:
      // ! Parent in the contraction tree
      HypernodeID _parent;
      // ! Number of pending contractions
      HypernodeID _pending_contractions;
      // ! Size of the subtree
      HypernodeID _subtree_size;
      // ! Version number of the hypergraph for which contract the corresponding vertex
      size_t _version;
      // ! "Time" interval on which the contraction of this node takes place
      Interval _interval;
  };

  static_assert(std::is_trivially_copyable<Node>::value, "Node is not trivially copyable");

 public:
  // ! Iterator to iterate over the childs of a tree node
  using ChildIterator = typename parallel::scalable_vector<HypernodeID>::const_iterator;

  explicit ContractionTree() :
    _num_hypernodes(0),
    _finalized(false),
    _tree(),
    _roots(),
    _version_roots(),
    _out_degrees(),
    _incidence_array() { }

  ContractionTree(ContractionTree&& other) :
    _num_hypernodes(other._num_hypernodes),
    _finalized(other._finalized),
    _tree(std::move(other._tree)),
    _roots(std::move(other._roots)),
    _version_roots(std::move(other._version_roots)),
    _out_degrees(std::move(other._out_degrees)),
    _incidence_array(std::move(other._incidence_array)) { }

  ContractionTree& operator= (ContractionTree&& other) {
    _num_hypernodes = other._num_hypernodes;
    _finalized = other._finalized;
    _tree = std::move(other._tree);
    _roots = std::move(other._roots);
    _version_roots = std::move(other._version_roots);
    _out_degrees = std::move(other._out_degrees);
    _incidence_array = std::move(other._incidence_array);
    return *this;
  }

  ~ContractionTree() {
    freeInternalData();
  }

  // ####################### Tree Node Information #######################

  HypernodeID num_hypernodes() const {
    return _num_hypernodes;
  }

  // ! Returns the parent of node u
  MT_KAHYPAR_ATTRIBUTE_ALWAYS_INLINE HypernodeID parent(const HypernodeID u) const {
    return node(u).parent();
  }

  // ! Number of pending contractions of node u
  MT_KAHYPAR_ATTRIBUTE_ALWAYS_INLINE HypernodeID pendingContractions(const HypernodeID u) const {
    return node(u).pendingContractions();
  }

  // ! Subtree size of node u
  HypernodeID subtreeSize(const HypernodeID u) const {
    ASSERT(_finalized, "Information currently not available");
    return node(u).subtreeSize();
  }


  size_t version(const HypernodeID u) const {
    ASSERT(u < _num_hypernodes, "Hypernode" << u << "does not exist");
    return _tree[u].version();
  }

  // ! Degree/Number of childs of node u
  HypernodeID degree(const HypernodeID u) const {
    ASSERT(_finalized, "Information currently not available");
    ASSERT(u < _num_hypernodes, "Hypernode" << u << "does not exist");
    return _out_degrees[u + 1] - _out_degrees[u];
  }

  const parallel::scalable_vector<HypernodeID>& roots() const {
    return _roots;
  }

  const parallel::scalable_vector<HypernodeID>& roots_of_version(const size_t version) const {
    ASSERT(version < _version_roots.size());
    return _version_roots[version];
  }

  Interval interval(const HypernodeID u) const {
    ASSERT(u < _num_hypernodes, "Hypernode" << u << "does not exist");
    return node(u).interval();
  }

  // ####################### Iterators #######################

  // ! Returns a range to loop over the childs of a tree node u.
  IteratorRange<ChildIterator> childs(const HypernodeID u) const {
    ASSERT(_finalized, "Information currently not available");
    ASSERT(u < _num_hypernodes, "Hypernode" << u << "does not exist");
    return IteratorRange<ChildIterator>(
      _incidence_array.cbegin() + _out_degrees[u],
      _incidence_array.cbegin() + _out_degrees[u + 1]);
  }

  // ! Calls function f for each child of vertex u with the corresponding version
  template<typename F>
  void doForEachChildOfVersion(const HypernodeID u, const size_t version, const F& f) const {
    ASSERT(_finalized, "Information currently not available");
    ASSERT(u < _num_hypernodes, "Hypernode" << u << "does not exist");
    for ( const HypernodeID& v : childs(u) ) {
      if ( _tree[v].version() == version ) {
        f(v);
      }
    }
  }

  // ####################### Contraction Functions #######################

  // ! Registers a contraction in the contraction tree
  void registerContraction(const HypernodeID u, const HypernodeID v, const size_t version = 0) {
    node(u).incrementPendingContractions();
    node(v).setParent(u);
    node(v).setVersion(version);
  }

  template<typename A, typename R>
  bool registerContraction(const HypernodeID u, const HypernodeID v, const size_t version, A acquire, R release) {
    // Acquires ownership of vertex v that gives the calling thread exclusive rights
    // to modify the contraction tree entry of v
    acquire(v);

    // If there is no other contraction registered for vertex v
    // we try to determine its representative in the contraction tree
    if ( parent(v) == v ) {

      HypernodeID w = u;
      bool cycle_detected = false;
      while ( true ) {
        // Search for representative of u in the contraction tree.
        // It is either a root of the contraction tree or a vertex
        // with a reference count greater than zero, which indicates
        // that there are still ongoing contractions on this node that
        // have to be processed.
        while ( parent(w) != w && pendingContractions(w) == 0 ) {
          w = parent(w);
          if ( w == v ) {
            cycle_detected = true;
            break;
          }
        }

        if ( !cycle_detected ) {
          // In case contraction of u and v does not induce any
          // cycle in the contraction tree we try to acquire vertex w
          if ( w < v ) {
            // Acquire ownership in correct order to prevent deadlocks
            release(v);
            acquire(w);
            acquire(v);
            if ( parent(v) != v ) {
              release(v);
              release(w);
              return false;
            }
          } else {
            acquire(w);
          }

          // Double-check condition of while loop above after acquiring
          // ownership of w
          if ( parent(w) != w && pendingContractions(w) == 0 ) {
            // In case something changed, we release ownership of w and
            // search again for the representative of u.
            release(w);
          } else {
            // Otherwise we perform final cycle check to verify that
            // contraction of u and v will not introduce any new cycle.
            HypernodeID x = w;
            do {
              x = parent(x);
              if ( x == v ) {
                cycle_detected = true;
                break;
              }
            } while ( parent(x) != x );

            if ( cycle_detected ) {
              release(w);
              release(v);
              return false;
            }

            // All checks succeded, we can safely increment the
            // reference count of w and update the contraction tree
            break;
          }
        } else {
          release(v);
          return false;
        }
      }

      // Increment reference count of w indicating that there pending
      // contraction at vertex w and update contraction tree.
      registerContraction(w, v, version);

      release(w);
      release(v);
      return true;
    } else {
      release(v);
      return false;
    }
  }

  // ! Unregisters a contraction in the contraction tree
  void unregisterContraction(const HypernodeID u, const HypernodeID v,
                             const Timepoint start, const Timepoint end,
                             const bool failed = false) {
    ASSERT(node(v).parent() == u, "Node" << u << "is not parent of node" << v);
    ASSERT(node(u).pendingContractions() > 0, "There are no pending contractions for node" << u);
    node(u).decrementPendingContractions();
    if ( failed ) {
      node(v).setParent(v);
      node(v).setVersion(kInvalidVersion);
    } else {
      node(v).setInterval(start, end);
    }
  }

  BatchVector createBatchUncontractionHierarchyForVersion(BatchIndexAssigner& batch_assigner,
                                                          const size_t version);

  // ! Only for testing
  void setParent(const HypernodeID u, const HypernodeID v, const size_t version = 0) {
    node(u).setParent(v);
    node(u).setVersion(version);
  }


  // ! Only for testing
  void decrementPendingContractions(const HypernodeID u) {
    node(u).decrementPendingContractions();
  }

  // ####################### Initialize / Finalize #######################

  // ! Initializes the data structure in parallel
  void initialize(const HypernodeID num_hypernodes);

  // ! Finalizes the contraction tree which involve reversing the parent pointers
  // ! such that the contraction tree can be traversed in a top-down fashion and
  // ! computing the subtree sizes.
  void finalize(const size_t num_versions = 1);

  // ####################### Copy #######################

  // ! Copy contraction tree in parallel
  ContractionTree copy(parallel_tag_t) const;

  // ! Copy contraction tree sequentially
  ContractionTree copy() const;

  // ! Resets internal data structures
  void reset();

  // ! Free internal data in parallel
  void freeInternalData();

  void memoryConsumption(utils::MemoryTreeNode* parent) const;

 private:
  // ! Accessor for contraction tree-related information
  MT_KAHYPAR_ATTRIBUTE_ALWAYS_INLINE const Node& node(const HypernodeID u) const {
    ASSERT(u < _num_hypernodes, "Hypernode" << u << "does not exist");
    return _tree[u];
  }

  // ! To avoid code duplication we implement non-const version in terms of const version
  MT_KAHYPAR_ATTRIBUTE_ALWAYS_INLINE Node& node(const HypernodeID u) {
    return const_cast<Node&>(static_cast<const ContractionTree&>(*this).node(u));
  }

  bool verifyBatchIndexAssignments(
    const BatchIndexAssigner& batch_assigner,
    const parallel::scalable_vector<parallel::scalable_vector<BatchAssignment>>& local_batch_assignments) const;

  HypernodeID _num_hypernodes;
  bool _finalized;
  parallel::scalable_vector<Node> _tree;
  parallel::scalable_vector<HypernodeID> _roots;
  parallel::scalable_vector<parallel::scalable_vector<HypernodeID>> _version_roots;
  parallel::scalable_vector<parallel::IntegralAtomicWrapper<HypernodeID>> _out_degrees;
  parallel::scalable_vector<HypernodeID> _incidence_array;
};

}  // namespace ds
}  // namespace mt_kahypar
