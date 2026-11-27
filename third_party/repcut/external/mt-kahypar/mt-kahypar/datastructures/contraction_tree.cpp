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

#include "mt-kahypar/datastructures/contraction_tree.h"

#include <queue>

#include <tbb/parallel_reduce.h>
#include <tbb/parallel_invoke.h>
#include <tbb/enumerable_thread_specific.h>

#include "mt-kahypar/parallel/parallel_prefix_sum.h"
#include "mt-kahypar/datastructures/streaming_vector.h"
#include "mt-kahypar/utils/timer.h"

namespace mt_kahypar {
namespace ds {

// ! Initializes the data structure in parallel
void ContractionTree::initialize(const HypernodeID num_hypernodes) {
  _num_hypernodes = num_hypernodes;
  tbb::parallel_invoke([&] {
    _tree.resize(_num_hypernodes);
    tbb::parallel_for(ID(0), _num_hypernodes, [&](const HypernodeID hn) {
      node(hn).setParent(hn);
    });
  }, [&] {
    _out_degrees.assign(_num_hypernodes + 1, parallel::IntegralAtomicWrapper<HypernodeID>(0));
  }, [&] {
    _incidence_array.resize(_num_hypernodes);
  });
}

// ! Finalizes the contraction tree which involve reversing the parent pointers
// ! such that the contraction tree can be traversed in a top-down fashion and
// ! computing the subtree sizes.
void ContractionTree::finalize(const size_t num_versions) {
  ASSERT(!_finalized, "Contraction tree already finalized");
  // Compute out degrees of each tree node
  tbb::parallel_for(ID(0), _num_hypernodes, [&](const HypernodeID hn) {
    ASSERT(node(hn).pendingContractions() == 0, "There are"
      << node(hn).pendingContractions() << "pending contractions for node" << hn);
    const HypernodeID parent = node(hn).parent();
    if ( parent != hn ) {
      ASSERT(parent + 1 <= _num_hypernodes, "Parent" << parent << "does not exist!");
      ++_out_degrees[parent + 1];
    }
  });

  // Compute prefix sum over out degrees which will be the index pointer into the incidence array
  parallel::scalable_vector<parallel::IntegralAtomicWrapper<HypernodeID>> incidence_array_pos;
  parallel::TBBPrefixSum<parallel::IntegralAtomicWrapper<HypernodeID>, parallel::scalable_vector>
    out_degree_prefix_sum(_out_degrees);
  tbb::parallel_invoke([&] {
    tbb::parallel_scan(tbb::blocked_range<size_t>(UL(0), _out_degrees.size()), out_degree_prefix_sum);
  }, [&] {
    incidence_array_pos.assign(_num_hypernodes, parallel::IntegralAtomicWrapper<HypernodeID>(0));
  });

  // Reverse parent pointer of contraction tree such that it can be traversed in top-down fashion
  StreamingVector<HypernodeID> tmp_roots;
  tbb::parallel_for(ID(0), _num_hypernodes, [&](const HypernodeID hn) {
    const HypernodeID parent = node(hn).parent();
    if ( parent != hn ) {
      const HypernodeID pos = _out_degrees[parent] + incidence_array_pos[parent]++;
      ASSERT(pos < _out_degrees[parent + 1]);
      _incidence_array[pos] = hn;
    } else {
      // In that case node hn is a root
      const bool contains_subtree = (_out_degrees[hn + 1] - _out_degrees[hn]) > 0;
      if ( contains_subtree ) {
        tmp_roots.stream(hn);
      }
    }
  });
  _roots = tmp_roots.copy_parallel();

  _finalized = true;

  // Compute roots for each version
  // Each contraction/edge in the contraction tree is associated with a version.
  // Later we want to be able to traverse the contraction tree for a specific version
  // in a top-down fashion. Therefore, we compute for each version the corresponding roots.
  // A vertex is a root of a version if contains a child with that version less than
  // the version number of the vertex itself. Note, that for all vertices in the contraction
  // tree version(u) <= version(parent(u)).
  parallel::scalable_vector<StreamingVector<HypernodeID>> tmp_version_roots(num_versions);
  tbb::parallel_for(ID(0), _num_hypernodes, [&](const HypernodeID u) {
    std::sort(_incidence_array.begin() + _out_degrees[u],
              _incidence_array.begin() + _out_degrees[u + 1],
              [&](const HypernodeID& u, const HypernodeID& v) {
                const size_t u_version = version(u);
                const size_t v_version = version(v);
                const Interval& u_ival = node(u).interval();
                const Interval& v_ival = node(v).interval();
                return u_version < v_version ||
                  ( u_version == v_version && u_ival.end > v_ival.end ) ||
                  ( u_version == v_version && u_ival.end == v_ival.end && u_ival.start > v_ival.start ) ||
                  ( u_version == v_version && u_ival.end == v_ival.end && u_ival.start == v_ival.start && u < v );
              });

    size_t version_u = _tree[u].version();
    ASSERT(version_u <= _tree[_tree[u].parent()].version());
    size_t last_version = kInvalidVersion;
    for ( const HypernodeID& v : childs(u) ) {
      size_t version_v = _tree[v].version();
      ASSERT(version_v < num_versions, V(version_v) << V(num_versions));
      if ( version_v != last_version && version_v < version_u ) {
        tmp_version_roots[version_v].stream(u);
      }
      last_version = version_v;
    }
  });
  _version_roots.resize(num_versions);
  tbb::parallel_for(UL(0), num_versions, [&](const size_t i) {
    _version_roots[i] = tmp_version_roots[i].copy_parallel();
    tmp_version_roots[i].clear_parallel();
  });

  // Compute subtree sizes of each root in parallel via dfs
  tbb::parallel_for(UL(0), _roots.size(), [&](const size_t i) {
    parallel::scalable_vector<HypernodeID> dfs;
    dfs.push_back(_roots[i]);
    while( !dfs.empty() ) {
      const HypernodeID u = dfs.back();
      if ( subtreeSize(u) == 0 ) {
        // Visit u for the first time => push all childs on the dfs stack
        for ( const HypernodeID& v : childs(u)) {
          dfs.push_back(v);
        }
        // Mark u as visited
        node(u).setSubtreeSize(1);
      } else {
        // Visit u for second time => accumulate subtree sizes and pop u
        dfs.pop_back();
        HypernodeID subtree_size = 0;
        for ( const HypernodeID& v : childs(u) ) {
          subtree_size += ( subtreeSize(v) + 1 );
        }
        node(u).setSubtreeSize(subtree_size);
      }
    }
  });

  tbb::parallel_invoke([&] {
    parallel::free(incidence_array_pos);
  }, [&] {
    tmp_roots.clear_parallel();
  });
}

// ####################### Copy #######################

// ! Copy contraction tree in parallel
ContractionTree ContractionTree::copy(parallel_tag_t) const {
  ContractionTree tree;

  tree._num_hypernodes = _num_hypernodes;
  tree._finalized = _finalized;

  tbb::parallel_invoke([&] {
    if (!_tree.empty()) {
      tree._tree.resize(_tree.size());
      memcpy(tree._tree.data(), _tree.data(), sizeof(Node) * _tree.size());
    }
  }, [&] {
    if (!_roots.empty()) {
      tree._roots.resize(_roots.size());
      memcpy(tree._roots.data(), _roots.data(), sizeof(HypernodeID) * _roots.size());
    }
  }, [&] {
    const size_t num_versions = _version_roots.size();
    tree._version_roots.resize(num_versions);
    tbb::parallel_for(UL(0), num_versions, [&](const size_t i) {
      if (!_version_roots[i].empty()) {
        tree._version_roots[i].resize(_version_roots[i].size());
        memcpy(tree._version_roots[i].data(), _version_roots[i].data(),
               sizeof(HypernodeID) * _version_roots[i].size());
      }
    });
  }, [&] {
    tree._out_degrees.resize(_out_degrees.size());
    for ( size_t i = 0; i < _out_degrees.size(); ++i ) {
      tree._out_degrees[i] = _out_degrees[i];
    }
  }, [&] {
    if (!_incidence_array.empty()) {
      tree._incidence_array.resize(_incidence_array.size());
      memcpy(tree._incidence_array.data(), _incidence_array.data(),
             sizeof(HypernodeID) * _incidence_array.size());
    }
  });

  return tree;
}

// ! Copy contraction tree sequentially
ContractionTree ContractionTree::copy() const {
  ContractionTree tree;

  tree._num_hypernodes = _num_hypernodes;
  tree._finalized = _finalized;

  if (!_tree.empty()) {
    tree._tree.resize(_tree.size());
    memcpy(tree._tree.data(), _tree.data(), sizeof(Node) * _tree.size());
  }
  if (!_roots.empty()) {
    tree._roots.resize(_roots.size());
    memcpy(tree._roots.data(), _roots.data(), sizeof(HypernodeID) * _roots.size());
  }
  const size_t num_versions = _version_roots.size();
  tree._version_roots.resize(num_versions);
  for ( size_t i = 0; i < num_versions; ++i ) {
    if (!_version_roots[i].empty()) {
      tree._version_roots[i].resize(_version_roots[i].size());
      memcpy(tree._version_roots[i].data(), _version_roots[i].data(),
             sizeof(HypernodeID) * _version_roots[i].size());
    }
  }
  tree._out_degrees.resize(_out_degrees.size());
  for ( size_t i = 0; i < _out_degrees.size(); ++i ) {
    tree._out_degrees[i] = _out_degrees[i];
  }
  if (!_incidence_array.empty()) {
    tree._incidence_array.resize(_incidence_array.size());
    memcpy(tree._incidence_array.data(), _incidence_array.data(),
           sizeof(HypernodeID) * _incidence_array.size());
  }

  return tree;
}

// ! Resets internal data structures
void ContractionTree::reset() {
  tbb::parallel_invoke([&] {
    tbb::parallel_for(ID(0), _num_hypernodes, [&](const HypernodeID hn) {
      _tree[hn].reset(hn);
      _out_degrees[hn].store(0);
    });
    _out_degrees[_num_hypernodes].store(0);
  }, [&] {
    parallel::parallel_free(_version_roots);
    _roots.clear();
  });
  _finalized = false;
}

// ! Free internal data in parallel
void ContractionTree::freeInternalData() {
  if ( _num_hypernodes > 0 ) {
    parallel::parallel_free(_tree, _roots, _out_degrees, _incidence_array);
  }
  _num_hypernodes = 0;
  _finalized = false;
}

void ContractionTree::memoryConsumption(utils::MemoryTreeNode* parent) const {
  ASSERT(parent);

  parent->addChild("Tree Nodes", sizeof(Node) * _tree.size());
  parent->addChild("Roots", sizeof(HypernodeID) * _roots.size());
  parent->addChild("Out-Degrees", sizeof(HypernodeID) * _out_degrees.size());
  parent->addChild("Incidence Array", sizeof(HypernodeID) * _incidence_array.size());
}


using ContractionInterval = typename ContractionTree::Interval;
using ChildIterator = typename ContractionTree::ChildIterator;

struct PQBatchUncontractionElement {
  int64_t _objective;
  std::pair<ChildIterator, ChildIterator> _iterator;
};

struct PQElementComparator {
  bool operator()(const PQBatchUncontractionElement& lhs, const PQBatchUncontractionElement& rhs){
      return lhs._objective < rhs._objective;
  }
};

bool ContractionTree::verifyBatchIndexAssignments(
  const BatchIndexAssigner& batch_assigner,
  const parallel::scalable_vector<parallel::scalable_vector<BatchAssignment>>& local_batch_assignments) const {
  parallel::scalable_vector<BatchAssignment> assignments;
  for ( size_t i = 0; i < local_batch_assignments.size(); ++i ) {
    for ( const BatchAssignment& batch_assign : local_batch_assignments[i] ) {
      assignments.push_back(batch_assign);
    }
  }
  std::sort(assignments.begin(), assignments.end(),
    [&](const BatchAssignment& lhs, const BatchAssignment& rhs) {
      return lhs.batch_index < rhs.batch_index ||
        (lhs.batch_index == rhs.batch_index && lhs.batch_pos < rhs.batch_pos);
    });

  if ( assignments.size() > 0 ) {
    if ( assignments[0].batch_index != 0 || assignments[0].batch_pos != 0 ) {
      LOG << "First uncontraction should start at batch 0 at position 0"
          << V(assignments[0].batch_index) << V(assignments[0].batch_pos);
      return false;
    }

    for ( size_t i = 1; i < assignments.size(); ++i ) {
      if ( assignments[i - 1].batch_index == assignments[i].batch_index ) {
        if ( assignments[i - 1].batch_pos + 1 != assignments[i].batch_pos ) {
          LOG << "Batch positions are not consecutive"
              << V(i) << V(assignments[i - 1].batch_pos) << V(assignments[i].batch_pos);
          return false;
        }
      } else {
        if ( assignments[i - 1].batch_index + 1 != assignments[i].batch_index ) {
          LOG << "Batch indices are not consecutive"
              << V(i) << V(assignments[i - 1].batch_index) << V(assignments[i].batch_index);
          return false;
        }
        if ( assignments[i].batch_pos != 0 ) {
          LOG << "First uncontraction of each batch should start at position 0"
              << V(assignments[i].batch_pos);
          return false;
        }
        if ( assignments[i - 1].batch_pos + 1 != batch_assigner.batchSize(assignments[i - 1].batch_index) ) {
          LOG << "Position of last uncontraction in batch" << assignments[i - 1].batch_index
              << "does not match size of batch"
              << V(assignments[i - 1].batch_pos) << V(batch_assigner.batchSize(assignments[i - 1].batch_index));
          return false;
        }
      }
    }
  }

  return true;
}

BatchVector ContractionTree::createBatchUncontractionHierarchyForVersion(BatchIndexAssigner& batch_assigner,
                                                                         const size_t version) {

  using PQ = std::priority_queue<PQBatchUncontractionElement,
                                 parallel::scalable_vector<PQBatchUncontractionElement>,
                                 PQElementComparator>;

  // Checks if two contraction intervals intersect
  auto does_interval_intersect = [&](const ContractionInterval& i1, const ContractionInterval& i2) {
    if (i1.start == kInvalidHypernode || i2.start == kInvalidHypernode) {
      return false;
    }
    return (i1.start <= i2.end && i1.end >= i2.end) ||
            (i2.start <= i1.end && i2.end >= i1.end);
  };

  auto push_into_pq = [&](PQ& prio_q, const HypernodeID& u) {
    auto it = childs(u);
    auto current = it.begin();
    auto end = it.end();
    while ( current != end && this->version(*current) != version ) {
      ++current;
    }
    if ( current != end ) {
      prio_q.push(PQBatchUncontractionElement {
        subtreeSize(*current), std::make_pair(current, end) } );
    }
  };

  // Distribute roots of the contraction tree to local priority queues of
  // each thread.
  const size_t num_hardware_threads = std::thread::hardware_concurrency();
  parallel::scalable_vector<PQ> local_pqs(num_hardware_threads);
  const parallel::scalable_vector<HypernodeID>& roots = roots_of_version(version);
  tbb::parallel_for(UL(0), roots.size(), [&](const size_t i) {
    const int cpu_id = THREAD_ID;
    push_into_pq(local_pqs[cpu_id], roots[i]);
  });

  using LocalBatchAssignments = parallel::scalable_vector<BatchAssignment>;
  parallel::scalable_vector<LocalBatchAssignments> local_batch_assignments(num_hardware_threads);
  parallel::scalable_vector<size_t> local_batch_indices(num_hardware_threads, 0);
  tbb::parallel_for(UL(0), num_hardware_threads, [&](const size_t i) {
    size_t& current_batch_index = local_batch_indices[i];
    LocalBatchAssignments& batch_assignments = local_batch_assignments[i];
    PQ& pq = local_pqs[i];
    PQ next_pq;

    while ( !pq.empty() ) {
      // Iterator over the childs of a active vertex
      auto it = pq.top()._iterator;
      ASSERT(it.first != it.second);
      const HypernodeID v = *it.first;
      ASSERT(this->version(v) == version);
      pq.pop();

      const size_t start_idx = batch_assignments.size();
      size_t num_uncontractions = 1;
      const HypernodeID u = parent(v);
      batch_assignments.push_back(BatchAssignment { u, v, UL(0), UL(0) });
      // Push contraction partner into pq for the next BFS level
      push_into_pq(next_pq, v);

      // Insert all childs of u that intersect the contraction time interval of
      // (u,v) into the current batch
      ++it.first;
      ContractionInterval current_ival = interval(v);
      while ( it.first != it.second && this->version(*it.first) == version ) {
        const HypernodeID w = *it.first;
        const ContractionInterval w_ival = interval(w);
        if ( does_interval_intersect(current_ival, w_ival) ) {
          ASSERT(parent(w) == u);
          ++num_uncontractions;
          batch_assignments.push_back(BatchAssignment { u, w, UL(0), UL(0) });
          current_ival.start = std::min(current_ival.start, w_ival.start);
          current_ival.end = std::max(current_ival.end, w_ival.end);
          push_into_pq(next_pq, w);
        } else {
          break;
        }
        ++it.first;
      }

      // If there are still childs left of u, we push the iterator again into the
      // priority queue of the current BFS level.
      if ( it.first != it.second && this->version(*it.first) == version ) {
        pq.push(PQBatchUncontractionElement { subtreeSize(*it.first), it });
      }

      // Request batch index and its position within that batch
      BatchAssignment assignment = batch_assigner.getBatchIndex(
        current_batch_index, num_uncontractions);
      for ( size_t j = start_idx; j < start_idx + num_uncontractions; ++j ) {
        batch_assignments[j].batch_index = assignment.batch_index;
        batch_assignments[j].batch_pos = assignment.batch_pos + (j - start_idx);
      }
      current_batch_index = assignment.batch_index;

      if ( pq.empty() ) {
        std::swap(pq, next_pq);
        // Compute minimum batch index to which a thread assigned last.
        // Afterwards, transmit information to batch assigner to speed up
        // batch index computation.
        ++current_batch_index;
        size_t min_batch_index = current_batch_index;
        for ( const size_t& batch_index : local_batch_indices ) {
          min_batch_index = std::min(min_batch_index, batch_index);
        }
        batch_assigner.increaseHighWaterMark(min_batch_index);
      }
    }
  });

  ASSERT(verifyBatchIndexAssignments(batch_assigner, local_batch_assignments), "Batch asisignment failed");

  // In the previous step we have calculated for each uncontraction a batch index and
  // its position within that batch. We have to write the uncontractions
  // into the global batch uncontraction vector.
  const size_t num_batches = batch_assigner.numberOfNonEmptyBatches();
  BatchVector batches(num_batches);
  tbb::parallel_for(UL(0), num_batches, [&](const size_t batch_index) {
    batches[batch_index].resize(batch_assigner.batchSize(batch_index));
  });

  tbb::parallel_for(UL(0), num_hardware_threads, [&](const size_t i) {
    LocalBatchAssignments& batch_assignments = local_batch_assignments[i];
    for ( const BatchAssignment& batch_assignment : batch_assignments ) {
      const size_t batch_index = batch_assignment.batch_index;
      const size_t batch_pos = batch_assignment.batch_pos;
      ASSERT(batch_index < batches.size());
      ASSERT(batch_pos < batches[batch_index].size());
      batches[batch_index][batch_pos].u = batch_assignment.u;
      batches[batch_index][batch_pos].v = batch_assignment.v;
    }
  });

  while ( !batches.empty() && batches.back().empty() ) {
    batches.pop_back();
  }
  std::reverse(batches.begin(), batches.end());

  return batches;
}

}  // namespace ds
}  // namespace mt_kahypar
