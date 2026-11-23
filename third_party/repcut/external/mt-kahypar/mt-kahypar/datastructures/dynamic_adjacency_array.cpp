/*******************************************************************************
 * MIT License
 *
 * This file is part of Mt-KaHyPar.
 *
 * Copyright (C) 2020 Tobias Heuer <tobias.heuer@kit.edu>
 * Copyright (C) 2021 Nikolai Maas <nikolai.maas@student.kit.edu>
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

#include "mt-kahypar/datastructures/dynamic_adjacency_array.h"

#include "mt-kahypar/parallel/atomic_wrapper.h"
#include "mt-kahypar/parallel/parallel_prefix_sum.h"

namespace mt_kahypar {
namespace ds {

IncidentEdgeIterator::IncidentEdgeIterator(const HypernodeID u,
                                           const DynamicAdjacencyArray* dynamic_adjacency_array,
                                           const size_t pos,
                                           const bool end):
    _u(u),
    _current_u(u),
    _current_size(dynamic_adjacency_array->header(u).size()),
    _current_pos(pos),
    _dynamic_adjacency_array(dynamic_adjacency_array),
    _end(end) {
  if ( end ) {
    _current_pos = _current_size;
  }

  ASSERT(pos <= dynamic_adjacency_array->nodeDegree(u));
  traverse_headers();
}

HyperedgeID IncidentEdgeIterator::operator* () const {
  return _dynamic_adjacency_array->firstActiveEdge(_current_u) + _current_pos;
}

IncidentEdgeIterator & IncidentEdgeIterator::operator++ () {
  ASSERT(!_end);
  ++_current_pos;
  traverse_headers();
  return *this;
}

bool IncidentEdgeIterator::operator!= (const IncidentEdgeIterator& rhs) {
  return !(*this == rhs);
}

bool IncidentEdgeIterator::operator== (const IncidentEdgeIterator& rhs) {
  return _u == rhs._u && _end == rhs._end;
}

void IncidentEdgeIterator::traverse_headers() {
  skip_invalid();
  while ( _current_pos >= _current_size ) {
    const HypernodeID last_u = _current_u;
    _current_u = _dynamic_adjacency_array->header(last_u).it_next;
    _current_pos -= _current_size;
    _current_size = _dynamic_adjacency_array->header(_current_u).size();
    // It can happen that due to a contraction the current vertex
    // we iterate over becomes empty or the head of the current vertex
    // changes. Therefore, we set the end flag if we reach the current
    // head of the list or it_next is equal with the current vertex (means
    // that list becomes empty due to a contraction)
    if ( _dynamic_adjacency_array->header(_current_u).is_head ||
         last_u == _current_u ) {
      _end = true;
      break;
    }
    skip_invalid();
  }
}

void IncidentEdgeIterator::skip_invalid() {
  while (_current_pos < _current_size &&
         !_dynamic_adjacency_array->edge(**this).isValid()) {
    ++_current_pos;
  }
}

EdgeIterator::EdgeIterator(const HypernodeID u,
                           const DynamicAdjacencyArray* dynamic_adjacency_array):
    _current_u(u),
    _current_id(dynamic_adjacency_array->firstActiveEdge(u)),
    _current_last_id(dynamic_adjacency_array->firstInactiveEdge(u)),
    _dynamic_adjacency_array(dynamic_adjacency_array) {
  traverse_headers();
}

HyperedgeID EdgeIterator::operator* () const {
  return _current_id;
}

EdgeIterator & EdgeIterator::operator++ () {
  ++_current_id;
  traverse_headers();
  return *this;
}

bool EdgeIterator::operator!= (const EdgeIterator& rhs) {
  return !(*this == rhs);
}

bool EdgeIterator::operator== (const EdgeIterator& rhs) {
  return _current_id == rhs._current_id;
}

void EdgeIterator::traverse_headers() {
  skip_invalid();
  while (_current_id == _current_last_id && _current_u < _dynamic_adjacency_array->_num_nodes) {
    ++_current_u;
    _current_id = _dynamic_adjacency_array->firstActiveEdge(_current_u);
    _current_last_id = _dynamic_adjacency_array->firstInactiveEdge(_current_u);
    skip_invalid();
  }
}

void EdgeIterator::skip_invalid() {
  while (_current_id < _current_last_id &&
         !_dynamic_adjacency_array->edge(**this).isValid()) {
    ++_current_id;
  }
}

void DynamicAdjacencyArray::construct(const EdgeVector& edge_vector, const HyperedgeWeight* edge_weight) {
  // Accumulate degree of each vertex thread local
  const HyperedgeID num_edges = edge_vector.size();
  ThreadLocalCounter local_incident_nets_per_vertex(_num_nodes + 1, 0);
  Array<HyperedgeID> node_degrees;
  AtomicCounter current_incident_net_pos;
  tbb::parallel_invoke([&] {
    tbb::parallel_for(ID(0), num_edges, [&](const size_t pos) {
      const HypernodeID pins[2] = {edge_vector[pos].first, edge_vector[pos].second};
      if (pins[0] == pins[1]) {
        throw InvalidInputException("Edge " + STR(pos) + " has identical source and target: " + STR(pins[0]) + " " + STR(pins[0]));
      }

      parallel::scalable_vector<size_t>& num_incident_nets_per_vertex =
        local_incident_nets_per_vertex.local();
      for (const HypernodeID& pin: pins) {
        if (pin >= _num_nodes) {
          throw InvalidInputException("Edge " + STR(pos) + " points to invalid node: " + STR(pin));
        }
        ++num_incident_nets_per_vertex[pin];
      }
    });
  }, [&] {
    _header_array.resize(_num_nodes + 1);
  }, [&] {
    _edges.resize(2 * num_edges);
  }, [&] {
    _removable_edges.setSize(2 * num_edges);
  }, [&] {
    _edge_mapping.resize(2 * num_edges);
  }, [&] {
    node_degrees.resize(_num_nodes);
  }, [&] {
    current_incident_net_pos.assign(
      _num_nodes, parallel::IntegralAtomicWrapper<size_t>(0));
  });

  // We sum up the number of incident nets per vertex only thread local.
  // To obtain the global number of incident nets per vertex, we iterate
  // over each thread local counter and sum it up.
  for ( const parallel::scalable_vector<size_t>& c : local_incident_nets_per_vertex ) {
    tbb::parallel_for(ID(0), _num_nodes, [&](const size_t pos) {
      node_degrees[pos] += c[pos];
    });
  }

  // Compute start positon of the incident nets of each vertex via a parallel prefix sum
  parallel::TBBPrefixSum<HyperedgeID, Array> incident_net_prefix_sum(node_degrees);
  tbb::parallel_scan(tbb::blocked_range<size_t>(
          ID(0), ID(_num_nodes)), incident_net_prefix_sum);

  // Setup Header of each vertex
  tbb::parallel_for(ID(0), _num_nodes + 1, [&](const HypernodeID u) {
    Header& head = header(u);
    head.prev = u;
    head.next = u;
    head.it_prev = u;
    head.it_next = u;
    head.degree = (u == _num_nodes) ? 0 : incident_net_prefix_sum[u + 1] - incident_net_prefix_sum[u];
    head.first = incident_net_prefix_sum[u];
    head.first_active = head.first;
    head.first_inactive = head.first + head.degree;
    head.is_head = true;
  });

  // Insert incident nets into incidence array
  tbb::parallel_for(ID(0), num_edges, [&](const HyperedgeID he) {
    HypernodeID source = edge_vector[he].first;
    HypernodeID target = edge_vector[he].second;
    const HyperedgeWeight weight = edge_weight == nullptr ? 1 : edge_weight[he];
    HyperedgeID id1 = firstEdge(source) + current_incident_net_pos[source].fetch_add(1);
    HyperedgeID id2 = firstEdge(target) + current_incident_net_pos[target].fetch_add(1);
    Edge& e1 = edge(id1);
    e1.source = source;
    e1.target = target;
    e1.weight = weight;
    e1.back_edge = id2;
    Edge& e2 = edge(id2);
    e2.source = target;
    e2.target = source;
    e2.weight = weight;
    e2.back_edge = id1;
  });
}

void DynamicAdjacencyArray::contract(const HypernodeID u,
                                     const HypernodeID v,
                                     const AcquireLockFunc& acquire_lock,
                                     const ReleaseLockFunc& release_lock) {
  // iterate over edges of v and update them
  Header& head_v = header(v);
  for (const HypernodeID& current_v: headers(v)) {
    const HyperedgeID last = firstInactiveEdge(current_v);
    for ( HyperedgeID curr_edge = firstActiveEdge(current_v); curr_edge < last; ++curr_edge ) {
      Edge& e = edge(curr_edge);
      if (e.isValid() && e.isSinglePin()) {
        ASSERT(e.source == v);
        e.disable();
        --head_v.degree;
      } else if (e.isValid()) {
        ASSERT(e.source == v && edge(e.back_edge).target == v);
        e.source = u;
        edge(e.back_edge).target = u;
      }
    }
  }

  acquire_lock(u);
  // Concatenate double-linked list of u and v
  append(u, v);
  header(u).degree += head_v.degree;
  ASSERT(verifyIteratorPointers(u), "Iterator pointers of vertex" << u << "are corrupted");
  release_lock(u);
}

void DynamicAdjacencyArray::uncontract(const HypernodeID u,
                                       const HypernodeID v,
                                       const AcquireLockFunc& acquire_lock,
                                       const ReleaseLockFunc& release_lock) {
  uncontract(u, v, [](HyperedgeID) { return false; }, [](HyperedgeID) {}, [](HyperedgeID) {},
             acquire_lock, release_lock);
}

void DynamicAdjacencyArray::uncontract(const HypernodeID u,
                                       const HypernodeID v,
                                       const MarkEdgeFunc& mark_edge,
                                       const CaseOneFunc& case_one_func,
                                       const CaseTwoFunc& case_two_func,
                                       const AcquireLockFunc& acquire_lock,
                                       const ReleaseLockFunc& release_lock) {
  ASSERT(header(v).prev != v);
  Header& head_u = header(u);
  Header& head_v = header(v);
  acquire_lock(u);
  // Restores the incident list of v to the time before it was appended
  // to the double-linked list of u.
  splice(u, v);
  ASSERT(verifyIteratorPointers(u), "Iterator pointers of vertex" << u << "are corrupted");
  ASSERT(head_u.degree >= head_v.degree, V(head_u.degree) << V(head_v.degree));
  head_u.degree -= head_v.degree;
  release_lock(u);

  // iterate over edges of v, update backwards edges and restore removed edges
  HypernodeID last_non_empty_v = v;
  for (const HypernodeID& current_v: headers(v)) {
    const HyperedgeID first_inactive = firstInactiveEdge(current_v);
    for (HyperedgeID curr_edge = firstActiveEdge(current_v); curr_edge < first_inactive; ++curr_edge) {
      Edge& e = edge(curr_edge);
      ASSERT(e.source == u || !e.isValid());
      if (e.source == u) {
        bool singlePin = false;
        if (e.target == u) {
          // If we use a gain cache, it is necessary to correctly attribute
          // which uncontraction changes an edge from single pin to two pins.
          // To achieve this, we introduce a synchronization point with mark_edge.
          singlePin = !mark_edge(curr_edge);
        }
        e.source = v;
        edge(e.back_edge).target = v;
        if (singlePin) {
          case_one_func(curr_edge);
        } else {
          case_two_func(curr_edge);
        }
      } else if (e.source == v) {
        e.enable();
        ++head_v.degree;
      }
    }


    if (header(current_v).size() > 0) {
      restoreItLink(v, last_non_empty_v, current_v);
      last_non_empty_v = current_v;
    }
  }
  ASSERT(verifyIteratorPointers(v), "Iterator pointers of vertex" << v << "are corrupted");
}

parallel::scalable_vector<DynamicAdjacencyArray::RemovedEdge> DynamicAdjacencyArray::removeSinglePinAndParallelEdges() {
  // TODO(maas): special case for high degree nodes?
  StreamingVector<RemovedEdge> tmp_removed_edges;
  _removable_edges.reset();
  initializeEdgeMapping(_edge_mapping);

  // Step one: We mark each edge that should be removed and
  // update the weight of the representative edges.
  tbb::parallel_for(ID(0), _num_nodes, [&](const HypernodeID u) {
    if (header(u).is_head) {
      vec<ParallelEdgeInformation>& local_vec = _thread_local_vec.local();
      local_vec.clear();

      // mark single pin/invalid edges and sort all other incident edges
      for (const HypernodeID& current_u: headers(u)) {
        const HyperedgeID first_inactive = firstInactiveEdge(current_u);
        for (HyperedgeID id = firstActiveEdge(current_u); id < first_inactive; ++id) {
          const Edge& e = edge(id);
          if (e.isValid() && !e.isSinglePin()) {
            local_vec.emplace_back(e.target, id, uniqueEdgeID(id));
          } else {
            _removable_edges.set(id, true);
            if (e.isValid()) {
              --header(u).degree;
            }
          }
        }
      }
      std::sort(local_vec.begin(), local_vec.end(), [](const auto& e1, const auto& e2) {
        // we need a symmetric order on edges and backedges to ensure that the
        // kept forward and backward edge are actually the same edge
        return e1.target < e2.target || (e1.target == e2.target && e1.unique_id < e2.unique_id);
      });

      // mark all duplicate edges and update weight
      if (!local_vec.empty()) {
        HyperedgeID current_representative = local_vec[0].edge_id;
        for (size_t i = 0; i + 1 < local_vec.size(); ++i) {
          const ParallelEdgeInformation& e1 = local_vec[i];
          const ParallelEdgeInformation& e2 = local_vec[i + 1];
          ASSERT(e2.target != kInvalidHypernode && e2.target != u);
          if (e1.target == e2.target) {
            // we abuse the source to save the representative edge
            edge(e2.edge_id).source = current_representative;
            edge(current_representative).weight += edge(e2.edge_id).weight;
            _removable_edges.set(e2.edge_id, true);
            --header(u).degree;
          } else {
            current_representative = e2.edge_id;
          }
        }
      }
    }
  });

  // Step two: Swap each marked edge and update the edge mapping accordingly.
  tbb::parallel_for(ID(0), _num_nodes, [&](const HypernodeID u) {
    Header& head = header(u);
    const HyperedgeID first_inactive = firstInactiveEdge(u);
    for (HyperedgeID e = firstActiveEdge(u); e < first_inactive; ++e) {
      if (_removable_edges[e]) {
        const HyperedgeID new_id = firstActiveEdge(u);
        swapAndUpdateMapping(e, new_id);
        ++head.first_active;
        tmp_removed_edges.stream(RemovedEdge {new_id, e});
      }
    }

    if (head.size() == 0 && !head.is_head) {
      head.it_next = u;
      head.it_prev = u;
    }
  });

  // Step three: Update iterator pointers and back edges, collect removed edges.
  vec<RemovedEdge> removed_edges;
  tbb::parallel_invoke([&]() {
    tbb::parallel_for(ID(0), _num_nodes, [&](const HypernodeID u) {
      if (header(u).is_head) {
        restoreIteratorPointers(u);
      }
    });
  }, [&]() {
    applyEdgeMapping(_edge_mapping);
  }, [&]() {
    removed_edges = tmp_removed_edges.copy_parallel();
    tmp_removed_edges.clear_parallel();
  });

  HEAVY_COARSENING_ASSERT(verifyBackEdges());
  return removed_edges;
}

void DynamicAdjacencyArray::restoreSinglePinAndParallelEdges(
      const parallel::scalable_vector<DynamicAdjacencyArray::RemovedEdge>& edges_to_restore) {
  _removable_edges.reset();
  initializeEdgeMapping(_edge_mapping);

  // Step one: We mark all edges that need to be restored and save their swap target.
  tbb::parallel_for(UL(0), edges_to_restore.size(), [&](const size_t i) {
    const RemovedEdge& re = edges_to_restore[i];
    _removable_edges.set(re.edge_id, true);
    // we abuse the edge mapping to save the swap target
    _edge_mapping[re.edge_id] = re.old_id;
  });

  // Step two: We swap each marked edge (in reverse order to removeSinglePinAndParallelEdges),
  // update the edge mapping accordingly and mark the edge again.
  tbb::parallel_for(ID(0), _num_nodes, [&](const HypernodeID u) {
    Header& head = header(u);
    const HyperedgeID first = firstEdge(u);
    for (HyperedgeID curr = firstActiveEdge(u);
         curr > first && _removable_edges[curr - 1]; --curr) {
      const HyperedgeID e = curr - 1;
      _removable_edges.set(e, false);
      _removable_edges.set(_edge_mapping[e], true);
      swapAndUpdateMapping(e, _edge_mapping[e]);
      --head.first_active;
    }
  });

  // Step three: We update the node degrees, restore iterator pointers and the weights
  // of the representatives and update the back edges.
  tbb::parallel_invoke([&]() {
    tbb::parallel_for(ID(0), _num_nodes, [&](const HypernodeID u) {
      if (header(u).is_head) {
        bool restore_it = false;
        for (const HypernodeID& current_u: headers(u)) {
          HyperedgeID num_restored = 0;
          const HyperedgeID first_inactive = firstInactiveEdge(current_u);
          for (HyperedgeID id = firstActiveEdge(current_u); id < first_inactive; ++id) {
            Edge& e = edge(id);
            // Note: We use e.target to check whether it is a single pin edge.
            // Comparing e.source and e.target does not work, because e.source
            // currently holds the representative edge and the id of the representative
            // could accidentially be equal to e.target.
            if (_removable_edges[id] && e.isValid() && e.target != u) {
              Edge& representative = edge(e.source);
              representative.weight -= e.weight;
              e.source = u;
            } else if (e.isValid()) {
              ASSERT(e.source == u);
            }
            if (_removable_edges[id] && e.isValid()) {
              ++num_restored;
            }
          }
          header(u).degree += num_restored;
          restore_it |= (num_restored > 0);
        }

        if (restore_it) {
          restoreIteratorPointers(u);
        }
      }
    });
  }, [&]() {
    applyEdgeMapping(_edge_mapping);
  });

  HEAVY_REFINEMENT_ASSERT(verifyBackEdges());
}

void DynamicAdjacencyArray::reset() {
  // Nothing to do here
}

void DynamicAdjacencyArray::sortIncidentEdges() {
  // this is a bit complicated because we need to update the back edges
  Array<HyperedgeID> edge_permutation;
  edge_permutation.resize(_edges.size());
  initializeEdgeMapping(edge_permutation);

  tbb::parallel_for(ID(0), ID(_header_array.size()), [&](HypernodeID u) {
    // sort mapped indizes
    const HyperedgeID start = firstActiveEdge(u);
    const HyperedgeID end = firstInactiveEdge(u);
    std::sort(edge_permutation.data() + start, edge_permutation.data() + end,
      [&](const auto& e1, const auto& e2) {
        return edge(e1).target < edge(e2).target;
      }
    );

    // apply permutation
    for (size_t i = start; i < end; ++i) {
      HyperedgeID target = edge_permutation[i];
      while (target < i) {
        target = edge_permutation[target];
      }
      std::swap(_edges[i], _edges[target]);
    }
  });

  // we need the reversed permutation for the back edges
  tbb::parallel_for(ID(0), ID(edge_permutation.size()), [&](const HyperedgeID e) {
    _edge_mapping[edge_permutation[e]] = e;
  });
  applyEdgeMapping(_edge_mapping);

  HEAVY_PREPROCESSING_ASSERT(verifyBackEdges());
}

DynamicAdjacencyArray DynamicAdjacencyArray::copy(parallel_tag_t) const {
  DynamicAdjacencyArray adjacency_array;
  adjacency_array._num_nodes = _num_nodes;

  tbb::parallel_invoke([&] {
    adjacency_array._header_array.resize(_header_array.size());
    memcpy(adjacency_array._header_array.data(), _header_array.data(),
      sizeof(Header) * _header_array.size());
  }, [&] {
    adjacency_array._edges.resize(_edges.size());
    memcpy(adjacency_array._edges.data(), _edges.data(), sizeof(Edge) * _edges.size());
  },[&] {
    adjacency_array._removable_edges.setSize(_edges.size());
  }, [&] {
    adjacency_array._edge_mapping.resize(_edge_mapping.size());
  });

  return adjacency_array;
}

DynamicAdjacencyArray DynamicAdjacencyArray::copy() const {
  DynamicAdjacencyArray adjacency_array;
  adjacency_array._num_nodes = _num_nodes;

  adjacency_array._header_array.resize(_header_array.size());
  memcpy(adjacency_array._header_array.data(), _header_array.data(),
    sizeof(Header) * _header_array.size());
  adjacency_array._edges.resize(_edges.size());
  memcpy(adjacency_array._edges.data(), _edges.data(), sizeof(Edge) * _edges.size());
  adjacency_array._removable_edges.setSize(_edges.size());
  adjacency_array._edge_mapping.resize(_edge_mapping.size());
  return adjacency_array;
}

void DynamicAdjacencyArray::swapAndUpdateMapping(const HyperedgeID e, const HyperedgeID new_id) {
  HyperedgeID permutation_source = new_id;
  while (_edge_mapping[permutation_source] != new_id) {
    permutation_source = _edge_mapping[permutation_source];
  }
  ASSERT(_edge_mapping[permutation_source] == new_id);
  std::swap(edge(e), edge(new_id));
  _edge_mapping[e] = new_id;
  _edge_mapping[permutation_source] = e;
}

void DynamicAdjacencyArray::append(const HypernodeID u, const HypernodeID v) {
  const HypernodeID tail_u = header(u).prev;
  const HypernodeID tail_v = header(v).prev;
  header(tail_u).next = v;
  header(v).prev = tail_u;
  header(tail_v).next = u;
  header(u).prev = tail_v;

  const HypernodeID it_tail_u = header(u).it_prev;
  const HypernodeID it_tail_v = header(v).it_prev;
  header(it_tail_u).it_next = v;
  header(v).it_prev = it_tail_u;
  header(it_tail_v).it_next = u;
  header(u).it_prev = it_tail_v;

  header(v).tail = tail_v;
  header(v).is_head = false;

  if ( header(v).size() == 0 ) {
    removeEmptyIncidentEdgeList(v);
  }
}

void DynamicAdjacencyArray::splice(const HypernodeID u, const HypernodeID v) {
  // Restore the iterator double-linked list of u such that it does not contain
  // any incident net list of v
  const HypernodeID tail = header(v).tail;
  HypernodeID non_empty_entry_prev_v = v;
  HypernodeID non_empty_entry_next_tail = tail;
  while ( ( non_empty_entry_prev_v == v ||
          header(non_empty_entry_prev_v).size() == 0 ) &&
          non_empty_entry_prev_v != u ) {
    non_empty_entry_prev_v = header(non_empty_entry_prev_v).prev;
  }
  while ( ( non_empty_entry_next_tail == tail ||
          header(non_empty_entry_next_tail).size() == 0 ) &&
          non_empty_entry_next_tail != u ) {
    non_empty_entry_next_tail = header(non_empty_entry_next_tail).next;
  }
  header(non_empty_entry_prev_v).it_next = non_empty_entry_next_tail;
  header(non_empty_entry_next_tail).it_prev = non_empty_entry_prev_v;

  // Cut out incident list of v
  const HypernodeID prev_v = header(v).prev;
  const HypernodeID next_tail = header(tail).next;
  header(v).prev = tail;
  header(tail).next = v;
  header(next_tail).prev = prev_v;
  header(prev_v).next = next_tail;
  header(v).is_head = true;
}

void DynamicAdjacencyArray::removeEmptyIncidentEdgeList(const HypernodeID u) {
  ASSERT(!header(u).is_head);
  ASSERT(header(u).size() == 0, V(u) << V(header(u).size()));
  Header& head = header(u);
  header(head.it_prev).it_next = head.it_next;
  header(head.it_next).it_prev = head.it_prev;
  head.it_next = u;
  head.it_prev = u;
}

void DynamicAdjacencyArray::restoreIteratorPointers(const HypernodeID u) {
  ASSERT(header(u).is_head);
  HypernodeID last_non_empty_u = u;
  for (const HypernodeID& current_u: headers(u)) {
    if (header(current_u).size() > 0 || current_u == u) {
      restoreItLink(u, last_non_empty_u, current_u);
      last_non_empty_u = current_u;
    }
  }
  ASSERT(verifyIteratorPointers(u));
}

void DynamicAdjacencyArray::restoreItLink(const HypernodeID u, const HypernodeID prev, const HypernodeID current) {
  header(prev).it_next = current;
  header(current).it_prev = prev;
  header(current).it_next = u;
  header(u).it_prev = current;
}

bool DynamicAdjacencyArray::verifyIteratorPointers(const HypernodeID u) const {
  HypernodeID current_u = u;
  HypernodeID last_non_empty_entry = kInvalidHypernode;
  do {
    if ( header(current_u).size() > 0 || current_u == u ) {
      if ( last_non_empty_entry != kInvalidHypernode ) {
        if ( header(current_u).it_prev != last_non_empty_entry ) {
          return false;
        } else if ( header(last_non_empty_entry).it_next != current_u ) {
          return false;
        }
      }
      last_non_empty_entry = current_u;
    } else {
      if ( header(current_u).it_next != current_u ) {
        return false;
      } else if ( header(current_u).it_prev != current_u ) {
        return false;
      }
    }

    current_u = header(current_u).next;
  } while(current_u != u);

  if ( header(u).it_prev != last_non_empty_entry ) {
    return false;
  } else if ( header(last_non_empty_entry).it_next != u ) {
    return false;
  }

  return true;
}

bool DynamicAdjacencyArray::verifyBackEdges() const {
  for (HyperedgeID e = 0; e < _edges.size(); ++e) {
    if (edge(edge(e).back_edge).back_edge != e) {
      return false;
    }
  }
  return true;
}

}  // namespace ds
}  // namespace mt_kahypar
