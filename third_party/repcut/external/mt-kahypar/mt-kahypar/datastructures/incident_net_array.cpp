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

#include "mt-kahypar/datastructures/incident_net_array.h"

#include "mt-kahypar/parallel/parallel_prefix_sum.h"

namespace mt_kahypar {
namespace ds {

IncidentNetIterator::IncidentNetIterator(const HypernodeID u,
                                         const IncidentNetArray* incident_net_array,
                                         const size_t pos,
                                         const bool end) :
  _u(u),
  _current_u(u),
  _current_size(incident_net_array->header(u)->size),
  _current_pos(0),
  _incident_net_array(incident_net_array),
  _end(end) {
  if ( end ) {
    _current_pos = _current_size;
  }

  if ( !end && _current_pos == _current_size ) {
    next_iterator();
  }

  if ( pos > 0 ) {
    ASSERT(pos <= incident_net_array->nodeDegree(u));
    size_t c_pos = pos;
    while ( c_pos != 0 ) {
      const size_t current_size = _current_size;
      if ( c_pos >= current_size ) {
        c_pos -= current_size;
        _current_pos = current_size;
        next_iterator();
      } else {
        _current_pos = c_pos;
        c_pos = 0;
      }
    }
  }
}

HyperedgeID IncidentNetIterator::operator* () const {
  ASSERT(!_end);
  return _incident_net_array->firstEntry(_current_u)[_current_pos].e;
}

IncidentNetIterator & IncidentNetIterator::operator++ () {
  ASSERT(!_end);
  ++_current_pos;
  if ( _current_pos == _current_size) {
    next_iterator();
  }
  return *this;
}

bool IncidentNetIterator::operator!= (const IncidentNetIterator& rhs) {
  return _u != rhs._u || _end != rhs._end;
}

bool IncidentNetIterator::operator== (const IncidentNetIterator& rhs) {
  return _u == rhs._u && _end == rhs._end;
}

void IncidentNetIterator::next_iterator() {
  while ( _current_pos == _current_size ) {
    const HypernodeID last_u = _current_u;
    _current_u = _incident_net_array->header(_current_u)->it_next;
    _current_pos = 0;
    _current_size = _incident_net_array->header(_current_u)->size;
    // It can happen that due to a contraction the current vertex
    // we iterate over becomes empty or the head of the current vertex
    // changes. Therefore, we set the end flag if we reach the current
    // head of the list or it_next is equal with the current vertex (means
    // that list becomes empty due to a contraction)
    if ( _incident_net_array->header(_current_u)->is_head ||
         last_u == _current_u ) {
      _end = true;
      break;
    }
  }
}

// ! Contracts two incident list of u and v, whereby u is the representative and
// ! v the contraction partner of the contraction. The contraction involves to remove
// ! all incident nets shared between u and v from the incident net list of v and append
// ! the list of v to u.
void IncidentNetArray::contract(const HypernodeID u,
                                const HypernodeID v,
                                const kahypar::ds::FastResetFlagArray<>& shared_hes_of_u_and_v,
                                const AcquireLockFunc& acquire_lock,
                                const ReleaseLockFunc& release_lock) {
  // Remove all HEs flagged in shared_hes_of_u_and_v from v
  removeIncidentNets(v, shared_hes_of_u_and_v);

  acquire_lock(u);
  // Concatenate double-linked list of u and v
  append(u, v);
  header(u)->degree += header(v)->degree;
  ASSERT(verifyIteratorPointers(u), "Iterator pointers of vertex" << u << "are corrupted");
  release_lock(u);
}

// ! Uncontract two previously contracted vertices u and v.
// ! Uncontraction involves to decrement the version number of all incident lists contained
// ! in v and restore all incident nets with a version number equal to the new version.
// ! Note, uncontraction must be done in relative contraction order
void IncidentNetArray::uncontract(const HypernodeID u,
                                  const HypernodeID v,
                                  const AcquireLockFunc& acquire_lock,
                                  const ReleaseLockFunc& release_lock) {
  uncontract(u, v, [](HyperedgeID) {}, [](HyperedgeID) {}, acquire_lock, release_lock);
}

// ! Uncontract two previously contracted vertices u and v.
// ! Uncontraction involves to decrement the version number of all incident lists contained
// ! in v and restore all incident nets with a version number equal to the new version.
// ! Additionally it calls case_one_func for a hyperedge he, if u and v were previously both
// ! adjacent to he and case_two_func if only v was previously adjacent to he.
// ! Note, uncontraction must be done in relative contraction order
void IncidentNetArray::uncontract(const HypernodeID u,
                                  const HypernodeID v,
                                  const CaseOneFunc& case_one_func,
                                  const CaseTwoFunc& case_two_func,
                                  const AcquireLockFunc& acquire_lock,
                                  const ReleaseLockFunc& release_lock) {
  ASSERT(header(v)->prev != v);
  Header* head_v = header(v);
  acquire_lock(u);
  // Restores the incident list of v to the time before it was appended
  // to the double-linked list of u.
  splice(u, v);
  header(u)->degree -= head_v->degree;
  ASSERT(verifyIteratorPointers(u), "Iterator pointers of vertex" << u << "are corrupted");
  release_lock(u);

  // Restore all incident nets of v removed by the contraction of u and v
  restoreIncidentNets(v, case_one_func, case_two_func);
}

// ! Removes all incidents nets of u flagged in hes_to_remove.
void IncidentNetArray::removeIncidentNets(const HypernodeID u,
                                          const kahypar::ds::FastResetFlagArray<>& hes_to_remove) {
  HypernodeID current_u = u;
  Header* head_u = header(u);
  do {
    Header* head = header(current_u);
    const HypernodeID new_version = ++head->current_version;
    Entry* last_entry = lastEntry(current_u);
    for ( Entry* current_entry = firstEntry(current_u); current_entry != last_entry; ++current_entry ) {
      if ( hes_to_remove[current_entry->e] ) {
        // Hyperedge should be removed => decrement size of incident net list
        swap(current_entry--, --last_entry);
        ASSERT(head->size > 0);
        --head->size;
        --head_u->degree;
      } else {
        // Vertex is non-shared between u and v => adapt version number of current incident net
        current_entry->version = new_version;
      }
    }

    if ( head->size == 0 && current_u != u ) {
      // Current list becomes empty => remove it from the iterator double linked list
      // such that iteration over the incident nets is more efficient
      removeEmptyIncidentNetList(current_u);
    }
    current_u = head->next;
  } while ( current_u != u );
  ASSERT(verifyIteratorPointers(u), "Iterator pointers of vertex" << u << "are corrupted");
}

// ! Restores all previously removed incident nets
// ! Note, function must be called in reverse order of calls to
// ! removeIncidentNets(...) and all uncontraction that happens
// ! between two consecutive calls to removeIncidentNets(...) must
// ! be processed.
void IncidentNetArray::restoreIncidentNets(const HypernodeID u) {
  restoreIncidentNets(u, [](HyperedgeID) {}, [](HyperedgeID) {});
}

// ! Restores all previously removed incident nets
// ! Note, function must be called in reverse order of calls to
// ! removeIncidentNets(...) and all uncontraction that happens
// ! between two consecutive calls to removeIncidentNets(...) must
// ! be processed.
void IncidentNetArray::restoreIncidentNets(const HypernodeID u,
                                           const CaseOneFunc& case_one_func,
                                           const CaseTwoFunc& case_two_func) {
  Header* head_u = header(u);
  HypernodeID current_u = u;
  HypernodeID last_non_empty_entry = kInvalidHypernode;
  do {
    Header* head = header(current_u);
    ASSERT(head->current_version > 0);
    const HypernodeID new_version = --head->current_version;

    // Iterate over all active entries and call case_two_func
    // => After an uncontraction only u was part of them not its representative
    for ( Entry* current_entry = firstEntry(current_u);
          current_entry != lastEntry(current_u);
          ++current_entry ) {
      case_two_func(current_entry->e);
    }

    // Iterate over non-active entries (and activate them) until the version number
    // is not equal to the new version of the list
    const Entry* last_entry = reinterpret_cast<const Entry*>(header(current_u + 1));
    for ( Entry* current_entry = lastEntry(current_u);
          current_entry != last_entry;
          ++current_entry ) {
      if ( current_entry->version == new_version ) {
        ++head->size;
        ++head_u->degree;
        case_one_func(current_entry->e);
      } else {
        break;
      }
    }

    // Restore iterator double-linked list which only contains
    // non-empty incident net lists
    if ( head->size > 0 || current_u == u ) {
      if ( last_non_empty_entry != kInvalidHypernode &&
           head->it_prev != last_non_empty_entry ) {
        header(last_non_empty_entry)->it_next = current_u;
        head->it_prev = last_non_empty_entry;
      }
      last_non_empty_entry = current_u;
    }
    current_u = head->next;
  } while ( current_u != u );

  ASSERT(last_non_empty_entry != kInvalidHypernode);
  head_u->it_prev = last_non_empty_entry;
  header(last_non_empty_entry)->it_next = u;
  ASSERT(verifyIteratorPointers(u), "Iterator pointers of vertex" << u << "are corrupted");
}

IncidentNetArray IncidentNetArray::copy(parallel_tag_t) const {
  IncidentNetArray incident_nets;
  incident_nets._num_hypernodes = _num_hypernodes;
  incident_nets._size_in_bytes = _size_in_bytes;

  tbb::parallel_invoke([&] {
    incident_nets._index_array.resize(_index_array.size());
    memcpy(incident_nets._index_array.data(), _index_array.data(),
      sizeof(size_t) * _index_array.size());
  }, [&] {
    incident_nets._incident_net_array = parallel::make_unique<char>(_size_in_bytes);
    memcpy(incident_nets._incident_net_array.get(), _incident_net_array.get(), _size_in_bytes);
  });

  return incident_nets;
}

IncidentNetArray IncidentNetArray::copy() const {
  IncidentNetArray incident_nets;
  incident_nets._num_hypernodes = _num_hypernodes;
  incident_nets._size_in_bytes = _size_in_bytes;
  incident_nets._index_array.resize(_index_array.size());
  memcpy(incident_nets._index_array.data(), _index_array.data(),
    sizeof(size_t) * _index_array.size());
  incident_nets._incident_net_array = parallel::make_unique<char>(_size_in_bytes);
  memcpy(incident_nets._incident_net_array.get(), _incident_net_array.get(), _size_in_bytes);
  return incident_nets;
}

void IncidentNetArray::reset() {
  tbb::parallel_for(ID(0), _num_hypernodes, [&](const HypernodeID u) {
    header(u)->current_version = 0;
    for ( Entry* entry = firstEntry(u); entry != lastEntry(u); ++entry ) {
      entry->version = 0;
    }
  });
}

void IncidentNetArray::append(const HypernodeID u, const HypernodeID v) {
  const HypernodeID tail_u = header(u)->prev;
  const HypernodeID tail_v = header(v)->prev;
  header(tail_u)->next = v;
  header(u)->prev = tail_v;
  header(v)->tail = tail_v;
  header(v)->prev = tail_u;
  header(tail_v)->next = u;

  const HypernodeID it_tail_u = header(u)->it_prev;
  const HypernodeID it_tail_v = header(v)->it_prev;
  header(it_tail_u)->it_next = v;
  header(u)->it_prev = it_tail_v;
  header(v)->it_prev = it_tail_u;
  header(it_tail_v)->it_next = u;
  header(v)->is_head = false;

  if ( header(v)->size == 0 ) {
    removeEmptyIncidentNetList(v);
  }
}

void IncidentNetArray::splice(const HypernodeID u, const HypernodeID v) {
  // Restore the iterator double-linked list of u such that it does not contain
  // any incident net list of v
  const HypernodeID tail = header(v)->tail;
  HypernodeID non_empty_entry_prev_v = v;
  HypernodeID non_empty_entry_next_tail = tail;
  while ( ( non_empty_entry_prev_v == v ||
          header(non_empty_entry_prev_v)->size == 0 ) &&
          non_empty_entry_prev_v != u ) {
    non_empty_entry_prev_v = header(non_empty_entry_prev_v)->prev;
  }
  while ( ( non_empty_entry_next_tail == tail ||
          header(non_empty_entry_next_tail)->size == 0 ) &&
          non_empty_entry_next_tail != u ) {
    non_empty_entry_next_tail = header(non_empty_entry_next_tail)->next;
  }
  header(non_empty_entry_prev_v)->it_next = non_empty_entry_next_tail;
  header(non_empty_entry_next_tail)->it_prev = non_empty_entry_prev_v;

  // Cut out incident list of v
  const HypernodeID prev_v = header(v)->prev;
  const HypernodeID next_tail = header(tail)->next;
  header(v)->prev = tail;
  header(tail)->next = v;
  header(next_tail)->prev = prev_v;
  header(prev_v)->next = next_tail;
  header(v)->is_head = true;
}

void IncidentNetArray::removeEmptyIncidentNetList(const HypernodeID u) {
  ASSERT(!header(u)->is_head);
  ASSERT(header(u)->size == 0, V(u) << V(header(u)->size));
  Header* head = header(u);
  header(head->it_prev)->it_next = head->it_next;
  header(head->it_next)->it_prev = head->it_prev;
  head->it_next = u;
  head->it_prev = u;
}

void IncidentNetArray::construct(const HyperedgeVector& edge_vector) {
  // Accumulate degree of each vertex thread local
  const HyperedgeID num_hyperedges = edge_vector.size();
  ThreadLocalCounter local_incident_nets_per_vertex(_num_hypernodes + 1, 0);
  AtomicCounter current_incident_net_pos;
  tbb::parallel_invoke([&] {
    tbb::parallel_for(ID(0), num_hyperedges, [&](const size_t pos) {
      parallel::scalable_vector<size_t>& num_incident_nets_per_vertex =
        local_incident_nets_per_vertex.local();
      for ( const HypernodeID& pin : edge_vector[pos] ) {
        if (pin >= _num_hypernodes) {
          throw InvalidInputException("Hyperedge " + STR(pos) + " contains invalid pin: " + STR(pin));
        }
        ++num_incident_nets_per_vertex[pin + 1];
      }
    });
  }, [&] {
    _index_array.assign(_num_hypernodes + 1, sizeof(Header));
    current_incident_net_pos.assign(
      _num_hypernodes, parallel::IntegralAtomicWrapper<size_t>(0));
  });

  // We sum up the number of incident nets per vertex only thread local.
  // To obtain the global number of incident nets per vertex, we iterate
  // over each thread local counter and sum it up.
  for ( const parallel::scalable_vector<size_t>& c : local_incident_nets_per_vertex ) {
    tbb::parallel_for(ID(0), _num_hypernodes + 1, [&](const size_t pos) {
      _index_array[pos] += c[pos] * sizeof(Entry);
    });
  }

  // Compute start positon of the incident nets of each vertex via a parallel prefix sum
  parallel::TBBPrefixSum<size_t, Array> incident_net_prefix_sum(_index_array);
  tbb::parallel_scan(tbb::blocked_range<size_t>(
          UL(0), UI64(_num_hypernodes + 1)), incident_net_prefix_sum);
  _size_in_bytes = incident_net_prefix_sum.total_sum();
  _incident_net_array = parallel::make_unique<char>(_size_in_bytes);

  // Insert incident nets into incidence array
  tbb::parallel_for(ID(0), num_hyperedges, [&](const HyperedgeID he) {
    for ( const HypernodeID& pin : edge_vector[he] ) {
      Entry* entry = firstEntry(pin) + current_incident_net_pos[pin]++;
      entry->e = he;
      entry->version = 0;
    }
  });

  // Setup Header of each vertex
  tbb::parallel_for(ID(0), _num_hypernodes, [&](const HypernodeID u) {
    Header* head = header(u);
    head->prev = u;
    head->next = u;
    head->it_prev = u;
    head->it_next = u;
    head->size = current_incident_net_pos[u].load(std::memory_order_relaxed);
    head->degree = head->size;
    head->current_version = 0;
    head->is_head = true;
  });
}

bool IncidentNetArray::verifyIteratorPointers(const HypernodeID u) const {
  HypernodeID current_u = u;
  HypernodeID last_non_empty_entry = kInvalidHypernode;
  do {
    if ( header(current_u)->size > 0 || current_u == u ) {
      if ( last_non_empty_entry != kInvalidHypernode ) {
        if ( header(current_u)->it_prev != last_non_empty_entry ) {
          return false;
        } else if ( header(last_non_empty_entry)->it_next != current_u ) {
          return false;
        }
      }
      last_non_empty_entry = current_u;
    } else {
      if ( header(current_u)->it_next != current_u ) {
        return false;
      } else if ( header(current_u)->it_prev != current_u ) {
        return false;
      }
    }

    current_u = header(current_u)->next;
  } while(current_u != u);

  if ( header(u)->it_prev != last_non_empty_entry ) {
    return false;
  } else if ( header(last_non_empty_entry)->it_next != u ) {
    return false;
  }

  return true;
}

}  // namespace ds
}  // namespace mt_kahypar