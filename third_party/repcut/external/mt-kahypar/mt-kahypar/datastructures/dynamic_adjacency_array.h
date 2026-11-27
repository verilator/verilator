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

#pragma once

#include <cstddef>

#include <tbb/enumerable_thread_specific.h>

#include "kahypar-resources/datastructure/fast_reset_flag_array.h"

#include "mt-kahypar/macros.h"
#include "mt-kahypar/datastructures/hypergraph_common.h"
#include "mt-kahypar/datastructures/streaming_vector.h"
#include "mt-kahypar/datastructures/array.h"
#include "mt-kahypar/parallel/stl/scalable_vector.h"
#include "mt-kahypar/parallel/stl/scalable_unique_ptr.h"
#include "mt-kahypar/parallel/atomic_wrapper.h"
#include "mt-kahypar/utils/range.h"

namespace mt_kahypar {
namespace ds {

// forward declaration
class DynamicAdjacencyArray;

// Iterator over the incident edges of a vertex u
class IncidentEdgeIterator {
  public:
    using iterator_category = std::forward_iterator_tag;
    using value_type = HyperedgeID;
    using reference = HyperedgeID&;
    using pointer = const HyperedgeID*;
    using difference_type = std::ptrdiff_t;

  IncidentEdgeIterator(const HypernodeID u,
                      const DynamicAdjacencyArray* dynamic_adjacency_array,
                      const size_t pos,
                      const bool end);

  HyperedgeID operator* () const;

  IncidentEdgeIterator & operator++ ();

  IncidentEdgeIterator operator++ (int) {
    IncidentEdgeIterator copy = *this;
    operator++ ();
    return copy;
  }

  bool operator!= (const IncidentEdgeIterator& rhs);

  bool operator== (const IncidentEdgeIterator& rhs);

  private:
  void traverse_headers();

  void skip_invalid();

  HypernodeID _u;
  HypernodeID _current_u;
  HypernodeID _current_size;
  HyperedgeID _current_pos;
  const DynamicAdjacencyArray* _dynamic_adjacency_array;
  bool _end;
};

// Iterator over all edges
class EdgeIterator {
  public:
  using iterator_category = std::forward_iterator_tag;
  using value_type = HyperedgeID;
  using reference = HyperedgeID&;
  using pointer = const HyperedgeID*;
  using difference_type = std::ptrdiff_t;

  EdgeIterator(const HypernodeID u,
               const DynamicAdjacencyArray* dynamic_adjacency_array);

  HyperedgeID operator* () const;

  EdgeIterator & operator++ ();

  EdgeIterator operator++ (int) {
    EdgeIterator copy = *this;
    operator++ ();
    return copy;
  }

  bool operator!= (const EdgeIterator& rhs);

  bool operator== (const EdgeIterator& rhs);

  private:
  void traverse_headers();

  void skip_invalid();

  HypernodeID _current_u;
  HyperedgeID _current_id;
  HyperedgeID _current_last_id;
  const DynamicAdjacencyArray* _dynamic_adjacency_array;
};

class DynamicAdjacencyArray {
  using HyperedgeVector = parallel::scalable_vector<parallel::scalable_vector<HypernodeID>>;
  using EdgeVector = parallel::scalable_vector<std::pair<HypernodeID, HypernodeID>>;
  using ThreadLocalCounter = tbb::enumerable_thread_specific<parallel::scalable_vector<size_t>>;
  using AtomicCounter = parallel::scalable_vector<parallel::IntegralAtomicWrapper<size_t>>;

  using AcquireLockFunc = std::function<void (const HypernodeID)>;
  using ReleaseLockFunc = std::function<void (const HypernodeID)>;
  using MarkEdgeFunc = std::function<bool (const HyperedgeID)>;
  using CaseOneFunc = std::function<void (const HyperedgeID)>;
  using CaseTwoFunc = std::function<void (const HyperedgeID)>;
  #define NOOP_LOCK_FUNC [] (const HypernodeID) { }

  static constexpr bool enable_heavy_assert = false;

 public:
  // Represents one (directed) edge of a vertex.
  // Note that we maintain a direct link to the corresponding
  // backwards edge via its edge id, which is updated when any
  // edge ids change.
  struct Edge {
    static_assert(sizeof(HyperedgeID) == sizeof(HypernodeID));

    bool isSinglePin() const {
      return source == target;
    }

    bool isValid() const {
      return target != kInvalidHypernode;
    }

    void enable() {
      target = source;
    }

    void disable() {
      ASSERT(isSinglePin());
      target = kInvalidHypernode;
    }

    // ! Index of target node
    HypernodeID target;
    // ! Index of source node
    HypernodeID source;
    // ! edge weight
    HyperedgeWeight weight;
    // ! id of the backwards edge
    HyperedgeID back_edge;
  };

  struct RemovedEdge {
    // current id of removed edge
    HyperedgeID edge_id;
    // id of the edge before it was removed
    HyperedgeID old_id;
  };

 private:
  // Header of the incident edge list of a vertex. The incident edge lists
  // contracted into one vertex are concatenated in a double linked list.
  struct Header {
    Header() :
      prev(0),
      next(0),
      it_prev(0),
      it_next(0),
      tail(0),
      first_active(0),
      first_inactive(0),
      degree(0),
      is_head(false) { }

    explicit Header(const HypernodeID u) :
      prev(u),
      next(u),
      it_prev(u),
      it_next(u),
      tail(u),
      first_active(0),
      first_inactive(0),
      degree(0),
      is_head(true) { }

    HyperedgeID size() const {
      return first_inactive - first_active;
    }

    // ! Previous incident edge list
    HypernodeID prev;
    // ! Next incident edge list
    HypernodeID next;
    // ! Previous non-empty incident edge list
    HypernodeID it_prev;
    // ! Next non-empty incident edge list
    HypernodeID it_next;
    // ! If we append a vertex v to the incident edge list of a vertex u, we store
    // ! the previous tail of vertex v, such that we can restore the list of v
    // ! during uncontraction
    HypernodeID tail;
    // ! Id of the first edge
    HyperedgeID first;
    // ! All incident edges between [first_active, first_inactive) are active
    HyperedgeID first_active;
    // ! All incident edges between [first_active, first_inactive) are active
    HyperedgeID first_inactive;
    // ! Degree of the vertex
    HyperedgeID degree;
    // ! True, if the vertex is the head of a incident edge list
    bool is_head;
  };

  // Used for detecting parallel edges.
  // Represents one edge with the required information
  // for detecting duplicates and removing the represented edge.
  struct ParallelEdgeInformation {
    ParallelEdgeInformation() = default;

    ParallelEdgeInformation(HypernodeID target, HyperedgeID edge_id, HyperedgeID unique_id):
        target(target), edge_id(edge_id), unique_id(unique_id) { }

    // ! Index of target node
    HypernodeID target;
    // ! Index of edge
    HyperedgeID edge_id;
    // ! Unique id of edge
    HyperedgeID unique_id;
  };

  using ThreadLocalParallelEdgeVector = tbb::enumerable_thread_specific<vec<ParallelEdgeInformation>>;

 public:
  using const_iterator = IncidentEdgeIterator;

  DynamicAdjacencyArray() :
    _num_nodes(0),
    _header_array(),
    _edges(),
    _removable_edges(),
    _edge_mapping() { }

  DynamicAdjacencyArray(const HypernodeID num_nodes,
                        const EdgeVector& edge_vector,
                        const HyperedgeWeight* edge_weight = nullptr) :
    _num_nodes(num_nodes),
    _header_array(),
    _edges(),
    _thread_local_vec(),
    _removable_edges(),
    _edge_mapping() {
    construct(edge_vector, edge_weight);
  }

  MT_KAHYPAR_ATTRIBUTE_ALWAYS_INLINE const Edge& edge(const HyperedgeID e) const {
    ASSERT(e < _edges.size(), "Edge" << e << "does not exist");
    return _edges[e];
  }

  MT_KAHYPAR_ATTRIBUTE_ALWAYS_INLINE Edge& edge(const HyperedgeID e) {
    ASSERT(e <= _edges.size(), "Edge" << e << "does not exist");
    return _edges[e];
  }

  MT_KAHYPAR_ATTRIBUTE_ALWAYS_INLINE HypernodeID numNodes() const {
    return _num_nodes;
  }

  HyperedgeID uniqueEdgeID(const HyperedgeID e) const {
    return std::min(e, edge(e).back_edge);
  }

  // ! Degree of the vertex
  HypernodeID nodeDegree(const HypernodeID u) const {
    ASSERT(u < _num_nodes, "Hypernode" << u << "does not exist");
    return header(u).degree;
  }

  // ! Returns a range to loop over the incident edges of hypernode u.
  IteratorRange<IncidentEdgeIterator> incidentEdges(const HypernodeID u) const {
    ASSERT(u < _num_nodes, "Hypernode" << u << "does not exist");
    return IteratorRange<IncidentEdgeIterator>(
      IncidentEdgeIterator(u, this, UL(0), false),
      IncidentEdgeIterator(u, this, UL(0), true));
  }

  // ! Returns a range to loop over the incident edges of hypernode u.
  IteratorRange<IncidentEdgeIterator> incidentEdges(const HypernodeID u,
                                                    const size_t pos) const {
    ASSERT(u < _num_nodes, "Hypernode" << u << "does not exist");
    return IteratorRange<IncidentEdgeIterator>(
      IncidentEdgeIterator(u, this, pos, false),
      IncidentEdgeIterator(u, this, UL(0), true));
  }

  // ! Returns a range to loop over all edges.
  IteratorRange<EdgeIterator> edges() const {
    return IteratorRange<EdgeIterator>(
      EdgeIterator(0, this),
      EdgeIterator(_num_nodes, this));
  }


  // ! Iterates in parallel over all active edges and calls function f
  // ! for each net
  template<typename F>
  void doParallelForAllEdges(const F& f) const {
    tbb::parallel_for(ID(0), _num_nodes, [&](const HypernodeID& head) {
      const HyperedgeID last = firstInactiveEdge(head);
      for (HyperedgeID e = firstActiveEdge(head); e < last; ++e) {
        if (edge(e).isValid()) {
          f(e);
        }
      }
    });
  }

  // ! Contracts two incident list of u and v, whereby u is the representative and
  // ! v the contraction partner of the contraction. The contraction involves to remove
  // ! all incident edges shared between u and v from the incident edge list of v and append
  // ! the list of v to u, while also updating the back edges of all affected edges.
  void contract(const HypernodeID u,
                const HypernodeID v,
                const AcquireLockFunc& acquire_lock = NOOP_LOCK_FUNC,
                const ReleaseLockFunc& release_lock = NOOP_LOCK_FUNC);

  // ! Uncontract two previously contracted vertices u and v.
  // ! Uncontraction means restoring the incident edge list of v from the current list of u
  // ! and updating all affected backward edges.
  // ! Note, uncontraction must be done in relative contraction order
  void uncontract(const HypernodeID u,
                  const HypernodeID v,
                  const AcquireLockFunc& acquire_lock = NOOP_LOCK_FUNC,
                  const ReleaseLockFunc& release_lock = NOOP_LOCK_FUNC);

  // ! Uncontract two previously contracted vertices u and v.
  // ! Uncontraction means restoring the incident edge list of v from the current list of u
  // ! and updating all affected backward edges.
  // ! Additionally it calls case_one_func for an edge e, if u and v were previously both
  // ! adjacent to e and case_two_func if only v was previously adjacent to e.
  // ! mark_edge must return whether the edge was already locked previously in this round of uncontractions.
  // ! Note, uncontraction must be done in relative contraction order.
  void uncontract(const HypernodeID u,
                  const HypernodeID v,
                  const MarkEdgeFunc& mark_edge,
                  const CaseOneFunc& case_one_func,
                  const CaseTwoFunc& case_two_func,
                  const AcquireLockFunc& acquire_lock,
                  const ReleaseLockFunc& release_lock);

  parallel::scalable_vector<RemovedEdge> removeSinglePinAndParallelEdges();

  void restoreSinglePinAndParallelEdges(const parallel::scalable_vector<RemovedEdge>& edges_to_restore);

  DynamicAdjacencyArray copy(parallel_tag_t) const;

  DynamicAdjacencyArray copy() const;

  void reset();

  void sortIncidentEdges();

  size_t size_in_bytes() const {
    return _edges.size() * sizeof(Edge)
      + _edge_mapping.size() * sizeof(HyperedgeID)
      + _header_array.size() * sizeof(Header);
  }

 private:
  friend class IncidentEdgeIterator;
  friend class EdgeIterator;

  class HeaderIterator {
    public:
    using iterator_category = std::forward_iterator_tag;
    using value_type = HypernodeID;
    using reference = HypernodeID&;
    using pointer = const HypernodeID*;
    using difference_type = std::ptrdiff_t;

    HeaderIterator(const HypernodeID u,
                   const DynamicAdjacencyArray* dynamic_adjacency_array,
                   const bool end):
      _u(u),
      _current_u(u),
      _dynamic_adjacency_array(dynamic_adjacency_array),
      _end(end) { }

    HypernodeID operator* () const {
      return _current_u;
    }

    HeaderIterator & operator++ () {
      _current_u = _dynamic_adjacency_array->header(_current_u).next;
      if (_current_u == _u) {
        _end = true;
      }
      return *this;
    }

    HeaderIterator operator++ (int) {
      HeaderIterator copy = *this;
      operator++ ();
      return copy;
    }

    MT_KAHYPAR_ATTRIBUTE_ALWAYS_INLINE bool operator== (const HeaderIterator& rhs) {
      return _u == rhs._u && _end == rhs._end;
    }

    MT_KAHYPAR_ATTRIBUTE_ALWAYS_INLINE bool operator!= (const HeaderIterator& rhs) {
      return !(*this == rhs);
    }

    private:
    HypernodeID _u;
    HypernodeID _current_u;
    const DynamicAdjacencyArray* _dynamic_adjacency_array;
    bool _end;
  };

  MT_KAHYPAR_ATTRIBUTE_ALWAYS_INLINE const Header& header(const HypernodeID u) const {
    ASSERT(u <= _num_nodes, "Hypernode" << u << "does not exist");
    return _header_array[u];
  }

  MT_KAHYPAR_ATTRIBUTE_ALWAYS_INLINE Header& header(const HypernodeID u) {
    ASSERT(u <= _num_nodes, "Hypernode" << u << "does not exist");
    return _header_array[u];
  }

  MT_KAHYPAR_ATTRIBUTE_ALWAYS_INLINE HyperedgeID firstEdge(const HypernodeID u) const {
    ASSERT(u <= _num_nodes, "Hypernode" << u << "does not exist");
    return header(u).first;
  }

  MT_KAHYPAR_ATTRIBUTE_ALWAYS_INLINE HyperedgeID firstActiveEdge(const HypernodeID u) const {
    ASSERT(u <= _num_nodes, "Hypernode" << u << "does not exist");
    return header(u).first_active;
  }

  MT_KAHYPAR_ATTRIBUTE_ALWAYS_INLINE HyperedgeID firstInactiveEdge(const HypernodeID u) const {
    ASSERT(u <= _num_nodes, "Hypernode" << u << "does not exist");
    return header(u).first_inactive;
  }

  MT_KAHYPAR_ATTRIBUTE_ALWAYS_INLINE HyperedgeID lastEdge(const HypernodeID u) const {
    ASSERT(u <= _num_nodes, "Hypernode" << u << "does not exist");
    return header(u + 1).first;
  }

  // ! Returns a range to loop over the headers of node u.
  IteratorRange<HeaderIterator> headers(const HypernodeID u) const {
    ASSERT(u < _num_nodes, "Hypernode" << u << "does not exist");
    return IteratorRange<HeaderIterator>(
      HeaderIterator(u, this, false),
      HeaderIterator(u, this, true));
  }

  void initializeEdgeMapping(Array<HyperedgeID>& mapping) {
    ASSERT(mapping.size() == _edges.size());
    tbb::parallel_for(ID(0), ID(mapping.size()), [&](const HyperedgeID e) {
      mapping[e] = e;
    });
  }

  // ! Updates all backedges using the provided mapping
  void applyEdgeMapping(Array<HyperedgeID>& mapping) {
    ASSERT(mapping.size() == _edges.size());
    tbb::parallel_for(ID(0), ID(mapping.size()), [&](const HyperedgeID e) {
      edge(e).back_edge = mapping[edge(e).back_edge];
    });
  }

  void swapAndUpdateMapping(const HyperedgeID e, const HyperedgeID new_id);

  void append(const HypernodeID u, const HypernodeID v);

  void splice(const HypernodeID u, const HypernodeID v);

  void removeEmptyIncidentEdgeList(const HypernodeID u);

  void restoreIteratorPointers(const HypernodeID u);

  void restoreItLink(const HypernodeID u, const HypernodeID prev, const HypernodeID current);

  void construct(const EdgeVector& edge_vector, const HyperedgeWeight* edge_weight = nullptr);

  bool verifyIteratorPointers(const HypernodeID u) const;

  bool verifyBackEdges() const;

  HypernodeID _num_nodes;
  Array<Header> _header_array;
  Array<Edge> _edges;
  // data used during parallel edge removal
  ThreadLocalParallelEdgeVector _thread_local_vec;
  kahypar::ds::FastResetFlagArray<> _removable_edges;
  Array<HyperedgeID> _edge_mapping;
};

}  // namespace ds
}  // namespace mt_kahypar
