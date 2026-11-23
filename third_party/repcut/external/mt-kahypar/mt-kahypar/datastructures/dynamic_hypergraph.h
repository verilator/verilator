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

#include <mutex>
#include <queue>

#include <tbb/parallel_for.h>

#include "include/mtkahypartypes.h"

#include "kahypar-resources/meta/mandatory.h"
#include "kahypar-resources/datastructure/fast_reset_flag_array.h"
#include "kahypar-resources/utils/math.h"

#include "mt-kahypar/datastructures/hypergraph_common.h"
#include "mt-kahypar/datastructures/fixed_vertex_support.h"
#include "mt-kahypar/datastructures/incident_net_array.h"
#include "mt-kahypar/datastructures/contraction_tree.h"
#include "mt-kahypar/datastructures/thread_safe_fast_reset_flag_array.h"
#include "mt-kahypar/parallel/stl/scalable_vector.h"
#include "mt-kahypar/utils/memory_tree.h"
#include "mt-kahypar/utils/exception.h"

namespace mt_kahypar {
namespace ds {

// Forward
class DynamicHypergraphFactory;
template <typename Hypergraph,
          typename ConnectivityInformation>
class PartitionedHypergraph;

class DynamicHypergraph {

  static constexpr bool debug = false;
  static constexpr bool enable_heavy_assert = false;

  static_assert(std::is_unsigned<HypernodeID>::value, "Hypernode ID must be unsigned");
  static_assert(std::is_unsigned<HyperedgeID>::value, "Hyperedge ID must be unsigned");

  // ! In order to update gain cache correctly for an uncontraction (u,v),
  // ! the partitioned hypergraph has to know wheter v replaces u in a hyperedge
  // ! or both a incident to that hyperedge after uncontraction. Therefore, the partitioned
  // ! hypergraph passes two lambda functions to the batch uncontraction function, one for
  // ! each case.
  using UncontractionFunction = std::function<void (const HypernodeID, const HypernodeID, const HyperedgeID)>;
  #define NOOP_BATCH_FUNC [] (const HypernodeID, const HypernodeID, const HyperedgeID) { }

  /*!
  * This struct is used during multilevel coarsening to efficiently
  * detect parallel hyperedges.
  */
  struct ContractedHyperedgeInformation {
    HyperedgeID he = kInvalidHyperedge;
    size_t hash = kEdgeHashSeed;
    size_t size = std::numeric_limits<size_t>::max();
    bool valid = false;
  };

 private:
  /**
   * Represents a hypernode of the hypergraph and contains all information
   * associated with a vertex.
   */
  class Hypernode {
   public:
    using IDType = HypernodeID;

    Hypernode() :
      _weight(1),
      _community_id(0),
      _batch_idx(std::numeric_limits<HypernodeID>::max()),
      _valid(false) { }

    Hypernode(const bool valid) :
      _weight(1),
      _community_id(0),
      _batch_idx(std::numeric_limits<HypernodeID>::max()),
      _valid(valid) { }

    bool isDisabled() const {
      return _valid == false;
    }

    void enable() {
      ASSERT(isDisabled());
      _valid = true;
    }

    void disable() {
      ASSERT(!isDisabled());
      _valid = false;
    }

    HypernodeWeight weight() const {
      return _weight;
    }

    void setWeight(HypernodeWeight weight) {
      ASSERT(!isDisabled());
      _weight = weight;
    }

    PartitionID communityID() const {
      return _community_id;
    }

    void setCommunityID(const PartitionID community_id) {
      ASSERT(!isDisabled());
      _community_id = community_id;
    }

    HypernodeID batchIndex() const {
      return _batch_idx;
    }

    void setBatchIndex(const HypernodeID batch_idx) {
      _batch_idx = batch_idx;
    }

   private:
    // ! Hypernode weight
    HypernodeWeight _weight;
    // ! Community id
    PartitionID _community_id;
    // ! Index of the uncontraction batch in which this hypernode is contained in
    HypernodeID _batch_idx;
    // ! Flag indicating whether or not the element is active.
    bool _valid;
  };

  /**
   * Represents a hyperedge of the hypergraph and contains all information
   * associated with a net (except connectivity information).
   */
  class Hyperedge {
   public:
    using IDType = HyperedgeID;

    Hyperedge() :
      _begin(0),
      _size(0),
      _weight(1),
      _hash(kEdgeHashSeed),
      _valid(false) { }

    // Sentinel Constructor
    Hyperedge(const size_t begin) :
      _begin(begin),
      _size(0),
      _weight(1),
      _hash(kEdgeHashSeed),
      _valid(false) { }

    // ! Disables the hypernode/hyperedge. Disable hypernodes/hyperedges will be skipped
    // ! when iterating over the set of all nodes/edges.
    void disable() {
      ASSERT(!isDisabled());
      _valid = false;
    }

    void enable() {
      ASSERT(isDisabled());
      _valid = true;
    }

    bool isDisabled() const {
      return _valid == false;
    }

    // ! Returns the index of the first element in _incidence_array
    size_t firstEntry() const {
      return _begin;
    }

    // ! Sets the index of the first element in _incidence_array to begin
    void setFirstEntry(size_t begin) {
      ASSERT(!isDisabled());
      _begin = begin;
    }

    // ! Returns the index of the first element in _incidence_array
    size_t firstInvalidEntry() const {
      return _begin + _size;
    }

    size_t size() const {
      ASSERT(!isDisabled());
      return _size;
    }

    void setSize(size_t size) {
      ASSERT(!isDisabled());
      _size = size;
    }

    void incrementSize() {
      ASSERT(!isDisabled());
      ++_size;
    }

    void decrementSize() {
      ASSERT(!isDisabled());
      --_size;
    }

    HyperedgeWeight weight() const {
      ASSERT(!isDisabled());
      return _weight;
    }

    void setWeight(HyperedgeWeight weight) {
      ASSERT(!isDisabled());
      _weight = weight;
    }

    size_t& hash() {
      return _hash;
    }

    size_t hash() const {
      return _hash;
    }

    bool operator== (const Hyperedge& rhs) const {
      return _begin == rhs._begin && _size == rhs._size && _weight == rhs._weight;
    }

    bool operator!= (const Hyperedge& rhs) const {
      return _begin != rhs._begin || _size != rhs._size || _weight != rhs._weight;
    }

   private:
    // ! Index of the first element in _incidence_array
    size_t _begin;
    // ! Number of pins
    size_t _size;
    // ! hyperedge weight
    HyperedgeWeight _weight;
    // ! Hash of pins
    size_t _hash;
    // ! Flag indicating whether or not the element is active.
    bool _valid;
  };

  /*!
   * Iterator for HypergraphElements (Hypernodes/Hyperedges)
   *
   * The iterator is used in for-each loops over all hypernodes/hyperedges.
   * In order to support iteration over coarsened hypergraphs, this iterator
   * skips over HypergraphElements marked as invalid.
   * Iterating over the set of vertices \f$V\f$ therefore is linear in the
   * size \f$|V|\f$ of the original hypergraph - even if it has been coarsened
   * to much smaller size. The same also holds true for for-each loops over
   * the set of hyperedges.
   *
   * In order to be as generic as possible, the iterator does not expose the
   * internal Hypernode/Hyperedge representations. Instead only handles to
   * the respective elements are returned, i.e. the IDs of the corresponding
   * hypernodes/hyperedges.
   *
   */
  template <typename ElementType>
  class HypergraphElementIterator {
   public:
    using IDType = typename ElementType::IDType;
    using iterator_category = std::forward_iterator_tag;
    using value_type = IDType;
    using reference = IDType&;
    using pointer = const IDType*;
    using difference_type = std::ptrdiff_t;

    /*!
     * Construct a HypergraphElementIterator
     * See GenericHypergraph::nodes() or GenericHypergraph::edges() for usage.
     *
     * If start_element is invalid, the iterator advances to the first valid
     * element.
     *
     * \param start_element A pointer to the starting position
     * \param id The index of the element the pointer points to
     * \param max_id The maximum index allowed
     */
    HypergraphElementIterator(const ElementType* start_element, IDType id, IDType max_id) :
      _id(id),
      _max_id(max_id),
      _element(start_element) {
      if (_id != _max_id && _element->isDisabled()) {
        operator++ ();
      }
    }

    // ! Returns the id of the element the iterator currently points to.
    IDType operator* () const {
      return _id;
    }

    // ! Prefix increment. The iterator advances to the next valid element.
    HypergraphElementIterator & operator++ () {
      ASSERT(_id < _max_id);
      do {
        ++_id;
        ++_element;
      } while (_id < _max_id && _element->isDisabled());
      return *this;
    }

    // ! Postfix increment. The iterator advances to the next valid element.
    HypergraphElementIterator operator++ (int) {
      HypergraphElementIterator copy = *this;
      operator++ ();
      return copy;
    }

    bool operator!= (const HypergraphElementIterator& rhs) {
      return _id != rhs._id;
    }

    bool operator== (const HypergraphElementIterator& rhs) {
      return _id == rhs._id;
    }

   private:
    // Handle to the HypergraphElement the iterator currently points to
    IDType _id = 0;
    // Maximum allowed index
    IDType _max_id = 0;
    // HypergraphElement the iterator currently points to
    const ElementType* _element = nullptr;
  };

  static_assert(std::is_trivially_copyable<Hypernode>::value, "Hypernode is not trivially copyable");
  static_assert(std::is_trivially_copyable<Hyperedge>::value, "Hyperedge is not trivially copyable");

  enum class ContractionResult : uint8_t {
    CONTRACTED = 0,
    PENDING_CONTRACTIONS = 1,
    WEIGHT_LIMIT_REACHED = 2,
    INVALID_FIXED_VERTEX_CONTRACTION = 3
  };

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

  using IncidenceArray = Array<HypernodeID>;
  using OwnershipVector = parallel::scalable_vector<parallel::IntegralAtomicWrapper<bool>>;
  using ThreadLocalHyperedgeVector = tbb::enumerable_thread_specific<parallel::scalable_vector<HyperedgeID>>;
  using ThreadLocalBitset = tbb::enumerable_thread_specific<kahypar::ds::FastResetFlagArray<>>;
  using ThreadLocalBitvector = tbb::enumerable_thread_specific<parallel::scalable_vector<bool>>;

 public:
  static constexpr bool is_graph = false;
  static constexpr bool is_static_hypergraph = false;
  static constexpr bool is_partitioned = false;
  static constexpr size_t SIZE_OF_HYPERNODE = sizeof(Hypernode);
  static constexpr size_t SIZE_OF_HYPEREDGE = sizeof(Hyperedge);
  static constexpr mt_kahypar_hypergraph_type_t TYPE = DYNAMIC_HYPERGRAPH;

  // ! Factory
  using Factory = DynamicHypergraphFactory;
  // ! Iterator to iterate over the hypernodes
  using HypernodeIterator = HypergraphElementIterator<const Hypernode>;
  // ! Iterator to iterate over the hyperedges
  using HyperedgeIterator = HypergraphElementIterator<const Hyperedge>;
  // ! Iterator to iterate over the pins of a hyperedge
  using IncidenceIterator = typename IncidenceArray::const_iterator;
  // ! Iterator to iterate over the incident nets of a hypernode
  using IncidentNetsIterator = typename IncidentNetArray::const_iterator;

  struct ParallelHyperedge {
    HyperedgeID removed_hyperedge;
    HyperedgeID representative;
  };

  explicit DynamicHypergraph() :
    _num_hypernodes(0),
    _num_removed_hypernodes(0),
    _max_removed_degree_zero_hn_weight(0),
    _num_hyperedges(0),
    _num_removed_hyperedges(0),
    _max_edge_size(0),
    _num_pins(0),
    _total_degree(0),
    _total_weight(0),
    _version(0),
    _contraction_index(0),
    _hypernodes(),
    _contraction_tree(),
    _incident_nets(),
    _acquired_hns(),
    _hyperedges(),
    _incidence_array(),
    _acquired_hes(),
    _hes_to_resize_flag_array(),
    _failed_hyperedge_contractions(),
    _he_bitset(),
    _removable_single_pin_and_parallel_nets(),
    _fixed_vertices() { }

  DynamicHypergraph(const DynamicHypergraph&) = delete;
  DynamicHypergraph & operator= (const DynamicHypergraph &) = delete;

  DynamicHypergraph(DynamicHypergraph&& other) :
    _num_hypernodes(other._num_hypernodes),
    _num_removed_hypernodes(other._num_removed_hypernodes),
    _max_removed_degree_zero_hn_weight(other._max_removed_degree_zero_hn_weight),
    _num_hyperedges(other._num_hyperedges),
    _num_removed_hyperedges(other._num_removed_hyperedges),
    _max_edge_size(other._max_edge_size),
    _num_pins(other._num_pins),
    _total_degree(other._total_degree),
    _total_weight(other._total_weight),
    _version(other._version),
    _contraction_index(0),
    _hypernodes(std::move(other._hypernodes)),
    _contraction_tree(std::move(other._contraction_tree)),
    _incident_nets(std::move(other._incident_nets)),
    _acquired_hns(std::move(other._acquired_hns)),
    _hyperedges(std::move(other._hyperedges)),
    _incidence_array(std::move(other._incidence_array)),
    _acquired_hes(std::move(other._acquired_hes)),
    _hes_to_resize_flag_array(std::move(other._hes_to_resize_flag_array)),
    _failed_hyperedge_contractions(std::move(other._failed_hyperedge_contractions)),
    _he_bitset(std::move(other._he_bitset)),
    _removable_single_pin_and_parallel_nets(std::move(other._removable_single_pin_and_parallel_nets)),
    _fixed_vertices(std::move(other._fixed_vertices)) {
    _fixed_vertices.setHypergraph(this);
  }

  DynamicHypergraph & operator= (DynamicHypergraph&& other) {
    _num_hypernodes = other._num_hypernodes;
    _num_removed_hypernodes = other._num_removed_hypernodes;
    _max_removed_degree_zero_hn_weight = other._max_removed_degree_zero_hn_weight;
    _num_hyperedges = other._num_hyperedges;
    _num_removed_hyperedges = other._num_removed_hyperedges;
    _max_edge_size = other._max_edge_size;
    _num_pins = other._num_pins;
    _total_degree = other._total_degree;
    _total_weight = other._total_weight;
    _version = other._version;
    _contraction_index.store(other._contraction_index.load());
    _hypernodes = std::move(other._hypernodes);
    _contraction_tree = std::move(other._contraction_tree);
    _incident_nets = std::move(other._incident_nets);
    _acquired_hns = std::move(other._acquired_hns);
    _hyperedges = std::move(other._hyperedges);
    _incidence_array = std::move(other._incidence_array);
    _acquired_hes = std::move(other._acquired_hes);
    _hes_to_resize_flag_array = std::move(other._hes_to_resize_flag_array);
    _failed_hyperedge_contractions = std::move(other._failed_hyperedge_contractions);
    _he_bitset = std::move(other._he_bitset);
    _removable_single_pin_and_parallel_nets = std::move(other._removable_single_pin_and_parallel_nets);
    _fixed_vertices = std::move(other._fixed_vertices);
    _fixed_vertices.setHypergraph(this);
    return *this;
  }

  ~DynamicHypergraph() {
    freeInternalData();
  }

  // ####################### General Hypergraph Stats #######################

  // ! Initial number of hypernodes
  HypernodeID initialNumNodes() const {
    return _num_hypernodes;
  }

  // ! Number of removed hypernodes
  HypernodeID numRemovedHypernodes() const {
    return _num_removed_hypernodes;
  }

  // ! Max weight of removed degree zero vertex
  HypernodeWeight maxWeightOfRemovedDegreeZeroNode() const {
    return _max_removed_degree_zero_hn_weight;
  }

  // ! Initial number of hyperedges
  HyperedgeID initialNumEdges() const {
    return _num_hyperedges;
  }

  // ! Number of removed hyperedges
  HyperedgeID numRemovedHyperedges() const {
    return _num_removed_hyperedges;
  }

  // ! Set the number of removed hyperedges
  void setNumRemovedHyperedges(const HyperedgeID num_removed_hyperedges) {
    _num_removed_hyperedges = num_removed_hyperedges;
  }

  // ! Initial number of pins
  HypernodeID initialNumPins() const {
    return _num_pins;
  }

  // ! Initial sum of the degree of all vertices
  HypernodeID initialTotalVertexDegree() const {
    return _total_degree;
  }

  // ! Total weight of hypergraph
  HypernodeWeight totalWeight() const {
    return _total_weight;
  }

  // ! Computes the total node weight of the hypergraph
  void computeAndSetTotalNodeWeight(parallel_tag_t);

  // ####################### Iterators #######################

  // ! Iterates in parallel over all active nodes and calls function f
  // ! for each vertex
  template<typename F>
  void doParallelForAllNodes(const F& f) {
    static_cast<const DynamicHypergraph&>(*this).doParallelForAllNodes(f);
  }

  // ! Iterates in parallel over all active nodes and calls function f
  // ! for each vertex
  template<typename F>
  void doParallelForAllNodes(const F& f) const {
    tbb::parallel_for(ID(0), _num_hypernodes, [&](const HypernodeID& hn) {
      if ( nodeIsEnabled(hn) ) {
        f(hn);
      }
    });
  }

  // ! Iterates in parallel over all active edges and calls function f
  // ! for each net
  template<typename F>
  void doParallelForAllEdges(const F& f) {
    static_cast<const DynamicHypergraph&>(*this).doParallelForAllEdges(f);
  }

  // ! Iterates in parallel over all active edges and calls function f
  // ! for each net
  template<typename F>
  void doParallelForAllEdges(const F& f) const {
    tbb::parallel_for(ID(0), _num_hyperedges, [&](const HyperedgeID& he) {
      if ( edgeIsEnabled(he) ) {
        f(he);
      }
    });
  }

  // ! Returns a range of the active nodes of the hypergraph
  IteratorRange<HypernodeIterator> nodes() const {
    return IteratorRange<HypernodeIterator>(
      HypernodeIterator(_hypernodes.data(), ID(0), _num_hypernodes),
      HypernodeIterator(_hypernodes.data() + _num_hypernodes, _num_hypernodes, _num_hypernodes));
  }

  // ! Returns a range of the active edges of the hypergraph
  IteratorRange<HyperedgeIterator> edges() const {
    return IteratorRange<HyperedgeIterator>(
      HyperedgeIterator(_hyperedges.data(), ID(0), _num_hyperedges),
      HyperedgeIterator(_hyperedges.data() + _num_hyperedges, _num_hyperedges, _num_hyperedges));
  }

  // ! Returns a range to loop over the incident nets of hypernode u.
  IteratorRange<IncidentNetsIterator> incidentEdges(const HypernodeID u) const {
    ASSERT(u < _num_hypernodes, "Hypernode" << u << "does not exist");
    return _incident_nets.incidentEdges(u);
  }

  // ! Returns a range to loop over the pins of hyperedge e.
  IteratorRange<IncidenceIterator> pins(const HyperedgeID e) const {
    ASSERT(!hyperedge(e).isDisabled(), "Hyperedge" << e << "is disabled");
    const Hyperedge& he = hyperedge(e);
    return IteratorRange<IncidenceIterator>(
      _incidence_array.cbegin() + he.firstEntry(),
      _incidence_array.cbegin() + he.firstInvalidEntry());
  }

  // ####################### Hypernode Information #######################

  // ! Weight of a vertex
  HypernodeWeight nodeWeight(const HypernodeID u) const {
    ASSERT(u < _num_hypernodes, "Hypernode" << u << "does not exist");
    return hypernode(u).weight();
  }

  // ! Sets the weight of a vertex
  void setNodeWeight(const HypernodeID u, const HypernodeWeight weight) {
    ASSERT(!hypernode(u).isDisabled(), "Hypernode" << u << "is disabled");
    return hypernode(u).setWeight(weight);
  }

  // ! Degree of a hypernode
  HyperedgeID nodeDegree(const HypernodeID u) const {
    ASSERT(u < _num_hypernodes, "Hypernode" << u << "does not exist");
    return _incident_nets.nodeDegree(u);
  }

  // ! Returns, whether a hypernode is enabled or not
  bool nodeIsEnabled(const HypernodeID u) const {
    return !hypernode(u).isDisabled();
  }

  // ! Enables a hypernode (must be disabled before)
  void enableHypernode(const HypernodeID u) {
    hypernode(u).enable();
  }

  // ! Disables a hypernode (must be enabled before)
  void disableHypernode(const HypernodeID u) {
    hypernode(u).disable();
  }

  // ! Removes a hypernode (must be enabled before)
  void removeHypernode(const HypernodeID u) {
    hypernode(u).disable();
    ++_num_removed_hypernodes;
  }

  // ! Removes a degree zero hypernode
  void removeDegreeZeroHypernode(const HypernodeID u) {
    ASSERT(nodeDegree(u) == 0);
    removeHypernode(u);
    _max_removed_degree_zero_hn_weight =
      std::max(_max_removed_degree_zero_hn_weight, nodeWeight(u));
  }

  // ! Restores a degree zero hypernode
  void restoreDegreeZeroHypernode(const HypernodeID u) {
    hypernode(u).enable();
    ASSERT(nodeDegree(u) == 0);
    _max_removed_degree_zero_hn_weight = 0;
  }

  // ####################### Hyperedge Information #######################

  // ! Weight of a hyperedge
  HyperedgeWeight edgeWeight(const HyperedgeID e) const {
    ASSERT(!hyperedge(e).isDisabled(), "Hyperedge" << e << "is disabled");
    return hyperedge(e).weight();
  }

  // ! Sets the weight of a hyperedge
  void setEdgeWeight(const HyperedgeID e, const HyperedgeWeight weight) {
    ASSERT(!hyperedge(e).isDisabled(), "Hyperedge" << e << "is disabled");
    return hyperedge(e).setWeight(weight);
  }

  // ! Number of pins of a hyperedge
  HypernodeID edgeSize(const HyperedgeID e) const {
    ASSERT(!hyperedge(e).isDisabled(), "Hyperedge" << e << "is disabled");
    return hyperedge(e).size();
  }

  // ! Maximum size of a hyperedge
  HypernodeID maxEdgeSize() const {
    return _max_edge_size;
  }

  // ! Hash value defined over the pins of a hyperedge
  size_t edgeHash(const HyperedgeID e) const {
    ASSERT(!hyperedge(e).isDisabled(), "Hyperedge" << e << "is disabled");
    return hyperedge(e).hash();
  }

  // ! Returns, whether a hyperedge is enabled or not
  bool edgeIsEnabled(const HyperedgeID e) const {
    return !hyperedge(e).isDisabled();
  }

  // ! Enables a hyperedge (must be disabled before)
  void enableHyperedge(const HyperedgeID e) {
    hyperedge(e).enable();
  }

  // ! Disabled a hyperedge (must be enabled before)
  void disableHyperedge(const HyperedgeID e) {
    hyperedge(e).disable();
  }

  // ####################### Community Information #######################

  // ! Community id which hypernode u is assigned to
  PartitionID communityID(const HypernodeID u) const {
    ASSERT(u < _num_hypernodes, "Hypernode" << u << "does not exist");
    return hypernode(u).communityID();
  }

  // ! Assign a community to a hypernode
  // ! Note, in order to use all community-related functions, initializeCommunities()
  // ! have to be called after assigning to each vertex a community id
  void setCommunityID(const HypernodeID u, const PartitionID community_id) {
    ASSERT(!hypernode(u).isDisabled(), "Hypernode" << u << "is disabled");
    return hypernode(u).setCommunityID(community_id);
  }

  // ####################### Fixed Vertex Support #######################

  void addFixedVertexSupport(FixedVertexSupport<DynamicHypergraph>&& fixed_vertices) {
    _fixed_vertices = std::move(fixed_vertices);
    _fixed_vertices.setHypergraph(this);
  }

  bool hasFixedVertices() const {
    return _fixed_vertices.hasFixedVertices();
  }

  HypernodeWeight totalFixedVertexWeight() const {
    return _fixed_vertices.totalFixedVertexWeight();
  }

  HypernodeWeight fixedVertexBlockWeight(const PartitionID block) const {
    return _fixed_vertices.fixedVertexBlockWeight(block);
  }

  bool isFixed(const HypernodeID hn) const {
    return _fixed_vertices.isFixed(hn);
  }

  PartitionID fixedVertexBlock(const HypernodeID hn) const {
    return _fixed_vertices.fixedVertexBlock(hn);
  }

  void setMaxFixedVertexBlockWeight(const std::vector<HypernodeWeight> max_block_weights) {
    _fixed_vertices.setMaxBlockWeight(max_block_weights);
  }

  const FixedVertexSupport<DynamicHypergraph>& fixedVertexSupport() const {
    return _fixed_vertices;
  }

  FixedVertexSupport<DynamicHypergraph> copyOfFixedVertexSupport() const {
    return _fixed_vertices.copy();
  }

  // ####################### Contract / Uncontract #######################

  DynamicHypergraph contract(parallel::scalable_vector<HypernodeID>&, bool deterministic = false) {
    unused(deterministic);
    throw UnsupportedOperationException(
      "contract(c, id) is not supported in dynamic hypergraph");
    return DynamicHypergraph();
  }

  /**!
   * Registers a contraction in the hypergraph whereas vertex u is the representative
   * of the contraction and v its contraction partner. Several threads can call this function
   * in parallel. The function adds the contraction of u and v to a contraction tree that determines
   * a parallel execution order and synchronization points for all running contractions.
   * The contraction can be executed by calling function contract(v, max_node_weight).
   */
  bool registerContraction(const HypernodeID u, const HypernodeID v);

  /**!
   * Contracts a previously registered contraction. Representative u of vertex v is looked up
   * in the contraction tree and performed if there are no pending contractions in the subtree
   * of v and the contractions respects the maximum allowed node weight. If (u,v) is the last
   * pending contraction in the subtree of u then the function recursively contracts also
   * u (if any contraction is registered). Therefore, function can return several contractions
   * or also return an empty contraction vector.
   */
  size_t contract(const HypernodeID v,
                  const HypernodeWeight max_node_weight = std::numeric_limits<HypernodeWeight>::max());

  /**
   * Uncontracts a batch of contractions in parallel. The batches must be uncontracted exactly
   * in the order computed by the function createBatchUncontractionHierarchy(...).
   * The two uncontraction functions are required by the partitioned hypergraph to restore
   * pin counts and gain cache values.
   */
  void uncontract(const Batch& batch,
                  const UncontractionFunction& case_one_func = NOOP_BATCH_FUNC,
                  const UncontractionFunction& case_two_func = NOOP_BATCH_FUNC);

  /**
   * Computes a batch uncontraction hierarchy. A batch is a vector of mementos
   * (uncontractions) that are uncontracted in parallel. The function returns a vector
   * of versioned batch vectors. A new version of the hypergraph is induced if we perform
   * single-pin and parallel net detection. Once we process all batches of a versioned
   * batch vector, we have to restore all previously removed single-pin and parallel nets
   * in order to uncontract the next batch vector. We create for each version of the
   * hypergraph a seperate batch uncontraction hierarchy (see createBatchUncontractionHierarchyOfVersion(...))
   */
  VersionedBatchVector createBatchUncontractionHierarchy(const size_t batch_size,
                                                         const bool test = false);

  // ! Only for testing
  VersionedBatchVector createBatchUncontractionHierarchy(ContractionTree&& tree,
                                                         const size_t batch_size,
                                                         const size_t num_versions = 1) {
    ASSERT(num_versions > 0);
    _version = num_versions - 1;
    _contraction_tree = std::move(tree);
    return createBatchUncontractionHierarchy(batch_size, true);
  }

  // ! Only for testing
  HypernodeID contractionTree(const HypernodeID u) const {
    ASSERT(!hypernode(u).isDisabled(), "Hypernode" << u << "is disabled");
    return _contraction_tree.parent(u);
  }

  // ! Only for testing
  HypernodeID pendingContractions(const HypernodeID u) const {
    ASSERT(!hypernode(u).isDisabled(), "Hypernode" << u << "is disabled");
    return _contraction_tree.pendingContractions(u);
  }

  // ! Only for testing
  void decrementPendingContractions(const HypernodeID u) {
    ASSERT(!hypernode(u).isDisabled(), "Hypernode" << u << "is disabled");
    _contraction_tree.decrementPendingContractions(u);
  }

  // ####################### Remove / Restore Hyperedges #######################

  /*!
  * Removes a hyperedge from the hypergraph. This includes the removal of he from all
  * of its pins and to disable the hyperedge.
  *
  * NOTE, this function is not thread-safe and should only be called in a single-threaded
  * setting.
  */
  void removeEdge(const HyperedgeID he) {
    ASSERT(edgeIsEnabled(he), "Hyperedge" << he << "is disabled");
    kahypar::ds::FastResetFlagArray<>& he_to_remove = _he_bitset.local();
    he_to_remove.set(he, true);
    for ( const HypernodeID& pin : pins(he) ) {
      _incident_nets.removeIncidentNets(pin, he_to_remove);
    }
    ++_num_removed_hyperedges;
    disableHyperedge(he);
  }

  /*!
   * Restores a hyperedge previously removed from the hypergraph.
   */
  void restoreEdge(const HyperedgeID he) {
    ASSERT(!edgeIsEnabled(he), "Hyperedge" << he << "is enabled");
    enableHyperedge(he);
    for ( const HypernodeID& pin : pins(he) ) {
      _incident_nets.restoreIncidentNets(pin);
    }
  }

  /*!
  * Removes a hyperedge from the hypergraph. This includes the removal of he from all
  * of its pins and to disable the hyperedge. Note, in contrast to removeEdge, this function
  * removes hyperedge from all its pins in parallel.
  *
  * NOTE, this function is not thread-safe and should only be called in a single-threaded
  * setting.
  */
  void removeLargeEdge(const HyperedgeID he) {
    ASSERT(edgeIsEnabled(he), "Hyperedge" << he << "is disabled");
    const size_t incidence_array_start = hyperedge(he).firstEntry();
    const size_t incidence_array_end = hyperedge(he).firstInvalidEntry();
    kahypar::ds::FastResetFlagArray<>& he_to_remove = _he_bitset.local();
    he_to_remove.set(he, true);
    tbb::parallel_for(incidence_array_start, incidence_array_end, [&](const size_t pos) {
      const HypernodeID pin = _incidence_array[pos];
      _incident_nets.removeIncidentNets(pin, he_to_remove);
    });
    disableHyperedge(he);
  }

  /*!
   * Restores a large hyperedge previously removed from the hypergraph.
   */
  void restoreLargeEdge(const HyperedgeID& he) {
    ASSERT(!edgeIsEnabled(he), "Hyperedge" << he << "is enabled");
    enableHyperedge(he);
    const size_t incidence_array_start = hyperedge(he).firstEntry();
    const size_t incidence_array_end = hyperedge(he).firstInvalidEntry();
    tbb::parallel_for(incidence_array_start, incidence_array_end, [&](const size_t pos) {
      const HypernodeID pin = _incidence_array[pos];
      _incident_nets.restoreIncidentNets(pin);
    });
  }

  /**
   * Removes single-pin and parallel nets from the hypergraph. The weight
   * of a set of identical nets is aggregated in one representative hyperedge
   * and single-pin hyperedges are removed. Returns a vector of removed hyperedges.
   */
  parallel::scalable_vector<ParallelHyperedge> removeSinglePinAndParallelHyperedges();

  /**
   * Restores a previously removed set of singple-pin and parallel hyperedges. Note, that hes_to_restore
   * must be exactly the same and given in the reverse order as returned by removeSinglePinAndParallelNets(...).
   */
  void restoreSinglePinAndParallelNets(const parallel::scalable_vector<ParallelHyperedge>& hes_to_restore);

  // ####################### Initialization / Reset Functions #######################

  // ! Reset internal community information
  void setCommunityIDs(const parallel::scalable_vector<PartitionID>& community_ids) {
    ASSERT(community_ids.size() == UI64(_num_hypernodes));
    doParallelForAllNodes([&](const HypernodeID& hn) {
      hypernode(hn).setCommunityID(community_ids[hn]);
    });

  }

  // ####################### Copy #######################

  // ! Copy dynamic hypergraph in parallel
  DynamicHypergraph copy(parallel_tag_t) const;

  // ! Copy dynamic hypergraph sequential
  DynamicHypergraph copy() const;

  // ! Reset internal data structure
  void reset() {
    _contraction_tree.reset();
    _incident_nets.reset();
    _version = 0;
  }

  // ! Free internal data in parallel
  void freeInternalData() {
    _num_hypernodes = 0;
    _num_hyperedges = 0;
  }

  void freeTmpContractionBuffer() {
    throw UnsupportedOperationException(
      "freeTmpContractionBuffer() is not supported in dynamic hypergraph");
  }

  void memoryConsumption(utils::MemoryTreeNode* parent) const;

  // ! Only for testing
  bool verifyIncidenceArrayAndIncidentNets();

 private:
  friend class DynamicHypergraphFactory;
  template<typename Hypergraph>
  friend class CommunitySupport;
  template <typename Hypergraph,
            typename ConnectivityInformation>
  friend class PartitionedHypergraph;

  // ####################### Acquiring / Releasing Ownership #######################

  MT_KAHYPAR_ATTRIBUTE_ALWAYS_INLINE void acquireHypernode(const HypernodeID u) {
    ASSERT(u < _num_hypernodes, "Hypernode" << u << "does not exist");
    bool expected = false;
    bool desired = true;
    while ( !_acquired_hns[u].compare_exchange_strong(expected, desired) ) {
      expected = false;
    }
  }

  MT_KAHYPAR_ATTRIBUTE_ALWAYS_INLINE bool tryAcquireHypernode(const HypernodeID u) {
    ASSERT(u < _num_hypernodes, "Hypernode" << u << "does not exist");
    bool expected = false;
    bool desired = true;
    return _acquired_hns[u].compare_exchange_strong(expected, desired);
  }

  MT_KAHYPAR_ATTRIBUTE_ALWAYS_INLINE void releaseHypernode(const HypernodeID u) {
    ASSERT(u < _num_hypernodes, "Hypernode" << u << "does not exist");
    ASSERT(_acquired_hns[u], "Hypernode" << u << "is not acquired!");
    _acquired_hns[u] = false;
  }

  MT_KAHYPAR_ATTRIBUTE_ALWAYS_INLINE void acquireHyperedge(const HyperedgeID e) {
    ASSERT(e < _num_hyperedges, "Hyperedge" << e << "does not exist");
    bool expected = false;
    bool desired = true;
    while ( !_acquired_hes[e].compare_exchange_strong(expected, desired) ) {
      expected = false;
    }
  }

  MT_KAHYPAR_ATTRIBUTE_ALWAYS_INLINE bool tryAcquireHyperedge(const HyperedgeID e) {
    ASSERT(e < _num_hyperedges, "Hyperedge" << e << "does not exist");
    bool expected = false;
    bool desired = true;
    return _acquired_hes[e].compare_exchange_strong(expected, desired);
  }

  MT_KAHYPAR_ATTRIBUTE_ALWAYS_INLINE void releaseHyperedge(const HyperedgeID e) {
    ASSERT(e < _num_hyperedges, "Hyperedge" << e << "does not exist");
    ASSERT(_acquired_hes[e], "Hyperedge" << e << "is not acquired!");
    _acquired_hes[e] = false;
  }

  // ####################### Hypernode Information #######################

  // ! Accessor for hypernode-related information
  MT_KAHYPAR_ATTRIBUTE_ALWAYS_INLINE const Hypernode& hypernode(const HypernodeID u) const {
    ASSERT(u <= _num_hypernodes, "Hypernode" << u << "does not exist");
    return _hypernodes[u];
  }

  // ! To avoid code duplication we implement non-const version in terms of const version
  MT_KAHYPAR_ATTRIBUTE_ALWAYS_INLINE Hypernode& hypernode(const HypernodeID u) {
    return const_cast<Hypernode&>(static_cast<const DynamicHypergraph&>(*this).hypernode(u));
  }

  MT_KAHYPAR_ATTRIBUTE_ALWAYS_INLINE IteratorRange<IncidentNetsIterator> incident_nets_of(const HypernodeID u,
                                                                                          const size_t pos = 0) const {
    return _incident_nets.incidentEdges(u, pos);
  }

  // ####################### Hyperedge Information #######################

  // ! Accessor for hyperedge-related information
  MT_KAHYPAR_ATTRIBUTE_ALWAYS_INLINE const Hyperedge& hyperedge(const HyperedgeID e) const {
    ASSERT(e <= _num_hyperedges, "Hyperedge" << e << "does not exist");
    return _hyperedges[e];
  }

  // ! To avoid code duplication we implement non-const version in terms of const version
  MT_KAHYPAR_ATTRIBUTE_ALWAYS_INLINE Hyperedge& hyperedge(const HyperedgeID e) {
    return const_cast<Hyperedge&>(static_cast<const DynamicHypergraph&>(*this).hyperedge(e));
  }

  // ####################### Contract / Uncontract #######################

  /**!
   * Contracts a previously registered contraction. The contraction of u and v is
   * performed if there are no pending contractions in the subtree of v and the
   * contractions respects the maximum allowed node weight. In case the contraction
   * was performed successfully, enum type CONTRACTED is returned. If contraction
   * was not performed either WEIGHT_LIMIT_REACHED (in case sum of both vertices is
   * greater than the maximum allowed node weight) or PENDING_CONTRACTIONS (in case
   * there are some unfinished contractions in the subtree of v) is returned.
   */
  ContractionResult contract(const HypernodeID u,
                             const HypernodeID v,
                             const HypernodeWeight max_node_weight);

  // ! Performs the contraction of (u,v) inside hyperedge he
  MT_KAHYPAR_ATTRIBUTE_ALWAYS_INLINE void contractHyperedge(const HypernodeID u, const HypernodeID v, const HyperedgeID he,
                                                            kahypar::ds::FastResetFlagArray<>& shared_incident_nets_u_and_v);

  // ! Restore the size of the hyperedge to the size before the batch with
  // ! index batch_index was contracted. After each size increment, we call case_one_func
  // ! that triggers updates in the partitioned hypergraph and gain cache
  MT_KAHYPAR_ATTRIBUTE_ALWAYS_INLINE void restoreHyperedgeSizeForBatch(const HyperedgeID he,
                                                                       const HypernodeID batch_index,
                                                                       const UncontractionFunction& case_one_func);

  // ! Search for the position of pin u in hyperedge he in the incidence array
  MT_KAHYPAR_ATTRIBUTE_ALWAYS_INLINE size_t findPositionOfPinInIncidenceArray(const HypernodeID u,
                                                                              const HyperedgeID he);

  /**
   * Computes a batch uncontraction hierarchy for a specific version of the hypergraph.
   * A batch is a vector of mementos (uncontractions) that are uncontracted in parallel.
   * Each time we perform single-pin and parallel net detection we create a new version of
   * the hypergraph.
   * A batch of uncontractions that is uncontracted in parallel must satisfy two conditions:
   *  1.) All representatives must be active vertices of the hypergraph
   *  2.) For a specific representative its contraction partners must be uncontracted in reverse
   *      contraction order. Meaning that a contraction (u, v) that happens before a contraction (u, w)
   *      must be uncontracted in a batch that is part of the same batch or a batch uncontracted after the
   *      batch which (u, w) is part of. This ensures that a parallel batch uncontraction does not
   *      increase the objective function.
   * We use the contraction tree to create a batch uncontraction order. Note, uncontractions from
   * different subtrees can be interleaved abitrary. To ensure condition 1.) we peform a BFS starting
   * from all roots of the contraction tree. Each BFS level induces a new batch. Since we contract
   * vertices in parallel its not possible to create a relative order of the contractions which is
   * neccassary for condition 2.). However, during a contraction we store a start and end "timepoint"
   * of a contraction. If two contractions time intervals do not intersect, we can determine
   * which contraction happens strictly before the other. If they intersect, it is not possible to
   * give a relative order. To ensure condition 2.) we sort the childs of a vertex in the contraction tree
   * after its time intervals. Once we add a uncontraction (u,v) to a batch, we also add all uncontractions
   * (u,w) to the batch which intersect the time interval of (u,v). To merge uncontractions of different
   * subtrees in a batch, we insert all eligble uncontractions into a max priority queue with the subtree
   * size of the contraction partner as key. We insert uncontractions into the current batch as long
   * as the maximum batch size is not reached or the PQ is empty. Once the batch reaches its maximum
   * batch size, we create a new empty batch. If the PQ is empty, we replace it with the PQ of the next
   * BFS level. With this approach heavy vertices are uncontracted earlier (subtree size in the PQ as key = weight of
   * a vertex for an unweighted hypergraph) such that average node weight of the hypergraph decreases faster and
   * local searches are more effective in early stages of the uncontraction hierarchy where hyperedge sizes are
   * usually smaller than on the original hypergraph.
   */
  BatchVector createBatchUncontractionHierarchyForVersion(BatchIndexAssigner& batch_assigner,
                                                          const size_t version);

  // ! Number of hypernodes
  HypernodeID _num_hypernodes;
  // ! Number of removed hypernodes
  HypernodeID _num_removed_hypernodes;
  // ! Maximum weight of all removed degree zero nodes
  HypernodeWeight _max_removed_degree_zero_hn_weight;
  // ! Number of hyperedges
  HyperedgeID _num_hyperedges;
  // ! Number of removed hyperedges
  HyperedgeID _num_removed_hyperedges;
  // ! Maximum size of a hyperedge
  HypernodeID _max_edge_size;
  // ! Number of pins
  HypernodeID _num_pins;
  // ! Total degree of all vertices
  HypernodeID _total_degree;
  // ! Total weight of hypergraph
  HypernodeWeight _total_weight;
  // ! Version of the hypergraph, each time we remove a single-pin and parallel nets,
  // ! we create a new version
  size_t _version;
  // ! Contraction Index, increment whenever a contraction terminates
  std::atomic<HypernodeID> _contraction_index;

  // ! Hypernodes
  Array<Hypernode> _hypernodes;
  // ! Contraction Tree
  ContractionTree _contraction_tree;
  // ! Pins of hyperedges
  IncidentNetArray _incident_nets;
  // ! Atomic bool vector used to acquire unique ownership of hypernodes
  OwnershipVector _acquired_hns;


  // ! Hyperedges
  Array<Hyperedge> _hyperedges;
  // ! Incident nets of hypernodes
  IncidenceArray _incidence_array;
  // ! Atomic bool vector used to acquire unique ownership of hyperedges
  OwnershipVector _acquired_hes;
  // ! During batch uncontraction we flag hyperedges already considered for resizing
  ThreadSafeFastResetFlagArray<> _hes_to_resize_flag_array;
  // ! Collects hyperedge contractions that failed due to failed acquired ownership
  ThreadLocalHyperedgeVector _failed_hyperedge_contractions;
  // ! Bitset to mark hyperedges, e.g. if want to flag shared incident nets of u and v
  // ! if we contract both.
  ThreadLocalBitset _he_bitset;
  // ! Single-pin and parallel nets are marked within that vector during the algorithm
  kahypar::ds::FastResetFlagArray<> _removable_single_pin_and_parallel_nets;

  // ! Fixed Vertex Support
  FixedVertexSupport<DynamicHypergraph> _fixed_vertices;
};

} // namespace ds
} // namespace mt_kahypar
