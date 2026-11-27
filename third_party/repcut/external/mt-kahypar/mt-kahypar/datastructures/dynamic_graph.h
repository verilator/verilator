/*******************************************************************************
 * MIT License
 *
 * This file is part of Mt-KaHyPar.
 *
 * Copyright (C) 2020 Lars Gottesbüren <lars.gottesbueren@kit.edu>
 * Copyright (C) 2020 Tobias Heuer <tobias.heuer@kit.edu>
 * Copyright (C) 2022 Nikolai Maas <nikolai.maas@student.kit.edu>
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
#include "mt-kahypar/datastructures/dynamic_adjacency_array.h"
#include "mt-kahypar/datastructures/contraction_tree.h"
#include "mt-kahypar/datastructures/thread_safe_fast_reset_flag_array.h"
#include "mt-kahypar/parallel/stl/scalable_vector.h"
#include "mt-kahypar/utils/memory_tree.h"
#include "mt-kahypar/utils/exception.h"

namespace mt_kahypar {
namespace ds {

// Forward
class DynamicGraphFactory;
template <typename Hypergraph>
class PartitionedGraph;

class DynamicGraph {

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
  using MarkEdgeFunc = std::function<bool (const HyperedgeID)>;
  #define NOOP_BATCH_FUNC [] (const HypernodeID, const HypernodeID, const HyperedgeID) { }

  // Represents a uncontraction that is assigned to a certain batch
  // and within that batch to a certain position.
  struct BatchAssignment {
    HypernodeID u;
    HypernodeID v;
    size_t batch_index;
    size_t batch_pos;
  };

 private:
  /**
   * Represents a hypernode of the hypergraph and contains all information
   * associated with a vertex.
   */
  class Node {
   public:
    using IDType = HypernodeID;

    Node() :
      _weight(1),
      _community_id(0),
      _batch_idx(std::numeric_limits<HypernodeID>::max()),
      _valid(false) { }

    Node(const bool valid) :
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

  /*!
   * Iterator for pins of an edge
   *
   * Note that because this is a graph, each edge has exactly two pins.
   */
  class PinIterator {
   public:
    using iterator_category = std::forward_iterator_tag;
    using value_type = HypernodeID;
    using reference = HypernodeID&;
    using pointer = const HypernodeID*;
    using difference_type = std::ptrdiff_t;

    /*!
     * Constructs a pin iterator based on the IDs of the two nodes
     */
    PinIterator(HypernodeID source, HypernodeID target, unsigned int iteration_count) :
      _source(source),
      _target(target),
      _iteration_count(iteration_count) {
      // ASSERT(target != kInvalidHypernode); -- doesn't hold for parallel contractions
    }

    // ! Returns the id of the element the iterator currently points to.
    HypernodeID operator* () const {
      ASSERT(_iteration_count < 2);
      return _iteration_count == 0 ? _source : _target;
    }

    // ! Prefix increment. The iterator advances to the next valid element.
    PinIterator & operator++ () {
      ASSERT(_iteration_count < 2);
      ++_iteration_count;
      if (_iteration_count == 1 && (_source == _target || _target == kInvalidHypernode)) {
        // the edge is a single pin edge
        ++_iteration_count;
      }
      return *this;
    }

    // ! Postfix increment. The iterator advances to the next valid element.
    PinIterator operator++ (int) {
      PinIterator copy = *this;
      operator++ ();
      return copy;
    }

    bool operator!= (const PinIterator& rhs) {
      return _iteration_count != rhs._iteration_count ||
             _source != rhs._source || _target != rhs._target;
    }

    bool operator== (const PinIterator& rhs) {
      return _iteration_count == rhs._iteration_count &&
              _source == rhs._source && _target == rhs._target;
    }

   private:
    // source node of the edge
    HypernodeID _source = 0;
    // target node of the edge
    HypernodeID _target = 0;
    // state of the iterator
    unsigned int _iteration_count = 0;
  };

  enum class ContractionResult : uint8_t {
    CONTRACTED = 0,
    PENDING_CONTRACTIONS = 1,
    WEIGHT_LIMIT_REACHED = 2,
    INVALID_FIXED_VERTEX_CONTRACTION = 3
  };

  using OwnershipVector = parallel::scalable_vector<parallel::IntegralAtomicWrapper<bool>>;
  using ThreadLocalHyperedgeVector = tbb::enumerable_thread_specific<parallel::scalable_vector<HyperedgeID>>;
  using Edge = DynamicAdjacencyArray::Edge;

 public:
  static constexpr bool is_graph = true;
  static constexpr bool is_static_hypergraph = false;
  static constexpr bool is_partitioned = false;
  static constexpr size_t SIZE_OF_HYPERNODE = sizeof(Node);
  static constexpr size_t SIZE_OF_HYPEREDGE = sizeof(Edge);
  static constexpr mt_kahypar_hypergraph_type_t TYPE = DYNAMIC_GRAPH;

  // ! Factory
  using Factory = DynamicGraphFactory;
  using Hyperedge = Edge;
  // ! Iterator to iterate over the hypernodes
  using HypernodeIterator = HypergraphElementIterator<const Node>;
  // ! Iterator to iterate over the hyperedges
  using HyperedgeIterator = EdgeIterator;
  // ! Iterator to iterate over the pins of a hyperedge
  using IncidenceIterator = PinIterator;
  // ! Iterator to iterate over the incident edges of a node
  using IncidentNetsIterator = DynamicAdjacencyArray::const_iterator;

  using ParallelHyperedge = DynamicAdjacencyArray::RemovedEdge;

  explicit DynamicGraph() :
    _num_removed_nodes(0),
    _max_removed_degree_zero_hn_weight(0),
    _num_edges(0),
    _total_weight(0),
    _version(0),
    _contraction_index(0),
    _nodes(),
    _contraction_tree(),
    _adjacency_array(),
    _acquired_nodes(),
    _fixed_vertices() { }

  DynamicGraph(const DynamicGraph&) = delete;
  DynamicGraph & operator= (const DynamicGraph &) = delete;

  DynamicGraph(DynamicGraph&& other) :
    _num_removed_nodes(other._num_removed_nodes),
    _max_removed_degree_zero_hn_weight(other._max_removed_degree_zero_hn_weight),
    _num_edges(other._num_edges),
    _total_weight(other._total_weight),
    _version(other._version),
    _contraction_index(0),
    _nodes(std::move(other._nodes)),
    _contraction_tree(std::move(other._contraction_tree)),
    _adjacency_array(std::move(other._adjacency_array)),
    _acquired_nodes(std::move(other._acquired_nodes)),
    _fixed_vertices(std::move(other._fixed_vertices)) {
    _fixed_vertices.setHypergraph(this);
  }

  DynamicGraph & operator= (DynamicGraph&& other) {
    _num_removed_nodes = other._num_removed_nodes;
    _max_removed_degree_zero_hn_weight = other._max_removed_degree_zero_hn_weight;
    _num_edges = other._num_edges;
    _total_weight = other._total_weight;
    _version = other._version;
    _contraction_index.store(other._contraction_index.load());
    _nodes = std::move(other._nodes);
    _contraction_tree = std::move(other._contraction_tree);
    _adjacency_array = std::move(other._adjacency_array);
    _acquired_nodes = std::move(other._acquired_nodes);
    _fixed_vertices = std::move(other._fixed_vertices);
    _fixed_vertices.setHypergraph(this);
    return *this;
  }

  ~DynamicGraph() {
    freeInternalData();
  }

  // ####################### General Hypergraph Stats #######################

  // ! Initial number of hypernodes
  HypernodeID initialNumNodes() const {
    return numNodes();
  }

  // ! Number of removed hypernodes
  HypernodeID numRemovedHypernodes() const {
    return _num_removed_nodes;
  }

  // ! Max weight of removed degree zero vertex
  HypernodeWeight maxWeightOfRemovedDegreeZeroNode() const {
    return _max_removed_degree_zero_hn_weight;
  }

  // ! Initial number of hyperedges
  HyperedgeID initialNumEdges() const {
    return _num_edges;
  }

  // ! Number of removed hyperedges
  HyperedgeID numRemovedHyperedges() const {
    return 0;
  }

  // ! Set the number of removed hyperedges
  void setNumRemovedHyperedges(const HyperedgeID num_removed_hyperedges) {
    ASSERT(num_removed_hyperedges == 0);
    unused(num_removed_hyperedges);
  }

  // ! Initial number of pins
  HypernodeID initialNumPins() const {
    return _num_edges;
  }

  // ! Initial sum of the degree of all vertices
  HypernodeID initialTotalVertexDegree() const {
    return _num_edges;
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
  void doParallelForAllNodes(const F& f) const {
    tbb::parallel_for(ID(0), numNodes(), [&](const HypernodeID& hn) {
      if ( nodeIsEnabled(hn) ) {
        f(hn);
      }
    });
  }

  // ! Iterates in parallel over all active edges and calls function f
  // ! for each net
  template<typename F>
  void doParallelForAllEdges(const F& f) const {
    _adjacency_array.doParallelForAllEdges(f);
  }

  // ! Returns a range of the active nodes of the hypergraph
  IteratorRange<HypernodeIterator> nodes() const {
    return IteratorRange<HypernodeIterator>(
      HypernodeIterator(_nodes.data(), ID(0), numNodes()),
      HypernodeIterator(_nodes.data() + numNodes(), numNodes(), numNodes()));
  }

  // ! Returns a range of the active edges of the hypergraph
  IteratorRange<HyperedgeIterator> edges() const {
    return _adjacency_array.edges();
  }

  // ! Returns a range to loop over the incident edges of node u.
  IteratorRange<IncidentNetsIterator> incidentEdges(const HypernodeID u) const {
    ASSERT(u < numNodes(), "Hypernode" << u << "does not exist");
    return _adjacency_array.incidentEdges(u);
  }

  // ! Returns a range to loop over the pins of hyperedge e.
  IteratorRange<IncidenceIterator> pins(const HyperedgeID id) const {
    const Edge& e = edge(id);
    const HypernodeID source = e.source;
    const HypernodeID target = e.target;
    return IteratorRange<IncidenceIterator>(
      IncidenceIterator(source, target, 0),
      IncidenceIterator(source, target, 2));
  }

  // ####################### Hypernode Information #######################

  // ! Weight of a vertex
  HypernodeWeight nodeWeight(const HypernodeID u) const {
    ASSERT(u < numNodes(), "Hypernode" << u << "does not exist");
    return hypernode(u).weight();
  }

  // ! Sets the weight of a vertex
  void setNodeWeight(const HypernodeID u, const HypernodeWeight weight) {
    ASSERT(!hypernode(u).isDisabled(), "Hypernode" << u << "is disabled");
    return hypernode(u).setWeight(weight);
  }

  // ! Degree of a hypernode
  HyperedgeID nodeDegree(const HypernodeID u) const {
    ASSERT(u < numNodes(), "Hypernode" << u << "does not exist");
    return _adjacency_array.nodeDegree(u);
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
    ++_num_removed_nodes;
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

  // ! Accessor for hyperedge-related information
  MT_KAHYPAR_ATTRIBUTE_ALWAYS_INLINE const Edge& edge(const HyperedgeID e) const {
    const Edge& he = _adjacency_array.edge(e);
    // ASSERT(he.isValid()); -- doesn't hold for parallel contractions
    return he;
  }

  // ! To avoid code duplication we implement non-const version in terms of const version
  MT_KAHYPAR_ATTRIBUTE_ALWAYS_INLINE Hyperedge& edge(const HyperedgeID e) {
    Hyperedge& he = _adjacency_array.edge(e);
    // ASSERT(he.isValid()); -- doesn't hold for parallel contractions
    return he;
  }

  // ! Weight of an edge
  HyperedgeWeight edgeWeight(const HyperedgeID e) const {
    return edge(e).weight;
  }

  // ! Unique id of a hyperedge
  HyperedgeID uniqueEdgeID(const HyperedgeID e) const {
    return _adjacency_array.uniqueEdgeID(e);
  }

  // ! Range of unique id edge ids
  HyperedgeID maxUniqueID() const {
    return initialNumEdges();
  }

  // ! Sets the weight of a hyperedge
  void setEdgeWeight(const HyperedgeID e, const HyperedgeWeight weight) {
    edge(e).weight = weight;
  }

  // ! Number of pins of a hyperedge
  HypernodeID edgeSize(const HyperedgeID e) const {
    return isSinglePin(e) ? 1 : 2;
  }

  // ! Maximum size of a hyperedge
  HypernodeID maxEdgeSize() const {
    return 2;
  }

  // ! Returns, whether a hyperedge is enabled or not
  bool edgeIsEnabled(const HyperedgeID) const {
    return true;
  }

  // ! Enables a hyperedge (must be disabled before)
  void enableHyperedge(const HyperedgeID) {
    throw UnsupportedOperationException(
      "enableHyperedge() is not supported in dynamic graph");
  }

  HyperedgeID edgeSource(const HyperedgeID e) const {
    return edge(e).source;
  }

  HyperedgeID edgeTarget(const HyperedgeID e) const {
    return edge(e).target;
  }

  bool isSinglePin(const HyperedgeID e) const {
    return edgeSource(e) == edgeTarget(e);
  }

  // ####################### Community Information #######################

  // ! Community id which hypernode u is assigned to
  PartitionID communityID(const HypernodeID u) const {
    ASSERT(u < numNodes(), "Hypernode" << u << "does not exist");
    return hypernode(u).communityID();
  }

  // ! Assign a community to a hypernode
  // ! Note, in order to use all community-related functions, initializeCommunities()
  // ! have to be called after assigning to each vertex a community id
  void setCommunityID(const HypernodeID u, const PartitionID community_id) {
    ASSERT(!hypernode(u).isDisabled(), "Hypernode" << u << "is disabled");
    return hypernode(u).setCommunityID(community_id);
  }

  // ! Reset internal community information
  void setCommunityIDs(const parallel::scalable_vector<PartitionID>& community_ids) {
    ASSERT(community_ids.size() == UI64(numNodes()));
    doParallelForAllNodes([&](const HypernodeID& hn) {
      hypernode(hn).setCommunityID(community_ids[hn]);
    });
  }

  // ####################### Fixed Vertex Support #######################

  void addFixedVertexSupport(FixedVertexSupport<DynamicGraph>&& fixed_vertices) {
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

  const FixedVertexSupport<DynamicGraph>& fixedVertexSupport() const {
    return _fixed_vertices;
  }

  FixedVertexSupport<DynamicGraph> copyOfFixedVertexSupport() const {
    return _fixed_vertices.copy();
  }

  // ####################### Contract / Uncontract #######################

  DynamicGraph contract(parallel::scalable_vector<HypernodeID>&, bool deterministic = false) {
    unused(deterministic);
    throw UnsupportedOperationException(
      "contract(c, id) is not supported in dynamic graph");
    return DynamicGraph();
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
   * The two uncontraction functions are required by the partitioned graph to update
   * gain cache values.
   */
  void uncontract(const Batch& batch,
                  const MarkEdgeFunc& mark_edge,
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
  VersionedBatchVector createBatchUncontractionHierarchy(const size_t batch_size);

  // ! Only for testing
  VersionedBatchVector createBatchUncontractionHierarchy(ContractionTree&& tree,
                                                         const size_t batch_size,
                                                         const size_t num_versions = 1) {
    ASSERT(num_versions > 0);
    _version = num_versions - 1;
    _contraction_tree = std::move(tree);
    return createBatchUncontractionHierarchy(batch_size);
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

  // ! Only for testing
  void sortIncidentEdges() {
    _adjacency_array.sortIncidentEdges();
  }

  // ####################### Remove / Restore Hyperedges #######################

  /*!
  * (Not supported.)
  */
  void removeEdge(const HyperedgeID) {
    throw UnsupportedOperationException(
      "removeEdge is not supported in dynamic graph");
  }

  /*!
  * (Not supported.)
  */
  void restoreEdge(const HyperedgeID) {
    throw UnsupportedOperationException(
      "restoreEdge is not supported in dynamic graph");
  }

  /*!
  * (Not supported.)
  */
  void removeLargeEdge(const HyperedgeID) {
    throw UnsupportedOperationException(
      "removeLargeEdge is not supported in dynamic graph");
  }

  /*!
   * (Not supported.)
   */
  void restoreLargeEdge(const HyperedgeID&) {
    throw UnsupportedOperationException(
      "restoreLargeEdge is not supported in dynamic graph");
  }

  /**
   * Removes parallel edges from the graph. Returns a vector with the headers and number
   * removed edges per header.
   */
  parallel::scalable_vector<ParallelHyperedge> removeSinglePinAndParallelHyperedges();

  /**
   * Restores a previously removed set of singple-pin and parallel hyperedges. Note, that hes_to_restore
   * must be exactly the same and given in the reverse order as returned by removeSinglePinAndParallelNets(...).
   */
  void restoreSinglePinAndParallelNets(const parallel::scalable_vector<ParallelHyperedge>& hes_to_restore);

  // ####################### Copy #######################

  // ! Copy dynamic hypergraph in parallel
  DynamicGraph copy(parallel_tag_t) const;

  // ! Copy dynamic hypergraph sequential
  DynamicGraph copy() const;

  // ! Reset internal data structure
  void reset() {
    _contraction_tree.reset();
    _adjacency_array.reset();
    _version = 0;
  }

  // ! Free internal data in parallel
  void freeInternalData() {
    _num_edges = 0;
  }

  void freeTmpContractionBuffer() {
    throw UnsupportedOperationException(
      "freeTmpContractionBuffer() is not supported in dynamic hypergraph");
  }

  void memoryConsumption(utils::MemoryTreeNode* parent) const;

  // ! Only for testing
  bool verifyIncidenceArrayAndIncidentNets();

 private:
  friend class DynamicGraphFactory;
  template<typename Hypergraph>
  friend class CommunitySupport;
  template <typename Hypergraph>
  friend class PartitionedGraph;

  // ####################### Acquiring / Releasing Ownership #######################

  MT_KAHYPAR_ATTRIBUTE_ALWAYS_INLINE HypernodeID numNodes() const {
    return _adjacency_array.numNodes();
  }

  MT_KAHYPAR_ATTRIBUTE_ALWAYS_INLINE void acquireHypernode(const HypernodeID u) {
    ASSERT(u < numNodes(), "Hypernode" << u << "does not exist");
    bool expected = false;
    bool desired = true;
    while ( !_acquired_nodes[u].compare_exchange_strong(expected, desired) ) {
      expected = false;
    }
  }

  MT_KAHYPAR_ATTRIBUTE_ALWAYS_INLINE bool tryAcquireHypernode(const HypernodeID u) {
    ASSERT(u < numNodes(), "Hypernode" << u << "does not exist");
    bool expected = false;
    bool desired = true;
    return _acquired_nodes[u].compare_exchange_strong(expected, desired);
  }

  MT_KAHYPAR_ATTRIBUTE_ALWAYS_INLINE void releaseHypernode(const HypernodeID u) {
    ASSERT(u < numNodes(), "Hypernode" << u << "does not exist");
    ASSERT(_acquired_nodes[u], "Hypernode" << u << "is not acquired!");
    _acquired_nodes[u] = false;
  }

  // ####################### Iterators #######################

  MT_KAHYPAR_ATTRIBUTE_ALWAYS_INLINE
  IteratorRange<IncidentNetsIterator> incident_nets_of(const HypernodeID u,
                                                       const size_t pos = 0) const {
    ASSERT(u < numNodes(), "Hypernode" << u << "does not exist");
    return _adjacency_array.incidentEdges(u, pos);
  }

  // ####################### Hypernode Information #######################

  // ! Accessor for hypernode-related information
  MT_KAHYPAR_ATTRIBUTE_ALWAYS_INLINE const Node& hypernode(const HypernodeID u) const {
    ASSERT(u <= numNodes(), "Hypernode" << u << "does not exist");
    return _nodes[u];
  }

  // ! To avoid code duplication we implement non-const version in terms of const version
  MT_KAHYPAR_ATTRIBUTE_ALWAYS_INLINE Node& hypernode(const HypernodeID u) {
    return const_cast<Node&>(static_cast<const DynamicGraph&>(*this).hypernode(u));
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

  // ! Number of removed hypernodes
  HypernodeID _num_removed_nodes;
  // ! Maximum weight of all removed degree zero nodes
  HypernodeWeight _max_removed_degree_zero_hn_weight;
  // ! Number of hyperedges
  HyperedgeID _num_edges;
  // ! Total weight of hypergraph
  HypernodeWeight _total_weight;
  // ! Version of the hypergraph, each time we remove a single-pin and parallel nets,
  // ! we create a new version
  size_t _version;
  // ! Contraction Index, increment whenever a contraction terminates
  std::atomic<HypernodeID> _contraction_index;

  // ! Hypernodes
  Array<Node> _nodes;
  // ! Contraction Tree
  ContractionTree _contraction_tree;
  // ! Pins of hyperedges
  DynamicAdjacencyArray _adjacency_array;
  // ! Atomic bool vector used to acquire unique ownership of hypernodes
  OwnershipVector _acquired_nodes;

  // ! Fixed Vertex Support
  FixedVertexSupport<DynamicGraph> _fixed_vertices;
};

} // namespace ds
} // namespace mt_kahypar
