/*******************************************************************************
 * MIT License
 *
 * This file is part of Mt-KaHyPar.
 *
 * Copyright (C) 2019 Lars Gottesbüren <lars.gottesbueren@kit.edu>
 * Copyright (C) 2019 Tobias Heuer <tobias.heuer@kit.edu>
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

#include <functional>

#include <tbb/parallel_for.h>

#include "include/mtkahypartypes.h"

#include "mt-kahypar/macros.h"
#include "mt-kahypar/datastructures/array.h"
#include "mt-kahypar/datastructures/hypergraph_common.h"
#include "mt-kahypar/datastructures/fixed_vertex_support.h"
#include "mt-kahypar/parallel/atomic_wrapper.h"
#include "mt-kahypar/parallel/stl/scalable_vector.h"
#include "mt-kahypar/partition/context_enum_classes.h"
#include "mt-kahypar/utils/memory_tree.h"
#include "mt-kahypar/utils/range.h"
#include "mt-kahypar/utils/exception.h"

namespace mt_kahypar {
namespace ds {

// Forward
class StaticGraphFactory;
template <typename Hypergraph>
class PartitionedGraph;

class StaticGraph {

  static constexpr bool enable_heavy_assert = false;

  // During contractions we temporary memcpy all incident nets of a collapsed
  // vertex to consecutive range in a temporary incident nets structure.
  // Afterwards, we sort that range and remove duplicates. However, it turned
  // out that this become a major sequential bottleneck in presence of high
  // degree vertices. Therefore, all vertices with temporary degree greater
  // than this threshold are contracted with a special procedure.
  static constexpr HyperedgeID HIGH_DEGREE_CONTRACTION_THRESHOLD = ID(350000);

  static_assert(std::is_unsigned<HypernodeID>::value, "Node ID must be unsigned");
  static_assert(std::is_unsigned<HyperedgeID>::value, "Hyperedge ID must be unsigned");

  using UncontractionFunction = std::function<void (const HypernodeID, const HypernodeID, const HyperedgeID)>;
  using MarkEdgeFunc = std::function<bool (const HyperedgeID)>;
  #define NOOP_BATCH_FUNC [] (const HypernodeID, const HypernodeID, const HyperedgeID) { }

  /**
   * Represents a hypernode of the hypergraph and contains all information
   * associated with a vertex.
   */
  class Node {
   public:
    using IDType = HypernodeID;

    Node() :
      _begin(0),
      _weight(1),
      _valid(false) { }

    explicit Node(const bool valid) :
      _begin(0),
      _weight(1),
      _valid(valid) { }

    // Sentinel Constructor
    explicit Node(const size_t begin) :
      _begin(begin),
      _weight(1),
      _valid(false) { }

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

    // ! Returns the index of the first element in _incident_nets
    HyperedgeID firstEntry() const {
      return _begin;
    }

    // ! Sets the index of the first element in _incident_nets to begin
    void setFirstEntry(size_t begin) {
      ASSERT(!isDisabled());
      _begin = begin;
    }

    HypernodeWeight weight() const {
      return _weight;
    }

    void setWeight(HypernodeWeight weight) {
      ASSERT(!isDisabled());
      _weight = weight;
    }

   private:
    // ! Index of the first element in _edges
    HyperedgeID _begin;
    // ! Node weight
    HypernodeWeight _weight;
    // ! Flag indicating whether or not the element is active.
    bool _valid;
  };

  /**
   * Represents a hyperedge of the hypergraph and contains all information
   * associated with a net (except connectivity information).
   */
  class Edge {
   public:
    using IDType = HyperedgeID;

    Edge() :
      _target(0),
      _source(0),
      _weight(1) { }

    explicit Edge(HypernodeID target, HypernodeID source) :
      _target(target),
      _source(source),
      _weight(1) { }

    // ! Returns the index of the target node
    HypernodeID target() const {
      return _target;
    }

    // ! Sets the index of the target node
    void setTarget(HypernodeID target) {
      _target = target;
    }

    // ! Returns the index of the source node
    HypernodeID source() const {
      return _source;
    }

    // ! Sets the index of the source node
    void setSource(HypernodeID source) {
      _source = source;
    }

    HyperedgeWeight weight() const {
      return _weight;
    }

    void setWeight(HyperedgeWeight weight) {
      _weight = weight;
    }

    bool operator== (const Edge& rhs) const {
      return _target == rhs._target && _source == rhs._source && _weight == rhs._weight;
    }

    bool operator!= (const Edge& rhs) const {
      return _target != rhs._target || _source != rhs._source || _weight != rhs._weight;
    }

   private:
    // ! Index of target node
    HypernodeID _target;
    // ! Index of source node
    HypernodeID _source;
    // ! hyperedge weight
    HyperedgeWeight _weight;
  };

  /*!
   * Iterator for nodes
   *
   * The iterator is used in for-each loops over all nodes.
   * In order to support iteration over coarsened hypergraphs, this iterator
   * skips over nodes marked as invalid.
   * Iterating over the set of vertices \f$V\f$ therefore is linear in the
   * size \f$|V|\f$ of the original hypergraph - even if it has been coarsened
   * to much smaller size.
   *
   * In order to be as generic as possible, the iterator does not expose the
   * internal representation. Instead only handles to the respective elements
   * are returned, i.e. the IDs of the corresponding hypernodes/hyperedges.
   */
  class NodeIterator {
   public:
    using iterator_category = std::forward_iterator_tag;
    using value_type = HypernodeID;
    using reference = HypernodeID&;
    using pointer = const HypernodeID*;
    using difference_type = std::ptrdiff_t;

    /*!
     * If start_element is invalid, the iterator advances to the first valid
     * element.
     *
     * \param start_element A pointer to the starting position
     * \param id The index of the element the pointer points to
     * \param max_id The maximum index allowed
     */
    NodeIterator(const Node* start_element, HypernodeID id, HypernodeID max_id) :
      _id(id),
      _max_id(max_id),
      _node(start_element) {
      if (_id != _max_id && _node->isDisabled()) {
        operator++ ();
      }
    }

    // ! Returns the id of the element the iterator currently points to.
    HypernodeID operator* () const {
      return _id;
    }

    // ! Prefix increment. The iterator advances to the next valid element.
    NodeIterator & operator++ () {
      ASSERT(_id < _max_id);
      do {
        ++_id;
        ++_node;
      } while (_id < _max_id && _node->isDisabled());
      return *this;
    }

    // ! Postfix increment. The iterator advances to the next valid element.
    NodeIterator operator++ (int) {
      NodeIterator copy = *this;
      operator++ ();
      return copy;
    }

    bool operator!= (const NodeIterator& rhs) {
      return _id != rhs._id;
    }

    bool operator== (const NodeIterator& rhs) {
      return _id == rhs._id;
    }

   private:
    // Handle to the node the iterator currently points to
    HypernodeID _id = 0;
    // Maximum allowed index
    HypernodeID _max_id = 0;
    // node the iterator currently points to
    const Node* _node = nullptr;
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

  static_assert(std::is_trivially_copyable<Node>::value, "Node is not trivially copyable");
  static_assert(std::is_trivially_copyable<Edge>::value, "Hyperedge is not trivially copyable");

 private:
  struct TmpEdgeInformation {
    // ! invalid edge
    TmpEdgeInformation() :
      _target(kInvalidHyperedge),
      _valid_or_weight(0),
      _id(kInvalidHyperedge) {
    }

    // ! valid edge
    TmpEdgeInformation(HyperedgeID target, HyperedgeWeight weight, HyperedgeID id) :
      _target(target),
      _valid_or_weight(weight),
      _id(id) {
      ASSERT(isValid());
    }

    bool isValid() const {
      return _valid_or_weight != 0;
    }

    HyperedgeID getTarget() const {
      ASSERT(isValid());
      return _target;
    }

    HyperedgeWeight getWeight() const {
      ASSERT(isValid());
      return _valid_or_weight;
    }

    HyperedgeID getID() const {
      ASSERT(isValid());
      return _id;
    }

    void invalidate() {
      _valid_or_weight = 0;
    }

    void addWeight(HyperedgeWeight weight) {
      ASSERT(isValid());
      _valid_or_weight += weight;
    }

    void updateID(HyperedgeID id) {
      ASSERT(isValid());
      _id = std::min(_id, id);
    }

    HyperedgeID _target;
    HyperedgeWeight _valid_or_weight;
    HyperedgeID _id;
  };

  // ! Contains buffers that are needed during multilevel contractions.
  // ! Struct is allocated on top level hypergraph and passed to each contracted
  // ! hypergraph such that memory can be reused in consecutive contractions.
  struct TmpContractionBuffer {
    explicit TmpContractionBuffer(const HypernodeID num_nodes,
                                  const HyperedgeID num_edges) {
      tbb::parallel_invoke([&] {
        mapping.resize("Coarsening", "mapping", num_nodes);
      }, [&] {
        tmp_nodes.resize("Coarsening", "tmp_nodes", num_nodes);
      }, [&] {
        node_sizes.resize("Coarsening", "node_sizes", num_nodes);
      }, [&] {
        tmp_num_incident_edges.resize("Coarsening", "tmp_num_incident_edges", num_nodes);
      }, [&] {
        node_weights.resize("Coarsening", "node_weights", num_nodes);
      }, [&] {
        tmp_edges.resize("Coarsening", "tmp_edges", num_edges);
      }, [&] {
        edge_id_mapping.resize("Coarsening", "edge_id_mapping", num_edges / 2);
      });
    }

    Array<HypernodeID> mapping;
    Array<Node> tmp_nodes;
    Array<HyperedgeID> node_sizes;
    Array<parallel::IntegralAtomicWrapper<HyperedgeID>> tmp_num_incident_edges;
    Array<parallel::IntegralAtomicWrapper<HypernodeWeight>> node_weights;
    Array<TmpEdgeInformation> tmp_edges;
    Array<HyperedgeID> edge_id_mapping;
  };

 public:
  static constexpr bool is_graph = true;
  static constexpr bool is_static_hypergraph = true;
  static constexpr bool is_partitioned = false;
  static constexpr size_t SIZE_OF_HYPERNODE = sizeof(Node);
  static constexpr size_t SIZE_OF_HYPEREDGE = sizeof(TmpEdgeInformation);
  static constexpr mt_kahypar_hypergraph_type_t TYPE = STATIC_GRAPH;

  // ! Factory
  using Factory = StaticGraphFactory;
  // ! Iterator to iterate over the hypernodes
  using HypernodeIterator = NodeIterator;
  // ! Iterator to iterate over the hyperedges
  using HyperedgeIterator = IntegerIterator<HyperedgeID>;
  // ! Iterator to iterate over the pins of a hyperedge
  using IncidenceIterator = PinIterator;
  // ! Iterator to iterate over the incident nets of a hypernode
  using IncidentNetsIterator = IntegerIterator<HyperedgeID>;

  // ! static graph does not support explicit parallel edge detection
  struct ParallelHyperedge {
    HyperedgeID edge_id;
    HyperedgeID old_id;
  };

  explicit StaticGraph() :
    _num_nodes(0),
    _num_removed_nodes(0),
    _max_removed_degree_zero_hn_weight(0),
    _num_edges(0),
    _total_weight(0),
    _nodes(),
    _edges(),
    _unique_edge_ids(),
    _community_ids(),
    _fixed_vertices(),
    _tmp_contraction_buffer(nullptr) { }

  StaticGraph(const StaticGraph&) = delete;
  StaticGraph & operator= (const StaticGraph &) = delete;

  StaticGraph(StaticGraph&& other) :
    _num_nodes(other._num_nodes),
    _num_removed_nodes(other._num_removed_nodes),
    _max_removed_degree_zero_hn_weight(other._max_removed_degree_zero_hn_weight),
    _num_edges(other._num_edges),
    _total_weight(other._total_weight),
    _nodes(std::move(other._nodes)),
    _edges(std::move(other._edges)),
    _unique_edge_ids(std::move(other._unique_edge_ids)),
    _community_ids(std::move(other._community_ids)),
    _fixed_vertices(std::move(other._fixed_vertices)),
    _tmp_contraction_buffer(std::move(other._tmp_contraction_buffer)) {
    _fixed_vertices.setHypergraph(this);
    other._tmp_contraction_buffer = nullptr;
  }

  StaticGraph & operator= (StaticGraph&& other) {
    _num_nodes = other._num_nodes;
    _num_removed_nodes = other._num_removed_nodes;
    _max_removed_degree_zero_hn_weight = other._max_removed_degree_zero_hn_weight;
    _num_edges = other._num_edges;
    _total_weight = other._total_weight;
    _nodes = std::move(other._nodes);
    _edges = std::move(other._edges);
    _unique_edge_ids = std::move(other._unique_edge_ids);
    _community_ids = std::move(other._community_ids),
    _fixed_vertices = std::move(other._fixed_vertices);
    _fixed_vertices.setHypergraph(this);
    _tmp_contraction_buffer = std::move(other._tmp_contraction_buffer);
    other._tmp_contraction_buffer = nullptr;
    return *this;
  }

  ~StaticGraph() {
    if ( _tmp_contraction_buffer ) {
      delete(_tmp_contraction_buffer);
      _tmp_contraction_buffer = nullptr;
    }
    freeInternalData();
  }

  // ####################### General Hypergraph Stats #######################

  // ! Initial number of hypernodes
  HypernodeID initialNumNodes() const {
    return _num_nodes;
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
    tbb::parallel_for(ID(0), _num_nodes, [&](const HypernodeID& hn) {
      if ( nodeIsEnabled(hn) ) {
        f(hn);
      }
    });
  }

  // ! Iterates in parallel over all active edges and calls function f
  // ! for each net
  template<typename F>
  void doParallelForAllEdges(const F& f) const {
    tbb::parallel_for(ID(0), _num_edges, [&](const HyperedgeID& e) {
      f(e);
    });
  }

  // ! Returns a range of the active nodes of the hypergraph
  IteratorRange<HypernodeIterator> nodes() const {
    return IteratorRange<HypernodeIterator>(
      HypernodeIterator(_nodes.data(), ID(0), _num_nodes),
      HypernodeIterator(_nodes.data() + _num_nodes, _num_nodes, _num_nodes));
  }

  // ! Returns a range of the active edges of the hypergraph
  IteratorRange<HyperedgeIterator> edges() const {
    return integer_range(_num_edges);
  }

  // ! Returns a range to loop over the incident nets of hypernode u.
  IteratorRange<IncidentNetsIterator> incidentEdges(const HypernodeID u) const {
    return incident_nets_of(u, 0);
  }

  // ! Returns a range to loop over the pins of hyperedge e.
  IteratorRange<IncidenceIterator> pins(const HyperedgeID id) const {
    const Edge& e = edge(id);
    const HypernodeID source = e.source();
    const HypernodeID target = e.target();
    return IteratorRange<IncidenceIterator>(
      IncidenceIterator(source, target, 0),
      IncidenceIterator(source, target, 2));
  }

    // ####################### Node Information #######################

  // ! Weight of a vertex
  HypernodeWeight nodeWeight(const HypernodeID u) const {
    return node(u).weight();
  }

  // ! Sets the weight of a vertex
  void setNodeWeight(const HypernodeID u, const HypernodeWeight weight) {
    return node(u).setWeight(weight);
  }

  // ! Degree of a hypernode
  HyperedgeID nodeDegree(const HypernodeID u) const {
    return node(u + 1).firstEntry() - node(u).firstEntry();
  }

  // ! Returns whether a hypernode is enabled or not
  bool nodeIsEnabled(const HypernodeID u) const {
    return !node(u).isDisabled();
  }

  // ! Removes a degree zero hypernode
  void removeDegreeZeroHypernode(const HypernodeID u) {
    ASSERT(nodeDegree(u) == 0);
    node(u).disable();
    ++_num_removed_nodes;
    _max_removed_degree_zero_hn_weight =
      std::max(_max_removed_degree_zero_hn_weight, nodeWeight(u));
  }

  // ! Restores a degree zero hypernode
  void restoreDegreeZeroHypernode(const HypernodeID u) {
    node(u).enable();
    ASSERT(nodeDegree(u) == 0);
    _max_removed_degree_zero_hn_weight = 0;
  }

  // ####################### Hyperedge Information #######################

  // ! Target of an edge
  HypernodeID edgeTarget(const HyperedgeID e) const {
    return edge(e).target();
  }

  // ! Source of an edge
  HypernodeID edgeSource(const HyperedgeID e) const {
    return edge(e).source();
  }

  bool isSinglePin(const HyperedgeID) const {
    return false;
  }

  // ! Weight of a hyperedge
  HyperedgeWeight edgeWeight(const HyperedgeID e) const {
    return edge(e).weight();
  }

  // ! Unique id of a hyperedge, in the range of [0, initialNumEdges() / 2)
  HyperedgeID uniqueEdgeID(const HyperedgeID e) const {
    ASSERT(e <= _edges.size(), "Hyperedge" << e << "does not exist");
    const HyperedgeID id = _unique_edge_ids[e];
    ASSERT(id < initialNumEdges() / 2);
    return id;
  }

  // ! Range of unique id edge ids
  HyperedgeID maxUniqueID() const {
    return initialNumEdges() / 2;
  }

  // ! Sets the weight of a hyperedge
  void setEdgeWeight(const HyperedgeID e, const HyperedgeWeight weight) {
    return edge(e).setWeight(weight);
  }

  // ! Number of pins of a hyperedge
  HypernodeID edgeSize(const HyperedgeID e) const {
    ASSERT(e <= _edges.size(), "Hyperedge" << e << "does not exist");
    unused(e);
    return 2;
  }

  // ! Maximum size of a hyperedge
  HypernodeID maxEdgeSize() const {
    return 2;
  }

  // ! Returns whether a hyperedge is enabled or not
  bool edgeIsEnabled(const HyperedgeID) const {
    return true;
  }

  // ! Enables a hyperedge (must be disabled before)
  void enableHyperedge(const HyperedgeID) {
    throw UnsupportedOperationException(
      "enableHyperedge() is not supported in static graph");
  }

  // ! Community id which hypernode u is assigned to
  PartitionID communityID(const HypernodeID u) const {
    return _community_ids[u];
  }

  // ! Assign a community to a hypernode
  void setCommunityID(const HypernodeID u, const PartitionID community_id) {
    _community_ids[u] = community_id;
  }

  // ####################### Fixed Vertex Support #######################

  void addFixedVertexSupport(FixedVertexSupport<StaticGraph>&& fixed_vertices) {
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

  const FixedVertexSupport<StaticGraph>& fixedVertexSupport() const {
    return _fixed_vertices;
  }

  FixedVertexSupport<StaticGraph> copyOfFixedVertexSupport() const {
    return _fixed_vertices.copy();
  }

  // ####################### Contract / Uncontract #######################

  /*!
   * Contracts a given community structure. All vertices with the same label
   * are collapsed into the same vertex. The resulting single-pin and parallel
   * hyperedges are removed from the contracted graph. The function returns
   * the contracted hypergraph and a mapping which specifies a mapping from
   * community label (given in 'communities') to a vertex in the coarse hypergraph.
   *
   * \param communities Community structure that should be contracted
   */
  StaticGraph contract(parallel::scalable_vector<HypernodeID>& communities, bool deterministic = false);

  bool registerContraction(const HypernodeID, const HypernodeID) {
    throw UnsupportedOperationException(
      "registerContraction(u, v) is not supported in static graph");
    return false;
  }

  size_t contract(const HypernodeID,
                  const HypernodeWeight max_node_weight = std::numeric_limits<HypernodeWeight>::max()) {
    unused(max_node_weight);
    throw UnsupportedOperationException(
      "contract(v, max_node_weight) is not supported in static graph");
    return 0;
  }

  void uncontract(const Batch&,
                  const MarkEdgeFunc& mark_edge,
                  const UncontractionFunction& case_one_func = NOOP_BATCH_FUNC,
                  const UncontractionFunction& case_two_func = NOOP_BATCH_FUNC) {
    unused(mark_edge);
    unused(case_one_func);
    unused(case_two_func);
    throw UnsupportedOperationException(
      "uncontract(batch) is not supported in static graph");
  }

  VersionedBatchVector createBatchUncontractionHierarchy(const size_t) {
    throw UnsupportedOperationException(
      "createBatchUncontractionHierarchy(batch_size) is not supported in static graph");
    return { };
  }

  // ####################### Remove / Restore Hyperedges #######################

  /*!
  * (Not supported.)
  */
  void removeEdge(const HyperedgeID) {
    throw UnsupportedOperationException(
      "removeEdge is not supported in static graph");
  }

  /*!
  * (Not supported.)
  */
  void restoreEdge(const HyperedgeID) {
    throw UnsupportedOperationException(
      "restoreEdge is not supported in static graph");
  }

  /*!
  * (Not supported.)
  */
  void removeLargeEdge(const HyperedgeID) {
    throw UnsupportedOperationException(
      "removeLargeEdge() is not supported in static graph");
  }

  /*!
  * (Not supported.)
  */
  void restoreLargeEdge(const HyperedgeID&) {
    throw UnsupportedOperationException(
      "restoreLargeEdge() is not supported in static graph");
  }

  parallel::scalable_vector<ParallelHyperedge> removeSinglePinAndParallelHyperedges() {
    throw UnsupportedOperationException(
      "removeSinglePinAndParallelHyperedges() is not supported in static graph");
    return { };
  }

  void restoreSinglePinAndParallelNets(const parallel::scalable_vector<ParallelHyperedge>&) {
    throw UnsupportedOperationException(
      "restoreSinglePinAndParallelNets(hes_to_restore) is not supported in static graph");
  }

  // ####################### Initialization / Reset Functions #######################

  // ! Reset internal community information
  void copyCommunityIDs(const parallel::scalable_vector<PartitionID>& community_ids) {
    ASSERT(community_ids.size() == UI64(_num_nodes));
    doParallelForAllNodes([&](const HypernodeID& hn) {
      _community_ids[hn] = community_ids[hn];
    });
  }

  void setCommunityIDs(ds::Clustering&& communities) {
    ASSERT(communities.size() == initialNumNodes());
    _community_ids = std::move(communities);
  }

  // ! Copy static hypergraph in parallel
  StaticGraph copy(parallel_tag_t) const;

  // ! Copy static hypergraph sequential
  StaticGraph copy() const;

  // ! Reset internal data structure
  void reset() { }

  // ! Free internal data in parallel
  void freeInternalData() {
    if ( _num_nodes > 0 || _num_edges > 0 ) {
      freeTmpContractionBuffer();
    }
    _num_nodes = 0;
    _num_edges = 0;
  }

  void freeTmpContractionBuffer() {
    if ( _tmp_contraction_buffer ) {
      delete(_tmp_contraction_buffer);
      _tmp_contraction_buffer = nullptr;
    }
  }

  void memoryConsumption(utils::MemoryTreeNode* parent) const;

    // ! Only for testing
  bool verifyIncidenceArrayAndIncidentNets() {
    throw UnsupportedOperationException(
      "verifyIncidenceArrayAndIncidentNets() not supported in static graph");
    return false;
  }

 private:
  friend class StaticGraphFactory;
  template<typename Hypergraph>
  friend class CommunitySupport;
  template <typename Hypergraph>
  friend class PartitionedGraph;

  // ####################### Node Information #######################

  // ! Accessor for node-related information
  MT_KAHYPAR_ATTRIBUTE_ALWAYS_INLINE const Node& node(const HypernodeID u) const {
    ASSERT(u <= _num_nodes, "Node" << u << "does not exist");
    return _nodes[u];
  }

  // ! Accessor for node-related information
  MT_KAHYPAR_ATTRIBUTE_ALWAYS_INLINE Node& node(const HypernodeID u) {
    ASSERT(u <= _num_nodes, "Node" << u << "does not exist");
    return _nodes[u];
  }

  MT_KAHYPAR_ATTRIBUTE_ALWAYS_INLINE IteratorRange<IncidentNetsIterator> incident_nets_of(const HypernodeID u,
                                                                                          const size_t pos = 0) const {
    return integer_range<HyperedgeID>(node(u).firstEntry() + pos, node(u + 1).firstEntry());
  }

  // ####################### Hyperedge Information #######################

  // ! Accessor for hyperedge-related information
  MT_KAHYPAR_ATTRIBUTE_ALWAYS_INLINE const Edge& edge(const HyperedgeID e) const {
    ASSERT(e <= _edges.size(), "Hyperedge" << e << "does not exist");
    return _edges[e];
  }

  // ! Accessor for hyperedge-related information
  MT_KAHYPAR_ATTRIBUTE_ALWAYS_INLINE Edge& edge(const HyperedgeID e) {
    ASSERT(e <= _edges.size(), "Hyperedge" << e << "does not exist");
    return _edges[e];
  }

  // ! Helper function for deduplication of temporary edges. Returns the number of remaining edges
  static size_t deduplicateTmpEdges(TmpEdgeInformation* edge_start, TmpEdgeInformation* edge_end);

  // ! Allocate the temporary contraction buffer
  void allocateTmpContractionBuffer() {
    if ( !_tmp_contraction_buffer ) {
      _tmp_contraction_buffer = new TmpContractionBuffer(_num_nodes, _num_edges);
    }
  }

  // ! Number of nodes
  HypernodeID _num_nodes;
  // ! Number of removed nodes
  HypernodeID _num_removed_nodes;
  // ! Maximum weight of all removed degree zero nodes
  HypernodeWeight _max_removed_degree_zero_hn_weight;
  // ! Number of edges (note that each hyperedge is respresented as two graph edges)
  HyperedgeID _num_edges;
  // ! Total weight of the graph
  HypernodeWeight _total_weight;

  // ! Nodes
  Array<Node> _nodes;
  // ! Edges
  Array<Edge> _edges;
  // ! Edges
  Array<HyperedgeID> _unique_edge_ids;

  // ! Communities
  ds::Clustering _community_ids;

  // ! Fixed Vertex Support
  FixedVertexSupport<StaticGraph> _fixed_vertices;

  // ! Data that is reused throughout the multilevel hierarchy
  // ! to contract the hypergraph and to prevent expensive allocations
  TmpContractionBuffer* _tmp_contraction_buffer;
};

} // namespace ds
} // namespace mt_kahypar
