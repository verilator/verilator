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

#include "repcut_serial.h"

#include <atomic>
#include <type_traits>
#include <mutex>

#include <tbb/parallel_invoke.h>

#include "kahypar-resources/meta/mandatory.h"

#include "mt-kahypar/datastructures/hypergraph_common.h"
#include "mt-kahypar/datastructures/bitset.h"
#include "mt-kahypar/datastructures/connectivity_set.h"
#include "mt-kahypar/datastructures/synchronized_edge_update.h"
#include "mt-kahypar/datastructures/thread_safe_fast_reset_flag_array.h"
#include "mt-kahypar/parallel/atomic_wrapper.h"
#include "mt-kahypar/parallel/stl/scalable_vector.h"
#include "mt-kahypar/parallel/stl/thread_locals.h"
#include "mt-kahypar/utils/range.h"
#include "mt-kahypar/utils/timer.h"

namespace mt_kahypar {

// Forward
class TargetGraph;

namespace ds {

// Forward
template <typename PartitionedGraph,
          bool maintain_connectivity_set>
class DeltaPartitionedGraph;

template <typename Hypergraph = Mandatory>
class PartitionedGraph {
private:
  static_assert(!Hypergraph::is_partitioned,  "Only unpartitioned hypergraphs are allowed");

  using Self = PartitionedGraph<Hypergraph>;
  using NotificationFunc = std::function<void (SynchronizedEdgeUpdate&)>;
  using DeltaFunction = std::function<void (const SynchronizedEdgeUpdate&)>;
  #define NOOP_NOTIFY_FUNC [] (const SynchronizedEdgeUpdate&) { }
  #define NOOP_FUNC [] (const SynchronizedEdgeUpdate&) { }

  // Factory
  using HypergraphFactory = typename Hypergraph::Factory;

  static constexpr bool debug = false;
  static constexpr bool enable_heavy_assert = false;

  class ConnectivityIterator {
   public:
    using iterator_category = std::forward_iterator_tag;
    using value_type = PartitionID;
    using reference = PartitionID&;
    using pointer = const PartitionID*;
    using difference_type = std::ptrdiff_t;

    /*!
     * Constructs a connectivity iterator based on a pin iterator
     */
    ConnectivityIterator(PartitionID first, PartitionID second, unsigned int count) :
      _first(first),
      _second(second),
      _iteration_count(count) {
        if (_first == _second) {
          ++_iteration_count;
        }
        if (_first == kInvalidPartition) {
          ++_iteration_count;
        } else if (_second == kInvalidPartition) {
          ++_iteration_count;
          _second = _first;
        }
        _iteration_count = std::min<unsigned int>(_iteration_count, 2);
    }

    // ! Returns the current partiton id.
    PartitionID operator* () const {
      ASSERT(_iteration_count < 2);
      return _iteration_count == 0 ? _first : _second;
    }

    // ! Prefix increment. The iterator advances to the next valid element.
    ConnectivityIterator & operator++ () {
      ASSERT(_iteration_count < 2);
      ++_iteration_count;
      return *this;
    }

    // ! Postfix increment. The iterator advances to the next valid element.
    ConnectivityIterator operator++ (int) {
      ConnectivityIterator copy = *this;
      operator++ ();
      return copy;
    }

    bool operator!= (const ConnectivityIterator& rhs) {
      return _first != rhs._first || _second != rhs._second ||
             _iteration_count != rhs._iteration_count;
    }

    bool operator== (const ConnectivityIterator& rhs) {
      return _first == rhs._first && _second == rhs._second &&
             _iteration_count == rhs._iteration_count;
    }


   private:
    PartitionID _first = 0;
    PartitionID _second = 0;
    // state of the iterator
    unsigned int _iteration_count = 0;
  };

  struct EdgeMove {
    EdgeMove() :
      block_of_smaller(kInvalidPartition),
      block_of_larger(kInvalidPartition),
      version(0) { }

    PartitionID block_of_smaller;
    PartitionID block_of_larger;
    uint32_t version;
  };

 public:
  static constexpr bool is_static_hypergraph = Hypergraph::is_static_hypergraph;
  static constexpr bool is_graph = Hypergraph::is_graph;
  static constexpr bool is_partitioned = true;
  static constexpr bool supports_connectivity_set = true;
  static constexpr mt_kahypar_partition_type_t TYPE = PartitionedGraphType<Hypergraph>::TYPE;

  static constexpr HyperedgeID HIGH_DEGREE_THRESHOLD = ID(100000);
  static constexpr size_t SIZE_OF_EDGE_LOCK = sizeof(EdgeMove);

  using UnderlyingHypergraph = Hypergraph;
  using HypernodeIterator = typename Hypergraph::HypernodeIterator;
  using HyperedgeIterator = typename Hypergraph::HyperedgeIterator;
  using IncidenceIterator = typename Hypergraph::IncidenceIterator;
  using IncidentNetsIterator = typename Hypergraph::IncidentNetsIterator;
  template<bool maintain_connectivity_set>
  using DeltaPartition = DeltaPartitionedGraph<PartitionedGraph<Hypergraph>, maintain_connectivity_set>;
  using ExtractedBlock = ExtractedHypergraph<Hypergraph>;

  PartitionedGraph() = default;

  explicit PartitionedGraph(const PartitionID k,
                            Hypergraph& hypergraph) :
    _input_num_nodes(hypergraph.initialNumNodes()),
    _input_num_edges(hypergraph.initialNumEdges()),
    _input_unique_ids(hypergraph.maxUniqueID()),
    _k(k),
    _hg(&hypergraph),
    _target_graph(nullptr),
    _part_weights(k, CAtomic<HypernodeWeight>(0)),
    _part_ids(
      "Refinement", "part_ids", hypergraph.initialNumNodes(), false, false),
    _edge_sync_version(0),
    _edge_sync(
      "Refinement", "edge_sync", hypergraph.maxUniqueID(), false, false),
    _edge_sync_is_dirty(false),
    _edge_locks(
      "Refinement", "edge_locks", hypergraph.maxUniqueID(), false, false),
    _edge_markers(Hypergraph::is_static_hypergraph ? 0 : hypergraph.maxUniqueID()) {
    _part_ids.assign(hypergraph.initialNumNodes(), kInvalidPartition, false);
    _edge_sync.assign(hypergraph.maxUniqueID(), EdgeMove(), false);
    _edge_locks.assign(hypergraph.maxUniqueID(), SpinLock(), false);
  }

  explicit PartitionedGraph(const PartitionID k,
                            Hypergraph& hypergraph,
                            parallel_tag_t) :
    _input_num_nodes(hypergraph.initialNumNodes()),
    _input_num_edges(hypergraph.initialNumEdges()),
    _input_unique_ids(hypergraph.maxUniqueID()),
    _k(k),
    _hg(&hypergraph),
    _target_graph(nullptr),
    _part_weights(k, CAtomic<HypernodeWeight>(0)),
    _part_ids(),
    _edge_sync_version(0),
    _edge_sync(),
    _edge_sync_is_dirty(false),
    _edge_locks(),
    _edge_markers() {
    tbb::parallel_invoke([&] {
      _part_ids.resize(
        "Refinement", "part_ids", hypergraph.initialNumNodes());
      _part_ids.assign(hypergraph.initialNumNodes(), kInvalidPartition);
    }, [&] {
      _edge_sync.resize(
        "Refinement", "edge_sync", static_cast<size_t>(hypergraph.maxUniqueID()));
      _edge_sync.assign(hypergraph.maxUniqueID(), EdgeMove());
    }, [&] {
      _edge_locks.resize(
        "Refinement", "edge_locks", static_cast<size_t>(hypergraph.maxUniqueID()));
      _edge_locks.assign(hypergraph.maxUniqueID(), SpinLock());
    }, [&] {
      if (!Hypergraph::is_static_hypergraph) {
        _edge_markers.setSize(hypergraph.maxUniqueID());
      }
    });
  }

  PartitionedGraph(const PartitionedGraph&) = delete;
  PartitionedGraph & operator= (const PartitionedGraph &) = delete;

  PartitionedGraph(PartitionedGraph&& other) = default;
  PartitionedGraph & operator= (PartitionedGraph&& other) = default;

  ~PartitionedGraph() {
    freeInternalData();
  }

  void resetData() {
    tbb::parallel_invoke([&] {
    }, [&] {
      _part_ids.assign(_part_ids.size(), kInvalidPartition);
    }, [&] {
      for (auto& x : _part_weights) x.store(0, std::memory_order_relaxed);
    }, [&] {
      _edge_sync.assign(_hg->maxUniqueID(), EdgeMove());
    });
  }

  // ####################### General Hypergraph Stats ######################

  Hypergraph& hypergraph() {
    ASSERT(_hg);
    return *_hg;
  }

  void setHypergraph(Hypergraph& hypergraph) {
    _hg = &hypergraph;
  }

  // ! Initial number of hypernodes
  HypernodeID initialNumNodes() const {
    return _hg->initialNumNodes();
  }

  // ! Number of nodes of the input hypergraph
  HypernodeID topLevelNumNodes() const {
    return _input_num_nodes;
  }

  // ! Number of removed hypernodes
  HypernodeID numRemovedHypernodes() const {
    return _hg->numRemovedHypernodes();
  }

  // ! Max weight of removed degree zero vertex
  HypernodeWeight maxWeightOfRemovedDegreeZeroNode() const {
    return _hg->maxWeightOfRemovedDegreeZeroNode();
  }

  // ! Initial number of hyperedges
  HyperedgeID initialNumEdges() const {
    return _hg->initialNumEdges();
  }

  // ! Number of edges of the input hypergraph
  HyperedgeID topLevelNumEdges() const {
    return _input_num_edges;
  }

  // ! Number of unique edge ids of the input hypergraph
  HyperedgeID topLevelNumUniqueIds() const {
    return _input_unique_ids;
  }

  // ! Initial number of pins
  HypernodeID initialNumPins() const {
    return _hg->initialNumPins();
  }

  // ! Initial sum of the degree of all vertices
  HypernodeID initialTotalVertexDegree() const {
    return _hg->initialTotalVertexDegree();
  }

  // ! Total weight of hypergraph
  HypernodeWeight totalWeight() const {
    return _hg->totalWeight();
  }

  // ! Number of blocks this hypergraph is partitioned into
  PartitionID k() const {
    return _k;
  }

  // ####################### Mapping ######################

  void setTargetGraph(const TargetGraph* target_graph) {
    _target_graph = target_graph;
  }

  bool hasTargetGraph() const {
    return _target_graph != nullptr;
  }

  const TargetGraph* targetGraph() const {
    return _target_graph;
  }

  // ####################### Iterators #######################

  // ! Iterates in parallel over all active nodes and calls function f
  // ! for each vertex
  template<typename F>
  void doParallelForAllNodes(const F& f) const {
    _hg->doParallelForAllNodes(f);
  }

  // ! Iterates in parallel over all active edges and calls function f
  // ! for each net
  template<typename F>
  void doParallelForAllEdges(const F& f) const {
    _hg->doParallelForAllEdges(f);
  }

  // ! Returns an iterator over the set of active nodes of the hypergraph
  IteratorRange<HypernodeIterator> nodes() const {
    return _hg->nodes();
  }

  // ! Returns an iterator over the set of active edges of the hypergraph
  IteratorRange<HyperedgeIterator> edges() const {
    return _hg->edges();
  }

  // ! Returns a range to loop over the incident nets of hypernode u.
  IteratorRange<IncidentNetsIterator> incidentEdges(const HypernodeID u) const {
    return _hg->incidentEdges(u);
  }

  // ! Returns a range to loop over the incident nets of hypernode u.
  IteratorRange<IncidentNetsIterator> incidentEdges(const HypernodeID u,
                                                    const size_t pos) const {
    return _hg->incident_nets_of(u, pos);
  }

  // ! Returns a range to loop over the pins of hyperedge e.
  IteratorRange<IncidenceIterator> pins(const HyperedgeID e) const {
    return _hg->pins(e);
  }

  // ! Returns a range to loop over the set of block ids contained in hyperedge e.
  IteratorRange<ConnectivityIterator> connectivitySet(const HyperedgeID e) const {
    ASSERT(_hg->edgeIsEnabled(e), "Hyperedge" << e << "is disabled");
    ASSERT(e < _hg->initialNumEdges(), "Hyperedge" << e << "does not exist");
    PartitionID first = partID(edgeSource(e));
    PartitionID second = partID(edgeTarget(e));
    return IteratorRange<ConnectivityIterator>(
      ConnectivityIterator(first, second, 0),
      ConnectivityIterator(first, second, 2));
  }

  // ####################### Hypernode Information #######################

  // ! Weight of a vertex
  HypernodeWeight nodeWeight(const HypernodeID u) const {
    return _hg->nodeWeight(u);
  }

  // ! Sets the weight of a vertex
  void setNodeWeight(const HypernodeID u, const HypernodeWeight weight) {
    const PartitionID block = partID(u);
    if ( block != kInvalidPartition ) {
      ASSERT(block < _k);
      const HypernodeWeight delta = weight - _hg->nodeWeight(u);
      _part_weights[block] += delta;
    }
    _hg->setNodeWeight(u, weight);
  }

  // ! Degree of a hypernode
  HyperedgeID nodeDegree(const HypernodeID u) const {
    return _hg->nodeDegree(u);
  }

  // ! Returns, whether a hypernode is enabled or not
  bool nodeIsEnabled(const HypernodeID u) const {
    return _hg->nodeIsEnabled(u);
  }

  // ! Restores a degree zero hypernode
  void restoreDegreeZeroHypernode(const HypernodeID u, const PartitionID to) {
    _hg->restoreDegreeZeroHypernode(u);
    setNodePart(u, to);
  }

  // ####################### Hyperedge Information #######################

  // ! Target of an edge
  HypernodeID edgeTarget(const HyperedgeID e) const {
    return _hg->edgeTarget(e);
  }

  // ! Source of an edge
  HypernodeID edgeSource(const HyperedgeID e) const {
    return _hg->edgeSource(e);
  }

  // ! Whether the edge is a single pin edge
  bool isSinglePin(const HyperedgeID e) const {
    return _hg->isSinglePin(e);
  }

  // ! Weight of a hyperedge
  HyperedgeWeight edgeWeight(const HyperedgeID e) const {
    return _hg->edgeWeight(e);
  }

  // ! Unique id of a hyperedge
  HyperedgeID uniqueEdgeID(const HyperedgeID e) const {
    return _hg->uniqueEdgeID(e);
  }

  // ! Sets the weight of a hyperedge
  void setEdgeWeight(const HyperedgeID e, const HyperedgeWeight weight) {
    _hg->setEdgeWeight(e, weight);
  }

  // ! Number of pins of a hyperedge
  HypernodeID edgeSize(const HyperedgeID e) const {
    return _hg->edgeSize(e);
  }

  // ! Returns, whether a hyperedge is enabled or not
  bool edgeIsEnabled(const HyperedgeID e) const {
    return _hg->edgeIsEnabled(e);
  }

  // ####################### Uncontraction #######################

  template<typename GainCache>
  void uncontract(const Batch& batch, GainCache& gain_cache) {
    // Set block ids of contraction partners
    tbb::parallel_for(UL(0), batch.size(), [&](const size_t i) {
      const Memento& memento = batch[i];
      ASSERT(nodeIsEnabled(memento.u));
      ASSERT(!nodeIsEnabled(memento.v));
      const PartitionID part_id = partID(memento.u);
      ASSERT(part_id != kInvalidPartition && part_id < _k);
      setOnlyNodePart(memento.v, part_id);
    });

    _hg->uncontract(batch,
      [&](const HyperedgeID e) { return !_edge_markers.compare_and_set_to_true(uniqueEdgeID(e)); },
      [&](const HypernodeID u, const HypernodeID v, const HyperedgeID e) {
        // In this case, e was a single pin edge before uncontraction
        gain_cache.uncontractUpdateAfterRestore(*this, u, v, e, 0);
      },
      [&](const HypernodeID u, const HypernodeID v, const HyperedgeID e) {
        // In this case, u is replaced by v in e
        gain_cache.uncontractUpdateAfterReplacement(*this, u, v, e);
      });

    if constexpr ( GainCache::initializes_gain_cache_entry_after_batch_uncontractions ) {
      tbb::parallel_for(UL(0), batch.size(), [&](const size_t i) {
        const Memento& memento = batch[i];
        gain_cache.initializeGainCacheEntryForNode(*this, memento.v);
      });
    }
    gain_cache.batchUncontractionsCompleted();
    ++_edge_sync_version;
  }

  // ####################### Restore Hyperedges #######################

  void restoreLargeEdge(const HyperedgeID& he) {
    _hg->restoreLargeEdge(he);
  }

  /*!
   * Restores a single pin hyperedge previously removed from the hypergraph.
   */
  void restoreSinglePinEdge(const HyperedgeID& he) {
    throw UnsupportedOperationException(
      "restoreSinglePinEdge is not supported in partitioned graph");
  }

  template<typename GainCache>
  void restoreSinglePinAndParallelNets(const vec<typename Hypergraph::ParallelHyperedge>& hes_to_restore,
                                       GainCache& gain_cache) {
    _edge_markers.reset();
    _hg->restoreSinglePinAndParallelNets(hes_to_restore);

    tbb::parallel_for(UL(0), hes_to_restore.size(), [&](const size_t i) {
      const HyperedgeID he = hes_to_restore[i].old_id;
      ASSERT(edgeIsEnabled(he));
      const bool is_single_pin_he = edgeSize(he) == 1;
      if ( is_single_pin_he ) {
        // Restore single-pin net
        HypernodeID single_vertex_of_he = edgeSource(he);
        const PartitionID block_of_single_pin = partID(single_vertex_of_he);
        gain_cache.restoreSinglePinHyperedge(
          single_vertex_of_he, block_of_single_pin, edgeWeight(he));
      } else if ( nodeIsEnabled(edgeSource(he)) ) {
        // Restore parallel net
        gain_cache.restoreIdenticalHyperedge(*this, he);
      }
    });
    ++_edge_sync_version;
  }

  // ####################### Partition Information #######################

  // ! Block that vertex u belongs to
  PartitionID partID(const HypernodeID u) const {
    ASSERT(u < initialNumNodes(), "Hypernode" << u << "does not exist");
    return _part_ids[u];
  }

  void extractPartIDs(Array<PartitionID>& part_ids) {
    // If we pass the input hypergraph to initial partitioning, then initial partitioning
    // will pass an part ID vector of size |V'|, where V' are the number of nodes of
    // smallest hypergraph, while the _part_ids vector of the input hypergraph is initialized
    // with the original number of nodes. This can cause segmentation fault when we simply swap them
    // during main uncoarsening.
    if ( _part_ids.size() == part_ids.size() ) {
      std::swap(_part_ids, part_ids);
    } else {
      ASSERT(part_ids.size() <= _part_ids.size());
      tbb::parallel_for(UL(0), part_ids.size(), [&](const size_t i) {
        part_ids[i] = _part_ids[i];
      });
    }
  }


  void setOnlyNodePart(const HypernodeID u, PartitionID p) {
    ASSERT(p != kInvalidPartition && p < _k);
    ASSERT(_part_ids[u] == kInvalidPartition);
    _part_ids[u] = p;
  }

  void setNodePart(const HypernodeID u, PartitionID p) {
    ASSERT(_part_ids[u] == kInvalidPartition);
    setOnlyNodePart(u, p);
    _part_weights[p].fetch_add(nodeWeight(u), std::memory_order_relaxed);
  }

  // ! Changes the block id of vertex u from block 'from' to block 'to'
  // ! Returns true, if move of vertex u to corresponding block succeeds.
  template<typename SuccessFunc>
  MT_KAHYPAR_ATTRIBUTE_ALWAYS_INLINE
  bool changeNodePartNoSync(const HypernodeID u,
                            PartitionID from,
                            PartitionID to,
                            HypernodeWeight max_weight_to,
                            SuccessFunc&& report_success) {
    return changeNodePartImpl<false, false>(u, from, to,
      max_weight_to, report_success, NOOP_FUNC, NOOP_NOTIFY_FUNC);
  }

  MT_KAHYPAR_ATTRIBUTE_ALWAYS_INLINE
  bool changeNodePartNoSync(const HypernodeID u,
                            PartitionID from,
                            PartitionID to,
                            const bool force_moving_fixed_vertices = false) {
    return changeNodePartImpl<false, false>(u, from, to,
      std::numeric_limits<HypernodeWeight>::max(), []{},
      NOOP_FUNC, NOOP_NOTIFY_FUNC, force_moving_fixed_vertices);
  }

  template<typename SuccessFunc>
  MT_KAHYPAR_ATTRIBUTE_ALWAYS_INLINE
  bool changeNodePart(const HypernodeID u,
                      PartitionID from,
                      PartitionID to,
                      HypernodeWeight max_weight_to,
                      SuccessFunc&& report_success,
                      const DeltaFunction& delta_func) {
    return changeNodePartImpl<true, false>(u, from, to,
      max_weight_to, report_success, delta_func, NOOP_NOTIFY_FUNC);
  }

  MT_KAHYPAR_ATTRIBUTE_ALWAYS_INLINE
  bool changeNodePart(const HypernodeID u,
                            PartitionID from,
                            PartitionID to) {
    return changeNodePartImpl<true, false>(u, from, to,
      std::numeric_limits<HypernodeWeight>::max(), []{}, NOOP_FUNC, NOOP_NOTIFY_FUNC);
  }

  MT_KAHYPAR_ATTRIBUTE_ALWAYS_INLINE
  bool changeNodePart(const HypernodeID u,
                      PartitionID from,
                      PartitionID to,
                      const DeltaFunction& delta_func) {
    return changeNodePartImpl<true, false>(u, from, to,
      std::numeric_limits<HypernodeWeight>::max(), []{}, delta_func, NOOP_NOTIFY_FUNC);
  }

  template<typename GainCache, typename SuccessFunc>
  MT_KAHYPAR_ATTRIBUTE_ALWAYS_INLINE
  bool changeNodePart(GainCache& gain_cache,
                      const HypernodeID u,
                      PartitionID from,
                      PartitionID to,
                      HypernodeWeight max_weight_to,
                      SuccessFunc&& report_success,
                      const DeltaFunction& delta_func) {
    auto my_delta_func = [&](const SynchronizedEdgeUpdate& sync_update) {
      delta_func(sync_update);
      gain_cache.deltaGainUpdate(*this, sync_update);
    };
    if constexpr ( !GainCache::requires_notification_before_update ) {
      return changeNodePartImpl<true, false>(u, from, to, max_weight_to,
        report_success, my_delta_func, NOOP_NOTIFY_FUNC);
    } else {
      return changeNodePartImpl<true, true>(u, from, to, max_weight_to,
        report_success, my_delta_func, [&](SynchronizedEdgeUpdate& sync_update) {
          gain_cache.notifyBeforeDeltaGainUpdate(*this, sync_update);
        });
    }
  }

  template<typename GainCache>
  MT_KAHYPAR_ATTRIBUTE_ALWAYS_INLINE
  bool changeNodePart(GainCache& gain_cache,
                      const HypernodeID u,
                      PartitionID from,
                      PartitionID to) {
    return changeNodePart(gain_cache, u, from, to,
      std::numeric_limits<HypernodeWeight>::max(), []{}, NoOpDeltaFunc());
  }

  // ! Weight of a block
  HypernodeWeight partWeight(const PartitionID p) const {
    ASSERT(p != kInvalidPartition && p < _k);
    return _part_weights[p].load(std::memory_order_relaxed);
  }

  // ! Returns whether hypernode u is adjacent to a least one cut hyperedge.
  bool isBorderNode(const HypernodeID u) const {
    const PartitionID part_id = partID(u);
    if ( nodeDegree(u) <= HIGH_DEGREE_THRESHOLD ) {
      for ( const HyperedgeID& he : incidentEdges(u) ) {
        if ( partID(edgeTarget(he)) != part_id ) {
          return true;
        }
      }
    }
    return false;
  }

  HypernodeID numIncidentCutHyperedges(const HypernodeID u) const {
    const PartitionID part_id = partID(u);
    HypernodeID num_incident_cut_hyperedges = 0;
    for ( const HyperedgeID& he : incidentEdges(u) ) {
      if ( partID(edgeTarget(he)) != part_id ) {
        ++num_incident_cut_hyperedges;
      }
    }
    return num_incident_cut_hyperedges;
  }

  // ! Number of blocks which pins of hyperedge e belongs to
  PartitionID connectivity(const HyperedgeID e) const {
    ASSERT(e < _hg->initialNumEdges(), "Hyperedge" << e << "does not exist");
    ASSERT(edgeIsEnabled(e), "Hyperedge" << e << "is disabled");
    const PartitionID source_id = partID(edgeSource(e));
    const PartitionID target_id = partID(edgeTarget(e));
    PartitionID sum = 0;
    if (source_id != kInvalidPartition) {
      ++sum;
    }
    if (target_id != kInvalidPartition && target_id != source_id) {
      ++sum;
    }
    return sum;
  }

  // ! Returns the number pins of hyperedge e that are part of block id
  HypernodeID pinCountInPart(const HyperedgeID e, const PartitionID p) const {
    ASSERT(e < _hg->initialNumEdges(), "Hyperedge" << e << "does not exist");
    ASSERT(edgeIsEnabled(e), "Hyperedge" << e << "is disabled");
    ASSERT(p != kInvalidPartition && p < _k);
    HypernodeID count = 0;
    if (p == partID(edgeSource(e))) {
      count++;
    }
    if (!isSinglePin(e) && p == partID(edgeTarget(e))) {
      count++;
    }
    return count;
  }

  // ! Creates a shallow copy of the connectivity set of hyperedge he
  StaticBitset& shallowCopyOfConnectivitySet(const HyperedgeID he) const {
    // Shallow copy not possible for graph data structure
    Bitset& deep_copy = deepCopyOfConnectivitySet(he);
    StaticBitset& shallow_copy = _shallow_copy_bitset.local();
    shallow_copy.set(deep_copy.numBlocks(), deep_copy.data());
    return shallow_copy;
  }

  // ! Creates a deep copy of the connectivity set of hyperedge he
  Bitset& deepCopyOfConnectivitySet(const HyperedgeID he) const {
    Bitset& deep_copy = _deep_copy_bitset.local();
    deep_copy.resize(_k);
    const PartitionID source_block = partID(edgeSource(he));
    const PartitionID target_block = partID(edgeTarget(he));
    if ( source_block != kInvalidPartition ) deep_copy.set(source_block);
    if ( target_block != kInvalidPartition ) deep_copy.set(target_block);
    return deep_copy;
  }

  // ! Creates a SynchronizedEdgeUpdate for the hyperedge. The caller must ensure that there is no concurrent access
  // ! which modifies connectivity set of the hyperedge.
  MT_KAHYPAR_ATTRIBUTE_ALWAYS_INLINE
  SynchronizedEdgeUpdate createEdgeUpdate(const HyperedgeID he) {
    SynchronizedEdgeUpdate sync_update;
    ASSERT(uniqueEdgeID(he) < _edge_locks.size());
    sync_update.he = he;
    sync_update.edge_weight = edgeWeight(he);
    sync_update.edge_size = edgeSize(he);
    sync_update.target_graph = _target_graph;
    sync_update.edge_locks = &_edge_locks;
    return sync_update;
  }

  // ! Initializes the partition of the hypergraph, if block ids are assigned with
  // ! setOnlyNodePart(...). In that case, block weights must be initialized explicitly here.
  void initializePartition() {
    initializeBlockWeights();
  }

  // ! Reset partition (not thread-safe)
  void resetPartition() {
    _part_ids.assign(_part_ids.size(), kInvalidPartition, false);
    _edge_sync.assign(_hg->maxUniqueID(), EdgeMove(), false);
    for (auto& weight : _part_weights) {
      weight.store(0, std::memory_order_relaxed);
    }
  }

  // ! Reset synchronization. Necessary after changeNodePartNoSync (not thread-safe)
  void resetEdgeSynchronization() {
    ++_edge_sync_version;
    _edge_sync_is_dirty = false;
  }

  // ! Only for testing
  void recomputePartWeights() {
    for (PartitionID p = 0; p < _k; ++p) {
      _part_weights[p].store(0);
    }

    for (HypernodeID u : nodes()) {
      _part_weights[ partID(u) ] += nodeWeight(u);
    }
  }

  void recomputeMoveFromPenalty(const HypernodeID) {
    // Nothing to do here
  }

  // ! Only for testing
  bool checkTrackedPartitionInformation() {
    bool success = true;

    for (HyperedgeID e : edges()) {
      PartitionID expected_connectivity = 0;
      for (PartitionID i = 0; i < k(); ++i) {
        expected_connectivity += (pinCountInPart(e, i) > 0);
      }
      if ( expected_connectivity != connectivity(e) ) {
        LOG << "Connectivity of hyperedge" << e << "=>" <<
            "Expected:" << V(expected_connectivity)  << "," <<
            "Actual:" << V(connectivity(e));
        success = false;
      }
    }

    return success;
  }

  // ! Only for testing
  template<typename GainCache>
  bool checkTrackedPartitionInformation(GainCache& gain_cache) {
    bool success = true;

    for (HyperedgeID e : edges()) {
      PartitionID expected_connectivity = 0;
      for (PartitionID i = 0; i < k(); ++i) {
        expected_connectivity += (pinCountInPart(e, i) > 0);
      }
      if ( expected_connectivity != connectivity(e) ) {
        LOG << "Connectivity of hyperedge" << e << "=>" <<
            "Expected:" << V(expected_connectivity)  << "," <<
            "Actual:" << V(connectivity(e));
        success = false;
      }
    }

    if ( gain_cache.isInitialized() ) {
      for (HypernodeID u : nodes()) {
        const PartitionID block_of_u = partID(u);
        if ( gain_cache.penaltyTerm(u, block_of_u) !=
             gain_cache.recomputePenaltyTerm(*this, u) ) {
          LOG << "Penalty term of hypernode" << u << "=>" <<
              "Expected:" << V(gain_cache.recomputePenaltyTerm(*this, u)) << ", " <<
              "Actual:" <<  V(gain_cache.penaltyTerm(u, block_of_u));
          for ( const HyperedgeID& e : incidentEdges(u) ) {
            LOG << V(u) << V(partID(u)) << V(e) << V(edgeSize(e))
                << V(edgeWeight(e)) << V(pinCountInPart(e, partID(u)));
          }
          success = false;
        }

        for ( const PartitionID& i : gain_cache.adjacentBlocks(u) ) {
          if (partID(u) != i) {
            if ( gain_cache.benefitTerm(u, i) !=
                 gain_cache.recomputeBenefitTerm(*this, u, i) ) {
              LOG << "Benefit term of hypernode" << u << "in block" << i << "=>" <<
                  "Expected:" << V(gain_cache.recomputeBenefitTerm(*this, u, i)) << ", " <<
                  "Actual:" <<  V(gain_cache.benefitTerm(u, i));
              success = false;
            }
          }
        }
      }
      if ( !gain_cache.verifyTrackedAdjacentBlocksOfNodes(*this) ) {
        success = false;
      }
    }
    return success;
  }

  // ####################### Fixed Vertex Support #######################

  bool hasFixedVertices() const {
    return _hg->hasFixedVertices();
  }

  bool isFixed(const HypernodeID hn) const {
    return _hg->isFixed(hn);
  }

  PartitionID fixedVertexBlock(const HypernodeID hn) const {
    return _hg->fixedVertexBlock(hn);
  }

  // ####################### Memory Consumption #######################

  void memoryConsumption(utils::MemoryTreeNode* parent) const {
    ASSERT(parent);
    parent->addChild("Part Weights", sizeof(CAtomic<HypernodeWeight>) * _k);
    parent->addChild("Part IDs", sizeof(PartitionID) * _hg->initialNumNodes());
    parent->addChild("Edge Synchronization", sizeof(EdgeMove) * _edge_sync.size());
    parent->addChild("Edge Locks", sizeof(SpinLock) * _edge_locks.size());
    parent->addChild("Edge Markers", sizeof(uint8_t) * _edge_markers.size());
  }

  // ####################### Extract Block #######################

  // ! Extracts a block of the partition.
  // ! The extracted block stores a hypergraph containing all nodes and hyperedges
  // ! of the corresponding block, a vector that maps the node IDs of the original
  // ! hypergraph to the node IDs of the extracted hypergraph, and an array that
  // ! stores which hyperedges of the extracted hypergraph are already cut in
  // ! the original hypergraph.
  // ! If cut_net_splitting is activated, then cut hyperedges are splitted containing
  // ! only the pins of the corresponding block. Otherwise, they are discarded.
  ExtractedBlock extract(const PartitionID block,
                         const vec<uint8_t>* already_cut,
                         bool /*cut_net_splitting*/,
                         bool stable_construction_of_incident_edges) {
    ASSERT(block != kInvalidPartition && block < _k);
    ASSERT(!already_cut || already_cut->size() == _hg->initialNumEdges());

    // Compactify vertex ids
    ExtractedBlock extracted_block;
    vec<HypernodeID>& node_mapping = extracted_block.hn_mapping;
    node_mapping.assign(_hg->initialNumNodes(), kInvalidHypernode);
    vec<HyperedgeID> he_mapping(_hg->initialNumEdges(), kInvalidHyperedge);
    HypernodeID num_nodes = 0;
    HypernodeID num_edges = 0;
    tbb::parallel_invoke([&] {
      for (const HypernodeID& node : nodes()) {
        if (partID(node) == block) {
          node_mapping[node] = num_nodes++;
        }
      }
    }, [&] {
      for (const HyperedgeID& edge : edges()) {
        const HypernodeID source = edgeSource(edge);
        const HypernodeID target = edgeTarget(edge);
        if (partID(source) == block && partID(target) == block && source < target) {
          he_mapping[edge] = num_edges++;
        }
      }
    });

    // Extract plain hypergraph data for corresponding block
    using EdgeVector = vec<std::pair<HypernodeID, HypernodeID>>;
    EdgeVector edge_vector;
    vec<HyperedgeWeight> edge_weight;
    vec<HypernodeWeight> node_weight;
    tbb::parallel_invoke([&] {
      edge_vector.resize(num_edges);
      edge_weight.resize(num_edges);
      doParallelForAllEdges([&](const HyperedgeID edge) {
        const HypernodeID source = edgeSource(edge);
        const HypernodeID target = edgeTarget(edge);
        if (partID(source) == block && partID(target) == block && source < target) {
          ASSERT(he_mapping[edge] < num_edges);
          edge_weight[he_mapping[edge]] = edgeWeight(edge);
          edge_vector[he_mapping[edge]] = {node_mapping[source], node_mapping[target]};
        }
      });
    }, [&] {
      node_weight.resize(num_nodes);
      doParallelForAllNodes([&](const HypernodeID node) {
        if (partID(node) == block) {
          node_weight[node_mapping[node]] = nodeWeight(node);
        }
      });
    }, [&] {
      if ( already_cut ) {
        // Extracted graph only contains non-cut edges
        extracted_block.already_cut.assign(num_edges, 0);
      }
    });

    // Construct hypergraph
    extracted_block.hg = HypergraphFactory::construct_from_graph_edges(
      num_nodes, num_edges, edge_vector, edge_weight.data(), node_weight.data(),
      stable_construction_of_incident_edges);

    // Set community ids
    doParallelForAllNodes([&](const HypernodeID& node) {
      if (partID(node) == block) {
        const HypernodeID extracted_node = node_mapping[node];
        extracted_block.hg.setCommunityID(extracted_node, _hg->communityID(node));
      }
    });
    return extracted_block;
  }

  // ! Extracts all blocks of the partition (from block 0 to block k).
  // ! This function has running time linear in the size of the original hypergraph
  // ! and should be used instead of extract(...) when more than two blocks should be extracted.
  std::pair<vec<ExtractedBlock>, vec<HypernodeID>> extractAllBlocks(const PartitionID k,
                                                                    const vec<uint8_t>* already_cut,
                                                                    const bool /*cut_net_splitting*/,
                                                                    const bool stable_construction_of_incident_edges) {
    ASSERT(k <= _k);

    // Compactify node and edge ids
    vec<HypernodeID> hn_mapping(_hg->initialNumNodes(), kInvalidHypernode);
    vec<HyperedgeID> he_mapping(_hg->initialNumEdges(), kInvalidHyperedge);
    vec<parallel::AtomicWrapper<HypernodeID>> nodes_cnt(
      k, parallel::AtomicWrapper<HypernodeID>(0));
    vec<parallel::AtomicWrapper<HyperedgeID>> edges_cnt(
      k, parallel::AtomicWrapper<HyperedgeID>(0));
    if ( stable_construction_of_incident_edges ) {
      // Stable construction for deterministic behavior requires
      // to determine node and edge IDs sequentially
      tbb::parallel_invoke([&] {
        for ( const HypernodeID& hn : nodes() ) {
          const PartitionID block = partID(hn);
          if ( block < k ) {
            hn_mapping[hn] = nodes_cnt[block]++;
          }
        }
      }, [&] {
        for ( const HyperedgeID& he : edges() ) {
          const HypernodeID source = edgeSource(he);
          const HypernodeID target = edgeTarget(he);
          const PartitionID sourceBlock = partID(source);
          const PartitionID targetBlock = partID(target);
          if (source < target && sourceBlock == targetBlock && sourceBlock < k) {
            he_mapping[he] = edges_cnt[sourceBlock]++;
          }
        }
      });
    } else {
      tbb::parallel_invoke([&] {
        doParallelForAllNodes([&](const HypernodeID& hn) {
          const PartitionID block = partID(hn);
          if ( block < k ) {
            hn_mapping[hn] = nodes_cnt[block]++;
          }
        });
      }, [&] {
        doParallelForAllEdges([&](const HyperedgeID& he) {
          const HypernodeID source = edgeSource(he);
          const HypernodeID target = edgeTarget(he);
          const PartitionID sourceBlock = partID(source);
          const PartitionID targetBlock = partID(target);
          if (source < target && sourceBlock == targetBlock && sourceBlock < k) {
            he_mapping[he] = edges_cnt[sourceBlock]++;
          }
        });
      });
    }

    using EdgeVector = vec<std::pair<HypernodeID, HypernodeID>>;
    vec<ExtractedBlock> extracted_blocks(k);
    vec<EdgeVector> edge_vector(k);
    vec<vec<HyperedgeWeight>> edge_weight(k);
    vec<vec<HypernodeWeight>> node_weight(k);
    // Allocate auxilliary graph data structures
    tbb::parallel_for(static_cast<PartitionID>(0), k, [&](const PartitionID p) {
      const HypernodeID num_nodes = nodes_cnt[p];
      const HyperedgeID num_edges = edges_cnt[p];
      tbb::parallel_invoke([&] {
        edge_vector[p].resize(num_edges);
      }, [&] {
        edge_weight[p].resize(num_edges);
      }, [&] {
        node_weight[p].resize(num_nodes);
      }, [&] {
        if ( already_cut ) {
          // Extracted graph only contains non-cut edges
          extracted_blocks[p].already_cut.assign(num_edges, 0);
        }
      });
    });

    // Write blocks to auxilliary graph data structure
    tbb::parallel_invoke([&] {
      doParallelForAllEdges([&](const HyperedgeID& he) {
        const HyperedgeID mapped_he = he_mapping[he];
        const HypernodeID source = edgeSource(he);
        const HypernodeID target = edgeTarget(he);
        const PartitionID sourceBlock = partID(source);
        const PartitionID targetBlock = partID(target);
        if (source < target && sourceBlock == targetBlock && sourceBlock < k) {
          ASSERT(UL(mapped_he) < edge_weight[sourceBlock].size());
          edge_weight[sourceBlock][mapped_he] = edgeWeight(he);
          edge_vector[sourceBlock][mapped_he] =
            { hn_mapping[edgeSource(he)], hn_mapping[edgeTarget(he)] };
        }
      });
    }, [&] {
      doParallelForAllNodes([&](const HypernodeID& hn) {
        const PartitionID block = partID(hn);
        const HypernodeID mapped_hn = hn_mapping[hn];
        if ( block < k ) {
          ASSERT(UL(mapped_hn) < node_weight[block].size());
          node_weight[block][mapped_hn] = nodeWeight(hn);
        }
      });
    });

    // Construct graph of each block
    tbb::parallel_for(static_cast<PartitionID>(0), k, [&](const PartitionID p) {
      const HypernodeID num_nodes = nodes_cnt[p];
      const HyperedgeID num_edges = edges_cnt[p];
      extracted_blocks[p].hg = HypergraphFactory::construct_from_graph_edges(
        num_nodes, num_edges, edge_vector[p], edge_weight[p].data(), node_weight[p].data(),
        stable_construction_of_incident_edges);
    });

    // Set community ids
    doParallelForAllNodes([&](const HypernodeID& hn) {
      const PartitionID block = partID(hn);
      if ( block < k ) {
        extracted_blocks[block].hg.setCommunityID(hn_mapping[hn], _hg->communityID(hn));
      }
    });

    parallel::parallel_free(edge_vector);
    parallel::parallel_free(edge_weight, node_weight);

    return std::make_pair(std::move(extracted_blocks), std::move(hn_mapping));
  }

  void freeInternalData() {
    if ( _k > 0 ) {
      parallel::parallel_free(_part_ids, _edge_sync, _edge_locks);
    }
    _k = 0;
  }

 private:
  template<bool sync, bool notify, typename SuccessFunc>
  MT_KAHYPAR_ATTRIBUTE_ALWAYS_INLINE
  bool changeNodePartImpl(const HypernodeID u,
                          PartitionID from,
                          PartitionID to,
                          HypernodeWeight max_weight_to,
                          SuccessFunc&& report_success,
                          const DeltaFunction& delta_func,
                          const NotificationFunc& notify_func,
                          const bool force_moving_fixed_vertices = false) {
    unused(force_moving_fixed_vertices);
    static_assert(!notify || sync);
    ASSERT(partID(u) == from);
    ASSERT(from != to);
    ASSERT(force_moving_fixed_vertices || !isFixed(u));
    const HypernodeWeight weight = nodeWeight(u);
    const HypernodeWeight to_weight_after = _part_weights[to].add_fetch(weight, std::memory_order_relaxed);
    if (to_weight_after <= max_weight_to) {
      _part_weights[from].fetch_sub(weight, std::memory_order_relaxed);
      report_success();
      DBG << "<<< Start changing node part: " << V(u) << " - " << V(from) << " - " << V(to);
      if constexpr (sync) {
        ASSERT(!_edge_sync_is_dirty, "Missing call to resetEdgeSynchronization after changeNodePartNoSync!");
        SynchronizedEdgeUpdate sync_update;
        sync_update.from = from;
        sync_update.to = to;
        sync_update.target_graph = _target_graph;
        sync_update.edge_locks = &_edge_locks;
        for (const HyperedgeID edge : incidentEdges(u)) {
          if (!isSinglePin(edge)) {
            sync_update.he = edge;
            sync_update.edge_weight = edgeWeight(edge);
            sync_update.edge_size = edgeSize(edge);
            synchronizeMoveOnEdge<notify>(sync_update, edge, u, to, notify_func);
            sync_update.pin_count_in_from_part_after = sync_update.block_of_other_node == from ? 1 : 0;
            sync_update.pin_count_in_to_part_after = sync_update.block_of_other_node == to ? 2 : 1;
            delta_func(sync_update);
          }
        }
      } else {
        // small hack to only set this when assertions are enabled
        ASSERT(_edge_sync_is_dirty = true);
      }
      repcut_serial::Ref(_part_ids[u]).store(to, std::memory_order_relaxed);
      DBG << "Done changing node part: " << V(u) << " >>>";
      return true;
    } else {
      _part_weights[to].fetch_sub(weight, std::memory_order_relaxed);
      return false;
    }
  }

  void initializeBlockWeights() {
    tbb::parallel_for(tbb::blocked_range<HypernodeID>(HypernodeID(0), initialNumNodes()),
      [&](tbb::blocked_range<HypernodeID>& r) {
        // this is not enumerable_thread_specific because of the static partitioner
        parallel::scalable_vector<HypernodeWeight> part_weight_deltas(_k, 0);
        for (HypernodeID node = r.begin(); node < r.end(); ++node) {
          if (nodeIsEnabled(node)) {
            const PartitionID part = partID(node);
            ASSERT(part >= 0 && part < _k);
            part_weight_deltas[part] += nodeWeight(node);
          }
        }
        for (PartitionID p = 0; p < _k; ++p) {
          _part_weights[p].fetch_add(part_weight_deltas[p], std::memory_order_relaxed);
        }
      },
      tbb::static_partitioner()
    );
  }

  // ####################### Edge Locks #######################

  // This function synchronizes a move on an edge and returns the block ID
  // of the target node of the corresponding edge. The function assumes that
  // node u is moved to the block 'to'.
  template<bool notify>
  MT_KAHYPAR_ATTRIBUTE_ALWAYS_INLINE
  PartitionID synchronizeMoveOnEdge(SynchronizedEdgeUpdate& sync_update,
                                    const HyperedgeID edge,
                                    const HypernodeID u,
                                    const PartitionID to,
                                    const NotificationFunc& notify_func) {
    const HyperedgeID unique_id = uniqueEdgeID(edge);
    const HypernodeID v = edgeTarget(edge);
    PartitionID block_of_v = repcut_serial::Ref(_part_ids[v]).load(std::memory_order_relaxed);
    EdgeMove& edge_move = _edge_sync[unique_id];

    // Note: It is important that `edge_move` tracks the block of both nodes.
    // Previously, the struct only contained the block of the node that was moved most recently.
    // However, this caused a race condition if a move is applied and then immediately reverted.
    // If the other node is moved concurrently and the concurrent move acquired the lock first
    // but did not update _part_ids yet, the reverting move would incorrectly use the old part id.
    auto execute_sychnronization = [&](PartitionID& move_block_u, PartitionID& move_block_v) {
      _edge_locks[unique_id].lock();
      if ( move_block_v != kInvalidPartition && edge_move.version == _edge_sync_version ) {
        ASSERT(move_block_v < _k);
        block_of_v = move_block_v;
      } else if ( edge_move.version != _edge_sync_version ) {
        move_block_v = kInvalidPartition;
      }
      move_block_u = to;
      edge_move.version = _edge_sync_version;
      sync_update.block_of_other_node = block_of_v;
      if constexpr ( notify ) {
        notify_func(sync_update);
      }
      _edge_locks[unique_id].unlock();
    };

    if (u < v) {
      execute_sychnronization(edge_move.block_of_smaller, edge_move.block_of_larger);
    } else {
      ASSERT(u > v);
      execute_sychnronization(edge_move.block_of_larger, edge_move.block_of_smaller);
    }
    return block_of_v;
  }

  HypernodeID _input_num_nodes = 0;

  HyperedgeID _input_num_edges = 0;

  HyperedgeID _input_unique_ids = 0;

  // ! Number of blocks
  PartitionID _k = 0;

  // ! Underlying graph
  Hypergraph* _hg = nullptr;

  // ! Target graph on which this graph is mapped
  const TargetGraph* _target_graph;

  // ! Weight and information for all blocks.
  parallel::scalable_vector< CAtomic<HypernodeWeight> > _part_weights;

  // ! Current block IDs of the vertices
  Array< PartitionID > _part_ids;

  // ! Incrementing this counter invalidates all EdgeMove objects (see _edge_sync)
  // ! with a version < _edge_sync_version
  uint32_t _edge_sync_version;

  // ! Used to syncronize moves on edges
  Array< EdgeMove > _edge_sync;
  bool _edge_sync_is_dirty;

  // ! Lock to syncronize moves on edges
  Array< SpinLock > _edge_locks;

  // ! We need to synchronize uncontractions via atomic markers
  ThreadSafeFastResetFlagArray<uint8_t> _edge_markers;

  // ! Bitsets to create shallow and deep copies of the connectivity set
  // ! They are only required to implement the same interface of our hypergraph
  // ! data structure but should not be required in practice.
  mutable tbb::enumerable_thread_specific<Bitset> _deep_copy_bitset;
  mutable tbb::enumerable_thread_specific<StaticBitset> _shallow_copy_bitset;
};

} // namespace ds
} // namespace mt_kahypar
