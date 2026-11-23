/*******************************************************************************
 * MIT License
 *
 * This file is part of Mt-KaHyPar.
 *
 * Copyright (C) 2020 Lars Gottesbüren <lars.gottesbueren@kit.edu>
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

#include <atomic>
#include <type_traits>

#include "kahypar-resources/meta/mandatory.h"

#include "mt-kahypar/datastructures/hypergraph_common.h"
#include "mt-kahypar/datastructures/sparse_map.h"
#include "mt-kahypar/datastructures/delta_connectivity_set.h"
#include "mt-kahypar/datastructures/connectivity_set.h"
#include "mt-kahypar/datastructures/synchronized_edge_update.h"
#include "mt-kahypar/parallel/stl/scalable_vector.h"
#include "mt-kahypar/partition/context.h"
#include "mt-kahypar/utils/exception.h"

namespace mt_kahypar {
namespace ds {

/*!
 * Special graph data structure for the FM algorithm.
 * This is a variant of DeltaPartitionedHypergraph specialized for graphs.
 * See delte_partitioned_hypergraph.h for more details.
 */
template <typename PartitionedGraph = Mandatory,
          bool maintain_connectivity_set = false>
class DeltaPartitionedGraph {
 private:
  static constexpr size_t MAP_SIZE_SMALL = 128;

  using HypernodeIterator = typename PartitionedGraph::HypernodeIterator;
  using HyperedgeIterator = typename PartitionedGraph::HyperedgeIterator;
  using IncidenceIterator = typename PartitionedGraph::IncidenceIterator;
  using IncidentNetsIterator = typename PartitionedGraph::IncidentNetsIterator;
  using DummyConnectivitySet = DeltaConnectivitySet<ConnectivitySets>;
  using ConnectivitySetIterator = typename DummyConnectivitySet::Iterator;

 public:
  static constexpr bool supports_connectivity_set = false;
  static constexpr HyperedgeID HIGH_DEGREE_THRESHOLD = PartitionedGraph::HIGH_DEGREE_THRESHOLD;

  DeltaPartitionedGraph(const Context& context) :
    _k(context.partition.k),
    _pg(nullptr),
    _part_weights_delta(context.partition.k, 0),
    _part_ids_delta(),
    _dummy_connectivity_set() {
      _part_ids_delta.initialize(MAP_SIZE_SMALL);
    }

  DeltaPartitionedGraph(const DeltaPartitionedGraph&) = delete;
  DeltaPartitionedGraph & operator= (const DeltaPartitionedGraph &) = delete;

  DeltaPartitionedGraph(DeltaPartitionedGraph&& other) = default;
  DeltaPartitionedGraph & operator= (DeltaPartitionedGraph&& other) = default;

  ~DeltaPartitionedGraph() = default;

  void setPartitionedHypergraph(PartitionedGraph* pg) {
    _pg = pg;
  }

  // ####################### Mapping ######################

  bool hasTargetGraph() const {
    ASSERT(_pg);
    return _pg->hasTargetGraph();
  }

  const TargetGraph* targetGraph() const {
    ASSERT(_pg);
    return _pg->targetGraph();
  }

  // ####################### Iterators #######################

  // ! Returns an iterator over the set of active nodes of the hypergraph
  IteratorRange<HypernodeIterator> nodes() const {
    ASSERT(_pg);
    return _pg->nodes();
  }

  // ! Returns an iterator over the set of active edges of the hypergraph
  IteratorRange<HyperedgeIterator> edges() const {
    ASSERT(_pg);
    return _pg->edges();
  }

  // ! Returns a range to loop over the incident nets of hypernode u.
  IteratorRange<IncidentNetsIterator> incidentEdges(const HypernodeID u) const {
    ASSERT(_pg);
    return _pg->incidentEdges(u);
  }

  // ! Returns a range to loop over the pins of hyperedge e.
  IteratorRange<IncidenceIterator> pins(const HyperedgeID e) const {
    ASSERT(_pg);
    return _pg->pins(e);
  }

  // ####################### Hypernode Information #######################

  HypernodeWeight nodeWeight(const HypernodeID u) const {
    ASSERT(_pg);
    return _pg->nodeWeight(u);
  }

  HyperedgeID nodeDegree(const HypernodeID u) const {
    ASSERT(_pg);
    return _pg->nodeDegree(u);
  }

  // ####################### Hyperedge Information #######################

  // ! Target of an edge
  HypernodeID edgeTarget(const HyperedgeID e) const {
    return _pg->edgeTarget(e);
  }

  // ! Source of an edge
  HypernodeID edgeSource(const HyperedgeID e) const {
    return _pg->edgeSource(e);
  }

  // ! Returns true, if the edge is selfloop
  bool isSinglePin(const HyperedgeID e) const {
    ASSERT(_pg);
    return _pg->isSinglePin(e);
  }

  // ! Number of pins of an edge
  HypernodeID edgeSize(const HyperedgeID e) const {
    ASSERT(_pg);
    return _pg->edgeSize(e);
  }

  HyperedgeWeight edgeWeight(const HyperedgeID e) const {
    ASSERT(_pg);
    return _pg->edgeWeight(e);
  }

  // ####################### Partition Information #######################

  // ! Changes the block of hypernode u from 'from' to 'to'.
  // ! Move is successful, if it is not violating the balance
  // ! constraint specified by 'max_weight_to'.
  template<typename DeltaFunc>
  bool changeNodePart(const HypernodeID u,
                      const PartitionID from,
                      const PartitionID to,
                      const HypernodeWeight max_weight_to,
                      DeltaFunc&& delta_func) {
    ASSERT(_pg);
    ASSERT(partID(u) == from);
    ASSERT(from != to);

    const HypernodeWeight weight = _pg->nodeWeight(u);
    if (partWeight(to) + weight <= max_weight_to) {
      _part_ids_delta[u] = to;
      _part_weights_delta[to] += weight;
      _part_weights_delta[from] -= weight;

      SynchronizedEdgeUpdate sync_update;
      sync_update.from = from;
      sync_update.to = to;
      sync_update.target_graph = _pg->targetGraph();
      for (const HyperedgeID edge : _pg->incidentEdges(u)) {
        const PartitionID target_part = partID(_pg->edgeTarget(edge));
        sync_update.he = edge;
        sync_update.edge_weight = _pg->edgeWeight(edge);
        sync_update.edge_size = _pg->edgeSize(edge);
        sync_update.pin_count_in_from_part_after = target_part == from ? 1 : 0;
        sync_update.pin_count_in_to_part_after = target_part == to ? 2 : 1;
        delta_func(sync_update);
      }
      return true;
    } else {
      return false;
    }
  }

  bool changeNodePart(const HypernodeID u,
                      const PartitionID from,
                      const PartitionID to,
                      const HypernodeWeight max_weight_to) {
    ASSERT(_pg);
    ASSERT(partID(u) == from);
    ASSERT(from != to);

    const HypernodeWeight weight = _pg->nodeWeight(u);
    if (partWeight(to) + weight <= max_weight_to) {
      _part_ids_delta[u] = to;
      _part_weights_delta[to] += weight;
      _part_weights_delta[from] -= weight;
      return true;
    } else {
      return false;
    }
  }

  // ! Returns the block of hypernode u
  PartitionID partID(const HypernodeID u) const {
    ASSERT(_pg);
    const PartitionID* part_id = _part_ids_delta.get_if_contained(u);
    return part_id ? *part_id : _pg->partID(u);
  }

  // ! Returns if the node is a fixed vertex
  bool isFixed(const HypernodeID u) const {
    ASSERT(_pg);
    return _pg->isFixed(u);
  }

  // ! Returns the total weight of block p
  HypernodeWeight partWeight(const PartitionID p) const {
    ASSERT(_pg);
    ASSERT(p != kInvalidPartition && p < _k);
    return _pg->partWeight(p) + _part_weights_delta[p];
  }

  // ! Returns the number of pins of edge e in block p
  HypernodeID pinCountInPart(const HyperedgeID e, const PartitionID p) const {
    ASSERT(_pg);
    ASSERT(e < _pg->initialNumEdges(), "Hyperedge" << e << "does not exist");
    ASSERT(_pg->edgeIsEnabled(e), "Hyperedge" << e << "is disabled");
    ASSERT(p != kInvalidPartition && p < _k);
    HypernodeID count = 0;
    if (p == partID(edgeSource(e))) {
      count++;
    }
    if (!_pg->isSinglePin(e) && p == partID(edgeTarget(e))) {
      count++;
    }
    return count;
  }

  // ! Returns an iterator over the connectivity set of hyperedge he (not supported)
  IteratorRange<ConnectivitySetIterator> connectivitySet(const HyperedgeID e) const {
    throw UnsupportedOperationException("Not supported for graphs");
    return _dummy_connectivity_set.connectivitySet(e);
  }

  // ! Returns the number of blocks contained in hyperedge he (not supported)
  PartitionID connectivity(const HyperedgeID e) const {
    throw UnsupportedOperationException("Not supported for graphs");
    return _dummy_connectivity_set.connectivity(e);
  }

  // ! Creates a deep copy of the connectivity set of hyperedge he (not supported)
  Bitset& deepCopyOfConnectivitySet(const HyperedgeID he) const {
    throw UnsupportedOperationException("Not supported for graphs");
    return _dummy_connectivity_set.deepCopy(he);
  }

  // ! Clears all deltas applied to the partitioned hypergraph
  void clear() {
    // O(k)
    _part_weights_delta.assign(_k, 0);
    // Constant Time
    _part_ids_delta.clear();
  }

  void dropMemory() {
    if (!_memory_dropped) {
      _memory_dropped = true;
      _part_ids_delta.freeInternalData();
    }
  }

  size_t combinedMemoryConsumption() const {
    return _part_ids_delta.size_in_bytes();
  }

  PartitionID k() const {
    return _k;
  }

  void changeNumberOfBlocks(const PartitionID new_k) {
    if ( new_k > _k ) {
      _part_weights_delta.assign(new_k, 0);
    }
    _k = new_k;
  }

  void memoryConsumption(utils::MemoryTreeNode* parent) const {
    ASSERT(parent);

    utils::MemoryTreeNode* delta_pg_node = parent->addChild("Delta Partitioned Hypergraph");
    utils::MemoryTreeNode* part_weights_node = delta_pg_node->addChild("Delta Part Weights");
    part_weights_node->updateSize(_part_weights_delta.capacity() * sizeof(HypernodeWeight));
    utils::MemoryTreeNode* part_ids_node = delta_pg_node->addChild("Delta Part IDs");
    part_ids_node->updateSize(_part_ids_delta.size_in_bytes());
  }

 private:
  bool _memory_dropped = false;

  // ! Number of blocks
  PartitionID _k;

  // ! Partitioned graph where all deltas are stored relative to
  PartitionedGraph* _pg;

  // ! Delta for block weights
  vec< HypernodeWeight > _part_weights_delta;

  // ! Stores for each locally moved node its new block id
  DynamicFlatMap<HypernodeID, PartitionID> _part_ids_delta;

  // ! Maintain the connectivity set is not supported in the delta partitioned graph.
  // ! We therefore add here a dummy delta connectivity set to implement the same interface
  // ! as the delta partitioned hypergraph
  DummyConnectivitySet _dummy_connectivity_set;
};

} // namespace ds
} // namespace mt_kahypar
