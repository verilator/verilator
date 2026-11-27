/*******************************************************************************
 * MIT License
 *
 * This file is part of Mt-KaHyPar.
 *
 * Copyright (C) 2019 Lars Gottesbüren <lars.gottesbueren@kit.edu>
 * Copyright (C) 2019 Tobias Heuer <tobias.heuer@kit.edu>
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
#include "mt-kahypar/datastructures/synchronized_edge_update.h"
#include "mt-kahypar/parallel/stl/scalable_vector.h"
#include "mt-kahypar/partition/context.h"

namespace mt_kahypar {
namespace ds {

/*!
 * Special hypergraph data structure for the FM algorithm.
 * In order to perform frequent moves on the hypergraph without affecting other
 * local searches one can wrap this hypergraph around a partitioned hypergraph and
 * perform those moves locally on this hypergraph. The changes are not reflected
 * in the global partitioned hypergraph. Instead, the data structure stores deltas
 * relative to the global partitioned hypergraph for each internal member such that
 * by applying those deltas to the original partitioned hypergraph it would reflect the
 * global state of the partitioned hypergraph after all local moves would be applied
 * to it.
 * The rationale behind this is that the majority of local searches to not yield to
 * an improvement and are immediatly reverted. However, applying them directly to global
 * partitioned hypergraph would affect other local searches running concurrently, which build
 * upon that state. This special partitioned hypergraph allows a local search to hide its
 * current search state from other searches in a space efficient manner.
 */
template <typename PartitionedHypergraph = Mandatory,
          bool maintain_connectivity_set = false>
class DeltaPartitionedHypergraph {
 private:
  static constexpr size_t MAP_SIZE_LARGE = 16384;
  static constexpr size_t MAP_SIZE_SMALL = 128;

  using HypernodeIterator = typename PartitionedHypergraph::HypernodeIterator;
  using HyperedgeIterator = typename PartitionedHypergraph::HyperedgeIterator;
  using IncidenceIterator = typename PartitionedHypergraph::IncidenceIterator;
  using IncidentNetsIterator = typename PartitionedHypergraph::IncidentNetsIterator;
  using DeltaConSet = DeltaConnectivitySet<typename PartitionedHypergraph::ConInfo>;
  using ConnectivitySetIterator = typename DeltaConSet::Iterator;

 public:
  static constexpr bool supports_connectivity_set = false;
  static constexpr HyperedgeID HIGH_DEGREE_THRESHOLD = PartitionedHypergraph::HIGH_DEGREE_THRESHOLD;

  DeltaPartitionedHypergraph(const Context& context) :
    _k(context.partition.k),
    _phg(nullptr),
    _part_weights_delta(context.partition.k, 0),
    _part_ids_delta(),
    _pins_in_part_delta(),
    _connectivity_set_delta(context.partition.k) {
      _part_ids_delta.initialize(MAP_SIZE_SMALL);
      _pins_in_part_delta.initialize(MAP_SIZE_LARGE);
    }

  DeltaPartitionedHypergraph(const DeltaPartitionedHypergraph&) = delete;
  DeltaPartitionedHypergraph & operator= (const DeltaPartitionedHypergraph &) = delete;

  DeltaPartitionedHypergraph(DeltaPartitionedHypergraph&& other) = default;
  DeltaPartitionedHypergraph & operator= (DeltaPartitionedHypergraph&& other) = default;

  ~DeltaPartitionedHypergraph() = default;

  void setPartitionedHypergraph(PartitionedHypergraph* phg) {
    _phg = phg;
    _connectivity_set_delta.setConnectivitySet(&phg->getConnectivityInformation());
  }

  // ####################### Mapping ######################

  bool hasTargetGraph() const {
    ASSERT(_phg);
    return _phg->hasTargetGraph();
  }

  const TargetGraph* targetGraph() const {
    ASSERT(_phg);
    return _phg->targetGraph();
  }

  // ####################### Iterators #######################

  // ! Returns an iterator over the set of active nodes of the hypergraph
  IteratorRange<HypernodeIterator> nodes() const {
    ASSERT(_phg);
    return _phg->nodes();
  }

  // ! Returns an iterator over the set of active edges of the hypergraph
  IteratorRange<HyperedgeIterator> edges() const {
    ASSERT(_phg);
    return _phg->edges();
  }

  // ! Returns a range to loop over the incident nets of hypernode u.
  IteratorRange<IncidentNetsIterator> incidentEdges(const HypernodeID u) const {
    ASSERT(_phg);
    return _phg->incidentEdges(u);
  }

  // ! Returns a range to loop over the pins of hyperedge e.
  IteratorRange<IncidenceIterator> pins(const HyperedgeID e) const {
    ASSERT(_phg);
    return _phg->pins(e);
  }

  // ####################### Hypernode Information #######################

  HypernodeWeight nodeWeight(const HypernodeID u) const {
    ASSERT(_phg);
    return _phg->nodeWeight(u);
  }

  HyperedgeID nodeDegree(const HypernodeID u) const {
    ASSERT(_phg);
    return _phg->nodeDegree(u);
  }

  // ####################### Hyperedge Information #######################

  // ! Number of pins of a hyperedge
  HypernodeID edgeSize(const HyperedgeID e) const {
    ASSERT(_phg);
    return _phg->edgeSize(e);
  }

  HyperedgeWeight edgeWeight(const HyperedgeID e) const {
    ASSERT(_phg);
    return _phg->edgeWeight(e);
  }

  // ! Returns true, if the hyperedge contains only a single pin
  bool isSinglePin(const HyperedgeID e) const {
    ASSERT(_phg);
    return _phg->isSinglePin(e);
  }

  // ! Target of an edge
  HypernodeID edgeTarget(const HyperedgeID e) const {
    ASSERT(_phg);
    return _phg->edgeTarget(e);
  }

  // ! Source of an edge
  HypernodeID edgeSource(const HyperedgeID e) const {
    ASSERT(_phg);
    return _phg->edgeSource(e);
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
    ASSERT(_phg);
    assert(partID(u) == from);
    assert(from != to);
    const HypernodeWeight wu = _phg->nodeWeight(u);
    if ( partWeight(to) + wu <= max_weight_to ) {
      _part_ids_delta[u] = to;
      _part_weights_delta[to] += wu;
      _part_weights_delta[from] -= wu;

      SynchronizedEdgeUpdate sync_update;
      sync_update.from = from;
      sync_update.to = to;
      sync_update.target_graph = _phg->targetGraph();
      for ( const HyperedgeID& he : _phg->incidentEdges(u) ) {
        sync_update.he = he;
        sync_update.edge_weight = edgeWeight(he);
        sync_update.edge_size = edgeSize(he);
        sync_update.pin_count_in_from_part_after = decrementPinCountOfBlock(he, from);
        sync_update.pin_count_in_to_part_after = incrementPinCountOfBlock(he, to);
        if constexpr ( maintain_connectivity_set ) {
          updateConnectivitySet(he, sync_update);
          sync_update.connectivity_set_after = &deepCopyOfConnectivitySet(he);
        }
        delta_func(sync_update);
      }
      return true;
    } else {
      return false;
    }
  }

  // curry
  bool changeNodePart(const HypernodeID u,
                      const PartitionID from,
                      const PartitionID to,
                      const HypernodeWeight max_weight_to) {
    return changeNodePart(u, from, to, max_weight_to, NoOpDeltaFunc());
  }

  // ! Returns the block of hypernode u
  PartitionID partID(const HypernodeID u) const {
    ASSERT(_phg);
    const PartitionID* part_id = _part_ids_delta.get_if_contained(u);
    return part_id ? *part_id : _phg->partID(u);
  }

  // ! Returns if the node is a fixed vertex
  bool isFixed(const HypernodeID u) const {
    ASSERT(_phg);
    return _phg->isFixed(u);
  }

  // ! Returns the total weight of block p
  HypernodeWeight partWeight(const PartitionID p) const {
    ASSERT(_phg);
    ASSERT(p != kInvalidPartition && p < _k);
    return _phg->partWeight(p) + _part_weights_delta[p];
  }

  // ! Returns the number of pins of hyperedge e in block p
  HypernodeID pinCountInPart(const HyperedgeID e, const PartitionID p) const {
    ASSERT(_phg);
    ASSERT(p != kInvalidPartition && p < _k);
    const int32_t* pin_count_delta = _pins_in_part_delta.get_if_contained(e * _k + p);
    return std::max(static_cast<int32_t>(_phg->pinCountInPart(e, p)) +
      ( pin_count_delta ? *pin_count_delta : 0 ), 0);
  }

  // ! Returns an iterator over the connectivity set of hyperedge he
  IteratorRange<ConnectivitySetIterator> connectivitySet(const HyperedgeID e) const {
    return _connectivity_set_delta.connectivitySet(e);
  }

  // ! Returns the number of blocks contained in hyperedge he
  PartitionID connectivity(const HyperedgeID e) const {
    return _connectivity_set_delta.connectivity(e);
  }

  // ! Creates a deep copy of the connectivity set of hyperedge he
  Bitset& deepCopyOfConnectivitySet(const HyperedgeID he) const {
    return _connectivity_set_delta.deepCopy(he);
  }

  // ! Clears all deltas applied to the partitioned hypergraph
  void clear() {
    // O(k)
    _part_weights_delta.assign(_k, 0);
    // Constant Time
    _part_ids_delta.clear();
    _pins_in_part_delta.clear();
    _connectivity_set_delta.reset();
  }

  void dropMemory() {
    if (!_memory_dropped) {
      _memory_dropped = true;
      _part_ids_delta.freeInternalData();
      _pins_in_part_delta.freeInternalData();
      _connectivity_set_delta.freeInternalData();
    }
  }

  size_t combinedMemoryConsumption() const {
    return _pins_in_part_delta.size_in_bytes()
           + _part_ids_delta.size_in_bytes()
           + _connectivity_set_delta.size_in_bytes();
  }

  PartitionID k() const {
    return _k;
  }

  void changeNumberOfBlocks(const PartitionID new_k) {
    if ( new_k > _k ) {
      _part_weights_delta.assign(new_k, 0);
    }
    _connectivity_set_delta.setNumberOfBlocks(new_k);
    _k = new_k;
  }

  void memoryConsumption(utils::MemoryTreeNode* parent) const {
    ASSERT(parent);

    utils::MemoryTreeNode* delta_phg_node = parent->addChild("Delta Partitioned Hypergraph");
    utils::MemoryTreeNode* part_weights_node = delta_phg_node->addChild("Delta Part Weights");
    part_weights_node->updateSize(_part_weights_delta.capacity() * sizeof(HypernodeWeight));
    utils::MemoryTreeNode* part_ids_node = delta_phg_node->addChild("Delta Part IDs");
    part_ids_node->updateSize(_part_ids_delta.size_in_bytes());
    utils::MemoryTreeNode* pins_in_part_node = delta_phg_node->addChild("Delta Pins In Part");
    pins_in_part_node->updateSize(_pins_in_part_delta.size_in_bytes());
  }

 private:
  MT_KAHYPAR_ATTRIBUTE_ALWAYS_INLINE
  HypernodeID decrementPinCountOfBlock(const HyperedgeID e, const PartitionID p) {
    return std::max(static_cast<int32_t>(
      _phg->pinCountInPart(e, p)) + --_pins_in_part_delta[e * _k + p], static_cast<int32_t>(0));
  }

  MT_KAHYPAR_ATTRIBUTE_ALWAYS_INLINE
  HypernodeID incrementPinCountOfBlock(const HyperedgeID e, const PartitionID p) {
    return std::max(static_cast<int32_t>(
      _phg->pinCountInPart(e, p)) + ++_pins_in_part_delta[e * _k + p], static_cast<int32_t>(0));
  }

  MT_KAHYPAR_ATTRIBUTE_ALWAYS_INLINE
  void updateConnectivitySet(const HyperedgeID e,
                             const SynchronizedEdgeUpdate& sync_update) {
    unused(e);
    if ( sync_update.pin_count_in_from_part_after == 0 ) {
      _connectivity_set_delta.remove(sync_update.he, sync_update.from);
    }
    if ( sync_update.pin_count_in_to_part_after == 1 ) {
      _connectivity_set_delta.add(sync_update.he, sync_update.to);
    }
  }

  bool _memory_dropped = false;

  // ! Number of blocks
  PartitionID _k;

  // ! Partitioned hypergraph where all deltas are stored relative to
  PartitionedHypergraph* _phg;

  // ! Delta for block weights
  vec< HypernodeWeight > _part_weights_delta;

  // ! Stores for each locally moved node, its new block id
  DynamicFlatMap<HypernodeID, PartitionID> _part_ids_delta;

  // ! Stores the delta of each locally touched pin count entry
  // ! relative to the _pins_in_part member in '_phg'
  DynamicFlatMap<size_t, int32_t> _pins_in_part_delta;

  // ! Stores the connectivity set relative to the connectivity set
  // ! in the shared partition
  DeltaConSet _connectivity_set_delta;
};

} // namespace ds
} // namespace mt_kahypar
