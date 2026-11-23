/*******************************************************************************
 * MIT License
 *
 * This file is part of Mt-KaHyPar.
 *
 * Copyright (C) 2023 Tobias Heuer <tobias.heuer@kit.edu>
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

#include "kahypar-resources/meta/policy_registry.h"

#include "mt-kahypar/partition/context_enum_classes.h"
#include "mt-kahypar/datastructures/hypergraph_common.h"
#include "mt-kahypar/datastructures/array.h"
#include "mt-kahypar/datastructures/sparse_map.h"
#include "mt-kahypar/datastructures/synchronized_edge_update.h"
#include "mt-kahypar/parallel/atomic_wrapper.h"
#include "mt-kahypar/macros.h"
#include "mt-kahypar/utils/range.h"
#include "mt-kahypar/partition/context.h"

namespace mt_kahypar {

// Forward
class DeltaGraphCutGainCache;

/**
 * The gain cache stores the gain values for all possible node moves for the cut metric on plain graphs.
 *
 * For a weighted graph G = (V,E,c,w), the cut metric is defined as follows
 * connectivity(H) := \sum_{e \in cut(E)} w(e).
 *
 * The gain of moving a node u from its current block V_i to a target block V_j can be expressed as follows
 * g(u, V_j) := w(u, V_j) - w(u, V_i) = b(u, V_j) - p(u)
 * where w(u, V') are the weight of all edges that connects node u to block V'.
 * We call b(u, V_j) the benefit term and p(u) the penalty term. Our gain cache stores and maintains these
 * entries for each node and block. Note that p(u) = b(u, V_i).
 * Thus, the gain cache stores k entries per node.
*/
class GraphCutGainCache {

 public:

  static constexpr GainPolicy TYPE = GainPolicy::cut_for_graphs;
  static constexpr bool requires_notification_before_update = false;
  static constexpr bool initializes_gain_cache_entry_after_batch_uncontractions = false;
  static constexpr bool invalidates_entries = false;

  using AdjacentBlocksIterator = IntegerIterator<PartitionID>;

  GraphCutGainCache() :
    _is_initialized(false),
    _k(kInvalidPartition),
    _current_k(kInvalidPartition),
    _gain_cache() { }

  GraphCutGainCache(const Context&) :
    _is_initialized(false),
    _k(kInvalidPartition),
    _current_k(kInvalidPartition),
    _gain_cache() { }

  GraphCutGainCache(const GraphCutGainCache&) = delete;
  GraphCutGainCache & operator= (const GraphCutGainCache &) = delete;

  GraphCutGainCache(GraphCutGainCache&& other) = default;
  GraphCutGainCache & operator= (GraphCutGainCache&& other) = default;

  // ####################### Initialization #######################

  bool isInitialized() const {
    return _is_initialized;
  }

  void reset(HypernodeID num_nodes, PartitionID k, bool run_parallel = true) {
    if ( _is_initialized ) {
      ASSERT(num_nodes * k <= _gain_cache.size());
      _gain_cache.assign(num_nodes * k, CAtomic<HyperedgeWeight>(0), run_parallel);
    }
    _is_initialized = false;
  }

  size_t size() const {
    return _gain_cache.size();
  }

  // ! Initializes all gain cache entries
  template<typename PartitionedGraph>
  void initializeGainCache(const PartitionedGraph& partitioned_graph);

  template<typename PartitionedGraph>
  MT_KAHYPAR_ATTRIBUTE_ALWAYS_INLINE
  void initializeGainCacheEntryForNode(const PartitionedGraph&,
                                       const HypernodeID&) {
    // Do nothing
  }

  // ! Returns whether the block is adjacent to the node
  bool blockIsAdjacent(const HypernodeID, const PartitionID) const {
    return true;
  }

  IteratorRange<AdjacentBlocksIterator> adjacentBlocks(const HypernodeID) const {
    // We do not maintain the adjacent blocks of a node in this gain cache.
    // We therefore return an iterator over all blocks here
    return integer_range(_current_k);
  }

  // ####################### Gain Computation #######################

  // ! Returns the penalty term of node u.
  // ! More formally, p(u) := w(u, partID(u))
  MT_KAHYPAR_ATTRIBUTE_ALWAYS_INLINE
  HyperedgeWeight penaltyTerm(const HypernodeID u,
                              const PartitionID from) const {
    ASSERT(_is_initialized, "Gain cache is not initialized");
    return _gain_cache[incident_weight_index(u, from)].load(std::memory_order_relaxed);
  }

  template<typename PartitionedGraph>
  MT_KAHYPAR_ATTRIBUTE_ALWAYS_INLINE
  void recomputeInvalidTerms(const PartitionedGraph&,
                             const HypernodeID) {
    // Do nothing here (only relevant for hypergraph gain cache)
  }

  // ! Returns the benefit term for moving node u to block to.
  // ! More formally, b(u, V_j) := w(u, V_j)
  MT_KAHYPAR_ATTRIBUTE_ALWAYS_INLINE
  HyperedgeWeight benefitTerm(const HypernodeID u, const PartitionID to) const {
    ASSERT(_is_initialized, "Gain cache is not initialized");
    return _gain_cache[incident_weight_index(u, to)].load(std::memory_order_relaxed);
  }

  // ! Returns the gain of moving node u from its current block to a target block V_j.
  // ! More formally, g(u, V_j) := b(u, V_j) - p(u).
  MT_KAHYPAR_ATTRIBUTE_ALWAYS_INLINE
  HyperedgeWeight gain(const HypernodeID u, const PartitionID from, const PartitionID to) const {
    ASSERT(_is_initialized, "Gain cache is not initialized");
    return benefitTerm(u, to) - penaltyTerm(u, from);
  }

  // ####################### Delta Gain Update #######################

  // ! This function returns true if the corresponding syncronized edge update triggers
  // ! a gain cache update.
  static bool triggersDeltaGainUpdate(const SynchronizedEdgeUpdate& sync_update);

  // ! The partitioned (hyper)graph call this function when its updates its internal
  // ! data structures before calling the delta gain update function. The partitioned
  // ! (hyper)graph holds a lock for the corresponding (hyper)edge when calling this
  // ! function. Thus, it is guaranteed that no other thread will modify the hyperedge.
  template<typename PartitionedHypergraph>
  void notifyBeforeDeltaGainUpdate(const PartitionedHypergraph&, const SynchronizedEdgeUpdate&) {
    // Do nothing
  }

  // ! This functions implements the delta gain updates for the cut metric on plain graphs.
  // ! When moving a node from its current block from to a target block to, we iterate
  // ! over its incident edges and syncronize the move on each edge. After syncronization,
  // ! we call this function to update the gain cache to changes associated with
  // ! corresponding edge.
  template<typename PartitionedGraph>
  void deltaGainUpdate(const PartitionedGraph& partitioned_graph,
                       const SynchronizedEdgeUpdate& sync_update);

  // ####################### Uncontraction #######################

  // ! This function implements the gain cache update after an uncontraction that restores node v in
  // ! an edge he. After the uncontraction the corresponding edge turns from a selfloop to a regular edge.
  template<typename PartitionedGraph>
  void uncontractUpdateAfterRestore(const PartitionedGraph& partitioned_graph,
                                    const HypernodeID u,
                                    const HypernodeID v,
                                    const HyperedgeID he,
                                    const HypernodeID pin_count_in_part_after);

  // ! This function implements the gain cache update after an uncontraction that replaces u with v in
  // ! an edge he. After the uncontraction only node v is part of edge he.
  template<typename PartitionedGraph>
  void uncontractUpdateAfterReplacement(const PartitionedGraph& partitioned_graph,
                                        const HypernodeID u,
                                        const HypernodeID v,
                                        const HyperedgeID he);

  void restoreSinglePinHyperedge(const HypernodeID,
                                 const PartitionID,
                                 const HyperedgeWeight) {
    // Do nothing here (only relevant for hypergraph gain cache)
  }

  // ! This function is called after restoring a net that became identical to another due to a contraction.
  template<typename PartitionedHypergraph>
  void restoreIdenticalHyperedge(const PartitionedHypergraph&,
                                 const HyperedgeID) {
    // Do nothing
  }

  // ! Notifies the gain cache that all uncontractions of the current batch are completed.
  void batchUncontractionsCompleted() {
    // Do nothing
  }

  // ####################### Only for Testing #######################

  template<typename PartitionedGraph>
  MT_KAHYPAR_ATTRIBUTE_ALWAYS_INLINE
  HyperedgeWeight recomputePenaltyTerm(const PartitionedGraph& partitioned_graph,
                                       const HypernodeID u) const {
    PartitionID block_of_u = partitioned_graph.partID(u);
    HyperedgeWeight penalty = 0;
    for (HyperedgeID e : partitioned_graph.incidentEdges(u)) {
      if (!partitioned_graph.isSinglePin(e) &&
          partitioned_graph.partID(partitioned_graph.edgeTarget(e)) == block_of_u) {
        penalty += partitioned_graph.edgeWeight(e);
      }
    }
    return penalty;
  }

  template<typename PartitionedGraph>
  MT_KAHYPAR_ATTRIBUTE_ALWAYS_INLINE
  HyperedgeWeight recomputeBenefitTerm(const PartitionedGraph& partitioned_graph,
                                       const HypernodeID u,
                                       const PartitionID to) const {
    HyperedgeWeight benefit = 0;
    for (HyperedgeID e : partitioned_graph.incidentEdges(u)) {
      if (!partitioned_graph.isSinglePin(e) &&
          partitioned_graph.partID(partitioned_graph.edgeTarget(e)) == to) {
        benefit += partitioned_graph.edgeWeight(e);
      }
    }
    return benefit;
  }

  void changeNumberOfBlocks(const PartitionID new_k) {
    ASSERT(new_k <= _k);
    _current_k = new_k;
  }

  template<typename PartitionedHypergraph>
  bool verifyTrackedAdjacentBlocksOfNodes(const PartitionedHypergraph&) const {
    // Gain cache does not track adjacent blocks of nodes
    return true;
  }

 private:
  friend class DeltaGraphCutGainCache;

  MT_KAHYPAR_ATTRIBUTE_ALWAYS_INLINE
  size_t incident_weight_index(const HypernodeID u, const PartitionID p) const {
    return size_t(u) * _k  + p;
  }

  // ! Allocates the memory required to store the gain cache
  void allocateGainTable(const HypernodeID num_nodes,
                         const PartitionID k) {
    if (_gain_cache.size() == 0 && k != kInvalidPartition) {
      _k = k;
      _current_k = k;
      _gain_cache.resize("Refinement", "incident_weight_in_part", num_nodes * size_t(_k), true);
    }
  }

  // ! Indicate whether or not the gain cache is initialized
  bool _is_initialized;

  // ! Number of blocks
  PartitionID _k;
  PartitionID _current_k;

  // ! Array of size |V| * k, which stores the benefit and penalty terms of each node.
  ds::Array< CAtomic<HyperedgeWeight> > _gain_cache;
};

/**
 * In our FM algorithm, the different local searches perform nodes moves locally not visible for other
 * threads. The delta gain cache stores these local changes relative to the shared
 * gain cache. For example, the penalty term can be computed as follows
 * p'(u) := p(u) + Δp(u)
 * where p(u) is the penalty term stored in the shared gain cache and Δp(u) is the penalty term stored in
 * the delta gain cache after performing some moves locally. To maintain Δp(u) and Δb(u,V_j), we use a hash
 * table that only stores entries affected by a gain cache update.
*/
class DeltaGraphCutGainCache {

  using AdjacentBlocksIterator = typename GraphCutGainCache::AdjacentBlocksIterator;

 public:
  static constexpr bool requires_connectivity_set = false;

  DeltaGraphCutGainCache(const GraphCutGainCache& gain_cache) :
    _gain_cache(gain_cache),
    _incident_weight_in_part_delta() { }

  // ####################### Initialize & Reset #######################

  void initialize(const size_t size) {
    _incident_weight_in_part_delta.initialize(size);
  }

  void clear() {
    _incident_weight_in_part_delta.clear();
  }

  void dropMemory() {
    _incident_weight_in_part_delta.freeInternalData();
  }

  size_t size_in_bytes() const {
    return _incident_weight_in_part_delta.size_in_bytes();
  }

  // ####################### Gain Computation #######################

  // ! Returns whether the block is adjacent to the node
  bool blockIsAdjacent(const HypernodeID hn, const PartitionID block) const {
    return _gain_cache.blockIsAdjacent(hn, block);
  }

  // ! Returns an iterator over the adjacent blocks of a node
  IteratorRange<AdjacentBlocksIterator> adjacentBlocks(const HypernodeID hn) const {
    return _gain_cache.adjacentBlocks(hn);
  }

  // ! Returns the penalty term of node u.
  // ! More formally, p(u) := w(u, partID(u))
  MT_KAHYPAR_ATTRIBUTE_ALWAYS_INLINE
  HyperedgeWeight penaltyTerm(const HypernodeID u,
                              const PartitionID from) const {
    const HyperedgeWeight* penalty_delta =
      _incident_weight_in_part_delta.get_if_contained(
        _gain_cache.incident_weight_index(u, from));
    return _gain_cache.penaltyTerm(u, from) + (penalty_delta ? *penalty_delta : 0);
  }

  // ! Returns the benefit term for moving node u to block to.
  // ! More formally, b(u, V_j) := w(u, V_j)
  MT_KAHYPAR_ATTRIBUTE_ALWAYS_INLINE
  HyperedgeWeight benefitTerm(const HypernodeID u, const PartitionID to) const {
    const HyperedgeWeight* benefit_delta =
      _incident_weight_in_part_delta.get_if_contained(
        _gain_cache.incident_weight_index(u, to));
    return _gain_cache.benefitTerm(u, to) + (benefit_delta ? *benefit_delta : 0);
  }

  // ! Returns the gain of moving node u from its current block to a target block V_j.
  // ! More formally, g(u, V_j) := b(u, V_j) - p(u).
  MT_KAHYPAR_ATTRIBUTE_ALWAYS_INLINE
  HyperedgeWeight gain(const HypernodeID u,
                       const PartitionID from,
                       const PartitionID to ) const {
    return benefitTerm(u, to) - penaltyTerm(u, from);
  }

 // ####################### Delta Gain Update #######################

  template<typename PartitionedGraph>
  MT_KAHYPAR_ATTRIBUTE_ALWAYS_INLINE
  void deltaGainUpdate(const PartitionedGraph& partitioned_graph,
                       const SynchronizedEdgeUpdate& sync_update) {
    const HypernodeID target = partitioned_graph.edgeTarget(sync_update.he);
    const size_t index_in_from_part = _gain_cache.incident_weight_index(target, sync_update.from);
    _incident_weight_in_part_delta[index_in_from_part] -= sync_update.edge_weight;
    const size_t index_in_to_part = _gain_cache.incident_weight_index(target, sync_update.to);
    _incident_weight_in_part_delta[index_in_to_part] += sync_update.edge_weight;
  }


 // ####################### Miscellaneous #######################

  void memoryConsumption(utils::MemoryTreeNode* parent) const {
    ASSERT(parent);
    utils::MemoryTreeNode* gain_cache_delta_node = parent->addChild("Delta Gain Cache");
    gain_cache_delta_node->updateSize(size_in_bytes());
  }

 private:
  const GraphCutGainCache& _gain_cache;

  // ! Stores the delta of each locally touched gain cache entry
  // ! relative to the gain cache in '_phg'
  ds::DynamicFlatMap<size_t, HyperedgeWeight> _incident_weight_in_part_delta;
};

}  // namespace mt_kahypar
