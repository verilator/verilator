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

#include <algorithm>

#include "kahypar-resources/meta/policy_registry.h"

#include <tbb/parallel_invoke.h>
#include <tbb/concurrent_vector.h>

#include "mt-kahypar/partition/context_enum_classes.h"
#include "mt-kahypar/partition/context.h"
#include "mt-kahypar/partition/mapping/target_graph.h"
#include "mt-kahypar/datastructures/hypergraph_common.h"
#include "mt-kahypar/datastructures/array.h"
#include "mt-kahypar/datastructures/sparse_map.h"
#include "mt-kahypar/datastructures/static_bitset.h"
#include "mt-kahypar/datastructures/connectivity_set.h"
#include "mt-kahypar/datastructures/delta_connectivity_set.h"
#include "mt-kahypar/datastructures/synchronized_edge_update.h"
#include "mt-kahypar/parallel/atomic_wrapper.h"
#include "mt-kahypar/macros.h"
#include "mt-kahypar/utils/range.h"

namespace mt_kahypar {

/**
 * The gain cache stores the gain values for all possible node moves for the steiner tree metric metric on graphs.
 *
 * The mapping problem asks for a mapping Π: V -> V_p of the node set V of a weighted graph G = (V,E,c,w)
 * onto a target graph P = (V_P, E_P) such that the following objective function is minimized:
 * steiner_tree(G, P, Π) := sum_{{u,v} \in E} dist_P(Π[u],Π[v]) * w(u,v)
 * Here, dist_P(Π[u],Π[v]) is shortest path connecting block Π[u] and Π[v] in the target graph.
 *
 * The gain of moving a node u from its current block V_i to a target block V_j can be expressed as follows:
 * g(u,V_j) := Ψ(u,Π[u]) - Ψ(u,V_j) with Ψ(u,V') := \sum_{{u,v} \in E} dist_P(V',Π[v]) * w(u,v)
 * This gain cache implementation maintains the Ψ(u,V') terms for all nodes and their adjacent blocks.
 * Thus, the gain cache stores and maintains at most k entries per node where k := |V_P|.
*/
class GraphSteinerTreeGainCache {

  static constexpr HyperedgeID HIGH_DEGREE_THRESHOLD = ID(100000);

  using AdjacentBlocksIterator = IteratorRange<typename ds::ConnectivitySets::Iterator>;

 public:
  static_assert(sizeof(PartitionID) == 4 && sizeof(uint64_t) == 8);

  struct EdgeState {
    EdgeState() :
      is_valid(0),
      version(0),
      update_version(0),
      blocks_of_nodes(0) {
      updateBlocks(kInvalidPartition, kInvalidPartition, 0);
    }

    void updateBlocks(const PartitionID source_block,
                      const PartitionID target_block,
                      const uint32_t valid_threshold) {
      blocks_of_nodes = static_cast<uint64_t>(source_block) << 32 | static_cast<uint64_t>(target_block);
      is_valid = valid_threshold;
    }

    PartitionID sourceBlock(const uint32_t valid_threshold) const {
      return is_valid == valid_threshold ? blocks_of_nodes >> 32 : kInvalidPartition;
    }

    PartitionID targetBlock(const uint32_t valid_threshold) const {
      return is_valid == valid_threshold ? blocks_of_nodes & (( UL(1) << 32 ) - 1) : kInvalidPartition;
    }

    uint32_t is_valid;
    CAtomic<uint32_t> version;
    CAtomic<uint32_t> update_version;
    uint64_t blocks_of_nodes;
  };

  static constexpr GainPolicy TYPE = GainPolicy::steiner_tree_for_graphs;
  static constexpr bool requires_notification_before_update = true;
  static constexpr bool initializes_gain_cache_entry_after_batch_uncontractions = true;
  static constexpr bool invalidates_entries = false;

  GraphSteinerTreeGainCache() :
    _is_initialized(false),
    _k(kInvalidPartition),
    _gain_cache(),
    _ets_benefit_aggregator([&] { return initializeBenefitAggregator(); }),
    _num_incident_edges_of_block(),
    _adjacent_blocks(),
    _edge_state(),
    _uncontraction_version(0),
    _ets_version() { }

  GraphSteinerTreeGainCache(const Context&) :
    _is_initialized(false),
    _k(kInvalidPartition),
    _gain_cache(),
    _ets_benefit_aggregator([&] { return initializeBenefitAggregator(); }),
    _num_incident_edges_of_block(),
    _adjacent_blocks(),
    _edge_state(),
    _uncontraction_version(0),
    _ets_version() { }

  GraphSteinerTreeGainCache(const GraphSteinerTreeGainCache&) = delete;
  GraphSteinerTreeGainCache & operator= (const GraphSteinerTreeGainCache &) = delete;

  GraphSteinerTreeGainCache(GraphSteinerTreeGainCache&& other) = default;
  GraphSteinerTreeGainCache & operator= (GraphSteinerTreeGainCache&& other) = default;

  // ####################### Initialization #######################

  bool isInitialized() const {
    return _is_initialized;
  }

  void reset(HypernodeID /*num_nodes*/, PartitionID /*k*/, const bool run_parallel = true) {
    unused(run_parallel);
    _is_initialized = false;
  }

  size_t size() const {
    return _gain_cache.size();
  }

  // ! Initializes all gain cache entries
  template<typename PartitionedHypergraph>
  void initializeGainCache(const PartitionedHypergraph& partitioned_hg);

  // ! Initializes the gain cache entry for a node
  template<typename PartitionedHypergraph>
  void initializeGainCacheEntryForNode(const PartitionedHypergraph& partitioned_hg,
                                       const HypernodeID hn);

  // ! Returns whether the block is adjacent to the node
  bool blockIsAdjacent(const HypernodeID hn, const PartitionID block) const {
    return _adjacent_blocks.contains(hn, block);
  }

  // ! Returns an iterator over the adjacent blocks of a node
  AdjacentBlocksIterator adjacentBlocks(const HypernodeID hn) const {
    return _adjacent_blocks.connectivitySet(hn);
  }

  // ####################### Gain Computation #######################

  // ! Returns the penalty term p(u) := -Ψ(u,Π[u]) of node u.
  MT_KAHYPAR_ATTRIBUTE_ALWAYS_INLINE
  HyperedgeWeight penaltyTerm(const HypernodeID u, const PartitionID from) const {
    ASSERT(_is_initialized, "Gain cache is not initialized");
    return _gain_cache[gain_entry_index(u, from)].load(std::memory_order_relaxed);
  }

  // ! Recomputes all gain cache entries for node u
  template<typename PartitionedHypergraph>
  MT_KAHYPAR_ATTRIBUTE_ALWAYS_INLINE
  void recomputeInvalidTerms(const PartitionedHypergraph&,
                             const HypernodeID) {
    // Do nothing
  }

  // ! Returns the benefit term b(u, V_j) := -Ψ(u,V_j) of node u.
  MT_KAHYPAR_ATTRIBUTE_ALWAYS_INLINE
  HyperedgeWeight benefitTerm(const HypernodeID u, const PartitionID to) const {
    ASSERT(_is_initialized, "Gain cache is not initialized");
    return _gain_cache[gain_entry_index(u, to)].load(std::memory_order_relaxed);
  }

  // ! Returns the gain value g(u,V_j) = b(u,V_j) - p(u) for moving node u to block to.
  MT_KAHYPAR_ATTRIBUTE_ALWAYS_INLINE
  HyperedgeWeight gain(const HypernodeID u,
                       const PartitionID from,
                       const PartitionID to ) const {
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
  void notifyBeforeDeltaGainUpdate(const PartitionedHypergraph& partitioned_hg,
                                   const SynchronizedEdgeUpdate& sync_update);


  // ! This functions implements the delta gain updates for the steiner tree metric.
  // ! When moving a node from its current block to a target block, we iterate
  // ! over its incident hyperedges and update their pin count values. After each pin count
  // ! update, we call this function to update the gain cache to changes associated with
  // ! corresponding hyperedge.
  template<typename PartitionedHypergraph>
  void deltaGainUpdate(const PartitionedHypergraph& partitioned_hg,
                       const SynchronizedEdgeUpdate& sync_update);

  // ####################### Uncontraction #######################

  // ! This function implements the gain cache update after an uncontraction that restores node v in
  // ! edge he. The uncontraction transforms the edge from a selfloop to a regular edge.
  template<typename PartitionedHypergraph>
  void uncontractUpdateAfterRestore(const PartitionedHypergraph& partitioned_hg,
                                    const HypernodeID u,
                                    const HypernodeID v,
                                    const HyperedgeID he,
                                    const HypernodeID pin_count_in_part_after);

  // ! This function implements the gain cache update after an uncontraction that replaces u with v in
  // ! edge he. After the uncontraction only node v is contained in edge he.
  template<typename PartitionedHypergraph>
  void uncontractUpdateAfterReplacement(const PartitionedHypergraph& partitioned_hg,
                                        const HypernodeID u,
                                        const HypernodeID v,
                                        const HyperedgeID he);

  // ! This function is called after restoring a selfloop. The function assumes that
  // ! u is the only pin of the corresponding edge, while block_of_u is its corresponding block ID.
  void restoreSinglePinHyperedge(const HypernodeID u,
                                 const PartitionID block_of_u,
                                 const HyperedgeWeight weight_of_he);

  // ! This function is called after restoring a net that became identical to another due to a contraction.
  template<typename PartitionedHypergraph>
  void restoreIdenticalHyperedge(const PartitionedHypergraph&,
                                 const HyperedgeID);

  // ! Notifies the gain cache that all uncontractions of the current batch are completed.
  void batchUncontractionsCompleted() {
    ++_uncontraction_version;
  }

  // ####################### Only for Testing #######################

  template<typename PartitionedHypergraph>
  MT_KAHYPAR_ATTRIBUTE_ALWAYS_INLINE
  HyperedgeWeight recomputePenaltyTerm(const PartitionedHypergraph& partitioned_hg,
                                       const HypernodeID u) const {
    ASSERT(partitioned_hg.hasTargetGraph());
    HyperedgeWeight gain = 0;
    const TargetGraph& target_graph = *partitioned_hg.targetGraph();
    const PartitionID from = partitioned_hg.partID(u);
    for ( const HyperedgeID& e : partitioned_hg.incidentEdges(u) ) {
      if ( !partitioned_hg.isSinglePin(e) ) {
        const PartitionID block_of_target = partitioned_hg.partID(partitioned_hg.edgeTarget(e));
        gain -= target_graph.distance(from, block_of_target) * partitioned_hg.edgeWeight(e);
      }
    }
    return gain;
  }

  template<typename PartitionedHypergraph>
  MT_KAHYPAR_ATTRIBUTE_ALWAYS_INLINE
  HyperedgeWeight recomputeBenefitTerm(const PartitionedHypergraph& partitioned_hg,
                                       const HypernodeID u,
                                       const PartitionID to) const {
    ASSERT(partitioned_hg.hasTargetGraph());
    HyperedgeWeight gain = 0;
    const TargetGraph& target_graph = *partitioned_hg.targetGraph();
    for ( const HyperedgeID& e : partitioned_hg.incidentEdges(u) ) {
      if ( !partitioned_hg.isSinglePin(e) ) {
        const PartitionID block_of_target = partitioned_hg.partID(partitioned_hg.edgeTarget(e));
        gain -= target_graph.distance(to, block_of_target) * partitioned_hg.edgeWeight(e);
      }
    }
    return gain;
  }

  void changeNumberOfBlocks(const PartitionID new_k) {
    ASSERT(new_k <= _k);
    unused(new_k);
    // Do nothing
  }

  template<typename PartitionedHypergraph>
  bool verifyTrackedAdjacentBlocksOfNodes(const PartitionedHypergraph& partitioned_hg) const;

 private:
  friend class GraphDeltaSteinerTreeGainCache;

  MT_KAHYPAR_ATTRIBUTE_ALWAYS_INLINE
  size_t gain_entry_index(const HypernodeID u, const PartitionID p) const {
    return size_t(u) * _k + p;
  }

  // ! Allocates the memory required to store the gain cache
  void allocateGainTable(const HypernodeID num_nodes,
                         const HyperedgeID num_edges,
                         const PartitionID k) {
    if (_gain_cache.size() == 0 && k != kInvalidPartition) {
      _k = k;
      tbb::parallel_invoke([&] {
        _gain_cache.resize(
          "Refinement", "gain_cache", num_nodes * _k, true);
      }, [&] {
        _num_incident_edges_of_block.resize(
          "Refinement", "num_incident_edges_of_block", num_nodes * _k, true);
      }, [&] {
        _adjacent_blocks = ds::ConnectivitySets(num_nodes, k, true);
      }, [&] {
        _edge_state.assign(num_edges, EdgeState());
      });
    }
  }

  // ! Initializes the adjacent blocks of all nodes
  template<typename PartitionedHypergraph>
  void initializeAdjacentBlocks(const PartitionedHypergraph& partitioned_hg);

    // ! Initializes the adjacent blocks of for a node
  template<typename PartitionedHypergraph>
  void initializeAdjacentBlocksOfNode(const PartitionedHypergraph& partitioned_hg,
                                      const HypernodeID hn);

  // ! Updates the adjacent blocks of a node based on a synronized hyperedge update
  template<typename PartitionedHypergraph>
  void updateAdjacentBlocks(const PartitionedHypergraph& partitioned_hg,
                            const SynchronizedEdgeUpdate& sync_update);

  // ! Increments the number of incident edges of node u that contains pins of block to.
  // ! If the value increases to one, we add the block to the connectivity set of the node
  // ! u and initialize the gain cache entry for moving u to that block.
  HyperedgeID incrementIncidentEdges(const HypernodeID u, const PartitionID to);

  // ! Decrements the number of incident edges of node u that contains pins of block to
  // ! If the value decreases to zero, we remove the block from the connectivity set of the node.
  HyperedgeID decrementIncidentEdges(const HypernodeID u, const PartitionID to);

  // ! Initializes the benefit and penalty terms for a node u
  template<typename PartitionedHypergraph>
  void initializeGainCacheEntryForNode(const PartitionedHypergraph& partitioned_hg,
                                       const HypernodeID u,
                                       vec<Gain>& benefit_aggregator);

  // ! Initializes the gain cache entry of moving u to block 'to'. The function is
  // ! thread-safe, meaning that it supports correct initialization while simultanously
  // ! performing gain cache updates.
  template<typename PartitionedHypergraph>
  void initializeGainCacheEntry(const PartitionedHypergraph& partitioned_hg,
                                const HypernodeID hn,
                                const PartitionID to,
                                ds::Array<SpinLock>& edge_locks);

  vec<Gain> initializeBenefitAggregator() const {
    return vec<Gain>(_k, 0);
  }

  // ! Indicate whether or not the gain cache is initialized
  bool _is_initialized;

  // ! Number of blocks
  PartitionID _k;

  // ! Array of size |V| * (k + 1), which stores the benefit and penalty terms of each node.
  ds::Array< CAtomic<HyperedgeWeight> > _gain_cache;

  // ! Thread-local for initializing gain cache entries
  tbb::enumerable_thread_specific<vec<Gain>> _ets_benefit_aggregator;

  // ! This array stores the number of incident hyperedges that contains
  // ! pins of a particular block for each node.
  ds::Array< CAtomic<HyperedgeID> > _num_incident_edges_of_block;

  // ! Stores the adjacent blocks of a node
  ds::ConnectivitySets _adjacent_blocks;

  // ! This array stores a version ID for each hyperedge. The partitioned hypergraph
  // ! increments the version for a hyperedge before it updates it internal data structure
  // ! (see notifyBeforeDeltaGainUpdate(...)). This can be use when initialize a new gain cache entries, while
  // ! other threads perform concurrent moves on the data structure.
  vec<EdgeState> _edge_state;

  // ! After calling batchUncontractionsCompleted(), we increment this counter marking all
  // entries in _edge_state with a version < _uncontraction_version as invalid.
  uint32_t _uncontraction_version;

  // ! Array to store version IDs when we lazily initialize a gain cache entry
  tbb::enumerable_thread_specific<vec<uint32_t>> _ets_version;
};

/**
 * In our FM algorithm, the different local searches perform nodes moves locally not visible for other
 * threads. The delta gain cache stores these local changes relative to the shared
 * gain cache. For example, the gain can be computed as follows
 * g'(u,V') := g(u,V') + Δg(u,V')
 * where g(u,V') is the gain stored in the shared gain cache and Δg(u,V') is the gain stored in
 * the delta gain cache after performing some moves locally. To maintain Δg(u,V'), we use a hash
 * table that only stores entries affected by a gain cache update.
*/
class GraphDeltaSteinerTreeGainCache {

  using DeltaAdjacentBlocks = ds::DeltaConnectivitySet<ds::ConnectivitySets>;
  using AdjacentBlocksIterator = typename DeltaAdjacentBlocks::Iterator;

 public:
  static constexpr bool requires_connectivity_set = true;

  GraphDeltaSteinerTreeGainCache(const GraphSteinerTreeGainCache& gain_cache) :
    _gain_cache(gain_cache),
    _gain_cache_delta(),
    _invalid_gain_cache_entry(),
    _num_incident_edges_delta(),
    _adjacent_blocks_delta(gain_cache._k) {
    _adjacent_blocks_delta.setConnectivitySet(&_gain_cache._adjacent_blocks);
  }

  // ####################### Initialize & Reset #######################

  void initialize(const size_t size) {
    _adjacent_blocks_delta.setNumberOfBlocks(_gain_cache._k);
    _gain_cache_delta.initialize(size);
    _invalid_gain_cache_entry.initialize(size);
    _num_incident_edges_delta.initialize(size);
  }

  void clear() {
    _gain_cache_delta.clear();
    _invalid_gain_cache_entry.clear();
    _num_incident_edges_delta.clear();
    _adjacent_blocks_delta.reset();
  }

  void dropMemory() {
    _gain_cache_delta.freeInternalData();
    _invalid_gain_cache_entry.freeInternalData();
    _num_incident_edges_delta.freeInternalData();
    _adjacent_blocks_delta.freeInternalData();
  }

  size_t size_in_bytes() const {
    return _gain_cache_delta.size_in_bytes() +
     _invalid_gain_cache_entry.size_in_bytes() +
     _num_incident_edges_delta.size_in_bytes() +
     _adjacent_blocks_delta.size_in_bytes();
  }

  // ####################### Gain Computation #######################

  // ! Returns whether the block is adjacent to the node
  bool blockIsAdjacent(const HypernodeID hn, const PartitionID block) const {
    return _adjacent_blocks_delta.contains(hn, block);
  }

  // ! Returns an iterator over the adjacent blocks of a node
  IteratorRange<AdjacentBlocksIterator> adjacentBlocks(const HypernodeID hn) const {
    return _adjacent_blocks_delta.connectivitySet(hn);
  }

  // ! Returns the penalty term p(u) := -Ψ(u,Π[u]) of node u.
  MT_KAHYPAR_ATTRIBUTE_ALWAYS_INLINE
  HyperedgeWeight penaltyTerm(const HypernodeID u,
                              const PartitionID from) const {
    return benefitTerm(u, from);
  }

  // ! Returns the benefit term b(u, V_j) := -Ψ(u,V_j) of node u.
  MT_KAHYPAR_ATTRIBUTE_ALWAYS_INLINE
  HyperedgeWeight benefitTerm(const HypernodeID u,
                              const PartitionID to) const {
    ASSERT(to != kInvalidPartition && to < _gain_cache._k);
    const bool use_benefit_term_from_shared_gain_cache =
      !_invalid_gain_cache_entry.contains(_gain_cache.gain_entry_index(u, to)) &&
      _gain_cache._adjacent_blocks.contains(u, to);
    const HyperedgeWeight benefit_term =
      use_benefit_term_from_shared_gain_cache * _gain_cache.benefitTerm(u, to);
    const HyperedgeWeight* benefit_delta =
      _gain_cache_delta.get_if_contained(_gain_cache.gain_entry_index(u, to));
    return benefit_term + ( benefit_delta ? *benefit_delta : 0 );
  }

  // ! Returns the gain value g(u,V_j) = b(u,V_j) - p(u) for moving node u to block to.
  MT_KAHYPAR_ATTRIBUTE_ALWAYS_INLINE
  HyperedgeWeight gain(const HypernodeID u,
                       const PartitionID from,
                       const PartitionID to ) const {
    return benefitTerm(u, to) - penaltyTerm(u, from);
  }

 // ####################### Delta Gain Update #######################

  template<typename PartitionedHypergraph>
  MT_KAHYPAR_ATTRIBUTE_ALWAYS_INLINE
  void deltaGainUpdate(const PartitionedHypergraph& partitioned_hg,
                       const SynchronizedEdgeUpdate& sync_update) {
    ASSERT(sync_update.target_graph);

    const HyperedgeID he = sync_update.he;
    if ( !partitioned_hg.isSinglePin(he) ) {
      const PartitionID from = sync_update.from;
      const PartitionID to = sync_update.to;
      const HyperedgeWeight edge_weight = sync_update.edge_weight;
      const TargetGraph& target_graph = *sync_update.target_graph;

      const HypernodeID v = partitioned_hg.edgeTarget(he);
      for ( const PartitionID& target : adjacentBlocks(v) ) {
        const HyperedgeWeight delta = ( target_graph.distance(from, target) -
          target_graph.distance(to, target) ) * edge_weight ;
        _gain_cache_delta[_gain_cache.gain_entry_index(v, target)] += delta;
      }

      // We update the adjacent blocks of nodes affected by this gain cache update
      // which will then trigger initialization of gain entries if a node becomes adjacent
      // to a new block.
      updateAdjacentBlocks(partitioned_hg, sync_update);
    }
  }

 // ####################### Miscellaneous #######################

  void memoryConsumption(utils::MemoryTreeNode* parent) const {
    ASSERT(parent);
    utils::MemoryTreeNode* gain_cache_delta_node = parent->addChild("Delta Gain Cache");
    gain_cache_delta_node->updateSize(size_in_bytes());
  }

 private:
  // ! Updates the adjacent blocks of a node based on a synronized hyperedge update
  template<typename PartitionedHypergraph>
  void updateAdjacentBlocks(const PartitionedHypergraph& partitioned_hg,
                            const SynchronizedEdgeUpdate& sync_update) {
    if ( sync_update.pin_count_in_from_part_after == 0 ) {
      for ( const HypernodeID& pin : partitioned_hg.pins(sync_update.he) ) {
        decrementIncidentEdges(pin, sync_update.from);
      }
    }
    if ( sync_update.pin_count_in_to_part_after == 1 ) {
      for ( const HypernodeID& pin : partitioned_hg.pins(sync_update.he) ) {
        const HyperedgeID incident_edges_after = incrementIncidentEdges(pin, sync_update.to);
        if ( incident_edges_after == 1 ) {
          _invalid_gain_cache_entry[_gain_cache.gain_entry_index(pin, sync_update.to)] = true;
          initializeGainCacheEntry(partitioned_hg, pin, sync_update.to);
        }
      }
    }
  }

  // ! Decrements the number of incident edges of node u that contains pins of block to
  // ! If the value decreases to zero, we remove the block from the connectivity set of the node
  HypernodeID decrementIncidentEdges(const HypernodeID hn, const PartitionID to) {
    const HypernodeID shared_incident_count =
      _gain_cache._num_incident_edges_of_block[_gain_cache.gain_entry_index(hn, to)];
    const HypernodeID thread_local_incident_count_after =
      --_num_incident_edges_delta[_gain_cache.gain_entry_index(hn, to)];
    if ( shared_incident_count + thread_local_incident_count_after == 0 ) {
      _adjacent_blocks_delta.remove(hn, to);
    }
    return shared_incident_count + thread_local_incident_count_after;
  }

  // ! Increments the number of incident edges of node u that contains pins of block to.
  // ! If the value increases to one, we add the block to the connectivity set of the node
  // ! u and initialize the gain cache entry for moving u to that block.
  HypernodeID incrementIncidentEdges(const HypernodeID hn, const PartitionID to) {
    const HypernodeID shared_incident_count =
      _gain_cache._num_incident_edges_of_block[_gain_cache.gain_entry_index(hn, to)];
    const HypernodeID thread_local_incident_count_after =
      ++_num_incident_edges_delta[_gain_cache.gain_entry_index(hn, to)];
    if ( shared_incident_count + thread_local_incident_count_after == 1 ) {
      _adjacent_blocks_delta.add(hn, to);
    }
    return shared_incident_count + thread_local_incident_count_after;
  }

  // ! Initializes a gain cache entry
  template<typename PartitionedHypergraph>
  void initializeGainCacheEntry(const PartitionedHypergraph& partitioned_hg,
                                const HypernodeID u,
                                const PartitionID to) {
    ASSERT(partitioned_hg.hasTargetGraph());
    const TargetGraph& target_graph = *partitioned_hg.targetGraph();
    HyperedgeWeight gain = 0;
    for ( const HyperedgeID& he : partitioned_hg.incidentEdges(u) ) {
      ASSERT(partitioned_hg.edgeSource(he) == u);
      const HypernodeID v = partitioned_hg.edgeTarget(he);
      const PartitionID block_of_v = partitioned_hg.partID(v);
      gain -= target_graph.distance(to, block_of_v) * partitioned_hg.edgeWeight(he);
    }
    _gain_cache_delta[_gain_cache.gain_entry_index(u, to)] = gain;
  }

  const GraphSteinerTreeGainCache& _gain_cache;

  // ! Stores the delta of each locally touched gain cache entry
  // ! relative to the shared gain cache
  ds::DynamicFlatMap<size_t, HyperedgeWeight> _gain_cache_delta;

  // ! If we initialize a gain cache entry locally, we mark that entry
  // ! as invalid such that we do not access the shared gain cache when
  // ! we request the gain cache entry
  ds::DynamicFlatMap<size_t, bool> _invalid_gain_cache_entry;

  // ! Stores the delta of the number of incident edges for each block and node
  ds::DynamicFlatMap<size_t, int32_t> _num_incident_edges_delta;

  // ! Stores the adjacent blocks of each node relative to the
  // ! adjacent blocks in the shared gain cache
  DeltaAdjacentBlocks _adjacent_blocks_delta;
};

}  // namespace mt_kahypar
