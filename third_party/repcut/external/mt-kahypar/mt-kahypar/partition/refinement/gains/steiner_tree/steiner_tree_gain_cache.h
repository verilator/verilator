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
 * The gain cache stores the gain values for all possible node moves for the steiner tree metric.
 *
 * The mapping problem asks for a mapping Π: V -> V_p of the node set V of a weighted hypergraph H = (V,E,c,w)
 * onto a target graph P = (V_P, E_P) such that the following objective function is minimized:
 * steiner_tree(H, P, Π) := sum_{e \in E} dist_P(Λ(e)) * w(e)
 * Here, dist_P(Λ(e)) is shortest connections between all blocks Λ(e) contained in a hyperedge e using only edges
 * of the target graph. Computing dist_P(Λ(e)) reverts to the steiner tree problem which is an NP-hard problem.
 * However, we precompute all steiner trees up to a certain size and for larger connectivity sets Λ(e), we compute
 * a 2-approximation.
 *
 * The gain of moving a node u from its current block V_i to a target block V_j can be expressed as follows:
 * g(u,V_j) := sum_{e \in I(u): Φ(e,V_i) = 1 and Φ(e, V_j) > 0} Δdist_P(e, Λ(e)\{V_i}) * w(e) +
 *             sum_{e \in I(u): Φ(e,V_i) = 1 and Φ(e, V_j) = 0} Δdist_P(e, Λ(e)\{V_i} u {V_j}) * w(e) +
 *             sum_{e \in I(u): Φ(e,V_i) > 1 and Φ(e, V_j) = 0} Δdist_P(e, Λ(e) u {V_j}) * w(e)
 * For a set of blocks A, we define Δdist_P(e, A) := (dist_P(Λ(e)) - dist_P(A)). Moreover, Φ(e,V') is the number
 * of pins contained in hyperedge e which are also part of block V'. More formally, Φ(e,V') := |e n V'|.
 *
 * This gain cache implementation maintains the gain values g(u,V_j) for all nodes and their adjacent blocks.
 * Thus, the gain cache stores and maintains at most k entries per node where k := |V_P|.
*/
class SteinerTreeGainCache {

  static constexpr HyperedgeID HIGH_DEGREE_THRESHOLD = ID(100000);

  using AdjacentBlocksIterator = IteratorRange<typename ds::ConnectivitySets::Iterator>;

 public:
  struct HyperedgeState {
    HyperedgeState() :
      version(0),
      update_version(0) { }

    CAtomic<uint32_t> version;
    CAtomic<uint32_t> update_version;
  };

  static constexpr GainPolicy TYPE = GainPolicy::steiner_tree;
  static constexpr bool requires_notification_before_update = true;
  static constexpr bool initializes_gain_cache_entry_after_batch_uncontractions = true;
  static constexpr bool invalidates_entries = true;

  SteinerTreeGainCache() :
    _is_initialized(false),
    _k(kInvalidPartition),
    _gain_cache(),
    _ets_benefit_aggregator([&] { return initializeBenefitAggregator(); }),
    _num_incident_edges_of_block(),
    _adjacent_blocks(),
    _version(),
    _ets_version(),
    _large_he_threshold(std::numeric_limits<HypernodeID>::max()) { }

  SteinerTreeGainCache(const Context& context) :
    _is_initialized(false),
    _k(kInvalidPartition),
    _gain_cache(),
    _ets_benefit_aggregator([&] { return initializeBenefitAggregator(); }),
    _num_incident_edges_of_block(),
    _adjacent_blocks(),
    _version(),
    _ets_version(),
    _large_he_threshold(context.mapping.large_he_threshold) { }

  SteinerTreeGainCache(const SteinerTreeGainCache&) = delete;
  SteinerTreeGainCache & operator= (const SteinerTreeGainCache &) = delete;

  SteinerTreeGainCache(SteinerTreeGainCache&& other) = default;
  SteinerTreeGainCache & operator= (SteinerTreeGainCache&& other) = default;

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

  // ! Returns the penalty term of node u.
  // ! Note that the steiner tree gain cache does not maintain a
  // ! penalty term and returns zero in this case.
  MT_KAHYPAR_ATTRIBUTE_ALWAYS_INLINE
  HyperedgeWeight penaltyTerm(const HypernodeID,
                              const PartitionID) const {
    ASSERT(_is_initialized, "Gain cache is not initialized");
    return 0;
  }

  // ! Recomputes all gain cache entries for node u
  template<typename PartitionedHypergraph>
  MT_KAHYPAR_ATTRIBUTE_ALWAYS_INLINE
  void recomputeInvalidTerms(const PartitionedHypergraph& partitioned_hg,
                             const HypernodeID u) {
    vec<HyperedgeWeight>& benefit_aggregator = _ets_benefit_aggregator.local();
    initializeGainCacheEntryForNode(partitioned_hg, u, benefit_aggregator);
  }

  // ! Returns the gain value for moving node u to block to.
  MT_KAHYPAR_ATTRIBUTE_ALWAYS_INLINE
  HyperedgeWeight benefitTerm(const HypernodeID u, const PartitionID to) const {
    ASSERT(_is_initialized, "Gain cache is not initialized");
    return _gain_cache[benefit_index(u, to)].load(std::memory_order_relaxed);
  }

  // ! Returns the gain value for moving node u to block to.
  // ! (same as benefitTerm(...))
  MT_KAHYPAR_ATTRIBUTE_ALWAYS_INLINE
  HyperedgeWeight gain(const HypernodeID u,
                       const PartitionID, /* only relevant for graphs */
                       const PartitionID to ) const {
    ASSERT(_is_initialized, "Gain cache is not initialized");
    return benefitTerm(u, to);
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
  // ! When moving a node from its current block from to a target block to, we iterate
  // ! over its incident hyperedges and update their pin count values. After each pin count
  // ! update, we call this function to update the gain cache to changes associated with
  // ! corresponding hyperedge.
  template<typename PartitionedHypergraph>
  void deltaGainUpdate(const PartitionedHypergraph& partitioned_hg,
                       const SynchronizedEdgeUpdate& sync_update);

  // ####################### Uncontraction #######################

  // ! This function implements the gain cache update after an uncontraction that restores node v in
  // ! hyperedge he. After the uncontraction operation, node u and v are contained in hyperedge he.
  template<typename PartitionedHypergraph>
  void uncontractUpdateAfterRestore(const PartitionedHypergraph& partitioned_hg,
                                    const HypernodeID u,
                                    const HypernodeID v,
                                    const HyperedgeID he,
                                    const HypernodeID pin_count_in_part_after);

  // ! This function implements the gain cache update after an uncontraction that replaces u with v in
  // ! hyperedge he. After the uncontraction only node v is contained in hyperedge he.
  template<typename PartitionedHypergraph>
  void uncontractUpdateAfterReplacement(const PartitionedHypergraph& partitioned_hg,
                                        const HypernodeID u,
                                        const HypernodeID v,
                                        const HyperedgeID he);

  // ! This function is called after restoring a single-pin hyperedge. The function assumes that
  // ! u is the only pin of the corresponding hyperedge, while block_of_u is its corresponding block ID.
  void restoreSinglePinHyperedge(const HypernodeID u,
                                 const PartitionID block_of_u,
                                 const HyperedgeWeight weight_of_he);

  // ! This function is called after restoring a net that became identical to another due to a contraction.
  template<typename PartitionedHypergraph>
  void restoreIdenticalHyperedge(const PartitionedHypergraph&,
                                 const HyperedgeID);

  // ! Notifies the gain cache that all uncontractions of the current batch are completed.
  void batchUncontractionsCompleted() {
    // Do nothing
  }

  // ####################### Only for Testing #######################

  template<typename PartitionedHypergraph>
  MT_KAHYPAR_ATTRIBUTE_ALWAYS_INLINE
  HyperedgeWeight recomputePenaltyTerm(const PartitionedHypergraph&,
                                       const HypernodeID) const {
    ASSERT(_is_initialized, "Gain cache is not initialized");
    return 0;
  }

  template<typename PartitionedHypergraph>
  MT_KAHYPAR_ATTRIBUTE_ALWAYS_INLINE
  HyperedgeWeight recomputeBenefitTerm(const PartitionedHypergraph& partitioned_hg,
                                       const HypernodeID u,
                                       const PartitionID to) const {
    ASSERT(partitioned_hg.hasTargetGraph());
    HyperedgeWeight gain = 0;
    const TargetGraph& target_graph = *partitioned_hg.targetGraph();
    const PartitionID from = partitioned_hg.partID(u);
    for (const HyperedgeID& e : partitioned_hg.incidentEdges(u)) {
      ds::Bitset& connectivity_set = partitioned_hg.deepCopyOfConnectivitySet(e);
      const HyperedgeWeight current_distance = target_graph.distance(connectivity_set);
      if ( partitioned_hg.pinCountInPart(e, from) == 1 ) {
        // Moving the node out of its current block removes
        // its block from the connectivity set
        connectivity_set.unset(from);
      }
      const HyperedgeWeight distance_with_to = target_graph.distanceWithBlock(connectivity_set, to);
      gain += (current_distance - distance_with_to) * partitioned_hg.edgeWeight(e);
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
  friend class DeltaSteinerTreeGainCache;

  MT_KAHYPAR_ATTRIBUTE_ALWAYS_INLINE
  size_t benefit_index(const HypernodeID u, const PartitionID p) const {
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
        _version.assign(num_edges, HyperedgeState());
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

  bool nodeGainAssertions(const HypernodeID u, const PartitionID p) const {
    if ( p == kInvalidPartition || p >= _k ) {
      LOG << "Invalid block ID (Node" << u << "is part of block" << p
          << ", but valid block IDs must be in the range [ 0," << _k << "])";
      return false;
    }
    if ( benefit_index(u, p) >= _gain_cache.size() ) {
      LOG << "Access to gain cache would result in an out-of-bounds access ("
          << "Benefit Index =" << benefit_index(u, p)
          << ", Gain Cache Size =" << _gain_cache.size() << ")";
      return false;
    }
    return true;
  }

  vec<Gain> initializeBenefitAggregator() const {
    return vec<Gain>(_k, std::numeric_limits<Gain>::min());
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
  vec<HyperedgeState> _version;

  // ! Array to store version IDs when we lazily initialize a gain cache entry
  tbb::enumerable_thread_specific<vec<uint32_t>> _ets_version;

  // ! Threshold for the size of a hyperedge that we do not count when tracking adjacent blocks
  HypernodeID _large_he_threshold;
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
class DeltaSteinerTreeGainCache {

  using DeltaAdjacentBlocks = ds::DeltaConnectivitySet<ds::ConnectivitySets>;
  using AdjacentBlocksIterator = typename DeltaAdjacentBlocks::Iterator;

 public:
  static constexpr bool requires_connectivity_set = true;

  DeltaSteinerTreeGainCache(const SteinerTreeGainCache& gain_cache) :
    _gain_cache(gain_cache),
    _gain_cache_delta(),
    _invalid_gain_cache_entry(),
    _num_incident_edges_delta(),
    _adjacent_blocks_delta(gain_cache._k),
    _large_he_threshold(gain_cache._large_he_threshold) {
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

  // ! Returns the penalty term of node u.
  // ! Note that the steiner tree gain cache does not maintain a
  // ! penalty term and returns zero in this case.
  MT_KAHYPAR_ATTRIBUTE_ALWAYS_INLINE
  HyperedgeWeight penaltyTerm(const HypernodeID,
                              const PartitionID) const {
    return 0;
  }

  // ! Returns the gain value for moving node u to block to.
  MT_KAHYPAR_ATTRIBUTE_ALWAYS_INLINE
  HyperedgeWeight benefitTerm(const HypernodeID u, const PartitionID to) const {
    ASSERT(to != kInvalidPartition && to < _gain_cache._k);
    const bool use_benefit_term_from_shared_gain_cache =
      !_invalid_gain_cache_entry.contains(_gain_cache.benefit_index(u, to)) &&
      _gain_cache._adjacent_blocks.contains(u, to);
    const HyperedgeWeight benefit_term =
      use_benefit_term_from_shared_gain_cache * _gain_cache.benefitTerm(u, to);
    const HyperedgeWeight* benefit_delta =
      _gain_cache_delta.get_if_contained(_gain_cache.benefit_index(u, to));
    return benefit_term + ( benefit_delta ? *benefit_delta : 0 );
  }

  // ! Returns the gain value for moving node u to block to.
  // ! (same as benefitTerm(...))
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
    ASSERT(sync_update.connectivity_set_after);
    ASSERT(sync_update.target_graph);
    const HyperedgeID he = sync_update.he;
    const PartitionID from = sync_update.from;
    const PartitionID to = sync_update.to;
    const HyperedgeWeight edge_weight = sync_update.edge_weight;
    const HypernodeID pin_count_in_from_part_after = sync_update.pin_count_in_from_part_after;
    const HypernodeID pin_count_in_to_part_after = sync_update.pin_count_in_to_part_after;
    const TargetGraph& target_graph = *sync_update.target_graph;
    ds::Bitset& connectivity_set = *sync_update.connectivity_set_after;

    if ( pin_count_in_from_part_after == 0 || pin_count_in_to_part_after == 1 ) {
      // Connectivity set has changed
      // => Recompute gain of hyperedge for all pins and their adjacent blocks

      // Compute new gain of hyperedge for all pins and their adjacent blocks and
      // add it to the gain cache entries
      for ( const HypernodeID& pin : partitioned_hg.pins(he) ) {
        const PartitionID source = partitioned_hg.partID(pin);
        const HypernodeID pin_count_in_source_block_after =
          partitioned_hg.pinCountInPart(he, source);
        for ( const PartitionID& target : adjacentBlocks(pin) ) {
          if ( source != target ) {
            const HyperedgeWeight gain_after = gainOfHyperedge(
              source, target, pin_count_in_source_block_after,
              edge_weight, target_graph, connectivity_set);
            _gain_cache_delta[_gain_cache.benefit_index(pin, target)] += gain_after;
          }
        }
      }

      // Reconstruct connectivity set and pin counts before the node move
      reconstructConnectivitySetBeforeMove(sync_update, connectivity_set);
      // Compute old gain of hyperedge for all pins and their adjacent blocks and
      // subtract it from the gain cache entries
      for ( const HypernodeID& pin : partitioned_hg.pins(he) ) {
        const PartitionID source = partitioned_hg.partID(pin);
        const PartitionID pin_count_in_source_part_before = source == from ?
          sync_update.pin_count_in_from_part_after + 1 : (source == to ?
          sync_update.pin_count_in_to_part_after - 1 : partitioned_hg.pinCountInPart(he, source));
        for ( const PartitionID& target : adjacentBlocks(pin) ) {
            if ( source != target ) {
            const HyperedgeWeight gain_before = gainOfHyperedge(
              source, target, pin_count_in_source_part_before,
              edge_weight, target_graph, connectivity_set);
            _gain_cache_delta[_gain_cache.benefit_index(pin, target)] -= gain_before;
          }
        }
      }
    } else {
     if ( pin_count_in_from_part_after == 1 ) {
        // In this case, there is only one pin left in block `from` and moving it to another block
        // would remove the block from the connectivity set. Thus, we search for the last remaining pin
        // in that block and update its gains for moving it to all its adjacent blocks.
        for ( const HypernodeID& u : partitioned_hg.pins(he) ) {
          if ( partitioned_hg.partID(u) == from ) {
            for ( const PartitionID& target : adjacentBlocks(u) ) {
              if ( from != target ) {
                // Compute new gain of hyperedge for moving u to the target block
                const HyperedgeWeight gain = gainOfHyperedge(
                  from, target, pin_count_in_from_part_after,
                  edge_weight, target_graph, connectivity_set);
                _gain_cache_delta[_gain_cache.benefit_index(u, target)] += gain;

                // Before the node move, we would have increase the connectivity of the hyperedge
                // if we would have moved u to a block not in the connectivity set of the hyperedge.
                // Thus, we subtract the old gain from gain cache entry.
                const HypernodeID pin_count_target_part_before = target == to ?
                  pin_count_in_to_part_after - 1 : partitioned_hg.pinCountInPart(he, target);
                if ( pin_count_target_part_before == 0 ) {
                  // The target part was not part of the connectivity set of the hyperedge before the move.
                  // Thus, moving u to that block would have increased the connectivity of the hyperedge.
                  // However, this is no longer the case since moving u out of its block would remove the
                  // block from the connectivity set.
                  const bool was_set = connectivity_set.isSet(target);
                  connectivity_set.unset(target);
                  const HyperedgeWeight distance_before = target_graph.distance(connectivity_set);
                  const HyperedgeWeight distance_after = target_graph.distanceWithBlock(connectivity_set, target);
                  const HyperedgeWeight gain_before = (distance_before - distance_after) * edge_weight;
                  _gain_cache_delta[_gain_cache.benefit_index(u, target)] -= gain_before;
                  if ( was_set ) connectivity_set.set(target);
                }
              }
            }
          }
        }
      }

      if (pin_count_in_to_part_after == 2) {
        // In this case, there are now two pins in block `to`. However, moving out the previously last pin
        // of block `to` would have decreased the connectivity of the hyperedge. This is no longer the case
        // since there are two pins in the block. Thus, we search for this pin and update its gain.
        for ( const HypernodeID& u : partitioned_hg.pins(he) ) {
          if ( partitioned_hg.partID(u) == to ) {
            for ( const PartitionID& target : adjacentBlocks(u) ) {
              if ( target != to ) {
                // Compute new gain of hyperedge for moving u to the target block
                const HyperedgeWeight gain = gainOfHyperedge(
                  to, target, pin_count_in_to_part_after,
                  edge_weight, target_graph, connectivity_set);
                _gain_cache_delta[_gain_cache.benefit_index(u, target)] += gain;

                // Before the node move, we would have decreased the connectivity of the hyperedge
                // if we would have moved u to a block in the connecivity set or replaced its block
                // with another if we would have moved it to block not in the connectivity set.
                // Thus, we subtract the old gain from gain cache entry.
                const HypernodeID pin_count_target_part_before = target == from ?
                  pin_count_in_from_part_after + 1 : partitioned_hg.pinCountInPart(he, target);
                const bool was_set = connectivity_set.isSet(target);
                if ( pin_count_target_part_before == 0 ) connectivity_set.unset(target);
                const HyperedgeWeight distance_before = target_graph.distance(connectivity_set);
                HyperedgeWeight distance_after = 0;
                if ( pin_count_target_part_before > 0 ) {
                  // The target block was part of the connectivity set before the node move.
                  // Thus, moving u out of its block would have decreased the connectivity of
                  // the hyperedge.
                  distance_after = target_graph.distanceWithoutBlock(connectivity_set, to);
                } else {
                  // The target block was not part of the connectivity set before the node move.
                  // Thus, moving u out of its block would have replaced block `to` with the target block
                  // in the connectivity set.
                  distance_after = target_graph.distanceAfterExchangingBlocks(connectivity_set, to, target);
                }
                const HyperedgeWeight gain_before = (distance_before - distance_after) * edge_weight;
                _gain_cache_delta[_gain_cache.benefit_index(u, target)] -= gain_before;
                if ( was_set ) connectivity_set.set(target);
              }
            }
          }
        }
      }
    }

    updateAdjacentBlocks(partitioned_hg, sync_update);
  }

 // ####################### Miscellaneous #######################

  void memoryConsumption(utils::MemoryTreeNode* parent) const {
    ASSERT(parent);
    utils::MemoryTreeNode* gain_cache_delta_node = parent->addChild("Delta Gain Cache");
    gain_cache_delta_node->updateSize(size_in_bytes());
  }

 private:
  MT_KAHYPAR_ATTRIBUTE_ALWAYS_INLINE
  HyperedgeWeight gainOfHyperedge(const PartitionID from,
                                  const PartitionID to,
                                  const HypernodeID pin_count_in_from_part,
                                  const HyperedgeWeight edge_weight,
                                  const TargetGraph& target_graph,
                                  ds::Bitset& connectivity_set) {
    const HyperedgeWeight current_distance = target_graph.distance(connectivity_set);
    if ( pin_count_in_from_part == 1 ) {
      connectivity_set.unset(from);
    }
    const HyperedgeWeight distance_with_to = target_graph.distanceWithBlock(connectivity_set, to);
    if ( pin_count_in_from_part == 1 ) {
      connectivity_set.set(from);
    }
    return (current_distance - distance_with_to) * edge_weight;
  }

  MT_KAHYPAR_ATTRIBUTE_ALWAYS_INLINE
  void reconstructConnectivitySetBeforeMove(const SynchronizedEdgeUpdate& sync_update,
                                            ds::Bitset& connectivity_set) {
    if ( sync_update.pin_count_in_from_part_after == 0 ) {
      connectivity_set.set(sync_update.from);
    }
    if ( sync_update.pin_count_in_to_part_after == 1 ) {
      connectivity_set.unset(sync_update.to);
    }
  }

  // ! Updates the adjacent blocks of a node based on a synronized hyperedge update
  template<typename PartitionedHypergraph>
  void updateAdjacentBlocks(const PartitionedHypergraph& partitioned_hg,
                            const SynchronizedEdgeUpdate& sync_update) {
    if ( partitioned_hg.edgeSize(sync_update.he) <= _large_he_threshold ) {
      if ( sync_update.pin_count_in_from_part_after == 0 ) {
        for ( const HypernodeID& pin : partitioned_hg.pins(sync_update.he) ) {
          decrementIncidentEdges(pin, sync_update.from);
        }
      }
      if ( sync_update.pin_count_in_to_part_after == 1 ) {
        for ( const HypernodeID& pin : partitioned_hg.pins(sync_update.he) ) {
          const HyperedgeID incident_edges_after = incrementIncidentEdges(pin, sync_update.to);
          if ( incident_edges_after == 1 ) {
            _invalid_gain_cache_entry[_gain_cache.benefit_index(pin, sync_update.to)] = true;
            initializeGainCacheEntry(partitioned_hg, pin, sync_update.to);
          }
        }
      }
    }
  }

  // ! Decrements the number of incident edges of node u that contains pins of block to
  // ! If the value decreases to zero, we remove the block from the connectivity set of the node
  HypernodeID decrementIncidentEdges(const HypernodeID hn, const PartitionID to) {
    const HypernodeID shared_incident_count =
      _gain_cache._num_incident_edges_of_block[_gain_cache.benefit_index(hn, to)];
    const HypernodeID thread_local_incident_count_after =
      --_num_incident_edges_delta[_gain_cache.benefit_index(hn, to)];
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
      _gain_cache._num_incident_edges_of_block[_gain_cache.benefit_index(hn, to)];
    const HypernodeID thread_local_incident_count_after =
      ++_num_incident_edges_delta[_gain_cache.benefit_index(hn, to)];
    if ( shared_incident_count + thread_local_incident_count_after == 1 ) {
      _adjacent_blocks_delta.add(hn, to);
    }
    return shared_incident_count + thread_local_incident_count_after;
  }

  // ! Initializes a gain cache entry
  template<typename PartitionedHypergraph>
  void initializeGainCacheEntry(const PartitionedHypergraph& partitioned_hg,
                                const HypernodeID hn,
                                const PartitionID to) {
    ASSERT(partitioned_hg.hasTargetGraph());
    const TargetGraph& target_graph = *partitioned_hg.targetGraph();
    const HypernodeID from = partitioned_hg.partID(hn);
    HyperedgeWeight gain = 0;
    for ( const HyperedgeID& he : partitioned_hg.incidentEdges(hn) ) {
      ds::Bitset& connectivity_set = partitioned_hg.deepCopyOfConnectivitySet(he);
      const HyperedgeWeight current_distance = target_graph.distance(connectivity_set);
      if ( partitioned_hg.pinCountInPart(he, from) == 1 ) {
        connectivity_set.unset(from);
      }
      const HyperedgeWeight distance_with_to =
        target_graph.distanceWithBlock(connectivity_set, to);
      gain += (current_distance - distance_with_to) * partitioned_hg.edgeWeight(he);
    }
    _gain_cache_delta[_gain_cache.benefit_index(hn, to)] = gain;
  }

  const SteinerTreeGainCache& _gain_cache;

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

  // ! Threshold for the size of a hyperedge that we do not count when tracking adjacent blocks
  HypernodeID _large_he_threshold;
};

}  // namespace mt_kahypar
