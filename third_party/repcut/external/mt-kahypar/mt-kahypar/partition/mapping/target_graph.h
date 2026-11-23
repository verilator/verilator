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

#include <queue>
#include <numeric>
#include <iostream>

#include <tbb/enumerable_thread_specific.h>

#ifdef KAHYPAR_USE_GROWT
#ifdef __clang__
#pragma clang diagnostic push
#pragma clang diagnostic ignored "-Wunused-parameter"
#endif
#ifdef __GNUC__
#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wpedantic"
#endif
#include "growt/allocator/alignedallocator.hpp"
#include "growt/data-structures/hash_table_mods.hpp"
#include "growt/data-structures/table_config.hpp"
#ifdef __GNUC__
#pragma GCC diagnostic pop
#endif
#ifdef __clang__
#pragma clang diagnostic pop
#endif
#else
#include <tbb/concurrent_unordered_map.h>
#endif

#include "mt-kahypar/macros.h"
#include "mt-kahypar/datastructures/static_graph.h"
#include "mt-kahypar/datastructures/static_bitset.h"
#include "mt-kahypar/parallel/atomic_wrapper.h"

namespace mt_kahypar {

#ifdef KAHYPAR_ENABLE_STEINER_TREE_METRIC
class TargetGraph {

  static constexpr HyperedgeWeight kInvalidDistance = std::numeric_limits<HyperedgeWeight>::max() / 3;
  static constexpr size_t INITIAL_HASH_TABLE_CAPACITY = 100000;
  static constexpr size_t MEMORY_LIMIT = 100000000;

  using PQElement = std::pair<HyperedgeWeight, PartitionID>;
  using PQ = std::priority_queue<PQElement, vec<PQElement>, std::greater<PQElement>>;

  #ifdef KAHYPAR_USE_GROWT
  using hasher_type    = utils_tm::hash_tm::murmur2_hash;
  using allocator_type = growt::AlignedAllocator<>;
  using ConcurrentHashTable = typename growt::table_config<
    uint64_t, uint64_t, hasher_type, allocator_type, hmod::growable, hmod::sync>::table_type;
  using HashTableHandle = typename ConcurrentHashTable::handle_type;
  #else
  using ConcurrentHashTable = tbb::concurrent_unordered_map<uint64_t, uint64_t>;
  #endif

  struct MSTData {
    MSTData(const size_t n) :
      bitset(n),
      lightest_edge(n),
      pq() { }

    ds::Bitset bitset;
    vec<HyperedgeWeight> lightest_edge;
    PQ pq;
  };

  struct Stats {
    Stats() :
      precomputed(0),
      cache_misses(0),
      cache_hits(0) { }

    CAtomic<size_t> precomputed;
    CAtomic<size_t> cache_misses;
    CAtomic<size_t> cache_hits;
  };

 public:
  static constexpr bool TRACK_STATS = false;

  explicit TargetGraph(ds::StaticGraph&& graph) :
    _is_initialized(false),
    _k(graph.initialNumNodes()),
    _graph(std::move(graph)),
    _max_precomputed_connectitivty(0),
    _distances(),
    _local_mst_data(graph.initialNumNodes()),
    _cache(INITIAL_HASH_TABLE_CAPACITY),
     #ifdef KAHYPAR_USE_GROWT
    _handles([&]() { return getHandle(); }),
     #endif
    _stats() { }

  TargetGraph(const TargetGraph&) = delete;
  TargetGraph & operator= (const TargetGraph &) = delete;

  TargetGraph(TargetGraph&&) = default;
  TargetGraph & operator= (TargetGraph &&) = default;

  PartitionID numBlocks() const {
    return _k;
  }

  bool isInitialized() const {
    return _is_initialized;
  }

  const ds::StaticGraph& graph() const {
    return _graph;
  }

  // ! This function computes the weight of all steiner trees for all
  // ! connectivity sets with connectivity at most m (:= max_connectivity),
  void precomputeDistances(const size_t max_conectivity);

  // ! Returns the weight of the optimal steiner tree between all blocks
  // ! in the connectivity set if precomputed. Otherwise, we compute
  // ! a 2-approximation of the optimal steiner tree
  // ! (see computeWeightOfMSTOnMetricCompletion(...))
  HyperedgeWeight distance(const ds::StaticBitset& connectivity_set) const;

  HyperedgeWeight distance(const ds::Bitset& connectivity_set) const {
    ds::StaticBitset view(connectivity_set.numBlocks(), connectivity_set.data());
    return distance(view);
  }

  // ! Computes the optimal steiner tree between the blocks in the connectivity
  // ! set if we would add an additional block.
  HyperedgeWeight distanceWithBlock(ds::Bitset& connectivity_set, const PartitionID block) const {
    ASSERT(block < _k);
    const bool was_set = connectivity_set.isSet(block);
    connectivity_set.set(block);
    ds::StaticBitset view(connectivity_set.numBlocks(), connectivity_set.data());
    const HyperedgeWeight dist = distance(view);
    if ( !was_set ) connectivity_set.unset(block);
    return dist;
  }

  // ! Computes the optimal steiner tree between the blocks in the connectivity
  // ! set if we would remove an block.
  HyperedgeWeight distanceWithoutBlock(ds::Bitset& connectivity_set, const PartitionID block) const {
    ASSERT(block < _k);
    const bool was_set = connectivity_set.isSet(block);
    connectivity_set.unset(block);
    ds::StaticBitset view(connectivity_set.numBlocks(), connectivity_set.data());
    const HyperedgeWeight dist = distance(view);
    if ( was_set ) connectivity_set.set(block);
    return dist;
  }

  // ! Computes the optimal steiner tree between the blocks in the connectivity
  // ! set if we would remove block `removed_block` and block `added_block` to
  // ! the connectivity set.
  HyperedgeWeight distanceAfterExchangingBlocks(ds::Bitset& connectivity_set,
                                                const PartitionID removed_block,
                                                const PartitionID added_block) const {
    ASSERT(removed_block < _k && added_block < _k);
    const bool was_removed_set = connectivity_set.isSet(removed_block);
    const bool was_added_set = connectivity_set.isSet(added_block);
    connectivity_set.unset(removed_block);
    connectivity_set.set(added_block);
    ds::StaticBitset view(connectivity_set.numBlocks(), connectivity_set.data());
    const HyperedgeWeight dist = distance(view);
    if ( was_removed_set ) connectivity_set.set(removed_block);
    if ( !was_added_set ) connectivity_set.unset(added_block);
    return dist;
  }

  // ! Returns the shortest path between two blocks in the target graph
  HyperedgeWeight distance(const PartitionID i, const PartitionID j) const {
    ASSERT(_is_initialized);
    return _distances[index(i, j)];
  }

  // ! Print statistics
  void printStats() const {
    const size_t total_requests = _stats.precomputed + _stats.cache_hits + _stats.cache_misses;
    LOG << "\nTarget Graph Distance Computation Stats:";
    std::cout << "Accessed Precomputed Distance = " << std::setprecision(2)
              << (static_cast<double>(_stats.precomputed) / total_requests) * 100 << "% ("
              << _stats.precomputed << ")" << std::endl;
    std::cout << "                 Computed MST = " << std::setprecision(2)
              << (static_cast<double>(_stats.cache_misses) / total_requests) * 100 << "% ("
              << _stats.cache_misses << ")" << std::endl;
    std::cout << "              Used Cached MST = " << std::setprecision(2)
              << (static_cast<double>(_stats.cache_hits) / total_requests) * 100 << "% ("
              << _stats.cache_hits << ")" << std::endl;
  }

  void printStats(std::stringstream& oss) const {
    oss << " used_precomputed_distance=" << _stats.precomputed
        << " used_mst=" << _stats.cache_misses
        << " used_cached_mst=" << _stats.cache_hits;
  }

 private:
  MT_KAHYPAR_ATTRIBUTE_ALWAYS_INLINE size_t index(const PartitionID i,
                                                  const PartitionID j) const {
    ASSERT(i < _k && j < _k);
    return i + j * _k;
  }

  MT_KAHYPAR_ATTRIBUTE_ALWAYS_INLINE size_t index(const ds::StaticBitset& connectivity_set) const {
    size_t index = 0;
    size_t multiplier = 1;
    PartitionID last_block = kInvalidPartition;
    for ( const PartitionID block : connectivity_set ) {
      ASSERT(block != kInvalidPartition && block < _k);
      index += multiplier * UL(block);
      multiplier *= UL(_k);
      last_block = block;
    }
    return last_block != kInvalidPartition ? index +
      (multiplier == UL(_k) ? last_block * _k : 0) : 0;
  }

  MT_KAHYPAR_ATTRIBUTE_ALWAYS_INLINE uint64_t computeHash(const ds::StaticBitset& connectivity_set) const {
    uint64_t index = 0;
    for ( const PartitionID block : connectivity_set ) {
      ASSERT(block != kInvalidPartition && block < _k && block < 64);
      index |= (static_cast<uint64_t>(1) << block);
    }
    return index;
  }

  // ! This function computes an MST on the metric completion of the target graph
  // ! restricted to the blocks in the connectivity set. The metric completion is
  // ! complete graph where each edge {u,v} has a weight equals the shortest path
  // ! connecting u and v. This gives a 2-approximation for steiner tree problem.
  HyperedgeWeight computeWeightOfMSTOnMetricCompletion(const ds::StaticBitset& connectivity_set) const;

  bool inputGraphIsConnected() const;

  #ifdef KAHYPAR_USE_GROWT
  HashTableHandle getHandle() const {
    return _cache.get_handle();
  }
  #endif

  bool _is_initialized;

  // ! Number of blocks
  PartitionID _k;

  // ! Graph data structure representing the target graph
  ds::StaticGraph _graph;

  // ! Maximum size of the connectivity set for which we have
  // ! precomputed optimal steiner trees
  PartitionID _max_precomputed_connectitivty;

  // ! Stores the weight of all precomputed steiner trees
  vec<HyperedgeWeight> _distances;

  // ! Data structures to compute MST for non-precomputed connectivity sets
  mutable tbb::enumerable_thread_specific<MSTData> _local_mst_data;

  // ! Cache stores the weight of MST computations
  mutable ConcurrentHashTable _cache;

  #ifdef KAHYPAR_USE_GROWT
  // ! Handle to access concurrent hash table
  mutable tbb::enumerable_thread_specific<HashTableHandle> _handles;
  #endif

  // ! Stats
  mutable Stats _stats;
};

#else
class TargetGraph {
 public:
  static constexpr bool TRACK_STATS = false;

  explicit TargetGraph(ds::StaticGraph&&) { }

  TargetGraph(const TargetGraph&) = delete;
  TargetGraph & operator= (const TargetGraph &) = delete;

  TargetGraph(TargetGraph&&) = default;
  TargetGraph & operator= (TargetGraph &&) = default;

  PartitionID numBlocks() const {
    return 0;
  }

  bool isInitialized() const {
    return false;
  }

  void precomputeDistances(const size_t) { }

  HyperedgeWeight distance(const ds::StaticBitset&) const {
    return 0;
  }


  HyperedgeWeight distance(const ds::Bitset&) const {
    return 0;
  }

  HyperedgeWeight distance(const PartitionID, const PartitionID) const {
    return 0;
  }

  HyperedgeWeight distanceWithBlock(ds::Bitset&, const PartitionID) const {
    return 0;
  }

  HyperedgeWeight distanceWithoutBlock(ds::Bitset&, const PartitionID) const {
    return 0;
  }

  HyperedgeWeight distanceAfterExchangingBlocks(ds::Bitset&, const PartitionID, const PartitionID) const {
    return 0;
  }


  const ds::StaticGraph& graph() const {
    return _dummy_graph;
  }

  void printStats() const {  }

  void printStats(std::stringstream&) const {  }

 private:

  ds::StaticGraph _dummy_graph;
};
#endif

}  // namespace kahypar
