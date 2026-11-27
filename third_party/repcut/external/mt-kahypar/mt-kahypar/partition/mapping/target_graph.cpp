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

#include "mt-kahypar/partition/mapping/target_graph.h"

#include <cmath>
#include <limits>

#include "mt-kahypar/datastructures/static_graph.h"
#include "mt-kahypar/partition/mapping/steiner_tree.h"
#include "mt-kahypar/utils/exception.h"

namespace mt_kahypar {

#ifdef KAHYPAR_ENABLE_STEINER_TREE_METRIC
void TargetGraph::precomputeDistances(const size_t max_connectivity) {
  ALWAYS_ASSERT(max_connectivity >= 2);
  if (!inputGraphIsConnected()) {
    throw InvalidInputException("Target graph must be connected, but it is not.");
  }

  const size_t num_entries = std::pow(_k, max_connectivity);
  if ( num_entries > MEMORY_LIMIT ) {
    throw SystemException(
      "Too much memory requested for precomputing steiner trees "
      "of connectivity sets in the target graph.");
  }
  _distances.assign(num_entries, kInvalidDistance);
  SteinerTree::compute(_graph, max_connectivity, _distances);

  _max_precomputed_connectitivty = max_connectivity;
  _is_initialized = true;
}

HyperedgeWeight TargetGraph::distance(const ds::StaticBitset& connectivity_set) const {
  ASSERT(_is_initialized);
  const PartitionID connectivity = connectivity_set.popcount();
  if ( likely(connectivity <= _max_precomputed_connectitivty) ) {
    const size_t idx = index(connectivity_set);
    ASSERT(idx < _distances.size());
    if constexpr ( TRACK_STATS ) ++_stats.precomputed;
    ASSERT(_distances[idx] < kInvalidDistance);
    return _distances[idx];
  } else {
    const uint64_t hash_key = computeHash(connectivity_set);
    // We have not precomputed the optimal steiner tree for the connectivity set.
    #ifdef KAHYPAR_USE_GROWT
    HashTableHandle& handle = _handles.local();
    auto res = handle.find(hash_key);
    if ( likely( res != handle.end() ) ) {
      if constexpr ( TRACK_STATS ) ++_stats.cache_hits;
      return (*res).second;
    } else {
      if constexpr ( TRACK_STATS ) ++_stats.cache_misses;
      // Entry is not cached => Compute 2-approximation of optimal steiner tree
      const HyperedgeWeight mst_weight =
        computeWeightOfMSTOnMetricCompletion(connectivity_set);
      handle.insert(hash_key, mst_weight);
      return mst_weight;
    }
    #else
    auto res = _cache.find(hash_key);
    if ( likely ( res != _cache.end() ) ) {
      if constexpr ( TRACK_STATS ) ++_stats.cache_hits;
      return res->second;
    } else {
      if constexpr ( TRACK_STATS ) ++_stats.cache_misses;
      // Entry is not cached => Compute 2-approximation of optimal steiner tree
      const HyperedgeWeight mst_weight =
        computeWeightOfMSTOnMetricCompletion(connectivity_set);
      _cache.insert(std::make_pair(hash_key, mst_weight));
      return mst_weight;
    }
    #endif
  }
}

/**
 * This function computes an MST on the metric completion of the target graph restricted to
 * the blocks in the connectivity set. To compute the MST, we use Jarnik-Prim algorithm which
 * has time complexity of |E| + |V| * log(|V|) = |V|^2 + |V| * log(|V|) (since we work on a
 * complete graph). However, we restrict the computation only to nodes and edges contained in
 * the connectivity set.
 */
HyperedgeWeight TargetGraph::computeWeightOfMSTOnMetricCompletion(const ds::StaticBitset& connectivity_set) const {
  ASSERT(_is_initialized);
  ASSERT(connectivity_set.popcount() > 0);
  MSTData& mst_data = _local_mst_data.local();
  ds::Bitset& remaining_nodes = mst_data.bitset;
  ds::StaticBitset cur_blocks(
    remaining_nodes.numBlocks(), remaining_nodes.data());
  vec<HyperedgeWeight>& lightest_edge = mst_data.lightest_edge;
  PQ& pq = mst_data.pq;
  ASSERT(pq.empty());

  auto push = [&](const PartitionID u) {
    for ( const PartitionID& v : cur_blocks ) {
      ASSERT(u != v);
      const HyperedgeWeight dist = _distances[index(u,v)];
      // If there is a lighter edge connecting v to the MST,
      // we push v with the new weight into the PQ.
      if ( dist < lightest_edge[v] ) {
        pq.push(std::make_pair(dist, v));
        lightest_edge[v] = dist;
      }
    }
  };

  // Initialize data structure and PQ
  PartitionID root = kInvalidPartition;
  for ( const PartitionID& block : connectivity_set ) {
    remaining_nodes.set(block);
    lightest_edge[block] = std::numeric_limits<HyperedgeWeight>::max();
    root = block;
  }
  remaining_nodes.unset(root);
  push(root);

  HyperedgeWeight res = 0;
  while ( !pq.empty() ) {
    PQElement best = pq.top(); pq.pop();
    const PartitionID u = best.second;
    if ( !remaining_nodes.isSet(u) ) {
      // u is already contained in the MST -> skip
      continue;
    }
    // Add u to the MST and update PQ
    res += best.first;
    remaining_nodes.unset(u);
    push(u);
  }

  // Reset data structures
  remaining_nodes.reset();
  ASSERT(pq.empty());
  return res;
}

bool TargetGraph::inputGraphIsConnected() const {
  // stack-based DFS
  std::vector<uint8_t> visited;
  std::vector<HypernodeID> stack;
  visited.resize(_graph.initialNumNodes(), 0);
  stack.push_back(0);
  visited[0] = 1;
  HypernodeID num_visited = 1;
  while (!stack.empty() && num_visited < _graph.initialNumNodes()) {
    HypernodeID hn = stack.back();
    stack.pop_back();
    for (HyperedgeID edge: _graph.incidentEdges(hn)) {
      HypernodeID neighbor = _graph.edgeTarget(edge);
      if (visited[neighbor] == 0) {
        stack.push_back(neighbor);
        visited[neighbor] = 1;
        num_visited++;
      }
    }
  }
  return num_visited == _graph.initialNumNodes();
}
#endif

}  // namespace kahypar
