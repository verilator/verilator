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

#include "mt-kahypar/partition/refinement/gains/cut_for_graphs/cut_gain_cache_for_graphs.h"

#include <tbb/parallel_for.h>
#include <tbb/enumerable_thread_specific.h>
#include <tbb/concurrent_vector.h>

#include "mt-kahypar/datastructures/synchronized_edge_update.h"
#include "mt-kahypar/definitions.h"

namespace mt_kahypar {

template<typename PartitionedGraph>
void GraphCutGainCache::initializeGainCache(const PartitionedGraph& partitioned_graph) {
  ASSERT(!_is_initialized, "Gain cache is already initialized");
  ASSERT(_k <= 0 || _k >= partitioned_graph.k(),
    "Gain cache was already initialized for a different k" << V(_k) << V(partitioned_graph.k()));
  allocateGainTable(partitioned_graph.topLevelNumNodes(), partitioned_graph.k());

  // assert that current gain values are zero
  ASSERT(!_is_initialized &&
          std::none_of(_gain_cache.begin(), _gain_cache.end(),
            [&](const auto& weight) { return weight.load() != 0; }));

  // Initialize gain cache
  partitioned_graph.doParallelForAllEdges([&](const HyperedgeID e) {
    const HypernodeID u = partitioned_graph.edgeSource(e);
    if (partitioned_graph.nodeIsEnabled(u) && !partitioned_graph.isSinglePin(e)) {
      size_t index = incident_weight_index(u,
        partitioned_graph.partID(partitioned_graph.edgeTarget(e)));
      _gain_cache[index].fetch_add(partitioned_graph.edgeWeight(e), std::memory_order_relaxed);
    }
  });

  _is_initialized = true;
}

bool GraphCutGainCache::triggersDeltaGainUpdate(const SynchronizedEdgeUpdate& /* only relevant for hypergraphs */) {
  return true;
}

template<typename PartitionedGraph>
void GraphCutGainCache::deltaGainUpdate(const PartitionedGraph& partitioned_graph,
                                        const SynchronizedEdgeUpdate& sync_update) {
  ASSERT(_is_initialized, "Gain cache is not initialized");
  const HypernodeID target = partitioned_graph.edgeTarget(sync_update.he);
  const size_t index_in_from_part = incident_weight_index(target, sync_update.from);
  _gain_cache[index_in_from_part].fetch_sub(sync_update.edge_weight, std::memory_order_relaxed);
  const size_t index_in_to_part = incident_weight_index(target, sync_update.to);
  _gain_cache[index_in_to_part].fetch_add(sync_update.edge_weight, std::memory_order_relaxed);
}

template<typename PartitionedGraph>
void GraphCutGainCache::uncontractUpdateAfterRestore(const PartitionedGraph& partitioned_graph,
                                                     const HypernodeID u,
                                                     const HypernodeID v,
                                                     const HyperedgeID he,
                                                     const HypernodeID) {
  if ( _is_initialized ) {
    // the edge weight is added to u and v
    const PartitionID block = partitioned_graph.partID(u);
    const HyperedgeWeight we = partitioned_graph.edgeWeight(he);
    _gain_cache[incident_weight_index(u, block)].fetch_add(we, std::memory_order_relaxed);
    _gain_cache[incident_weight_index(v, block)].fetch_add(we, std::memory_order_relaxed);
  }
}

template<typename PartitionedGraph>
MT_KAHYPAR_ATTRIBUTE_ALWAYS_INLINE
void GraphCutGainCache::uncontractUpdateAfterReplacement(const PartitionedGraph& partitioned_graph,
                                                         const HypernodeID u,
                                                         const HypernodeID v,
                                                         const HyperedgeID he) {
  if ( _is_initialized ) {
    // the edge weight shifts from u to v
    const HypernodeID w = partitioned_graph.edgeTarget(he);
    const PartitionID block_of_w = partitioned_graph.partID(w);
    const HyperedgeWeight we = partitioned_graph.edgeWeight(he);
    _gain_cache[incident_weight_index(u, block_of_w)].fetch_sub(we, std::memory_order_relaxed);
    _gain_cache[incident_weight_index(v, block_of_w)].fetch_add(we, std::memory_order_relaxed);
  }
}

namespace {
#define GRAPH_CUT_INITIALIZE_GAIN_CACHE(X) void GraphCutGainCache::initializeGainCache(const X&)
#define GRAPH_CUT_DELTA_GAIN_UPDATE(X) void GraphCutGainCache::deltaGainUpdate(const X&,                     \
                                                                               const SynchronizedEdgeUpdate&)
#define GRAPH_CUT_RESTORE_UPDATE(X) void GraphCutGainCache::uncontractUpdateAfterRestore(const X&,   \
                                                                              const HypernodeID,     \
                                                                              const HypernodeID,     \
                                                                              const HyperedgeID,     \
                                                                              const HypernodeID)
#define GRAPH_CUT_REPLACEMENT_UPDATE(X) void GraphCutGainCache::uncontractUpdateAfterReplacement(const X&,   \
                                                                                      const HypernodeID,     \
                                                                                      const HypernodeID,     \
                                                                                      const HyperedgeID)
}

INSTANTIATE_FUNC_WITH_PARTITIONED_HG(GRAPH_CUT_INITIALIZE_GAIN_CACHE)
INSTANTIATE_FUNC_WITH_PARTITIONED_HG(GRAPH_CUT_DELTA_GAIN_UPDATE)
INSTANTIATE_FUNC_WITH_PARTITIONED_HG(GRAPH_CUT_RESTORE_UPDATE)
INSTANTIATE_FUNC_WITH_PARTITIONED_HG(GRAPH_CUT_REPLACEMENT_UPDATE)

}  // namespace mt_kahypar
