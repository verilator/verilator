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

#include "mt-kahypar/partition/refinement/gains/steiner_tree_for_graphs/steiner_tree_gain_cache_for_graphs.h"

#include <tbb/parallel_for.h>
#include <tbb/enumerable_thread_specific.h>
#include <tbb/concurrent_vector.h>

#include "mt-kahypar/datastructures/synchronized_edge_update.h"
#include "mt-kahypar/definitions.h"

namespace mt_kahypar {

template<typename PartitionedHypergraph>
void GraphSteinerTreeGainCache::initializeGainCache(const PartitionedHypergraph& partitioned_hg) {
  ASSERT(!_is_initialized, "Gain cache is already initialized");
  ASSERT(_k <= 0 || _k >= partitioned_hg.k(),
    "Gain cache was already initialized for a different k" << V(_k) << V(partitioned_hg.k()));
  allocateGainTable(partitioned_hg.topLevelNumNodes(), partitioned_hg.topLevelNumUniqueIds(), partitioned_hg.k());
  initializeAdjacentBlocks(partitioned_hg);

  tbb::parallel_invoke([&] {
  // Compute gain of all nodes
    tbb::parallel_for(tbb::blocked_range<HypernodeID>(HypernodeID(0), partitioned_hg.initialNumNodes()),
      [&](tbb::blocked_range<HypernodeID>& r) {
        vec<HyperedgeWeight>& gain_aggregator = _ets_benefit_aggregator.local();
        for (HypernodeID u = r.begin(); u < r.end(); ++u) {
          if ( partitioned_hg.nodeIsEnabled(u)) {
            initializeGainCacheEntryForNode(partitioned_hg, u, gain_aggregator);
          }
        }
      });
  }, [&] {
    // Resets edge states
    partitioned_hg.doParallelForAllEdges([&](const HyperedgeID& he) {
      _edge_state[partitioned_hg.uniqueEdgeID(he)].updateBlocks(
        kInvalidPartition, kInvalidPartition, 0);
    });
  });

  _is_initialized = true;
}

template<typename PartitionedHypergraph>
void GraphSteinerTreeGainCache::initializeGainCacheEntryForNode(const PartitionedHypergraph& partitioned_hg,
                                                                const HypernodeID hn) {
  vec<HyperedgeWeight>& gain_aggregator = _ets_benefit_aggregator.local();
  initializeAdjacentBlocksOfNode(partitioned_hg, hn);
  initializeGainCacheEntryForNode(partitioned_hg, hn, gain_aggregator);
}

bool GraphSteinerTreeGainCache::triggersDeltaGainUpdate(const SynchronizedEdgeUpdate&) {
  return true;
}

template<typename PartitionedHypergraph>
void GraphSteinerTreeGainCache::notifyBeforeDeltaGainUpdate(const PartitionedHypergraph& partitioned_hg,
                                                            const SynchronizedEdgeUpdate& sync_update) {
  if ( !partitioned_hg.isSinglePin(sync_update.he) ) {
    const HyperedgeID unique_id = partitioned_hg.uniqueEdgeID(sync_update.he);
    ASSERT(UL(unique_id) < _edge_state.size());
    ++_edge_state[unique_id].version;
    const HypernodeID u = partitioned_hg.edgeSource(sync_update.he);
    const HypernodeID v = partitioned_hg.edgeTarget(sync_update.he);
    if ( u < v ) {
      _edge_state[unique_id].updateBlocks(
        sync_update.to, sync_update.block_of_other_node, _uncontraction_version);
    } else {
      _edge_state[unique_id].updateBlocks(
        sync_update.block_of_other_node, sync_update.to, _uncontraction_version);
    }
  }
}

template<typename PartitionedHypergraph>
void GraphSteinerTreeGainCache::deltaGainUpdate(const PartitionedHypergraph& partitioned_hg,
                                                const SynchronizedEdgeUpdate& sync_update) {
  ASSERT(_is_initialized, "Gain cache is not initialized");
  ASSERT(sync_update.target_graph);

  const HyperedgeID he = sync_update.he;
  if ( !partitioned_hg.isSinglePin(he) ) {
    const PartitionID from = sync_update.from;
    const PartitionID to = sync_update.to;
    const HyperedgeWeight edge_weight = sync_update.edge_weight;
    const TargetGraph& target_graph = *sync_update.target_graph;

    const HypernodeID v = partitioned_hg.edgeTarget(he);
    for ( const PartitionID& target : _adjacent_blocks.connectivitySet(v) ) {
      const HyperedgeWeight delta = ( target_graph.distance(from, target) -
        target_graph.distance(to, target) ) * edge_weight ;
      _gain_cache[gain_entry_index(v, target)].add_fetch(delta, std::memory_order_relaxed);
    }

    // Update gain version of hyperedge. If the update version is equal to the version
    // of the hyperedge, then we know that all gain cache updates are completed. This is
    // important for initializing gain entries while simultanously running gain cache updates.
    const HyperedgeID unique_id = partitioned_hg.uniqueEdgeID(sync_update.he);
    ASSERT(UL(unique_id) < _edge_state.size());
    ++_edge_state[unique_id].update_version;

    // We update the adjacent blocks of nodes affected by this gain cache update
    // which will then trigger initialization of gain entries if a node becomes adjacent
    // to a new block.
    updateAdjacentBlocks(partitioned_hg, sync_update);
  }
}

template<typename PartitionedHypergraph>
void GraphSteinerTreeGainCache::uncontractUpdateAfterRestore(const PartitionedHypergraph& partitioned_hg,
                                                             const HypernodeID u,
                                                             const HypernodeID v,
                                                             const HyperedgeID he,
                                                             const HypernodeID) {
  unused(v);
  // In this case, edge he was a selfloop and now it turns to a regular edge
  if ( _is_initialized ) {
    ASSERT(partitioned_hg.hasTargetGraph());
    ASSERT(!partitioned_hg.isSinglePin(he));
    ASSERT(partitioned_hg.edgeSource(he) == v);
    const TargetGraph& target_graph = *partitioned_hg.targetGraph();
    const PartitionID from = partitioned_hg.partID(u);
    const HyperedgeWeight edge_weight = partitioned_hg.edgeWeight(he);
    for ( const PartitionID& to : _adjacent_blocks.connectivitySet(u) ) {
      _gain_cache[gain_entry_index(u, to)].fetch_sub(
        target_graph.distance(from, to) * edge_weight, std::memory_order_relaxed);
    }
    incrementIncidentEdges(u, from);
    // Gain cache entry for v is initialized after batch uncontractions
  }
}

template<typename PartitionedHypergraph>
void GraphSteinerTreeGainCache::uncontractUpdateAfterReplacement(const PartitionedHypergraph& partitioned_hg,
                                                                 const HypernodeID u,
                                                                 const HypernodeID v,
                                                                 const HyperedgeID he) {
  unused(v);
  // In this case, u is replaced by v in hyperedge he
  // => Pin counts and connectivity set of hyperedge he does not change
  if ( _is_initialized && !partitioned_hg.isSinglePin(he) ) {
    const PartitionID block_of_u = partitioned_hg.partID(u);
    ASSERT(partitioned_hg.hasTargetGraph());
    ASSERT(partitioned_hg.edgeSource(he) == v);
    const TargetGraph& target_graph = *partitioned_hg.targetGraph();
    const HypernodeID w = partitioned_hg.edgeTarget(he);
    const PartitionID block_of_w = partitioned_hg.partID(w);
    const HyperedgeWeight edge_weight = partitioned_hg.edgeWeight(he);
    for ( const PartitionID& to : _adjacent_blocks.connectivitySet(u) ) {
      _gain_cache[gain_entry_index(u, to)].fetch_add(
        target_graph.distance(block_of_w, to) * edge_weight, std::memory_order_relaxed);
    }
    if ( block_of_u != block_of_w ) {
      decrementIncidentEdges(u, block_of_u);
    }
    decrementIncidentEdges(u, block_of_w);
    // Gain cache entry for v is initialized after batch uncontractions
  }
}

void GraphSteinerTreeGainCache::restoreSinglePinHyperedge(const HypernodeID,
                                                          const PartitionID,
                                                          const HyperedgeWeight) {
  // Do nothing
}

template<typename PartitionedHypergraph>
void GraphSteinerTreeGainCache::restoreIdenticalHyperedge(const PartitionedHypergraph& partitioned_hg,
                                                          const HyperedgeID he) {
  const HypernodeID u = partitioned_hg.edgeSource(he);
  const HypernodeID v = partitioned_hg.edgeTarget(he);
  if ( u < v ) {
    ASSERT(!partitioned_hg.isSinglePin(he));
    ASSERT(u != kInvalidHypernode && v != kInvalidHypernode && u != v, V(u) << V(v));
    ASSERT(partitioned_hg.nodeIsEnabled(u));
    ASSERT(partitioned_hg.nodeIsEnabled(v));
    const PartitionID block_of_u = partitioned_hg.partID(u);
    const PartitionID block_of_v = partitioned_hg.partID(v);
    incrementIncidentEdges(u, block_of_u);
    incrementIncidentEdges(v, block_of_u);
    if ( block_of_u != block_of_v ) {
      incrementIncidentEdges(u, block_of_v);
      incrementIncidentEdges(v, block_of_v);
    }
  }
}

template<typename PartitionedHypergraph>
void GraphSteinerTreeGainCache::initializeAdjacentBlocks(const PartitionedHypergraph& partitioned_hg) {
  // Initialize adjacent blocks of each node
  partitioned_hg.doParallelForAllNodes([&](const HypernodeID& hn) {
    initializeAdjacentBlocksOfNode(partitioned_hg, hn);
  });
}

template<typename PartitionedHypergraph>
void GraphSteinerTreeGainCache::initializeAdjacentBlocksOfNode(const PartitionedHypergraph& partitioned_hg,
                                                               const HypernodeID hn) {
  _adjacent_blocks.clear(hn);
  for ( PartitionID to = 0; to < _k; ++to ) {
    _num_incident_edges_of_block[gain_entry_index(hn, to)].store(0, std::memory_order_relaxed);
  }
  for ( const HyperedgeID& he : partitioned_hg.incidentEdges(hn) ) {
    if ( !partitioned_hg.isSinglePin(he) ) {
      const PartitionID block_of_source = partitioned_hg.partID(partitioned_hg.edgeSource(he));
      const PartitionID block_of_target = partitioned_hg.partID(partitioned_hg.edgeTarget(he));
      if ( block_of_source != block_of_target ) {
        incrementIncidentEdges(hn, block_of_source);
      }
      incrementIncidentEdges(hn, block_of_target);
    }
  }
}

template<typename PartitionedHypergraph>
void GraphSteinerTreeGainCache::updateAdjacentBlocks(const PartitionedHypergraph& partitioned_hg,
                                                     const SynchronizedEdgeUpdate& sync_update) {
  ASSERT(!partitioned_hg.isSinglePin(sync_update.he));
  if ( sync_update.pin_count_in_from_part_after == 0 ) {
    // The node move has removed the source block of the move from the
    // connectivity set of the hyperedge. We therefore decrement the number of
    // incident edges in the source block for each pin of the hyperedge. If this
    // decreases the counter to zero for some pin, we remove the source block
    // from the adjacent blocks of that pin.
    for ( const HypernodeID& pin : partitioned_hg.pins(sync_update.he) ) {
      decrementIncidentEdges(pin, sync_update.from);
    }
  }
  if ( sync_update.pin_count_in_to_part_after == 1 ) {
    // The node move has added the target block of the move to the
    // connectivity set of the hyperedge. We therefore increment the number of
    // incident edges in the target block for each pin of the hyperedge. If this
    // increases the counter to one for some pin, we add the target block
    // to the adjacent blocks of that pin. Moreover, since we only compute gain
    // cache entries to adjacent blocks, we initialize the gain cache entry
    // for that pin and target block.
    for ( const HypernodeID& pin : partitioned_hg.pins(sync_update.he) ) {
      const HyperedgeID incident_edges_after = incrementIncidentEdges(pin, sync_update.to);
      if ( incident_edges_after == 1 ) {
        ASSERT(sync_update.edge_locks);
        initializeGainCacheEntry(partitioned_hg, pin, sync_update.to, *sync_update.edge_locks);
      }
    }
  }
}

HyperedgeID GraphSteinerTreeGainCache::incrementIncidentEdges(const HypernodeID u, const PartitionID to) {
  const HyperedgeID incident_count_after =
    _num_incident_edges_of_block[gain_entry_index(u, to)].add_fetch(1, std::memory_order_relaxed);
  if ( incident_count_after == 1 ) {
    _adjacent_blocks.add(u, to);
  }
  return incident_count_after;
}

HyperedgeID GraphSteinerTreeGainCache::decrementIncidentEdges(const HypernodeID u, const PartitionID to) {
  ASSERT(_num_incident_edges_of_block[gain_entry_index(u, to)].load() > 0);
  const HyperedgeID incident_count_after =
    _num_incident_edges_of_block[gain_entry_index(u, to)].sub_fetch(1, std::memory_order_relaxed);
  if ( incident_count_after == 0 ) {
    _adjacent_blocks.remove(u, to);
  }
  return incident_count_after;
}

template<typename PartitionedHypergraph>
void GraphSteinerTreeGainCache::initializeGainCacheEntryForNode(const PartitionedHypergraph& partitioned_hg,
                                                                const HypernodeID u,
                                                                vec<Gain>& gain_aggregator) {
  ASSERT(partitioned_hg.hasTargetGraph());
  const TargetGraph& target_graph = *partitioned_hg.targetGraph();
  for ( const HyperedgeID& e : partitioned_hg.incidentEdges(u) ) {
    if ( !partitioned_hg.isSinglePin(e) ) {
      ASSERT(partitioned_hg.edgeSource(e) == u);
      const PartitionID block_of_target = partitioned_hg.partID(partitioned_hg.edgeTarget(e));
      const HyperedgeWeight edge_weight = partitioned_hg.edgeWeight(e);
      ASSERT(_adjacent_blocks.contains(u, partitioned_hg.partID(u)));
      for ( const PartitionID& to : _adjacent_blocks.connectivitySet(u) ) {
        gain_aggregator[to] -= target_graph.distance(to, block_of_target) * edge_weight;
      }
    }
  }

  for ( const PartitionID& to : _adjacent_blocks.connectivitySet(u) ) {
    _gain_cache[gain_entry_index(u, to)].store(gain_aggregator[to], std::memory_order_relaxed);
    gain_aggregator[to] = 0;
  }
}

template<typename PartitionedHypergraph>
void GraphSteinerTreeGainCache::initializeGainCacheEntry(const PartitionedHypergraph& partitioned_hg,
                                                         const HypernodeID u,
                                                         const PartitionID to,
                                                         ds::Array<SpinLock>& edge_locks) {
  ASSERT(partitioned_hg.hasTargetGraph());
  const TargetGraph& target_graph = *partitioned_hg.targetGraph();
  vec<uint32_t>& seen_versions = _ets_version.local();
  bool success = false;
  while ( !success ) {
    success = true;
    seen_versions.clear();
    HyperedgeWeight gain = 0;
    for ( const HyperedgeID& he : partitioned_hg.incidentEdges(u) ) {
      if ( !partitioned_hg.isSinglePin(he) ) {
        ASSERT(partitioned_hg.edgeSource(he) == u);
        const HyperedgeID unique_id = partitioned_hg.uniqueEdgeID(he);
        edge_locks[unique_id].lock();
        // The internal data structures in the partitioned graph are updated
        // in one transaction and each update is assoicated with a version ID. We
        // retrieve here the actual block IDs of the nodes incident to the edge he
        // at the time of its last update with a version ID. If this version ID changes
        // after the gain computation, we know that we computed the gain on outdated
        // information and retry.
        const uint32_t update_version = _edge_state[unique_id].update_version.load(std::memory_order_relaxed);
        const uint32_t edge_version = _edge_state[unique_id].version.load(std::memory_order_relaxed);
        PartitionID block_of_u = _edge_state[unique_id].sourceBlock(_uncontraction_version);
        PartitionID block_of_v = _edge_state[unique_id].targetBlock(_uncontraction_version);
        edge_locks[unique_id].unlock();

        const HypernodeID v = partitioned_hg.edgeTarget(he);
        // The edge state object stores the block ID of the node with smaller ID
        // first. Swapping both entries in case v < u gives the correct block for node v
        if ( v < u ) std::swap(block_of_u, block_of_v);
        // In case u and v were not moved yet, we retrieve the block ID of v from the partition.
        block_of_v = block_of_v == kInvalidPartition ? partitioned_hg.partID(v) : block_of_v;

        ASSERT(update_version <= edge_version);
        if ( update_version < edge_version ) {
          // There are still pending gain cache updates that must be finished
          // before we initialize the gain cache entry.
          success = false;
          break;
        }
        seen_versions.push_back(edge_version);

        gain -= target_graph.distance(to, block_of_v) * partitioned_hg.edgeWeight(he);
      }
    }
    _gain_cache[gain_entry_index(u, to)].store(gain, std::memory_order_relaxed);

    // Check if versions of an incident edge has changed in the meantime.
    // If not, gain cache entry is correct. Otherwise, recompute it.
    if ( success ) {
      size_t idx = 0;
      for ( const HyperedgeID& he : partitioned_hg.incidentEdges(u) ) {
        if ( !partitioned_hg.isSinglePin(he) ) {
          ASSERT(idx < seen_versions.size());
          const HyperedgeID unique_id = partitioned_hg.uniqueEdgeID(he);
          if ( seen_versions[idx++] != _edge_state[unique_id].version.load(std::memory_order_relaxed) ) {
            success = false;
            break;
          }
        }
      }
    }
  }
}

template<typename PartitionedHypergraph>
bool GraphSteinerTreeGainCache::verifyTrackedAdjacentBlocksOfNodes(const PartitionedHypergraph& partitioned_hg) const {
  bool success = true;
  vec<HyperedgeID> num_incident_edges(_k, 0);
  for ( const HypernodeID& hn : partitioned_hg.nodes() ) {
    num_incident_edges.assign(_k, 0);
    for ( const HyperedgeID& he : partitioned_hg.incidentEdges(hn) ) {
      if ( !partitioned_hg.isSinglePin(he) ) {
        for ( const PartitionID& block : partitioned_hg.connectivitySet(he) ) {
          ++num_incident_edges[block];
        }
      }
    }

    for ( PartitionID block = 0; block < _k; ++block ) {
      if ( _num_incident_edges_of_block[gain_entry_index(hn, block)] != num_incident_edges[block] )  {
        LOG << "Number of incident edges of node" << hn << "to block" << block << "=>"
            << "Expected:" << num_incident_edges[block] << ","
            << "Actual:" << _num_incident_edges_of_block[gain_entry_index(hn, block)];
        success = false;
      }
    }

    for ( const PartitionID block : _adjacent_blocks.connectivitySet(hn) ) {
      if ( num_incident_edges[block] == 0 ) {
        LOG << "Node" << hn << "is not adjacent to block" << block
            << ", but it is in its connectivity set";
        success = false;
      }
    }

    for ( PartitionID block = 0; block < _k; ++block ) {
      if ( num_incident_edges[block] > 0 && !_adjacent_blocks.contains(hn, block) ) {
        LOG << "Node" << hn << "should be adjacent to block" << block
            << ", but it is not in its connectivity set";
        success = false;
      }
    }
  }
  return success;
}

namespace {
#define STEINER_TREE_INITIALIZE_GAIN_CACHE(X) void GraphSteinerTreeGainCache::initializeGainCache(const X&)
#define STEINER_TREE_INITIALIZE_GAIN_CACHE_FOR_NODE(X) void GraphSteinerTreeGainCache::initializeGainCacheEntryForNode(const X&,          \
                                                                                                                       const HypernodeID)
#define STEINER_TREE_NOTIFY(X) void GraphSteinerTreeGainCache::notifyBeforeDeltaGainUpdate(const X&,                     \
                                                                                           const SynchronizedEdgeUpdate&)
#define STEINER_TREE_DELTA_GAIN_UPDATE(X) void GraphSteinerTreeGainCache::deltaGainUpdate(const X&,                     \
                                                                                          const SynchronizedEdgeUpdate&)
#define STEINER_TREE_RESTORE_UPDATE(X) void GraphSteinerTreeGainCache::uncontractUpdateAfterRestore(const X&,          \
                                                                                                    const HypernodeID, \
                                                                                                    const HypernodeID, \
                                                                                                    const HyperedgeID, \
                                                                                                    const HypernodeID)
#define STEINER_TREE_REPLACEMENT_UPDATE(X) void GraphSteinerTreeGainCache::uncontractUpdateAfterReplacement(const X&,            \
                                                                                                            const HypernodeID,   \
                                                                                                            const HypernodeID,   \
                                                                                                            const HyperedgeID)
#define STEINER_TREE_RESTORE_IDENTICAL_HYPEREDGE(X) void GraphSteinerTreeGainCache::restoreIdenticalHyperedge(const X&,            \
                                                                                                              const HyperedgeID)
#define STEINER_TREE_INIT_ADJACENT_BLOCKS(X) void GraphSteinerTreeGainCache::initializeAdjacentBlocks(const X&)
#define STEINER_TREE_INIT_ADJACENT_BLOCKS_OF_NODE(X) void GraphSteinerTreeGainCache::initializeAdjacentBlocksOfNode(const X&,          \
                                                                                                                    const HypernodeID)
#define STEINER_TREE_UPDATE_ADJACENT_BLOCKS(X) void GraphSteinerTreeGainCache::updateAdjacentBlocks(const X&,                     \
                                                                                                    const SynchronizedEdgeUpdate&)
#define STEINER_TREE_INIT_GAIN_CACHE_ENTRY(X) void GraphSteinerTreeGainCache::initializeGainCacheEntryForNode(const X&,           \
                                                                                                              const HypernodeID,  \
                                                                                                              vec<Gain>&)
#define STEINER_TREE_INIT_LAZY_GAIN_CACHE_ENTRY(X) void GraphSteinerTreeGainCache::initializeGainCacheEntry(const X&,             \
                                                                                                            const HypernodeID,    \
                                                                                                            const PartitionID,    \
                                                                                                            ds::Array<SpinLock>&)
#define STEINER_TREE_VERIFY_ADJACENT_BLOCKS(X) bool GraphSteinerTreeGainCache::verifyTrackedAdjacentBlocksOfNodes(const X&) const
}

INSTANTIATE_FUNC_WITH_PARTITIONED_HG(STEINER_TREE_INITIALIZE_GAIN_CACHE)
INSTANTIATE_FUNC_WITH_PARTITIONED_HG(STEINER_TREE_INITIALIZE_GAIN_CACHE_FOR_NODE)
INSTANTIATE_FUNC_WITH_PARTITIONED_HG(STEINER_TREE_NOTIFY)
INSTANTIATE_FUNC_WITH_PARTITIONED_HG(STEINER_TREE_DELTA_GAIN_UPDATE)
INSTANTIATE_FUNC_WITH_PARTITIONED_HG(STEINER_TREE_RESTORE_UPDATE)
INSTANTIATE_FUNC_WITH_PARTITIONED_HG(STEINER_TREE_REPLACEMENT_UPDATE)
INSTANTIATE_FUNC_WITH_PARTITIONED_HG(STEINER_TREE_RESTORE_IDENTICAL_HYPEREDGE)
INSTANTIATE_FUNC_WITH_PARTITIONED_HG(STEINER_TREE_INIT_ADJACENT_BLOCKS)
INSTANTIATE_FUNC_WITH_PARTITIONED_HG(STEINER_TREE_INIT_ADJACENT_BLOCKS_OF_NODE)
INSTANTIATE_FUNC_WITH_PARTITIONED_HG(STEINER_TREE_UPDATE_ADJACENT_BLOCKS)
INSTANTIATE_FUNC_WITH_PARTITIONED_HG(STEINER_TREE_INIT_GAIN_CACHE_ENTRY)
INSTANTIATE_FUNC_WITH_PARTITIONED_HG(STEINER_TREE_INIT_LAZY_GAIN_CACHE_ENTRY)
INSTANTIATE_FUNC_WITH_PARTITIONED_HG(STEINER_TREE_VERIFY_ADJACENT_BLOCKS)

}  // namespace mt_kahypar
