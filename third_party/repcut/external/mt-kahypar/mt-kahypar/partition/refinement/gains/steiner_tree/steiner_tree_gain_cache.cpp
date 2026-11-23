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

#include "mt-kahypar/partition/refinement/gains/steiner_tree/steiner_tree_gain_cache.h"

#include <tbb/parallel_for.h>
#include <tbb/enumerable_thread_specific.h>
#include <tbb/concurrent_vector.h>

#include "mt-kahypar/datastructures/synchronized_edge_update.h"
#include "mt-kahypar/definitions.h"

namespace mt_kahypar {

template<typename PartitionedHypergraph>
void SteinerTreeGainCache::initializeGainCache(const PartitionedHypergraph& partitioned_hg) {
  ASSERT(!_is_initialized, "Gain cache is already initialized");
  ASSERT(_k <= 0 || _k >= partitioned_hg.k(),
    "Gain cache was already initialized for a different k" << V(_k) << V(partitioned_hg.k()));
  allocateGainTable(partitioned_hg.topLevelNumNodes(), partitioned_hg.topLevelNumEdges(), partitioned_hg.k());
  initializeAdjacentBlocks(partitioned_hg);

  // Compute gain of all nodes
  tbb::parallel_for(tbb::blocked_range<HypernodeID>(HypernodeID(0), partitioned_hg.initialNumNodes()),
    [&](tbb::blocked_range<HypernodeID>& r) {
      vec<HyperedgeWeight>& benefit_aggregator = _ets_benefit_aggregator.local();
      for (HypernodeID u = r.begin(); u < r.end(); ++u) {
        if ( partitioned_hg.nodeIsEnabled(u)) {
          initializeGainCacheEntryForNode(partitioned_hg, u, benefit_aggregator);
        }
      }
    });

  _is_initialized = true;
}

template<typename PartitionedHypergraph>
void SteinerTreeGainCache::initializeGainCacheEntryForNode(const PartitionedHypergraph& partitioned_hg,
                                                           const HypernodeID hn) {
  vec<HyperedgeWeight>& benefit_aggregator = _ets_benefit_aggregator.local();
  initializeAdjacentBlocksOfNode(partitioned_hg, hn);
  initializeGainCacheEntryForNode(partitioned_hg, hn, benefit_aggregator);
}

bool SteinerTreeGainCache::triggersDeltaGainUpdate(const SynchronizedEdgeUpdate& sync_update) {
  return sync_update.pin_count_in_from_part_after == 0 ||
         sync_update.pin_count_in_from_part_after == 1 ||
         sync_update.pin_count_in_to_part_after == 1 ||
         sync_update.pin_count_in_to_part_after == 2;
}

template<typename PartitionedHypergraph>
void SteinerTreeGainCache::notifyBeforeDeltaGainUpdate(const PartitionedHypergraph&,
                                                       const SynchronizedEdgeUpdate& sync_update) {
  if ( triggersDeltaGainUpdate(sync_update) ) {
    ASSERT(UL(sync_update.he) < _version.size());
    // The move will induce a gain cache update. In this case, we increment the version ID
    // of the hyperedge such that concurrent running initializations of gain entries are
    // notified and rerun the initialization step if this affected the gain computation.
    ++_version[sync_update.he].version;
  }
}

namespace {
MT_KAHYPAR_ATTRIBUTE_ALWAYS_INLINE
HyperedgeWeight gainOfHyperedge(const PartitionID from,
                                const PartitionID to,
                                const HyperedgeWeight edge_weight,
                                const TargetGraph& target_graph,
                                ds::PinCountSnapshot& pin_counts,
                                ds::Bitset& connectivity_set) {
  const HypernodeID pin_count_in_from_part = pin_counts.pinCountInPart(from);
  const HyperedgeWeight current_distance = target_graph.distance(connectivity_set);
  if ( pin_count_in_from_part == 1 ) {
    ASSERT(connectivity_set.isSet(from));
    connectivity_set.unset(from);
  }
  const HyperedgeWeight distance_with_to = target_graph.distanceWithBlock(connectivity_set, to);
  if ( pin_count_in_from_part == 1 ) {
    connectivity_set.set(from);
  }
  return (current_distance - distance_with_to) * edge_weight;
}

MT_KAHYPAR_ATTRIBUTE_ALWAYS_INLINE
void reconstructConnectivitySetAndPinCountsBeforeMove(const SynchronizedEdgeUpdate& sync_update,
                                                      ds::Bitset& connectivity_set,
                                                      ds::PinCountSnapshot& pin_counts) {
  if ( sync_update.pin_count_in_from_part_after == 0 ) {
    ASSERT(!connectivity_set.isSet(sync_update.from));
    connectivity_set.set(sync_update.from);
  }
  if ( sync_update.pin_count_in_to_part_after == 1 ) {
    ASSERT(connectivity_set.isSet(sync_update.to));
    connectivity_set.unset(sync_update.to);
  }
  pin_counts.setPinCountInPart(sync_update.from, sync_update.pin_count_in_from_part_after + 1);
  pin_counts.setPinCountInPart(sync_update.to, sync_update.pin_count_in_to_part_after - 1);
}
}

template<typename PartitionedHypergraph>
void SteinerTreeGainCache::deltaGainUpdate(const PartitionedHypergraph& partitioned_hg,
                                           const SynchronizedEdgeUpdate& sync_update) {
  ASSERT(_is_initialized, "Gain cache is not initialized");
  ASSERT(sync_update.connectivity_set_after);
  ASSERT(sync_update.pin_counts_after);
  ASSERT(sync_update.target_graph);

  if ( triggersDeltaGainUpdate(sync_update) ) {
    const HyperedgeID he = sync_update.he;
    const PartitionID from = sync_update.from;
    const PartitionID to = sync_update.to;
    const HyperedgeWeight edge_weight = sync_update.edge_weight;
    const HypernodeID pin_count_in_from_part_after = sync_update.pin_count_in_from_part_after;
    const HypernodeID pin_count_in_to_part_after = sync_update.pin_count_in_to_part_after;
    const TargetGraph& target_graph = *sync_update.target_graph;
    ds::Bitset& connectivity_set = *sync_update.connectivity_set_after;
    ds::PinCountSnapshot& pin_counts = *sync_update.pin_counts_after;

    if ( pin_count_in_from_part_after == 0 || pin_count_in_to_part_after == 1 ) {
      // Connectivity set has changed
      // => Recompute gain of hyperedge for all pins and their adjacent blocks

      // Compute new gain of hyperedge for all pins and their adjacent blocks and
      // add it to the gain cache entries
      for ( const HypernodeID& pin : partitioned_hg.pins(he) ) {
        const PartitionID source = partitioned_hg.partID(pin);
        for ( const PartitionID& target : _adjacent_blocks.connectivitySet(pin) ) {
          if ( source != target ) {
            const HyperedgeWeight gain_after = gainOfHyperedge(
              source, target, edge_weight, target_graph, pin_counts, connectivity_set);
            _gain_cache[benefit_index(pin, target)].add_fetch(gain_after, std::memory_order_relaxed);
          }
        }
      }

      // Reconstruct connectivity set and pin counts before the node move
      reconstructConnectivitySetAndPinCountsBeforeMove(sync_update, connectivity_set, pin_counts);
      // Compute old gain of hyperedge for all pins and their adjacent blocks and
      // subtract it from the gain cache entries
      for ( const HypernodeID& pin : partitioned_hg.pins(he) ) {
        const PartitionID source = partitioned_hg.partID(pin);
        for ( const PartitionID& target : _adjacent_blocks.connectivitySet(pin) ) {
            if ( source != target ) {
            const HyperedgeWeight gain_before = gainOfHyperedge(
              source, target, edge_weight, target_graph, pin_counts, connectivity_set);
            _gain_cache[benefit_index(pin, target)].sub_fetch(gain_before, std::memory_order_relaxed);
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
            for ( const PartitionID& target : _adjacent_blocks.connectivitySet(u) ) {
              if ( from != target ) {
                // Compute new gain of hyperedge for moving u to the target block
                const HyperedgeWeight gain = gainOfHyperedge(
                  from, target, edge_weight, target_graph, pin_counts, connectivity_set);
                _gain_cache[benefit_index(u, target)].add_fetch(gain, std::memory_order_relaxed);

                // Before the node move, we would have increase the connectivity of the hyperedge
                // if we would have moved u to a block not in the connectivity set of the hyperedge.
                // Thus, we subtract the old gain from gain cache entry.
                const HypernodeID pin_count_target_part_before = target == to ?
                  pin_count_in_to_part_after - 1 : pin_counts.pinCountInPart(target);
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
                  _gain_cache[benefit_index(u, target)].sub_fetch(gain_before, std::memory_order_relaxed);
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
            for ( const PartitionID& target : _adjacent_blocks.connectivitySet(u) ) {
              if ( target != to ) {
                // Compute new gain of hyperedge for moving u to the target block
                const HyperedgeWeight gain = gainOfHyperedge(
                  to, target, edge_weight, target_graph, pin_counts, connectivity_set);
                _gain_cache[benefit_index(u, target)].add_fetch(gain, std::memory_order_relaxed);

                // Before the node move, we would have decreased the connectivity of the hyperedge
                // if we would have moved u to a block in the connecivity set or replaced its block
                // with another if we would have moved it to block not in the connectivity set.
                // Thus, we subtract the old gain from gain cache entry.
                const HypernodeID pin_count_target_part_before = target == from ?
                  pin_count_in_from_part_after + 1 : pin_counts.pinCountInPart(target);
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
                _gain_cache[benefit_index(u, target)].sub_fetch(gain_before, std::memory_order_relaxed);
                if ( was_set ) connectivity_set.set(target);
              }
            }
          }
        }
      }
    }

    // Update gain version of hyperedge. If the update version is equal to the version
    // of the hyperedge, then we know that all gain cache updates are completed. This is
    // important for initializing gain entries while simultanously running gain cache updates.
    ++_version[sync_update.he].update_version;
  }

  // We update the adjacent blocks of nodes affected by this gain cache update
  // which will then trigger initialization of gain entries if a node becomes adjacent
  // to a new block.
  updateAdjacentBlocks(partitioned_hg, sync_update);
}

template<typename PartitionedHypergraph>
void SteinerTreeGainCache::uncontractUpdateAfterRestore(const PartitionedHypergraph& partitioned_hg,
                                                        const HypernodeID u,
                                                        const HypernodeID v,
                                                        const HyperedgeID he,
                                                        const HypernodeID pin_count_in_part_after) {
  // In this case, u and v are both contained in the hyperedge after the uncontraction operation
  // => Pin count of the block of node u increases by one, but connectivity set does not change.
  if ( _is_initialized ) {
    ASSERT(partitioned_hg.hasTargetGraph());
    const TargetGraph& target_graph = *partitioned_hg.targetGraph();
    const PartitionID block = partitioned_hg.partID(u);
    const HyperedgeWeight edge_weight = partitioned_hg.edgeWeight(he);
    if ( pin_count_in_part_after == 2 ) {
      // In this case, u was the only pin of its block contained in the hyperedge.
      // Aftwards, u and v are contained in the hyperedge both in the same block.
      // This changes the gain of u to all its adjacent blocks
      for ( const HypernodeID& pin : partitioned_hg.pins(he) ) {
        // u might be replaced by an other node in the batch
        // => search for other pin of the corresponding block and update gain.
        if ( pin != v && partitioned_hg.partID(pin) == block ) {
          ds::Bitset& connectivity_set = partitioned_hg.deepCopyOfConnectivitySet(he);
          const HyperedgeWeight current_distance = target_graph.distance(connectivity_set);
          for ( const PartitionID to : _adjacent_blocks.connectivitySet(pin) ) {
            if ( block != to ) {
              // u does no longer decrease the connectivity of the hyperedge. We therefore
              // subtract the previous contribution of the hyperedge to gain values of u
              HyperedgeWeight old_distance_after_move = 0;
              HyperedgeWeight new_distance_after_move = current_distance;
              if ( partitioned_hg.pinCountInPart(he, to) == 0 ) {
                old_distance_after_move = target_graph.distanceAfterExchangingBlocks(connectivity_set, block, to);
                new_distance_after_move = target_graph.distanceWithBlock(connectivity_set, to);
              } else {
                old_distance_after_move = target_graph.distanceWithoutBlock(connectivity_set, block);
              }
              const HyperedgeWeight old_gain = (current_distance - old_distance_after_move) * edge_weight;
              const HyperedgeWeight new_gain = (current_distance - new_distance_after_move) * edge_weight;
              _gain_cache[benefit_index(pin, to)].add_fetch(new_gain - old_gain, std::memory_order_relaxed);
            }
          }
          break;
        }
      }
    }

    if ( partitioned_hg.edgeSize(he) > _large_he_threshold ) {
      for ( const HypernodeID& pin : partitioned_hg.pins(he) ) {
        for ( const PartitionID& block : partitioned_hg.connectivitySet(he) ) {
          decrementIncidentEdges(pin, block);
        }
      }
    }

    // Other gain cache implementations initialize here the gain of node v.
    // However, this not possible since there are still pending uncontractions and
    // we do not know all adjacent blocks of node v at this point. We therefore initialize
    // them after all uncontractions are finished.
  }
}

template<typename PartitionedHypergraph>
void SteinerTreeGainCache::uncontractUpdateAfterReplacement(const PartitionedHypergraph& partitioned_hg,
                                                            const HypernodeID u,
                                                            const HypernodeID,
                                                            const HyperedgeID he) {
  // In this case, u is replaced by v in hyperedge he
  // => Pin counts and connectivity set of hyperedge he does not change
  if ( _is_initialized ) {
    ASSERT(partitioned_hg.hasTargetGraph());
    const TargetGraph& target_graph = *partitioned_hg.targetGraph();
    const PartitionID block = partitioned_hg.partID(u);
    const HyperedgeWeight edge_weight = partitioned_hg.edgeWeight(he);
    ds::Bitset& connectivity_set = partitioned_hg.deepCopyOfConnectivitySet(he);
    const HyperedgeWeight current_distance = target_graph.distance(connectivity_set);
    // Since u is no longer part of the hyperedge, we have to subtract the previous
    // contribution of the hyperedge for moving u out of its block from all its gain values
    // and add its new contribution.
    if ( partitioned_hg.pinCountInPart(he, block) == 1  ) {
      for ( const PartitionID to : _adjacent_blocks.connectivitySet(u) ) {
        if ( block != to ) {
          HyperedgeWeight distance_used_for_gain = 0;
          if ( partitioned_hg.pinCountInPart(he, to) == 0 ) {
            distance_used_for_gain = target_graph.distanceAfterExchangingBlocks(connectivity_set, block, to);
          } else {
            distance_used_for_gain = target_graph.distanceWithoutBlock(connectivity_set, block);
          }
          const HyperedgeWeight old_gain = (current_distance - distance_used_for_gain) * edge_weight;
          _gain_cache[benefit_index(u, to)].sub_fetch(old_gain, std::memory_order_relaxed);
        }
      }
    } else {
      for ( const PartitionID to : _adjacent_blocks.connectivitySet(u) ) {
        if ( block != to && partitioned_hg.pinCountInPart(he, to) == 0 ) {
          const HyperedgeWeight distance_with_to = target_graph.distanceWithBlock(connectivity_set, to);
          const HyperedgeWeight old_gain = (current_distance - distance_with_to) * edge_weight;
          _gain_cache[benefit_index(u, to)].sub_fetch(old_gain, std::memory_order_relaxed);
        }
      }
    }

    // Decrement number of incident edges of each block in the connectivity set
    // of the hyperedge since u is no longer part of the hyperedge.
    if ( partitioned_hg.edgeSize(he) <= _large_he_threshold ) {
      for ( const PartitionID& to : partitioned_hg.connectivitySet(he) ) {
        decrementIncidentEdges(u, to);
      }
    }

    // Other gain cache implementations initialize here the gain of node v.
    // However, this not possible since there are still pending uncontractions and
    // we do not know all adjacent blocks of node v at this point. We therefore initialize
    // them after all uncontractions are finished.
  }
}

void SteinerTreeGainCache::restoreSinglePinHyperedge(const HypernodeID u,
                                                     const PartitionID block_of_u,
                                                     const HyperedgeWeight) {
  incrementIncidentEdges(u, block_of_u);
}

template<typename PartitionedHypergraph>
void SteinerTreeGainCache::restoreIdenticalHyperedge(const PartitionedHypergraph& partitioned_hg,
                                                     const HyperedgeID he) {
  if ( partitioned_hg.edgeSize(he) <= _large_he_threshold ) {
    for ( const HypernodeID& pin : partitioned_hg.pins(he) ) {
      for ( const PartitionID& block : partitioned_hg.connectivitySet(he) ) {
        incrementIncidentEdges(pin, block);
      }
    }
  }
}

template<typename PartitionedHypergraph>
void SteinerTreeGainCache::initializeAdjacentBlocks(const PartitionedHypergraph& partitioned_hg) {
  // Initialize adjacent blocks of each node
  partitioned_hg.doParallelForAllNodes([&](const HypernodeID& hn) {
    initializeAdjacentBlocksOfNode(partitioned_hg, hn);
  });
}

template<typename PartitionedHypergraph>
void SteinerTreeGainCache::initializeAdjacentBlocksOfNode(const PartitionedHypergraph& partitioned_hg,
                                                          const HypernodeID hn) {
  _adjacent_blocks.clear(hn);
  for ( PartitionID to = 0; to < _k; ++to ) {
    _num_incident_edges_of_block[benefit_index(hn, to)].store(0, std::memory_order_relaxed);
  }
  for ( const HyperedgeID& he : partitioned_hg.incidentEdges(hn) ) {
    if ( partitioned_hg.edgeSize(he) <= _large_he_threshold ) {
      for ( const PartitionID& block : partitioned_hg.connectivitySet(he) ) {
        incrementIncidentEdges(hn, block);
      }
    }
  }
}

template<typename PartitionedHypergraph>
void SteinerTreeGainCache::updateAdjacentBlocks(const PartitionedHypergraph& partitioned_hg,
                                                const SynchronizedEdgeUpdate& sync_update) {
  if ( partitioned_hg.edgeSize(sync_update.he) <= _large_he_threshold ) {
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
}

HyperedgeID SteinerTreeGainCache::incrementIncidentEdges(const HypernodeID u, const PartitionID to) {
  const HyperedgeID incident_count_after =
    _num_incident_edges_of_block[benefit_index(u, to)].add_fetch(1, std::memory_order_relaxed);
  if ( incident_count_after == 1 ) {
    ASSERT(!_adjacent_blocks.contains(u, to));
    _gain_cache[benefit_index(u, to)].store(0, std::memory_order_relaxed);
    _adjacent_blocks.add(u, to);
  }
  return incident_count_after;
}

HyperedgeID SteinerTreeGainCache::decrementIncidentEdges(const HypernodeID u, const PartitionID to) {
  ASSERT(_num_incident_edges_of_block[benefit_index(u, to)].load() > 0);
  const HyperedgeID incident_count_after =
    _num_incident_edges_of_block[benefit_index(u, to)].sub_fetch(1, std::memory_order_relaxed);
  if ( incident_count_after == 0 ) {
    ASSERT(_adjacent_blocks.contains(u, to));
    _adjacent_blocks.remove(u, to);
  }
  return incident_count_after;
}

template<typename PartitionedHypergraph>
void SteinerTreeGainCache::initializeGainCacheEntryForNode(const PartitionedHypergraph& partitioned_hg,
                                                           const HypernodeID u,
                                                           vec<Gain>& benefit_aggregator) {
  ASSERT(partitioned_hg.hasTargetGraph());
  const TargetGraph& target_graph = *partitioned_hg.targetGraph();
  const PartitionID from = partitioned_hg.partID(u);

  // We only compute the gain to adjacent blocks of a node and initialize them here.
  // The gain to non-adjacent blocks is -inf.
  for ( const PartitionID& to : _adjacent_blocks.connectivitySet(u) ) {
    benefit_aggregator[to] = 0;
  }

  for ( const HyperedgeID& he : partitioned_hg.incidentEdges(u) ) {
    const HyperedgeWeight edge_weight = partitioned_hg.edgeWeight(he);
    ds::Bitset& connectivity_set = partitioned_hg.deepCopyOfConnectivitySet(he);

    const HyperedgeWeight current_distance = target_graph.distance(connectivity_set);
    if ( partitioned_hg.pinCountInPart(he, from) == 1 ) {
      // Moving the node out of its current block removes
      // its block from the connectivity set
      connectivity_set.unset(from);
    }
    // Compute gain to all adjacent blocks
    for ( const PartitionID& to : _adjacent_blocks.connectivitySet(u) ) {
      const HyperedgeWeight distance_with_to =
        target_graph.distanceWithBlock(connectivity_set, to);
      benefit_aggregator[to] += ( current_distance - distance_with_to ) * edge_weight;
    }
  }

  for ( PartitionID to = 0; to < _k; ++to ) {
    _gain_cache[benefit_index(u, to)].store(benefit_aggregator[to], std::memory_order_relaxed);
    benefit_aggregator[to] = std::numeric_limits<Gain>::min();
  }
}



template<typename PartitionedHypergraph>
void SteinerTreeGainCache::initializeGainCacheEntry(const PartitionedHypergraph& partitioned_hg,
                                                    const HypernodeID hn,
                                                    const PartitionID to,
                                                    ds::Array<SpinLock>& edge_locks) {
  ASSERT(partitioned_hg.hasTargetGraph());
  const TargetGraph& target_graph = *partitioned_hg.targetGraph();
  const HypernodeID from = partitioned_hg.partID(hn);
  vec<uint32_t>& seen_versions = _ets_version.local();
  bool success = false;
  while ( !success ) {
    success = true;
    seen_versions.clear();
    HyperedgeWeight gain = 0;
    for ( const HyperedgeID& he : partitioned_hg.incidentEdges(hn) ) {
      edge_locks[partitioned_hg.uniqueEdgeID(he)].lock();
      // The internal data structures in the partitioned hypergraph are updated
      // in one transaction and each update is assoicated with a version ID. We
      // retrieve here the actual state of the connectivity set of the hyperedge
      // with its version ID. If this version ID changes after the gain computation,
      // we know that we computed the gain on outdated information and retry.
      const uint32_t update_version = _version[he].update_version.load(std::memory_order_relaxed);
      const uint32_t he_version = _version[he].version.load(std::memory_order_relaxed);
      ds::Bitset& connectivity_set = partitioned_hg.deepCopyOfConnectivitySet(he);
      edge_locks[partitioned_hg.uniqueEdgeID(he)].unlock();

      ASSERT(update_version <= he_version);
      if ( update_version < he_version ) {
        // There are still pending gain cache updates that must be finished
        // before we initialize the gain cache entry.
        success = false;
        break;
      }
      seen_versions.push_back(he_version);

      // Now compute gain of moving node hn to block `to` for hyperedge
      const HyperedgeWeight current_distance = target_graph.distance(connectivity_set);
      if ( partitioned_hg.pinCountInPart(he, from) == 1 ) {
        // Moving the node out of its current block removes
        // its block from the connectivity set
        connectivity_set.unset(from);
      }
      const HyperedgeWeight distance_with_to =
        target_graph.distanceWithBlock(connectivity_set, to);
      gain += (current_distance - distance_with_to) * partitioned_hg.edgeWeight(he);
    }
    _gain_cache[benefit_index(hn, to)].store(gain, std::memory_order_relaxed);

    // Check if versions of an incident hyperedge has changed in the meantime.
    // If not, gain cache entry is correct. Otherwise, recompute it.
    if ( success ) {
      ASSERT(seen_versions.size() == UL(partitioned_hg.nodeDegree(hn)),
        V(hn) << V(seen_versions.size()) << V(partitioned_hg.nodeDegree(hn)));
      size_t idx = 0;
      for ( const HyperedgeID& he : partitioned_hg.incidentEdges(hn) ) {
        if ( seen_versions[idx++] != _version[he].version.load(std::memory_order_relaxed) ) {
          success = false;
          break;
        }
      }
    }
  }
}

template<typename PartitionedHypergraph>
bool SteinerTreeGainCache::verifyTrackedAdjacentBlocksOfNodes(const PartitionedHypergraph& partitioned_hg) const {
  bool success = true;
  vec<HyperedgeID> num_incident_edges(_k, 0);
  for ( const HypernodeID& hn : partitioned_hg.nodes() ) {
    num_incident_edges.assign(_k, 0);
    for ( const HyperedgeID& he : partitioned_hg.incidentEdges(hn) ) {
      if ( partitioned_hg.edgeSize(he) <= _large_he_threshold ) {
        for ( const PartitionID& block : partitioned_hg.connectivitySet(he) ) {
          ++num_incident_edges[block];
        }
      }
    }

    for ( PartitionID block = 0; block < _k; ++block ) {
      if ( _num_incident_edges_of_block[benefit_index(hn, block)] != num_incident_edges[block] )  {
        LOG << "Number of incident edges of node" << hn << "to block" << block << "=>"
            << "Expected:" << num_incident_edges[block] << ","
            << "Actual:" << _num_incident_edges_of_block[benefit_index(hn, block)];
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
#define STEINER_TREE_INITIALIZE_GAIN_CACHE(X) void SteinerTreeGainCache::initializeGainCache(const X&)
#define STEINER_TREE_INITIALIZE_GAIN_CACHE_FOR_NODE(X) void SteinerTreeGainCache::initializeGainCacheEntryForNode(const X&,          \
                                                                                                                  const HypernodeID)
#define STEINER_TREE_NOTIFY(X) void SteinerTreeGainCache::notifyBeforeDeltaGainUpdate(const X&,                     \
                                                                                      const SynchronizedEdgeUpdate&)
#define STEINER_TREE_DELTA_GAIN_UPDATE(X) void SteinerTreeGainCache::deltaGainUpdate(const X&,                     \
                                                                                     const SynchronizedEdgeUpdate&)
#define STEINER_TREE_RESTORE_UPDATE(X) void SteinerTreeGainCache::uncontractUpdateAfterRestore(const X&,          \
                                                                                               const HypernodeID, \
                                                                                               const HypernodeID, \
                                                                                               const HyperedgeID, \
                                                                                               const HypernodeID)
#define STEINER_TREE_REPLACEMENT_UPDATE(X) void SteinerTreeGainCache::uncontractUpdateAfterReplacement(const X&,            \
                                                                                                       const HypernodeID,   \
                                                                                                       const HypernodeID,   \
                                                                                                       const HyperedgeID)
#define STEINER_TREE_RESTORE_IDENTICAL_HYPEREDGE(X) void SteinerTreeGainCache::restoreIdenticalHyperedge(const X&,            \
                                                                                                         const HyperedgeID)
#define STEINER_TREE_INIT_ADJACENT_BLOCKS(X) void SteinerTreeGainCache::initializeAdjacentBlocks(const X&)
#define STEINER_TREE_INIT_ADJACENT_BLOCKS_OF_NODE(X) void SteinerTreeGainCache::initializeAdjacentBlocksOfNode(const X&,          \
                                                                                                               const HypernodeID)
#define STEINER_TREE_UPDATE_ADJACENT_BLOCKS(X) void SteinerTreeGainCache::updateAdjacentBlocks(const X&,                     \
                                                                                               const SynchronizedEdgeUpdate&)
#define STEINER_TREE_INIT_GAIN_CACHE_ENTRY(X) void SteinerTreeGainCache::initializeGainCacheEntryForNode(const X&,           \
                                                                                                         const HypernodeID,  \
                                                                                                         vec<Gain>&)
#define STEINER_TREE_INIT_LAZY_GAIN_CACHE_ENTRY(X) void SteinerTreeGainCache::initializeGainCacheEntry(const X&,             \
                                                                                                       const HypernodeID,    \
                                                                                                       const PartitionID,    \
                                                                                                       ds::Array<SpinLock>&)
#define STEINER_TREE_VERIFY_ADJACENT_BLOCKS(X) bool SteinerTreeGainCache::verifyTrackedAdjacentBlocksOfNodes(const X&) const
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
