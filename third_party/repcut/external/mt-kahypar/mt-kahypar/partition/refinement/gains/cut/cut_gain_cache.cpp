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

#include "mt-kahypar/partition/refinement/gains/cut/cut_gain_cache.h"

#include <tbb/parallel_for.h>
#include <tbb/enumerable_thread_specific.h>
#include <tbb/concurrent_vector.h>

#include "mt-kahypar/datastructures/synchronized_edge_update.h"
#include "mt-kahypar/definitions.h"

namespace mt_kahypar {

template<typename PartitionedHypergraph>
void CutGainCache::initializeGainCache(const PartitionedHypergraph& partitioned_hg) {
  ASSERT(!_is_initialized, "Gain cache is already initialized");
  ASSERT(_k <= 0 || _k >= partitioned_hg.k(),
    "Gain cache was already initialized for a different k" << V(_k) << V(partitioned_hg.k()));
  allocateGainTable(partitioned_hg.topLevelNumNodes(), partitioned_hg.k());

  // Gain calculation consist of two stages
  //  1. Compute gain of all low degree vertices
  //  2. Compute gain of all high degree vertices
  tbb::enumerable_thread_specific< vec<HyperedgeWeight> > ets_mtb(_k, 0);
  tbb::concurrent_vector<HypernodeID> high_degree_vertices;
  // Compute gain of all low degree vertices
  tbb::parallel_for(tbb::blocked_range<HypernodeID>(HypernodeID(0), partitioned_hg.initialNumNodes()),
    [&](tbb::blocked_range<HypernodeID>& r) {
      vec<HyperedgeWeight>& benefit_aggregator = ets_mtb.local();
      for (HypernodeID u = r.begin(); u < r.end(); ++u) {
        if ( partitioned_hg.nodeIsEnabled(u)) {
          if ( partitioned_hg.nodeDegree(u) <= HIGH_DEGREE_THRESHOLD) {
            initializeGainCacheEntryForNode(partitioned_hg, u, benefit_aggregator);
          } else {
            // Collect high degree vertices
            high_degree_vertices.push_back(u);
          }
        }
      }
    });

  auto aggregate_contribution_of_he_for_node =
    [&](const PartitionID block_of_u,
        const HyperedgeID he,
        HyperedgeWeight& penalty_aggregator,
        vec<HyperedgeWeight>& benefit_aggregator) {
    const HypernodeID edge_size = partitioned_hg.edgeSize(he);
    if ( edge_size > 1 && partitioned_hg.connectivity(he) <= 2 ) {
      HyperedgeWeight edge_weight = partitioned_hg.edgeWeight(he);
      if (partitioned_hg.pinCountInPart(he, block_of_u) == edge_size) {
        penalty_aggregator += edge_weight;
      }

      for (const PartitionID block : partitioned_hg.connectivitySet(he)) {
        if ( partitioned_hg.pinCountInPart(he, block) == edge_size - 1 ) {
          benefit_aggregator[block] += edge_weight;
        }
      }
    }
  };

  // Compute gain of all high degree vertices
  for ( const HypernodeID& u : high_degree_vertices ) {
    tbb::enumerable_thread_specific<HyperedgeWeight> ets_mfp(0);
    const PartitionID from = partitioned_hg.partID(u);
    const HypernodeID degree_of_u = partitioned_hg.nodeDegree(u);
    tbb::parallel_for(tbb::blocked_range<HypernodeID>(ID(0), degree_of_u),
      [&](tbb::blocked_range<HypernodeID>& r) {
      vec<HyperedgeWeight>& benefit_aggregator = ets_mtb.local();
      HyperedgeWeight& penalty_aggregator = ets_mfp.local();
      size_t current_pos = r.begin();
      for ( const HyperedgeID& he : partitioned_hg.incidentEdges(u, r.begin()) ) {
        aggregate_contribution_of_he_for_node(from, he,
          penalty_aggregator, benefit_aggregator);
        ++current_pos;
        if ( current_pos == r.end() ) {
          break;
        }
      }
    });

    // Aggregate thread locals to compute overall gain of the high degree vertex
    const HyperedgeWeight penalty_term = ets_mfp.combine(std::plus<HyperedgeWeight>());
    _gain_cache[penalty_index(u)].store(penalty_term, std::memory_order_relaxed);
    for (PartitionID p = 0; p < _k; ++p) {
      HyperedgeWeight move_to_benefit = 0;
      for ( auto& l_move_to_benefit : ets_mtb ) {
        move_to_benefit += l_move_to_benefit[p];
        l_move_to_benefit[p] = 0;
      }
      _gain_cache[benefit_index(u, p)].store(move_to_benefit, std::memory_order_relaxed);
    }
  }

  _is_initialized = true;
}

bool CutGainCache::triggersDeltaGainUpdate(const SynchronizedEdgeUpdate& sync_update) {
  return sync_update.pin_count_in_from_part_after == sync_update.edge_size - 1 ||
         sync_update.pin_count_in_from_part_after == sync_update.edge_size - 2 ||
         sync_update.pin_count_in_to_part_after == sync_update.edge_size ||
         sync_update.pin_count_in_to_part_after == sync_update.edge_size - 1;
}


template<typename PartitionedHypergraph>
void CutGainCache::deltaGainUpdate(const PartitionedHypergraph& partitioned_hg,
                                   const SynchronizedEdgeUpdate& sync_update) {
  ASSERT(_is_initialized, "Gain cache is not initialized");
  const HypernodeID edge_size = sync_update.edge_size;
  if ( edge_size > 1 ) {
    const HyperedgeID he = sync_update.he;
    const PartitionID from = sync_update.from;
    const PartitionID to = sync_update.to;
    const HyperedgeWeight edge_weight = sync_update.edge_weight;
    const HypernodeID pin_count_in_from_part_after = sync_update.pin_count_in_from_part_after;
    const HypernodeID pin_count_in_to_part_after = sync_update.pin_count_in_to_part_after;
    if ( pin_count_in_from_part_after == edge_size - 1 ) {
      for ( const HypernodeID& u : partitioned_hg.pins(he) ) {
        ASSERT(nodeGainAssertions(u, from));
        _gain_cache[penalty_index(u)].fetch_sub(edge_weight, std::memory_order_relaxed);
        _gain_cache[benefit_index(u, from)].fetch_add(edge_weight, std::memory_order_relaxed);
      }
    } else if ( pin_count_in_from_part_after == edge_size - 2 ) {
      for ( const HypernodeID& u : partitioned_hg.pins(he) ) {
        ASSERT(nodeGainAssertions(u, from));
        _gain_cache[benefit_index(u, from)].fetch_sub(edge_weight, std::memory_order_relaxed);
      }
    }

    if ( pin_count_in_to_part_after == edge_size ) {
      for ( const HypernodeID& u : partitioned_hg.pins(he) ) {
        ASSERT(nodeGainAssertions(u, to));
        _gain_cache[penalty_index(u)].fetch_add(edge_weight, std::memory_order_relaxed);
        _gain_cache[benefit_index(u, to)].fetch_sub(edge_weight, std::memory_order_relaxed);
      }
    } else if ( pin_count_in_to_part_after == edge_size - 1 ) {
      for ( const HypernodeID& u : partitioned_hg.pins(he) ) {
        ASSERT(nodeGainAssertions(u, to));
        _gain_cache[benefit_index(u, to)].fetch_add(edge_weight, std::memory_order_relaxed);
      }
    }
  }
}

template<typename PartitionedHypergraph>
void CutGainCache::uncontractUpdateAfterRestore(const PartitionedHypergraph& partitioned_hg,
                                                const HypernodeID u,
                                                const HypernodeID v,
                                                const HyperedgeID he,
                                                const HypernodeID pin_count_in_part_after) {
  if ( _is_initialized ) {
    const PartitionID block = partitioned_hg.partID(u);
    const HyperedgeWeight edge_weight = partitioned_hg.edgeWeight(he);
    const HypernodeID edge_size = partitioned_hg.edgeSize(he);

    if ( partitioned_hg.connectivity(he) == 2 ) {
      if ( pin_count_in_part_after == 2 ) {
        // In this case, the hyperedge contains two blocks, while the other block V' (!= block)
        // had |e| - 1 pins before the uncontraction of u and v. Now the size of the hyperedge
        // increased by one while the block of u and v contains two pins (obviously) and the
        // other block |e| - 2. Therefore, we have to subtract w(e) from b(u, V') for all pins
        // in the hyperedge.
        PartitionID other_block = kInvalidPartition;
        for ( const PartitionID other : partitioned_hg.connectivitySet(he) ) {
          if ( other != block ) {
            other_block = other;
            break;
          }
        }

        for ( const HypernodeID& pin : partitioned_hg.pins(he) ) {
          if ( pin != v ) {
            _gain_cache[benefit_index(pin, other_block)].fetch_sub(edge_weight, std::memory_order_relaxed);
          }
        }
      }

      for ( const PartitionID to : partitioned_hg.connectivitySet(he) ) {
        if ( partitioned_hg.pinCountInPart(he, to) == edge_size - 1 ) {
          _gain_cache[benefit_index(v, to)].fetch_add(edge_weight, std::memory_order_relaxed);
        }
      }
    } else if ( pin_count_in_part_after == edge_size ) {
      // In this case, we have to add w(e) to the penalty term of v
      _gain_cache[penalty_index(v)].fetch_add(edge_weight, std::memory_order_relaxed);
      if ( edge_size == 2 ) {
        // Special case: Hyperedge is not a single-pin net anymore. Since we do not consider
        // single-pin nets in the penalty terms, we have to add w(e) to the penalty term of u.
        for ( const HypernodeID& pin : partitioned_hg.pins(he) ) {
          if ( pin != v ) {
            // Note that u may be replaced by another uncontraction.
            _gain_cache[penalty_index(pin)].fetch_add(edge_weight, std::memory_order_relaxed);
          }
        }
      }
    }
  }
}

template<typename PartitionedHypergraph>
void CutGainCache::uncontractUpdateAfterReplacement(const PartitionedHypergraph& partitioned_hg,
                                                    const HypernodeID u,
                                                    const HypernodeID v,
                                                    const HyperedgeID he) {
  if ( _is_initialized ) {
    const HypernodeID edge_size = partitioned_hg.edgeSize(he);
    if ( edge_size > 1 ) {
      const PartitionID block = partitioned_hg.partID(u);
      const HyperedgeWeight edge_weight = partitioned_hg.edgeWeight(he);
      if ( partitioned_hg.pinCountInPart(he, block) == edge_size ) {
        // u is no longer part of the hyperedge => transfer penalty term to v
        _gain_cache[penalty_index(u)].fetch_sub(edge_weight, std::memory_order_relaxed);
        _gain_cache[penalty_index(v)].fetch_add(edge_weight, std::memory_order_relaxed);
      }

      if ( partitioned_hg.connectivity(he) == 2 ) {
        for ( const PartitionID to : partitioned_hg.connectivitySet(he) ) {
          if ( partitioned_hg.pinCountInPart(he, to) == edge_size - 1 ) {
            // u is no longer part of the hyperedge => transfer benefit term to v
            _gain_cache[benefit_index(u, to)].fetch_sub(edge_weight, std::memory_order_relaxed);
            _gain_cache[benefit_index(v, to)].fetch_add(edge_weight, std::memory_order_relaxed);
          }
        }
      }
    }
  }
}

template<typename PartitionedHypergraph>
void CutGainCache::initializeGainCacheEntryForNode(const PartitionedHypergraph& partitioned_hg,
                                                   const HypernodeID u,
                                                   vec<Gain>& benefit_aggregator) {
  PartitionID from = partitioned_hg.partID(u);
  Gain penalty = 0;
  for (const HyperedgeID& e : partitioned_hg.incidentEdges(u)) {
    const HypernodeID edge_size = partitioned_hg.edgeSize(e);
    if ( edge_size > 1 && partitioned_hg.connectivity(e) <= 2 ) {
      HyperedgeWeight ew = partitioned_hg.edgeWeight(e);
      if ( partitioned_hg.pinCountInPart(e, from) == edge_size ) {
        penalty += ew;
      }
      for (const PartitionID& to : partitioned_hg.connectivitySet(e)) {
        if ( partitioned_hg.pinCountInPart(e, to) == edge_size - 1 ) {
          benefit_aggregator[to] += ew;
        }
      }
    }
  }

  _gain_cache[penalty_index(u)].store(penalty, std::memory_order_relaxed);
  for (PartitionID i = 0; i < _k; ++i) {
    _gain_cache[benefit_index(u, i)].store(benefit_aggregator[i], std::memory_order_relaxed);
    benefit_aggregator[i] = 0;
  }
}


namespace {
#define CUT_INITIALIZE_GAIN_CACHE(X) void CutGainCache::initializeGainCache(const X&)
#define CUT_DELTA_GAIN_UPDATE(X) void CutGainCache::deltaGainUpdate(const X&,                     \
                                                                    const SynchronizedEdgeUpdate&)
#define CUT_RESTORE_UPDATE(X) void CutGainCache::uncontractUpdateAfterRestore(const X&,          \
                                                                              const HypernodeID, \
                                                                              const HypernodeID, \
                                                                              const HyperedgeID, \
                                                                              const HypernodeID)
#define CUT_REPLACEMENT_UPDATE(X) void CutGainCache::uncontractUpdateAfterReplacement(const X&,            \
                                                                                      const HypernodeID,   \
                                                                                      const HypernodeID,   \
                                                                                      const HyperedgeID)
#define CUT_INIT_GAIN_CACHE_ENTRY(X) void CutGainCache::initializeGainCacheEntryForNode(const X&,           \
                                                                                        const HypernodeID,  \
                                                                                        vec<Gain>&)
}

INSTANTIATE_FUNC_WITH_PARTITIONED_HG(CUT_INITIALIZE_GAIN_CACHE)
INSTANTIATE_FUNC_WITH_PARTITIONED_HG(CUT_DELTA_GAIN_UPDATE)
INSTANTIATE_FUNC_WITH_PARTITIONED_HG(CUT_RESTORE_UPDATE)
INSTANTIATE_FUNC_WITH_PARTITIONED_HG(CUT_REPLACEMENT_UPDATE)
INSTANTIATE_FUNC_WITH_PARTITIONED_HG(CUT_INIT_GAIN_CACHE_ENTRY)

}  // namespace mt_kahypar
