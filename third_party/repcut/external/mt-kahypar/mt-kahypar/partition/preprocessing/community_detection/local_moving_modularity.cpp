/*******************************************************************************
 * MIT License
 *
 * This file is part of Mt-KaHyPar.
 *
 * Copyright (C) 2020 Lars Gottesbüren <lars.gottesbueren@kit.edu>
 * Copyright (C) 2020 Tobias Heuer <tobias.heuer@kit.edu>
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

#include "local_moving_modularity.h"

#include "mt-kahypar/definitions.h"
#include "mt-kahypar/utils/timer.h"
#include "mt-kahypar/utils/floating_point_comparisons.h"
#include "mt-kahypar/parallel/stl/thread_locals.h"

#include <tbb/parallel_reduce.h>
#include <tbb/parallel_sort.h>

namespace mt_kahypar::metrics {

double modularity(const Graph& graph, const ds::Clustering& communities) {
  ASSERT(graph.canBeUsed());
  ASSERT(graph.numNodes() == communities.size());
  vec<NodeID> nodes(graph.numNodes());
  vec<double> cluster_mod(graph.numNodes(), 0.0);

  // make summation order deterministic!
  tbb::parallel_for(UL(0), graph.numNodes(), [&](size_t pos) {
    nodes[pos] = pos;
  });
  tbb::parallel_sort(nodes.begin(), nodes.end(), [&](NodeID lhs, NodeID rhs) {
    return std::tie(communities[lhs], lhs) < std::tie(communities[rhs], rhs);
  });

  // deterministic reduce doesn't have dynamic load balancing --> precompute the contributions and then sum them
  tbb::parallel_for(UL(0), graph.numNodes(), [&](size_t pos) {
    NodeID x = nodes[pos];
    PartitionID comm = communities[x];
    double comm_vol = 0.0, internal = 0.0;
    if (pos == 0 || communities[nodes[pos - 1]] != comm) {
      for (size_t i = pos; i < nodes.size() && communities[nodes[i]] == comm; ++i) {
        NodeID u = nodes[i];
        comm_vol += graph.nodeVolume(u);
        for (const Arc& arc : graph.arcsOf(u)) {
          if (communities[arc.head] != comm) {
            internal -= arc.weight;
          }
        }
      }
      internal += comm_vol;
      cluster_mod[comm] = internal - (comm_vol * comm_vol) / graph.totalVolume();
    }
  });

  auto r = tbb::blocked_range<size_t>(UL(0), graph.numNodes(), 1000);
  auto combine_range = [&](const tbb::blocked_range<size_t>& r, double partial) {
    return std::accumulate(cluster_mod.begin() + r.begin(), cluster_mod.begin() + r.end(), partial);
  };
  return tbb::parallel_deterministic_reduce(r, 0.0, combine_range, std::plus<>()) / graph.totalVolume();
}

}

namespace mt_kahypar::community_detection {

bool ParallelLocalMovingModularity::localMoving(Graph& graph, ds::Clustering& communities) {
  ASSERT(graph.canBeUsed());
  _max_degree = graph.max_degree();
  _reciprocal_total_volume = 1.0 / graph.totalVolume();
  _vol_multiplier_div_by_node_vol = _reciprocal_total_volume;

  // init
  if (_context.partition.deterministic) {
    tbb::parallel_for(UL(0), graph.numNodes(), [&](NodeID u) {
      communities[u] = u;
      _cluster_volumes[u].store(graph.nodeVolume(u), std::memory_order_relaxed);
    });
  } else {
    auto& nodes = permutation.permutation;
    nodes.resize(graph.numNodes());
    tbb::parallel_for(ID(0), static_cast<NodeID>(graph.numNodes()), [&](const NodeID u) {
      nodes[u] = u;
      communities[u] = u;
      _cluster_volumes[u].store(graph.nodeVolume(u), std::memory_order_relaxed);
    });
  }

  DBG << "Louvain level" << V(graph.numNodes()) << V(graph.numArcs());

  // local moving
  bool clustering_changed = false;
  if ( graph.numArcs() > 0 ) {
    size_t number_of_nodes_moved = graph.numNodes();
    for (size_t round = 0;
        number_of_nodes_moved >= _context.preprocessing.community_detection.min_vertex_move_fraction * graph.numNodes()
        && round < _context.preprocessing.community_detection.max_pass_iterations; round++) {
      if (_context.partition.deterministic) {
        number_of_nodes_moved = synchronousParallelRound(graph, communities);
      } else {
        number_of_nodes_moved = parallelNonDeterministicRound(graph, communities);
      }
      clustering_changed |= number_of_nodes_moved > 0;
      DBG << "Louvain-Pass #" << round << " - num moves " << number_of_nodes_moved << " - Modularity:" << metrics::modularity(graph, communities);
    }
  }
  return clustering_changed;
}

size_t ParallelLocalMovingModularity::synchronousParallelRound(const Graph& graph, ds::Clustering& communities) {
  if (graph.numNodes() < 200) {
    return sequentialRound(graph, communities);
  }

  size_t seed = prng();
  permutation.random_grouping(graph.numNodes(), _context.shared_memory.static_balancing_work_packages, seed);
  size_t num_moved_nodes = 0;
  constexpr size_t num_buckets = utils::ParallelPermutation<HypernodeID>::num_buckets;
  const size_t num_sub_rounds = _context.preprocessing.community_detection.num_sub_rounds_deterministic;
  size_t num_buckets_per_sub_round = parallel::chunking::idiv_ceil(num_buckets, num_sub_rounds);

  size_t max_round_size = 0;
  for (size_t sub_round = 0; sub_round < num_sub_rounds; ++sub_round) {
    auto [first_bucket, last_bucket] = parallel::chunking::bounds(sub_round, num_buckets, num_buckets_per_sub_round);
    max_round_size = std::max(max_round_size,
                              size_t(permutation.bucket_bounds[last_bucket] - permutation.bucket_bounds[first_bucket]));
  }
  volume_updates_to.adapt_capacity(max_round_size);
  volume_updates_from.adapt_capacity(max_round_size);

  for (size_t sub_round = 0; sub_round < num_sub_rounds; ++sub_round) {
    auto [first_bucket, last_bucket] = parallel::chunking::bounds(sub_round, num_buckets, num_buckets_per_sub_round);
    assert(first_bucket < last_bucket && last_bucket < permutation.bucket_bounds.size());
    size_t first = permutation.bucket_bounds[first_bucket];
    size_t last = permutation.bucket_bounds[last_bucket];

    tbb::enumerable_thread_specific<size_t> num_moved_local(0);
    tbb::parallel_for(first, last, [&](size_t pos) {
      HypernodeID u = permutation.at(pos);
      PartitionID best_cluster = computeMaxGainCluster(graph, communities, u);
      if (best_cluster != communities[u]) {
        volume_updates_from.push_back_buffered({ communities[u], u });
        volume_updates_to.push_back_buffered({best_cluster, u });
        num_moved_local.local() += 1;
      }
    });

    size_t num_moved_sub_round = num_moved_local.combine(std::plus<>());
    num_moved_nodes += num_moved_sub_round;

    // We can't do atomic adds of the volumes since they're not commutative and thus lead to non-deterministic decisions
    // Instead we sort the updates, and for each cluster let one thread sum up the updates.
    tbb::parallel_invoke([&] {
      volume_updates_to.finalize();
      tbb::parallel_sort(volume_updates_to.begin(), volume_updates_to.end());
    }, [&] {
      volume_updates_from.finalize();
      tbb::parallel_sort(volume_updates_from.begin(), volume_updates_from.end());
    });

    const size_t sz_to = volume_updates_to.size();
    tbb::parallel_for(UL(0), sz_to, [&](size_t pos) {
      PartitionID c = volume_updates_to[pos].cluster;
      if (pos == 0 || volume_updates_to[pos - 1].cluster != c) {
        ArcWeight vol_delta = 0.0;
        for ( ; pos < sz_to && volume_updates_to[pos].cluster == c; ++pos) {
          vol_delta += graph.nodeVolume(volume_updates_to[pos].node);
          communities[volume_updates_to[pos].node] = c;
        }
        _cluster_volumes[c].store(_cluster_volumes[c].load(std::memory_order_relaxed) + vol_delta, std::memory_order_relaxed);
      }
    });
    volume_updates_to.clear();

    const size_t sz_from = volume_updates_from.size();
    tbb::parallel_for(UL(0), sz_from, [&](size_t pos) {
      PartitionID c = volume_updates_from[pos].cluster;
      if (pos == 0 || volume_updates_from[pos - 1].cluster != c) {
        ArcWeight vol_delta = 0.0;
        for ( ; pos < sz_from && volume_updates_from[pos].cluster == c; ++pos) {
          vol_delta -= graph.nodeVolume(volume_updates_from[pos].node);
        }
        _cluster_volumes[c].store(_cluster_volumes[c].load(std::memory_order_relaxed) + vol_delta, std::memory_order_relaxed);
      }
    });
    volume_updates_from.clear();
  }

  return num_moved_nodes;
}

size_t ParallelLocalMovingModularity::sequentialRound(const Graph& graph, ds::Clustering& communities) {
  size_t seed = prng();
  permutation.sequential_fallback(graph.numNodes(), seed);
  size_t num_moved = 0;
  for (size_t i = 0; i < graph.numNodes(); ++i) {
    NodeID u = permutation.at(i);
    PartitionID best_cluster = computeMaxGainCluster(graph, communities, u);
    if (best_cluster != communities[u]) {
      _cluster_volumes[best_cluster] += graph.nodeVolume(u);
      _cluster_volumes[communities[u]] -= graph.nodeVolume(u);
      communities[u] = best_cluster;
      num_moved++;
    }
  }
  return num_moved;
}

size_t ParallelLocalMovingModularity::parallelNonDeterministicRound(const Graph& graph, ds::Clustering& communities) {
  auto& nodes = permutation.permutation;
  if ( !_disable_randomization ) {
    utils::Randomize::instance().parallelShuffleVector(nodes, UL(0), nodes.size());
  }

  tbb::enumerable_thread_specific<size_t> local_number_of_nodes_moved(0);
  auto moveNode = [&](const NodeID u) {
    const ArcWeight volU = graph.nodeVolume(u);
    const PartitionID from = communities[u];
    PartitionID best_cluster = computeMaxGainCluster(graph, communities, u);
    if (best_cluster != from) {
      _cluster_volumes[best_cluster] += volU;
      _cluster_volumes[from] -= volU;
      communities[u] = best_cluster;
      ++local_number_of_nodes_moved.local();
    }
  };

#ifdef KAHYPAR_ENABLE_HEAVY_PREPROCESSING_ASSERTIONS
  std::for_each(nodes.begin(), nodes.end(), moveNode);
#else
  tbb::parallel_for(UL(0), nodes.size(), [&](size_t i) { moveNode(nodes[i]); });
#endif
  size_t number_of_nodes_moved = local_number_of_nodes_moved.combine(std::plus<>());
  return number_of_nodes_moved;
}

bool ParallelLocalMovingModularity::verifyGain(const Graph& graph, const ds::Clustering& communities, const NodeID u,
                                                           const PartitionID to, double gain, double weight_from, double weight_to) {
  if (_context.partition.deterministic) {
    // the check is omitted, since changing the cluster volumes breaks determinism
    return true;
  }

  const PartitionID from = communities[u];

  long double adjustedGain = adjustAdvancedModGain(gain, weight_from, _cluster_volumes[from], graph.nodeVolume(u));
  const double volMultiplier = _vol_multiplier_div_by_node_vol * graph.nodeVolume(u);
  double modGain = modularityGain(weight_to, _cluster_volumes[to], volMultiplier);
  long double adjustedGainRecomputed = adjustAdvancedModGain(modGain, weight_from, _cluster_volumes[from], graph.nodeVolume(u));
  unused(adjustedGainRecomputed);

  if (from == to) {
    adjustedGainRecomputed = 0.0L;
    adjustedGain = 0.0L;
  }

  ASSERT(adjustedGain == adjustedGainRecomputed);

  long double dTotalVolumeSquared = static_cast<long double>(graph.totalVolume()) * static_cast<long double>(graph.totalVolume());

  auto accBeforeMove = intraClusterWeightsAndSumOfSquaredClusterVolumes(graph, communities);
  long double coverageBeforeMove = static_cast<long double>(accBeforeMove.first) / graph.totalVolume();
  long double expectedCoverageBeforeMove = accBeforeMove.second / dTotalVolumeSquared;
  long double modBeforeMove = coverageBeforeMove - expectedCoverageBeforeMove;

  // apply move
  ds::Clustering communities_after_move = communities;
  communities_after_move[u] = to;
  _cluster_volumes[to] += graph.nodeVolume(u);
  _cluster_volumes[from] -= graph.nodeVolume(u);

  auto accAfterMove = intraClusterWeightsAndSumOfSquaredClusterVolumes(graph, communities_after_move);
  long double coverageAfterMove = static_cast<long double>(accAfterMove.first) / graph.totalVolume();
  long double expectedCoverageAfterMove = accAfterMove.second / dTotalVolumeSquared;
  long double modAfterMove = coverageAfterMove - expectedCoverageAfterMove;

  const bool result = math::are_almost_equal_ld(modBeforeMove + adjustedGain, modAfterMove, 1e-8);
  ASSERT(result,
         V(modBeforeMove + adjustedGain) << V(modAfterMove) << V(gain) << V(adjustedGain)
                                         << V(coverageBeforeMove) << V(expectedCoverageBeforeMove) << V(modBeforeMove)
                                         << V(coverageAfterMove) << V(expectedCoverageAfterMove) << V(modAfterMove));

  _cluster_volumes[to] -= graph.nodeVolume(u);
  _cluster_volumes[from] += graph.nodeVolume(u);

  return result;
}

std::pair<ArcWeight, ArcWeight> ParallelLocalMovingModularity::intraClusterWeightsAndSumOfSquaredClusterVolumes(
        const Graph& graph, const ds::Clustering& communities) {
  ArcWeight intraClusterWeights = 0;
  ArcWeight sumOfSquaredClusterVolumes = 0;
  vec<ArcWeight> cluster_volumes(graph.numNodes(), 0);

  for (NodeID u : graph.nodes()) {
    ArcWeight arcVol = 0;
    for (const Arc& arc : graph.arcsOf(u)) {
      if (communities[u] == communities[arc.head])
        intraClusterWeights += arc.weight;
      arcVol += arc.weight;
    }

    ArcWeight selfLoopWeight = graph.nodeVolume(u) - arcVol;          // already accounted for as twice!
    ASSERT(selfLoopWeight >= 0.0);
    intraClusterWeights += selfLoopWeight;
    cluster_volumes[communities[u]] += graph.nodeVolume(u);
  }

  for (NodeID cluster : graph.nodes()) {      // unused cluster IDs have volume 0
    sumOfSquaredClusterVolumes += cluster_volumes[cluster] * cluster_volumes[cluster];
  }
  return std::make_pair(intraClusterWeights, sumOfSquaredClusterVolumes);
}

void ParallelLocalMovingModularity::initializeClusterVolumes(const Graph& graph, ds::Clustering& communities) {
  _reciprocal_total_volume = 1.0 / graph.totalVolume();
  _vol_multiplier_div_by_node_vol =  _reciprocal_total_volume;
  tbb::parallel_for(ID(0), static_cast<NodeID>(graph.numNodes()), [&](const NodeID u) {
    const PartitionID community_id = communities[u];
    _cluster_volumes[community_id] += graph.nodeVolume(u);
  });
}

ParallelLocalMovingModularity::~ParallelLocalMovingModularity() {
/*
  tbb::parallel_invoke([&] {
    parallel::parallel_free_thread_local_internal_data(
            _local_small_incident_cluster_weight, [&](CacheEfficientIncidentClusterWeights& data) {
              data.freeInternalData();
            });
  }, [&] {
    parallel::parallel_free_thread_local_internal_data(
            _local_large_incident_cluster_weight, [&](LargeIncidentClusterWeights& data) {
              data.freeInternalData();
            });
  }, [&] {
     parallel::free(_cluster_volumes);
  });
*/
}

}
