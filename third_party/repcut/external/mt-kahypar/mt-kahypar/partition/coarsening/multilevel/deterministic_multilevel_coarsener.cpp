/*******************************************************************************
 * MIT License
 *
 * This file is part of Mt-KaHyPar.
 *
 * Copyright (C) 2021 Lars Gottesbüren <lars.gottesbueren@kit.edu>
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

#include "repcut_serial.h"

#include "deterministic_multilevel_coarsener.h"

#include <atomic>

#include <tbb/parallel_sort.h>

#include "mt-kahypar/definitions.h"
#include "mt-kahypar/partition/coarsening/policies/rating_fixed_vertex_acceptance_policy.h"
#include "mt-kahypar/utils/hash.h"

namespace mt_kahypar {

static size_t align_to_next_power_of_two(const size_t size) {
  return std::pow(2.0, std::ceil(std::log2(static_cast<double>(size))));
}

template<typename TypeTraits>
DeterministicMultilevelCoarsener<TypeTraits>::DeterministicMultilevelCoarsener(mt_kahypar_hypergraph_t hypergraph,
                                                                               const Context& context,
                                                                               uncoarsening_data_t* uncoarseningData) :
  Base(utils::cast<Hypergraph>(hypergraph),
        context,
        uncoarsening::to_reference<TypeTraits>(uncoarseningData)),
  config(context),
  initial_num_nodes(utils::cast<Hypergraph>(hypergraph).initialNumNodes()),
  propositions(),
  cluster_weight(),
  opportunistic_cluster_weight(),
  nodes_in_too_heavy_clusters(),
  default_rating_maps(utils::cast<Hypergraph>(hypergraph).initialNumNodes()),
  cache_efficient_rating_maps(0.0),
  pass(0),
  progress_bar(utils::cast<Hypergraph>(hypergraph).initialNumNodes(), 0, false),
  cluster_weights_to_fix(),
  bloom_filter_mask(0),
  bloom_filters() {

  // Initialize internal data structures parallel
  tbb::parallel_invoke([&] {
    propositions.resize(_hg.initialNumNodes());
  }, [&] {
    cluster_weight.resize(_hg.initialNumNodes(), 0);
  }, [&] {
    opportunistic_cluster_weight.resize(_hg.initialNumNodes(), 0);
  }, [&] {
    nodes_in_too_heavy_clusters.adapt_capacity(_hg.initialNumNodes());
  }, [&] {
    cluster_weights_to_fix.adapt_capacity(_hg.initialNumNodes());
  });
  initializeEdgeDeduplication();
}

template<typename TypeTraits>
bool DeterministicMultilevelCoarsener<TypeTraits>::coarseningPassImpl() {
  auto& timer = utils::Utilities::instance().getTimer(_context.utility_id);
  const auto pass_start_time = std::chrono::high_resolution_clock::now();

  timer.start_timer("coarsening_pass", "Clustering");
  const Hypergraph& hg = Base::currentHypergraph();
  HypernodeID num_nodes = Base::currentNumNodes();
  const double num_nodes_before_pass = num_nodes;

  vec<HypernodeID> clusters(num_nodes, kInvalidHypernode);
  tbb::parallel_for(ID(0), num_nodes, [&](HypernodeID u) {
    cluster_weight[u] = hg.nodeWeight(u);
    opportunistic_cluster_weight[u] = cluster_weight[u];
    propositions[u] = u;
    clusters[u] = u;
  });

  ds::FixedVertexSupport<Hypergraph> fixed_vertices = hg.copyOfFixedVertexSupport();
  fixed_vertices.setMaxBlockWeight(_context.partition.max_part_weights);

  permutation.random_grouping(num_nodes, _context.shared_memory.static_balancing_work_packages, config.prng());
  for (size_t sub_round = 0; sub_round < config.num_sub_rounds && num_nodes > currentLevelContractionLimit(); ++sub_round) {
    auto [first_bucket, last_bucket] = parallel::chunking::bounds(
      sub_round, config.num_buckets, config.num_buckets_per_sub_round);
    size_t first = permutation.bucket_bounds[first_bucket], last = permutation.bucket_bounds[last_bucket];

    if (hg.hasFixedVertices()) {
      clusterNodesInRange<true>(clusters, num_nodes, first, last, fixed_vertices);
    } else {
      clusterNodesInRange<false>(clusters, num_nodes, first, last, fixed_vertices);
    }
  }
  timer.stop_timer("coarsening_pass");

  ++pass;
  if (num_nodes_before_pass / num_nodes <= _context.coarsening.minimum_shrink_factor) {
    return false;
  }
  _timer.start_timer("contraction", "Contraction");
  _uncoarseningData.performMultilevelContraction(std::move(clusters), true /* deterministic */, pass_start_time);
  _timer.stop_timer("contraction");
  return true;
}

template<typename TypeTraits>
template<bool has_fixed_vertices>
void DeterministicMultilevelCoarsener<TypeTraits>::clusterNodesInRange(vec<HypernodeID>& clusters,
                                                                       HypernodeID& num_nodes,
                                                                       size_t first,
                                                                       size_t last,
                                                                       ds::FixedVertexSupport<Hypergraph>& fixed_vertices) {
  const Hypergraph& hg = Base::currentHypergraph();

  // each vertex finds a cluster it wants to join
  tbb::parallel_for(first, last, [&](size_t pos) {
    const HypernodeID u = permutation.at(pos);
    if (cluster_weight[u] == hg.nodeWeight(u) && hg.nodeIsEnabled(u)) {
      if (useLargeRatingMapForRatingOfHypernode(hg, u)) {
        calculatePreferredTargetCluster<has_fixed_vertices>(u, clusters, default_rating_maps.local(), fixed_vertices);
      } else {
        // note: the cache efficient rating map is still deterministic since its size (and thus the iteration order) never changes
        calculatePreferredTargetCluster<has_fixed_vertices>(u, clusters, cache_efficient_rating_maps.local(), fixed_vertices);
      }
    }
  });

  if (_context.coarsening.det_resolve_swaps) {
    handleNodeSwaps(first, last, hg);
  }

  tbb::enumerable_thread_specific<size_t> num_contracted_nodes{ 0 };
  // already approve if we can grant all requests for proposed cluster
  // otherwise insert to shared vector so that we can group vertices by cluster
  tbb::parallel_for(first, last, [&](size_t pos) {
    HypernodeID u = permutation.at(pos);
    HypernodeID target = propositions[u];
    if (target != u) {
      if (opportunistic_cluster_weight[target] <= _context.coarsening.max_allowed_node_weight) {
        // if other nodes joined cluster u but u itself leaves for a different cluster, it doesn't count
        if (opportunistic_cluster_weight[u] == hg.nodeWeight(u)) {
          num_contracted_nodes.local() += 1;
        } else {
          cluster_weights_to_fix.push_back_buffered(u);
        }
        if constexpr (has_fixed_vertices) {
          bool success = fixed_vertices.contractWithoutChains(target, u);
          ASSERT(success); unused(success);
        }
        clusters[u] = target;
        cluster_weight[target] = opportunistic_cluster_weight[target];
      } else {
        if (opportunistic_cluster_weight[u] != hg.nodeWeight(u)) {
          // node u could still not move
          cluster_weights_to_fix.push_back_buffered(u);
        }
        nodes_in_too_heavy_clusters.push_back_buffered(u);
      }
    }
  });

  num_nodes -= num_contracted_nodes.combine(std::plus<>());
  nodes_in_too_heavy_clusters.finalize();
  if (nodes_in_too_heavy_clusters.size() > 0) {
    num_nodes -= approveNodes<has_fixed_vertices>(clusters, fixed_vertices);
    nodes_in_too_heavy_clusters.clear();
  }

  cluster_weights_to_fix.finalize();
  if (cluster_weights_to_fix.size() > 0) {
    tbb::parallel_for(UL(0), cluster_weights_to_fix.size(), [&](const size_t i) {
      const HypernodeID hn = cluster_weights_to_fix[i];
      const HypernodeID cluster = clusters[hn];
      if (cluster != hn) {
        cluster_weight[hn] -= hg.nodeWeight(hn);
        opportunistic_cluster_weight[hn] -= hg.nodeWeight(hn);
      }
    });
    cluster_weights_to_fix.clear();
  }

  HEAVY_COARSENING_ASSERT([&] {
    vec<HypernodeWeight> cluster_weight_recalced(cluster_weight.size(), 0);
    for (const HypernodeID hn : hg.nodes()) {
      const HypernodeID cluster = clusters[hn];
      cluster_weight_recalced[cluster] += hg.nodeWeight(hn);
    }
    for (const HypernodeID c : hg.nodes()) {
      if (cluster_weight_recalced[c] > 0 && (cluster_weight_recalced[c] != cluster_weight[c] || cluster_weight_recalced[c] != opportunistic_cluster_weight[c])) {
        LOG << "Wrong cluster weight: " << V(cluster_weight_recalced[c]) << ", " << V(cluster_weight[c]) << ", " << V(opportunistic_cluster_weight[c]);
        return false;
      }
    }
    return true;
  }(), "Clustering calculated wrong cluster-weights/opportunistic-cluster-weights");
}

template<typename TypeTraits>
template<bool has_fixed_vertices, typename RatingMap>
void DeterministicMultilevelCoarsener<TypeTraits>::calculatePreferredTargetCluster(HypernodeID u,
                                                                                   const vec<HypernodeID>& clusters,
                                                                                   RatingMap& tmp_ratings,
                                                                                   const ds::FixedVertexSupport<Hypergraph>& fixed_vertices) {
  const Hypergraph& hg = Base::currentHypergraph();
  tmp_ratings.clear();

  // calculate ratings
  if constexpr (Hypergraph::is_graph) {
    for (HyperedgeID he : hg.incidentEdges(u)) {
      double he_score = static_cast<double>(hg.edgeWeight(he));
      const HypernodeID representative = clusters[hg.edgeTarget(he)];
      tmp_ratings[representative] += he_score;
    }
  } else {
    auto& bloom_filter = bloom_filters.local();
    for (HyperedgeID he : hg.incidentEdges(u)) {
      HypernodeID he_size = hg.edgeSize(he);
      if (he_size < _context.partition.ignore_hyperedge_size_threshold) {
        double he_score = static_cast<double>(hg.edgeWeight(he)) / he_size;
        for (HypernodeID v : hg.pins(he)) {
          const HypernodeID target = clusters[v];
          const HypernodeID bloom_rep = target & bloom_filter_mask;
          if (!bloom_filter[bloom_rep]) {
            tmp_ratings[target] += he_score;
            bloom_filter.set(bloom_rep, true);
          }
        }
        bloom_filter.reset();
      }
    }
  }

  // find highest rated, feasible cluster
  const PartitionID comm_u = hg.communityID(u);
  const HypernodeWeight weight_u = hg.nodeWeight(u);
  vec<HypernodeID>& best_targets = ties.local();
  double best_score = 0.0;

  for (const auto& entry : tmp_ratings) {
    HypernodeID target_cluster = entry.key;
    double target_score = entry.value;
    bool accept_fixed_vertex_contraction = true;
    if constexpr ( has_fixed_vertices ) {
      accept_fixed_vertex_contraction = FixedVertexAcceptancePolicy::acceptContraction(hg, fixed_vertices, _context, u, target_cluster);
    }

    if (target_score >= best_score && target_cluster != u && hg.communityID(target_cluster) == comm_u
        && cluster_weight[target_cluster] + weight_u <= _context.coarsening.max_allowed_node_weight
        && accept_fixed_vertex_contraction) {
      if (target_score > best_score) {
        best_targets.clear();
        best_score = target_score;
      }
      best_targets.push_back(target_cluster);
    }
  }

  HypernodeID best_target;
  if (best_targets.size() == 1) {
    best_target = best_targets[0];
  } else if (best_targets.empty()) {
    best_target = u;
  } else {
    hashing::SimpleIntHash<uint32_t> sih;
    hashing::HashRNG<hashing::SimpleIntHash<uint32_t>> hash_prng(sih, u);
    size_t pos = std::uniform_int_distribution<uint32_t>(0, best_targets.size() - 1)(hash_prng);
    ASSERT(pos < best_targets.size());
    best_target = best_targets[pos];
  }
  best_targets.clear();

  if (best_target != u) {
    propositions[u] = best_target;
    repcut_serial::Ref(opportunistic_cluster_weight[best_target]).fetch_add(hg.nodeWeight(u), std::memory_order_relaxed);
  }
}

template<typename TypeTraits>
template<bool has_fixed_vertices>
size_t DeterministicMultilevelCoarsener<TypeTraits>::approveNodes(vec<HypernodeID>& clusters, ds::FixedVertexSupport<Hypergraph>& fixed_vertices) {
  const Hypergraph& hg = Base::currentHypergraph();
  tbb::enumerable_thread_specific<size_t> num_contracted_nodes { 0 };

  // group vertices by desired cluster, if their cluster is too heavy. approve the lower weight nodes first
  auto comp = [&](HypernodeID lhs, HypernodeID rhs) {
    HypernodeWeight wl = hg.nodeWeight(lhs), wr = hg.nodeWeight(rhs);
    return std::tie(propositions[lhs], wl, lhs) < std::tie(propositions[rhs], wr, rhs);
  };
  tbb::parallel_sort(nodes_in_too_heavy_clusters.begin(), nodes_in_too_heavy_clusters.end(), comp);

  tbb::parallel_for(UL(0), nodes_in_too_heavy_clusters.size(), [&](size_t pos) {
    HypernodeID target = propositions[nodes_in_too_heavy_clusters[pos]];
    // the first vertex for this cluster handles the approval
    size_t num_contracted_local = 0;
    if (pos == 0 || propositions[nodes_in_too_heavy_clusters[pos - 1]] != target) {
      HypernodeWeight target_weight = cluster_weight[target];
      size_t first_rejected = pos;
      // could be parallelized without extra memory but factor 2 work overhead and log(n) depth via binary search
      for (; ; ++first_rejected) {
        // we know that this cluster is too heavy, so the loop will terminate before
        ASSERT(first_rejected < nodes_in_too_heavy_clusters.size());
        ASSERT(propositions[nodes_in_too_heavy_clusters[first_rejected]] == target);
        HypernodeID v = nodes_in_too_heavy_clusters[first_rejected];
        if (target_weight + hg.nodeWeight(v) > _context.coarsening.max_allowed_node_weight) {
          break;
        }
        if constexpr (has_fixed_vertices) {
          bool success = fixed_vertices.contractWithoutChains(target, v);
          ASSERT(success); unused(success);
        }
        clusters[v] = target;
        target_weight += hg.nodeWeight(v);
        if (opportunistic_cluster_weight[v] == hg.nodeWeight(v)) {
          num_contracted_local += 1;
        }
      }
      cluster_weight[target] = target_weight;
      opportunistic_cluster_weight[target] = target_weight;
      num_contracted_nodes.local() += num_contracted_local;
    }
  });

  return num_contracted_nodes.combine(std::plus<>());
}

template<typename TypeTraits>
void DeterministicMultilevelCoarsener<TypeTraits>::handleNodeSwaps(const size_t first, const size_t last, const Hypergraph& hg) {
  tbb::parallel_for(first, last, [&](size_t pos) {
    const HypernodeID u = permutation.at(pos);
    const HypernodeID v = propositions[u];
    if (u < v && u == propositions[v]) {
      const HypernodeID target = opportunistic_cluster_weight[u] > opportunistic_cluster_weight[v] ? u : v;
      const HypernodeID source = target == u ? v : u;
      propositions[u] = target;
      propositions[v] = target;
      opportunistic_cluster_weight[source] -= hg.nodeWeight(target);
    }
  });
}

template<typename TypeTraits>
bool DeterministicMultilevelCoarsener<TypeTraits>::useLargeRatingMapForRatingOfHypernode(const Hypergraph& hypergraph, const HypernodeID u) {
  const size_t cache_efficient_map_size = CacheEfficientRatingMap::MAP_SIZE;

  // In case the current number of nodes is smaller than size
  // of the cache-efficient sparse map, the large tmp rating map
  // consumes less memory
  if (Base::currentNumNodes() < cache_efficient_map_size) {
    return true;
  }

  // If the number of estimated neighbors is greater than the size of the cache efficient rating map / 3, we
  // use the large sparse map. The division by 3 also ensures that the fill grade
  // of the cache efficient sparse map would be small enough such that linear probing
  // is fast.
  if constexpr (Hypergraph::is_graph) {
    return hypergraph.nodeDegree(u) > cache_efficient_map_size / 3UL;
  } else {
    // Compute estimation for the upper bound of neighbors of u
    HypernodeID ub_neighbors_u = 0;
    for (const HyperedgeID& he : hypergraph.incidentEdges(u)) {
      const HypernodeID edge_size = hypergraph.edgeSize(he);
      // Ignore large hyperedges
      ub_neighbors_u += edge_size < _context.partition.ignore_hyperedge_size_threshold ? edge_size : 0;
      if (ub_neighbors_u > cache_efficient_map_size / 3UL) {
        return true;
      }
    }
    return false;
  }
}

template<typename TypeTraits>
void DeterministicMultilevelCoarsener<TypeTraits>::initializeEdgeDeduplication() {
  if constexpr (!Hypergraph::is_graph) {
    size_t max_edge_size = _hg.maxEdgeSize();
    bloom_filter_mask = align_to_next_power_of_two(std::min<size_t>(10 * max_edge_size, initial_num_nodes)) - 1;
    bloom_filters = tbb::enumerable_thread_specific<kahypar::ds::FastResetFlagArray<>>(bloom_filter_mask + 1);
  }
}

INSTANTIATE_CLASS_WITH_TYPE_TRAITS(DeterministicMultilevelCoarsener)

}
