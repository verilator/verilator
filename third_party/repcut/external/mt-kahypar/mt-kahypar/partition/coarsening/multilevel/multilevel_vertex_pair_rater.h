/*******************************************************************************
 * MIT License
 *
 * This file is part of Mt-KaHyPar.
 *
 * Copyright (C) 2019 Lars Gottesbüren <lars.gottesbueren@kit.edu>
 * Copyright (C) 2019 Tobias Heuer <tobias.heuer@kit.edu>
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
#include <limits>
#include <stack>
#include <vector>

#include <tbb/enumerable_thread_specific.h>

#include "kahypar-resources/datastructure/fast_reset_flag_array.h"
#include "kahypar-resources/meta/mandatory.h"

#include "mt-kahypar/datastructures/sparse_map.h"
#include "mt-kahypar/partition/context.h"
#include "mt-kahypar/partition/coarsening/policies/rating_fixed_vertex_acceptance_policy.h"


namespace mt_kahypar {
class MultilevelVertexPairRater {
  using LargeTmpRatingMap = ds::SparseMap<HypernodeID, RatingType>;
  using CacheEfficientRatingMap = ds::FixedSizeSparseMap<HypernodeID, RatingType>;
  using ThreadLocalCacheEfficientRatingMap = tbb::enumerable_thread_specific<CacheEfficientRatingMap>;
  using ThreadLocalVertexDegreeBoundedRatingMap = tbb::enumerable_thread_specific<CacheEfficientRatingMap>;
  using ThreadLocalLargeTmpRatingMap = tbb::enumerable_thread_specific<LargeTmpRatingMap>;
  using ThreadLocalFastResetFlagArray = tbb::enumerable_thread_specific<kahypar::ds::FastResetFlagArray<> >;

 private:
  static constexpr bool debug = false;

  class VertexPairRating {
   public:
    VertexPairRating(HypernodeID trgt, RatingType val, bool is_valid) :
      target(trgt),
      value(val),
      valid(is_valid) { }

    VertexPairRating() :
      target(std::numeric_limits<HypernodeID>::max()),
      value(std::numeric_limits<RatingType>::min()),
      valid(false) { }

    VertexPairRating(const VertexPairRating&) = delete;
    VertexPairRating & operator= (const VertexPairRating &) = delete;

    VertexPairRating(VertexPairRating&&) = default;
    VertexPairRating & operator= (VertexPairRating &&) = delete;

    HypernodeID target;
    RatingType value;
    bool valid;
  };

  enum class RatingMapType {
    CACHE_EFFICIENT_RATING_MAP,
    VERTEX_DEGREE_BOUNDED_RATING_MAP,
    LARGE_RATING_MAP
  };

  using AtomicWeight = parallel::IntegralAtomicWrapper<HypernodeWeight>;

 public:
  using Rating = VertexPairRating;

  MultilevelVertexPairRater(const HypernodeID num_hypernodes,
                            const HypernodeID max_edge_size,
                            const Context& context) :
    _context(context),
    _current_num_nodes(num_hypernodes),
    _vertex_degree_sampling_threshold(context.coarsening.vertex_degree_sampling_threshold),
    _local_cache_efficient_rating_map(0.0),
    _local_vertex_degree_bounded_rating_map(3UL * _vertex_degree_sampling_threshold, 0.0),
    _local_large_rating_map([&] {
      return construct_large_tmp_rating_map();
    }),
    // Should give a false positive rate < 1%
    _bloom_filter_mask(align_to_next_power_of_two(
      std::min(ID(10) * max_edge_size, _current_num_nodes)) - 1),
    _local_bloom_filter(_bloom_filter_mask + 1),
    _already_matched(num_hypernodes) { }

  MultilevelVertexPairRater(const MultilevelVertexPairRater&) = delete;
  MultilevelVertexPairRater & operator= (const MultilevelVertexPairRater &) = delete;

  MultilevelVertexPairRater(MultilevelVertexPairRater&&) = delete;
  MultilevelVertexPairRater & operator= (MultilevelVertexPairRater &&) = delete;

  template<typename ScorePolicy, typename HeavyNodePenaltyPolicy, typename AcceptancePolicy,
           bool has_fixed_vertices, typename Hypergraph>
  VertexPairRating rate(const Hypergraph& hypergraph,
                        const HypernodeID u,
                        const parallel::scalable_vector<HypernodeID>& cluster_ids,
                        const parallel::scalable_vector<AtomicWeight>& cluster_weight,
                        const ds::FixedVertexSupport<Hypergraph>& fixed_vertices,
                        const HypernodeWeight max_allowed_node_weight) {

    const RatingMapType rating_map_type = getRatingMapTypeForRatingOfHypernode(hypergraph, u);
    if ( rating_map_type == RatingMapType::CACHE_EFFICIENT_RATING_MAP ) {
      return rate<ScorePolicy, HeavyNodePenaltyPolicy, AcceptancePolicy, has_fixed_vertices>(
        hypergraph, u, _local_cache_efficient_rating_map.local(),
        cluster_ids, cluster_weight, fixed_vertices, max_allowed_node_weight, false);
    } else if ( rating_map_type == RatingMapType::VERTEX_DEGREE_BOUNDED_RATING_MAP ) {
      return rate<ScorePolicy, HeavyNodePenaltyPolicy, AcceptancePolicy, has_fixed_vertices>(
        hypergraph, u, _local_vertex_degree_bounded_rating_map.local(),
        cluster_ids, cluster_weight, fixed_vertices, max_allowed_node_weight, true);
    } else {
      LargeTmpRatingMap& large_tmp_rating_map = _local_large_rating_map.local();
      large_tmp_rating_map.setMaxSize(_current_num_nodes);
      return rate<ScorePolicy, HeavyNodePenaltyPolicy, AcceptancePolicy, has_fixed_vertices>(
        hypergraph, u, large_tmp_rating_map,
        cluster_ids, cluster_weight, fixed_vertices, max_allowed_node_weight, false);
    }
  }

  // ! Several threads will mark matches in parallel. However, since
  // ! we only set the corresponding value to true this function is
  // ! thread-safe.
  void markAsMatched(const HypernodeID original_id) {
    _already_matched.set(original_id, true);
  }

  // ! Note, this function is not thread safe
  void resetMatches() {
    _already_matched.reset();
  }

  void setCurrentNumberOfNodes(const HypernodeID current_num_nodes) {
    _current_num_nodes = current_num_nodes;
  }

 private:
  template<typename ScorePolicy, typename HeavyNodePenaltyPolicy, typename AcceptancePolicy,
           bool has_fixed_vertices, typename Hypergraph, typename RatingMap>
  VertexPairRating rate(const Hypergraph& hypergraph,
                        const HypernodeID u,
                        RatingMap& tmp_ratings,
                        const parallel::scalable_vector<HypernodeID>& cluster_ids,
                        const parallel::scalable_vector<AtomicWeight>& cluster_weight,
                        const ds::FixedVertexSupport<Hypergraph>& fixed_vertices,
                        const HypernodeWeight max_allowed_node_weight,
                        const bool use_vertex_degree_sampling) {

    if ( use_vertex_degree_sampling ) {
      fillRatingMapWithSampling<ScorePolicy>(hypergraph, u, tmp_ratings, cluster_ids);
    } else {
      fillRatingMap<ScorePolicy>(hypergraph, u, tmp_ratings, cluster_ids);
    }

    int cpu_id = THREAD_ID;
    const HypernodeWeight weight_u = cluster_weight[u];
    const PartitionID community_u_id = hypergraph.communityID(u);
    RatingType max_rating = std::numeric_limits<RatingType>::min();
    HypernodeID target = std::numeric_limits<HypernodeID>::max();
    HypernodeID target_id = std::numeric_limits<HypernodeID>::max();
    for (auto it = tmp_ratings.end() - 1; it >= tmp_ratings.begin(); --it) {
      const HypernodeID tmp_target_id = it->key;
      const HypernodeID tmp_target = tmp_target_id;
      const HypernodeWeight target_weight = cluster_weight[tmp_target_id];

      if ( tmp_target != u && weight_u + target_weight <= max_allowed_node_weight ) {
        HypernodeWeight penalty = HeavyNodePenaltyPolicy::penalty(weight_u, target_weight);
        penalty = std::max(penalty, 1);
        const RatingType tmp_rating = it->value / static_cast<double>(penalty);

        bool accept_fixed_vertex_contraction = true;
        if constexpr ( has_fixed_vertices ) {
          accept_fixed_vertex_contraction =
            FixedVertexAcceptancePolicy::acceptContraction(
              hypergraph, fixed_vertices, _context, u, tmp_target);
        }

        DBG << "r(" << u << "," << tmp_target << ")=" << tmp_rating;
        if ( accept_fixed_vertex_contraction &&
             community_u_id == hypergraph.communityID(tmp_target) &&
             AcceptancePolicy::acceptRating( tmp_rating, max_rating,
               target_id, tmp_target_id, cpu_id, _already_matched) ) {
          max_rating = tmp_rating;
          target_id = tmp_target_id;
          target = tmp_target;
        }
      }
    }

    VertexPairRating ret;
    if (max_rating != std::numeric_limits<RatingType>::min()) {
      ASSERT(target != std::numeric_limits<HypernodeID>::max(), "invalid contraction target");
      ret.value = max_rating;
      ret.target = target;
      ret.valid = true;
    }
    tmp_ratings.clear();
    return ret;
  }

  template<typename ScorePolicy, typename Hypergraph, typename RatingMap>
  void fillRatingMap(const Hypergraph& hypergraph,
                     const HypernodeID u,
                     RatingMap& tmp_ratings,
                     const parallel::scalable_vector<HypernodeID>& cluster_ids) {
    if constexpr (Hypergraph::is_graph) {
      for ( const HyperedgeID& he : hypergraph.incidentEdges(u) ) {
        const RatingType score = ScorePolicy::score(hypergraph.edgeWeight(he), hypergraph.edgeSize(he));
        const HypernodeID representative = cluster_ids[hypergraph.edgeTarget(he)];
        ASSERT(representative < hypergraph.initialNumNodes());
        tmp_ratings[representative] += score;
      }
    } else {
      kahypar::ds::FastResetFlagArray<>& bloom_filter = _local_bloom_filter.local();
      for ( const HyperedgeID& he : hypergraph.incidentEdges(u) ) {
        HypernodeID edge_size = hypergraph.edgeSize(he);
        ASSERT(edge_size > 1, V(he));
        if ( edge_size < _context.partition.ignore_hyperedge_size_threshold ) {
          edge_size = _context.coarsening.use_adaptive_edge_size ?
            std::max(adaptiveEdgeSize(hypergraph, he, bloom_filter, cluster_ids), ID(2)) : edge_size;
          const RatingType score = ScorePolicy::score(
            hypergraph.edgeWeight(he), edge_size);
          for ( const HypernodeID& v : hypergraph.pins(he) ) {
            const HypernodeID representative = cluster_ids[v];
            ASSERT(representative < hypergraph.initialNumNodes());
            const HypernodeID bloom_filter_rep = representative & _bloom_filter_mask;
            if ( !bloom_filter[bloom_filter_rep] ) {
              tmp_ratings[representative] += score;
              bloom_filter.set(bloom_filter_rep, true);
            }
          }
          bloom_filter.reset();
        }
      }
    }
  }

  template<typename ScorePolicy, typename Hypergraph, typename RatingMap>
  void fillRatingMapWithSampling(const Hypergraph& hypergraph,
                                 const HypernodeID u,
                                 RatingMap& tmp_ratings,
                                 const parallel::scalable_vector<HypernodeID>& cluster_ids) {
    size_t num_tmp_rating_map_accesses = 0;
    if constexpr (Hypergraph::is_graph) {
      for ( const HyperedgeID& he : hypergraph.incidentEdges(u) ) {
        // Break if number of accesses to the tmp rating map would exceed
        // vertex degree sampling threshold
        if ( num_tmp_rating_map_accesses >= _vertex_degree_sampling_threshold  ) {
          break;
        }
        const RatingType score = ScorePolicy::score(hypergraph.edgeWeight(he), hypergraph.edgeSize(he));
        const HypernodeID representative = cluster_ids[hypergraph.edgeTarget(he)];
        ASSERT(representative < hypergraph.initialNumNodes());
        tmp_ratings[representative] += score;
        ++num_tmp_rating_map_accesses;
      }
    } else {
      kahypar::ds::FastResetFlagArray<>& bloom_filter = _local_bloom_filter.local();
      for ( const HyperedgeID& he : hypergraph.incidentEdges(u) ) {
        HypernodeID edge_size = hypergraph.edgeSize(he);
        if ( edge_size < _context.partition.ignore_hyperedge_size_threshold ) {
          edge_size = _context.coarsening.use_adaptive_edge_size ?
            std::max(adaptiveEdgeSize(hypergraph, he, bloom_filter, cluster_ids), ID(2)) : edge_size;
          // Break if number of accesses to the tmp rating map would exceed
          // vertex degree sampling threshold
          if ( num_tmp_rating_map_accesses + edge_size > _vertex_degree_sampling_threshold  ) {
            break;
          }
          const RatingType score = ScorePolicy::score(
            hypergraph.edgeWeight(he), edge_size);
          for ( const HypernodeID& v : hypergraph.pins(he) ) {
            const HypernodeID representative = cluster_ids[v];
            ASSERT(representative < hypergraph.initialNumNodes());
            const HypernodeID bloom_filter_rep = representative & _bloom_filter_mask;
            if ( !bloom_filter[bloom_filter_rep] ) {
              tmp_ratings[representative] += score;
              bloom_filter.set(bloom_filter_rep, true);
              ++num_tmp_rating_map_accesses;
            }
          }
          bloom_filter.reset();
        }
      }
    }
  }

  template<typename Hypergraph>
  inline HypernodeID adaptiveEdgeSize(const Hypergraph& hypergraph,
                                      const HyperedgeID he,
                                      kahypar::ds::FastResetFlagArray<>& bloom_filter,
                                      const parallel::scalable_vector<HypernodeID>& cluster_ids) {
    HypernodeID edge_size = 0;
    for ( const HypernodeID& v : hypergraph.pins(he) ) {
      const HypernodeID representative = cluster_ids[v];
      ASSERT(representative < hypergraph.initialNumNodes());
      const HypernodeID bloom_filter_rep = representative & _bloom_filter_mask;
      if ( !bloom_filter[bloom_filter_rep] ) {
        ++edge_size;
        bloom_filter.set(bloom_filter_rep, true);
      }
    }
    bloom_filter.reset();
    return edge_size;
  }

  template<typename Hypergraph>
  inline RatingMapType getRatingMapTypeForRatingOfHypernode(const Hypergraph& hypergraph,
                                                            const HypernodeID u) {
    const bool use_vertex_degree_sampling =
      _vertex_degree_sampling_threshold != std::numeric_limits<size_t>::max();
    const size_t vertex_degree_bounded_rating_map_size = use_vertex_degree_sampling ?
      3UL * _vertex_degree_sampling_threshold : std::numeric_limits<size_t>::max();
    const size_t cache_efficient_rating_map_size = CacheEfficientRatingMap::MAP_SIZE;
    const size_t size_of_smaller_rating_map = std::min(
      vertex_degree_bounded_rating_map_size, cache_efficient_rating_map_size);

    // In case the current number of nodes is smaller than size
    // of the cache-efficient sparse map, the large tmp rating map
    // consumes less memory
    if ( _current_num_nodes < size_of_smaller_rating_map ) {
      return RatingMapType::LARGE_RATING_MAP;
    }

    // Compute estimation for the upper bound of neighbors of u
    if constexpr (Hypergraph::is_graph) {
      if ( hypergraph.nodeDegree(u) > cache_efficient_rating_map_size / 3UL ) {
        if ( vertex_degree_bounded_rating_map_size < _current_num_nodes ) {
          return RatingMapType::VERTEX_DEGREE_BOUNDED_RATING_MAP;
        } else {
          return RatingMapType::LARGE_RATING_MAP;
        }
      }
    } else {
      HypernodeID ub_neighbors_u = 0;
      for ( const HyperedgeID& he : hypergraph.incidentEdges(u) ) {
        const HypernodeID edge_size = hypergraph.edgeSize(he);
        // Ignore large hyperedges
        ub_neighbors_u += edge_size < _context.partition.ignore_hyperedge_size_threshold ? edge_size : 0;
        // If the number of estimated neighbors is greater than the size of the cache efficient rating map / 3, we
        // use the large sparse map. The division by 3 also ensures that the fill grade
        // of the cache efficient sparse map would be small enough such that linear probing
        // is fast.
        if ( ub_neighbors_u > cache_efficient_rating_map_size / 3UL ) {
          if ( vertex_degree_bounded_rating_map_size < _current_num_nodes ) {
            return RatingMapType::VERTEX_DEGREE_BOUNDED_RATING_MAP;
          } else {
            return RatingMapType::LARGE_RATING_MAP;
          }
        }
      }
    }

    return RatingMapType::CACHE_EFFICIENT_RATING_MAP;
  }

  LargeTmpRatingMap construct_large_tmp_rating_map() {
    return LargeTmpRatingMap(_current_num_nodes);
  }

  size_t align_to_next_power_of_two(const size_t size) const {
    return std::pow(2.0, std::ceil(std::log2(static_cast<double>(size))));
  }

  const Context& _context;
  // ! Number of nodes of the current hypergraph
  HypernodeID _current_num_nodes;
  // ! Maximum number of neighbors that are considered for rating
  size_t _vertex_degree_sampling_threshold;

  // ! Cache efficient rating map (with linear probing) that is used if the
  // ! estimated number of neighbors smaller than 10922 (= 32768 / 3)
  ThreadLocalCacheEfficientRatingMap _local_cache_efficient_rating_map;
  // ! Rating map that is used if vertex degree sampling is activated.
  // ! In that case the number of neighbors is bounded by the vertex degree
  // ! sampling threshold
  ThreadLocalVertexDegreeBoundedRatingMap _local_vertex_degree_bounded_rating_map;
  // ! Rating map that is used, if the estimated number of neighbors does not fit
  // ! into the previous rating maps (fallback -> size is current number of nodes)
  ThreadLocalLargeTmpRatingMap _local_large_rating_map;

  // ! If we iterate over the pins of a hyperedge to accumulate its ratings,
  // ! we have to make sure that we do not rate one cluster id twice. To do so
  // ! we use this bloom filter.
  size_t _bloom_filter_mask;
  ThreadLocalFastResetFlagArray _local_bloom_filter;

  // ! Marks all matched vertices
  kahypar::ds::FastResetFlagArray<> _already_matched;
};
}  // namespace mt_kahypar
