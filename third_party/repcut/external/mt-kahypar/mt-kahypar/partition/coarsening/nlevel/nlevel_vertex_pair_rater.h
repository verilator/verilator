/*******************************************************************************
 * MIT License
 *
 * This file is part of Mt-KaHyPar.
 *
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
template <typename ScorePolicy = Mandatory,
          typename HeavyNodePenaltyPolicy = Mandatory,
          typename AcceptancePolicy = Mandatory>
class NLevelVertexPairRater {
  using LargeTmpRatingMap = ds::SparseMap<HypernodeID, RatingType>;
  using CacheEfficientRatingMap = ds::FixedSizeSparseMap<HypernodeID, RatingType>;
  using ThreadLocalCacheEfficientRatingMap = tbb::enumerable_thread_specific<CacheEfficientRatingMap>;
  using ThreadLocalVertexDegreeBoundedRatingMap = tbb::enumerable_thread_specific<CacheEfficientRatingMap>;
  using ThreadLocalLargeTmpRatingMap = tbb::enumerable_thread_specific<LargeTmpRatingMap>;

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

 public:
  using Rating = VertexPairRating;

  NLevelVertexPairRater(const HypernodeID num_hypernodes,
                        const Context& context) :
    _context(context),
    _current_num_nodes(num_hypernodes),
    _vertex_degree_sampling_threshold(context.coarsening.vertex_degree_sampling_threshold),
    _local_cache_efficient_rating_map(0.0),
    _local_vertex_degree_bounded_rating_map(3UL * _vertex_degree_sampling_threshold, 0.0),
    _local_large_rating_map([&] {
      return construct_large_tmp_rating_map();
    }),
    _already_matched(num_hypernodes) { }

  NLevelVertexPairRater(const NLevelVertexPairRater&) = delete;
  NLevelVertexPairRater & operator= (const NLevelVertexPairRater &) = delete;

  NLevelVertexPairRater(NLevelVertexPairRater&&) = delete;
  NLevelVertexPairRater & operator= (NLevelVertexPairRater &&) = delete;

  template<bool has_fixed_vertices, typename Hypergraph>
  VertexPairRating rate(const Hypergraph& hypergraph,
                        const HypernodeID u,
                        const HypernodeWeight max_allowed_node_weight) {

    const RatingMapType rating_map_type = getRatingMapTypeForRatingOfHypernode(hypergraph, u);
    if ( rating_map_type == RatingMapType::CACHE_EFFICIENT_RATING_MAP ) {
      return rate<has_fixed_vertices>(hypergraph, u, _local_cache_efficient_rating_map.local(), max_allowed_node_weight, false);
    } else if ( rating_map_type == RatingMapType::VERTEX_DEGREE_BOUNDED_RATING_MAP ) {
      return rate<has_fixed_vertices>(hypergraph, u, _local_vertex_degree_bounded_rating_map.local(), max_allowed_node_weight, true);
    } else {
      LargeTmpRatingMap& large_tmp_rating_map = _local_large_rating_map.local();
      large_tmp_rating_map.setMaxSize(_current_num_nodes);
      return rate<has_fixed_vertices>(hypergraph, u, large_tmp_rating_map, max_allowed_node_weight, false);
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
  template<bool has_fixed_vertices, typename Hypergraph, typename RatingMap>
  VertexPairRating rate(const Hypergraph& hypergraph,
                        const HypernodeID u,
                        RatingMap& tmp_ratings,
                        const HypernodeWeight max_allowed_node_weight,
                        const bool use_vertex_degree_sampling) {

    if ( use_vertex_degree_sampling ) {
      fillRatingMapWithSampling(hypergraph, u, tmp_ratings);
    } else {
      fillRatingMap(hypergraph, u, tmp_ratings);
    }

    int cpu_id = THREAD_ID;
    const HypernodeWeight weight_u = hypergraph.nodeWeight(u);
    const PartitionID community_u_id = hypergraph.communityID(u);
    RatingType max_rating = std::numeric_limits<RatingType>::min();
    HypernodeID target = kInvalidHypernode;
    for (auto it = tmp_ratings.end() - 1; it >= tmp_ratings.begin(); --it) {
      const HypernodeID tmp_target = it->key;
      const HypernodeWeight target_weight = hypergraph.nodeWeight(tmp_target);

      if ( tmp_target != u && weight_u + target_weight <= max_allowed_node_weight ) {
        HypernodeWeight penalty = HeavyNodePenaltyPolicy::penalty(weight_u, target_weight);
        penalty = penalty == 0 ? std::max(std::max(weight_u, target_weight), 1) : penalty;
        const RatingType tmp_rating = it->value / static_cast<double>(penalty);

        bool accept_fixed_vertex_contraction = true;
        if constexpr ( has_fixed_vertices ) {
          accept_fixed_vertex_contraction =
            FixedVertexAcceptancePolicy::acceptContraction(
              hypergraph, hypergraph.fixedVertexSupport(), _context, u, tmp_target);
        }

        DBG << "r(" << u << "," << tmp_target << ")=" << tmp_rating;
        if ( accept_fixed_vertex_contraction &&
             community_u_id == hypergraph.communityID(tmp_target) &&
             AcceptancePolicy::acceptRating(tmp_rating, max_rating,
                                            target, tmp_target,
                                            cpu_id, _already_matched) ) {
          max_rating = tmp_rating;
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

  template<typename Hypergraph, typename RatingMap>
  void fillRatingMap(const Hypergraph& hypergraph,
                     const HypernodeID u,
                     RatingMap& tmp_ratings) {
    for ( const HyperedgeID& he : hypergraph.incidentEdges(u) ) {
      HypernodeID edge_size = hypergraph.edgeSize(he);
      if ( edge_size > 1 && edge_size < _context.partition.ignore_hyperedge_size_threshold ) {
        const RatingType score = ScorePolicy::score(hypergraph.edgeWeight(he), edge_size);
        for ( const HypernodeID& v : hypergraph.pins(he) ) {
          tmp_ratings[v] += score;
        }
      }
    }
  }

  template<typename Hypergraph, typename RatingMap>
  void fillRatingMapWithSampling(const Hypergraph& hypergraph,
                                 const HypernodeID u,
                                 RatingMap& tmp_ratings) {
    size_t num_tmp_rating_map_accesses = 0;
    for ( const HyperedgeID& he : hypergraph.incidentEdges(u) ) {
      HypernodeID edge_size = hypergraph.edgeSize(he);
      if ( edge_size > 1 && edge_size < _context.partition.ignore_hyperedge_size_threshold ) {
        // Break if number of accesses to the tmp rating map would exceed
        // vertex degree sampling threshold
        if ( num_tmp_rating_map_accesses + edge_size > _vertex_degree_sampling_threshold  ) {
          break;
        }
        const RatingType score = ScorePolicy::score(hypergraph.edgeWeight(he), edge_size);
        for ( const HypernodeID& v : hypergraph.pins(he) ) {
          tmp_ratings[v] += score;
          ++num_tmp_rating_map_accesses;
        }
      }
    }
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

    return RatingMapType::CACHE_EFFICIENT_RATING_MAP;
  }

  LargeTmpRatingMap construct_large_tmp_rating_map() {
    return LargeTmpRatingMap(_current_num_nodes);
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

  // ! Marks all matched vertices
  kahypar::ds::FastResetFlagArray<> _already_matched;
};
}  // namespace mt_kahypar
