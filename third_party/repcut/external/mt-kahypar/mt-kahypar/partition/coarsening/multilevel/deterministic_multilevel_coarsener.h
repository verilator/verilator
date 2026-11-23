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

#pragma once

#include "kahypar-resources/datastructure/fast_reset_flag_array.h"

#include "include/mtkahypartypes.h"

#include "mt-kahypar/partition/coarsening/i_coarsener.h"
#include "mt-kahypar/partition/coarsening/multilevel/multilevel_coarsener_base.h"
#include "mt-kahypar/utils/reproducible_random.h"
#include "mt-kahypar/datastructures/sparse_map.h"
#include "mt-kahypar/datastructures/buffered_vector.h"
#include "mt-kahypar/datastructures/fixed_vertex_support.h"
#include "mt-kahypar/utils/utilities.h"
#include "mt-kahypar/utils/progress_bar.h"
#include "mt-kahypar/utils/cast.h"

#include <tbb/enumerable_thread_specific.h>

namespace mt_kahypar {

template<typename TypeTraits>
class DeterministicMultilevelCoarsener :  public ICoarsener,
                                          private MultilevelCoarsenerBase<TypeTraits> {

  struct DeterministicCoarseningConfig {
    explicit DeterministicCoarseningConfig(const Context& context) :
      prng(context.partition.seed),
      num_buckets(utils::ParallelPermutation<HypernodeID>::num_buckets),
      num_sub_rounds(context.coarsening.num_sub_rounds_deterministic),
      num_buckets_per_sub_round(0) {
      num_buckets_per_sub_round = parallel::chunking::idiv_ceil(num_buckets, num_sub_rounds);
    }

    std::mt19937 prng;
    const size_t num_buckets;
    const size_t num_sub_rounds;
    size_t num_buckets_per_sub_round;
  };

  using Hypergraph = typename TypeTraits::Hypergraph;
  using PartitionedHypergraph = typename TypeTraits::PartitionedHypergraph;
  using CacheEfficientRatingMap = ds::FixedSizeSparseMap<HypernodeID, double>;
  using LargeRatingMap = ds::SparseMap<HypernodeID, double>;

public:
  DeterministicMultilevelCoarsener(mt_kahypar_hypergraph_t hypergraph,
                                   const Context& context,
                                   uncoarsening_data_t* uncoarseningData);

  ~DeterministicMultilevelCoarsener() {

  }

private:
  static constexpr bool debug = false;
  static constexpr bool enable_heavy_assert = false;

  void initializeImpl() override {
    if ( _context.partition.enable_logging && _context.partition.enable_progress_bar ) {
      progress_bar.enable();
    }
  }

  bool coarseningPassImpl() override;

  bool shouldNotTerminateImpl() const override {
    return Base::currentNumNodes() > _context.coarsening.contraction_limit;
  }

  void terminateImpl() override {
    progress_bar += (initial_num_nodes - progress_bar.count());   // fill to 100%
    progress_bar.disable();
    _uncoarseningData.finalizeCoarsening();
  }

  HypernodeID currentLevelContractionLimit() {
    const auto& hg = Base::currentHypergraph();
    return std::max( _context.coarsening.contraction_limit,
               static_cast<HypernodeID>(
                    (hg.initialNumNodes() - hg.numRemovedHypernodes()) / _context.coarsening.maximum_shrink_factor) );
  }

  template<bool has_fixed_vertices>
  void clusterNodesInRange(vec<HypernodeID>& clusters,
                           HypernodeID& num_nodes,
                           size_t first,
                           size_t last,
                           ds::FixedVertexSupport<Hypergraph>& fixed_vertices);

  template<bool has_fixed_vertices, typename RatingMap>
  void calculatePreferredTargetCluster(HypernodeID u,
                                       const vec<HypernodeID>& clusters,
                                       RatingMap& tmp_ratings,
                                       const ds::FixedVertexSupport<Hypergraph>& fixed_vertices);

  template<bool has_fixed_vertices>
  size_t approveNodes(vec<HypernodeID>& clusters, ds::FixedVertexSupport<Hypergraph>& fixed_vertices);

  HypernodeID currentNumberOfNodesImpl() const override {
    return Base::currentNumNodes();
  }

  mt_kahypar_hypergraph_t coarsestHypergraphImpl() override {
    return mt_kahypar_hypergraph_t {
      reinterpret_cast<mt_kahypar_hypergraph_s*>(
        &Base::currentHypergraph()), Hypergraph::TYPE };
  }

  mt_kahypar_partitioned_hypergraph_t coarsestPartitionedHypergraphImpl() override {
    return mt_kahypar_partitioned_hypergraph_t {
      reinterpret_cast<mt_kahypar_partitioned_hypergraph_s*>(
        &Base::currentPartitionedHypergraph()), PartitionedHypergraph::TYPE };
  }

  void handleNodeSwaps(const size_t first, const size_t last, const Hypergraph& hg);

  bool useLargeRatingMapForRatingOfHypernode(const Hypergraph& hypergraph, const HypernodeID u);

  void initializeEdgeDeduplication();

  using Base = MultilevelCoarsenerBase<TypeTraits>;
  using Base::_hg;
  using Base::_context;
  using Base::_timer;
  using Base::_uncoarseningData;

  DeterministicCoarseningConfig config;
  HypernodeID initial_num_nodes;
  utils::ParallelPermutation<HypernodeID> permutation;
  vec<HypernodeID> propositions;
  vec<HypernodeWeight> cluster_weight, opportunistic_cluster_weight;
  ds::BufferedVector<HypernodeID> nodes_in_too_heavy_clusters;
  tbb::enumerable_thread_specific<LargeRatingMap> default_rating_maps;
  tbb::enumerable_thread_specific<CacheEfficientRatingMap> cache_efficient_rating_maps;
  tbb::enumerable_thread_specific<vec<HypernodeID>> ties;
  size_t pass;
  utils::ProgressBar progress_bar;
  ds::BufferedVector<HypernodeID> cluster_weights_to_fix;

  size_t bloom_filter_mask;
  tbb::enumerable_thread_specific<kahypar::ds::FastResetFlagArray<>> bloom_filters;
};
}
