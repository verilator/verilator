/*******************************************************************************
 * MIT License
 *
 * This file is part of Mt-KaHyPar.
 *
 * Copyright (C) 2019 Lars Gottesbüren <lars.gottesbueren@kit.edu>
 * Copyright (C) 2019 Tobias Heuer <tobias.heuer@kit.edu>
 * Copyright (C) 2023 Nikolai Maas <nikolai.maas@kit.edu>
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

#include "tbb/enumerable_thread_specific.h"

#include "mt-kahypar/definitions.h"
#include "mt-kahypar/partition/context.h"
#include "mt-kahypar/partition/coarsening/multilevel/concurrent_clustering_data.h"
#include "mt-kahypar/partition/coarsening/multilevel/multilevel_vertex_pair_rater.h"
#include "mt-kahypar/partition/coarsening/num_nodes_tracker.h"
#include "mt-kahypar/partition/coarsening/policies/rating_fixed_vertex_acceptance_policy.h"


namespace mt_kahypar {

// this struct bundles data and parameters that are needed for a multilevel coarsening pass
template<typename Hypergraph>
struct ClusteringContext {
  static constexpr bool enable_heavy_assert = false;

 public:
  using Rating = MultilevelVertexPairRater::Rating;

  explicit ClusteringContext(const Context& context,
                             HypernodeID hierarchy_contraction_limit,
                             vec<HypernodeID>& cluster_ids,
                             MultilevelVertexPairRater& rater,
                             ConcurrentClusteringData& clustering_data):
    hierarchy_contraction_limit(hierarchy_contraction_limit),
    max_allowed_node_weight(context.coarsening.max_allowed_node_weight),
    original_num_threads(context.shared_memory.original_num_threads),
    num_hns_before_pass(0),
    previous_num_nodes(0),
    num_nodes_tracker(),
    fixed_vertices(),
    cluster_ids(cluster_ids),
    rater(rater),
    clustering_data(clustering_data) { }

  ClusteringContext(const ClusteringContext&) = delete;
  ClusteringContext(ClusteringContext&&) = delete;
  ClusteringContext & operator= (const ClusteringContext &) = delete;
  ClusteringContext & operator= (ClusteringContext&&) = delete;

  MT_KAHYPAR_ATTRIBUTE_ALWAYS_INLINE HypernodeID clusterID(HypernodeID hn) const {
    ASSERT(hn < cluster_ids.size());
    return cluster_ids[hn];
  }

  // returns the weight of the cluster of this node
  MT_KAHYPAR_ATTRIBUTE_ALWAYS_INLINE HypernodeWeight clusterWeight(HypernodeID hn) const {
    HypernodeID cluster_id = clusterID(hn);
    ASSERT(cluster_id < clustering_data.clusterWeight().size());
    return clustering_data.clusterWeight()[cluster_id];
  }

  MT_KAHYPAR_ATTRIBUTE_ALWAYS_INLINE bool vertexIsUnmatched(const HypernodeID u) const {
    return clustering_data.vertexIsUnmatched(u);
  }

  MT_KAHYPAR_ATTRIBUTE_ALWAYS_INLINE HypernodeID currentNumNodes() const {
    return num_nodes_tracker.currentNumNodes();
  }

  MT_KAHYPAR_ATTRIBUTE_ALWAYS_INLINE HypernodeID finalNumNodes() {
    return num_nodes_tracker.finalNumNodes();
  }

  MT_KAHYPAR_ATTRIBUTE_ALWAYS_INLINE bool shouldContinue() const {
    return num_nodes_tracker.currentNumNodes() > hierarchy_contraction_limit;
  }

  void initializeCoarseningPass(Hypergraph& current_hg, const Context& context) {
    num_hns_before_pass = current_hg.initialNumNodes() - current_hg.numRemovedHypernodes();
    previous_num_nodes = num_hns_before_pass;
    fixed_vertices = current_hg.copyOfFixedVertexSupport();
    fixed_vertices.setMaxBlockWeight(context.partition.max_part_weights);

    clustering_data.initializeCoarseningPass(current_hg, cluster_ids);
    num_nodes_tracker.initialize(num_hns_before_pass);
    rater.resetMatches();
    rater.setCurrentNumberOfNodes(current_hg.initialNumNodes());
  }

  template<typename ScorePolicy, typename HeavyNodePenaltyPolicy, typename AcceptancePolicy>
  MT_KAHYPAR_ATTRIBUTE_ALWAYS_INLINE
  Rating rate(const Hypergraph& current_hg, const HypernodeID u) {
    if (fixed_vertices.hasFixedVertices()) {
      return rater.rate<ScorePolicy, HeavyNodePenaltyPolicy, AcceptancePolicy, true>(
                  current_hg, u, cluster_ids, clustering_data.clusterWeight(), fixed_vertices, max_allowed_node_weight);
    } else {
      return rater.rate<ScorePolicy, HeavyNodePenaltyPolicy, AcceptancePolicy, false>(
                  current_hg, u, cluster_ids, clustering_data.clusterWeight(), fixed_vertices, max_allowed_node_weight);
    }
  }

  MT_KAHYPAR_ATTRIBUTE_ALWAYS_INLINE
  bool matchVertices(const Hypergraph& current_hg, const HypernodeID u, const HypernodeID v) {
    bool success;
    if (fixed_vertices.hasFixedVertices()) {
      success = clustering_data.template matchVertices<true>(current_hg, u, v, cluster_ids, rater, fixed_vertices);
    } else {
      success = clustering_data.template matchVertices<false>(current_hg, u, v, cluster_ids, rater, fixed_vertices);
    }
    if (success) {
      // update the number of nodes in a way that minimizes synchronization overhead
      num_nodes_tracker.subtractNode(original_num_threads, hierarchy_contraction_limit);
    }
    return success;
  }

  MT_KAHYPAR_ATTRIBUTE_ALWAYS_INLINE
  bool acceptFixedVertexContraction(const Hypergraph& current_hg, const Context& context, const HypernodeID u, const HypernodeID v) {
    return FixedVertexAcceptancePolicy::acceptContraction(current_hg, fixed_vertices, context, u, v);
  }

  bool finalize(const Hypergraph& current_hg, const Context& context) {
    if (fixed_vertices.hasFixedVertices()) {
      ASSERT(fixed_vertices.verifyClustering(cluster_ids), "Fixed vertex support is corrupted");
    }
    HEAVY_COARSENING_ASSERT(clustering_data.verifyClustering(current_hg, cluster_ids),
                            "Parallel clustering computed invalid cluster ids and weights");
    unused(current_hg);

    const double reduction_vertices_percentage =
      static_cast<double>(num_hns_before_pass) / static_cast<double>(num_nodes_tracker.finalNumNodes());
    return reduction_vertices_percentage > context.coarsening.minimum_shrink_factor;
  }

  HypernodeID hierarchy_contraction_limit;
  HypernodeWeight max_allowed_node_weight;
  size_t original_num_threads;

 private:
  HypernodeID num_hns_before_pass;
  HypernodeID previous_num_nodes;
  NumNodesTracker num_nodes_tracker;
  ds::FixedVertexSupport<Hypergraph> fixed_vertices;

  vec<HypernodeID>& cluster_ids;
  MultilevelVertexPairRater& rater;
  ConcurrentClusteringData& clustering_data;
};

}  // namespace mt_kahypar
