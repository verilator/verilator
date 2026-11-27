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

#include <string>

#include <tbb/parallel_for.h>
#include <tbb/parallel_reduce.h>

#include "kahypar-resources/meta/mandatory.h"

#include "include/mtkahypartypes.h"

#include "mt-kahypar/partition/coarsening/multilevel/clustering_context.h"
#include "mt-kahypar/partition/coarsening/multilevel/concurrent_clustering_data.h"
#include "mt-kahypar/partition/coarsening/multilevel/multilevel_coarsener_base.h"
#include "mt-kahypar/partition/coarsening/multilevel/multilevel_vertex_pair_rater.h"
#include "mt-kahypar/partition/coarsening/num_nodes_tracker.h"
#include "mt-kahypar/partition/coarsening/multilevel/two_hop_clustering.h"
#include "mt-kahypar/partition/coarsening/i_coarsener.h"
#include "mt-kahypar/partition/coarsening/policies/rating_acceptance_policy.h"
#include "mt-kahypar/partition/coarsening/policies/rating_heavy_node_penalty_policy.h"
#include "mt-kahypar/partition/coarsening/policies/rating_score_policy.h"
#include "mt-kahypar/utils/cast.h"
#include "mt-kahypar/utils/exception.h"
#include "mt-kahypar/utils/progress_bar.h"
#include "mt-kahypar/utils/randomize.h"
#include "mt-kahypar/utils/stats.h"
#include "mt-kahypar/utils/timer.h"

namespace mt_kahypar {

template <class TypeTraits = Mandatory,
          class ScorePolicy = HeavyEdgeScore,
          class HeavyNodePenaltyPolicy = NoWeightPenalty,
          class AcceptancePolicy = BestRatingPreferringUnmatched>
class MultilevelCoarsener : public ICoarsener,
                            private MultilevelCoarsenerBase<TypeTraits> {
 private:

  using Base = MultilevelCoarsenerBase<TypeTraits>;
  using Rating = MultilevelVertexPairRater::Rating;
  using Hypergraph = typename TypeTraits::Hypergraph;
  using PartitionedHypergraph = typename TypeTraits::PartitionedHypergraph;

  static constexpr bool debug = false;
  static constexpr bool enable_heavy_assert = false;
  static constexpr HypernodeID kInvalidHypernode = std::numeric_limits<HypernodeID>::max();

 public:
  MultilevelCoarsener(mt_kahypar_hypergraph_t hypergraph,
                      const Context& context,
                      uncoarsening_data_t* uncoarseningData) :
    Base(utils::cast<Hypergraph>(hypergraph),
         context,
         uncoarsening::to_reference<TypeTraits>(uncoarseningData)),
    _two_hop_clustering(utils::cast<Hypergraph>(hypergraph).initialNumNodes(), context),
    _rater(utils::cast<Hypergraph>(hypergraph).initialNumNodes(),
           utils::cast<Hypergraph>(hypergraph).maxEdgeSize(), context),
    _clustering_data(_hg.initialNumNodes(), context),
    _initial_num_nodes(utils::cast<Hypergraph>(hypergraph).initialNumNodes()),
    _current_vertices(),
    _pass_nr(0),
    _progress_bar(utils::cast<Hypergraph>(hypergraph).initialNumNodes(), 0, false),
    _enable_randomization(true) {
    if (_context.coarsening.two_hop_shrink_threshold <= 1) {
      throw InvalidParameterException("Value for c-two-hop-threshold too small, must be larger than 1");
    }
    if (_context.coarsening.minimum_shrink_factor <= 1) {
      throw InvalidParameterException("Value for c-min-shrink-factor too small, must be larger than 1");
    }
    if (_context.coarsening.maximum_shrink_factor <= _context.coarsening.minimum_shrink_factor) {
      throw InvalidParameterException("Value for c-max-shrink-factor too small, must be larger than c-min-shrink-factor");
    }

    _progress_bar += _hg.numRemovedHypernodes();
    _current_vertices.resize(_hg.initialNumNodes());
  }

  MultilevelCoarsener(const MultilevelCoarsener&) = delete;
  MultilevelCoarsener(MultilevelCoarsener&&) = delete;
  MultilevelCoarsener & operator= (const MultilevelCoarsener &) = delete;
  MultilevelCoarsener & operator= (MultilevelCoarsener &&) = delete;

  void disableRandomization() {
    _enable_randomization = false;
  }

 private:
  void initializeImpl() override {
    if ( _context.partition.enable_logging && _context.partition.enable_progress_bar ) {
      _progress_bar.enable();
    }
  }

  bool shouldNotTerminateImpl() const override {
    return Base::currentNumNodes() > _context.coarsening.contraction_limit;
  }

  bool coarseningPassImpl() override {
    HighResClockTimepoint round_start = std::chrono::high_resolution_clock::now();
    Hypergraph& current_hg = Base::currentHypergraph();
    DBG << V(_pass_nr)
        << V(current_hg.initialNumNodes())
        << V(current_hg.initialNumEdges())
        << V(current_hg.initialNumPins());

    // initialization of various things
    parallel::scalable_vector<HypernodeID> cluster_ids;
    const HypernodeID hierarchy_contraction_limit = hierarchyContractionLimit(current_hg);
    const HypernodeID two_hop_contraction_limit = twoHopContractionThreshold(current_hg);
    ClusteringContext<Hypergraph> cc(_context, hierarchy_contraction_limit, cluster_ids,
                                     _rater, _clustering_data);
    cc.initializeCoarseningPass(current_hg, _context);

    // the actual coarsening pass
    _current_vertices.resize(current_hg.initialNumNodes());
    tbb::parallel_for(ID(0), current_hg.initialNumNodes(), [&](const HypernodeID hn) {
      _current_vertices[hn] = hn;
    });
    if ( _enable_randomization ) {
      utils::Randomize::instance().parallelShuffleVector( _current_vertices, UL(0), _current_vertices.size());
    }

    const HypernodeID num_hns_before_pass =
      current_hg.initialNumNodes() - current_hg.numRemovedHypernodes();
    HypernodeID current_num_nodes = performClustering(current_hg, cc);
    DBG << V(current_num_nodes) << V(hierarchy_contraction_limit);

    if (_context.coarsening.use_two_hop && current_num_nodes > two_hop_contraction_limit) {
      // if not enough nodes have been contracted, use two hop clustering
      _timer.start_timer("two_hop_clustering", "Two-Hop Clustering");
      if (!_context.coarsening.two_hop_full_shrinkage) {
        cc.hierarchy_contraction_limit = two_hop_contraction_limit;
      }
      if ( _enable_randomization ) {
        utils::Randomize::instance().parallelShuffleVector( _current_vertices, UL(0), _current_vertices.size());
      }
      _two_hop_clustering.performClustering(current_hg, _current_vertices, cc);
      _timer.stop_timer("two_hop_clustering");

      current_num_nodes =  cc.finalNumNodes();
      DBG << "Two-Hop Clustering: " << V(current_num_nodes) << V(hierarchy_contraction_limit);
    }

    bool should_continue = cc.finalize(current_hg, _context);
    if (!should_continue) {
      return false;
    }
    _progress_bar += (num_hns_before_pass - current_num_nodes);

    _timer.start_timer("contraction", "Contraction");
    // Perform parallel contraction
    _uncoarseningData.performMultilevelContraction(std::move(cluster_ids), false /* deterministic */, round_start);
    _timer.stop_timer("contraction");

    ++_pass_nr;
    return true;
  }

  HypernodeID performClustering(const Hypergraph& current_hg,
                                ClusteringContext<Hypergraph>& cc) {
    // We iterate in parallel over all vertices of the hypergraph and compute its contraction partner.
    _timer.start_timer("clustering", "Clustering");
    if ( _context.partition.show_detailed_clustering_timings ) {
      _timer.start_timer("clustering_level_" + std::to_string(_pass_nr), "Level " + std::to_string(_pass_nr));
    }

    const HypernodeID hierarchy_contraction_limit = hierarchyContractionLimit(current_hg);
    DBG << V(current_hg.initialNumNodes()) << V(hierarchy_contraction_limit);
    tbb::parallel_for(ID(0), current_hg.initialNumNodes(), [&](const HypernodeID id) {
      ASSERT(id < _current_vertices.size());
      const HypernodeID hn = _current_vertices[id];
      // We perform rating if ...
      //  1.) The contraction limit of the current level is not reached
      //  2.) Vertex hn is not matched before
      if (current_hg.nodeIsEnabled(hn) && cc.shouldContinue() && cc.vertexIsUnmatched(hn)) {
        const Rating rating = cc.template rate<ScorePolicy, HeavyNodePenaltyPolicy, AcceptancePolicy>(current_hg, hn);
        if (rating.target != kInvalidHypernode) {
          cc.matchVertices(current_hg, hn, rating.target);
        }
      }
    });

    if ( _context.partition.show_detailed_clustering_timings ) {
      _timer.stop_timer("clustering_level_" + std::to_string(_pass_nr));
    }
    _timer.stop_timer("clustering");

    return cc.finalNumNodes();
  }

  void terminateImpl() override {
    _progress_bar += (_initial_num_nodes - _progress_bar.count());
    _progress_bar.disable();
    _uncoarseningData.finalizeCoarsening();
  }

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

  HypernodeID hierarchyContractionLimit(const Hypergraph& hypergraph) const {
    return std::max( static_cast<HypernodeID>( static_cast<double>(hypergraph.initialNumNodes() -
      hypergraph.numRemovedHypernodes()) / _context.coarsening.maximum_shrink_factor ),
      _context.coarsening.contraction_limit );
  }

  HypernodeID twoHopContractionThreshold(const Hypergraph& hypergraph) const {
    return std::max( static_cast<HypernodeID>( static_cast<double>(hypergraph.initialNumNodes() -
      hypergraph.numRemovedHypernodes()) / _context.coarsening.two_hop_shrink_threshold ),
      _context.coarsening.contraction_limit );
  }

  using Base::_hg;
  using Base::_context;
  using Base::_timer;
  using Base::_uncoarseningData;
  TwoHopClustering _two_hop_clustering;
  MultilevelVertexPairRater _rater;
  ConcurrentClusteringData _clustering_data;
  HypernodeID _initial_num_nodes;
  parallel::scalable_vector<HypernodeID> _current_vertices;
  int _pass_nr;
  utils::ProgressBar _progress_bar;
  bool _enable_randomization;
};

}  // namespace mt_kahypar
