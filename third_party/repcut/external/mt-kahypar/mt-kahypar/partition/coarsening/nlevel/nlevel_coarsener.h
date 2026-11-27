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

#include <string>

#include <tbb/parallel_for.h>
#include <tbb/parallel_sort.h>
#include <tbb/parallel_scan.h>

#include "include/mtkahypartypes.h"

#include "kahypar-resources/meta/mandatory.h"
#include "mt-kahypar/partition/coarsening/nlevel/nlevel_coarsener_base.h"
#include "mt-kahypar/partition/coarsening/nlevel/nlevel_vertex_pair_rater.h"
#include "mt-kahypar/partition/coarsening/i_coarsener.h"
#include "mt-kahypar/partition/coarsening/num_nodes_tracker.h"
#include "mt-kahypar/partition/coarsening/policies/rating_acceptance_policy.h"
#include "mt-kahypar/partition/coarsening/policies/rating_heavy_node_penalty_policy.h"
#include "mt-kahypar/partition/coarsening/policies/rating_score_policy.h"
#include "mt-kahypar/parallel/parallel_prefix_sum.h"
#include "mt-kahypar/utils/cast.h"
#include "mt-kahypar/utils/progress_bar.h"
#include "mt-kahypar/utils/randomize.h"
#include "mt-kahypar/utils/stats.h"

namespace mt_kahypar {
template <class TypeTraits = Mandatory,
          class ScorePolicy = HeavyEdgeScore,
          class HeavyNodePenaltyPolicy = NoWeightPenalty,
          class AcceptancePolicy = BestRatingPreferringUnmatched>
class NLevelCoarsener : public ICoarsener,
                        private NLevelCoarsenerBase<TypeTraits> {
 private:

  #define HIGH_DEGREE_VERTEX_THRESHOLD ID(200000)

  using Base = NLevelCoarsenerBase<TypeTraits>;
  using Rater = NLevelVertexPairRater<ScorePolicy,
                                      HeavyNodePenaltyPolicy,
                                      AcceptancePolicy>;
  using Rating = typename Rater::Rating;
  using Hypergraph = typename TypeTraits::Hypergraph;
  using PartitionedHypergraph = typename TypeTraits::PartitionedHypergraph;

  static constexpr bool debug = false;
  static constexpr bool enable_heavy_assert = false;

 public:
  NLevelCoarsener(mt_kahypar_hypergraph_t hypergraph,
                  const Context& context,
                  uncoarsening_data_t* uncoarseningData) :
    Base(utils::cast<Hypergraph>(hypergraph),
         context,
         uncoarsening::to_reference<TypeTraits>(uncoarseningData)),
    _rater(utils::cast<Hypergraph>(hypergraph).initialNumNodes(), context),
    _initial_num_nodes(utils::cast<Hypergraph>(hypergraph).initialNumNodes() -
                       utils::cast<Hypergraph>(hypergraph).numRemovedHypernodes()),
    _current_vertices(),
    _tmp_current_vertices(),
    _enabled_vertex_flag_array(),
    _num_nodes_tracker(),
    _pass_nr(0),
    _progress_bar(utils::cast<Hypergraph>(hypergraph).initialNumNodes(), 0, false),
    _enable_randomization(true) {
    _progress_bar += _hg.numRemovedHypernodes();
    tbb::parallel_invoke([&] {
      _current_vertices.resize(_hg.initialNumNodes());
      tbb::parallel_for(ID(0), _hg.initialNumNodes(), [&](const HypernodeID hn) {
        _current_vertices[hn] = hn;
      });
      utils::Randomize::instance().parallelShuffleVector(_current_vertices, UL(0), _current_vertices.size());
    }, [&] {
      _tmp_current_vertices.resize(_hg.initialNumNodes());
    }, [&] {
      _enabled_vertex_flag_array.resize(_hg.initialNumNodes());
    });
  }

  NLevelCoarsener(const NLevelCoarsener&) = delete;
  NLevelCoarsener(NLevelCoarsener&&) = delete;
  NLevelCoarsener & operator= (const NLevelCoarsener &) = delete;
  NLevelCoarsener & operator= (NLevelCoarsener &&) = delete;

  ~NLevelCoarsener() = default;

  void disableRandomization() {
    _enable_randomization = false;
  }

 private:
  void initializeImpl() override {
    if ( _context.partition.enable_logging && _context.partition.enable_progress_bar ) {
      _progress_bar.enable();
    }
    _num_nodes_tracker.initialize(_initial_num_nodes);
  }

  bool coarseningPassImpl() override {
    DBG << V(_pass_nr) << V(_num_nodes_tracker.currentNumNodes());
    const HypernodeID num_hns_before_pass = _num_nodes_tracker.currentNumNodes();

      // Coarsening Pass
      _rater.resetMatches();
    double contraction_limit =
      std::max(static_cast<HypernodeID>(_num_nodes_tracker.currentNumNodes() /
        _context.coarsening.maximum_shrink_factor), _context.coarsening.contraction_limit);
    if ( _context.coarsening.maximum_shrink_factor > 99.0 ) {
      contraction_limit = _context.coarsening.contraction_limit;
    }

    HighResClockTimepoint round_start = std::chrono::high_resolution_clock::now();
    _timer.start_timer("clustering", "Clustering");
    if ( _hg.hasFixedVertices() ) {
      _hg.setMaxFixedVertexBlockWeight(_context.partition.max_part_weights);
      performClustering<true>(contraction_limit);
    } else {
      performClustering<false>(contraction_limit);
    }
    _timer.stop_timer("clustering");

    // Remove single-pin and parallel nets
    Base::removeSinglePinAndParallelNets(round_start);
    HEAVY_COARSENING_ASSERT(_hg.verifyIncidenceArrayAndIncidentNets());

    // Writes all enabled vertices to _current_vertices
    _num_nodes_tracker.updateCurrentNumNodes();
    compactifyVertices();
    utils::Randomize::instance().parallelShuffleVector(
      _current_vertices, UL(0), _current_vertices.size());

    // Terminate contraction if the number of contracted vertices in this round
    // is smaller than a certain fraction.
    const double reduction_vertices_percentage =
      static_cast<double>(num_hns_before_pass) /
      static_cast<double>(_num_nodes_tracker.currentNumNodes());
    if ( reduction_vertices_percentage <= _context.coarsening.minimum_shrink_factor ) {
      return false;
    }

    ++_pass_nr;
    return true;
  }

  template<bool has_fixed_vertices>
  void performClustering(const HypernodeID contraction_limit) {
    tbb::parallel_for(UL(0), _current_vertices.size(), [&](const size_t i) {
      if ( _num_nodes_tracker.currentNumNodes() > contraction_limit ) {
        const HypernodeID& hn = _current_vertices[i];
        const HypernodeID num_contractions = contract<has_fixed_vertices>(hn);
        _num_nodes_tracker.subtractMultiple(num_contractions, _context.shared_memory.original_num_threads, contraction_limit);
      }
    });
  }

  bool shouldNotTerminateImpl() const override {
    return _num_nodes_tracker.currentNumNodes() > _context.coarsening.contraction_limit;
  }

  void terminateImpl() override {
    _progress_bar += (_initial_num_nodes - _progress_bar.count());
    _progress_bar.disable();
    _uncoarseningData.finalizeCoarsening();
  }

  template<bool has_fixed_vertices>
  HypernodeID contract(const HypernodeID hn) {
    HypernodeID num_contractions = 0;
    if ( _hg.nodeIsEnabled(hn) ) {
      const Rating rating = _rater.template rate<has_fixed_vertices>(
        _hg, hn, _context.coarsening.max_allowed_node_weight);
      if ( rating.target != kInvalidHypernode ) {
        HypernodeID u = hn;
        HypernodeID v = rating.target;
        // In case v is a high degree vertex, we reverse contraction order to improve performance
        if ( _hg.nodeDegree(u) < _hg.nodeDegree(v) && _hg.nodeDegree(v) > HIGH_DEGREE_VERTEX_THRESHOLD ) {
          u = rating.target;
          v = hn;
        }

        if ( _hg.registerContraction(u, v) ) {
          _rater.markAsMatched(u);
          _rater.markAsMatched(v);
          num_contractions = _hg.contract(v, _context.coarsening.max_allowed_node_weight);
          _progress_bar += num_contractions;
        }
      }
    }
    return num_contractions;
  }

  HypernodeID currentNumberOfNodesImpl() const override {
    return _num_nodes_tracker.currentNumNodes();
  }

  mt_kahypar_hypergraph_t coarsestHypergraphImpl() override {
    return mt_kahypar_hypergraph_t {
      reinterpret_cast<mt_kahypar_hypergraph_s*>(
        &Base::compactifiedHypergraph()), Hypergraph::TYPE };
  }

  mt_kahypar_partitioned_hypergraph_t coarsestPartitionedHypergraphImpl() override {
    return mt_kahypar_partitioned_hypergraph_t {
      reinterpret_cast<mt_kahypar_partitioned_hypergraph_s*>(
        &Base::compactifiedPartitionedHypergraph()), PartitionedHypergraph::TYPE };
  }

  void compactifyVertices() {
    // Mark all vertices that are still enabled
    const HypernodeID current_num_nodes = _num_nodes_tracker.currentNumNodes();
    tbb::parallel_for(UL(0), _current_vertices.size(), [&](const size_t i) {
      const HypernodeID hn = _current_vertices[i];
      _enabled_vertex_flag_array[i] = _hg.nodeIsEnabled(hn);
    });

    // Calculate prefix sum over all enabled vertices to determine their new position
    // in _current_vertices
    parallel::TBBPrefixSum<size_t> active_vertex_prefix_sum(_enabled_vertex_flag_array);
    tbb::parallel_scan(tbb::blocked_range<size_t>(
      UL(0), _enabled_vertex_flag_array.size()), active_vertex_prefix_sum);
    ASSERT(active_vertex_prefix_sum.total_sum() == static_cast<size_t>(current_num_nodes));

    // Write all enabled vertices to _tmp_current_vertices
    _tmp_current_vertices.resize(current_num_nodes);
    tbb::parallel_for(UL(0), _current_vertices.size(), [&](const size_t i) {
      const HypernodeID hn = _current_vertices[i];
      if ( _hg.nodeIsEnabled(hn) ) {
        const size_t pos = active_vertex_prefix_sum[i];
        ASSERT(pos < _tmp_current_vertices.size());
        _tmp_current_vertices[pos] = hn;
      }
    });
    _current_vertices.swap(_tmp_current_vertices);
    _enabled_vertex_flag_array.resize(current_num_nodes);
    ASSERT(_current_vertices.size() == static_cast<size_t>(current_num_nodes));
  }

  using Base::_hg;
  using Base::_context;
  using Base::_timer;
  using Base::_uncoarseningData;
  Rater _rater;
  const HypernodeID _initial_num_nodes;
  parallel::scalable_vector<HypernodeID> _current_vertices;
  parallel::scalable_vector<HypernodeID> _tmp_current_vertices;
  parallel::scalable_vector<size_t> _enabled_vertex_flag_array;
  NumNodesTracker _num_nodes_tracker;
  int _pass_nr;
  utils::ProgressBar _progress_bar;
  bool _enable_randomization;
};

}  // namespace mt_kahypar
