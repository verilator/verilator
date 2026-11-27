/*******************************************************************************
 * MIT License
 *
 * This file is part of Mt-KaHyPar.
 *
 * Copyright (C) 2020 Lars Gottesbüren <lars.gottesbueren@kit.edu>
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

#include "kahypar-resources/datastructure/fast_reset_flag_array.h"

#include "mt-kahypar/datastructures/streaming_vector.h"
#include "mt-kahypar/datastructures/thread_safe_fast_reset_flag_array.h"
#include "mt-kahypar/parallel/stl/scalable_vector.h"
#include "mt-kahypar/partition/context.h"
#include "mt-kahypar/partition/metrics.h"
#include "mt-kahypar/partition/refinement/i_refiner.h"
#include "mt-kahypar/partition/refinement/i_rebalancer.h"
#include "mt-kahypar/partition/refinement/gains/gain_cache_ptr.h"
#include "mt-kahypar/utils/cast.h"


namespace mt_kahypar {
template <typename GraphAndGainTypes>
class LabelPropagationRefiner final : public IRefiner {
 private:
  using Hypergraph = typename GraphAndGainTypes::Hypergraph;
  using PartitionedHypergraph = typename GraphAndGainTypes::PartitionedHypergraph;
  using GainCache = typename GraphAndGainTypes::GainCache;
  using GainCalculator = typename GraphAndGainTypes::GainComputation;
  using ActiveNodes = parallel::scalable_vector<HypernodeID>;
  using NextActiveNodes = ds::StreamingVector<HypernodeID>;

  static constexpr bool debug = false;
  static constexpr bool enable_heavy_assert = false;

 public:
  explicit LabelPropagationRefiner(const HypernodeID num_hypernodes,
                                   const HyperedgeID num_hyperedges,
                                   const Context& context,
                                   GainCache& gain_cache,
                                   IRebalancer& rb) :
    _might_be_uninitialized(false),
    _context(context),
    _gain_cache(gain_cache),
    _current_k(context.partition.k),
    _current_num_nodes(kInvalidHypernode),
    _current_num_edges(kInvalidHyperedge),
    _gain(context),
    _active_nodes(),
    _active_node_was_moved(2 * num_hypernodes, uint8_t(false)),
    _old_part(_context.refinement.label_propagation.unconstrained || context.refinement.global.lp_unconstrained ? num_hypernodes : 0, kInvalidPartition),
    _old_part_is_initialized(_context.refinement.label_propagation.unconstrained || context.refinement.global.lp_unconstrained ? num_hypernodes : 0),
    _next_active(num_hypernodes),
    _visited_he(Hypergraph::is_graph ? 0 : num_hyperedges),
    _rebalancer(rb) { }

  explicit LabelPropagationRefiner(const HypernodeID num_hypernodes,
                                   const HyperedgeID num_hyperedges,
                                   const Context& context,
                                   gain_cache_t gain_cache,
                                   IRebalancer& rb) :
    LabelPropagationRefiner(num_hypernodes, num_hyperedges, context,
      GainCachePtr::cast<GainCache>(gain_cache), rb) { }

  LabelPropagationRefiner(const LabelPropagationRefiner&) = delete;
  LabelPropagationRefiner(LabelPropagationRefiner&&) = delete;

  LabelPropagationRefiner & operator= (const LabelPropagationRefiner &) = delete;
  LabelPropagationRefiner & operator= (LabelPropagationRefiner &&) = delete;

 private:
  bool refineImpl(mt_kahypar_partitioned_hypergraph_t& hypergraph,
                  const parallel::scalable_vector<HypernodeID>& refinement_nodes,
                  Metrics& best_metrics,
                  double) final ;

  void labelPropagation(PartitionedHypergraph& phg, Metrics& best_metrics);

  bool labelPropagationRound(PartitionedHypergraph& hypergraph,
                             NextActiveNodes& next_active_nodes,
                             Metrics& best_metrics,
                             vec<Move>& rebalance_moves,
                             bool unconstrained_lp);

  template<bool unconstrained>
  void moveActiveNodes(PartitionedHypergraph& hypergraph, NextActiveNodes& next_active_nodes);

  bool applyRebalancing(PartitionedHypergraph& hypergraph,
                        const Metrics& best_metrics,
                        Metrics& current_metrics,
                        vec<Move>& rebalance_moves);

  template<typename F>
  void forEachMovedNode(F node_fn);

  template<bool unconstrained, typename F>
  bool moveVertex(PartitionedHypergraph& hypergraph,
                  const HypernodeID hn,
                  NextActiveNodes& next_active_nodes,
                  const F& objective_delta);

  void initializeActiveNodes(PartitionedHypergraph& hypergraph,
                             const parallel::scalable_vector<HypernodeID>& refinement_nodes);

  void initializeImpl(mt_kahypar_partitioned_hypergraph_t&) final;

  template<bool unconstrained, typename F>
  bool changeNodePart(PartitionedHypergraph& phg,
                      const HypernodeID hn,
                      const PartitionID from,
                      const PartitionID to,
                      const F& objective_delta) {
    HypernodeWeight max_weight = unconstrained ? std::numeric_limits<HypernodeWeight>::max()
                                                 : _context.partition.max_part_weights[to];
    if ( _gain_cache.isInitialized() ) {
      return phg.changeNodePart(_gain_cache, hn, from, to, max_weight, []{}, objective_delta);
    } else {
      return phg.changeNodePart(hn, from, to, max_weight, []{}, objective_delta);
    }
  }

  MT_KAHYPAR_ATTRIBUTE_ALWAYS_INLINE
  void activateNodeAndNeighbors(PartitionedHypergraph& hypergraph,
                                NextActiveNodes& next_active_nodes,
                                const HypernodeID hn,
                                bool activate_moved) {
    auto activate = [&](const HypernodeID hn) {
      bool old_part_unintialized = _might_be_uninitialized && !_old_part_is_initialized[hn];
      if (activate_moved || old_part_unintialized || hypergraph.partID(hn) == _old_part[hn]) {
        if ( _next_active.compare_and_set_to_true(hn) ) {
          next_active_nodes.stream(hn);
          if ( old_part_unintialized ) {
            _old_part[hn] = hypergraph.partID(hn);
            _old_part_is_initialized.set(hn, true);
          }
        }
      }
    };

    // Set all neighbors of the vertex to active
    if constexpr (Hypergraph::is_graph) {
      for (const HyperedgeID& he : hypergraph.incidentEdges(hn)) {
        activate(hypergraph.edgeTarget(he));
      }
    } else {
      for (const HyperedgeID& he : hypergraph.incidentEdges(hn)) {
        if ( hypergraph.edgeSize(he) <=
              ID(_context.refinement.label_propagation.hyperedge_size_activation_threshold) ) {
          if ( !_visited_he[he] ) {
            for (const HypernodeID& pin : hypergraph.pins(he)) {
              activate(pin);
            }
            _visited_he.set(he, true);
          }
        }
      }
    }

    if ( activate_moved && _next_active.compare_and_set_to_true(hn) ) {
      ASSERT(!_might_be_uninitialized);
      next_active_nodes.stream(hn);
    }
  }

  void resizeDataStructuresForCurrentK() {
    // If the number of blocks changes, we resize data structures
    // (can happen during deep multilevel partitioning)
    if ( _current_k != _context.partition.k ) {
      _current_k = _context.partition.k;
      _gain.changeNumberOfBlocks(_current_k);
      if ( _gain_cache.isInitialized() ) {
        _gain_cache.changeNumberOfBlocks(_current_k);
      }
    }
  }

  bool _might_be_uninitialized;
  const Context& _context;
  GainCache& _gain_cache;
  PartitionID _current_k;
  HypernodeID _current_num_nodes;
  HyperedgeID _current_num_edges;
  GainCalculator _gain;
  ActiveNodes _active_nodes;
  parallel::scalable_vector<uint8_t> _active_node_was_moved;
  parallel::scalable_vector<PartitionID> _old_part;
  kahypar::ds::FastResetFlagArray<> _old_part_is_initialized;
  ds::ThreadSafeFastResetFlagArray<> _next_active;
  kahypar::ds::FastResetFlagArray<> _visited_he;
  IRebalancer& _rebalancer;
};

}  // namespace kahypar
