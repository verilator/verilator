/*******************************************************************************
 * MIT License
 *
 * This file is part of Mt-KaHyPar.
 *
 * Copyright (C) 2023 Robert Krause <robert.krause@student.kit.edu>
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

#include "kahypar-resources/datastructure/fast_reset_flag_array.h"

#include "mt-kahypar/datastructures/streaming_vector.h"
#include "mt-kahypar/datastructures/thread_safe_fast_reset_flag_array.h"
#include "mt-kahypar/parallel/stl/scalable_vector.h"
#include "mt-kahypar/partition/context.h"
#include "mt-kahypar/partition/refinement/i_refiner.h"
#include "mt-kahypar/partition/refinement/i_rebalancer.h"
#include "mt-kahypar/partition/refinement/gains/gain_cache_ptr.h"
#include "mt-kahypar/utils/reproducible_random.h"

namespace mt_kahypar {

template<typename GraphAndGainTypes>
class DeterministicJetRefiner final : public IRefiner {

  using PartitionedHypergraph = typename GraphAndGainTypes::PartitionedHypergraph;
  using GainComputation = typename GraphAndGainTypes::GainComputation;
  using AttributedGains = typename GraphAndGainTypes::AttributedGains;
  using GainCache = typename GraphAndGainTypes::GainCache;
  using ActiveNodes = typename parallel::scalable_vector<HypernodeID>;
  using RatingMap = typename GainComputation::RatingMap;

public:
  explicit DeterministicJetRefiner(const HypernodeID num_hypernodes,
                                   const HyperedgeID num_hyperedges,
                                   const Context& context,
                                   gain_cache_t gain_cache,
                                   IRebalancer& rebalancer) :
    DeterministicJetRefiner(num_hypernodes, num_hyperedges, context,
      GainCachePtr::cast<GainCache>(gain_cache), rebalancer) {}

  explicit DeterministicJetRefiner(const HypernodeID num_hypernodes,
                                   const HyperedgeID num_hyperedges,
                                   const Context& context,
                                   GainCache& gain_cache,
                                   IRebalancer& rebalancer) :
    _context(context),
    _current_k(context.partition.k),
    _top_level_num_nodes(num_hypernodes),
    _current_partition_is_best(true),
    _negative_gain_factor(0.0),
    _active_nodes(),
    _tmp_active_nodes(),
    _moves(),
    _best_partition(num_hypernodes, kInvalidPartition),
    _part_before_round(num_hypernodes, kInvalidPartition),
    _gains_and_target(num_hypernodes),
    _locks(num_hypernodes),
    _gain_cache(gain_cache),
    _gain_computation(context, true /* disable_randomization */),
    _rebalancer(rebalancer),
    _afterburner_gain(PartitionedHypergraph::is_graph ? 0 : num_hypernodes),
    _afterburner_edge_buffer(),
    _afterburner_visited_hes(PartitionedHypergraph::is_graph ? 0 : num_hyperedges) {}

private:
  static constexpr bool debug = false;
  static constexpr bool enable_heavy_assert = false;

  bool refineImpl(mt_kahypar_partitioned_hypergraph_t& hypergraph,
                  const vec<HypernodeID>&,
                  Metrics& best_metrics, double) final;

  void initializeImpl(mt_kahypar_partitioned_hypergraph_t& phg);

  void runJetRounds(PartitionedHypergraph& phg, Metrics& best_metrics, double time_limit);

  void computeActiveNodesFromGraph(const PartitionedHypergraph& hypergraph);

  Gain performMoveWithAttributedGain(PartitionedHypergraph& phg, const HypernodeID hn);

  void rollbackToBestPartition(PartitionedHypergraph& hypergraph);

  template<typename F>
  void changeNodePart(PartitionedHypergraph& phg,
                      const HypernodeID hn,
                      const PartitionID from,
                      const PartitionID to,
                      const F& objective_delta);

  void graphAfterburner(PartitionedHypergraph& phg);

  void hypergraphAfterburner(PartitionedHypergraph& phg);

  HyperedgeWeight calculateGainDelta(PartitionedHypergraph& phg) const;

  bool arePotentialMovesToOtherParts(const PartitionedHypergraph& hypergraph, const parallel::scalable_vector<HypernodeID>& moves);

  bool noInvalidPartitions(const PartitionedHypergraph& phg, const parallel::scalable_vector<PartitionID>& parts);

  void resizeDataStructuresForCurrentK();

  const Context& _context;
  PartitionID _current_k;
  HypernodeID _top_level_num_nodes;
  bool _current_partition_is_best;
  double _negative_gain_factor;
  ActiveNodes _active_nodes;
  ds::StreamingVector<HypernodeID> _tmp_active_nodes;
  parallel::scalable_vector<HypernodeID> _moves;
  parallel::scalable_vector<PartitionID> _best_partition;
  parallel::scalable_vector<PartitionID> _part_before_round;
  parallel::scalable_vector<std::pair<Gain, PartitionID>> _gains_and_target;
  kahypar::ds::FastResetFlagArray<> _locks;
  GainCache& _gain_cache;
  GainComputation _gain_computation;
  IRebalancer& _rebalancer;

  // hypergraph afterburner
  parallel::scalable_vector<std::atomic<Gain>> _afterburner_gain;
  tbb::enumerable_thread_specific<parallel::scalable_vector<HypernodeID>> _afterburner_edge_buffer;
  ds::ThreadSafeFastResetFlagArray<> _afterburner_visited_hes;
};

}
