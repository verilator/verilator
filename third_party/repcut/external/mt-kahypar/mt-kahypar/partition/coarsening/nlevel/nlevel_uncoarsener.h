/*******************************************************************************
 * MIT License
 *
 * This file is part of Mt-KaHyPar.
 *
 * Copyright (C) 2021 Noah Wahl <noah.wahl@kit.edu>
 * Copyright (C) 2021 Tobias Heuer <tobias.heuer@kit.edu>
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

#include "mt-kahypar/partition/context.h"
#include "mt-kahypar/partition/coarsening/i_uncoarsener.h"
#include "mt-kahypar/partition/coarsening/uncoarsener_base.h"
#include "mt-kahypar/partition/refinement/i_refiner.h"
#include "mt-kahypar/partition/coarsening/coarsening_commons.h"
#include "mt-kahypar/datastructures/streaming_vector.h"
#include "mt-kahypar/utils/progress_bar.h"

namespace mt_kahypar {

// Forward Declaration
class TargetGraph;

template<typename TypeTraits>
class NLevelUncoarsener : public IUncoarsener<TypeTraits>,
                          private UncoarsenerBase<TypeTraits> {

  using Base = UncoarsenerBase<TypeTraits>;
  using Hypergraph = typename TypeTraits::Hypergraph;
  using PartitionedHypergraph = typename TypeTraits::PartitionedHypergraph;
  using ParallelHyperedge = typename Hypergraph::ParallelHyperedge;
  using ParallelHyperedgeVector = vec<vec<ParallelHyperedge>>;

 private:
  static constexpr bool debug = false;
  static constexpr bool enable_heavy_assert = false;


  struct NLevelStats {
    explicit NLevelStats(const Context& context) :
      utility_id(context.utility_id),
      num_batches(0),
      total_batch_sizes(0),
      current_number_of_nodes(0),
      min_num_border_vertices(0) {
      min_num_border_vertices = std::max(context.refinement.max_batch_size,
        context.shared_memory.num_threads * context.refinement.min_border_vertices_per_thread);
    }

    ~NLevelStats() {
      double avg_batch_size = static_cast<double>(total_batch_sizes) / num_batches;
      utils::Utilities::instance().getStats(utility_id).add_stat(
        "num_batches", static_cast<int64_t>(num_batches));
      utils::Utilities::instance().getStats(utility_id).add_stat(
        "avg_batch_size", avg_batch_size);
      DBG << V(num_batches) << V(avg_batch_size);
    }

    const size_t utility_id;
    size_t num_batches;
    size_t total_batch_sizes;
    HypernodeID current_number_of_nodes;
    size_t min_num_border_vertices;
  };

 public:
  NLevelUncoarsener(Hypergraph& hypergraph,
                    const Context& context,
                    UncoarseningData<TypeTraits>& uncoarseningData,
                    const TargetGraph* target_graph) :
    Base(hypergraph, context, uncoarseningData),
    _target_graph(target_graph),
    _hierarchy(),
    _global_label_propagation(nullptr),
    _global_fm(nullptr),
    _tmp_refinement_nodes(),
    _border_vertices_of_batch(hypergraph.initialNumNodes()),
    _stats(context),
    _progress(hypergraph.initialNumNodes(), 0, false),
    _is_timer_disabled(false),
    _force_measure_timings(context.partition.show_detailed_uncontraction_timings && context.type == ContextType::main) { }

  NLevelUncoarsener(const NLevelUncoarsener&) = delete;
  NLevelUncoarsener(NLevelUncoarsener&&) = delete;
  NLevelUncoarsener & operator= (const NLevelUncoarsener &) = delete;
  NLevelUncoarsener & operator= (NLevelUncoarsener &&) = delete;

 private:
  void initializeImpl() override;

  bool isTopLevelImpl() const override;

  void projectToNextLevelAndRefineImpl() override;

  void refineImpl() override;

  void rebalancingImpl() override;

  gain_cache_t getGainCacheImpl() override {
    return _gain_cache;
  }

  HyperedgeWeight getObjectiveImpl() const override;

  void updateMetricsImpl() override;

  PartitionedHypergraph& currentPartitionedHypergraphImpl() override;

  HypernodeID currentNumberOfNodesImpl() const override;

  PartitionedHypergraph&& movePartitionedHypergraphImpl() override;

  void localizedRefine(PartitionedHypergraph& partitioned_hypergraph);

  void globalRefine(PartitionedHypergraph& partitioned_hypergraph,
                    const double time_limit);

  template<typename Func>
  void runInGlobalRefinementContext(Func func);

  using Base::_hg;
  using Base::_context;
  using Base::_uncoarseningData;
  using Base::_gain_cache;
  using Base::_label_propagation;
  using Base::_jet;
  using Base::_fm;
  using Base::_flows;
  using Base::_rebalancer;
  using Base::_timer;
  using Base::_current_metrics;

  const TargetGraph* _target_graph;

  // ! Represents the n-level hierarchy
  // ! A batch is vector of uncontractions/mementos that can be uncontracted in parallel
  // ! without conflicts. All batches of a specific version of the hypergraph are assembled
  // ! in a batch vector. Each time we perform single-pin and parallel net detection we create
  // ! a new version (simply increment a counter) of the hypergraph. Once a batch vector is
  // ! completly processed single-pin and parallel nets have to be restored.
  VersionedBatchVector _hierarchy;

  // ! If we use different algorithms for local and global refinement, we need two LP/FM refiner instances
  std::unique_ptr<IRefiner> _global_label_propagation;
  std::unique_ptr<IRefiner> _global_fm;

  ds::StreamingVector<HypernodeID> _tmp_refinement_nodes;
  kahypar::ds::FastResetFlagArray<> _border_vertices_of_batch;

  NLevelStats _stats;
  utils::ProgressBar _progress;
  bool _is_timer_disabled;
  bool _force_measure_timings;
};
}
