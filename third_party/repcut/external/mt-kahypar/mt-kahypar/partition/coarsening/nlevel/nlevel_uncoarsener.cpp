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

#include "mt-kahypar/partition/coarsening/nlevel/nlevel_uncoarsener.h"

#include "mt-kahypar/definitions.h"
#include "mt-kahypar/utils/progress_bar.h"
#include "mt-kahypar/io/partitioning_output.h"
#include "mt-kahypar/utils/utilities.h"
#include "mt-kahypar/utils/cast.h"

namespace mt_kahypar {

  template<typename TypeTraits>
  void NLevelUncoarsener<TypeTraits>::initializeImpl() {
    // Initialize n-level batch uncontraction hierarchy
    _timer.start_timer("create_batch_uncontraction_hierarchy", "Create n-Level Hierarchy");
    _hierarchy = _hg.createBatchUncontractionHierarchy(_context.refinement.max_batch_size);
    ASSERT(_uncoarseningData.removed_hyperedges_batches.size() == _hierarchy.size() - 1);
    _timer.stop_timer("create_batch_uncontraction_hierarchy");

    ASSERT(_uncoarseningData.is_finalized);
    _uncoarseningData.compactified_phg->setTargetGraph(_target_graph);
    _current_metrics = Base::initializeMetrics(*_uncoarseningData.compactified_phg);
    _stats.current_number_of_nodes = _uncoarseningData.compactified_hg->initialNumNodes();
    Base::initializeRefinementAlgorithms();

    // Initialize separate refiner for global LP and global (unconstrained) FM
    if (_context.refinement.label_propagation.algorithm != _context.refinement.global.lp_algorithm) {
      runInGlobalRefinementContext([&]{
        _global_label_propagation = LabelPropagationFactory::getInstance().createObject(
          _context.refinement.global.lp_algorithm,
          _hg.initialNumNodes(), _hg.initialNumEdges(), _context, _gain_cache, *_rebalancer);
      });
    }
    if (_context.refinement.fm.algorithm != _context.refinement.global.fm_algorithm) {
      runInGlobalRefinementContext([&]{
        _global_fm = FMFactory::getInstance().createObject(
          _context.refinement.global.fm_algorithm,
          _hg.initialNumNodes(), _hg.initialNumEdges(), _context, _gain_cache, *_rebalancer);
      });
    }

    if (_context.type == ContextType::main) {
      _context.initial_km1 = _current_metrics.quality;
    }

    // For initial partitioning, we compactify the node IDs of smallest hypergraph to
    // a consecutive range. This step project the partition from the compactified hypergraph
    // to the node IDs of the input hypergraph.
    _timer.start_timer("initialize_partition", "Initialize Partition");
    *_uncoarseningData.partitioned_hg = PartitionedHypergraph(_context.partition.k, _hg, parallel_tag_t());
    _uncoarseningData.partitioned_hg->doParallelForAllNodes([&](const HypernodeID hn) {
      ASSERT(static_cast<size_t>(hn) < _uncoarseningData.compactified_hn_mapping.size());
      const HypernodeID compactified_hn = _uncoarseningData.compactified_hn_mapping[hn];
      const PartitionID block_id = _uncoarseningData.compactified_phg->partID(compactified_hn);
      ASSERT(block_id != kInvalidPartition && block_id < _context.partition.k);
      _uncoarseningData.partitioned_hg->setOnlyNodePart(hn, block_id);
    });
    _uncoarseningData.partitioned_hg->initializePartition();
    _uncoarseningData.partitioned_hg->setTargetGraph(_target_graph);

    ASSERT(metrics::quality(*_uncoarseningData.compactified_phg, _context) ==
           metrics::quality(*_uncoarseningData.partitioned_hg, _context),
           V(metrics::quality(*_uncoarseningData.compactified_phg, _context)) <<
           V(metrics::quality(*_uncoarseningData.partitioned_hg, _context)));
    ASSERT(metrics::imbalance(*_uncoarseningData.compactified_phg, _context) ==
           metrics::imbalance(*_uncoarseningData.partitioned_hg, _context),
           V(metrics::imbalance(*_uncoarseningData.compactified_phg, _context)) <<
           V(metrics::imbalance(*_uncoarseningData.partitioned_hg, _context)));
    _timer.stop_timer("initialize_partition");

    // Enable progress bar if logging is enabled
    if ( _context.partition.enable_logging && _context.partition.enable_progress_bar && !debug ) {
      _progress.enable();
      _progress.setObjective(_current_metrics.quality);
      _progress += _uncoarseningData.compactified_hg->initialNumNodes();
    }

    // Initialize Refiner
    mt_kahypar_partitioned_hypergraph_t phg =
      utils::partitioned_hg_cast(*_uncoarseningData.partitioned_hg);
    if ( _rebalancer ) {
      _rebalancer->initialize(phg);
    }
    if ( _label_propagation ) {
      _label_propagation->initialize(phg);
    }
    if ( _fm ) {
      _fm->initialize(phg);
    }
    if ( _global_label_propagation ) {
      runInGlobalRefinementContext([&]{ _global_label_propagation->initialize(phg); });
    }
    if ( _global_fm ) {
      runInGlobalRefinementContext([&]{ _global_fm->initialize(phg); });
    }

    ASSERT(_uncoarseningData.round_coarsening_times.size() == _uncoarseningData.removed_hyperedges_batches.size());
    _uncoarseningData.round_coarsening_times.push_back(_uncoarseningData.round_coarsening_times.size() > 0 ?
      _uncoarseningData.round_coarsening_times.back() : std::numeric_limits<double>::max()); // Sentinel

    if ( _timer.isEnabled() ) {
      _timer.disable();
      _is_timer_disabled = true;
    }
  }

  template<typename TypeTraits>
  bool NLevelUncoarsener<TypeTraits>::isTopLevelImpl() const {
    return _hierarchy.empty();
  }

  template<typename TypeTraits>
  void NLevelUncoarsener<TypeTraits>::projectToNextLevelAndRefineImpl() {
    BatchVector& batches = _hierarchy.back();

    // Uncontracts all batches from one coarsening pass. One coarsening pass iterates over all
    // nodes and contracts each node onto another node. Afterwards, we remove all single-pin and
    // identical nets. The following loop reverts all contractions and restores single-pin and
    // identical nets.
    while ( !batches.empty() ) {
      const Batch& batch = batches.back();
      if ( batch.size() > 0 ) {
        HEAVY_REFINEMENT_ASSERT(metrics::quality(*_uncoarseningData.partitioned_hg, _context) == _current_metrics.quality,
          V(_current_metrics.quality) << V(metrics::quality(*_uncoarseningData.partitioned_hg, _context)));

        // Performs batch uncontraction operation
        _timer.start_timer("batch_uncontractions", "Batch Uncontractions", false, _force_measure_timings);
        GainCachePtr::uncontract(*_uncoarseningData.partitioned_hg, batch, _gain_cache);
        _timer.stop_timer("batch_uncontractions", _force_measure_timings);

        HEAVY_REFINEMENT_ASSERT(_hg.verifyIncidenceArrayAndIncidentNets());
        HEAVY_REFINEMENT_ASSERT(GainCachePtr::checkTrackedPartitionInformation(*_uncoarseningData.partitioned_hg, _gain_cache));
        HEAVY_REFINEMENT_ASSERT(metrics::quality(*_uncoarseningData.partitioned_hg, _context) == _current_metrics.quality,
          V(_current_metrics.quality) << V(metrics::quality(*_uncoarseningData.partitioned_hg, _context)));

        // Extracts all border vertices of the current batch
        _timer.start_timer("collect_border_vertices", "Collect Border Vertices", false, _force_measure_timings);
        tbb::parallel_for(UL(0), batch.size(), [&](const size_t i) {
          const Memento& memento = batch[i];
          if ( !_border_vertices_of_batch[memento.u] && _uncoarseningData.partitioned_hg->isBorderNode(memento.u) ) {
            _border_vertices_of_batch.set(memento.u, true);
            _tmp_refinement_nodes.stream(memento.u);
          }
          if ( !_border_vertices_of_batch[memento.v] && _uncoarseningData.partitioned_hg->isBorderNode(memento.v) ) {
            _border_vertices_of_batch.set(memento.v, true);
            _tmp_refinement_nodes.stream(memento.v);
          }
        });
        _timer.stop_timer("collect_border_vertices", _force_measure_timings);

        // We perform localized refinement around the uncontracted nodes if the current number
        // of border nodes is greater than a predefined threshold.
        if ( _tmp_refinement_nodes.size() >= _stats.min_num_border_vertices ) {
          localizedRefine(*_uncoarseningData.partitioned_hg);
        }

        ++_stats.num_batches;
        _stats.total_batch_sizes += batch.size();
        // Update Progress Bar
        _progress.setObjective(_current_metrics.quality);
        _progress += batch.size();
        _stats.current_number_of_nodes += batch.size();
      }
      batches.pop_back();
    }

    // Perform localized refinement on the remaining nodes such that we do
    // not miss any improvement.
    if ( _tmp_refinement_nodes.size() > 0 ) {
      localizedRefine(*_uncoarseningData.partitioned_hg);
    }

    // Restore single-pin and identical nets
    if ( !_uncoarseningData.removed_hyperedges_batches.empty() ) {
      _timer.start_timer("restore_single_pin_and_parallel_nets", "Restore Single Pin and Parallel Nets", false, _force_measure_timings);
      GainCachePtr::restoreSinglePinAndParallelNets(*_uncoarseningData.partitioned_hg,
        _uncoarseningData.removed_hyperedges_batches.back(), _gain_cache);
      _uncoarseningData.removed_hyperedges_batches.pop_back();
      _timer.stop_timer("restore_single_pin_and_parallel_nets", _force_measure_timings);
      HEAVY_REFINEMENT_ASSERT(_hg.verifyIncidenceArrayAndIncidentNets());
      HEAVY_REFINEMENT_ASSERT(GainCachePtr::checkTrackedPartitionInformation(*_uncoarseningData.partitioned_hg, _gain_cache));

      // After restoring all single-pin and identical-nets, we perform an additional
      // refinement step on all border nodes.
      IUncoarsener<TypeTraits>::refine();
      _progress.setObjective(_current_metrics.quality);
      _uncoarseningData.round_coarsening_times.pop_back();
    }

    _hierarchy.pop_back();

    if ( _hierarchy.empty() ) {
      // After we reach the top-level hypergraph, we perform an additional
      // refinement step on all border nodes.
      const HyperedgeWeight objective_before = _current_metrics.quality;
      const double time_limit = Base::refinementTimeLimit(_context, _uncoarseningData.round_coarsening_times.back());
      globalRefine(*_uncoarseningData.partitioned_hg, time_limit);
      _uncoarseningData.round_coarsening_times.pop_back();
      ASSERT(_uncoarseningData.round_coarsening_times.size() == 0);
      const HyperedgeWeight objective_after = _current_metrics.quality;
      if ( _context.partition.enable_logging
           && _context.partition.verbose_logging
           && objective_after < objective_before ) {
        LOG << GREEN << "Top-Level Refinment improved objective from"
        << objective_before << "to" << objective_after << END;
      }

      if ( _is_timer_disabled ) {
        _timer.enable();
      }
    }
  }

  template<typename TypeTraits>
  void NLevelUncoarsener<TypeTraits>::refineImpl() {
    const double time_limit = _uncoarseningData.round_coarsening_times.empty() ?
      std::numeric_limits<double>::max() : Base::refinementTimeLimit(_context, _uncoarseningData.round_coarsening_times.back());
    globalRefine(*_uncoarseningData.partitioned_hg, time_limit);
  }

  template<typename TypeTraits>
  void NLevelUncoarsener<TypeTraits>::rebalancingImpl() {
    // If we reach the top-level hypergraph and the partition is still imbalanced,
    // we use a rebalancing algorithm to restore balance.
    if ( _context.type == ContextType::main && !metrics::isValidPartition(*_uncoarseningData.partitioned_hg, _context)) {
      Base::applyRebalancing();
    }
  }

  template<typename TypeTraits>
  HyperedgeWeight NLevelUncoarsener<TypeTraits>::getObjectiveImpl() const {
    return _current_metrics.quality;
  }

  template<typename TypeTraits>
  void NLevelUncoarsener<TypeTraits>::updateMetricsImpl() {
    _current_metrics = Base::initializeMetrics(*_uncoarseningData.partitioned_hg);
    _progress.setObjective(_current_metrics.quality);
  }

  template<typename TypeTraits>
  typename TypeTraits::PartitionedHypergraph& NLevelUncoarsener<TypeTraits>::currentPartitionedHypergraphImpl() {
    return *_uncoarseningData.partitioned_hg;
  }

  template<typename TypeTraits>
  HypernodeID NLevelUncoarsener<TypeTraits>::currentNumberOfNodesImpl() const {
    return _stats.current_number_of_nodes;
  }

  template<typename TypeTraits>
  typename TypeTraits::PartitionedHypergraph&& NLevelUncoarsener<TypeTraits>::movePartitionedHypergraphImpl() {
    ASSERT(isTopLevelImpl());
    return std::move(*_uncoarseningData.partitioned_hg);
  }

  template<typename TypeTraits>
  void NLevelUncoarsener<TypeTraits>::localizedRefine(PartitionedHypergraph& partitioned_hypergraph) {
    // Copy all border nodes into one vector
    vec<HypernodeID> refinement_nodes = _tmp_refinement_nodes.copy_parallel();
    _tmp_refinement_nodes.clear_parallel();
    _border_vertices_of_batch.reset();

    if ( debug && _context.type == ContextType::main ) {
      io::printHypergraphInfo(partitioned_hypergraph.hypergraph(),
        _context, "Refinement Hypergraph", false);
      DBG << "Start Refinement - objective = " << _current_metrics.quality
          << ", imbalance = " << _current_metrics.imbalance;
    }

    _timer.start_timer("local_refinement", "Local Refinement", false, _force_measure_timings);
    bool improvement_found = true;
    mt_kahypar_partitioned_hypergraph_t phg = utils::partitioned_hg_cast(partitioned_hypergraph);
    while( improvement_found ) {
      improvement_found = false;

      if ( _label_propagation && _context.refinement.label_propagation.algorithm != LabelPropagationAlgorithm::do_nothing ) {
        _timer.start_timer("local_label_propagation", "Label Propagation", false, _force_measure_timings);
        improvement_found |= _label_propagation->refine(phg,
          refinement_nodes, _current_metrics, std::numeric_limits<double>::max());
        _timer.stop_timer("local_label_propagation", _force_measure_timings);
      }

      if ( _fm && _context.refinement.fm.algorithm != FMAlgorithm::do_nothing ) {
        _timer.start_timer("local_fm", "FM", false, _force_measure_timings);
        improvement_found |= _fm->refine(phg,
          refinement_nodes, _current_metrics, std::numeric_limits<double>::max());
        _timer.stop_timer("local_fm", _force_measure_timings);
      }

      if ( _context.type == ContextType::main ) {
        ASSERT(_current_metrics.quality == metrics::quality(partitioned_hypergraph, _context.partition.objective),
            "Actual metric" << V(metrics::quality(partitioned_hypergraph, _context)) <<
            "does not match the metric updated by the refiners" << V(_current_metrics.quality));
      }

      if ( !_context.refinement.refine_until_no_improvement ) {
        break;
      }
    }
    _timer.stop_timer("local_refinement", _force_measure_timings);

    if ( _context.type == ContextType::main) {
      DBG << "--------------------------------------------------\n";
    }
  }

  template<typename TypeTraits>
  void NLevelUncoarsener<TypeTraits>::globalRefine(PartitionedHypergraph& partitioned_hypergraph,
                                       const double time_limit) {
    if ( _context.refinement.global.use_global_refinement ) {
      if ( debug && _context.type == ContextType::main ) {
        io::printHypergraphInfo(partitioned_hypergraph.hypergraph(),
          _context, "Refinement Hypergraph", false);
        DBG << "Start Refinement - objective = " << _current_metrics.quality
            << ", imbalance = " << _current_metrics.imbalance;
      }

      // Enable Timings
      bool was_enabled = false;
      if ( !_timer.isEnabled() &&
           _context.type == ContextType::main ) {
        _timer.enable();
        was_enabled = true;
      }

      // Apply global FM parameters to FM context and temporary store old fm context
      _timer.start_timer("global_refinement", "Global Refinement");
      bool improvement_found = true;
      mt_kahypar_partitioned_hypergraph_t phg = utils::partitioned_hg_cast(partitioned_hypergraph);
      runInGlobalRefinementContext([&]{
        while( improvement_found ) {
          improvement_found = false;
          const HyperedgeWeight metric_before = _current_metrics.quality;

          IRefiner* lp_ptr = _global_label_propagation ? _global_label_propagation.get() : _label_propagation.get();
          if ( lp_ptr && _context.refinement.label_propagation.algorithm != LabelPropagationAlgorithm::do_nothing ) {
            _timer.start_timer("label_propagation", "Label Propagation");
              improvement_found |= lp_ptr->refine(phg, {}, _current_metrics, time_limit);
            _timer.stop_timer("label_propagation");
          }

          if ( _jet && _context.refinement.jet.algorithm != JetAlgorithm::do_nothing ) {
            _timer.start_timer("initialize_jet_refiner", "Initialize Jet Refiner");
            _jet->initialize(phg);
            _timer.stop_timer("initialize_jet_refiner");

            _timer.start_timer("jet", "Jet");
            improvement_found |= _jet->refine(phg, {}, _current_metrics, time_limit);
            _timer.stop_timer("jet");
          }

          IRefiner* fm_ptr = _global_fm ? _global_fm.get() : _fm.get();
          if ( fm_ptr && _context.refinement.global.fm_algorithm != FMAlgorithm::do_nothing ) {
            _timer.start_timer("fm", "FM");
              improvement_found |= fm_ptr->refine(phg, {}, _current_metrics, time_limit);
            _timer.stop_timer("fm");
          }

          if ( _flows && _context.refinement.flows.algorithm != FlowAlgorithm::do_nothing ) {
            _timer.start_timer("initialize_flow_scheduler", "Initialize Flow Scheduler");
            _flows->initialize(phg);
            _timer.stop_timer("initialize_flow_scheduler");

            _timer.start_timer("flow_refinement_scheduler", "Flow Refinement Scheduler");
            improvement_found |= _flows->refine(phg, {}, _current_metrics, time_limit);
            _timer.stop_timer("flow_refinement_scheduler");
          }

          if ( _context.type == ContextType::main ) {
            ASSERT(_current_metrics.quality == metrics::quality(partitioned_hypergraph, _context.partition.objective),
                "Actual metric" << V(metrics::quality(partitioned_hypergraph, _context)) <<
                "does not match the metric updated by the refiners" << V(_current_metrics.quality));
          }

          const HyperedgeWeight metric_after = _current_metrics.quality;
          const double relative_improvement = 1.0 -
            static_cast<double>(metric_after) / metric_before;
          if ( !_context.refinement.global.refine_until_no_improvement ||
              relative_improvement <= _context.refinement.relative_improvement_threshold ) {
            break;
          }
        }
      });
      _timer.stop_timer("global_refinement");

      if ( was_enabled ) {
        _timer.disable();
      }

      if ( _context.type == ContextType::main) {
        DBG << "--------------------------------------------------\n";
      }
    }
  }

  template<typename TypeTraits>
  template<typename Func>
  void NLevelUncoarsener<TypeTraits>::runInGlobalRefinementContext(Func func) {
    auto applyGlobalFMParameters = [&](const LabelPropagationParameters& label_propagation, const FMParameters& fm, const NLevelGlobalRefinementParameters global){
      NLevelGlobalRefinementParameters tmp_global;
      tmp_global.fm_algorithm = fm.algorithm;
      tmp_global.fm_num_seed_nodes = fm.num_seed_nodes;
      tmp_global.fm_obey_minimal_parallelism = fm.obey_minimal_parallelism;
      tmp_global.lp_unconstrained = label_propagation.unconstrained;
      fm.algorithm = global.fm_algorithm;
      fm.num_seed_nodes = global.fm_num_seed_nodes;
      fm.obey_minimal_parallelism = global.fm_obey_minimal_parallelism;
      label_propagation.unconstrained = global.lp_unconstrained;
      return tmp_global;
    };

    NLevelGlobalRefinementParameters tmp_global = applyGlobalFMParameters(
      _context.refinement.label_propagation, _context.refinement.fm, _context.refinement.global);
    func();

    // Reset FM context
    applyGlobalFMParameters(_context.refinement.label_propagation, _context.refinement.fm, tmp_global);
  }

  INSTANTIATE_CLASS_WITH_TYPE_TRAITS(NLevelUncoarsener)

}
