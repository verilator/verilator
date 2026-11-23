/*******************************************************************************
 * MIT License
 *
 * This file is part of Mt-KaHyPar.
 *
 * Copyright (C) 2021 Noah Wahl <noah.wahl@student.kit.edu>
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

#include "mt-kahypar/partition/coarsening/multilevel/multilevel_uncoarsener.h"
#include "mt-kahypar/definitions.h"
#include "mt-kahypar/io/partitioning_output.h"
#include "mt-kahypar/partition/refinement/i_refiner.h"
#include "mt-kahypar/partition/metrics.h"
#include "mt-kahypar/utils/stats.h"
#include "mt-kahypar/utils/cast.h"

namespace mt_kahypar {

  template<typename TypeTraits>
  void MultilevelUncoarsener<TypeTraits>::initializeImpl() {
    PartitionedHypergraph& partitioned_hg = *_uncoarseningData.partitioned_hg;
    _current_metrics = Base::initializeMetrics(partitioned_hg);
    Base::initializeRefinementAlgorithms();

    if (_context.type == ContextType::main) {
      _context.initial_km1 = _current_metrics.quality;
    }

    // Enable progress bar if logging is enabled
    if ( _context.partition.enable_logging && _context.partition.enable_progress_bar && !debug ) {
      _progress.enable();
      _progress.setObjective(_current_metrics.quality);
    }

    // Pass target graph to partitioned hypergraph
    partitioned_hg.setTargetGraph(_target_graph);

    _current_level = _uncoarseningData.hierarchy.size();
    _num_levels = _current_level;
  }

  template<typename TypeTraits>
  bool MultilevelUncoarsener<TypeTraits>::isTopLevelImpl() const {
    return _current_level < 0;
  }

  template<typename TypeTraits>
  void MultilevelUncoarsener<TypeTraits>::projectToNextLevelAndRefineImpl() {
    PartitionedHypergraph& partitioned_hg = *_uncoarseningData.partitioned_hg;
    if ( _current_level == _num_levels ) {
      // We always start with a refinement pass on the smallest hypergraph.
      // The next calls to this function will then project the partition to the next level
      // and perform refinement until we reach the input hypergraph.
      IUncoarsener<TypeTraits>::refine();
      _progress.setObjective(_current_metrics.quality);
      _progress += partitioned_hg.initialNumNodes();
    } else {
      ASSERT(_current_level >= 0);
      // Project partition to the hypergraph on the next level of the hierarchy
      _timer.start_timer("projecting_partition", "Projecting Partition");
      const size_t num_nodes_on_previous_level = partitioned_hg.initialNumNodes();
      if (_current_level == 0) {
        partitioned_hg.setHypergraph(_hg);
      } else {
        partitioned_hg.setHypergraph((_uncoarseningData.hierarchy)[_current_level-1].contractedHypergraph());
      }
      // Hypergraph stores partition from previous level.
      // We now extract the block ids and reset the partition to reuse the
      // data structure for the current level.
      partitioned_hg.extractPartIDs(_block_ids);
      partitioned_hg.resetData();
      GainCachePtr::resetGainCache(_gain_cache, num_nodes_on_previous_level, partitioned_hg.k());

      // Assign nodes of current level to their corresponding representative of the previous level
      partitioned_hg.doParallelForAllNodes([&](const HypernodeID hn) {
        const HypernodeID coarse_hn = (_uncoarseningData.hierarchy)[_current_level].mapToContractedHypergraph(hn);
        const PartitionID block = _block_ids[coarse_hn];
        ASSERT(block != kInvalidPartition && block < partitioned_hg.k());
        partitioned_hg.setOnlyNodePart(hn, block);
      });
      partitioned_hg.initializePartition();
      _timer.stop_timer("projecting_partition");

      // some imbalance constraints (empty blocks) can be different on top level
      _current_metrics.imbalance = metrics::imbalance(partitioned_hg, _context);

      // Improve partition
      IUncoarsener<TypeTraits>::refine();

      // Update Progress Bar
      _progress.setObjective(_current_metrics.quality);
      _progress += partitioned_hg.initialNumNodes() - num_nodes_on_previous_level;
    }

    ASSERT(metrics::quality(*_uncoarseningData.partitioned_hg, _context) == _current_metrics.quality,
      V(_current_metrics.quality) << V(metrics::quality(*_uncoarseningData.partitioned_hg, _context)));

    --_current_level;
  }

  template<typename TypeTraits>
  void MultilevelUncoarsener<TypeTraits>::rebalancingImpl() {
    // If we reach the top-level hypergraph and the partition is still imbalanced,
    // we use a rebalancing algorithm to restore balance.
    if (_context.type == ContextType::main && !metrics::isValidPartition(*_uncoarseningData.partitioned_hg, _context)) {
      Base::applyRebalancing();
    }
  }

  template<typename TypeTraits>
  HyperedgeWeight MultilevelUncoarsener<TypeTraits>::getObjectiveImpl() const {
    return _current_metrics.quality;
  }

  template<typename TypeTraits>
  void MultilevelUncoarsener<TypeTraits>::updateMetricsImpl() {
    _current_metrics = Base::initializeMetrics(*_uncoarseningData.partitioned_hg);
    _progress.setObjective(_current_metrics.quality);
  }

  template<typename TypeTraits>
  typename TypeTraits::PartitionedHypergraph& MultilevelUncoarsener<TypeTraits>::currentPartitionedHypergraphImpl() {
    return *_uncoarseningData.partitioned_hg;
  }

  template<typename TypeTraits>
  HypernodeID MultilevelUncoarsener<TypeTraits>::currentNumberOfNodesImpl() const {
    return _uncoarseningData.partitioned_hg->initialNumNodes();
  }

  template<typename TypeTraits>
  typename TypeTraits::PartitionedHypergraph&& MultilevelUncoarsener<TypeTraits>::movePartitionedHypergraphImpl() {
    ASSERT(isTopLevelImpl());
    return std::move(*_uncoarseningData.partitioned_hg);
  }

  template<typename TypeTraits>
  void MultilevelUncoarsener<TypeTraits>::refineImpl() {
    PartitionedHypergraph& partitioned_hypergraph = *_uncoarseningData.partitioned_hg;
    double time_limit = std::numeric_limits<double>::max();
    if (_current_level >= 0 && _current_level != _num_levels) {
      // there is a refinement run on the coarsest graph before projection. There is no value stored for this run, so we must avoid looking it up.
      time_limit = Base::refinementTimeLimit(_context, (_uncoarseningData.hierarchy)[_current_level].coarseningTime());
    }

    if ( debug && _context.type == ContextType::main ) {
      io::printHypergraphInfo(partitioned_hypergraph.hypergraph(),
        _context, "Refinement Hypergraph", false);
      DBG << "Start Refinement -" << _context.partition.objective << "=" << _current_metrics.quality
      << ", imbalance = " << _current_metrics.imbalance;
    }

    parallel::scalable_vector<HypernodeID> dummy;
    mt_kahypar_partitioned_hypergraph_t phg = utils::partitioned_hg_cast(partitioned_hypergraph);

    ASSERT(_rebalancer);
    if ( _context.refinement.rebalancing.algorithm != RebalancingAlgorithm::do_nothing ) {
      _rebalancer->initialize(phg);
    }
    if ( !metrics::isValidPartition(partitioned_hypergraph, _context) && _context.refinement.rebalancing.algorithm != RebalancingAlgorithm::do_nothing ) {
      _timer.start_timer("rebalance", "Rebalance");
      _rebalancer->refine(phg, dummy, _current_metrics, 0.0);
      _timer.stop_timer("rebalance");
    }

    bool improvement_found = true;
    while( improvement_found ) {
      improvement_found = false;
      const HyperedgeWeight metric_before = _current_metrics.quality;

      if ( _label_propagation && _context.refinement.label_propagation.algorithm != LabelPropagationAlgorithm::do_nothing ) {
        _timer.start_timer("initialize_lp_refiner", "Initialize LP Refiner");
        _label_propagation->initialize(phg);
        _timer.stop_timer("initialize_lp_refiner");

        _timer.start_timer("label_propagation", "Label Propagation");
        improvement_found |= _label_propagation->refine(phg, dummy, _current_metrics, time_limit);
        _timer.stop_timer("label_propagation");
      }

      if ( _jet && _context.refinement.jet.algorithm != JetAlgorithm::do_nothing ) {
        _timer.start_timer("initialize_jet_refiner", "Initialize Jet Refiner");
        _jet->initialize(phg);
        _timer.stop_timer("initialize_jet_refiner");

        _timer.start_timer("jet", "Jet");
        improvement_found |= _jet->refine(phg, dummy, _current_metrics, time_limit);
        _timer.stop_timer("jet");
      }

      if ( _fm && _context.refinement.fm.algorithm != FMAlgorithm::do_nothing ) {
        _timer.start_timer("initialize_fm_refiner", "Initialize FM Refiner");
        _fm->initialize(phg);
        _timer.stop_timer("initialize_fm_refiner");

        _timer.start_timer("fm", "FM");
        improvement_found |= _fm->refine(phg, dummy, _current_metrics, time_limit);
        _timer.stop_timer("fm");
      }

      if ( _flows && _context.refinement.flows.algorithm != FlowAlgorithm::do_nothing ) {
        _timer.start_timer("initialize_flow_scheduler", "Initialize Flow Scheduler");
        _flows->initialize(phg);
        _timer.stop_timer("initialize_flow_scheduler");

        _timer.start_timer("flow_refinement_scheduler", "Flow Refinement Scheduler");
        improvement_found |= _flows->refine(phg, dummy, _current_metrics, time_limit);
        _timer.stop_timer("flow_refinement_scheduler");
      }

      if ( _context.type == ContextType::main ) {
        ASSERT(_current_metrics.quality == metrics::quality(partitioned_hypergraph, _context),
          "Actual metric" << V(metrics::quality(partitioned_hypergraph, _context)) <<
          "does not match the metric updated by the refiners" << V(_current_metrics.quality));
      }

      const HyperedgeWeight metric_after = _current_metrics.quality;
      const double relative_improvement = 1.0 -
        static_cast<double>(metric_after) / metric_before;
      if ( !_context.refinement.refine_until_no_improvement ||
           relative_improvement <= _context.refinement.relative_improvement_threshold ) {
        break;
      }
    }

    if ( _context.type == ContextType::main) {
      DBG << "--------------------------------------------------\n";
    }
  }

  INSTANTIATE_CLASS_WITH_TYPE_TRAITS(MultilevelUncoarsener)

}
