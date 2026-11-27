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

#include "mt-kahypar/partition/multilevel.h"

#include <memory>

#include <tbb/task.h>

#include "include/mtkahypartypes.h"

#include "mt-kahypar/definitions.h"
#include "mt-kahypar/partition/factories.h"
#include "mt-kahypar/partition/preprocessing/sparsification/degree_zero_hn_remover.h"
#include "mt-kahypar/partition/preprocessing/sparsification/large_he_remover.h"
#include "mt-kahypar/partition/initial_partitioning/pool_initial_partitioner.h"
#include "mt-kahypar/partition/recursive_bipartitioning.h"
#include "mt-kahypar/partition/deep_multilevel.h"
#ifdef KAHYPAR_ENABLE_STEINER_TREE_METRIC
#include "mt-kahypar/partition/mapping/initial_mapping.h"
#endif
#include "mt-kahypar/parallel/memory_pool.h"
#include "mt-kahypar/io/partitioning_output.h"
#include "mt-kahypar/partition/coarsening/multilevel/multilevel_uncoarsener.h"
#ifdef KAHYPAR_ENABLE_HIGHEST_QUALITY_FEATURES
#include "mt-kahypar/partition/coarsening/nlevel/nlevel_uncoarsener.h"
#endif
#include "mt-kahypar/utils/cast.h"
#include "mt-kahypar/utils/utilities.h"
#include "mt-kahypar/utils/exception.h"

namespace mt_kahypar {

namespace {
  void disableTimerAndStats(const Context& context) {
    if ( context.type == ContextType::main && context.partition.mode == Mode::direct ) {
      utils::Utilities& utils = utils::Utilities::instance();
      parallel::MemoryPool::instance().deactivate_unused_memory_allocations();
      utils.getTimer(context.utility_id).disable();
      utils.getStats(context.utility_id).disable();
    }
  }

  void enableTimerAndStats(const Context& context) {
    if ( context.type == ContextType::main && context.partition.mode == Mode::direct ) {
      utils::Utilities& utils = utils::Utilities::instance();
      parallel::MemoryPool::instance().activate_unused_memory_allocations();
      utils.getTimer(context.utility_id).enable();
      utils.getStats(context.utility_id).enable();
    }
  }

  template<typename TypeTraits>
  typename TypeTraits::PartitionedHypergraph multilevel_partitioning(
    typename TypeTraits::Hypergraph& hypergraph,
    const Context& context,
    const TargetGraph* target_graph,
    const bool is_vcycle) {
    using Hypergraph = typename TypeTraits::Hypergraph;
    using PartitionedHypergraph = typename TypeTraits::PartitionedHypergraph;
    PartitionedHypergraph partitioned_hg;

    // ################## COARSENING ##################
    mt_kahypar::io::printCoarseningBanner(context);

    const bool nlevel = context.isNLevelPartitioning();
    UncoarseningData<TypeTraits> uncoarseningData(nlevel, hypergraph, context);

    utils::Timer& timer = utils::Utilities::instance().getTimer(context.utility_id);
    timer.start_timer("coarsening", "Coarsening");
    {
      std::unique_ptr<ICoarsener> coarsener = CoarsenerFactory::getInstance().createObject(
        context.coarsening.algorithm, utils::hypergraph_cast(hypergraph),
        context, uncoarsening::to_pointer(uncoarseningData));
      coarsener->coarsen();

      if (context.partition.enable_logging) {
        mt_kahypar_hypergraph_t coarsestHypergraph = coarsener->coarsestHypergraph();
        mt_kahypar::io::printHypergraphInfo(
          utils::cast<Hypergraph>(coarsestHypergraph), context,
          "Coarsened Hypergraph", context.partition.show_memory_consumption);
      }
    }
    timer.stop_timer("coarsening");

    // ################## INITIAL PARTITIONING ##################
    io::printInitialPartitioningBanner(context);
    timer.start_timer("initial_partitioning", "Initial Partitioning");
    PartitionedHypergraph& phg = uncoarseningData.coarsestPartitionedHypergraph();

    if ( !is_vcycle ) {
      DegreeZeroHypernodeRemover<TypeTraits> degree_zero_hn_remover(context);
      if ( context.initial_partitioning.remove_degree_zero_hns_before_ip ) {
        degree_zero_hn_remover.removeDegreeZeroHypernodes(phg.hypergraph());
      }

      Context ip_context(context);
      ip_context.type = ContextType::initial_partitioning;
      ip_context.refinement = context.initial_partitioning.refinement;
      disableTimerAndStats(context);
      if ( context.initial_partitioning.mode == Mode::direct ) {
        // The pool initial partitioner consist of several flat bipartitioning
        // techniques. This case runs as a base case (k = 2) within recursive bipartitioning
        // or the deep multilevel scheme.
        ip_context.partition.enable_logging = false;
        Pool<TypeTraits>::bipartition(phg, ip_context);
      } else if ( context.initial_partitioning.mode == Mode::recursive_bipartitioning ) {
        RecursiveBipartitioning<TypeTraits>::partition(phg, ip_context, target_graph);
      } else if ( context.initial_partitioning.mode == Mode::deep_multilevel ) {
        ASSERT(ip_context.partition.objective != Objective::steiner_tree);
        ip_context.partition.enable_logging = false;
        DeepMultilevel<TypeTraits>::partition(phg, ip_context);
      } else {
        throw InvalidParameterException("Undefined initial partitioning algorithm");
      }
      enableTimerAndStats(context);
      degree_zero_hn_remover.restoreDegreeZeroHypernodes(phg);
    } else {
      // When performing a V-cycle, we store the block IDs
      // of the input hypergraph as community IDs
      const Hypergraph& hypergraph = phg.hypergraph();
      phg.doParallelForAllNodes([&](const HypernodeID hn) {
        const PartitionID part_id = hypergraph.communityID(hn);
        ASSERT(part_id != kInvalidPartition && part_id < context.partition.k);
        ASSERT(phg.partID(hn) == kInvalidPartition);
        phg.setOnlyNodePart(hn, part_id);
      });
      phg.initializePartition();

      #ifdef KAHYPAR_ENABLE_STEINER_TREE_METRIC
      if ( context.partition.objective == Objective::steiner_tree ) {
        phg.setTargetGraph(target_graph);
        timer.start_timer("one_to_one_mapping", "One-To-One Mapping");
        // Try to improve current mapping
        InitialMapping<TypeTraits>::mapToTargetGraph(
          phg, *target_graph, context);
        timer.stop_timer("one_to_one_mapping");
      }
      #endif
    }

    ASSERT([&] {
      bool success = true;
      if ( phg.hasFixedVertices() ) {
        for ( const HypernodeID& hn : phg.nodes() ) {
          if ( phg.isFixed(hn) && phg.fixedVertexBlock(hn) != phg.partID(hn) ) {
            LOG << "Node" << hn << "is fixed to block" << phg.fixedVertexBlock(hn)
                << ", but is assigned to block" << phg.partID(hn);
            success = false;
          }
        }
      }
      return success;
    }(), "Some fixed vertices are not assigned to their corresponding block");

    if ( context.partition.objective == Objective::steiner_tree ) {
      phg.setTargetGraph(target_graph);
    }
    io::printPartitioningResults(phg, context, "Initial Partitioning Results:");
    if ( context.partition.enable_logging && context.partition.verbose_logging && !is_vcycle ) {
      utils::Utilities::instance().getInitialPartitioningStats(
        context.utility_id).printInitialPartitioningStats();
    }
    timer.stop_timer("initial_partitioning");

    // ################## UNCOARSENING ##################
    io::printLocalSearchBanner(context);
    timer.start_timer("refinement", "Refinement");
    std::unique_ptr<IUncoarsener<TypeTraits>> uncoarsener(nullptr);
    if (uncoarseningData.nlevel) {
      #ifdef KAHYPAR_ENABLE_HIGHEST_QUALITY_FEATURES
        uncoarsener = std::make_unique<NLevelUncoarsener<TypeTraits>>(
          hypergraph, context, uncoarseningData, target_graph);
      #else
        throw InvalidParameterException("NLevel features are deactivated.");
      #endif
    } else {
      uncoarsener = std::make_unique<MultilevelUncoarsener<TypeTraits>>(
        hypergraph, context, uncoarseningData, target_graph);
    }
    partitioned_hg = uncoarsener->uncoarsen();

    io::printPartitioningResults(partitioned_hg, context, "Local Search Results:");
    timer.stop_timer("refinement");

    return partitioned_hg;
  }
}

template<typename TypeTraits>
typename Multilevel<TypeTraits>::PartitionedHypergraph Multilevel<TypeTraits>::partition(
  Hypergraph& hypergraph, const Context& context, const TargetGraph* target_graph) {
  PartitionedHypergraph partitioned_hg =
    multilevel_partitioning<TypeTraits>(hypergraph, context, target_graph, false);

  // ################## V-CYCLES ##################
  if ( context.partition.num_vcycles > 0 && context.type == ContextType::main ) {
    partitionVCycle(hypergraph, partitioned_hg, context, target_graph);
  }

  return partitioned_hg;
}

template<typename TypeTraits>
void Multilevel<TypeTraits>::partition(PartitionedHypergraph& partitioned_hg,
                                       const Context& context,
                                       const TargetGraph* target_graph) {
  PartitionedHypergraph tmp_phg = partition(
    partitioned_hg.hypergraph(), context, target_graph);
  tmp_phg.doParallelForAllNodes([&](const HypernodeID& hn) {
    partitioned_hg.setOnlyNodePart(hn, tmp_phg.partID(hn));
  });
  partitioned_hg.initializePartition();
}

template<typename TypeTraits>
void Multilevel<TypeTraits>::partitionVCycle(Hypergraph& hypergraph,
                                             PartitionedHypergraph& partitioned_hg,
                                             const Context& context,
                                             const TargetGraph* target_graph) {
  ASSERT(context.partition.num_vcycles > 0);

  for ( size_t i = 0; i < context.partition.num_vcycles; ++i ) {
    // Reset memory pool
    hypergraph.reset();
    parallel::MemoryPool::instance().reset();
    parallel::MemoryPool::instance().release_mem_group("Preprocessing");

    if ( context.isNLevelPartitioning() ) {
      // Workaround: reset() function of hypergraph reinserts all removed hyperedges again.
      LargeHyperedgeRemover<TypeTraits> large_he_remover(context);
      large_he_remover.removeLargeHyperedgesInNLevelVCycle(hypergraph);
    }

    // The block IDs of the current partition are stored as community IDs.
    // This way coarsening does not contract nodes that do not belong to same block
    // of the input partition. For initial partitioning, we use the community IDs of
    // smallest hypergraph as initial partition.
    hypergraph.doParallelForAllNodes([&](const HypernodeID& hn) {
      hypergraph.setCommunityID(hn, partitioned_hg.partID(hn));
    });

    // Perform V-cycle
    io::printVCycleBanner(context, i + 1);
    partitioned_hg = multilevel_partitioning<TypeTraits>(
      hypergraph, context, target_graph, true /* V-cycle flag */ );
  }
}

INSTANTIATE_CLASS_WITH_TYPE_TRAITS(Multilevel)

}
