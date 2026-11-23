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

#include "partitioner.h"

#include <tbb/parallel_sort.h>
#include <tbb/parallel_reduce.h>

#include "mt-kahypar/definitions.h"
#include "mt-kahypar/io/partitioning_output.h"
#include "mt-kahypar/partition/multilevel.h"
#include "mt-kahypar/partition/preprocessing/sparsification/degree_zero_hn_remover.h"
#include "mt-kahypar/partition/preprocessing/sparsification/large_he_remover.h"
#include "mt-kahypar/partition/preprocessing/community_detection/parallel_louvain.h"
#include "mt-kahypar/partition/recursive_bipartitioning.h"
#include "mt-kahypar/partition/deep_multilevel.h"
#include "mt-kahypar/partition/mapping/target_graph.h"
#ifdef KAHYPAR_ENABLE_STEINER_TREE_METRIC
#include "mt-kahypar/partition/mapping/initial_mapping.h"
#endif
#include "mt-kahypar/utils/hypergraph_statistics.h"
#include "mt-kahypar/utils/stats.h"
#include "mt-kahypar/utils/timer.h"
#include "mt-kahypar/utils/exception.h"
#include "mt-kahypar/utils/utilities.h"


namespace mt_kahypar {

  template<typename Hypergraph>
  void setupContext(Hypergraph& hypergraph, Context& context, TargetGraph* target_graph) {
    if ( target_graph ) {
      context.partition.k = target_graph->numBlocks();
    }

    context.partition.large_hyperedge_size_threshold =
      std::max(static_cast<HypernodeID>(hypergraph.initialNumNodes() * context.partition.large_hyperedge_size_threshold_factor),
               context.partition.smallest_large_he_size_threshold);
    context.sanityCheck(target_graph);
    context.setupPartWeights(hypergraph.totalWeight());
    context.setupContractionLimit(hypergraph.totalWeight());
    context.setupThreadsPerFlowSearch();

    if ( context.partition.gain_policy == GainPolicy::steiner_tree ) {
      const PartitionID k = target_graph ? target_graph->numBlocks() : 1;
      const PartitionID max_k = Hypergraph::is_graph ? 256 : 64;
      if ( k  > max_k ) {
        const std::string type = Hypergraph::is_graph ? "graphs" : "hypergraphs";
        throw InvalidInputException(
          "We currently only support mappings of " + type + " onto target graphs with at "
          "most " + STR(max_k) + "nodes!");
      }

      if ( context.mapping.largest_he_fraction > 0.0 ) {
        // Determine a threshold of what we consider a large hyperedge in
        // the steiner tree gain cache
        vec<HypernodeID> he_sizes(hypergraph.initialNumEdges(), 0);
        hypergraph.doParallelForAllEdges([&](const HyperedgeID& he) {
          he_sizes[he] = hypergraph.edgeSize(he);
        });
        // Sort hyperedges in decreasing order of their sizes
        tbb::parallel_sort(he_sizes.begin(), he_sizes.end(),
          [&](const HypernodeID& lhs, const HypernodeID& rhs) {
            return lhs > rhs;
          });
        const size_t percentile = context.mapping.largest_he_fraction * hypergraph.initialNumEdges();
        // Compute the percentage of pins covered by the largest hyperedges
        const double covered_pins_percentage =
          static_cast<double>(tbb::parallel_reduce(
            tbb::blocked_range<size_t>(UL(0), percentile),
            0, [&](const tbb::blocked_range<size_t>& range, int init) {
                  for ( size_t i = range.begin(); i < range.end(); ++i ) {
                    init += he_sizes[i];
                  }
                  return init;
                }, [&](const int lhs, const int rhs) {
                  return lhs + rhs;
                })) / hypergraph.initialNumPins();
        if ( covered_pins_percentage >= context.mapping.min_pin_coverage_of_largest_hes ) {
          // If the largest hyperedge covers a large portion of the hypergraph, we assume that
          // the hyperedge sizes follow a power law distribution and ignore hyperedges larger than
          // the following threshold when calculating and maintaining the adjacent blocks of node
          // in the steiner tree gain cache.
          context.mapping.large_he_threshold = he_sizes[percentile];
        }
      }
    }

    // Check enabled IP algorithms
    ALWAYS_ASSERT(context.initial_partitioning.enabled_ip_algos.size() == static_cast<size_t>(InitialPartitioningAlgorithm::UNDEFINED));
    bool is_one_ip_algo_enabled = false;
    for ( size_t i = 0; i < context.initial_partitioning.enabled_ip_algos.size(); ++i ) {
      is_one_ip_algo_enabled |= context.initial_partitioning.enabled_ip_algos[i];
    }
    if ( !is_one_ip_algo_enabled ) {
      throw InvalidParameterException(
        "At least one initial partitioning algorithm must be enabled!");
    }

    // Check fixed vertex support compatibility
    if ( hypergraph.hasFixedVertices() ) {
      if ( context.partition.mode == Mode::deep_multilevel ||
           context.initial_partitioning.mode == Mode::deep_multilevel ) {
        throw UnsupportedOperationException(
          "Deep multilevel partitioning scheme does not support fixed vertices!");
      }
    }
  }

  template<typename Hypergraph>
  void configurePreprocessing(const Hypergraph& hypergraph, Context& context) {
    const double density = static_cast<double>(Hypergraph::is_graph ? hypergraph.initialNumEdges() / 2 : hypergraph.initialNumEdges()) /
                           static_cast<double>(hypergraph.initialNumNodes());
    if (context.preprocessing.community_detection.edge_weight_function == LouvainEdgeWeight::hybrid) {
      if (density < 0.75) {
        context.preprocessing.community_detection.edge_weight_function = LouvainEdgeWeight::degree;
      } else if ( density < 2 && hypergraph.maxEdgeSize() > context.partition.ignore_hyperedge_size_threshold ) {
        context.preprocessing.community_detection.edge_weight_function = LouvainEdgeWeight::non_uniform;
      } else {
        context.preprocessing.community_detection.edge_weight_function = LouvainEdgeWeight::uniform;
      }
    }
  }

  template<typename TypeTraits>
  void sanitize(typename TypeTraits::Hypergraph& hypergraph,
                Context& context,
                DegreeZeroHypernodeRemover<TypeTraits>& degree_zero_hn_remover,
                LargeHyperedgeRemover<TypeTraits>& large_he_remover) {

    utils::Timer& timer = utils::Utilities::instance().getTimer(context.utility_id);
    timer.start_timer("degree_zero_hypernode_removal", "Degree Zero Hypernode Removal");
    const HypernodeID num_removed_degree_zero_hypernodes =
            degree_zero_hn_remover.removeDegreeZeroHypernodes(hypergraph);
    timer.stop_timer("degree_zero_hypernode_removal");

    timer.start_timer("large_hyperedge_removal", "Large Hyperedge Removal");
    const HypernodeID num_removed_large_hyperedges =
            large_he_remover.removeSinglePinAndLargeHyperedges(hypergraph);
    timer.stop_timer("large_hyperedge_removal");

    const HyperedgeID total_removed_hes = hypergraph.numRemovedHyperedges();
    const HyperedgeID num_removed_single_node_hes = total_removed_hes - num_removed_large_hyperedges;
    if (context.partition.enable_logging && context.partition.verbose_logging &&
        ( num_removed_single_node_hes > 0 ||
          num_removed_degree_zero_hypernodes > 0 ||
          num_removed_large_hyperedges > 0 )) {
      LOG << "Performed single-node/large HE removal and degree-zero HN contractions:";
      LOG << "\033[1m\033[31m" << " # removed"
          << num_removed_single_node_hes << "single-pin hyperedges"
          << "\033[0m";
      LOG << "\033[1m\033[31m" << " # removed"
          << num_removed_large_hyperedges << "large hyperedges with |e| >" << large_he_remover.largeHyperedgeThreshold() << "\033[0m";
      LOG << "\033[1m\033[31m" << " # contracted"
          << num_removed_degree_zero_hypernodes << "hypernodes with d(v) = 0 and w(v) = 1"
          << "\033[0m";
      io::printStripe();
    }
  }

  template<typename Hypergraph>
  bool isGraph(const Hypergraph& hypergraph) {
    if (Hypergraph::is_graph) {
      return true;
    }
    return tbb::parallel_reduce(tbb::blocked_range<HyperedgeID>(
            ID(0), hypergraph.initialNumEdges()), true, [&](const tbb::blocked_range<HyperedgeID>& range, bool isGraph) {
      if ( isGraph ) {
        bool tmp_is_graph = isGraph;
        for (HyperedgeID he = range.begin(); he < range.end(); ++he) {
          if ( hypergraph.edgeIsEnabled(he) ) {
            tmp_is_graph &= (hypergraph.edgeSize(he) == 2);
          }
        }
        return tmp_is_graph;
      }
      return false;
    }, [&](const bool lhs, const bool rhs) {
      return lhs && rhs;
    });
  }

  template<typename Hypergraph>
  bool isMeshGraph(const Hypergraph& graph) {
    const HypernodeID num_nodes = graph.initialNumNodes();
    const double avg_hn_degree = utils::avgHypernodeDegree(graph);
    std::vector<HyperedgeID> hn_degrees;
    hn_degrees.resize(graph.initialNumNodes());
    graph.doParallelForAllNodes([&](const HypernodeID& hn) {
      hn_degrees[hn] = graph.nodeDegree(hn);
    });
    const double stdev_hn_degree = utils::parallel_stdev(hn_degrees, avg_hn_degree, num_nodes);
    if (stdev_hn_degree > avg_hn_degree / 2) {
      return false;
    }

    // test whether 99.9th percentile hypernode degree is at most 4 times the average degree
    tbb::enumerable_thread_specific<size_t> num_high_degree_nodes(0);
    graph.doParallelForAllNodes([&](const HypernodeID& node) {
      if (graph.nodeDegree(node) > 4 * avg_hn_degree) {
        num_high_degree_nodes.local() += 1;
      }
    });
    return num_high_degree_nodes.combine(std::plus<>()) <= num_nodes / 1000;
  }

  template<typename Hypergraph>
  void precomputeSteinerTrees(Hypergraph& hypergraph, TargetGraph* target_graph, Context& context) {
    if ( target_graph && !target_graph->isInitialized() ) {
      utils::Timer& timer = utils::Utilities::instance().getTimer(context.utility_id);
      timer.start_timer("precompute_steiner_trees", "Precompute Steiner Trees");
      const size_t max_steiner_tree_size = std::min(
        std::min(context.mapping.max_steiner_tree_size, UL(context.partition.k)),
        static_cast<size_t>(hypergraph.maxEdgeSize()));
      target_graph->precomputeDistances(max_steiner_tree_size);
      timer.stop_timer("precompute_steiner_trees");
    }
  }

  template<typename Hypergraph>
  void preprocess(Hypergraph& hypergraph, Context& context, TargetGraph* target_graph) {
    bool use_community_detection = context.preprocessing.use_community_detection;
    bool is_graph = false;

    utils::Timer& timer = utils::Utilities::instance().getTimer(context.utility_id);
    if ( context.preprocessing.use_community_detection ) {
      timer.start_timer("detect_graph_structure", "Detect Graph Structure");
      is_graph = isGraph(hypergraph);
      if ( is_graph && context.preprocessing.disable_community_detection_for_mesh_graphs ) {
        use_community_detection = !isMeshGraph(hypergraph);
      }
      timer.stop_timer("detect_graph_structure");
    }

    if ( use_community_detection ) {
      io::printTopLevelPreprocessingBanner(context);

      timer.start_timer("community_detection", "Community Detection");
      timer.start_timer("construct_graph", "Construct Graph");
      Graph graph(hypergraph, context.preprocessing.community_detection.edge_weight_function, is_graph);
      if ( !context.preprocessing.community_detection.low_memory_contraction ) {
        graph.allocateContractionBuffers();
      }
      timer.stop_timer("construct_graph");
      timer.start_timer("perform_community_detection", "Perform Community Detection");
      ds::Clustering communities = community_detection::run_parallel_louvain(graph, context);
      graph.restrictClusteringToHypernodes(hypergraph, communities);
      hypergraph.setCommunityIDs(std::move(communities));
      timer.stop_timer("perform_community_detection");
      timer.stop_timer("community_detection");

      io::printCommunityInformation(hypergraph, context);
    }

    precomputeSteinerTrees(hypergraph, target_graph, context);

    parallel::MemoryPool::instance().release_mem_group("Preprocessing");
  }

  template<typename PartitionedHypergraph>
  void forceFixedVertexAssignment(PartitionedHypergraph& partitioned_hg,
                                  const Context& context) {
    if ( partitioned_hg.hasFixedVertices() ) {
      // This is a sanity check verifying that all fixed vertices are assigned
      // to their corresponding blocks. If one fixed vertex is assigned to a different
      // block, we move it to its fixed vertex block. Note that a wrong fixed vertex
      // block assignment will fail in debug mode. Thus, this loop should not move any node, but
      // we keep it in case anything goes wrong during partitioning.
      partitioned_hg.doParallelForAllNodes([&](const HypernodeID& hn) {
        if ( partitioned_hg.isFixed(hn) ) {
          const PartitionID from = partitioned_hg.partID(hn);
          const PartitionID to = partitioned_hg.fixedVertexBlock(hn);
          if ( from != to ) {
            if ( context.partition.enable_logging && context.partition.verbose_logging ) {
              LOG << RED << "Node" << hn << "is fixed to block" << to
                  << ", but it is assigned to block" << from << "!"
                  << "It is now moved to its fixed vertex block." << END;
            }
            partitioned_hg.changeNodePartNoSync(hn, from, to, true);
          }
        }
      });
      partitioned_hg.resetEdgeSynchronization();
    }
  }

  template<typename TypeTraits>
  typename Partitioner<TypeTraits>::PartitionedHypergraph Partitioner<TypeTraits>::partition(
    Hypergraph& hypergraph, Context& context, TargetGraph* target_graph) {
    configurePreprocessing(hypergraph, context);
    setupContext(hypergraph, context, target_graph);

    io::printContext(context);
    io::printMemoryPoolConsumption(context);
    io::printInputInformation(context, hypergraph);

    #ifdef KAHYPAR_ENABLE_STEINER_TREE_METRIC
    bool map_partition_to_target_graph_at_the_end = false;
    if ( context.partition.objective == Objective::steiner_tree &&
         context.mapping.use_two_phase_approach ) {
      map_partition_to_target_graph_at_the_end = true;
      context.partition.objective = Objective::km1;
      context.setupGainPolicy();
    }
    #endif

    // ################## PREPROCESSING ##################
    utils::Timer& timer = utils::Utilities::instance().getTimer(context.utility_id);
    timer.start_timer("preprocessing", "Preprocessing");
    DegreeZeroHypernodeRemover<TypeTraits> degree_zero_hn_remover(context);
    LargeHyperedgeRemover<TypeTraits> large_he_remover(context);
    preprocess(hypergraph, context, target_graph);
    sanitize(hypergraph, context, degree_zero_hn_remover, large_he_remover);
    timer.stop_timer("preprocessing");

    // ################## MULTILEVEL & VCYCLE ##################
    PartitionedHypergraph partitioned_hypergraph;
    if (context.partition.mode == Mode::direct) {
      partitioned_hypergraph = Multilevel<TypeTraits>::partition(hypergraph, context, target_graph);
    } else if (context.partition.mode == Mode::recursive_bipartitioning) {
      partitioned_hypergraph = RecursiveBipartitioning<TypeTraits>::partition(hypergraph, context, target_graph);
    } else if (context.partition.mode == Mode::deep_multilevel) {
      ASSERT(context.partition.objective != Objective::steiner_tree);
      partitioned_hypergraph = DeepMultilevel<TypeTraits>::partition(hypergraph, context);
    } else {
      throw InvalidParameterException("Invalid partitioning mode!");
    }

    ASSERT([&] {
      bool success = true;
      if ( partitioned_hypergraph.hasFixedVertices() ) {
        for ( const HypernodeID& hn : partitioned_hypergraph.nodes() ) {
          if ( partitioned_hypergraph.isFixed(hn) &&
               partitioned_hypergraph.fixedVertexBlock(hn) != partitioned_hypergraph.partID(hn) ) {
            LOG << "Node" << hn << "is fixed to block" << partitioned_hypergraph.fixedVertexBlock(hn)
                << ", but is assigned to block" << partitioned_hypergraph.partID(hn);
            success = false;
          }
        }
      }
      return success;
    }(), "Some fixed vertices are not assigned to their corresponding block");

    // ################## POSTPROCESSING ##################
    timer.start_timer("postprocessing", "Postprocessing");
    large_he_remover.restoreSinglePinAndLargeHyperedges(partitioned_hypergraph);
    degree_zero_hn_remover.restoreDegreeZeroHypernodes(partitioned_hypergraph);
    forceFixedVertexAssignment(partitioned_hypergraph, context);
    timer.stop_timer("postprocessing");

    #ifdef KAHYPAR_ENABLE_STEINER_TREE_METRIC
    if ( map_partition_to_target_graph_at_the_end ) {
      ASSERT(target_graph);
      context.partition.objective = Objective::steiner_tree;
      timer.start_timer("one_to_one_mapping", "One-To-One Mapping");
      InitialMapping<TypeTraits>::mapToTargetGraph(
        partitioned_hypergraph, *target_graph, context);
      timer.stop_timer("one_to_one_mapping");
    }
    #endif

    if (context.partition.enable_logging && context.partition.verbose_logging) {
      io::printHypergraphInfo(partitioned_hypergraph.hypergraph(), context,
        "Uncoarsened Hypergraph", context.partition.show_memory_consumption);
      io::printStripe();
    }

    return partitioned_hypergraph;
  }


  template<typename TypeTraits>
  void Partitioner<TypeTraits>::partitionVCycle(PartitionedHypergraph& partitioned_hg,
                                                Context& context,
                                                TargetGraph* target_graph) {
    Hypergraph& hypergraph = partitioned_hg.hypergraph();
    configurePreprocessing(hypergraph, context);
    setupContext(hypergraph, context, target_graph);

    utils::Timer& timer = utils::Utilities::instance().getTimer(context.utility_id);
    timer.start_timer("preprocessing", "Preprocessing");
    precomputeSteinerTrees(hypergraph, target_graph, context);
    partitioned_hg.setTargetGraph(target_graph);
    timer.stop_timer("preprocessing");

    io::printContext(context);
    io::printMemoryPoolConsumption(context);
    io::printInputInformation(context, hypergraph);
    io::printPartitioningResults(partitioned_hg, context, "\nInput Partition:");

    // ################## PREPROCESSING ##################
    timer.start_timer("preprocessing", "Preprocessing");
    DegreeZeroHypernodeRemover<TypeTraits> degree_zero_hn_remover(context);
    LargeHyperedgeRemover<TypeTraits> large_he_remover(context);
    sanitize(hypergraph, context, degree_zero_hn_remover, large_he_remover);
    timer.stop_timer("preprocessing");

    // ################## MULTILEVEL & VCYCLE ##################
    if (context.partition.mode == Mode::direct) {
      Multilevel<TypeTraits>::partitionVCycle(
        hypergraph, partitioned_hg, context, target_graph);
    } else {
      throw InvalidParameterException("Invalid V-cycle partitioning mode!");
    }

    // ################## POSTPROCESSING ##################
    timer.start_timer("postprocessing", "Postprocessing");
    large_he_remover.restoreSinglePinAndLargeHyperedges(partitioned_hg);
    degree_zero_hn_remover.restoreDegreeZeroHypernodes(partitioned_hg);
    forceFixedVertexAssignment(partitioned_hg, context);
    timer.stop_timer("postprocessing");

    if (context.partition.enable_logging && context.partition.verbose_logging) {
      io::printHypergraphInfo(partitioned_hg.hypergraph(), context,
        "Uncoarsened Hypergraph", context.partition.show_memory_consumption);
      io::printStripe();
    }

    ASSERT([&] {
      bool success = true;
      if ( partitioned_hg.hasFixedVertices() ) {
        for ( const HypernodeID& hn : partitioned_hg.nodes() ) {
          if ( partitioned_hg.isFixed(hn) &&
               partitioned_hg.fixedVertexBlock(hn) != partitioned_hg.partID(hn) ) {
            LOG << "Node" << hn << "is fixed to block" << partitioned_hg.fixedVertexBlock(hn)
                << ", but is assigned to block" << partitioned_hg.partID(hn);
            success = false;
          }
        }
      }
      return success;
    }(), "Some fixed vertices are not assigned to their corresponding block");
  }

  INSTANTIATE_CLASS_WITH_TYPE_TRAITS(Partitioner)
}
