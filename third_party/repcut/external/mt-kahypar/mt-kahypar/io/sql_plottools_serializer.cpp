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

#include "sql_plottools_serializer.h"

#include <sstream>

#include "mt-kahypar/definitions.h"
#include "mt-kahypar/partition/metrics.h"
#include "mt-kahypar/partition/mapping/target_graph.h"
#include "mt-kahypar/utils/utilities.h"
#include "mt-kahypar/utils/timer.h"

namespace mt_kahypar::io::serializer {

template<typename PartitionedHypergraph>
std::string serialize(const PartitionedHypergraph& hypergraph,
                      const Context& context,
                      const std::chrono::duration<double>& elapsed_seconds) {
  if (context.partition.sp_process_output) {
    std::stringstream oss;
    oss << "RESULT"
        << " algorithm=" << context.algorithm_name
        << " graph=" << context.partition.graph_filename.substr(
            context.partition.graph_filename.find_last_of('/') + 1);
    if ( context.partition.fixed_vertex_filename != "" ) {
      oss << " fixed_vertex_filename=" << context.partition.fixed_vertex_filename.substr(
              context.partition.fixed_vertex_filename.find_last_of('/') + 1);
    }
    oss << " numHNs=" << hypergraph.initialNumNodes()
        << " numHEs=" << (PartitionedHypergraph::is_graph ? hypergraph.initialNumEdges() / 2 : hypergraph.initialNumEdges())
        << " mode=" << context.partition.mode
        << " objective=" << context.partition.objective
        << " gain_policy=" << context.partition.gain_policy
        << " file_format=" << context.partition.file_format
        << " partition_type=" << context.partition.partition_type
        << " k=" << context.partition.k
        << " epsilon=" << context.partition.epsilon
        << " seed=" << context.partition.seed
        << " num_vcycles=" << context.partition.num_vcycles
        << " deterministic=" << context.partition.deterministic
        << " allow_empty_blocks=" << context.partition.allow_empty_blocks
        << " perform_parallel_recursion_in_deep_multilevel=" << context.partition.perform_parallel_recursion_in_deep_multilevel;
    oss << " large_hyperedge_size_threshold_factor=" << context.partition.large_hyperedge_size_threshold_factor
        << " smallest_large_he_size_threshold=" << context.partition.smallest_large_he_size_threshold
        << " large_hyperedge_size_threshold=" << context.partition.large_hyperedge_size_threshold
        << " ignore_hyperedge_size_threshold=" << context.partition.ignore_hyperedge_size_threshold
        << " time_limit=" << context.partition.time_limit
        << " use_individual_part_weights=" << context.partition.use_individual_part_weights
        << " perfect_balance_part_weight=" << context.partition.perfect_balance_part_weights[0]
        << " max_part_weight=" << context.partition.max_part_weights[0]
        << " total_graph_weight=" << hypergraph.totalWeight();
    oss << " use_community_detection=" << std::boolalpha << context.preprocessing.use_community_detection
        << " disable_community_detection_for_mesh_graphs=" << std::boolalpha << context.preprocessing.disable_community_detection_for_mesh_graphs
        << " community_edge_weight_function=" << context.preprocessing.community_detection.edge_weight_function
        << " community_max_pass_iterations=" << context.preprocessing.community_detection.max_pass_iterations
        << " community_min_vertex_move_fraction=" << context.preprocessing.community_detection.min_vertex_move_fraction
        << " community_vertex_degree_sampling_threshold=" << context.preprocessing.community_detection.vertex_degree_sampling_threshold
        << " community_num_sub_rounds_deterministic=" << context.preprocessing.community_detection.num_sub_rounds_deterministic
        << " community_low_memory_contraction=" << context.preprocessing.community_detection.low_memory_contraction;
    oss << " coarsening_algorithm=" << context.coarsening.algorithm
        << " coarsening_contraction_limit_multiplier=" << context.coarsening.contraction_limit_multiplier
        << " coarsening_deep_ml_contraction_limit_multiplier=" << context.coarsening.deep_ml_contraction_limit_multiplier
        << " coarsening_use_adaptive_edge_size=" << std::boolalpha << context.coarsening.use_adaptive_edge_size
        << " coarsening_max_allowed_weight_multiplier=" << context.coarsening.max_allowed_weight_multiplier
        << " coarsening_minimum_shrink_factor=" << context.coarsening.minimum_shrink_factor
        << " coarsening_maximum_shrink_factor=" << context.coarsening.maximum_shrink_factor
        << " coarsening_max_allowed_node_weight=" << context.coarsening.max_allowed_node_weight
        << " coarsening_vertex_degree_sampling_threshold=" << context.coarsening.vertex_degree_sampling_threshold
        << " coarsening_num_sub_rounds_deterministic=" << context.coarsening.num_sub_rounds_deterministic
        << " coarsening_det_resolve_swaps=" << std::boolalpha << context.coarsening.det_resolve_swaps
        << " coarsening_use_two_hop=" << std::boolalpha << context.coarsening.use_two_hop
        << " coarsening_two_hop_full_shrinkage=" << std::boolalpha << context.coarsening.two_hop_full_shrinkage
        << " coarsening_two_hop_shrink_threshold=" << context.coarsening.two_hop_shrink_threshold
        << " coarsening_two_hop_cluster_size=" << context.coarsening.two_hop_cluster_size
        << " coarsening_two_hop_degree_threshold=" << context.coarsening.two_hop_degree_threshold
        << " coarsening_contraction_limit=" << context.coarsening.contraction_limit
        << " rating_function=" << context.coarsening.rating.rating_function
        << " rating_heavy_node_penalty_policy=" << context.coarsening.rating.heavy_node_penalty_policy
        << " rating_acceptance_policy=" << context.coarsening.rating.acceptance_policy;
    oss << " initial_partitioning_mode=" << context.initial_partitioning.mode
        << " initial_partitioning_runs=" << context.initial_partitioning.runs
        << " initial_partitioning_use_adaptive_ip_runs=" << std::boolalpha << context.initial_partitioning.use_adaptive_ip_runs
        << " initial_partitioning_min_adaptive_ip_runs=" << context.initial_partitioning.min_adaptive_ip_runs
        << " initial_partitioning_perform_refinement_on_best_partitions=" << std::boolalpha << context.initial_partitioning.perform_refinement_on_best_partitions
        << " initial_partitioning_fm_refinment_rounds=" << std::boolalpha << context.initial_partitioning.fm_refinment_rounds
        << " initial_partitioning_remove_degree_zero_hns_before_ip=" << std::boolalpha << context.initial_partitioning.remove_degree_zero_hns_before_ip
        << " initial_partitioning_lp_maximum_iterations=" << context.initial_partitioning.lp_maximum_iterations
        << " initial_partitioning_lp_initial_block_size=" << context.initial_partitioning.lp_initial_block_size
        << " initial_partitioning_population_size=" << context.initial_partitioning.population_size;
    oss << " refine_until_no_improvement=" << std::boolalpha << context.refinement.refine_until_no_improvement
        << " relative_improvement_threshold=" << context.refinement.relative_improvement_threshold
        << " max_batch_size=" << context.refinement.max_batch_size
        << " min_border_vertices_per_thread=" << context.refinement.min_border_vertices_per_thread
        << " rebalancing_algorithm=" << context.refinement.rebalancing.algorithm
        << " rebalancing_heavy_vertex_exclusion_factor=" << context.refinement.rebalancing.det_heavy_vertex_exclusion_factor
        << " rebalancing_relative_deadzone_size=" << context.refinement.rebalancing.det_relative_deadzone_size
        << " rebalancing_det_max_rounds=" << context.refinement.rebalancing.det_max_rounds
        << " lp_algorithm=" << context.refinement.label_propagation.algorithm
        << " lp_maximum_iterations=" << context.refinement.label_propagation.maximum_iterations
        << " lp_rebalancing=" << std::boolalpha << context.refinement.label_propagation.rebalancing
        << " lp_unconstrained=" << std::boolalpha << context.refinement.label_propagation.unconstrained
        << " lp_relative_improvement_threshold=" << context.refinement.label_propagation.relative_improvement_threshold
        << " lp_hyperedge_size_activation_threshold=" << context.refinement.label_propagation.hyperedge_size_activation_threshold
        << " sync_lp_num_sub_rounds_sync_lp=" << context.refinement.deterministic_refinement.num_sub_rounds_sync_lp
        << " sync_lp_use_active_node_set=" << context.refinement.deterministic_refinement.use_active_node_set
        << " jet_algorithm=" << context.refinement.jet.algorithm
        << " jet_num_iterations_without_improvement=" << context.refinement.jet.num_iterations
        << " jet_relative_improvement_threshold=" << context.refinement.jet.relative_improvement_threshold
        << " jet_dynamic_rounds=" << context.refinement.jet.dynamic_rounds
        << " jet_initial_negative_gain_factor=" << context.refinement.jet.initial_negative_gain_factor
        << " jet_initial_final_negative_gain_factor=" << context.refinement.jet.final_negative_gain_factor;
    oss << " fm_algorithm=" << context.refinement.fm.algorithm
        << " fm_multitry_rounds=" << context.refinement.fm.multitry_rounds
        << " fm_rollback_parallel=" << std::boolalpha << context.refinement.fm.rollback_parallel
        << " fm_rollback_sensitive_to_num_moves=" << std::boolalpha << context.refinement.fm.iter_moves_on_recalc
        << " fm_rollback_balance_violation_factor=" << context.refinement.fm.rollback_balance_violation_factor
        << " fm_min_improvement=" << context.refinement.fm.min_improvement
        << " fm_release_nodes=" << context.refinement.fm.release_nodes
        << " fm_iter_moves_on_recalc=" << context.refinement.fm.iter_moves_on_recalc
        << " fm_num_seed_nodes=" << context.refinement.fm.num_seed_nodes
        << " fm_time_limit_factor=" << context.refinement.fm.time_limit_factor
        << " fm_obey_minimal_parallelism=" << std::boolalpha << context.refinement.fm.obey_minimal_parallelism
        << " fm_shuffle=" << std::boolalpha << context.refinement.fm.shuffle
        << " fm_unconstrained_rounds=" << context.refinement.fm.unconstrained_rounds
        << " fm_treshold_border_node_inclusion=" << context.refinement.fm.treshold_border_node_inclusion
        << " fm_unconstrained_min_improvement=" << context.refinement.fm.unconstrained_min_improvement
        << " fm_unconstrained_upper_bound=" << context.refinement.fm.unconstrained_upper_bound
        << " fm_unconstrained_upper_bound_min=" << context.refinement.fm.unconstrained_upper_bound_min
        << " fm_imbalance_penalty_min=" << context.refinement.fm.imbalance_penalty_min
        << " fm_imbalance_penalty_max=" << context.refinement.fm.imbalance_penalty_max
        << " fm_activate_unconstrained_dynamically=" << std::boolalpha << context.refinement.fm.activate_unconstrained_dynamically
        << " fm_penalty_for_activation_test=" << context.refinement.fm.penalty_for_activation_test
        << " global_refine_use_global_refinement=" << std::boolalpha << context.refinement.global.use_global_refinement
        << " global_refine_refine_until_no_improvement=" << std::boolalpha << context.refinement.global.refine_until_no_improvement
        << " global_refine_fm_algorithm=" << context.refinement.global.fm_algorithm
        << " global_refine_fm_num_seed_nodes=" << context.refinement.global.fm_num_seed_nodes
        << " global_refine_fm_obey_minimal_parallelism=" << std::boolalpha << context.refinement.global.fm_obey_minimal_parallelism
        << " global_refine_lp_algorithm=" << context.refinement.global.lp_algorithm
        << " global_refine_lp_unconstrained=" << std::boolalpha << context.refinement.global.lp_unconstrained;
    oss << " flow_algorithm=" << context.refinement.flows.algorithm
        << " flow_num_parallel_searches=" << context.refinement.flows.num_parallel_searches
        << " flow_max_bfs_distance=" << context.refinement.flows.max_bfs_distance
        << " flow_min_relative_improvement_per_round=" << context.refinement.flows.min_relative_improvement_per_round
        << " flow_time_limit_factor=" << context.refinement.flows.time_limit_factor
        << " flow_skip_small_cuts=" << std::boolalpha << context.refinement.flows.skip_small_cuts
        << " flow_skip_unpromising_blocks=" << std::boolalpha << context.refinement.flows.skip_unpromising_blocks
        << " flow_pierce_in_bulk=" << std::boolalpha << context.refinement.flows.pierce_in_bulk
        << " flow_alpha=" << context.refinement.flows.alpha
        << " flow_max_num_pins=" << context.refinement.flows.max_num_pins
        << " flow_find_most_balanced_cut=" << std::boolalpha << context.refinement.flows.find_most_balanced_cut
        << " flow_determine_distance_from_cut=" << std::boolalpha << context.refinement.flows.determine_distance_from_cut
        << " flow_steiner_tree_policy=" << context.refinement.flows.steiner_tree_policy;
    oss << " num_threads=" << context.shared_memory.num_threads
        << " use_localized_random_shuffle=" << std::boolalpha << context.shared_memory.use_localized_random_shuffle
        << " shuffle_block_size=" << context.shared_memory.shuffle_block_size
        << " static_balancing_work_packages=" << context.shared_memory.static_balancing_work_packages;

    if ( context.partition.objective == Objective::steiner_tree ) {
      oss << " target_graph_file=" << context.mapping.target_graph_file.substr(
            context.mapping.target_graph_file.find_last_of('/') + 1)
          << " mapping_strategy=" << context.mapping.strategy
          << " mapping_use_local_search=" << std::boolalpha << context.mapping.use_local_search
          << " mapping_use_two_phase_approach=" << std::boolalpha << context.mapping.use_two_phase_approach
          << " mapping_max_steiner_tree_size=" << context.mapping.max_steiner_tree_size
          << " mapping_largest_he_fraction=" << context.mapping.largest_he_fraction
          << " mapping_min_pin_coverage_of_largest_hes=" << context.mapping.min_pin_coverage_of_largest_hes
          << " mapping_large_he_threshold=" << context.mapping.large_he_threshold;
      if ( TargetGraph::TRACK_STATS ) {
        hypergraph.targetGraph()->printStats(oss);
      }
    }

    // Metrics
    if ( hypergraph.initialNumEdges() > 0 ) {
      oss << " " << context.partition.objective << "=" << metrics::quality(hypergraph, context);
      if ( context.partition.objective == Objective::steiner_tree ) {
        oss << " approximation_factor=" << metrics::approximationFactorForProcessMapping(hypergraph, context);
      }
      if ( context.partition.objective != Objective::cut ) {
        oss << " cut=" << metrics::quality(hypergraph, Objective::cut);
      }
      if ( context.partition.objective != Objective::km1 ) {
        oss << " km1=" << metrics::quality(hypergraph, Objective::km1);
      }
      if ( context.partition.objective != Objective::soed ) {
        oss << " soed=" << metrics::quality(hypergraph, Objective::soed);
      }
      BalanceMetrics imbalance = metrics::imbalance(hypergraph, context);
      oss << " imbalance=" << imbalance.imbalance_value;
      oss << " violates_non_empty_blocks=" << imbalance.violates_non_empty_blocks;
    }
    oss << " totalPartitionTime=" << elapsed_seconds.count();

    // Timings
    utils::Timer& timer = utils::Utilities::instance().getTimer(context.utility_id);
    timer.showDetailedTimings(context.partition.show_detailed_timings);
    timer.serialize(oss);

    // Stats
    oss << utils::Utilities::instance().getStats(context.utility_id);

    // Initial Partitioning Stats
    oss << utils::Utilities::instance().getInitialPartitioningStats(context.utility_id);

    return oss.str();
  } else {
    return "";
  }
}

namespace {
#define SERIALIZE(X) std::string serialize(const X& hypergraph,                                  \
                                           const Context& context,                               \
                                           const std::chrono::duration<double>& elapsed_seconds)
} // namespace

INSTANTIATE_FUNC_WITH_PARTITIONED_HG(SERIALIZE)

}  // namespace
