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

#include "mt-kahypar/datastructures/hypergraph_common.h"
#include "mt-kahypar/partition/context_enum_classes.h"

namespace mt_kahypar {

// Forward Declartion
class TargetGraph;

struct PartitioningParameters {
  Mode mode = Mode::direct;
  Objective objective = Objective::UNDEFINED;
  GainPolicy gain_policy = GainPolicy::none;
  FileFormat file_format = FileFormat::hMetis;
  InstanceType instance_type = InstanceType::UNDEFINED;
  PresetType preset_type = PresetType::UNDEFINED;
  mt_kahypar_partition_type_t partition_type =  NULLPTR_PARTITION;
  double epsilon = std::numeric_limits<double>::max();
  PartitionID k = std::numeric_limits<PartitionID>::max();
  int seed = 0;
  size_t num_vcycles = 0;
  bool perform_parallel_recursion_in_deep_multilevel = true;

  int time_limit = 0;
  bool allow_empty_blocks = false;
  bool use_individual_part_weights = false;
  std::vector<HypernodeWeight> perfect_balance_part_weights;
  std::vector<HypernodeWeight> max_part_weights;
  double large_hyperedge_size_threshold_factor = 0.01;
  HypernodeID large_hyperedge_size_threshold = std::numeric_limits<HypernodeID>::max();
  HypernodeID smallest_large_he_size_threshold = 50000;
  HypernodeID ignore_hyperedge_size_threshold = 1000;

  bool enable_logging = true;
  bool verbose_logging = false;
  bool show_detailed_timings = false;
  bool show_detailed_clustering_timings = false;
  bool show_detailed_uncontraction_timings = false;
  size_t timings_output_depth = std::numeric_limits<size_t>::max();
  bool show_memory_consumption = false;
  bool show_advanced_cut_analysis = false;
  bool enable_progress_bar = false;
  bool sp_process_output = false;
  bool csv_output = false;
  bool write_partition_file = false;
  bool deterministic = false;

  std::string graph_filename { };
  std::string fixed_vertex_filename { };
  std::string graph_partition_output_folder {};
  std::string graph_partition_filename { };
  std::string graph_community_filename { };
  std::string preset_file { };
};

struct CommunityDetectionParameters {
  LouvainEdgeWeight edge_weight_function = LouvainEdgeWeight::hybrid;
  uint32_t max_pass_iterations = 5;
  bool low_memory_contraction = false;
  long double min_vertex_move_fraction = 0.01;
  size_t vertex_degree_sampling_threshold = 200000;
  size_t num_sub_rounds_deterministic = 16;
};

struct PreprocessingParameters {
  bool stable_construction_of_incident_edges = false;
  bool use_community_detection = true;
  bool disable_community_detection_for_mesh_graphs = true;
  CommunityDetectionParameters community_detection = { };
};

struct RatingParameters {
  RatingFunction rating_function = RatingFunction::heavy_edge;
  HeavyNodePenaltyPolicy heavy_node_penalty_policy = HeavyNodePenaltyPolicy::no_penalty;
  AcceptancePolicy acceptance_policy = AcceptancePolicy::best_prefer_unmatched;
};

struct CoarseningParameters {
  CoarseningAlgorithm algorithm = CoarseningAlgorithm::UNDEFINED;
  RatingParameters rating = { };
  HypernodeID contraction_limit_multiplier = 160;
  HypernodeID deep_ml_contraction_limit_multiplier = 160;
  bool use_adaptive_edge_size = true;
  double max_allowed_weight_multiplier = 1;
  double minimum_shrink_factor = 1.1;
  double maximum_shrink_factor = 2.5;
  size_t vertex_degree_sampling_threshold = 200000;

  // parameters for deterministic coarsening
  size_t num_sub_rounds_deterministic = 16;
  bool det_resolve_swaps = true;

  // parameters for two-hop clustering
  bool use_two_hop = true;
  bool two_hop_full_shrinkage = true;
  double two_hop_shrink_threshold = 1.75;
  HypernodeID two_hop_cluster_size = 4;
  size_t two_hop_degree_threshold = 100;

  // Those will be determined dynamically
  HypernodeWeight max_allowed_node_weight = 0;
  HypernodeID contraction_limit = 0;
};

struct LabelPropagationParameters {
  LabelPropagationAlgorithm algorithm = LabelPropagationAlgorithm::do_nothing;
  size_t maximum_iterations = 5;
  mutable bool unconstrained = false;
  bool rebalancing = true;
  bool execute_sequential = false;
  size_t hyperedge_size_activation_threshold = 100;
  double relative_improvement_threshold = -1.0;
};

struct JetParameters {
  JetAlgorithm algorithm = JetAlgorithm::do_nothing;
  size_t num_iterations = 12;
  double relative_improvement_threshold = 0.001;
  size_t dynamic_rounds = 3;
  double initial_negative_gain_factor = 0.75;
  double final_negative_gain_factor = 0.0;
};

struct FMParameters {
  mutable FMAlgorithm algorithm = FMAlgorithm::do_nothing;

  size_t multitry_rounds = 10;
  mutable size_t num_seed_nodes = 25;

  double rollback_balance_violation_factor = 1.0;
  double min_improvement = -1.0;
  double time_limit_factor = 0.25;

  bool rollback_parallel = true;
  bool iter_moves_on_recalc = false;
  bool shuffle = true;
  mutable bool obey_minimal_parallelism = true;
  bool release_nodes = true;

  // unconstrained
  size_t unconstrained_rounds = 8;
  double treshold_border_node_inclusion = 0.75;
  double imbalance_penalty_min = 0.2;
  double imbalance_penalty_max = 1.0;
  double unconstrained_upper_bound = 0.0;
  double unconstrained_upper_bound_min = 0.0;
  double unconstrained_min_improvement = -1.0;

  bool activate_unconstrained_dynamically = false;
  double penalty_for_activation_test = 0.5;
};

struct NLevelGlobalRefinementParameters {
  bool use_global_refinement = false;
  bool refine_until_no_improvement = false;

  FMAlgorithm fm_algorithm = FMAlgorithm::kway_fm;
  size_t fm_num_seed_nodes = 25;
  bool fm_obey_minimal_parallelism = true;

  LabelPropagationAlgorithm lp_algorithm = LabelPropagationAlgorithm::do_nothing;
  bool lp_unconstrained = false;
};

struct FlowParameters {
  FlowAlgorithm algorithm = FlowAlgorithm::do_nothing;
  double alpha = 16.0;
  HypernodeID max_num_pins = std::numeric_limits<HypernodeID>::max();
  bool find_most_balanced_cut = true;
  bool determine_distance_from_cut = true;
  size_t max_bfs_distance = 2;
  double min_relative_improvement_per_round = 0.001;
  double time_limit_factor = 8.0;
  bool skip_small_cuts = true;
  bool skip_unpromising_blocks = true;
  bool pierce_in_bulk = true;
  SteinerTreeFlowValuePolicy steiner_tree_policy = SteinerTreeFlowValuePolicy::lower_bound;

  // configured at runtime
  size_t num_parallel_searches = 0;
};

struct DeterministicRefinementParameters {
  size_t num_sub_rounds_sync_lp = 5;
  bool use_active_node_set = true;
};

struct RebalancingParameters {
  RebalancingAlgorithm algorithm = RebalancingAlgorithm::do_nothing;
  double det_heavy_vertex_exclusion_factor = 1.5;
  double det_relative_deadzone_size = 1.0;
  size_t det_max_rounds = 0;
};

struct RefinementParameters {
  LabelPropagationParameters label_propagation;
  JetParameters jet;
  FMParameters fm;
  DeterministicRefinementParameters deterministic_refinement;
  NLevelGlobalRefinementParameters global;
  FlowParameters flows;
  RebalancingParameters rebalancing;
  bool refine_until_no_improvement = false;
  double relative_improvement_threshold = 0.0;
  size_t max_batch_size = 1000;
  size_t min_border_vertices_per_thread = 0;
};

struct InitialPartitioningParameters {
  InitialPartitioningParameters() :
    // Enable all initial partitioner per default
    enabled_ip_algos(static_cast<size_t>(InitialPartitioningAlgorithm::UNDEFINED), true) { }

  Mode mode = Mode::recursive_bipartitioning;
  RefinementParameters refinement = { };
  std::vector<bool> enabled_ip_algos;
  size_t runs = 20;
  bool use_adaptive_ip_runs = true;
  size_t min_adaptive_ip_runs = 5;
  bool perform_refinement_on_best_partitions = false;
  size_t fm_refinment_rounds = 1;
  bool remove_degree_zero_hns_before_ip = true;
  size_t lp_maximum_iterations = 20;
  size_t lp_initial_block_size = 5;
  size_t population_size = 16;
};

struct MappingParameters {
  std::string target_graph_file = "";
  OneToOneMappingStrategy strategy = OneToOneMappingStrategy::identity;
  bool use_local_search = false;
  bool use_two_phase_approach = false;
  size_t max_steiner_tree_size = 0;
  double largest_he_fraction = 0.0;
  double min_pin_coverage_of_largest_hes = 1.0;
  HypernodeID large_he_threshold = std::numeric_limits<HypernodeID>::max();
};

struct SharedMemoryParameters {
  size_t original_num_threads = 1;
  size_t num_threads = 1;
  size_t static_balancing_work_packages = 128;
  bool use_localized_random_shuffle = false;
  size_t shuffle_block_size = 2;
  double degree_of_parallelism = 1.0;
};

class Context {
 public:
  PartitioningParameters partition { };
  PreprocessingParameters preprocessing { };
  CoarseningParameters coarsening { };
  InitialPartitioningParameters initial_partitioning { };
  RefinementParameters refinement { };
  MappingParameters mapping { };
  SharedMemoryParameters shared_memory { };
  ContextType type = ContextType::main;

  std::string algorithm_name = "Mt-KaHyPar";
  mutable size_t initial_km1 = std::numeric_limits<size_t>::max();
  size_t utility_id = std::numeric_limits<size_t>::max();

  Context(const bool register_utilities = true);

  bool isNLevelPartitioning() const;

  bool forceGainCacheUpdates() const;

  void setupPartWeights(const HypernodeWeight total_hypergraph_weight);

  void setupContractionLimit(const HypernodeWeight total_hypergraph_weight);

  void setupMaximumAllowedNodeWeight(const HypernodeWeight total_hypergraph_weight);

  void setupThreadsPerFlowSearch();

  void setupGainPolicy();

  void sanityCheck(const TargetGraph* target_graph);
};

std::ostream & operator<< (std::ostream& str, const Context& context);

}  // namespace mt_kahypar
