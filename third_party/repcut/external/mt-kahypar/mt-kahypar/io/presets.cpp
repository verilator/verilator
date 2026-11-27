/*******************************************************************************
 * MIT License
 *
 * This file is part of Mt-KaHyPar.
 *
 * Copyright (C) 2024 Nikolai Maas <nikolai.maas@kit.edu>
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

#include "presets.h"

#include <vector>
#include <sstream>

namespace mt_kahypar {

// construction helper
std::string create_option(const std::string& key, const std::string& value) {
  std::stringstream out;
  out << "--" << key << "=" << value;
  return out.str();
}

std::vector<std::string> validPresetTypes() {
  return {
    "default", "quality", "highest_quality",
    "deterministic", "deterministic_quality", "large_k"
  };
}

std::vector<std::string> load_default_preset() {
  return {
    // general
    create_option("mode", "direct"),
    create_option("preset-type", "default"),
    create_option("maxnet-removal-factor", "0.01"),
    create_option("smallest-maxnet-threshold", "50000"),
    create_option("maxnet-ignore", "1000"),
    create_option("num-vcycles", "0"),
    // main -> shared_memory
    create_option("s-use-localized-random-shuffle", "false"),
    create_option("s-static-balancing-work-packages", "128"),
    // main -> preprocessing
    create_option("p-enable-community-detection", "true"),
    // main -> preprocessing -> community_detection
    create_option("p-louvain-edge-weight-function", "hybrid"),
    create_option("p-max-louvain-pass-iterations", "5"),
    create_option("p-louvain-min-vertex-move-fraction", "0.01"),
    create_option("p-vertex-degree-sampling-threshold", "200000"),
    // main -> coarsening
    create_option("c-type", "multilevel_coarsener"),
    create_option("c-use-adaptive-edge-size", "true"),
    create_option("c-min-shrink-factor", "1.1"),
    create_option("c-max-shrink-factor", "2.5"),
    create_option("c-s", "1"),
    create_option("c-t", "160"),
    create_option("c-vertex-degree-sampling-threshold", "200000"),
    // main -> coarsening -> rating
    create_option("c-rating-score", "heavy_edge"),
    create_option("c-rating-heavy-node-penalty", "no_penalty"),
    create_option("c-rating-acceptance-criterion", "best_prefer_unmatched"),
    // main -> coarsening -> two-hop
    create_option("c-use-two-hop", "true"),
    create_option("c-two-hop-full-shrinkage", "true"),
    create_option("c-two-hop-threshold", "1.75"),
    create_option("c-two-hop-cluster-size", "4"),
    create_option("c-two-hop-degree-threshold", "100"),
    // main -> initial_partitioning
    create_option("i-mode", "rb"),
    create_option("i-runs", "20"),
    create_option("i-use-adaptive-ip-runs", "true"),
    create_option("i-min-adaptive-ip-runs", "5"),
    create_option("i-perform-refinement-on-best-partitions", "true"),
    create_option("i-remove-degree-zero-hns-before-ip", "true"),
    create_option("i-fm-refinement-rounds", "1"),
    create_option("i-lp-maximum-iterations", "20"),
    create_option("i-lp-initial-block-size", "5"),
    // main -> initial_partitioning -> refinement
    create_option("i-r-refine-until-no-improvement", "false"),
    // main -> initial_partitioning -> refinement -> label_propagation
    create_option("i-r-lp-type", "label_propagation"),
    create_option("i-r-lp-maximum-iterations", "5"),
    create_option("i-r-lp-rebalancing", "true"),
    create_option("i-r-lp-he-size-activation-threshold", "100"),
    // main -> initial_partitioning -> refinement -> fm
    create_option("i-r-fm-type", "kway_fm"),
    create_option("i-r-fm-multitry-rounds", "5"),
    create_option("i-r-fm-rollback-parallel", "true"),
    create_option("i-r-fm-rollback-balance-violation-factor", "1"),
    create_option("i-r-fm-seed-nodes", "25"),
    create_option("i-r-fm-obey-minimal-parallelism", "false"),
    create_option("i-r-fm-release-nodes", "true"),
    create_option("i-r-fm-time-limit-factor", "0.25"),
    create_option("i-r-fm-iter-moves-on-recalc", "true"),
    // main -> initial_partitioning -> refinement -> flows
    create_option("i-r-flow-algo", "do_nothing"),
    // main -> refinement
    create_option("r-rebalancer-type", "advanced_rebalancer"),
    create_option("r-refine-until-no-improvement", "false"),
    // main -> refinement -> label_propagation
    create_option("r-lp-type", "label_propagation"),
    create_option("r-lp-unconstrained", "true"),
    create_option("r-lp-maximum-iterations", "5"),
    create_option("r-lp-rebalancing", "false"),
    create_option("r-lp-he-size-activation-threshold", "100"),
    create_option("r-lp-relative-improvement-threshold", "0.001"),
    // main -> refinement -> fm
    create_option("r-fm-type", "unconstrained_fm"),
    create_option("r-fm-multitry-rounds", "10"),
    create_option("r-fm-unconstrained-rounds", "8"),
    create_option("r-fm-rollback-parallel", "true"),
    create_option("r-fm-rollback-balance-violation-factor", "1.0"),
    create_option("r-fm-threshold-border-node-inclusion", "0.7"),
    create_option("r-fm-imbalance-penalty-min", "0.2"),
    create_option("r-fm-imbalance-penalty-max", "1.0"),
    create_option("r-fm-seed-nodes", "25"),
    create_option("r-fm-release-nodes", "true"),
    create_option("r-fm-min-improvement", "-1.0"),
    create_option("r-fm-unconstrained-min-improvement", "0.002"),
    create_option("r-fm-obey-minimal-parallelism", "true"),
    create_option("r-fm-time-limit-factor", "0.25"),
    create_option("r-fm-iter-moves-on-recalc", "true"),
    // main -> refinement -> flows
    create_option("r-flow-algo", "do_nothing"),
    // main -> mapping
    create_option("one-to-one-mapping-strategy", "greedy_mapping"),
    create_option("mapping-use-local-search", "true"),
    create_option("mapping-use-two-phase-approach", "false"),
    create_option("mapping-max-steiner-tree-size", "4"),
    create_option("mapping-largest-he-fraction", "0.0"),
    create_option("mapping-min-pin-coverage", "0.05"),
  };
}


std::vector<std::string> load_quality_preset() {
  return {
    // general
    create_option("mode", "direct"),
    create_option("preset-type", "quality"),
    create_option("maxnet-removal-factor", "0.01"),
    create_option("smallest-maxnet-threshold", "50000"),
    create_option("maxnet-ignore", "1000"),
    create_option("num-vcycles", "0"),
    // main -> shared_memory
    create_option("s-use-localized-random-shuffle", "false"),
    create_option("s-static-balancing-work-packages", "128"),
    // main -> preprocessing
    create_option("p-enable-community-detection", "true"),
    // main -> preprocessing -> community_detection
    create_option("p-louvain-edge-weight-function", "hybrid"),
    create_option("p-max-louvain-pass-iterations", "5"),
    create_option("p-louvain-min-vertex-move-fraction", "0.01"),
    create_option("p-vertex-degree-sampling-threshold", "200000"),
    // main -> coarsening
    create_option("c-type", "multilevel_coarsener"),
    create_option("c-use-adaptive-edge-size", "true"),
    create_option("c-min-shrink-factor", "1.1"),
    create_option("c-max-shrink-factor", "2.5"),
    create_option("c-s", "1"),
    create_option("c-t", "160"),
    create_option("c-vertex-degree-sampling-threshold", "200000"),
    // main -> coarsening -> rating
    create_option("c-rating-score", "heavy_edge"),
    create_option("c-rating-heavy-node-penalty", "no_penalty"),
    create_option("c-rating-acceptance-criterion", "best_prefer_unmatched"),
    // main -> coarsening -> two-hop
    create_option("c-use-two-hop", "true"),
    create_option("c-two-hop-full-shrinkage", "true"),
    create_option("c-two-hop-threshold", "1.75"),
    create_option("c-two-hop-cluster-size", "4"),
    create_option("c-two-hop-degree-threshold", "100"),
    // main -> initial_partitioning
    create_option("i-mode", "rb"),
    create_option("i-runs", "20"),
    create_option("i-use-adaptive-ip-runs", "true"),
    create_option("i-min-adaptive-ip-runs", "5"),
    create_option("i-perform-refinement-on-best-partitions", "true"),
    create_option("i-remove-degree-zero-hns-before-ip", "true"),
    create_option("i-fm-refinement-rounds", "1"),
    create_option("i-lp-maximum-iterations", "20"),
    create_option("i-lp-initial-block-size", "5"),
    // main -> initial_partitioning -> refinement
    create_option("i-r-refine-until-no-improvement", "false"),
    // main -> initial_partitioning -> refinement -> label_propagation
    create_option("i-r-lp-type", "label_propagation"),
    create_option("i-r-lp-maximum-iterations", "5"),
    create_option("i-r-lp-rebalancing", "true"),
    create_option("i-r-lp-he-size-activation-threshold", "100"),
    // main -> initial_partitioning -> refinement -> fm
    create_option("i-r-fm-type", "kway_fm"),
    create_option("i-r-fm-multitry-rounds", "5"),
    create_option("i-r-fm-rollback-parallel", "true"),
    create_option("i-r-fm-rollback-balance-violation-factor", "1"),
    create_option("i-r-fm-seed-nodes", "25"),
    create_option("i-r-fm-obey-minimal-parallelism", "false"),
    create_option("i-r-fm-release-nodes", "true"),
    create_option("i-r-fm-time-limit-factor", "0.25"),
    create_option("i-r-fm-iter-moves-on-recalc", "true"),
    // main -> initial_partitioning -> refinement -> flows
    create_option("i-r-flow-algo", "do_nothing"),
    // main -> refinement
    create_option("r-rebalancer-type", "advanced_rebalancer"),
    create_option("r-refine-until-no-improvement", "false"),
    // main -> refinement -> label_propagation
    create_option("r-lp-type", "label_propagation"),
    create_option("r-lp-unconstrained", "true"),
    create_option("r-lp-maximum-iterations", "5"),
    create_option("r-lp-rebalancing", "true"),
    create_option("r-lp-he-size-activation-threshold", "100"),
    create_option("r-lp-relative-improvement-threshold", "0.001"),
    // main -> refinement -> fm
    create_option("r-fm-type", "unconstrained_fm"),
    create_option("r-fm-multitry-rounds", "10"),
    create_option("r-fm-unconstrained-rounds", "8"),
    create_option("r-fm-rollback-parallel", "true"),
    create_option("r-fm-rollback-balance-violation-factor", "1.0"),
    create_option("r-fm-threshold-border-node-inclusion", "0.7"),
    create_option("r-fm-imbalance-penalty-min", "0.2"),
    create_option("r-fm-imbalance-penalty-max", "1.0"),
    create_option("r-fm-seed-nodes", "25"),
    create_option("r-fm-release-nodes", "true"),
    create_option("r-fm-min-improvement", "-1.0"),
    create_option("r-fm-unconstrained-min-improvement", "0.002"),
    create_option("r-fm-obey-minimal-parallelism", "true"),
    create_option("r-fm-time-limit-factor", "0.25"),
    create_option("r-fm-iter-moves-on-recalc", "true"),
    // main -> refinement -> flows
    create_option("r-flow-algo", "flow_cutter"),
    create_option("r-flow-scaling", "16"),
    create_option("r-flow-max-num-pins", "4294967295"),
    create_option("r-flow-find-most-balanced-cut", "true"),
    create_option("r-flow-determine-distance-from-cut", "true"),
    create_option("r-flow-max-bfs-distance", "2"),
    create_option("r-flow-min-relative-improvement-per-round", "0.001"),
    create_option("r-flow-time-limit-factor", "8"),
    create_option("r-flow-skip-small-cuts", "true"),
    create_option("r-flow-skip-unpromising-blocks", "true"),
    create_option("r-flow-pierce-in-bulk", "true"),
    create_option("r-flow-process-mapping-policy", "lower_bound"),
    // main -> mapping
    create_option("one-to-one-mapping-strategy", "greedy_mapping"),
    create_option("mapping-use-local-search", "true"),
    create_option("mapping-use-two-phase-approach", "false"),
    create_option("mapping-max-steiner-tree-size", "4"),
    create_option("mapping-largest-he-fraction", "0.0"),
    create_option("mapping-min-pin-coverage", "0.05"),
  };
}


std::vector<std::string> load_highest_quality_preset() {
  return {
    // general
    create_option("mode", "direct"),
    create_option("preset-type", "highest_quality"),
    create_option("maxnet-removal-factor", "0.01"),
    create_option("smallest-maxnet-threshold", "50000"),
    create_option("maxnet-ignore", "1000"),
    create_option("num-vcycles", "0"),
    // main -> shared_memory
    create_option("s-use-localized-random-shuffle", "false"),
    create_option("s-static-balancing-work-packages", "128"),
    // main -> preprocessing
    create_option("p-enable-community-detection", "true"),
    // main -> preprocessing -> community_detection
    create_option("p-louvain-edge-weight-function", "hybrid"),
    create_option("p-max-louvain-pass-iterations", "5"),
    create_option("p-louvain-min-vertex-move-fraction", "0.01"),
    create_option("p-vertex-degree-sampling-threshold", "200000"),
    // main -> coarsening
    create_option("c-type", "nlevel_coarsener"),
    create_option("c-min-shrink-factor", "1.01"),
    create_option("c-max-shrink-factor", "100.0"),
    create_option("c-s", "1"),
    create_option("c-t", "160"),
    create_option("c-vertex-degree-sampling-threshold", "200000"),
    // main -> coarsening -> rating
    create_option("c-rating-score", "heavy_edge"),
    create_option("c-rating-heavy-node-penalty", "no_penalty"),
    create_option("c-rating-acceptance-criterion", "best_prefer_unmatched"),
    // main -> initial_partitioning
    create_option("i-mode", "rb"),
    create_option("i-runs", "20"),
    create_option("i-use-adaptive-ip-runs", "true"),
    create_option("i-min-adaptive-ip-runs", "5"),
    create_option("i-perform-refinement-on-best-partitions", "true"),
    create_option("i-remove-degree-zero-hns-before-ip", "true"),
    create_option("i-fm-refinement-rounds", "2147483647"),
    create_option("i-lp-maximum-iterations", "20"),
    create_option("i-lp-initial-block-size", "5"),
    // main -> initial_partitioning -> refinement
    create_option("i-r-refine-until-no-improvement", "true"),
    create_option("i-r-relative-improvement-threshold", "0.0"),
    create_option("i-r-max-batch-size", "1000"),
    create_option("i-r-min-border-vertices-per-thread", "0"),
    // main -> initial_partitioning -> refinement -> label_propagation
    create_option("i-r-lp-type", "label_propagation"),
    create_option("i-r-lp-maximum-iterations", "5"),
    create_option("i-r-lp-rebalancing", "true"),
    create_option("i-r-lp-he-size-activation-threshold", "100"),
    // main -> initial_partitioning -> refinement -> fm
    create_option("i-r-fm-type", "kway_fm"),
    create_option("i-r-fm-multitry-rounds", "5"),
    create_option("i-r-fm-rollback-parallel", "false"),
    create_option("i-r-fm-rollback-balance-violation-factor", "1"),
    create_option("i-r-fm-seed-nodes", "5"),
    create_option("i-r-fm-obey-minimal-parallelism", "false"),
    create_option("i-r-fm-release-nodes", "true"),
    create_option("i-r-fm-time-limit-factor", "0.25"),
    // main -> initial_partitioning -> refinement -> global
    create_option("i-r-use-global-fm", "false"),
    // main -> initial_partitioning -> refinement -> flows
    create_option("i-r-flow-algo", "do_nothing"),
    // main -> refinement
    create_option("r-rebalancer-type", "advanced_rebalancer"),
    create_option("r-refine-until-no-improvement", "true"),
    create_option("r-relative-improvement-threshold", "0.0025"),
    create_option("r-max-batch-size", "1000"),
    create_option("r-min-border-vertices-per-thread", "50"),
    // main -> refinement -> label_propagation
    create_option("r-lp-type", "label_propagation"),
    create_option("r-lp-maximum-iterations", "5"),
    create_option("r-lp-rebalancing", "true"),
    create_option("r-lp-he-size-activation-threshold", "100"),
    // main -> refinement -> fm
    create_option("r-fm-type", "kway_fm"),
    create_option("r-fm-multitry-rounds", "10"),
    create_option("r-fm-unconstrained-rounds", "8"),
    create_option("r-fm-rollback-parallel", "false"),
    create_option("r-fm-rollback-balance-violation-factor", "1.0"),
    create_option("r-fm-threshold-border-node-inclusion", "0.7"),
    create_option("r-fm-imbalance-penalty-min", "0.2"),
    create_option("r-fm-imbalance-penalty-max", "1.0"),
    create_option("r-fm-seed-nodes", "5"),
    create_option("r-fm-release-nodes", "true"),
    create_option("r-fm-min-improvement", "-1.0"),
    create_option("r-fm-unconstrained-min-improvement", "0.001"),
    create_option("r-fm-obey-minimal-parallelism", "false"),
    create_option("r-fm-time-limit-factor", "0.25"),
    // applies only to global fm
    create_option("r-fm-iter-moves-on-recalc", "false"),
    // main -> refinement -> global
    create_option("r-use-global-fm", "true"),
    create_option("r-global-refine-until-no-improvement", "true"),
    create_option("r-global-fm-type", "unconstrained_fm"),
    create_option("r-global-fm-seed-nodes", "5"),
    create_option("r-global-fm-obey-minimal-parallelism", "true"),
    create_option("r-global-lp-type", "label_propagation"),
    create_option("r-global-lp-unconstrained", "true"),
    // main -> refinement -> flows
    create_option("r-flow-algo", "flow_cutter"),
    create_option("r-flow-scaling", "16"),
    create_option("r-flow-max-num-pins", "4294967295"),
    create_option("r-flow-find-most-balanced-cut", "true"),
    create_option("r-flow-determine-distance-from-cut", "true"),
    create_option("r-flow-max-bfs-distance", "2"),
    create_option("r-flow-min-relative-improvement-per-round", "0.001"),
    create_option("r-flow-time-limit-factor", "8"),
    create_option("r-flow-skip-small-cuts", "true"),
    create_option("r-flow-skip-unpromising-blocks", "true"),
    create_option("r-flow-pierce-in-bulk", "true"),
    create_option("r-flow-process-mapping-policy", "lower_bound"),
    // main -> mapping
    create_option("one-to-one-mapping-strategy", "greedy_mapping"),
    create_option("mapping-use-local-search", "true"),
    create_option("mapping-use-two-phase-approach", "false"),
    create_option("mapping-max-steiner-tree-size", "4"),
    create_option("mapping-largest-he-fraction", "0.0"),
    create_option("mapping-min-pin-coverage", "0.05"),
  };
}


std::vector<std::string> load_deterministic_preset() {
  return {
    // general
    create_option("mode", "direct"),
    create_option("preset-type", "deterministic"),
    create_option("deterministic", "true"),
    create_option("maxnet-removal-factor", "0.01"),
    create_option("smallest-maxnet-threshold", "50000"),
    create_option("maxnet-ignore", "1000"),
    create_option("num-vcycles", "0"),
    // main -> shared_memory
    create_option("s-use-localized-random-shuffle", "false"),
    create_option("s-static-balancing-work-packages", "128"),
    // main -> preprocessing
    create_option("p-stable-io", "true"),
    create_option("p-enable-community-detection", "true"),
    // main -> preprocessing -> community_detection
    create_option("p-louvain-edge-weight-function", "hybrid"),
    create_option("p-max-louvain-pass-iterations", "5"),
    create_option("p-louvain-min-vertex-move-fraction", "0.01"),
    create_option("p-vertex-degree-sampling-threshold", "200000"),
    create_option("p-louvain-low-memory-contraction", "true"),
    create_option("p-num-sub-rounds", "16"),
    // main -> coarsening
    create_option("c-type", "deterministic_multilevel_coarsener"),
    create_option("c-use-adaptive-edge-size", "false"),
    create_option("c-resolve-swaps", "true"),
    create_option("c-min-shrink-factor", "1.01"),
    create_option("c-max-shrink-factor", "2.5"),
    create_option("c-s", "1"),
    create_option("c-t", "160"),
    create_option("c-vertex-degree-sampling-threshold", "200000"),
    create_option("c-num-sub-rounds", "3"),
    // main -> coarsening -> rating
    create_option("c-rating-score", "heavy_edge"),
    create_option("c-rating-heavy-node-penalty", "no_penalty"),
    create_option("c-rating-acceptance-criterion", "best_prefer_unmatched"),
    // main -> initial_partitioning
    create_option("i-mode", "rb"),
    create_option("i-runs", "20"),
    create_option("i-use-adaptive-ip-runs", "false"),
    create_option("i-perform-refinement-on-best-partitions", "false"),
    create_option("i-remove-degree-zero-hns-before-ip", "true"),
    create_option("i-fm-refinement-rounds", "3"),
    create_option("i-lp-maximum-iterations", "20"),
    create_option("i-lp-initial-block-size", "5"),
    // main -> initial_partitioning -> refinement
    create_option("i-r-refine-until-no-improvement", "false"),
    // main -> initial_partitioning -> refinement -> label_propagation
    create_option("i-r-lp-type", "deterministic"),
    create_option("i-r-lp-maximum-iterations", "5"),
    create_option("i-r-sync-lp-sub-rounds", "1"),
    create_option("i-r-lp-he-size-activation-threshold", "100"),
    create_option("i-r-sync-lp-active-nodeset", "true"),
    // main -> initial_partitioning -> refinement -> fm
    create_option("i-r-fm-type", "do_nothing"),
    create_option("i-population-size", "64"),
    // main -> refinement
    create_option("r-refine-until-no-improvement", "false"),
    // main -> refinement -> rebalancing
    create_option("r-rebalancer-type", "deterministic"),
    create_option("r-max-det-rebalancing-rounds", "0"),
    create_option("r-det-rebalancing-deadzone", "0.1"),
    create_option("r-det-rebalancing-heavy-vertex-exclusion", "1.5"),
    // main -> refinement -> label_propagation
    create_option("r-lp-type", "do_nothing"),
    create_option("r-lp-maximum-iterations", "5"),
    create_option("r-sync-lp-sub-rounds", "1"),
    create_option("r-lp-he-size-activation-threshold", "100"),
    create_option("r-sync-lp-active-nodeset", "true"),
    // main -> refinement -> jet
    create_option("r-jet-type", "deterministic"),
    create_option("r-jet-num-iterations", "8"),
    create_option("r-jet-relative-improvement-threshold", "0.001"),
    create_option("r-jet-dynamic-rounds", "3"),
    create_option("r-jet-initial-negative-gain", "0.75"),
    create_option("r-jet-final-negative-gain", "0.0"),
    // main -> refinement -> fm
    create_option("r-fm-type", "do_nothing"),
    // main -> refinement -> flows
    create_option("r-flow-algo", "do_nothing"),
    // main -> mapping
    create_option("one-to-one-mapping-strategy", "greedy_mapping"),
    create_option("mapping-use-local-search", "true"),
    create_option("mapping-use-two-phase-approach", "false"),
    create_option("mapping-max-steiner-tree-size", "4"),
    create_option("mapping-largest-he-fraction", "0.0"),
    create_option("mapping-min-pin-coverage", "0.05"),
  };
}


std::vector<std::string> load_deterministic_quality_preset() {
  return {
    // general
    create_option("mode", "direct"),
    create_option("preset-type", "deterministic_quality"),
    create_option("deterministic", "true"),
    create_option("maxnet-removal-factor", "0.01"),
    create_option("smallest-maxnet-threshold", "50000"),
    create_option("maxnet-ignore", "1000"),
    create_option("num-vcycles", "0"),
    // main -> shared_memory
    create_option("s-use-localized-random-shuffle", "false"),
    create_option("s-static-balancing-work-packages", "128"),
    // main -> preprocessing
    create_option("p-stable-io", "true"),
    create_option("p-enable-community-detection", "true"),
    // main -> preprocessing -> community_detection
    create_option("p-louvain-edge-weight-function", "hybrid"),
    create_option("p-max-louvain-pass-iterations", "5"),
    create_option("p-louvain-min-vertex-move-fraction", "0.01"),
    create_option("p-vertex-degree-sampling-threshold", "200000"),
    create_option("p-louvain-low-memory-contraction", "true"),
    create_option("p-num-sub-rounds", "16"),
    // main -> coarsening
    create_option("c-type", "deterministic_multilevel_coarsener"),
    create_option("c-use-adaptive-edge-size", "false"),
    create_option("c-resolve-swaps", "true"),
    create_option("c-min-shrink-factor", "1.01"),
    create_option("c-max-shrink-factor", "2.5"),
    create_option("c-s", "1"),
    create_option("c-t", "160"),
    create_option("c-vertex-degree-sampling-threshold", "200000"),
    create_option("c-num-sub-rounds", "3"),
    // main -> coarsening -> rating
    create_option("c-rating-score", "heavy_edge"),
    create_option("c-rating-heavy-node-penalty", "no_penalty"),
    create_option("c-rating-acceptance-criterion", "best_prefer_unmatched"),
    // main -> initial_partitioning
    create_option("i-mode", "rb"),
    create_option("i-runs", "20"),
    create_option("i-use-adaptive-ip-runs", "false"),
    create_option("i-perform-refinement-on-best-partitions", "false"),
    create_option("i-remove-degree-zero-hns-before-ip", "true"),
    create_option("i-fm-refinement-rounds", "3"),
    create_option("i-lp-maximum-iterations", "20"),
    create_option("i-lp-initial-block-size", "5"),
    // main -> initial_partitioning -> refinement
    create_option("i-r-refine-until-no-improvement", "false"),
    // main -> initial_partitioning -> refinement -> label_propagation
    create_option("i-r-lp-type", "deterministic"),
    create_option("i-r-lp-maximum-iterations", "5"),
    create_option("i-r-sync-lp-sub-rounds", "1"),
    create_option("i-r-lp-he-size-activation-threshold", "100"),
    create_option("i-r-sync-lp-active-nodeset", "true"),
    // main -> initial_partitioning -> refinement -> fm
    create_option("i-r-fm-type", "do_nothing"),
    create_option("i-population-size", "64"),
    // main -> refinement
    create_option("r-refine-until-no-improvement", "false"),
    // main -> refinement -> rebalancing
    create_option("r-rebalancer-type", "deterministic"),
    create_option("r-max-det-rebalancing-rounds", "0"),
    create_option("r-det-rebalancing-deadzone", "0.1"),
    create_option("r-det-rebalancing-heavy-vertex-exclusion", "1.5"),
    // main -> refinement -> label_propagation
    create_option("r-lp-type", "do_nothing"),
    create_option("r-lp-maximum-iterations", "5"),
    create_option("r-sync-lp-sub-rounds", "1"),
    create_option("r-lp-he-size-activation-threshold", "100"),
    create_option("r-sync-lp-active-nodeset", "true"),
    // main -> refinement -> jet
    create_option("r-jet-type", "deterministic"),
    create_option("r-jet-num-iterations", "8"),
    create_option("r-jet-relative-improvement-threshold", "0.001"),
    create_option("r-jet-dynamic-rounds", "3"),
    create_option("r-jet-initial-negative-gain", "0.75"),
    create_option("r-jet-final-negative-gain", "0.0"),
    // main -> refinement -> fm
    create_option("r-fm-type", "do_nothing"),
    // main -> refinement -> flows
    create_option("r-flow-algo", "deterministic"),
    create_option("r-flow-scaling", "16"),
    create_option("r-flow-max-num-pins", "4294967295"),
    create_option("r-flow-find-most-balanced-cut", "true"),
    create_option("r-flow-determine-distance-from-cut", "true"),
    create_option("r-flow-max-bfs-distance", "2"),
    create_option("r-flow-min-relative-improvement-per-round", "0.001"),
    create_option("r-flow-time-limit-factor", "8"),
    create_option("r-flow-skip-small-cuts", "true"),
    create_option("r-flow-skip-unpromising-blocks", "true"),
    create_option("r-flow-pierce-in-bulk", "true"),
    create_option("r-flow-process-mapping-policy", "lower_bound"),
    // main -> mapping
    create_option("one-to-one-mapping-strategy", "greedy_mapping"),
    create_option("mapping-use-local-search", "true"),
    create_option("mapping-use-two-phase-approach", "false"),
    create_option("mapping-max-steiner-tree-size", "4"),
    create_option("mapping-largest-he-fraction", "0.0"),
    create_option("mapping-min-pin-coverage", "0.05"),
  };
}


std::vector<std::string> load_large_k_preset() {
  return {
    // general
    create_option("mode", "deep"),
    create_option("preset-type", "large_k"),
    create_option("maxnet-removal-factor", "0.01"),
    create_option("smallest-maxnet-threshold", "50000"),
    create_option("maxnet-ignore", "1000"),
    create_option("allow-empty-blocks", "true"),
    create_option("num-vcycles", "0"),
    // main -> shared_memory
    create_option("s-use-localized-random-shuffle", "false"),
    create_option("s-static-balancing-work-packages", "128"),
    // main -> preprocessing
    create_option("p-enable-community-detection", "true"),
    // main -> preprocessing -> community_detection
    create_option("p-louvain-edge-weight-function", "hybrid"),
    create_option("p-max-louvain-pass-iterations", "5"),
    create_option("p-louvain-min-vertex-move-fraction", "0.01"),
    create_option("p-vertex-degree-sampling-threshold", "200000"),
    // main -> coarsening
    create_option("c-type", "multilevel_coarsener"),
    create_option("c-use-adaptive-edge-size", "true"),
    create_option("c-min-shrink-factor", "1.1"),
    create_option("c-max-shrink-factor", "2.5"),
    create_option("c-s", "1"),
    create_option("c-t", "500"),
    create_option("c-deep-t", "160"),
    create_option("c-vertex-degree-sampling-threshold", "200000"),
    // main -> coarsening -> rating
    create_option("c-rating-score", "heavy_edge"),
    create_option("c-rating-heavy-node-penalty", "no_penalty"),
    create_option("c-rating-acceptance-criterion", "best_prefer_unmatched"),
    // main -> coarsening -> two-hop
    create_option("c-use-two-hop", "true"),
    create_option("c-two-hop-full-shrinkage", "true"),
    create_option("c-two-hop-threshold", "1.75"),
    create_option("c-two-hop-cluster-size", "4"),
    create_option("c-two-hop-degree-threshold", "100"),
    // main -> initial_partitioning
    create_option("i-mode", "direct"),
    create_option("i-runs", "5"),
    // disabled ip algos: greedy_sequential_fm, label_propagation, greedy_global_max_net
    create_option("i-enabled-ip-algos", "greedy_round_robin_fm"),
    create_option("i-enabled-ip-algos", "greedy_global_fm"),
    create_option("i-enabled-ip-algos", "random"),
    create_option("i-enabled-ip-algos", "bfs"),
    create_option("i-enabled-ip-algos", "greedy_round_robin_max_net"),
    create_option("i-enabled-ip-algos", "greedy_sequential_max_net"),
    create_option("i-use-adaptive-ip-runs", "true"),
    create_option("i-min-adaptive-ip-runs", "3"),
    create_option("i-perform-refinement-on-best-partitions", "true"),
    create_option("i-remove-degree-zero-hns-before-ip", "true"),
    create_option("i-fm-refinement-rounds", "1"),
    create_option("i-lp-maximum-iterations", "20"),
    create_option("i-lp-initial-block-size", "5"),
    // main -> initial_partitioning -> refinement
    create_option("i-r-refine-until-no-improvement", "false"),
    // main -> initial_partitioning -> refinement -> label_propagation
    create_option("i-r-lp-type", "label_propagation"),
    create_option("i-r-lp-maximum-iterations", "5"),
    create_option("i-r-lp-rebalancing", "true"),
    create_option("i-r-lp-he-size-activation-threshold", "100"),
    // main -> initial_partitioning -> refinement -> fm
    create_option("i-r-fm-type", "do_nothing"),
    // main -> initial_partitioning -> refinement -> flows
    create_option("i-r-flow-algo", "do_nothing"),
    // main -> refinement
    create_option("r-rebalancer-type", "deterministic"),
    create_option("r-max-det-rebalancing-rounds", "5"),
    create_option("r-det-rebalancing-deadzone", "0.5"),
    create_option("r-det-rebalancing-heavy-vertex-exclusion", "1.5"),
    create_option("r-refine-until-no-improvement", "false"),
    // main -> refinement -> label_propagation
    create_option("r-lp-type", "label_propagation"),
    create_option("r-lp-maximum-iterations", "5"),
    create_option("r-lp-rebalancing", "true"),
    create_option("r-lp-he-size-activation-threshold", "100"),
    // main -> refinement -> fm
    create_option("r-fm-type", "do_nothing"),
    // main -> refinement -> flows
    create_option("r-flow-algo", "do_nothing"),
  };
}


std::vector<std::string> loadPreset(PresetType preset) {
  switch( preset ) {
    case PresetType::deterministic:
      return load_deterministic_preset();
    case PresetType::deterministic_quality:
      return load_deterministic_quality_preset();
    case PresetType::large_k:
      return load_large_k_preset();
    case PresetType::default_preset:
      return load_default_preset();
    case PresetType::quality:
      return load_quality_preset();
    case PresetType::highest_quality:
      return load_highest_quality_preset();
    case PresetType::UNDEFINED:
      // can't be an exception since it is called in a C library
      // function without error return
      ERR("invalid preset");
  }
  return {};
}

} // namespace mt_kahypar
