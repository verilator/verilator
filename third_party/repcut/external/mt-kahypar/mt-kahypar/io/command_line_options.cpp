/*******************************************************************************
 * MIT License
 *
 * This file is part of Mt-KaHyPar.
 *
 * Copyright (C) 2019 Lars Gottesbüren <lars.gottesbueren@kit.edu>
 * Copyright (C) 2019 Tobias Heuer <tobias.heuer@kit.edu>
 * Copyright (C) 2025 Nikolai Maas <nikolai.maas@kit.edu>
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

// I don't understand what is happening here, but OK
#undef V
#include <CLI/CLI.hpp>

#include "command_line_options.h"

#ifdef _WIN32
#include <windows.h>
#else
#include <sys/ioctl.h>
#endif

#include <fstream>
#include <iostream>
#include <limits>
#include <memory>
#include <string>

#include "mt-kahypar/io/presets.h"
#include "mt-kahypar/utils/exception.h"
#include "mt-kahypar/io/version.h"


namespace mt_kahypar {
  namespace platform {
    int getTerminalWidth() {
      int columns = 0;
      #if defined(_WIN32)
      CONSOLE_SCREEN_BUFFER_INFO csbi;
      GetConsoleScreenBufferInfo(GetStdHandle(STD_OUTPUT_HANDLE), &csbi);
      columns = csbi.srWindow.Right - csbi.srWindow.Left + 1;
      #else
      struct winsize w = { };
      ioctl(0, TIOCGWINSZ, &w);
      columns = w.ws_col;
      #endif
      return columns;
    }
  }  // namespace platform

  // customized formatting of help output
  class MyFormatter: public CLI::Formatter {
   public:
    MyFormatter(): CLI::Formatter() {
      const int width = platform::getTerminalWidth();
      if (width >= 100) {
        long_option_alignment_ratio_ = 1 / 4.5f;
        column_width_ = 35;
        right_column_width_ = 65;
      } else {
        long_option_alignment_ratio_ = 1 / 3.5f;
        column_width_ = 25;
        right_column_width_ = 55;
      }
    }

   private:
    virtual std::string make_usage(const CLI::App*, std::string) const override {
      return "";
    }

    virtual std::string make_option_opts(const CLI::Option* opt) const override {
      std::stringstream out;

      if(!opt->get_option_text().empty()) {
        out << " " << opt->get_option_text();
      } else {
        if(opt->get_type_size() != 0) {
          std::string t_name = !opt->get_type_name().empty() ? get_label(opt->get_type_name()) : "";

          // slightly hacky fine-tuning of help output
          bool is_predefined_option = t_name.find("TEXT:{") != std::string::npos;
          if (t_name == "TEXT:FILE") t_name = "FILE";
          if (t_name.find("TEXT:PATH") == 0) t_name = "PATH";
          if (t_name.find("INT:") == 0) t_name = "INT";
          if (t_name.find("LIST[UINT]:") == 0) t_name = "LIST[UINT]";

          // print type
          bool print_type_name = !opt->get_type_name().empty() && !is_predefined_option;
          if(print_type_name) {
            out << "  " << t_name;
          }
          if(!opt->get_default_str().empty()) {
            if (!print_type_name) out << " ";
            out << " (=" << opt->get_default_str() << ") ";
          }
        }
      }
      return out.str();
    }
  };


  CLI::Option* addRequiredOptions(Context& context, CLI::App& app) {
    app.set_help_flag();  // avoid collision with --hypergraph

    app.option_defaults()->group("Required Options");
    app.add_option(
      "-h,--hypergraph",
      context.partition.graph_filename,
      "Hypergraph (or graph) filename"
    )->required()->check(CLI::ExistingFile);
    app.add_option(
      "-k,--blocks",
      context.partition.k,
      "Number of blocks"
    )->required();
    app.add_option(
      "-e,--epsilon",
      context.partition.epsilon,
      "Imbalance parameter epsilon"
    );
    app.add_option_function<std::string>(
      "-o,--objective", [&](const std::string& s) {
        context.partition.objective = objectiveFromString(s);
      },
      "Objective:\n"
      " - cut:  cut-net metric\n"
      " - km1:  connectivity metric\n"
      " - soed: sum-of-external-degree metric\n"
      " - steiner_tree: maps a (hyper)graph onto a target graph"
    )->required()->check(CLI::IsMember({"cut", "km1", "soed", "steiner_tree"}));
    return app.add_option_function<std::string>(
      "--preset-type", [&](const std::string& s) {
        context.partition.preset_type = presetTypeFromString(s);
        presetToContext(context, context.partition.preset_type, false);
      },
      "Preset:\n"
      " - default\n"
      " - quality\n"
      " - highest_quality\n"
      " - deterministic\n"
      " - deterministic_quality\n"
      " - large_k"
    )
    ->callback_priority(CLI::CallbackPriority::First)
    ->check(CLI::IsMember(validPresetTypes()));
  }

  void addUserOptions(Context& context, CLI::App& app, CLI::Option* preset_option, bool detailed) {
    app.option_defaults()->group("Additional Options");
    app.add_option_function<size_t>(
      // keep --s-num-threads for backwards compatibility
      detailed ? "-t,--threads,--s-num-threads" : "-t,--threads",
      [&](const size_t& num_threads) {
        context.shared_memory.num_threads = num_threads;
        context.shared_memory.original_num_threads = num_threads;
      },
      "Number of threads (default: sequential execution)"
    )->default_str("1");
    app.add_option(
      "-s,--seed",
      context.partition.seed,
      "Seed for randomization"
    )->capture_default_str();
    app.add_option_function<std::string>(
      // keep --input-file-format for backwards compatibility
      detailed ? "--file-format,--input-file-format" : "--file-format",
      [&](const std::string& s) {
        context.partition.file_format = fileFormatFromString(s);
      },
      "Input file format:\n"
      " - hmetis: hMETIS hypergraph file format\n"
      " - metis: METIS graph file format"
    )->check(CLI::IsMember({"hmetis", "metis"}))->default_str("hmetis");
    if (detailed) {
      app.add_option_function<std::string>(
        "--instance-type", [&](const std::string& s) {
          context.partition.instance_type = instanceTypeFromString(s);
        },
        "Instance Type (default: derive from file format):\n"
        " - graph\n"
        " - hypergraph"
      )->check(CLI::IsMember({"graph", "hypergraph"}));
    }
    app.add_flag(
      "-w,--write-partition-file",
      context.partition.write_partition_file,
      "Generate partition output file"
    );
    app.add_option(
      "--partition-output-folder",
      context.partition.graph_partition_output_folder,
      "Output folder for partition file"
    )->check(CLI::ExistingPath);
    auto config_option = app.add_option_function<std::string>(
      "-c,--config", [&](const std::string& file) {
        parseIniToContext(context, file, false);
      },
      "Config file, replaces the preset:\n"
      "<path-to-ini-file> (see config directory)"
    )->callback_priority(CLI::CallbackPriority::First)->check(CLI::ExistingFile);
    if (preset_option != nullptr) config_option->excludes(preset_option);
    app.add_option(
      // keep --target-graph-file for backwards compatibility
      detailed ? "-g,--target-graph,--target-graph-file" : "-g,--target-graph",
      context.mapping.target_graph_file,
      "Path to a target architecture graph in Metis file format (steiner_tree objective)."
    )->check(CLI::ExistingFile);
    app.add_option(
      "-f,--fixed",
      context.partition.fixed_vertex_filename,
      "Fixed vertex file: allows to pre-assign vertices to a block."
    )->check(CLI::ExistingFile);
    app.add_option(
      "--part-weights",
      context.partition.max_part_weights,
      "Use the specified individual part weights instead of epsilon."
    )->transform([&](const auto& value) {
      context.partition.use_individual_part_weights = true;
      return value;
    })->check(CLI::PositiveNumber)->type_name("LIST[UINT]");
    app.add_flag(
      "--allow-empty-blocks",
      context.partition.allow_empty_blocks,
      "Allow that the partition leaves blocks empty."
    );
    app.add_option(
      "--num-vcycles",
      context.partition.num_vcycles,
      "Number of V-Cycles to further improve the partition quality."
    )->capture_default_str();

    // --help and --version
    app.set_help_flag();
    app.add_flag_callback("--help", [&]{
        // custom help output
        printHelp(context, context.partition.verbose_logging);
        std::exit(0);
      },
      "Print this help and exit."
    )->callback_priority(CLI::CallbackPriority::PreRequirementsCheck);
    app.add_flag_callback(
      "--version", [&]{
        std::cout << "Mt-KaHyPar v" << MT_KAHYPAR_PROJECT_VERSION << std::endl;
        std::exit(0);
      },
      "Print version information and exit."
    )->callback_priority(CLI::CallbackPriority::PreRequirementsCheck);
  }

  void addDisplayOptions(Context& context, CLI::App& app, bool detailed) {
    app.option_defaults()->group("Display Options");
    app.add_flag_callback(
      "-q,--quiet", [&]{
        context.partition.enable_logging = false;
      },
      "Disable partitioning output"
    );
    app.add_flag(
      "-v,--verbose",
      context.partition.verbose_logging,
      "Verbose partitioning output"
      // increase priority so the flag can be used to extend the help output
    )->callback_priority(CLI::CallbackPriority::PreRequirementsCheckPreHelp);
    app.add_flag(
      "--enable-progress-bar",
      context.partition.enable_progress_bar,
      "Show a progress bar during coarsening and refinement."
    );
    app.add_flag(
      "--show-detailed-timings",
      context.partition.show_detailed_timings,
      "Show detailed subtimings of each multilevel phase."
    );
    if (detailed) {
      app.add_flag(
        "--show-detailed-clustering-timings",
        context.partition.show_detailed_clustering_timings,
        "Show detailed timings of each clustering iteration."
      );
      app.add_flag(
        "--show-detailed-uncontraction-timings",
        context.partition.show_detailed_uncontraction_timings,
        "Show detailed timings for n-level uncontraction."
      );
      app.add_flag(
        "--show-memory-consumption",
        context.partition.show_memory_consumption,
        "Show detailed information on how much memory was allocated "
        "and how memory was reused throughout partitioning."
      );
      app.add_flag(
        "--show-advanced-cut-analysis",
        context.partition.show_advanced_cut_analysis,
        "If true, calculates cut matrix, potential positive gain move matrix "
        "and connected cut hyperedge components after partitioning."
      );
      app.add_option(
        "--timings-output-depth",
        context.partition.timings_output_depth,
        "Number of levels shown in timing output"
      );
      app.add_flag(
        "--sp-process",
        context.partition.sp_process_output,
        "Summarize partitioning results in RESULT line compatible with sqlplottools "
        "(https://github.com/bingmann/sqlplottools)"
      );
      app.add_flag(
        "--csv",
        context.partition.csv_output,
        "Summarize results in CSV format"
      );
      app.add_option(
        "--algorithm-name",
        context.algorithm_name,
        "Algorithm name to print into the summarized output (csv or sqlplottools)."
      );
    }
  }

  void addGeneralOptions(Context& context, CLI::App& app) {
    app.option_defaults()->group("General Options");
    app.add_option_function<std::string>(
      "-m,--mode", [&](const std::string& s) {
        context.partition.mode = modeFromString(s);
      },
      "Partitioning mode: \n"
      " - direct: direct k-way partitioning\n"
      " - rb: recursive bipartitioning\n"
      " - deep: deep multilevel partitioning"
    )->capture_default_str();
    app.add_option(
      "--deterministic",
      context.partition.deterministic,
      "Necessary for deterministic partitioning: makes preprocessing and initial partitioning deterministic, "
      "and adds a check that no non-deterministic refinement algorithm is active."
    )->capture_default_str();
    app.add_option(
      "--perform-parallel-recursion-in-deep-multilevel",
      context.partition.perform_parallel_recursion_in_deep_multilevel,
      "Perform parallel recursion within the deep multilevel scheme."
    )->capture_default_str();
    app.add_option(
      "--smallest-maxnet-threshold",
      context.partition.smallest_large_he_size_threshold,
      "No hyperedge whose size is smaller than this threshold is removed in the large hyperedge removal step (see maxnet-removal-factor)"
    )->capture_default_str();
    app.add_option(
      "--maxnet-removal-factor",
      context.partition.large_hyperedge_size_threshold_factor,
      "Hyperedges larger than max(|V| * (this factor), p-smallest-maxnet-threshold) are removed before partitioning."
    )->capture_default_str();
    app.add_option(
      "--maxnet-ignore",
      context.partition.ignore_hyperedge_size_threshold,
      "Hyperedges larger than this threshold are partially ignored during partitioning."
    )->capture_default_str();
    auto time_limit = app.add_option(
      "--time-limit",
      context.partition.time_limit,
      "Time limit in seconds (not supported)"
    )->capture_default_str();
    CLI::retire_option(app, time_limit);
  }

  void addPreprocessingOptions(Context& context, CLI::App& app) {
    app.option_defaults()->group("Preprocessing Options");
    app.add_option(
      "--p-stable-io",
      context.preprocessing.stable_construction_of_incident_edges,
      "If true, the incident edges of a vertex are sorted after construction, so that the hypergraph "
      "data structure is independent of scheduling during construction."
    )->capture_default_str();
    app.add_option(
      "--p-enable-community-detection",
      context.preprocessing.use_community_detection,
      "If true, community detection is used as preprocessing step to restrict "
      "contractions to densely coupled regions in coarsening phase"
    )->capture_default_str();
    app.add_option(
      "--p-disable-community-detection-on-mesh-graphs",
      context.preprocessing.disable_community_detection_for_mesh_graphs,
      "If true, community detection is dynamically disabled for mesh graphs "
      "(as it is not effective for this type of graphs)."
    )->capture_default_str();
    app.add_option_function<std::string>(
      "--p-louvain-edge-weight-function", [&](const std::string& s) {
        context.preprocessing.community_detection.edge_weight_function = louvainEdgeWeightFromString(s);
      },
      "Louvain edge weight functions:\n"
      "- hybrid\n"
      "- uniform\n"
      "- non_uniform\n"
      "- degree"
    )->capture_default_str();
    app.add_option(
      "--p-max-louvain-pass-iterations",
      context.preprocessing.community_detection.max_pass_iterations,
      "Maximum number of iterations over all nodes of one louvain pass"
    )->capture_default_str();
    app.add_option(
      "--p-louvain-low-memory-contraction",
      context.preprocessing.community_detection.low_memory_contraction,
      "Use contraction algorithm with low memory usage in louvain algorithm"
    )->capture_default_str();
    app.add_option(
      "--p-louvain-min-vertex-move-fraction",
      context.preprocessing.community_detection.min_vertex_move_fraction,
      "Louvain pass terminates if less than that fraction of nodes moves during a passs"
    )->capture_default_str();
    app.add_option(
      "--p-vertex-degree-sampling-threshold",
      context.preprocessing.community_detection.vertex_degree_sampling_threshold,
      "If set, then neighbors of a vertex are sampled during rating if its degree is greater than this threshold."
    )->capture_default_str();
    app.add_option(
      "--p-num-sub-rounds",
      context.preprocessing.community_detection.num_sub_rounds_deterministic,
      "Number of sub-rounds used for deterministic community detection in preprocessing."
    )->capture_default_str();
  }

  void addCoarseningOptions(Context& context, CLI::App& app) {
    app.option_defaults()->group("Coarsening Options");
    app.add_option_function<std::string>(
      "--c-type", [&](const std::string& s) {
        context.coarsening.algorithm = coarseningAlgorithmFromString(s);
      },
      "Coarsening Algorithm:\n"
      " - multilevel_coarsener\n"
      " - nlevel_coarsener\n"
      " - deterministic_multilevel_coarsener\n"
      " - do_nothing"
    )->capture_default_str();
    app.add_option(
      "--c-use-adaptive-edge-size",
      context.coarsening.use_adaptive_edge_size,
      "If true, the rating function uses the number of distinct cluster IDs of a net as edge size rather "
      "than its original size during multilevel coarsing"
    )->capture_default_str();
    app.add_option(
      "--c-s",
      context.coarsening.max_allowed_weight_multiplier,
      "The maximum weight of a vertex in the coarsest hypergraph H is:\n"
      "(s * w(H)) / (t * k)"
    )->capture_default_str();
    app.add_option(
      "--c-t",
      context.coarsening.contraction_limit_multiplier,
      "Coarsening stops when there are no more than t * k hypernodes left"
    )->capture_default_str();
    app.add_option(
      "--c-deep-t",
      context.coarsening.deep_ml_contraction_limit_multiplier,
      "Deep multilevel performs coarsening until 2 * deep-t hypernodes are left for bipartitioning calls"
    )->capture_default_str();
    app.add_option(
      "--c-min-shrink-factor",
      context.coarsening.minimum_shrink_factor,
      "Minimum factor a hypergraph must shrink in a multilevel pass. Otherwise, we terminate coarsening phase."
    )->capture_default_str();
    app.add_option(
      "--c-max-shrink-factor",
      context.coarsening.maximum_shrink_factor,
      "Maximum factor a hypergraph is allowed to shrink in a clustering pass"
    )->capture_default_str();
    app.add_option_function<std::string>(
      "--c-rating-score", [&](const std::string& s) {
        context.coarsening.rating.rating_function = ratingFunctionFromString(s);
      },
      "Rating function used to calculate scores for vertex pairs:\n"
      #ifdef KAHYPAR_ENABLE_EXPERIMENTAL_FEATURES
      "- sameness\n"
      #endif
      "- heavy_edge"
    )->capture_default_str();
    app.add_option_function<std::string>(
      "--c-rating-heavy-node-penalty", [&](const std::string& s) {
        context.coarsening.rating.heavy_node_penalty_policy = heavyNodePenaltyFromString(s);
      },
      "Penalty function to discourage heavy vertices:\n"
      #ifdef KAHYPAR_ENABLE_EXPERIMENTAL_FEATURES
      "- additive\n"
      "- multiplicative\n"
      #endif
      "- no_penalty"
    )->capture_default_str();
    app.add_option_function<std::string>(
      "--c-rating-acceptance-criterion", [&](const std::string& s) {
        context.coarsening.rating.acceptance_policy = acceptanceCriterionFromString(s);
      },
      "Acceptance/Tiebreaking criterion for contraction partners having the same score:\n"
      #ifdef KAHYPAR_ENABLE_EXPERIMENTAL_FEATURES
      "- best\n"
      #endif
      "- best_prefer_unmatched"
    )->capture_default_str();
    app.add_option(
      "--c-vertex-degree-sampling-threshold",
      context.coarsening.vertex_degree_sampling_threshold,
      "If set, then neighbors of a vertex are sampled during rating "
      "if its degree is greater than this threshold."
    )->capture_default_str();
    app.add_option(
      "--c-num-sub-rounds",
      context.coarsening.num_sub_rounds_deterministic,
      "Number of sub-rounds used for deterministic coarsening."
    )->capture_default_str();
    app.add_option(
      "--c-resolve-swaps",
      context.coarsening.det_resolve_swaps,
      "Whether to resolve node swaps in a postprocessing step for deterministic coarsening."
    )->capture_default_str();
    app.add_option(
      "--c-use-two-hop",
      context.coarsening.use_two_hop,
      "Multilevel coarsener: use two-hop clustering, which clusters non-adjacent nodes, if the hypergraph would not shrink enough otherwise."
    )->capture_default_str();
    app.add_option(
      "--c-two-hop-full-shrinkage",
      context.coarsening.two_hop_full_shrinkage,
      "Use full hierarchy contraction factor for two-hop clustering (otherwise: use c-two-hop-threshold)."
    )->capture_default_str();
    app.add_option(
      "--c-two-hop-threshold",
      context.coarsening.two_hop_shrink_threshold,
      "If the hypergraph shrinks less than this factor in a clustering pass, two-hop clustering is used."
    )->capture_default_str();
    app.add_option(
      "--c-two-hop-cluster-size",
      context.coarsening.two_hop_cluster_size,
      "Two-hop clustering: maximum number of nodes in one cluster"
    )->capture_default_str();
    app.add_option(
      "--c-two-hop-degree-threshold",
      context.coarsening.two_hop_degree_threshold,
      "Vertices with more neighbors than the provided threshold are ignored during two-hop clustering."
    )->capture_default_str();
  }

  void addRefinementOptions(Context& context, CLI::App& app, const bool initial_partitioning) {
    app.option_defaults()->group(initial_partitioning ? "Refinement Options for Initial Partitioning" : "Refinement Options");
    app.add_option(
      (initial_partitioning ? "--i-r-refine-until-no-improvement" : "--r-refine-until-no-improvement"),
      (!initial_partitioning ? context.refinement.refine_until_no_improvement :
        context.initial_partitioning.refinement.refine_until_no_improvement),
      "Executes all refinement algorithms as long as they find an improvement on the current partition."
    )->capture_default_str();
    app.add_option(
      (initial_partitioning ? "--i-r-relative-improvement-threshold" : "--r-relative-improvement-threshold"),
      (!initial_partitioning ? context.refinement.relative_improvement_threshold :
        context.initial_partitioning.refinement.relative_improvement_threshold),
      "If the relative improvement during a refinement pass is less than this threshold, than refinement is aborted."
    )->capture_default_str();
    app.add_option(
      (initial_partitioning ? "--i-r-max-batch-size" : "--r-max-batch-size"),
      (!initial_partitioning ? context.refinement.max_batch_size :
        context.initial_partitioning.refinement.max_batch_size),
      "Maximum size of an uncontraction batch (n-Level Partitioner)."
    )->capture_default_str();
    app.add_option(
      (initial_partitioning ? "--i-r-min-border-vertices-per-thread" : "--r-min-border-vertices-per-thread"),
      (!initial_partitioning ? context.refinement.min_border_vertices_per_thread :
        context.initial_partitioning.refinement.min_border_vertices_per_thread),
      "Minimum number of border vertices per thread with which we perform a localized search (n-Level Partitioner)."
    )->capture_default_str();

    // Label Propagation
    app.add_option_function<std::string>(
      (initial_partitioning ? "--i-r-lp-type" : "--r-lp-type"), [&, initial_partitioning](const std::string& s) {
        if (initial_partitioning) {
          context.initial_partitioning.refinement.label_propagation.algorithm =
                  labelPropagationAlgorithmFromString(s);
        } else {
          context.refinement.label_propagation.algorithm =
                  labelPropagationAlgorithmFromString(s);
        }
      },
      "Label Propagation Algorithm:\n"
      "- label_propagation\n"
      "- deterministic\n"
      "- do_nothing"
    )->capture_default_str();
    app.add_option(
      (initial_partitioning ? "--i-r-lp-maximum-iterations" : "--r-lp-maximum-iterations"),
      (!initial_partitioning ? context.refinement.label_propagation.maximum_iterations :
        context.initial_partitioning.refinement.label_propagation.maximum_iterations ),
      "Maximum number of label propagation rounds"
    )->capture_default_str();
    app.add_option(
      (initial_partitioning ? "--i-r-sync-lp-sub-rounds" : "--r-sync-lp-sub-rounds"),
      (!initial_partitioning ? context.refinement.deterministic_refinement.num_sub_rounds_sync_lp :
        context.initial_partitioning.refinement.deterministic_refinement.num_sub_rounds_sync_lp ),
      "Number of sub-rounds for deterministic synchronous label propagation"
    )->capture_default_str();
    app.add_option(
      (initial_partitioning ? "--i-r-sync-lp-active-nodeset" : "--r-sync-lp-active-nodeset"),
      (!initial_partitioning ? context.refinement.deterministic_refinement.use_active_node_set :
        context.initial_partitioning.refinement.deterministic_refinement.use_active_node_set ),
      "Use active nodeset in synchronous label propagation"
    )->capture_default_str();
    app.add_option(
      (initial_partitioning ? "--i-r-lp-rebalancing" : "--r-lp-rebalancing"),
      (!initial_partitioning ? context.refinement.label_propagation.rebalancing :
        context.initial_partitioning.refinement.label_propagation.rebalancing ),
      "Zero gain moves are only performed if they improve the balance of the solution (only in label propagation)"
    )->capture_default_str();
    app.add_option(
      (initial_partitioning ? "--i-r-lp-unconstrained" : "--r-lp-unconstrained"),
      (!initial_partitioning ? context.refinement.label_propagation.unconstrained :
        context.initial_partitioning.refinement.label_propagation.unconstrained ),
      "If true, then unconstrained label propagation (including rebalancing) is used."
    )->capture_default_str();
    app.add_option(
      (initial_partitioning ? "--i-r-lp-he-size-activation-threshold" : "--r-lp-he-size-activation-threshold"),
      (!initial_partitioning ? context.refinement.label_propagation.hyperedge_size_activation_threshold :
        context.initial_partitioning.refinement.label_propagation.hyperedge_size_activation_threshold ),
      "LP refiner activates only neighbors of moved vertices that are part of hyperedges with a size less than this threshold"
    )->capture_default_str();
    app.add_option(
      (initial_partitioning ? "--i-r-lp-relative-improvement-threshold" : "--r-lp-relative-improvement-threshold"),
      (!initial_partitioning ? context.refinement.label_propagation.relative_improvement_threshold :
        context.initial_partitioning.refinement.label_propagation.relative_improvement_threshold ),
      "Relative improvement threshold for label propagation."
    )->capture_default_str();

    // Jet
    app.add_option_function<std::string>(
      (initial_partitioning ? "--i-r-jet-type" : "--r-jet-type"), [&, initial_partitioning](const std::string& s) {
        if (initial_partitioning) {
          context.initial_partitioning.refinement.jet.algorithm = jetAlgorithmFromString(s);
        } else {
          context.refinement.jet.algorithm = jetAlgorithmFromString(s);
        }
      },
      "Jet Algorithm:\n"
      "- deterministic\n"
      "- do_nothing"
    )->capture_default_str();
    app.add_option(
      (initial_partitioning ? "--i-r-jet-num-iterations" : "--r-jet-num-iterations"),
      (!initial_partitioning ? context.refinement.jet.num_iterations :
        context.initial_partitioning.refinement.jet.num_iterations ),
      "Jet: number of iterations without significant improvement"
    )->capture_default_str();
    app.add_option(
      (initial_partitioning ? "--i-r-jet-relative-improvement-threshold" : "--r-jet-relative-improvement-threshold"),
      (!initial_partitioning ? context.refinement.jet.relative_improvement_threshold :
        context.initial_partitioning.refinement.jet.relative_improvement_threshold ),
      "Relative improvement threshold for Jet."
    )->capture_default_str();
    app.add_option(
      (initial_partitioning ? "--i-r-jet-dynamic-rounds" : "--r-jet-dynamic-rounds"),
      (!initial_partitioning ? context.refinement.jet.dynamic_rounds :
        context.initial_partitioning.refinement.jet.dynamic_rounds ),
      "Jet: number of dynamic rounds with decreasing temperature"
    )->capture_default_str();
    app.add_option(
      (initial_partitioning ? "--i-r-jet-initial-negative-gain" : "--r-jet-initial-negative-gain"),
      (!initial_partitioning ? context.refinement.jet.initial_negative_gain_factor :
        context.initial_partitioning.refinement.jet.initial_negative_gain_factor ),
      "Jet: initial negative gain factor for dynamic gain factor"
    )->capture_default_str();
    app.add_option(
      (initial_partitioning ? "--i-r-jet-final-negative-gain" : "--r-jet-final-negative-gain"),
      (!initial_partitioning ? context.refinement.jet.final_negative_gain_factor :
        context.initial_partitioning.refinement.jet.final_negative_gain_factor ),
      "Jet: final negative gain factor for dynamic gain factor"
    )->capture_default_str();

    // FM
    app.add_option_function<std::string>(
      (initial_partitioning ? "--i-r-fm-type" : "--r-fm-type"), [&, initial_partitioning](const std::string& s) {
        if (initial_partitioning) {
          context.initial_partitioning.refinement.fm.algorithm = fmAlgorithmFromString(s);
        } else {
          context.refinement.fm.algorithm = fmAlgorithmFromString(s);
        }
      },
      "FM Algorithm:\n"
      "- kway_fm\n"
      "- unconstrained_fm\n"
      "- do_nothing"
    )->capture_default_str();
    app.add_option(
      (initial_partitioning ? "--i-r-fm-multitry-rounds" : "--r-fm-multitry-rounds"),
      (!initial_partitioning ? context.refinement.fm.multitry_rounds :
        context.initial_partitioning.refinement.fm.multitry_rounds ),
      "Number of FM rounds within one level of the multilevel hierarchy."
    )->capture_default_str();
    app.add_option(
      (initial_partitioning ? "--i-r-fm-seed-nodes" : "--r-fm-seed-nodes"),
      (!initial_partitioning ? context.refinement.fm.num_seed_nodes :
        context.initial_partitioning.refinement.fm.num_seed_nodes ),
      "Number of nodes to start the 'highly localized FM' with."
    )->capture_default_str();
    app.add_option(
      (initial_partitioning ? "--i-r-fm-rollback-parallel" : "--r-fm-rollback-parallel"),
      (!initial_partitioning ? context.refinement.fm.rollback_parallel :
        context.initial_partitioning.refinement.fm.rollback_parallel ),
      "Perform gain and balance recalculation, and reverting to best prefix in parallel."
    )->capture_default_str();
    app.add_option(
      (initial_partitioning ? "--i-r-fm-iter-moves-on-recalc" : "--r-fm-iter-moves-on-recalc"),
      (!initial_partitioning ? context.refinement.fm.iter_moves_on_recalc :
        context.initial_partitioning.refinement.fm.iter_moves_on_recalc ),
      "Touch only incident hyperedges of moved vertices for parallel gain recalculation."
    )->capture_default_str();
    app.add_option(
      (initial_partitioning ? "--i-r-fm-rollback-balance-violation-factor" : "--r-fm-rollback-balance-violation-factor"),
      (!initial_partitioning ? context.refinement.fm.rollback_balance_violation_factor :
        context.initial_partitioning.refinement.fm.rollback_balance_violation_factor ),
      "Used to relax or disable the balance constraint during the rollback phase of parallel FM. "
      "Set to 0 for disabling. Set to a value > 1.0 to multiply epsilon with this value."
    )->capture_default_str();
    app.add_option(
      (initial_partitioning ? "--i-r-fm-min-improvement" : "--r-fm-min-improvement"),
      (!initial_partitioning ? context.refinement.fm.min_improvement :
        context.initial_partitioning.refinement.fm.min_improvement ),
      "Min improvement for FM (default disabled)"
    )->capture_default_str();
    app.add_option(
      (initial_partitioning ? "--i-r-fm-release-nodes" : "--r-fm-release-nodes"),
      (!initial_partitioning ? context.refinement.fm.release_nodes :
        context.initial_partitioning.refinement.fm.release_nodes ),
      "FM releases nodes that weren't moved, so they might be found by another search."
    )->capture_default_str();
    app.add_option(
      (initial_partitioning ? "--i-r-fm-threshold-border-node-inclusion" : "--r-fm-threshold-border-node-inclusion"),
      (!initial_partitioning ? context.refinement.fm.treshold_border_node_inclusion :
        context.initial_partitioning.refinement.fm.treshold_border_node_inclusion ),
      "Threshold for block-internal incident weight when deciding whether to include border "
      "nodes for rebalancing estimation."
    )->capture_default_str();
    app.add_option(
      (initial_partitioning ? "--i-r-fm-unconstrained-rounds" : "--r-fm-unconstrained-rounds"),
      (!initial_partitioning ? context.refinement.fm.unconstrained_rounds :
        context.initial_partitioning.refinement.fm.unconstrained_rounds ),
      "Unconstrained FM: Number of rounds that are unconstrained."
    )->capture_default_str();
    app.add_option(
      (initial_partitioning ? "--i-r-fm-unconstrained-min-improvement" : "--r-fm-unconstrained-min-improvement"),
      (!initial_partitioning ? context.refinement.fm.unconstrained_min_improvement :
        context.initial_partitioning.refinement.fm.unconstrained_min_improvement ),
      "Switch to constrained FM if relative improvement of unconstrained FM is below this treshold."
    )->capture_default_str();
    app.add_option(
      (initial_partitioning ? "--i-r-fm-imbalance-penalty-min" : "--r-fm-imbalance-penalty-min"),
      (!initial_partitioning ? context.refinement.fm.imbalance_penalty_min :
        context.initial_partitioning.refinement.fm.imbalance_penalty_min ),
      "Unconstrained FM: Minimum (starting) penalty factor."
    )->capture_default_str();
    app.add_option(
      (initial_partitioning ? "--i-r-fm-imbalance-penalty-max" : "--r-fm-imbalance-penalty-max"),
      (!initial_partitioning ? context.refinement.fm.imbalance_penalty_max :
        context.initial_partitioning.refinement.fm.imbalance_penalty_max ),
      "Unconstrained FM: Maximum (final) penalty factor."
    )->capture_default_str();
    app.add_option(
      (initial_partitioning ? "--i-r-fm-unconstrained-upper-bound" : "--r-fm-unconstrained-upper-bound"),
      (!initial_partitioning ? context.refinement.fm.unconstrained_upper_bound :
        context.initial_partitioning.refinement.fm.unconstrained_upper_bound ),
      "Use upper limit for imbalance with unconstrained FM, expressed as a factor of the max part weight (0 = no limit)."
    )->capture_default_str();
    app.add_option(
      (initial_partitioning ? "--i-r-fm-unconstrained-upper-bound-min" : "--r-fm-unconstrained-upper-bound-min"),
      (!initial_partitioning ? context.refinement.fm.unconstrained_upper_bound_min :
        context.initial_partitioning.refinement.fm.unconstrained_upper_bound_min ),
      "Unconstrained FM: Minimum (final) upper bound (0 = equal to start)."
    )->capture_default_str();
    app.add_option(
      (initial_partitioning ? "--i-r-fm-activate-unconstrained-dynamically" : "--r-fm-activate-unconstrained-dynamically"),
      (!initial_partitioning ? context.refinement.fm.activate_unconstrained_dynamically :
        context.initial_partitioning.refinement.fm.activate_unconstrained_dynamically ),
      "Decide dynamically (based on first two rounds) whether to use unconstrained FM."
    )->capture_default_str();
    app.add_option(
      (initial_partitioning ? "--i-r-fm-penalty-for-activation-test" : "--r-fm-penalty-for-activation-test"),
      (!initial_partitioning ? context.refinement.fm.penalty_for_activation_test :
        context.initial_partitioning.refinement.fm.penalty_for_activation_test ),
      "If unconstrained FM is activated dynamically, determines the penalty factor used for the test round."
    )->capture_default_str();
    app.add_option(
      (initial_partitioning ? "--i-r-fm-obey-minimal-parallelism" : "--r-fm-obey-minimal-parallelism"),
      (!initial_partitioning ? context.refinement.fm.obey_minimal_parallelism :
        context.initial_partitioning.refinement.fm.obey_minimal_parallelism ),
      "If true, then parallel FM refinement stops if more than a certain number of threads are finished."
    )->capture_default_str();
    app.add_option(
      (initial_partitioning ? "--i-r-fm-time-limit-factor" : "--r-fm-time-limit-factor"),
      (!initial_partitioning ? context.refinement.fm.time_limit_factor :
        context.initial_partitioning.refinement.fm.time_limit_factor ),
      "If the FM time exceeds time_limit := k * factor * coarsening_time, than the FM config is switched into a light version. "
      "If the FM refiner exceeds 2 * time_limit, than the current multitry FM run is aborted and the algorithm proceeds to "
      "the next finer level."
    )->capture_default_str();

    // global refinement for n-level partitioning
    app.add_option(
      (initial_partitioning ? "--i-r-use-global-fm" : "--r-use-global-fm"),
      (!initial_partitioning ? context.refinement.global.use_global_refinement :
        context.initial_partitioning.refinement.global.use_global_refinement ),
      "If true, than we execute a globalized FM local search interleaved with the localized searches. "
      "Note, gobalized FM local searches are performed in multilevel style (not after each batch uncontraction)"
    )->capture_default_str();
    app.add_option(
      (initial_partitioning ? "--i-r-global-refine-until-no-improvement" : "--r-global-refine-until-no-improvement"),
      (!initial_partitioning ? context.refinement.global.refine_until_no_improvement :
        context.initial_partitioning.refinement.global.refine_until_no_improvement ),
      "Executes a globalized FM local search as long as it finds an improvement on the current partition."
    )->capture_default_str();
    app.add_option_function<std::string>(
      (initial_partitioning ? "--i-r-global-fm-type" : "--r-global-fm-type"), [&, initial_partitioning](const std::string& s) {
        if (initial_partitioning) {
          context.initial_partitioning.refinement.global.fm_algorithm = fmAlgorithmFromString(s);
        } else {
          context.refinement.global.fm_algorithm = fmAlgorithmFromString(s);
        }
      },
      "FM Algorithm for the global FM local search:\n"
      "- kway_fm\n"
      "- unconstrained_fm\n"
      "- do_nothing"
    )->capture_default_str();
    app.add_option(
      (initial_partitioning ? "--i-r-global-fm-seed-nodes" : "--r-global-fm-seed-nodes"),
      (!initial_partitioning ? context.refinement.global.fm_num_seed_nodes :
        context.initial_partitioning.refinement.global.fm_num_seed_nodes ),
      "Number of nodes to start FM with during the global FM local search."
    )->capture_default_str();
    app.add_option(
      (initial_partitioning ? "--i-r-global-fm-obey-minimal-parallelism" : "--r-global-fm-obey-minimal-parallelism"),
      (!initial_partitioning ? context.refinement.global.fm_obey_minimal_parallelism :
        context.initial_partitioning.refinement.global.fm_obey_minimal_parallelism ),
      "If true, then the global FM local search stops if more than a certain number of threads are finished."
    )->capture_default_str();
    app.add_option_function<std::string>(
      (initial_partitioning ? "--i-r-global-lp-type" : "--r-global-lp-type"), [&, initial_partitioning](const std::string& s) {
        if (initial_partitioning) {
          context.initial_partitioning.refinement.global.lp_algorithm = labelPropagationAlgorithmFromString(s);
        } else {
          context.refinement.global.lp_algorithm = labelPropagationAlgorithmFromString(s);
        }
      },
      "Label Propagation Algorithm for the global label propagation refinement:\n"
      "- label_propagation\n"
      "- deterministic\n"
      "- do_nothing"
    )->capture_default_str();
    app.add_option(
      (initial_partitioning ? "--i-r-global-lp-unconstrained" : "--r-global-lp-unconstrained"),
      (!initial_partitioning ? context.refinement.global.lp_unconstrained :
        context.initial_partitioning.refinement.global.lp_unconstrained ),
      "If true, then unconstrained LP is used for the global LP."
    )->capture_default_str();
    app.add_option_function<std::string>(
      (initial_partitioning ? "--i-r-rebalancer-type" : "--r-rebalancer-type"), [&, initial_partitioning](const std::string& s) {
        if (initial_partitioning) {
          context.initial_partitioning.refinement.rebalancing.algorithm = rebalancingAlgorithmFromString(s);
        } else {
          context.refinement.rebalancing.algorithm = rebalancingAlgorithmFromString(s);
        }
      },
      "Rebalancer Algorithm:\n"
      "- deterministic\n"
      "- advanced_rebalancer\n"
      "- do_nothing"
    )->capture_default_str();
    app.add_option(
      (initial_partitioning ? "--i-r-det-rebalancing-deadzone" : "--r-det-rebalancing-deadzone"),
      (!initial_partitioning ? context.refinement.rebalancing.det_relative_deadzone_size :
        context.initial_partitioning.refinement.rebalancing.det_relative_deadzone_size ),
       "Relative deadzone size for deterministic rebalancer"
    )->capture_default_str();
    app.add_option(
      (initial_partitioning ? "--i-r-det-rebalancing-heavy-vertex-exclusion" : "--r-det-rebalancing-heavy-vertex-exclusion"),
      (!initial_partitioning ? context.refinement.rebalancing.det_heavy_vertex_exclusion_factor :
        context.initial_partitioning.refinement.rebalancing.det_heavy_vertex_exclusion_factor ),
       "Relative weight threshold for heavy vertices which are ignored in deterministic rebalancing"
    )->capture_default_str();
    app.add_option(
      (initial_partitioning ? "--i-r-max-det-rebalancing-rounds" : "--r-max-det-rebalancing-rounds"),
      (!initial_partitioning ? context.refinement.rebalancing.det_max_rounds :
        context.initial_partitioning.refinement.rebalancing.det_max_rounds ),
       "Deterministic rebalancer: maximum number of iterations per rebalancing call (0 means unlimited)"
    )->capture_default_str();
  }

  void addFlowRefinementOptions(Context& context, CLI::App& app, const bool initial_partitioning) {
    app.option_defaults()->group(initial_partitioning ? "Refinement Options for Initial Partitioning" : "Refinement Options");
    app.add_option_function<std::string>(
      (initial_partitioning ? "--i-r-flow-algo" : "--r-flow-algo"), [&, initial_partitioning](const std::string& s) {
        if (initial_partitioning) {
          context.initial_partitioning.refinement.flows.algorithm = flowAlgorithmFromString(s);
        } else {
          context.refinement.flows.algorithm = flowAlgorithmFromString(s);
        }
      },
      "Flow Algorithm:\n"
      "- do_nothing\n"
      "- flow_cutter\n"
      "- deterministic"
    )->capture_default_str();
    app.add_option(
      (initial_partitioning ? "--i-r-flow-max-bfs-distance" : "--r-flow-max-bfs-distance"),
      (!initial_partitioning ? context.refinement.flows.max_bfs_distance :
        context.initial_partitioning.refinement.flows.max_bfs_distance ),
      "Flow problems are constructed via BFS search. The maximum BFS distance is the "
      "maximum distance from a cut hyperedge to any vertex of the problem."
    )->capture_default_str();
    app.add_option(
      (initial_partitioning ? "--i-r-flow-min-relative-improvement-per-round" : "--r-flow-min-relative-improvement-per-round"),
      (!initial_partitioning ? context.refinement.flows.min_relative_improvement_per_round :
        context.initial_partitioning.refinement.flows.min_relative_improvement_per_round ),
      "Minimum relative improvement per active block scheduling round. If the improvement is smaller "
      "then the flow algorithm terminates."
    )->capture_default_str();
    app.add_option(
      (initial_partitioning ? "--i-r-flow-time-limit-factor" : "--r-flow-time-limit-factor"),
      (!initial_partitioning ? context.refinement.flows.time_limit_factor :
        context.initial_partitioning.refinement.flows.time_limit_factor ),
      "The time limit for each flow problem is time_limit_factor * average running time of all previous searches."
    )->capture_default_str();
    app.add_option(
      (initial_partitioning ? "--i-r-flow-skip-small-cuts" : "--r-flow-skip-small-cuts"),
      (!initial_partitioning ? context.refinement.flows.skip_small_cuts :
        context.initial_partitioning.refinement.flows.skip_small_cuts ),
      "If true, than blocks with a cut <= 10 are not considered for refinement"
    )->capture_default_str();
    app.add_option(
      (initial_partitioning ? "--i-r-flow-skip-unpromising-blocks" : "--r-flow-skip-unpromising-blocks"),
      (!initial_partitioning ? context.refinement.flows.skip_unpromising_blocks :
        context.initial_partitioning.refinement.flows.skip_unpromising_blocks ),
      "If true, than blocks for which we never found an improvement are skipped"
    )->capture_default_str();
    app.add_option(
      (initial_partitioning ? "--i-r-flow-pierce-in-bulk" : "--r-flow-pierce-in-bulk"),
      (!initial_partitioning ? context.refinement.flows.pierce_in_bulk :
        context.initial_partitioning.refinement.flows.pierce_in_bulk ),
      "If true, then FlowCutter is accelerated by piercing multiple nodes at a time"
    )->capture_default_str();
    app.add_option(
      (initial_partitioning ? "--i-r-flow-scaling" : "--r-flow-scaling"),
      (!initial_partitioning ? context.refinement.flows.alpha :
        context.initial_partitioning.refinement.flows.alpha ),
      "Size constraint for flow problem: (1 + alpha * epsilon) * c(V) / k - c(V_1) (alpha = r-flow-scaling)"
    )->capture_default_str();
    app.add_option(
      (initial_partitioning ? "--i-r-flow-find-most-balanced-cut" : "--r-flow-find-most-balanced-cut"),
      (!initial_partitioning ? context.refinement.flows.find_most_balanced_cut :
        context.initial_partitioning.refinement.flows.find_most_balanced_cut ),
      "If true, than hyperflowcutter searches for the most balanced minimum cut."
    )->capture_default_str();
    app.add_option(
      (initial_partitioning ? "--i-r-flow-determine-distance-from-cut" : "--r-flow-determine-distance-from-cut"),
      (!initial_partitioning ? context.refinement.flows.determine_distance_from_cut :
        context.initial_partitioning.refinement.flows.determine_distance_from_cut ),
      "If true, than flow refiner determines distance of each node from cut which improves the piercing heuristic used in WHFC."
    )->capture_default_str();
    app.add_option(
      (initial_partitioning ? "--i-r-flow-max-num-pins" : "--r-flow-max-num-pins"),
      (!initial_partitioning ? context.refinement.flows.max_num_pins :
        context.initial_partitioning.refinement.flows.max_num_pins ),
      "Maximum number of pins a flow problem is allowed to contain"
    )->capture_default_str();
    app.add_option_function<std::string>(
      (initial_partitioning ? "--i-r-flow-process-mapping-policy" : "--r-flow-process-mapping-policy"), [&, initial_partitioning](const std::string& s) {
        if (initial_partitioning) {
          context.initial_partitioning.refinement.flows.steiner_tree_policy = steinerTreeFlowValuePolicyFromString(s);
        } else {
          context.refinement.flows.steiner_tree_policy = steinerTreeFlowValuePolicyFromString(s);
        }
      },
      "This option is only relevant for the Steiner tree metric. For flow-based refinement on hypergraphs, we cannot "
      "guarantee that the improvement found by solving the flow problem matches the exact improvement when we "
      "applied on the hypergraph. However, we can either guarantee that improvement is an lower or upper bound for "
      "the actual improvement. Therefore, the supported options are:\n"
      "- lower_bound\n"
      "- upper_bound"
    )->capture_default_str();
  }

  void addInitialPartitioningOptions(Context& context, CLI::App& app) {
    app.option_defaults()->group("Initial Partitioning Options");
    app.add_option_function<std::string>(
      "--i-mode", [&](const std::string& s) {
        context.initial_partitioning.mode = modeFromString(s);
      },
      "Mode of initial partitioning:\n"
      "- direct\n"
      "- deep\n"
      "- rb"
    )->capture_default_str();
    app.add_option_function<std::vector<std::string>>(
      "--i-enabled-ip-algos", [&](const std::vector<std::string>& list) {
        std::vector<bool>& enabled_ip_algos = context.initial_partitioning.enabled_ip_algos;
        enabled_ip_algos.assign(enabled_ip_algos.size(), false);
        for (const auto& name: list) {
          auto algo = initialPartitioningAlgorithmFromString(name);
          enabled_ip_algos.at(static_cast<size_t>(algo)) = true;
        }
      },
      "Indicate which IP algorithms should be executed, as a list of enabled algorithms:\n"
      "- greedy_round_robin_fm\n"
      "- greedy_global_fm\n"
      "- greedy_sequential_fm\n"
      "- random\n"
      "- bfs\n"
      "- label_propagation\n"
      "- greedy_round_robin_max_net\n"
      "- greedy_global_max_net\n"
      "- greedy_sequential_max_net\n"
      "For example, 'i-enabled-ip-algos=random bfs' enables the random and bfs algorithms."
    )->expected(1, 9)->capture_default_str();
    app.add_option(
      "--i-runs",
      context.initial_partitioning.runs,
     "Number of runs for each bipartitioning algorithm."
    )->capture_default_str();
    app.add_option(
      "--i-use-adaptive-ip-runs",
      context.initial_partitioning.use_adaptive_ip_runs,
      "If true, than each initial partitioner decides if it should further continue partitioning based on the "
      "quality produced by itself compared to the quality of the other partitioners. If it is not likely that the partitioner "
      "will produce a solution with a quality better than the current best, further runs of that partitioner are omitted."
    )->capture_default_str();
    app.add_option(
      "--i-min-adaptive-ip-runs",
      context.initial_partitioning.min_adaptive_ip_runs,
      "If adaptive IP runs is enabled, than each initial partitioner performs minimum min_adaptive_ip_runs runs before "
      "it decides if it should terminate."
    )->capture_default_str();
    app.add_option(
      "--i-population-size",
      context.initial_partitioning.population_size,
      "Size of population of flat bipartitions to perform secondary FM refinement on in deterministic mode."
      "Values < num threads are set to num threads. Does not affect behavior in non-deterministic mode."
    )->capture_default_str();
    app.add_option(
      "--i-perform-refinement-on-best-partitions",
      context.initial_partitioning.perform_refinement_on_best_partitions,
      "If true, then we perform an additional refinement on the best thread local partitions after IP."
    )->capture_default_str();
    app.add_option(
      "--i-fm-refinement-rounds",
      context.initial_partitioning.fm_refinment_rounds,
      "Maximum number of 2-way FM local searches on each bipartition produced by an initial partitioner."
    )->capture_default_str();
    app.add_option(
      "--i-remove-degree-zero-hns-before-ip",
      context.initial_partitioning.remove_degree_zero_hns_before_ip,
      "If true, degree-zero vertices are removed before initial partitioning."
    )->capture_default_str();
    app.add_option(
      "--i-lp-maximum-iterations",
      context.initial_partitioning.lp_maximum_iterations,
      "Maximum number of iterations of label propagation initial partitioner"
    )->capture_default_str();
    app.add_option(
      "--i-lp-initial-block-size",
      context.initial_partitioning.lp_initial_block_size,
      "Initial block size used for label propagation initial partitioner"
    )->capture_default_str();

    addRefinementOptions(context, app, true);
    addFlowRefinementOptions(context, app, true);
  }

  void addMappingOptions(Context& context, CLI::App& app) {
    app.option_defaults()->group("Mapping Options");
    app.add_option_function<std::string>(
      "--one-to-one-mapping-strategy", [&](const std::string& s) {
        context.mapping.strategy = oneToOneMappingStrategyFromString(s);
      },
      "Strategy for solving the one-to-one mapping problem after initial partitioning:\n"
      " - greedy_mapping\n"
      " - identity"
    )->capture_default_str();
    app.add_option(
      "--mapping-use-local-search",
      context.mapping.use_local_search,
      "If true, uses local search to improve the initial mapping."
    )->capture_default_str();
    app.add_option(
      "--mapping-use-two-phase-approach",
      context.mapping.use_two_phase_approach,
      "If true, then we first compute a k-way partition via optimizing the connectivity metric. "
      "Afterwards, each block of the partition is mapped onto a block of the target architecture graph."
    )->capture_default_str();
    app.add_option(
      "--mapping-max-steiner-tree-size",
      context.mapping.max_steiner_tree_size,
      "We precompute all optimal steiner trees up to this size in the target graph."
    )->capture_default_str();
    app.add_option(
      "--mapping-largest-he-fraction",
      context.mapping.largest_he_fraction,
      "If x% (x = process-mapping-largest-he-fraction) of the largest hyperedges covers more than y% of the pins "
      "(y = process-mapping-min-pin-coverage), then we ignore hyperedges larger than the x%-percentile in "
      "when counting adjacent blocks of a node."
    )->capture_default_str();
    app.add_option(
      "--mapping-min-pin-coverage",
      context.mapping.min_pin_coverage_of_largest_hes,
      "If x% (x = process-mapping-largest-he-fraction) of the largest hyperedges covers more than y% of the pins "
      "(y = process-mapping-min-pin-coverage), then we ignore hyperedges larger than the x%-percentile in "
      "when counting adjacent blocks of a node."
    )->capture_default_str();
  }

  void addSharedMemoryOptions(Context& context, CLI::App& app) {
    app.option_defaults()->group("Shared Memory Options");
    app.add_option(
      "--s-static-balancing-work-packages",
      context.shared_memory.static_balancing_work_packages,
      "Some sub-routines (sorting, shuffling) used in the deterministic presets employ static load balancing."
      "This parameter sets the number of work packages, in order to achieve deterministic results across different numbers of threads."
      "The default value is 128, and these sub-routines have little work, so there should rarely be a reason to change it. Max value is 256."
      "It does not affect the non-deterministic configs, unless you activate one of the deterministic algorithms."
    )->capture_default_str();
    app.add_option(
      "--s-use-localized-random-shuffle",
      context.shared_memory.use_localized_random_shuffle,
      "If true, localized parallel random shuffle is performed."
    )->capture_default_str();
    app.add_option(
      "--s-shuffle-block-size",
      context.shared_memory.shuffle_block_size,
      "If we perform a localized random shuffle in parallel, we perform a parallel for over blocks of size"
      "'shuffle_block_size' and shuffle them sequential."
    )->capture_default_str();
  }

  void addNonRequiredOptions(Context& context, CLI::App& app, CLI::Option* preset_option, bool detailed) {
    addUserOptions(context, app, preset_option, detailed);
    addDisplayOptions(context, app, detailed);
    if (detailed) {
      addGeneralOptions(context, app);
      addPreprocessingOptions(context, app);
      addCoarseningOptions(context, app);
      addInitialPartitioningOptions(context, app);
      addRefinementOptions(context, app, false);
      addFlowRefinementOptions(context, app, false);
      addMappingOptions(context, app);
      addSharedMemoryOptions(context, app);
    }
  }

  void printHelp(Context& context, bool verbose) {
    CLI::App app;

    auto preset_option = addRequiredOptions(context, app);
    addNonRequiredOptions(context, app, preset_option, verbose);

    if (!verbose) {
      app.footer("Run with '--help -v' to print an extensive list of available options.");
    }

    auto my_fmt = std::make_shared<MyFormatter>();
    app.formatter(my_fmt);

    std::cout << app.help();
  }

  void processCommandLineInput(Context& context, int argc, char *argv[]) {
    ALWAYS_ASSERT(!MT_KAHYPAR_IS_LIBRARY_MODE);

    std::string last_arg(argc > 0 ? argv[argc - 1] : "");
    if (argc <= 1 || last_arg == "-h") {
      printHelp(context, false);
      std::exit(0);
    }
    if (argc >= 2 && last_arg == "-v" && std::string(argv[argc - 2]) == "-h") {
      printHelp(context, true);
      std::exit(0);
    }

    CLI::App app;
    argv = app.ensure_utf8(argv);

    auto preset_option = addRequiredOptions(context, app);
    addNonRequiredOptions(context, app, preset_option, true);

    try {
      app.parse(argc, argv);
    } catch (const CLI::ParseError &e) {
      ERR(e.what());
    }

    std::string epsilon_str = std::to_string(context.partition.epsilon);
    epsilon_str.erase(epsilon_str.find_last_not_of('0') + 1, std::string::npos);

    if (context.partition.graph_partition_output_folder != "") {
      std::string graph_base_name = context.partition.graph_filename.substr(
              context.partition.graph_filename.find_last_of("/") + 1);
      context.partition.graph_partition_filename =
              context.partition.graph_partition_output_folder + "/" + graph_base_name;
    } else {
      context.partition.graph_partition_filename =
              context.partition.graph_filename;
    }
    context.partition.graph_partition_filename =
            context.partition.graph_partition_filename
            + ".part"
            + std::to_string(context.partition.k)
            + ".epsilon"
            + epsilon_str
            + ".seed"
            + std::to_string(context.partition.seed)
            + ".KaHyPar";
    context.partition.graph_community_filename =
            context.partition.graph_filename + ".community";
  }


  void parseIniToContext(Context& context, const std::string& ini_filename, bool disable_logging) {
    std::ifstream file(ini_filename.c_str());
    if (!file) {
      throw InvalidInputException(
        "Could not load context file at: " + ini_filename);
    }
    parseIniToContext(context, file, disable_logging);
  }

  void parseIniToContext(Context& context, std::istream& input, bool disable_logging) {
    if (disable_logging) {
      context.partition.enable_logging = false;
    }

    CLI::App app;
    app.add_option_function<std::string>(
      "--preset-type", [&](const std::string& s) {
        context.partition.preset_type = presetTypeFromString(s);
      },
      ""
    );
    addNonRequiredOptions(context, app, nullptr, true);
    app.allow_config_extras(false);
    try {
      app.parse_from_stream(input);
    } catch (const CLI::ParseError &e) {
      throw InvalidParameterException(e.what());
    }
  }


  void presetToContext(Context& context, PresetType preset, bool disable_logging) {
    if (disable_logging) {
      context.partition.enable_logging = false;
    }

    CLI::App app;
    app.add_option_function<std::string>(
      "--preset-type", [&](const std::string& s) {
        context.partition.preset_type = presetTypeFromString(s);
      },
      ""
    );
    addNonRequiredOptions(context, app, nullptr, true);
    app.parse(loadPreset(preset));
  }

}
