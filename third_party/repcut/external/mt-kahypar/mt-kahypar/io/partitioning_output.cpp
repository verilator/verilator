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

#include "partitioning_output.h"

#include <vector>

#include <tbb/blocked_range.h>
#include <tbb/parallel_invoke.h>
#include <tbb/parallel_sort.h>
#include <tbb/parallel_reduce.h>
#include <tbb/enumerable_thread_specific.h>

#include "mt-kahypar/definitions.h"
#include "mt-kahypar/parallel/memory_pool.h"
#include "mt-kahypar/parallel/atomic_wrapper.h"
#include "mt-kahypar/partition/metrics.h"
#include "mt-kahypar/partition/mapping/target_graph.h"
#include "mt-kahypar/utils/hypergraph_statistics.h"
#include "mt-kahypar/utils/memory_tree.h"
#include "mt-kahypar/utils/timer.h"
#include "mt-kahypar/utils/utilities.h"

#include "kahypar-resources/utils/math.h"


namespace mt_kahypar::io {
  namespace internal {
    struct Statistic {
      uint64_t min = 0;
      uint64_t q1 = 0;
      uint64_t med = 0;
      uint64_t q3 = 0;
      uint64_t max = 0;
      double avg = 0.0;
      double sd = 0.0;
    };

    template <typename T>
    Statistic createStats(const std::vector<T>& vec, const double avg, const double stdev) {
      internal::Statistic stats;
      if (!vec.empty()) {
        const auto quartiles = kahypar::math::firstAndThirdQuartile(vec);
        stats.min = vec.front();
        stats.q1 = quartiles.first;
        stats.med = kahypar::math::median(vec);
        stats.q3 = quartiles.second;
        stats.max = vec.back();
        stats.avg = avg;
        stats.sd = stdev;
      }
      return stats;
    }

    void printHypergraphStats(const Statistic& he_size_stats,
                              const Statistic& he_weight_stats,
                              const Statistic& hn_deg_stats,
                              const Statistic& hn_weight_stats) {
      // default double precision is 7
      const uint8_t double_width = 7;
      const uint8_t he_size_width = std::max(kahypar::math::digits(he_size_stats.max), double_width) + 4;
      const uint8_t he_weight_width = std::max(kahypar::math::digits(he_weight_stats.max), double_width) + 4;
      const uint8_t hn_deg_width = std::max(kahypar::math::digits(hn_deg_stats.max), double_width) + 4;
      const uint8_t hn_weight_width = std::max(kahypar::math::digits(hn_weight_stats.max), double_width) + 4;

      LOG << "HE size" << std::right << std::setw(he_size_width + 10)
          << "HE weight" << std::right << std::setw(he_weight_width + 8)
          << "HN degree" << std::right << std::setw(hn_deg_width + 8)
          << "HN weight";
      LOG << "| min=" << std::left << std::setw(he_size_width) << he_size_stats.min
          << " | min=" << std::left << std::setw(he_weight_width) << he_weight_stats.min
          << " | min=" << std::left << std::setw(hn_deg_width) << hn_deg_stats.min
          << " | min=" << std::left << std::setw(hn_weight_width) << hn_weight_stats.min;
      LOG << "| Q1 =" << std::left << std::setw(he_size_width) << he_size_stats.q1
          << " | Q1 =" << std::left << std::setw(he_weight_width) << he_weight_stats.q1
          << " | Q1 =" << std::left << std::setw(hn_deg_width) << hn_deg_stats.q1
          << " | Q1 =" << std::left << std::setw(hn_weight_width) << hn_weight_stats.q1;
      LOG << "| med=" << std::left << std::setw(he_size_width) << he_size_stats.med
          << " | med=" << std::left << std::setw(he_weight_width) << he_weight_stats.med
          << " | med=" << std::left << std::setw(hn_deg_width) << hn_deg_stats.med
          << " | med=" << std::left << std::setw(hn_weight_width) << hn_weight_stats.med;
      LOG << "| Q3 =" << std::left << std::setw(he_size_width) << he_size_stats.q3
          << " | Q3 =" << std::left << std::setw(he_weight_width) << he_weight_stats.q3
          << " | Q3 =" << std::left << std::setw(hn_deg_width) << hn_deg_stats.q3
          << " | Q3 =" << std::left << std::setw(hn_weight_width) << hn_weight_stats.q3;
      LOG << "| max=" << std::left << std::setw(he_size_width) << he_size_stats.max
          << " | max=" << std::left << std::setw(he_weight_width) << he_weight_stats.max
          << " | max=" << std::left << std::setw(hn_deg_width) << hn_deg_stats.max
          << " | max=" << std::left << std::setw(hn_weight_width) << hn_weight_stats.max;
      LOG << "| avg=" << std::left << std::setw(he_size_width) << he_size_stats.avg
          << " | avg=" << std::left << std::setw(he_weight_width) << he_weight_stats.avg
          << " | avg=" << std::left << std::setw(hn_deg_width) << hn_deg_stats.avg
          << " | avg=" << std::left << std::setw(hn_weight_width) << hn_weight_stats.avg;
      LOG << "| sd =" << std::left << std::setw(he_size_width) << he_size_stats.sd
          << " | sd =" << std::left << std::setw(he_weight_width) << he_weight_stats.sd
          << " | sd =" << std::left << std::setw(hn_deg_width) << hn_deg_stats.sd
          << " | sd =" << std::left << std::setw(hn_weight_width) << hn_weight_stats.sd;
    }

  }  // namespace internal

  template<typename Hypergraph>
  void printHypergraphInfo(const Hypergraph& hypergraph,
                           const Context& context,
                           const std::string& name,
                           const bool show_memory_consumption) {
    std::vector<HypernodeID> he_sizes;
    std::vector<HyperedgeWeight> he_weights;
    std::vector<HyperedgeID> hn_degrees;
    std::vector<HypernodeWeight> hn_weights;

    tbb::parallel_invoke([&] {
      he_sizes.resize(hypergraph.initialNumEdges());
    }, [&] {
      he_weights.resize(hypergraph.initialNumEdges());
    }, [&] {
      hn_degrees.resize(hypergraph.initialNumNodes());
    }, [&] {
      hn_weights.resize(hypergraph.initialNumNodes());
    });

    HypernodeID num_hypernodes = hypergraph.initialNumNodes();
    const double avg_hn_degree = utils::avgHypernodeDegree(hypergraph);
    hypergraph.doParallelForAllNodes([&](const HypernodeID& hn) {
      hn_degrees[hn] = hypergraph.nodeDegree(hn);
      hn_weights[hn] = hypergraph.nodeWeight(hn);
    });
    const double avg_hn_weight = utils::parallel_avg(hn_weights, num_hypernodes);
    const double stdev_hn_degree = utils::parallel_stdev(hn_degrees, avg_hn_degree, num_hypernodes);
    const double stdev_hn_weight = utils::parallel_stdev(hn_weights, avg_hn_weight, num_hypernodes);

    HyperedgeID num_hyperedges = hypergraph.initialNumEdges();
    HypernodeID num_pins = hypergraph.initialNumPins();
    const double avg_he_size = utils::avgHyperedgeDegree(hypergraph);
    hypergraph.doParallelForAllEdges([&](const HyperedgeID& he) {
      he_sizes[he] = hypergraph.edgeSize(he);
      he_weights[he] = hypergraph.edgeWeight(he);
    });
    const double avg_he_weight = utils::parallel_avg(he_weights, num_hyperedges);
    const double stdev_he_size = utils::parallel_stdev(he_sizes, avg_he_size, num_hyperedges);
    const double stdev_he_weight = utils::parallel_stdev(he_weights, avg_he_weight, num_hyperedges);

    tbb::enumerable_thread_specific<size_t> graph_edge_count(0);
    hypergraph.doParallelForAllEdges([&](const HyperedgeID& he) {
      if (hypergraph.edgeSize(he) == 2) {
        graph_edge_count.local() += 1;
      }
    });

    tbb::parallel_invoke([&] {
      tbb::parallel_sort(he_sizes.begin(), he_sizes.end());
    }, [&] {
      tbb::parallel_sort(he_weights.begin(), he_weights.end());
    }, [&] {
      tbb::parallel_sort(hn_degrees.begin(), hn_degrees.end());
    }, [&] {
      tbb::parallel_sort(hn_weights.begin(), hn_weights.end());
    });

    LOG << "Hypergraph Information";
    LOG << "Name :" << name;
    LOG << "# HNs:" << num_hypernodes
        << " # HEs:" << (Hypergraph::is_graph ? num_hyperedges / 2 : num_hyperedges)
        << " # pins:" << num_pins
        << " # graph edges:" << (Hypergraph::is_graph ? num_hyperedges / 2 : graph_edge_count.combine(std::plus<>()));

    internal::printHypergraphStats(
            internal::createStats(he_sizes, avg_he_size, stdev_he_size),
            internal::createStats(he_weights, avg_he_weight, stdev_he_weight),
            internal::createStats(hn_degrees, avg_hn_degree, stdev_hn_degree),
            internal::createStats(hn_weights, avg_hn_weight, stdev_hn_weight));

    if ( hypergraph.hasFixedVertices() ) {
      printFixedVertexPartWeights(hypergraph, context);
    }

    if ( show_memory_consumption ) {
      // Print Memory Consumption
      utils::MemoryTreeNode hypergraph_memory_consumption("Hypergraph", utils::OutputType::MEGABYTE);
      hypergraph.memoryConsumption(&hypergraph_memory_consumption);
      hypergraph_memory_consumption.finalize();
      LOG << "\nHypergraph Memory Consumption";
      LOG << hypergraph_memory_consumption;
    }
  }

  template<typename PartitionedHypergraph>
  void printPartWeightsAndSizes(const PartitionedHypergraph& hypergraph, const Context& context) {
    vec<HypernodeID> part_sizes(context.partition.k, 0);
    for (HypernodeID u : hypergraph.nodes()) {
      part_sizes[hypergraph.partID(u)]++;
    }
    PartitionID min_block = kInvalidPartition;
    HypernodeWeight min_part_weight = std::numeric_limits<HypernodeWeight>::max();
    HypernodeWeight avg_part_weight = 0;
    PartitionID max_block = kInvalidPartition;
    HypernodeWeight max_part_weight = 0;
    HypernodeID max_part_size = 0;
    size_t num_imbalanced_blocks = 0;
    for (PartitionID i = 0; i < context.partition.k; ++i) {
      avg_part_weight += hypergraph.partWeight(i);
      if ( hypergraph.partWeight(i) < min_part_weight ) {
        min_block = i;
        min_part_weight = hypergraph.partWeight(i);
      }
      if ( hypergraph.partWeight(i) > max_part_weight ) {
        max_block = i;
        max_part_weight = hypergraph.partWeight(i);
      }
      max_part_size = std::max(max_part_size, part_sizes[i]);
      num_imbalanced_blocks +=
        (hypergraph.partWeight(i) > context.partition.max_part_weights[i] ||
          ( !context.partition.allow_empty_blocks && hypergraph.partWeight(i) == 0 ));
    }
    avg_part_weight /= context.partition.k;

    const uint8_t part_digits = kahypar::math::digits(max_part_weight);
    const uint8_t k_digits = kahypar::math::digits(context.partition.k);
    if ( context.partition.k <= 32 ) {
      for (PartitionID i = 0; i != context.partition.k; ++i) {
        bool is_imbalanced =
                hypergraph.partWeight(i) > context.partition.max_part_weights[i] ||
                ( !context.partition.allow_empty_blocks && hypergraph.partWeight(i) == 0 );
        if ( is_imbalanced ) std::cout << RED;
        std::cout << "|block " << std::left  << std::setw(k_digits) << i
                  << std::setw(1) << "| = "  << std::right << std::setw(part_digits) << part_sizes[i]
                  << std::setw(1) << "  w( "  << std::right << std::setw(k_digits) << i
                  << std::setw(1) << " ) = "  << std::right << std::setw(part_digits) << hypergraph.partWeight(i)
                  << std::setw(1) << "  max( " << std::right << std::setw(k_digits) << i
                  << std::setw(1) << " ) = "  << std::right << std::setw(part_digits) << context.partition.max_part_weights[i]
                  << std::endl;
        if ( is_imbalanced ) std::cout << END;
      }
    } else {
      std::cout << "Avg Block Weight = " << avg_part_weight << std::endl;
      std::cout << "Min Block Weight = " << min_part_weight
                << (min_part_weight <= context.partition.max_part_weights[min_block] ? " <= " : " > ")
                << context.partition.max_part_weights[min_block]  << " (Block " << min_block << ")" << std::endl;
      std::cout << "Max Block Weight = " << max_part_weight
                << (max_part_weight <= context.partition.max_part_weights[max_block] ? " <= " : " > ")
                << context.partition.max_part_weights[max_block]  << " (Block " << max_block << ")" << std::endl;
      if ( num_imbalanced_blocks > 0 ) {
        LOG << RED << "Number of Imbalanced Blocks =" << num_imbalanced_blocks << END;
        for (PartitionID i = 0; i != context.partition.k; ++i) {
          const bool is_imbalanced =
            hypergraph.partWeight(i) > context.partition.max_part_weights[i] ||
            ( !context.partition.allow_empty_blocks && hypergraph.partWeight(i) == 0 );
          if ( is_imbalanced ) {
            std::cout << RED << "|block " << std::left  << std::setw(k_digits) << i
                      << std::setw(1) << "| = "  << std::right << std::setw(part_digits) << part_sizes[i]
                      << std::setw(1) << "  w( "  << std::right << std::setw(k_digits) << i
                      << std::setw(1) << " ) = "  << std::right << std::setw(part_digits) << hypergraph.partWeight(i)
                      << std::setw(1) << "  max( " << std::right << std::setw(k_digits) << i
                      << std::setw(1) << " ) = "  << std::right << std::setw(part_digits) << context.partition.max_part_weights[i]
                      << END << std::endl;
          }
        }
      }
    }
  }

  template<typename Hypergraph>
  void printFixedVertexPartWeights(const Hypergraph& hypergraph, const Context& context) {
    if ( context.partition.enable_logging && hypergraph.hasFixedVertices() ) {
      HypernodeWeight max_part_weight = 0;
      for (PartitionID i = 0; i < context.partition.k; ++i) {
        if ( hypergraph.fixedVertexBlockWeight(i) > max_part_weight ) {
          max_part_weight = hypergraph.fixedVertexBlockWeight(i);
        }
        if ( context.partition.max_part_weights[i] > max_part_weight ) {
          max_part_weight = context.partition.max_part_weights[i];
        }
      }

      const uint8_t part_digits = kahypar::math::digits(max_part_weight);
      const uint8_t k_digits = kahypar::math::digits(context.partition.k);
      LOG << BOLD << "\nHypergraph contains fixed vertices" << END;
      for (PartitionID i = 0; i != context.partition.k; ++i) {
        std::cout << "Fixed vertex weight of block " << std::left  << std::setw(k_digits) << i
                  << std::setw(1) << ": "
                  << std::setw(1) << "  w( "  << std::right << std::setw(k_digits) << i
                  << std::setw(1) << " ) = "  << std::right << std::setw(part_digits) << hypergraph.fixedVertexBlockWeight(i)
                  << std::setw(1) << "  max( " << std::right << std::setw(k_digits) << i
                  << std::setw(1) << " ) = "  << std::right << std::setw(part_digits) << context.partition.max_part_weights[i]
                  << std::endl;
      }
    }
  }

  template<typename PartitionedHypergraph>
  void printPartitioningResults(const PartitionedHypergraph& hypergraph,
                                const Context& context,
                                const std::string& description) {
    if (context.partition.enable_logging) {
      BalanceMetrics imbalance = metrics::imbalance(hypergraph, context);
      LOG << description;
      LOG << context.partition.objective << "      ="
          << metrics::quality(hypergraph, context);
      LOG << "imbalance =" << imbalance.imbalance_value;
      if (context.partition.verbose_logging) {
        LOG << "Part sizes and weights:";
        io::printPartWeightsAndSizes(hypergraph, context);
        LOG << "";
      }
    }
  }

  void printContext(const Context& context) {
    if (context.partition.enable_logging) {
      LOG << context;
    }
  }

  void printMemoryPoolConsumption(const Context& context) {
    if ( context.partition.enable_logging && context.partition.show_memory_consumption ) {
      utils::MemoryTreeNode memory_pool_consumption("Memory Pool", utils::OutputType::MEGABYTE);
      parallel::MemoryPool::instance().memory_consumption(&memory_pool_consumption);
      memory_pool_consumption.finalize();
      LOG << "\n Memory Pool Consumption:";
      LOG << memory_pool_consumption << "\n";
      parallel::MemoryPool::instance().explain_optimizations();
    }
  }

  template<typename Hypergraph>
  void printInputInformation(const Context& context, const Hypergraph& hypergraph) {
    if (context.partition.enable_logging) {
      LOG << "\n********************************************************************************";
      LOG << "*                                    Input                                     *";
      LOG << "********************************************************************************";
      io::printHypergraphInfo(hypergraph, context, context.partition.graph_filename.substr(
              context.partition.graph_filename.find_last_of('/') + 1),
                              context.partition.show_memory_consumption);
    }
  }

  void printTopLevelPreprocessingBanner(const Context& context) {
    if (context.partition.enable_logging) {
      LOG << "\n********************************************************************************";
      LOG << "*                              Preprocessing...                                *";
      LOG << "********************************************************************************";
    }
  }

  void printCoarseningBanner(const Context& context) {
    if (context.partition.enable_logging) {
      LOG << "********************************************************************************";
      LOG << "*                                Coarsening...                                 *";
      LOG << "********************************************************************************";
    }
  }

  void printInitialPartitioningBanner(const Context& context) {
    if (context.partition.enable_logging) {
      LOG << "\n********************************************************************************";
      LOG << "*                           Initial Partitioning...                            *";
      LOG << "********************************************************************************";
    }
  }

  void printLocalSearchBanner(const Context& context) {
    if (context.partition.enable_logging) {
      LOG << "\n********************************************************************************";
      LOG << "*                               Local Search...                                *";
      LOG << "********************************************************************************";
    }
  }

  void printVCycleBanner(const Context& context, const size_t vcycle_num) {
    if (context.partition.enable_logging) {
      LOG << "\n********************************************************************************";
      std::cout << "*                                  V-Cycle  " << vcycle_num;
      if ( vcycle_num < 10 ) {
        std::cout << "                                  *\n";
      } else {
        std::cout << "                                 *\n";
      }
      LOG << "********************************************************************************";
    }
  }
  void printDeepMultilevelBanner(const Context& context) {
    if (context.partition.enable_logging) {
      LOG << "\n********************************************************************************";
      LOG << "*                       Deep Multilevel Partitioning...                        *";
      LOG << "********************************************************************************";
    }
  }

  namespace {

  template<typename T, typename V>
  void printKeyValue(const T& key, const V& value, const std::string& details = "") {
    LOG << " " << std::left << std::setw(20) << key << "=" << value << details;
  }
  }

  template<typename PartitionedHypergraph>
  void printObjectives(const PartitionedHypergraph& hypergraph,
                       const Context& context,
                       const std::chrono::duration<double>& elapsed_seconds) {
    LOG << "Objectives:";
    printKeyValue(context.partition.objective, metrics::quality(hypergraph,
      context), "(primary objective function)");
    if ( context.partition.objective == Objective::steiner_tree ) {
      printKeyValue("Approximation Factor",
        metrics::approximationFactorForProcessMapping(hypergraph, context));
    }
    if ( context.partition.objective != Objective::cut ) {
      printKeyValue(Objective::cut, metrics::quality(hypergraph, Objective::cut));
    }
    if ( context.partition.objective != Objective::km1 && !PartitionedHypergraph::is_graph ) {
      printKeyValue(Objective::km1, metrics::quality(hypergraph, Objective::km1));
    }
    if ( context.partition.objective != Objective::soed && !PartitionedHypergraph::is_graph ) {
      printKeyValue(Objective::soed, metrics::quality(hypergraph, Objective::soed));
    }
    BalanceMetrics imbalance = metrics::imbalance(hypergraph, context);
    printKeyValue("Imbalance", imbalance.imbalance_value);
    if ( context.partition.verbose_logging && !context.partition.allow_empty_blocks ) {
      printKeyValue("Has Empty Blocks", imbalance.violates_non_empty_blocks ? "true" : "false");
    }
    printKeyValue("Partitioning Time", std::to_string(elapsed_seconds.count()) + " s");
  }

  using MCell = parallel::IntegralAtomicWrapper<HyperedgeWeight>;
  using MCol = std::vector<MCell>;

  void printMatrix(const std::vector<MCol>& matrix, PartitionID k) {
    ASSERT(matrix.size() == UL(k));

    HyperedgeWeight max_entry = 0;
    for ( PartitionID block_1 = 0; block_1 < k; ++block_1 ) {
      for ( PartitionID block_2 = block_1 + 1; block_2 < k; ++block_2 ) {
        max_entry = std::max(max_entry, matrix[block_1][block_2].load());
      }
    }

    // HEADER
    const uint8_t column_width = std::max(kahypar::math::digits(max_entry) + 2, 5);
    std::cout << std::right << std::setw(column_width) << "Block";
    for ( PartitionID block = 0; block < k; ++block ) {
      std::cout << std::right << std::setw(column_width) << block;
    }
    std::cout << std::endl;

    // CUT MATRIX
    for ( PartitionID block_1 = 0; block_1 < k; ++block_1 ) {
      std::cout << std::right << std::setw(column_width) << block_1;
      for ( PartitionID block_2 = 0; block_2 < k; ++block_2 ) {
        std::cout << std::right << std::setw(column_width) << matrix[block_1][block_2].load();
      }
      std::cout << std::endl;
    }
  }

  template<typename PartitionedHypergraph>
  void printCutMatrix(const PartitionedHypergraph& hypergraph) {
    const PartitionID k = hypergraph.k();

    using MCell = parallel::IntegralAtomicWrapper<HyperedgeWeight>;
    using MCol = std::vector<MCell>;
    std::vector<MCol> cut_matrix(k, MCol(k, MCell(0)));

    hypergraph.doParallelForAllEdges([&](const HyperedgeID& he) {
      if ( hypergraph.connectivity(he) > 1 ) {
        const HyperedgeWeight edge_weight = hypergraph.edgeWeight(he);
        for ( const PartitionID& block_1 : hypergraph.connectivitySet(he) ) {
          for ( const PartitionID& block_2 : hypergraph.connectivitySet(he) ) {
            if constexpr (PartitionedHypergraph::is_graph) {
              if (hypergraph.edgeSource(he) > hypergraph.edgeTarget(he)) {
                continue;
              }
            }
            if ( block_1 < block_2 ) {
              cut_matrix[block_1][block_2] += edge_weight;
            }
          }
        }
      }
    });

    printMatrix(cut_matrix, k);
  }


  template<typename PartitionedHypergraph>
  void printPotentialPositiveGainMoveMatrix(const PartitionedHypergraph& hypergraph) {
    const PartitionID k = hypergraph.k();

    using MCell = parallel::IntegralAtomicWrapper<HyperedgeWeight>;
    using MCol = std::vector<MCell>;
    std::vector<MCol> positive_gains(k, MCol(k, MCell(0)));

    tbb::enumerable_thread_specific<std::vector<Gain>> local_gain(k, 0);
    hypergraph.doParallelForAllNodes([&](const HypernodeID hn) {
      // Calculate gain to all blocks of the partition
      std::vector<Gain>& tmp_scores = local_gain.local();
      const PartitionID from = hypergraph.partID(hn);
      Gain internal_weight = 0;
      for (const HyperedgeID& he : hypergraph.incidentEdges(hn)) {
        HypernodeID pin_count_in_from_part = hypergraph.pinCountInPart(he, from);
        HyperedgeWeight he_weight = hypergraph.edgeWeight(he);

        if ( pin_count_in_from_part > 1 ) {
          internal_weight += he_weight;
        }

        for (const PartitionID& to : hypergraph.connectivitySet(he)) {
          if (from != to) {
            tmp_scores[to] -= he_weight;
          }
        }
      }

      for (PartitionID to = 0; to < k; ++to) {
        if (from != to) {
          Gain score = tmp_scores[to] + internal_weight;
          if ( score < 0 ) {
            positive_gains[from][to] += std::abs(score);
          }
        }
        tmp_scores[to] = 0;
      }
    });

    printMatrix(positive_gains, k);
  }

  template<typename PartitionedHypergraph>
  void printConnectedCutHyperedgeAnalysis(const PartitionedHypergraph& hypergraph) {
    std::vector<bool> visited_he(hypergraph.initialNumEdges(), false);
    std::vector<HyperedgeWeight> connected_cut_hyperedges;

    auto analyse_component = [&](const HyperedgeID he) {
      HyperedgeWeight component_weight = 0;
      std::vector<HyperedgeID> s;
      s.push_back(he);
      visited_he[hypergraph.uniqueEdgeID(he)] = true;

      while ( !s.empty() ) {
        const HyperedgeID e = s.back();
        s.pop_back();
        component_weight += hypergraph.edgeWeight(e);

        for ( const HypernodeID& pin : hypergraph.pins(e) ) {
          for ( const HyperedgeID& tmp_e : hypergraph.incidentEdges(pin) ) {
            if ( !visited_he[hypergraph.uniqueEdgeID(tmp_e)] && hypergraph.connectivity(tmp_e) > 1 ) {
              s.push_back(tmp_e);
              visited_he[hypergraph.uniqueEdgeID(tmp_e)] = true;
            }
          }
        }
      }

      return component_weight;
    };

    for ( const HyperedgeID& he : hypergraph.edges() ) {
      if ( hypergraph.connectivity(he) > 1 && !visited_he[hypergraph.uniqueEdgeID(he)] ) {
        connected_cut_hyperedges.push_back(analyse_component(he));
      }
    }
    std::sort(connected_cut_hyperedges.begin(), connected_cut_hyperedges.end());

    LOG << "Num Connected Cut Hyperedges =" << connected_cut_hyperedges.size();
    LOG << "Min Component Weight         =" << connected_cut_hyperedges[0];
    LOG << "Median Component Weight      =" << connected_cut_hyperedges[connected_cut_hyperedges.size() / 2];
    LOG << "Max Component Weight         =" << connected_cut_hyperedges.back();
    LOG << "Component Weight Vector:";
    std::cout << "(";
    for ( const HyperedgeWeight& weight : connected_cut_hyperedges ) {
      std::cout << weight << ",";
    }
    std::cout << "\b)" << std::endl;
  }

  template<typename PartitionedHypergraph>
  void printPartitioningResults(const PartitionedHypergraph& hypergraph,
                                const Context& context,
                                const std::chrono::duration<double>& elapsed_seconds) {
    if (context.partition.enable_logging) {
      LOG << "\n********************************************************************************";
      LOG << "*                             Partitioning Result                              *";
      LOG << "********************************************************************************";

      if ( context.partition.show_advanced_cut_analysis ) {
        LOG << "\nCut Matrix: ";
        printCutMatrix(hypergraph);

        LOG << "\nPotential Positive Gain Move Matrix: ";
        printPotentialPositiveGainMoveMatrix(hypergraph);

        LOG << "\nConnected Cut Hyperedge Analysis: ";
        printConnectedCutHyperedgeAnalysis(hypergraph);
      }

      printObjectives(hypergraph, context, elapsed_seconds);

      LOG << "\nPartition sizes and weights: ";
      printPartWeightsAndSizes(hypergraph, context);
      LOG << "";

      if ( context.partition.show_memory_consumption ) {
        // Print Memory Consumption
        utils::MemoryTreeNode hypergraph_memory_consumption(
          "Partitioned Hypergraph", utils::OutputType::MEGABYTE);
        hypergraph.memoryConsumption(&hypergraph_memory_consumption);
        hypergraph_memory_consumption.finalize();
        LOG << "Partitioned Hypergraph Memory Consumption";
        LOG << hypergraph_memory_consumption;
      }

      if ( hypergraph.hasTargetGraph() && TargetGraph::TRACK_STATS ) {
        hypergraph.targetGraph()->printStats();
      }

      if ( context.partition.verbose_logging || context.partition.show_detailed_timings ) {
        LOG << "Timings:";
        utils::Timer& timer = utils::Utilities::instance().getTimer(context.utility_id);
        timer.showDetailedTimings(context.partition.show_detailed_timings);
        timer.setMaximumOutputDepth(context.partition.timings_output_depth);
        LOG << timer;
      }
    }
  }

  void printStripe() {
    LOG << "--------------------------------------------------------------------------------";
  }

  void printBanner() {
    LOG << R"(+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++)";
    LOG << R"(+         __  __ _______       _  __     _    _       _____                   +)";
    LOG << R"(+        |  \/  |__   __|     | |/ /    | |  | |     |  __ \                  +)";
    LOG << R"(+        | \  / |  | |  ____  | ' / __ _| |__| |_   _| |__) |_ _ _ __         +)";
    LOG << R"(+        | |\/| |  | | |____| |  < / _` |  __  | | | |  ___/ _` | '__|        +)";
    LOG << R"(+        | |  | |  | |        | . \ (_| | |  | | |_| | |  | (_| | |           +)";
    LOG << R"(+        |_|  |_|  |_|        |_|\_\__,_|_|  |_|\__, |_|   \__,_|_|           +)";
    LOG << R"(+                                                __/ |                        +)";
    LOG << R"(+                                               |___/                         +)";
    LOG << R"(+          Karlsruhe Shared Memory Hypergraph Partitioning Framework          +)";
    LOG << R"(+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++)";
  }

  namespace internal {
    void printCommunityStats(const Statistic& community_size_stats,
                             const Statistic& community_pins_stats,
                             const Statistic& community_degree_stats) {
      // default double precision is 7
      const uint8_t double_width = 7;
      const uint8_t community_size_width = std::max(kahypar::math::digits(community_size_stats.max), double_width) + 4;
      const uint8_t community_pins_width = std::max(kahypar::math::digits(community_pins_stats.max), double_width) + 4;
      const uint8_t community_degree_width = std::max(kahypar::math::digits(community_degree_stats.max), double_width) + 4;

      LOG << "# HNs Per Community" << std::right << std::setw(community_size_width + 2)
          << "# Internal Pins" << std::right << std::setw(community_pins_width + 8 + 4)
          << "Internal Degree Sum" << std::right << std::setw(community_degree_width + 8);
      LOG << "| min=" << std::left << std::setw(community_size_width) << community_size_stats.min
          << " | min=" << std::left << std::setw(community_pins_width) << community_pins_stats.min
          << " | min=" << std::left << std::setw(community_degree_width) << community_degree_stats.min;
      LOG << "| Q1 =" << std::left << std::setw(community_size_width) << community_size_stats.q1
          << " | Q1 =" << std::left << std::setw(community_pins_width) << community_pins_stats.q1
          << " | Q1 =" << std::left << std::setw(community_degree_width) << community_degree_stats.q1;
      LOG << "| med=" << std::left << std::setw(community_size_width) << community_size_stats.med
          << " | med=" << std::left << std::setw(community_pins_width) << community_pins_stats.med
          << " | med=" << std::left << std::setw(community_degree_width) << community_degree_stats.med;
      LOG << "| Q3 =" << std::left << std::setw(community_size_width) << community_size_stats.q3
          << " | Q3 =" << std::left << std::setw(community_pins_width) << community_pins_stats.q3
          << " | Q3 =" << std::left << std::setw(community_degree_width) << community_degree_stats.q3;
      LOG << "| max=" << std::left << std::setw(community_size_width) << community_size_stats.max
          << " | max=" << std::left << std::setw(community_pins_width) << community_pins_stats.max
          << " | max=" << std::left << std::setw(community_degree_width) << community_degree_stats.max;
      LOG << "| avg=" << std::left << std::setw(community_size_width) << community_size_stats.avg
          << " | avg=" << std::left << std::setw(community_pins_width) << community_pins_stats.avg
          << " | avg=" << std::left << std::setw(community_degree_width) << community_degree_stats.avg;
      LOG << "| sd =" << std::left << std::setw(community_size_width) << community_size_stats.sd
          << " | sd =" << std::left << std::setw(community_pins_width) << community_pins_stats.sd
          << " | sd =" << std::left << std::setw(community_degree_width) << community_degree_stats.sd;
    }
  }

  template<typename Hypergraph>
  void printCommunityInformation(const Hypergraph& hypergraph, const Context& context) {
    if (context.partition.enable_logging) {
      PartitionID num_communities =
              tbb::parallel_reduce(
                      tbb::blocked_range<HypernodeID>(ID(0), hypergraph.initialNumNodes()),
                      0, [&](const tbb::blocked_range<HypernodeID>& range, PartitionID init) {
                PartitionID my_range_num_communities = init;
                for (HypernodeID hn = range.begin(); hn < range.end(); ++hn) {
                  if ( hypergraph.nodeIsEnabled(hn) ) {
                    my_range_num_communities = std::max(my_range_num_communities, hypergraph.communityID(hn) + 1);
                  }
                }
                return my_range_num_communities;
              },
              [](const PartitionID lhs, const PartitionID rhs) {
                return std::max(lhs, rhs);
              });
      num_communities = std::max(num_communities, 1);

      LOG << "# Communities:" << num_communities;

      if (context.partition.verbose_logging) {
        std::vector<size_t> nodes_per_community(num_communities, 0);
        std::vector<size_t> internal_pins(num_communities, 0);
        std::vector<size_t> internal_degree(num_communities, 0);

        auto reduce_nodes = [&] {
          tbb::enumerable_thread_specific< vec< std::pair<size_t, size_t> > > ets_nodes(num_communities, std::make_pair(UL(0), UL(0)));
          hypergraph.doParallelForAllNodes([&](const HypernodeID u) {
            const PartitionID cu = hypergraph.communityID(u);
            ets_nodes.local()[cu].first++;
            ets_nodes.local()[cu].second += hypergraph.nodeDegree(u);
          });

          for (const auto& x : ets_nodes) {
            for (PartitionID i = 0; i < num_communities; ++i) {
              nodes_per_community[i] += x[i].first;
              internal_degree[i] += x[i].second;
            }
          }
        };

        auto reduce_hyperedges = [&] {
          tbb::enumerable_thread_specific< vec<size_t> > ets_pins(num_communities, 0);
          hypergraph.doParallelForAllEdges([&](const HyperedgeID he) {
            auto& pin_counter = ets_pins.local();
            for (const HypernodeID pin : hypergraph.pins(he)) {
              pin_counter[ hypergraph.communityID(pin) ]++;
            }
          });

          for (const auto& x : ets_pins) {
            for (PartitionID i = 0; i < num_communities; ++i) {
              internal_pins[i] += x[i];
            }
          }
        };

        tbb::parallel_invoke(reduce_nodes, reduce_hyperedges);

        std::sort(nodes_per_community.begin(), nodes_per_community.end());
        std::sort(internal_pins.begin(), internal_pins.end());
        std::sort(internal_degree.begin(), internal_degree.end());

        auto square = [&](double x) { return x * x; };

        auto avg_and_std_dev = [&](const std::vector<size_t>& v) {
          const double avg = std::accumulate(v.begin(), v.end(), 0.0) / static_cast<double>(v.size());
          double std_dev = 0.0;
          for (size_t x : v) {
            std_dev += square(x - avg);
          }
          std_dev = std::sqrt(std_dev / static_cast<double>(v.size() - 1));
          return std::make_pair(avg, std_dev);
        };

        auto [avg_nodes, std_dev_nodes] = avg_and_std_dev(nodes_per_community);
        auto [avg_pins, std_dev_pins] = avg_and_std_dev(internal_pins);
        auto [avg_deg, std_dev_deg] = avg_and_std_dev(internal_degree);;

        internal::printCommunityStats(
                internal::createStats(nodes_per_community, avg_nodes, std_dev_nodes),
                internal::createStats(internal_pins, avg_pins, std_dev_pins),
                internal::createStats(internal_degree, avg_deg, std_dev_deg)
                );
      }

      LOG << "";
    }
  }

  namespace {
    #define PRINT_CUT_MATRIX(X) void printCutMatrix(const X& hypergraph)
    #define PRINT_HYPERGRAPH_INFO(X) void printHypergraphInfo(const X& hypergraph,                 \
                                                              const Context& context,              \
                                                              const std::string& name,             \
                                                              const bool show_memory_consumption)
    #define PRINT_PARTITIONING_RESULTS(X) void printPartitioningResults(const X& hypergraph,             \
                                                                        const Context& context,          \
                                                                        const std::string& description)
    #define PRINT_PARTITIONING_RESULTS_2(X) void printPartitioningResults(const X& hypergraph,                                   \
                                                                          const Context& context,                                \
                                                                          const std::chrono::duration<double>& elapsed_seconds)
    #define PRINT_PART_WEIGHT_AND_SIZES(X) void printPartWeightsAndSizes(const X& hypergraph, const Context& context)
    #define PRINT_FIXED_VERTEX_PART_WEIGHTS(X) void printFixedVertexPartWeights(const X& hypergraph, const Context& context)
    #define PRINT_INPUT_INFORMATION(X) void printInputInformation(const Context& context, const X& hypergraph)
    #define PRINT_COMMUNITY_INFORMATION(X) void printCommunityInformation(const X& hypergraph, const Context& context)
  } // namespace

  INSTANTIATE_FUNC_WITH_HYPERGRAPHS(PRINT_HYPERGRAPH_INFO)
  INSTANTIATE_FUNC_WITH_HYPERGRAPHS(PRINT_INPUT_INFORMATION)
  INSTANTIATE_FUNC_WITH_HYPERGRAPHS(PRINT_COMMUNITY_INFORMATION)
  INSTANTIATE_FUNC_WITH_HYPERGRAPHS(PRINT_FIXED_VERTEX_PART_WEIGHTS)
  INSTANTIATE_FUNC_WITH_PARTITIONED_HG(PRINT_CUT_MATRIX)
  INSTANTIATE_FUNC_WITH_PARTITIONED_HG(PRINT_PARTITIONING_RESULTS)
  INSTANTIATE_FUNC_WITH_PARTITIONED_HG(PRINT_PARTITIONING_RESULTS_2)
  INSTANTIATE_FUNC_WITH_PARTITIONED_HG(PRINT_PART_WEIGHT_AND_SIZES)
} // namespace mt_kahypar::io