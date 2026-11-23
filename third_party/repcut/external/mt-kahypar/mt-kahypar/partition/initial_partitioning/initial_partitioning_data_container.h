/*******************************************************************************
 * MIT License
 *
 * This file is part of Mt-KaHyPar.
 *
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

#include <sstream>

#include <tbb/enumerable_thread_specific.h>

#include "mt-kahypar/partition/initial_partitioning/initial_partitioning_commons.h"

#include "mt-kahypar/partition/context.h"
#include "mt-kahypar/partition/metrics.h"
#include "mt-kahypar/partition/factories.h"
#include "mt-kahypar/parallel/stl/scalable_vector.h"
#include "mt-kahypar/utils/cast.h"
#include "mt-kahypar/utils/utilities.h"
#include "mt-kahypar/utils/range.h"
#include "mt-kahypar/partition/refinement/fm/sequential_twoway_fm_refiner.h"
#include "mt-kahypar/partition/refinement/gains/gain_cache_ptr.h"


namespace mt_kahypar {

template<typename TypeTraits>
class InitialPartitioningDataContainer {

  static constexpr bool debug = false;
  static constexpr bool enable_heavy_assert = false;

  using Hypergraph = typename TypeTraits::Hypergraph;
  using PartitionedHypergraph = typename TypeTraits::PartitionedHypergraph;

  // ! Contains information about the best thread local partition
  struct PartitioningResult {
    PartitioningResult() = default;

    PartitioningResult(InitialPartitioningAlgorithm algorithm,
                       HyperedgeWeight objective_ip,
                       HyperedgeWeight objective,
                       BalanceMetrics imbalance) :
      _algorithm(algorithm),
      _objective_ip(objective_ip),
      _objective(objective),
      _imbalance(imbalance) { }

    bool is_other_better(const PartitioningResult& other) const {
      Metrics my_metric{_objective, _imbalance};
      Metrics other_metric{other._objective, other._imbalance};
      return other_metric.isBetter(my_metric) ||
             ( other_metric.isEqual(my_metric)     // tie breaking for deterministic mode
                && std::tie(other._random_tag, other._deterministic_tag) < std::tie(_random_tag, _deterministic_tag) );
    }

    std::string str() const {
      std::stringstream ss;
      ss << "Algorithm = " << _algorithm << ", "
         << "Objective IP = " << _objective_ip << ", "
         << "Objective = " << _objective << ", "
         << "Imbalance = " << _imbalance;
      return ss.str();
    }

    InitialPartitioningAlgorithm _algorithm = InitialPartitioningAlgorithm::UNDEFINED;
    HyperedgeWeight _objective_ip = std::numeric_limits<HyperedgeWeight>::max();
    HyperedgeWeight _objective = std::numeric_limits<HyperedgeWeight>::max();
    BalanceMetrics _imbalance;
    size_t _random_tag = std::numeric_limits<size_t>::max();
    size_t _deterministic_tag = std::numeric_limits<size_t>::max();
  };

  // ! Aggregates global stats about the partitions produced by an specific
  // ! initial partitioning algorithm.
  struct InitialPartitioningRunStats {
    explicit InitialPartitioningRunStats(InitialPartitioningAlgorithm algo) :
      algorithm(algo),
      average_quality(0.0),
      sum_of_squares(0.0),
      n(0),
      best_quality(std::numeric_limits<HyperedgeWeight>::max()) { }

    void add_run(const HyperedgeWeight quality) {
      ++n;
      // Incremental update standard deviation
      // Incremental update average quality
      const double old_average_quality = average_quality;
      average_quality += static_cast<double>(quality - average_quality) / n;
      sum_of_squares +=
        static_cast<long double>(quality - old_average_quality) *
        static_cast<long double>(quality - average_quality);
      if ( quality < best_quality ) {
        best_quality = quality;
      }
    }

    double stddev() const {
      return n == 1 ? 0 : std::sqrt(sum_of_squares / ( n - 1 ));
    }

    InitialPartitioningAlgorithm algorithm;
    double average_quality;
    long double sum_of_squares;
    size_t n;
    HyperedgeWeight best_quality;
  };

  // ! Aggregates global stats of all initial partitioning algorithms.
  // ! Additionally it provides a function that decides whether it is
  // ! beneficial to perform additional runs of a specific initial
  // ! partitioning algorithm based on its previous runs (see
  // ! should_initial_partitioner_run(...)).
  struct GlobalInitialPartitioningStats {

    explicit GlobalInitialPartitioningStats(const Context& context) :
      _context(context),
      _stats(),
      _best_quality(std::numeric_limits<HyperedgeWeight>::max()) {
      const uint8_t num_initial_partitioner = static_cast<uint8_t>(InitialPartitioningAlgorithm::UNDEFINED);
      for ( uint8_t algo = 0; algo < num_initial_partitioner; ++algo ) {
        _stats.emplace_back(static_cast<InitialPartitioningAlgorithm>(algo));
      }
    }

    void add_run(const InitialPartitioningAlgorithm algorithm,
                 const HyperedgeWeight quality,
                 const bool is_feasible) {
      const uint8_t algo_idx = static_cast<uint8_t>(algorithm);
      _stats[algo_idx].add_run(quality);
      if ( is_feasible && quality < _best_quality ) {
        _best_quality = quality;
      }
    }

    // ! Decides whether it is beneficial to perform further runs of a specific
    // ! initial partitioning algorithm. Function assumes that the quality produced
    // ! by a partitioner follows a normal distribution. In that case, approx. 95%
    // ! of the partitions produced by an initial partitioner have a quality between
    // ! avg_quality - 2 * stddev_quality and avg_quality + 2 * stddev_quality. If
    // ! avg_quality - 2 * stddev_quality is greater than the best partition produced
    // ! so far then we say that the probability that the corresponding initial
    // ! partitioner produce a new global best partition is too low and prohibit further
    // ! runs of that partitioner.
    bool should_initial_partitioner_run(const InitialPartitioningAlgorithm algorithm) const {
      return _context.partition.deterministic || should_initial_partitioner_run_ignoring_deterministic(algorithm);
    }

    bool should_initial_partitioner_run_ignoring_deterministic(const InitialPartitioningAlgorithm algorithm) const {
      const uint8_t algo_idx = static_cast<uint8_t>(algorithm);
      return !_context.initial_partitioning.use_adaptive_ip_runs ||
             _stats[algo_idx].n < _context.initial_partitioning.min_adaptive_ip_runs ||
             _stats[algo_idx].average_quality - 2.0 * _stats[algo_idx].stddev() <= _best_quality;
    }

    const Context& _context;
    parallel::scalable_vector<InitialPartitioningRunStats> _stats;
    HyperedgeWeight _best_quality;
  };

  struct LocalInitialPartitioningHypergraph {

    LocalInitialPartitioningHypergraph(Hypergraph& hypergraph,
                                       const Context& context,
                                       GlobalInitialPartitioningStats& global_stats,
                                       const bool disable_fm) :
      _partitioned_hypergraph(context.partition.k, hypergraph),
      _context(context),
      _global_stats(global_stats),
      _partition(hypergraph.initialNumNodes(), kInvalidPartition),
      _result(InitialPartitioningAlgorithm::UNDEFINED,
              std::numeric_limits<HyperedgeWeight>::max(),
              std::numeric_limits<HyperedgeWeight>::max(),
              BalanceMetrics()),
      _gain_cache(GainCachePtr::constructGainCache(context)),
      _rebalancer(nullptr),
      _label_propagation(nullptr),
      _twoway_fm(nullptr),
      _stats() {

      for ( uint8_t algo = 0; algo < static_cast<size_t>(InitialPartitioningAlgorithm::UNDEFINED); ++algo ) {
        _stats.emplace_back(static_cast<InitialPartitioningAlgorithm>(algo));
      }

      if ( _context.partition.k == 2 && !disable_fm ) {
        // In case of a bisection we instantiate the 2-way FM refiner
        _twoway_fm = std::make_unique<SequentialTwoWayFmRefiner<TypeTraits>>(_partitioned_hypergraph, _context);
      } else if ( _context.refinement.label_propagation.algorithm != LabelPropagationAlgorithm::do_nothing ) {
        // In case of a direct-kway initial partition we instantiate the LP refiner
        _rebalancer = RebalancerFactory::getInstance().createObject(
          _context.refinement.rebalancing.algorithm, hypergraph.initialNumNodes(), _context, _gain_cache);
        _label_propagation = LabelPropagationFactory::getInstance().createObject(
          _context.refinement.label_propagation.algorithm,
          hypergraph.initialNumNodes(), hypergraph.initialNumEdges(), _context, _gain_cache, *_rebalancer);
      }
    }

    ~LocalInitialPartitioningHypergraph() {
        GainCachePtr::deleteGainCache(_gain_cache);
    }

    PartitioningResult refineAndUpdateStats(const InitialPartitioningAlgorithm algorithm, std::mt19937& prng,
                                            const double time = 0.0) {
      ASSERT([&]() {
          for (const HypernodeID& hn : _partitioned_hypergraph.nodes()) {
            if (_partitioned_hypergraph.partID(hn) == kInvalidPartition) {
              return false;
            }
          }
          return true;
        } (), "There are unassigned hypernodes!");

      Metrics current_metric;
      current_metric.quality = metrics::quality(_partitioned_hypergraph, _context, false);
      current_metric.imbalance = metrics::imbalance(_partitioned_hypergraph, _context);

      const HyperedgeWeight quality_before_refinement = current_metric.quality;

      refineCurrentPartition(current_metric, prng);

      PartitioningResult result(algorithm, quality_before_refinement,
        current_metric.quality, current_metric.imbalance);

      // Aggregate Stats
      auto algorithm_index = static_cast<uint8_t>(algorithm);
      _stats[algorithm_index].total_sum_quality += result._objective;
      _stats[algorithm_index].total_time += time;
      ++_stats[algorithm_index].total_calls;

      _global_stats.add_run(algorithm, current_metric.quality,
        current_metric.imbalance.isValidPartition());

      return result;
    }

    PartitioningResult performRefinementOnPartition(vec<PartitionID>& partition,
                                                    PartitioningResult& input, std::mt19937& prng) {
      Metrics current_metric = { input._objective, input._imbalance };

      _partitioned_hypergraph.resetPartition();

      // Apply input partition to hypergraph
      for ( const HypernodeID& hn : _partitioned_hypergraph.nodes() ) {
        ASSERT(hn < partition.size());
        ASSERT(_partitioned_hypergraph.partID(hn) == kInvalidPartition);
        _partitioned_hypergraph.setNodePart(hn, partition[hn]);
      }

      HEAVY_INITIAL_PARTITIONING_ASSERT(
        current_metric.quality == metrics::quality(_partitioned_hypergraph, _context, false));

      refineCurrentPartition(current_metric, prng);

      PartitioningResult result(_result._algorithm,
        current_metric.quality, current_metric.quality,
        current_metric.imbalance);

      return result;
    }

    void performRefinementOnBestPartition(int seed) {
      std::mt19937 prng(seed);
      auto refined = performRefinementOnPartition(_partition, _result, prng);

      // Compare current best partition with refined partition
      if ( _result.is_other_better(refined) ) {
        for ( const HypernodeID& hn : _partitioned_hypergraph.nodes() ) {
          const PartitionID part_id = _partitioned_hypergraph.partID(hn);
          ASSERT(hn < _partition.size());
          ASSERT(part_id != kInvalidPartition);
          _partition[hn] = part_id;
        }
        _result = refined;
      }
    }

    void copyPartition(vec<PartitionID>& partition_store) const {
      for (HypernodeID node : _partitioned_hypergraph.nodes()) {
        ASSERT(_partitioned_hypergraph.partID(node) != kInvalidPartition);
        partition_store[node] = _partitioned_hypergraph.partID(node);
      }
    }

    void refineCurrentPartition(Metrics& current_metric, std::mt19937& prng) {
      if ( _context.partition.k == 2 && _twoway_fm ) {
        bool improvement = true;
        for ( size_t i = 0; i < _context.initial_partitioning.fm_refinment_rounds && improvement; ++i ) {
          improvement = _twoway_fm->refine(current_metric, prng);
        }
      } else if ( _label_propagation ) {
        mt_kahypar_partitioned_hypergraph_t phg =
          utils::partitioned_hg_cast(_partitioned_hypergraph);
        _label_propagation->initialize(phg);
        _label_propagation->refine(phg, {}, current_metric,
          std::numeric_limits<double>::max());
      }

      HEAVY_INITIAL_PARTITIONING_ASSERT(
        current_metric.quality == metrics::quality(_partitioned_hypergraph, _context, false));
    }

    void aggregate_stats(parallel::scalable_vector<utils::InitialPartitionerSummary>& main_stats) const {
      ASSERT(main_stats.size() == _stats.size());
      for ( size_t i = 0; i < _stats.size(); ++i ) {
        main_stats[i].add(_stats[i]);
      }
    }

    void freeInternalData() {
      tbb::parallel_invoke([&] {
        _partitioned_hypergraph.freeInternalData();
      }, [&] {
        parallel::free(_partition);
      });
    }

    PartitionedHypergraph _partitioned_hypergraph;
    const Context& _context;
    GlobalInitialPartitioningStats& _global_stats;
    parallel::scalable_vector<PartitionID> _partition;
    PartitioningResult _result;
    gain_cache_t _gain_cache;
    std::unique_ptr<IRebalancer> _rebalancer;
    std::unique_ptr<IRefiner> _label_propagation;
    std::unique_ptr<SequentialTwoWayFmRefiner<TypeTraits>> _twoway_fm;
    parallel::scalable_vector<utils::InitialPartitionerSummary> _stats;
  };

  using ThreadLocalHypergraph = tbb::enumerable_thread_specific<LocalInitialPartitioningHypergraph>;
  using ThreadLocalUnassignedHypernodes = tbb::enumerable_thread_specific<parallel::scalable_vector<HypernodeID>>;
  using FixedVertexIterator = typename vec<HypernodeID>::const_iterator;

 public:
  InitialPartitioningDataContainer(PartitionedHypergraph& hypergraph,
                                    const Context& context,
                                    const bool disable_fm = false) :
    _partitioned_hg(hypergraph),
    _context(context),
    _disable_fm(disable_fm),
    _global_stats(context),
    _local_hg([&] {
      return construct_local_partitioned_hypergraph();
    }),
    _local_kway_pq(_context.partition.k),
    _is_local_pq_initialized(false),
    _local_hn_visited(_context.partition.k * hypergraph.initialNumNodes()),
    _local_he_visited(_context.partition.k * hypergraph.initialNumEdges()),
    _local_unassigned_hypernodes(),
    _local_unassigned_hypernode_pointer(std::numeric_limits<size_t>::max()),
    _fixed_vertices(),
    _max_pop_size(_context.initial_partitioning.population_size)  {
    // Setup Label Propagation IRefiner Config for Initial Partitioning
    _context.refinement = _context.initial_partitioning.refinement;
    _context.refinement.label_propagation.execute_sequential = true;

    if (_context.partition.deterministic) {
      _best_partitions.resize(_max_pop_size);
      for (size_t i = 0; i < _max_pop_size; ++i) {
        _best_partitions[i].second.resize(hypergraph.initialNumNodes(), kInvalidPartition);
      }
    }

    if ( _partitioned_hg.hasFixedVertices() ) {
      for ( const HypernodeID& hn : _partitioned_hg.nodes() ) {
        if ( _partitioned_hg.isFixed(hn) ) {
          _fixed_vertices.push_back(hn);
        }
      }
    }
  }

  InitialPartitioningDataContainer(const InitialPartitioningDataContainer&) = delete;
  InitialPartitioningDataContainer & operator= (const InitialPartitioningDataContainer &) = delete;

  InitialPartitioningDataContainer(InitialPartitioningDataContainer&&) = delete;
  InitialPartitioningDataContainer & operator= (InitialPartitioningDataContainer &&) = delete;

  ~InitialPartitioningDataContainer() {
    tbb::parallel_invoke([&] {
      parallel::parallel_free_thread_local_internal_data(
        _local_hg, [&](LocalInitialPartitioningHypergraph& local_hg) {
          local_hg.freeInternalData();
        });
    }, [&] {
      parallel::parallel_free_thread_local_internal_data(
        _local_unassigned_hypernodes, [&](parallel::scalable_vector<HypernodeID>& array) {
          parallel::free(array);
        });
    });
  }

  PartitionedHypergraph& local_partitioned_hypergraph() {
    return _local_hg.local()._partitioned_hypergraph;
  }

  KWayPriorityQueue& local_kway_priority_queue() {
    bool& is_local_pq_initialized = _is_local_pq_initialized.local();
    KWayPriorityQueue& local_kway_pq = _local_kway_pq.local();
    if ( !is_local_pq_initialized ) {
      local_kway_pq.initialize(local_partitioned_hypergraph().initialNumNodes());
      is_local_pq_initialized = true;
    }
    return local_kway_pq;
  }

  kahypar::ds::FastResetFlagArray<>& local_hypernode_fast_reset_flag_array() {
    return _local_hn_visited.local();
  }

  kahypar::ds::FastResetFlagArray<>& local_hyperedge_fast_reset_flag_array() {
    return _local_he_visited.local();
  }

  void reset_unassigned_hypernodes(std::mt19937& prng) {
    vec<HypernodeID>& unassigned_hypernodes = _local_unassigned_hypernodes.local();
    size_t& unassigned_hypernode_pointer = _local_unassigned_hypernode_pointer.local();
    if ( unassigned_hypernode_pointer == std::numeric_limits<size_t>::max() || _context.partition.deterministic ) {
      if ( _context.partition.deterministic ) {
        unassigned_hypernodes.clear();
      }
      // In case the local unassigned hypernode vector was not initialized before
      // we initialize it here
      const PartitionedHypergraph& hypergraph = local_partitioned_hypergraph();
      for ( const HypernodeID& hn : hypergraph.nodes() ) {
        if ( !hypergraph.isFixed(hn) ) {
          unassigned_hypernodes.push_back(hn);
        }
      }
      std::shuffle(unassigned_hypernodes.begin(), unassigned_hypernodes.end(), prng);
    }
    unassigned_hypernode_pointer = unassigned_hypernodes.size();
  }

  HypernodeID get_unassigned_hypernode(const PartitionID unassigned_block = kInvalidPartition) {
    const PartitionedHypergraph& hypergraph = local_partitioned_hypergraph();
    parallel::scalable_vector<HypernodeID>& unassigned_hypernodes =
      _local_unassigned_hypernodes.local();
    size_t& unassigned_hypernode_pointer = _local_unassigned_hypernode_pointer.local();
    ASSERT(!unassigned_hypernodes.empty());
    ASSERT(unassigned_hypernode_pointer <= unassigned_hypernodes.size());

    while ( unassigned_hypernode_pointer > 0 ) {
      const HypernodeID current_hn = unassigned_hypernodes[0];
      // In case the current hypernode is unassigned we return it
      if ( hypergraph.partID(current_hn) == unassigned_block &&
           !hypergraph.isFixed(current_hn) ) {
        return current_hn;
      }
      // In case the hypernode on the first position is already assigned,
      // we swap it to end of the unassigned hypernode vector and decrement
      // the pointer such that we will not visit it again
      std::swap(unassigned_hypernodes[0], unassigned_hypernodes[--unassigned_hypernode_pointer]);
    }
    return kInvalidHypernode;
  }

  bool should_initial_partitioner_run(const InitialPartitioningAlgorithm algorithm) {
    return _global_stats.should_initial_partitioner_run(algorithm);
  }

  /*!
   * Commits the current partition computed on the local hypergraph. Partition replaces
   * the best local partition, if it has a better quality (or better imbalance).
   * Partition on the local hypergraph is resetted afterwards.
   */
  void commit(const InitialPartitioningAlgorithm algorithm, std::mt19937& prng, size_t deterministic_tag,
              const double time = 0.0) {
    // already commits the result if non-deterministic
    auto& my_ip_data = _local_hg.local();
    auto my_result = my_ip_data.refineAndUpdateStats(algorithm, prng, time);

    if ( _context.partition.deterministic ) {
      // apply result to shared pool
      my_result._random_tag = prng();   // this is deterministic since we call the prng owned exclusively by the flat IP algo object
      my_result._deterministic_tag = deterministic_tag;
      PartitioningResult worst_in_population = _best_partitions[0].first;
      if (worst_in_population.is_other_better(my_result)) {
        _pop_lock.lock();
        worst_in_population = _best_partitions[0].first;
        if (worst_in_population.is_other_better(my_result)) {
          // remove current worst and replace with my result
          my_ip_data.copyPartition(_best_partitions[0].second);
          auto comp = [&](const auto& l, const auto& r) { return r.first.is_other_better(l.first); };
          assert(std::is_heap(_best_partitions.begin(), _best_partitions.end(), comp));
          _best_partitions[0].first = my_result;
          std::pop_heap(_best_partitions.begin(), _best_partitions.end(), comp);
          std::push_heap(_best_partitions.begin(), _best_partitions.end(), comp);
        }
        _pop_lock.unlock();
      }
    } else {
      if (my_ip_data._result.is_other_better(my_result)) {
        my_ip_data._result = my_result;
        my_ip_data.copyPartition(my_ip_data._partition);
      }
    }
    my_ip_data._partitioned_hypergraph.resetPartition();
  }

  void commit(InitialPartitioningAlgorithm algorithm) {
    // dummy values for tests
    std::mt19937 prng(420);
    commit(algorithm, prng, 420);
  }

  /*!
   * Determines the best partition computed by all threads and applies it to
   * the hypergraph. Note, this function is not thread-safe and should be called
   * if no other thread using that object operates on it.
   */
  void apply() {
    // Initialize Stats
    parallel::scalable_vector<utils::InitialPartitionerSummary> stats;
    size_t number_of_threads = 0;
    for ( uint8_t algo = 0; algo < static_cast<uint8_t>(InitialPartitioningAlgorithm::UNDEFINED); ++algo ) {
      stats.emplace_back(static_cast<InitialPartitioningAlgorithm>(algo));
    }
    InitialPartitioningAlgorithm best_flat_algo = InitialPartitioningAlgorithm::UNDEFINED;
    HyperedgeWeight best_feasible_objective = std::numeric_limits<HyperedgeWeight>::max(); unused(best_feasible_objective);

    if ( _context.partition.deterministic ) {
      for (auto& p : _local_hg) {
        ++number_of_threads;
        p.aggregate_stats(stats);
      }

      // bring them in a deterministic order
      std::sort(_best_partitions.begin(), _best_partitions.end(), [&](const auto& l, const auto& r) {
        return r.first.is_other_better(l.first);
      });

      if ( _context.initial_partitioning.perform_refinement_on_best_partitions ) {
        auto refinement_task = [&](size_t i) {
          auto& my_data = _local_hg.local();
          auto& my_phg = my_data._partitioned_hypergraph;
          vec<PartitionID>& my_partition = _best_partitions[i].second;
          PartitioningResult& my_objectives = _best_partitions[i].first;
          std::mt19937 prng(_context.partition.seed + 420 + my_phg.initialNumPins() + i);
          auto refined = my_data.performRefinementOnPartition(my_partition, my_objectives, prng);
          refined._deterministic_tag = my_objectives._deterministic_tag;
          refined._random_tag = my_objectives._random_tag;

          if (my_objectives.is_other_better(refined)) {
            for (HypernodeID node : my_phg.nodes()) {
              my_partition[node] = my_phg.partID(node);
            }
            my_objectives = refined;
          }
        };

        tbb::task_group fm_refinement_group;
        for (size_t i = 0; i < _best_partitions.size(); ++i) {
          fm_refinement_group.run(std::bind(refinement_task, i));
        }
        fm_refinement_group.wait();
      }

      size_t best_index = 0;
      for (size_t i = 1; i < _best_partitions.size(); ++i) {
        if (_best_partitions[best_index].first.is_other_better(_best_partitions[i].first) ) {
          best_index = i;
        }
      }

      best_flat_algo = _best_partitions[best_index].first._algorithm;
      best_feasible_objective = _best_partitions[best_index].first._objective;
      const vec<PartitionID>& best_partition = _best_partitions[best_index].second;

      _partitioned_hg.doParallelForAllNodes([&](HypernodeID node) {
        ASSERT(node < best_partition.size() && best_partition[node] != kInvalidPartition);
        _partitioned_hg.setOnlyNodePart(node, best_partition[node]);
      });

    } else {
      // Perform FM refinement on the best partition of each thread
      int thread_counter = 0;
      if ( _context.initial_partitioning.perform_refinement_on_best_partitions ) {
        tbb::task_group fm_refinement_group;
        for ( LocalInitialPartitioningHypergraph& partition : _local_hg ) {
          fm_refinement_group.run([&, thread_counter] {
            partition.performRefinementOnBestPartition(_partitioned_hg.initialNumPins() + thread_counter);
          });
          thread_counter++;
        }
        fm_refinement_group.wait();
      }

      // Determine best partition
      LocalInitialPartitioningHypergraph* best = nullptr;
      LocalInitialPartitioningHypergraph* worst = nullptr;
      LocalInitialPartitioningHypergraph* best_imbalance = nullptr;
      LocalInitialPartitioningHypergraph* best_objective = nullptr;
      for ( LocalInitialPartitioningHypergraph& partition : _local_hg ) {
        ++number_of_threads;
        partition.aggregate_stats(stats);
        if ( !best || best->_result.is_other_better(partition._result) ) {
          best = &partition;
        }
        if ( !worst || !worst->_result.is_other_better(partition._result) ) {
          worst = &partition;
        }
        if ( !best_imbalance || partition._result._imbalance.isBetter(best_imbalance->_result._imbalance) ||
             (best_imbalance->_result._imbalance.isEqual(partition._result._imbalance) &&
              best_imbalance->_result._objective > partition._result._objective)) {
          best_imbalance = &partition;
        }
        if ( !best_objective || best_objective->_result._objective > partition._result._objective ) {
          best_objective = &partition;
        }
      }

      ASSERT(best);
      ASSERT(worst);
      ASSERT(best_imbalance);
      ASSERT(best_objective);
      DBG << "Num Vertices =" << _partitioned_hg.initialNumNodes()
          << ", Num Edges =" << _partitioned_hg.initialNumEdges()
          << ", k =" << _context.partition.k << ", epsilon =" << _context.partition.epsilon;
      DBG << "Best Partition                [" << best->_result.str() << "]";
      DBG << "Worst Partition               [" << worst->_result.str() << "]";
      DBG << "Best Balanced Partition       [" << best_imbalance->_result.str() << "]";
      DBG << "Partition with Best Objective [" << best_objective->_result.str() << "]";

      // Applies best partition to hypergraph
      _partitioned_hg.doParallelForAllNodes([&](const HypernodeID hn) {
        ASSERT(hn < best->_partition.size());
        const PartitionID part_id = best->_partition[hn];
        ASSERT(part_id != kInvalidPartition && part_id < _partitioned_hg.k());
        ASSERT(_partitioned_hg.partID(hn) == kInvalidPartition);
        _partitioned_hg.setOnlyNodePart(hn, part_id);
      });

      best_flat_algo = best->_result._algorithm;
      best_feasible_objective = best->_result._objective;
    }

    _partitioned_hg.initializePartition();
    ASSERT(best_feasible_objective == metrics::quality(_partitioned_hg, _context, false),
           V(best_feasible_objective) << V(metrics::quality(_partitioned_hg, _context, false)));
    utils::Utilities::instance().getInitialPartitioningStats(
      _context.utility_id).add_initial_partitioning_result(best_flat_algo, number_of_threads, stats);
  }

  IteratorRange<FixedVertexIterator> fixedVertices() const {
    return IteratorRange<FixedVertexIterator>(
      _fixed_vertices.cbegin(), _fixed_vertices.cend());
  }

  HypernodeID numFixedVertices() const {
    return _fixed_vertices.size();
  }

  void preassignFixedVertices(PartitionedHypergraph& hypergraph) {
    if ( hypergraph.hasFixedVertices() ) {
      for ( const HypernodeID& hn : fixedVertices() ) {
        ASSERT(hypergraph.isFixed(hn));
        hypergraph.setNodePart(hn, hypergraph.fixedVertexBlock(hn));
      }
    }
  }

 private:
  LocalInitialPartitioningHypergraph construct_local_partitioned_hypergraph() {
    return LocalInitialPartitioningHypergraph(
      _partitioned_hg.hypergraph(), _context, _global_stats, _disable_fm);
  }

  PartitionedHypergraph& _partitioned_hg;
  Context _context;
  const bool _disable_fm;

  GlobalInitialPartitioningStats _global_stats;

  // TODO group these objects into one struct --> fewer hash tables
  ThreadLocalHypergraph _local_hg;
  ThreadLocalKWayPriorityQueue _local_kway_pq;
  tbb::enumerable_thread_specific<bool> _is_local_pq_initialized;
  ThreadLocalFastResetFlagArray _local_hn_visited;
  ThreadLocalFastResetFlagArray _local_he_visited;
  ThreadLocalUnassignedHypernodes _local_unassigned_hypernodes;
  tbb::enumerable_thread_specific<size_t> _local_unassigned_hypernode_pointer;
  vec<HypernodeID> _fixed_vertices;

  size_t _max_pop_size;
  SpinLock _pop_lock;
  vec< std::pair<PartitioningResult, vec<PartitionID>>  > _best_partitions;
};

namespace ip {
  template<typename TypeTraits>
  ip_data_container_t* to_pointer(InitialPartitioningDataContainer<TypeTraits>& ip_data) {
    return reinterpret_cast<ip_data_container_t*>(&ip_data);
  }

  template<typename TypeTraits>
  InitialPartitioningDataContainer<TypeTraits>& to_reference(ip_data_container_t* ptr) {
    return *reinterpret_cast<InitialPartitioningDataContainer<TypeTraits>*>(ptr);
  }
}

} // namespace mt_kahypar
