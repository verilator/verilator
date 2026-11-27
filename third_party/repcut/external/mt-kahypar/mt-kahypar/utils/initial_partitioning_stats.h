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

#include <mutex>
#include <string>

#include "mt-kahypar/partition/context_enum_classes.h"
#include "mt-kahypar/parallel/stl/scalable_vector.h"

namespace mt_kahypar {
namespace utils {

struct InitialPartitionerSummary {

  explicit InitialPartitionerSummary(const InitialPartitioningAlgorithm algo) :
    algorithm(algo),
    total_sum_quality(0),
    total_time(0.0),
    total_best(0),
    total_calls(0) { }

  friend std::ostream & operator<< (std::ostream& str, const InitialPartitionerSummary& summary);

  void add(const InitialPartitionerSummary& summary) {
    ASSERT(algorithm == summary.algorithm);
    total_sum_quality += summary.total_sum_quality;
    total_time += summary.total_time;
    total_calls += summary.total_calls;
  }

  double average_quality() const {
    return static_cast<double>(total_sum_quality) / std::max(total_calls, UL(1));
  }

  double average_running_time() const {
    return static_cast<double>(total_time) / std::max(total_calls, UL(1));
  }

  double percentage_best(const size_t total_ip_calls) const {
    return ( static_cast<double>(total_best) / total_ip_calls ) * 100.0;
  }

  InitialPartitioningAlgorithm algorithm;
  double total_sum_quality;
  double total_time;
  size_t total_best;
  size_t total_calls;
};

inline std::ostream & operator<< (std::ostream& str, const InitialPartitionerSummary& summary) {
  str << " avg_quality_" << summary.algorithm << "=" << summary.average_quality()
      << " total_time_" << summary.algorithm << "=" << summary.total_time
      << " total_best_" << summary.algorithm << "=" << summary.total_best;
  return str;
}

class InitialPartitioningStats {

 public:
  explicit InitialPartitioningStats() :
    _stat_mutex(),
    _num_initial_partitioner(static_cast<uint8_t>(InitialPartitioningAlgorithm::UNDEFINED)),
    _ip_summary(),
    _total_ip_calls(0),
    _total_sum_number_of_threads(0) {
    for ( uint8_t algo = 0; algo < _num_initial_partitioner; ++algo ) {
      _ip_summary.emplace_back(static_cast<InitialPartitioningAlgorithm>(algo));
    }
  }

  InitialPartitioningStats(const InitialPartitioningStats& other) :
    _stat_mutex(),
    _num_initial_partitioner(other._num_initial_partitioner),
    _ip_summary(other._ip_summary),
    _total_ip_calls(other._total_ip_calls),
    _total_sum_number_of_threads(other._total_sum_number_of_threads) { }

  InitialPartitioningStats & operator= (const InitialPartitioningStats &) = delete;

  InitialPartitioningStats(InitialPartitioningStats&& other) :
    _stat_mutex(),
    _num_initial_partitioner(std::move(other._num_initial_partitioner)),
    _ip_summary(std::move(other._ip_summary)),
    _total_ip_calls(std::move(other._total_ip_calls)),
    _total_sum_number_of_threads(std::move(other._total_sum_number_of_threads)) { }

  InitialPartitioningStats & operator= (InitialPartitioningStats &&) = delete;

  void add_initial_partitioning_result(const InitialPartitioningAlgorithm best_algorithm,
                                       const size_t number_of_threads,
                                       const parallel::scalable_vector<InitialPartitionerSummary>& summary) {
    std::lock_guard<std::mutex> lock(_stat_mutex);
    ASSERT(summary.size() == _ip_summary.size());
    uint8_t best_algorithm_index = static_cast<uint8_t>(best_algorithm);
    ++_ip_summary[best_algorithm_index].total_best;

    for ( size_t i = 0; i < _num_initial_partitioner; ++i ) {
      _ip_summary[i].add(summary[i]);
    }

    _total_sum_number_of_threads += number_of_threads;
    ++_total_ip_calls;
  }

  double average_number_of_threads_per_ip_call() const {
    return static_cast<double>(_total_sum_number_of_threads) / _total_ip_calls;
  }

  void printInitialPartitioningStats() {
    LOG << "Initial Partitioning Algorithm Summary:";
    LOG << "Number of Initial Partitioning Calls =" << _total_ip_calls;
    LOG << "Average Number of Thread per IP Call ="
        << average_number_of_threads_per_ip_call() << "\n";
    std::cout << "\033[1m"
              << std::left << std::setw(30) << "Algorithm"
              << std::left << std::setw(15) << " Avg. Quality"
              << std::left << std::setw(15) << "  Total Time (s)"
              << std::left << std::setw(10) << "  Total Best"
              << std::left << std::setw(15) << " Total Best (%)"
              << "\033[0m" << std::endl;
    for ( const InitialPartitionerSummary& summary : _ip_summary ) {
      LOG << std::left << std::setw(30) << summary.algorithm
          << std::left << std::setw(15) << summary.average_quality()
          << std::left << std::setw(15) << summary.total_time
          << std::left << std::setw(10) << summary.total_best
          << std::left << std::setw(15) << summary.percentage_best(_total_ip_calls);
    }
  }

  friend std::ostream & operator<< (std::ostream& str, const InitialPartitioningStats& stats);

 private:
  std::mutex _stat_mutex;
  const uint8_t _num_initial_partitioner;
  parallel::scalable_vector<InitialPartitionerSummary> _ip_summary;
  size_t _total_ip_calls;
  size_t _total_sum_number_of_threads;
};

inline std::ostream & operator<< (std::ostream& str, const InitialPartitioningStats& stats) {
  str << " average_number_of_threads_per_ip_call="
      << stats.average_number_of_threads_per_ip_call();
  for ( const InitialPartitionerSummary& summary : stats._ip_summary ) {
    str << summary;
  }
  return str;
}

}  // namespace utils
}  // namespace mt_kahypar
