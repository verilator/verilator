/*******************************************************************************
 * MIT License
 *
 * This file is part of Mt-KaHyPar.
 *
 * Copyright (C) 2022 Tobias Heuer <tobias.heuer@kit.edu>
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

#include <tbb/concurrent_vector.h>

#include "mt-kahypar/macros.h"
#include "mt-kahypar/utils/stats.h"
#include "mt-kahypar/utils/initial_partitioning_stats.h"
#include "mt-kahypar/utils/timer.h"

namespace mt_kahypar {
namespace utils {

class Utilities {
  static constexpr bool debug = false;

  struct UtilityObjects {
    UtilityObjects() :
      stats(),
      ip_stats(),
      timer() { }

    Stats stats;
    InitialPartitioningStats ip_stats;
    Timer timer;
  };

 public:
  Utilities(const Utilities&) = delete;
  Utilities & operator= (const Utilities &) = delete;

  Utilities(Utilities&&) = delete;
  Utilities & operator= (Utilities &&) = delete;

  static Utilities& instance() {
    static Utilities instance;
    return instance;
  }

  size_t registerNewUtilityObjects() {
    std::lock_guard<std::mutex> lock(_utility_mutex);
    const size_t id = _utilities.size();
    _utilities.emplace_back();
    return id;
  }

  Stats& getStats(const size_t id) {
    ASSERT(id < _utilities.size());
    return _utilities[id].stats;
  }

  InitialPartitioningStats& getInitialPartitioningStats(const size_t id) {
    ASSERT(id < _utilities.size());
    return _utilities[id].ip_stats;
  }

  Timer& getTimer(const size_t id) {
    ASSERT(id < _utilities.size());
    return _utilities[id].timer;
  }

 private:
  explicit Utilities() :
    _utility_mutex(),
    _utilities() { }

  std::mutex _utility_mutex;
  tbb::concurrent_vector<UtilityObjects> _utilities;
};

}  // namespace utils
}  // namespace mt_kahypar
