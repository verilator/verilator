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

#include "repcut_serial.h"

#include <chrono>
#include <string>
#include <unordered_map>

#include <tbb/enumerable_thread_specific.h>

namespace mt_kahypar {
namespace utils {

class Timer {
  static constexpr bool debug = false;

  using HighResClockTimepoint = std::chrono::time_point<std::chrono::high_resolution_clock>;

 private:
  struct Key {
    std::string parent;
    std::string key;
  };

  struct KeyHasher {
    std::size_t operator() (const Key& key) const {
      return std::hash<std::string>()(key.parent) ^ std::hash<std::string>()(key.key);
    }
  };

  struct KeyEqual {
    bool operator() (const Key& lhs, const Key& rhs) const {
      return lhs.parent == rhs.parent && lhs.key == rhs.key;
    }
  };

  class ActiveTiming {
   public:
    ActiveTiming() :
      _key(""),
      _description(""),
      _start() { }

    ActiveTiming(const std::string& key,
                 const std::string& description,
                 const HighResClockTimepoint& start) :
      _key(key),
      _description(description),
      _start(start) { }

    std::string key() const {
      return _key;
    }

    std::string description() const {
      return _description;
    }

    HighResClockTimepoint start() const {
      return _start;
    }

   private:
    std::string _key;
    std::string _description;
    HighResClockTimepoint _start;
  };

  class Timing {
   public:
    Timing(const std::string& key,
           const std::string& description,
           const std::string& parent,
           const int order) :
      _key(key),
      _description(description),
      _parent(parent),
      _order(order),
      _timing(0.0) { }

    std::string key() const {
      return _key;
    }

    std::string description() const {
      return _description;
    }

    std::string parent() const {
      return _parent;
    }

    int order() const {
      return _order;
    }

    bool is_root() const {
      return (_parent == "");
    }

    double timing() const {
      return _timing;
    }

    void add_timing(const double timing) {
      _timing += timing;
    }

   private:
    std::string _key;
    std::string _description;
    std::string _parent;
    int _order;
    double _timing;
  };

  using ActiveTimingStack = std::vector<ActiveTiming>;
  using LocalActiveTimingStack = tbb::enumerable_thread_specific<ActiveTimingStack>;

 public:
  explicit Timer();

  Timer(const Timer& other);
  Timer & operator= (const Timer &) = delete;

  Timer(Timer&& other);
  Timer & operator= (Timer &&) = delete;

  void setMaximumOutputDepth(const size_t max_output_depth) {
    _max_output_depth = max_output_depth;
  }

  void showDetailedTimings(const bool show_detailed_timings) {
    _show_detailed_timings = show_detailed_timings;
  }

  bool isEnabled() const {
    return _is_enabled;
  }

  void enable();

  void disable();

  void clear();

  void start_timer(const std::string& key,
                   const std::string& description,
                   bool is_parallel_context = false,
                   bool force = false);

  void stop_timer(const std::string& key, bool force = false);

  void serialize(std::ostream& str);

  friend std::ostream & operator<< (std::ostream& str, const Timer& timer);

  double get(std::string key) const;

 private:
  std::unordered_map<Key, Timing, KeyHasher, KeyEqual> _timings;
  // Global Active Timing Stack
  // Timings are pushed to the global stack
  // if we are in a sequential context
  ActiveTimingStack _active_timings;
  // Thread Local Timing Stack
  // Timings are pushed to the thread local stack
  // if we are in a parallel context
  LocalActiveTimingStack _local_active_timings;
  int _index;
  bool _is_enabled;
  bool _show_detailed_timings;
  size_t _max_output_depth;
};

std::ostream & operator<< (std::ostream& str, const Timer& timer);

}  // namespace utils
}  // namespace mt_kahypar
