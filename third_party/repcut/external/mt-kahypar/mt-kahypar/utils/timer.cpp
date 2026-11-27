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

#include "mt-kahypar/utils/timer.h"

#include "mt-kahypar/macros.h"

namespace mt_kahypar {
namespace utils {

static constexpr int MAX_LINE_LENGTH = 45;
static constexpr char TOP_LEVEL_PREFIX[] = " + ";
static constexpr size_t TOP_LEVEL_PREFIX_LENGTH = 3;
static constexpr char SUB_LEVEL_PREFIX[] = " + ";
static constexpr size_t SUB_LEVEL_PREFIX_LENGTH = 3;

Timer::Timer() :
  _timings(),
  _active_timings(),
  _local_active_timings(),
  _index(0),
  _is_enabled(true),
  _show_detailed_timings(false),
  _max_output_depth(std::numeric_limits<size_t>::max()) { }

Timer::Timer(const Timer& other) :
  _timings(other._timings),
  _active_timings(other._active_timings),
  _local_active_timings(other._local_active_timings),
  _index(other._index),
  _is_enabled(other._is_enabled),
  _show_detailed_timings(other._show_detailed_timings),
  _max_output_depth(other._max_output_depth) { }

Timer::Timer(Timer&& other) :
  _timings(std::move(other._timings)),
  _active_timings(std::move(other._active_timings)),
  _local_active_timings(std::move(other._local_active_timings)),
  _index(other._index),
  _is_enabled(std::move(other._is_enabled)),
  _show_detailed_timings(std::move(other._show_detailed_timings)),
  _max_output_depth(std::move(other._max_output_depth)) { }

void Timer::enable() {
  _is_enabled = true;
}

void Timer::disable() {
  _is_enabled = false;
}

void Timer::clear() {
  _timings.clear();
  _active_timings.clear();
  _index = 0;
}

void Timer::start_timer(const std::string& key,
                  const std::string& description,
                  bool is_parallel_context,
                  bool force) {
  if (_is_enabled || force) {
    if (force || is_parallel_context) {
      _local_active_timings.local().emplace_back(key, description, std::chrono::high_resolution_clock::now());
    } else {
      _active_timings.emplace_back(key, description, std::chrono::high_resolution_clock::now());
    }
  }
}

void Timer::stop_timer(const std::string& key, bool force) {
  unused(key);
  if (_is_enabled || force) {
    HighResClockTimepoint end = std::chrono::high_resolution_clock::now();
    ASSERT(!force || !_local_active_timings.local().empty());
    ActiveTiming current_timing;
    // First check if there are some active timings on the local stack
    // (in that case we are in a parallel context) and if there are
    // no active timings we pop from global stack
    if (!_local_active_timings.local().empty()) {
      ASSERT(_local_active_timings.local().back().key() == key,
        V(_local_active_timings.local().back().key()) << V(key));
      current_timing = _local_active_timings.local().back();
      _local_active_timings.local().pop_back();
    } else {
      ASSERT(!_active_timings.empty());
      ASSERT(_active_timings.back().key() == key, V(_active_timings.back().key()) << V(key));
      current_timing = _active_timings.back();
      _active_timings.pop_back();
    }

    // Parent is either the last element on the local stack and
    // if there are no timings on the local stack the parent is
    // on the global stack. If there are no elements on the global
    // stack the timing represents a root.
    std::string parent = "";
    if (!_local_active_timings.local().empty()) {
      parent = _local_active_timings.local().back().key();
    } else if (!_active_timings.empty()) {
      parent = _active_timings.back().key();
    }

    Key timing_key { parent, current_timing.key() };
    if (_timings.find(timing_key) == _timings.end()) {
      _timings.emplace(
        std::piecewise_construct,
        std::forward_as_tuple(timing_key),
        std::forward_as_tuple(current_timing.key(),
                              current_timing.description(), parent, _index++));
    }
    double time = std::chrono::duration<double>(end - current_timing.start()).count();
    _timings.at(timing_key).add_timing(time);
  }
}

void Timer::serialize(std::ostream& str) {
  std::vector<Timing> timings;
  for (const auto& timing : _timings) {
    timings.emplace_back(timing.second);
  }
  std::sort(timings.begin(), timings.end(),
            [&](const Timing& lhs, const Timing& rhs) {
        return lhs.key() < rhs.key();
      });

  if (!timings.empty()) {
    auto print = [&](const std::string& key, const double time, const bool is_root) {
                    if (_show_detailed_timings || is_root) {
                      str << " " << key << "=" << time;
                    }
                  };

    // We aggregate timings in case there multiple timings with same key
    // but different parent
    std::string last_key = timings[0].key();
    double time = timings[0].timing();
    bool is_root = timings[0].is_root();
    for (size_t i = 1; i < timings.size(); ++i) {
      if (last_key == timings[i].key()) {
        time += timings[i].timing();
        is_root |= timings[i].is_root();
      } else {
        print(last_key, time, is_root);
        last_key = timings[i].key();
        time = timings[i].timing();
        is_root = timings[i].is_root();
      }
    }
    print(last_key, time, is_root);
  }
}

double Timer::get(std::string key) const {
  for (const auto& x : _timings) {
    // unfortunately it has to be linear search because the parent (which we can't lookup at this stage) is part of the map key
    if (x.first.key == key) {
      return x.second.timing();
    }
  }
  return 0.0;
}

std::ostream & operator<< (std::ostream& str, const Timer& timer) {
  std::vector<Timer::Timing> timings;
  for (const auto& timing : timer._timings) {
    timings.emplace_back(timing.second);
  }
  std::sort(timings.begin(), timings.end(),
            [&](const Timer::Timing& lhs, const Timer::Timing& rhs) {
        return lhs.order() < rhs.order();
      });

  auto print = [&](std::ostream& str, const Timer::Timing& timing, int level) {
                 std::string prefix = "";
                 prefix += level == 0 ? std::string(TOP_LEVEL_PREFIX, TOP_LEVEL_PREFIX_LENGTH) :
                           std::string(TOP_LEVEL_PREFIX_LENGTH, ' ');
                 prefix += level > 0 ? std::string(SUB_LEVEL_PREFIX_LENGTH * (level - 1), ' ') : "";
                 prefix += level > 0 ? std::string(SUB_LEVEL_PREFIX, SUB_LEVEL_PREFIX_LENGTH) : "";
                 size_t length = prefix.size() + timing.description().size();
                 str << prefix
                     << timing.description();
                 if (length < MAX_LINE_LENGTH) {
                   str << std::string(MAX_LINE_LENGTH - length, ' ');
                 }
                 str << " = " << timing.timing() << " s\n";
               };

  std::function<void(std::ostream&, const Timer::Timing&, int)> dfs =
    [&](std::ostream& str, const Timer::Timing& parent, int level) {
      if ( static_cast<size_t>(level) <= timer._max_output_depth ) {
        for (const Timer::Timing& timing : timings) {
          if (timing.parent() == parent.key()) {
            print(str, timing, level);
            dfs(str, timing, level + 1);
          }
        }
      }
    };

  for (const Timer::Timing& timing : timings) {
    if (timing.is_root()) {
      print(str, timing, 0);
      if (timer._show_detailed_timings) {
        dfs(str, timing, 1);
      }
    }
  }

  return str;
}

}  // namespace utils
}  // namespace mt_kahypar
