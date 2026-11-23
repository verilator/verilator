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

#include <mutex>
#include <string>
#include <unordered_map>
#include <atomic>
#include <sstream>
#include <chrono>
#if _WIN32
#include <windows.h>
#else
#include <sys/ioctl.h>
#include <unistd.h>
#endif
#include <stdio.h>

#include "mt-kahypar/macros.h"

namespace mt_kahypar {
namespace utils {
class ProgressBar {

 using HighResClockTimepoint = std::chrono::time_point<std::chrono::high_resolution_clock>;

 public:
  explicit ProgressBar(const size_t expected_count,
                       const int64_t objective,
                       const bool enable = true) :
    _display_mutex(),
    _count(0),
    _next_tic_count(0),
    _expected_count(expected_count),
    _start(std::chrono::high_resolution_clock::now()),
    _objective(objective),
    _progress_bar_size(0),
    _enable(enable) {
    #if _WIN32
    CONSOLE_SCREEN_BUFFER_INFO csbi;
    GetConsoleScreenBufferInfo(GetStdHandle(STD_OUTPUT_HANDLE), &csbi);
    _progress_bar_size = std::min((csbi.srWindow.Right - csbi.srWindow.Left + 1) / 2, 75);
    #else
    struct winsize w;
    ioctl(STDOUT_FILENO, TIOCGWINSZ, &w);
    _progress_bar_size =  std::min(w.ws_col / 2, 75);
    #endif
    display_progress();
  }

  ProgressBar(const ProgressBar&) = delete;
  ProgressBar & operator= (const ProgressBar &) = delete;

  ProgressBar(ProgressBar&&) = delete;
  ProgressBar & operator= (ProgressBar &&) = delete;

  ~ProgressBar() {
    finalize();
  }

  void enable() {
    _enable = true;
    display_progress();
  }

  void disable() {
    _enable = false;
  }

  size_t count() const {
    return _count.load();
  }

  size_t operator+=( const size_t increment ) {
    if ( _enable ) {
      _count.fetch_add(increment);
      if ( _count >= _next_tic_count ) {
        display_progress();
      }
    }
    return _count;
  }

  void setObjective(const int64_t objective) {
    _objective = objective;
  }

  void addToObjective(const int64_t delta) {
    repcut_serial::Ref(_objective).fetch_add(delta, std::memory_order_relaxed);
  }

 private:
  void finalize() {
    if ( _count.load() < _expected_count ) {
      _count = _expected_count;
      _next_tic_count = std::numeric_limits<size_t>::max();
      display_progress();
    }
  }

  void display_progress() {
    if ( _enable ) {
      std::lock_guard<std::mutex> lock(_display_mutex);
      HighResClockTimepoint end = std::chrono::high_resolution_clock::now();
      size_t current_count = std::min(_count.load(), _expected_count);
      _next_tic_count = compute_next_tic_count(current_count);
      size_t current_tics = get_tics(current_count);
      size_t progress = get_progress(current_count);

      std::cout << "[ " << GREEN;
      for ( size_t i = 0; i < current_tics; ++i ) {
        std::cout << "#";
      }
      std::cout << END;
      for ( size_t i = 0; i < _progress_bar_size - current_tics; ++i ) {
        std::cout << " ";
      }
      std::cout << " ] ";

      std::cout << "(" << progress << "%) ";

      size_t time = std::chrono::duration<double>(end - _start).count();
      display_time(time);

      std::cout << " - Current Objective: " << _objective;

      if ( current_count == _expected_count ) {
        std::cout << std::endl;
      } else {
        std::cout << "\r" << std::flush;
      }
    }
  }

  void display_time(const size_t time) {
    size_t minutes = time / 60;
    size_t seconds = time % 60;
    if ( minutes > 0 ) {
      std::cout << minutes << " min ";
    }
    std::cout << seconds << " s";
  }

  size_t get_progress(const size_t current_count) {
    return ( static_cast<double>(current_count) /
      static_cast<double>(_expected_count) ) * 100;
  }

  size_t get_tics(const size_t current_count) {
    return ( static_cast<double>(current_count) /
      static_cast<double>(_expected_count) ) * _progress_bar_size;
  }

  size_t compute_next_tic_count(const size_t current_count) {
    size_t next_tics = get_tics(current_count) + 1;
    if ( next_tics > _progress_bar_size ) {
      return std::numeric_limits<size_t>::max();
    } else {
      return ( static_cast<double>(next_tics) / static_cast<double>(_progress_bar_size) ) *
        static_cast<double>(_expected_count);
    }
  }

  std::mutex _display_mutex;
  std::atomic<size_t> _count;
  std::atomic<size_t> _next_tic_count;
  size_t _expected_count;
  HighResClockTimepoint _start;
  int64_t _objective;
  size_t _progress_bar_size;
  bool _enable;
};

}  // namespace utils
}  // namespace mt_kahypar
