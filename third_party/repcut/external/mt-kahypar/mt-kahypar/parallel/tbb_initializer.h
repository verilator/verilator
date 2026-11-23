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

#include "repcut_serial.h"
#include <tbb/global_control.h>

namespace mt_kahypar {
namespace parallel {

class SimpleTBBInitializer {

 public:
  static constexpr bool provides_numa_information = false;

  SimpleTBBInitializer(const SimpleTBBInitializer&) = delete;
  SimpleTBBInitializer & operator= (const SimpleTBBInitializer &) = delete;

  SimpleTBBInitializer(SimpleTBBInitializer&&) = delete;
  SimpleTBBInitializer & operator= (SimpleTBBInitializer &&) = delete;

  static void initialize(const size_t num_threads) {
    instanceImpl(num_threads);
  }

  static SimpleTBBInitializer& instance() {
    return instanceImpl(0);
  }

  int num_used_numa_nodes() const {
    return 1;
  }

  int total_number_of_threads() const {
    return _num_threads;
  }

  void terminate() { }

 private:
  explicit SimpleTBBInitializer(const int num_threads) :
    _num_threads(num_threads),
    _gc(tbb::global_control::max_allowed_parallelism, num_threads) { }

  static SimpleTBBInitializer& instanceImpl(const size_t num_threads) {
    static SimpleTBBInitializer instance(num_threads);
    return instance;
  }

  int _num_threads;
  tbb::global_control _gc;
};

}  // namespace parallel
}  // namespace mt_kahypar
