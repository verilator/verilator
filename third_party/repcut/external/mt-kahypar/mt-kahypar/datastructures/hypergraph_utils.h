/*******************************************************************************
 * MIT License
 *
 * This file is part of Mt-KaHyPar.
 *
 * Copyright (C) 2026 Nikolai Maas <nikolai.maas@kit.edu>
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

#include "mt-kahypar/datastructures/hypergraph_common.h"

#include <atomic>
#include <limits>

#include <tbb/parallel_reduce.h>


namespace mt_kahypar {

namespace impl {
  inline HypernodeWeight add(HypernodeWeight lhs, HypernodeWeight rhs, std::atomic_bool& error_flag) {
    if (lhs <= std::numeric_limits<HypernodeWeight>::max() - rhs) {
      return lhs + rhs;
    } else {
      error_flag.store(true, std::memory_order_relaxed);
      return lhs;  // prevent UB from signed overflow
    }
  }

  struct safe_addition {
    std::atomic_bool& error_flag;

    HypernodeWeight operator()(const HypernodeWeight& lhs, const HypernodeWeight& rhs) const {
      return add(lhs, rhs, error_flag);
    }
  };
}

template<typename Hypergraph>
HypernodeWeight computeTotalNodeWeightParallel(const Hypergraph& hypergraph, const HypernodeID num_hypernodes) {
  // For some reason, TBB has difficulty handling the exception if it is thrown from within the parallel loop
  // (crashes in debug mode, usually works in release mode but hangs in rare cases). Therefore, we instead set
  // a flag and throw the exception after the calculation is finished.
  std::atomic_bool error_flag = false;
  impl::safe_addition adder {error_flag};

  HypernodeWeight result = tbb::parallel_reduce(
    tbb::blocked_range<HypernodeID>(ID(0), num_hypernodes), 0,
    [&](const tbb::blocked_range<HypernodeID>& range, HypernodeWeight init) {
      HypernodeWeight weight = init;
      for (HypernodeID hn = range.begin(); hn < range.end(); ++hn) {
        if (hypergraph.nodeIsEnabled(hn)) {
          weight = impl::add(weight, hypergraph.nodeWeight(hn), error_flag);
        }
      }
      return weight;
    }, adder);

    if (error_flag) {
      throw InvalidInputException("total node weight overflows weight data type");
    }
    return result;
  }

} // namespace mt_kahypar
