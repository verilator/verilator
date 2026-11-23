/*******************************************************************************
 * MIT License
 *
 * This file is part of KaHyPar.
 *
 * Copyright (C) 2015 Sebastian Schlag <sebastian.schlag@kit.edu>
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

#include <array>
#include <string>
#include <utility>
#include <vector>

#include "mt-kahypar/partition/refinement/i_rebalancer.h"

namespace mt_kahypar {
class DoNothingRefiner final : public IRebalancer {
 public:
  template <typename ... Args>
  explicit DoNothingRefiner(Args&& ...) noexcept { }
  DoNothingRefiner(const DoNothingRefiner&) = delete;
  DoNothingRefiner(DoNothingRefiner&&) = delete;
  DoNothingRefiner & operator= (const DoNothingRefiner &) = delete;
  DoNothingRefiner & operator= (DoNothingRefiner &&) = delete;

 private:
  void initializeImpl(mt_kahypar_partitioned_hypergraph_t&) override final { }

  bool refineImpl(mt_kahypar_partitioned_hypergraph_t&,
                  const parallel::scalable_vector<HypernodeID>&,
                  Metrics &,
                  const double) override final {
    return false;
  }

  virtual bool refineAndOutputMovesImpl(mt_kahypar_partitioned_hypergraph_t&,
                                        const parallel::scalable_vector<HypernodeID>&,
                                        parallel::scalable_vector<parallel::scalable_vector<Move>>&,
                                        Metrics&,
                                        const double) override final {
    return false;
  }

  virtual bool refineAndOutputMovesLinearImpl(mt_kahypar_partitioned_hypergraph_t&,
                                              const parallel::scalable_vector<HypernodeID>&,
                                              parallel::scalable_vector<Move>&,
                                              Metrics&,
                                              const double) override final {
    return false;
  }
};
}  // namespace kahypar
