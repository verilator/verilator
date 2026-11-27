/*******************************************************************************
 * MIT License
 *
 * This file is part of Mt-KaHyPar.
 *
 * Copyright (C) 2021 Tobias Heuer <tobias.heuer@kit.edu>
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

#include "mt-kahypar/partition/refinement/flows/i_flow_refiner.h"

namespace mt_kahypar {
class DoNothingFlowRefiner final : public IFlowRefiner {
 public:
  template <typename ... Args>
  explicit DoNothingFlowRefiner(Args&& ...) noexcept { }
  DoNothingFlowRefiner(const DoNothingFlowRefiner&) = delete;
  DoNothingFlowRefiner(DoNothingFlowRefiner&&) = delete;
  DoNothingFlowRefiner & operator= (const DoNothingFlowRefiner &) = delete;
  DoNothingFlowRefiner & operator= (DoNothingFlowRefiner &&) = delete;

 private:
  void initializeImpl(mt_kahypar_partitioned_hypergraph_const_t&) override final { }

  MoveSequence refineImpl(mt_kahypar_partitioned_hypergraph_const_t&,
                          const Subhypergraph&,
                          const HighResClockTimepoint&) override final {
    return MoveSequence { {}, 0 };
  }
};
}  // namespace kahypar
