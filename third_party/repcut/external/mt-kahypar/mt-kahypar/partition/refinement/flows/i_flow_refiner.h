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


#include "include/mtkahypartypes.h"

#include "mt-kahypar/definitions.h"
#include "mt-kahypar/macros.h"
#include "mt-kahypar/partition/metrics.h"
#include "mt-kahypar/parallel/stl/scalable_vector.h"
#include "mt-kahypar/partition/refinement/flows/flow_common.h"

namespace mt_kahypar {

class IFlowRefiner {

 public:
  IFlowRefiner(const IFlowRefiner&) = delete;
  IFlowRefiner(IFlowRefiner&&) = delete;
  IFlowRefiner & operator= (const IFlowRefiner &) = delete;
  IFlowRefiner & operator= (IFlowRefiner &&) = delete;

  virtual ~IFlowRefiner() = default;

  void initialize(mt_kahypar_partitioned_hypergraph_const_t& phg) {
    initializeImpl(phg);
  }

  MoveSequence refine(mt_kahypar_partitioned_hypergraph_const_t& phg,
                      const Subhypergraph& sub_hg,
                      const HighResClockTimepoint& start) {
    return refineImpl(phg, sub_hg, start);
  }

  // ! Updates the time limit (in seconds)
  void updateTimeLimit(const double time_limit) {
    _time_limit = time_limit;
  }


 protected:
  IFlowRefiner() = default;

  double _time_limit = 0;

 private:
  virtual void initializeImpl(mt_kahypar_partitioned_hypergraph_const_t& phg) = 0;

  virtual MoveSequence refineImpl(mt_kahypar_partitioned_hypergraph_const_t& phg,
                                  const Subhypergraph& sub_hg,
                                  const HighResClockTimepoint& start) = 0;
};

}  // namespace mt_kahypar
