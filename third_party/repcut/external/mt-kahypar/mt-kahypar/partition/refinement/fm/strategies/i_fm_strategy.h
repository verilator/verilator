/*******************************************************************************
 * MIT License
 *
 * This file is part of Mt-KaHyPar.
 *
 * Copyright (C) 2023 Nikolai Maas <nikolai.maas@kit.edu>
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
#include "mt-kahypar/partition/context.h"

namespace mt_kahypar {

struct localized_k_way_fm_s;

struct localized_k_way_fm_t {
  localized_k_way_fm_s* local_fm;
  mt_kahypar_partition_type_t type;
};

// forward declaration
struct FMSharedData;

class IFMStrategy {
 public:
  // !!! The following declarations should be present in subclasses:
  // using LocalFM = ...;
  // using PartitionedHypergraph = ...;

  IFMStrategy(const IFMStrategy&) = delete;
  IFMStrategy(IFMStrategy&&) = delete;
  IFMStrategy & operator= (const IFMStrategy &) = delete;
  IFMStrategy & operator= (IFMStrategy &&) = delete;

  virtual ~IFMStrategy() = default;

  void findMoves(localized_k_way_fm_t local_fm, mt_kahypar_partitioned_hypergraph_t& phg,
                 size_t num_tasks, size_t num_seeds, size_t round) {
    findMovesImpl(local_fm, phg, num_tasks, num_seeds, round);
  }

  bool isUnconstrainedRound(size_t round) const {
    return isUnconstrainedRoundImpl(round);
  }

  void reportImprovement(size_t round, Gain absolute_improvement, double relative_improvement) {
    reportImprovementImpl(round, absolute_improvement, relative_improvement);
  }

  // !!! The following method should be present in subclasses:
  // bool dispatchedFindMoves(LocalFM& local_fm, PartitionedHypergraph& phg,
  //                          size_t task_id, size_t num_seeds, size_t round);

 protected:
  IFMStrategy(const Context& context, FMSharedData& sharedData):
      context(context), sharedData(sharedData) { }

  const Context& context;
  FMSharedData& sharedData;

 private:
  virtual void findMovesImpl(localized_k_way_fm_t local_fm, mt_kahypar_partitioned_hypergraph_t& phg,
                             size_t num_tasks, size_t num_seeds, size_t round) = 0;

  virtual bool isUnconstrainedRoundImpl(size_t round) const = 0;

  virtual void reportImprovementImpl(size_t, Gain, double) {
    // most strategies don't use this
  }
};

}  // namespace mt_kahypar
