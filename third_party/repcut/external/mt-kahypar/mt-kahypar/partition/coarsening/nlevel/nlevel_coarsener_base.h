/*******************************************************************************
 * MIT License
 *
 * This file is part of Mt-KaHyPar.
 *
 * Copyright (C) 2020 Tobias Heuer <tobias.heuer@kit.edu>
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

#include <tbb/task_group.h>

#include "mt-kahypar/partition/context.h"
#include "mt-kahypar/partition/metrics.h"
#include "mt-kahypar/partition/refinement/i_refiner.h"
#include "mt-kahypar/partition/refinement/flows/i_flow_refiner.h"
#include "mt-kahypar/parallel/stl/scalable_vector.h"
#include "mt-kahypar/utils/utilities.h"
#include "mt-kahypar/partition/coarsening/coarsening_commons.h"

namespace mt_kahypar {

template<typename TypeTraits>
class NLevelCoarsenerBase {
 private:

  static constexpr bool debug = false;
  static constexpr bool enable_heavy_assert = false;

  using Hypergraph = typename TypeTraits::Hypergraph;
  using PartitionedHypergraph = typename TypeTraits::PartitionedHypergraph;
  using ParallelHyperedge = typename Hypergraph::ParallelHyperedge;
  using ParallelHyperedgeVector = vec<vec<ParallelHyperedge>>;

 public:
  NLevelCoarsenerBase(Hypergraph& hypergraph,
                      const Context& context,
                      UncoarseningData<TypeTraits>& uncoarseningData) :
    _hg(hypergraph),
    _context(context),
    _timer(utils::Utilities::instance().getTimer(context.utility_id)),
    _uncoarseningData(uncoarseningData) { }

  NLevelCoarsenerBase(const NLevelCoarsenerBase&) = delete;
  NLevelCoarsenerBase(NLevelCoarsenerBase&&) = delete;
  NLevelCoarsenerBase & operator= (const NLevelCoarsenerBase &) = delete;
  NLevelCoarsenerBase & operator= (NLevelCoarsenerBase &&) = delete;

  virtual ~NLevelCoarsenerBase() = default;

 protected:

  Hypergraph& compactifiedHypergraph() {
    ASSERT(_uncoarseningData.is_finalized);
    return *_uncoarseningData.compactified_hg;
  }

  PartitionedHypergraph& compactifiedPartitionedHypergraph() {
    ASSERT(_uncoarseningData.is_finalized);
    return *_uncoarseningData.compactified_phg;
  }

  void removeSinglePinAndParallelNets(const HighResClockTimepoint& round_start) {
    _timer.start_timer("remove_single_pin_and_parallel_nets", "Remove Single Pin and Parallel Nets");
    _uncoarseningData.removed_hyperedges_batches.emplace_back(_hg.removeSinglePinAndParallelHyperedges());
    const HighResClockTimepoint round_end = std::chrono::high_resolution_clock::now();
    const double elapsed_time = std::chrono::duration<double>(round_end - round_start).count();
    _uncoarseningData.round_coarsening_times.push_back(elapsed_time);
    _timer.stop_timer("remove_single_pin_and_parallel_nets");
  }

 protected:
  // ! Original hypergraph
  Hypergraph& _hg;
  const Context& _context;
  utils::Timer& _timer;
  UncoarseningData<TypeTraits>& _uncoarseningData;
};
}  // namespace mt_kahypar
