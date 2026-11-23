/*******************************************************************************
 * MIT License
 *
 * This file is part of Mt-KaHyPar.
 *
 * Copyright (C) 2021 Tobias Heuer <tobias.heuer@kit.edu>
 * Copyright (C) 2021 Lars Gottesbüren <lars.gottesbueren@kit.edu>
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

#include <memory>

#include <tbb/concurrent_vector.h>

#include "WHFC/algorithm/hyperflowcutter.h"
#include "WHFC/algorithm/sequential_push_relabel.h"
#include "WHFC/algorithm/parallel_push_relabel.h"

#include "mt-kahypar/partition/context.h"
#include "mt-kahypar/partition/refinement/flows/i_flow_refiner.h"
#include "mt-kahypar/datastructures/sparse_map.h"
#include "mt-kahypar/datastructures/thread_safe_fast_reset_flag_array.h"
#include "mt-kahypar/parallel/stl/scalable_queue.h"
#include "mt-kahypar/partition/refinement/flows/sequential_construction.h"
#include "mt-kahypar/partition/refinement/flows/parallel_construction.h"
#include "mt-kahypar/partition/refinement/flows/flow_hypergraph_builder.h"
#include "mt-kahypar/utils/cast.h"

namespace mt_kahypar {

template<typename GraphAndGainTypes>
class FlowRefiner final : public IFlowRefiner {

  static constexpr bool debug = false;

  using PartitionedHypergraph = typename GraphAndGainTypes::PartitionedHypergraph;

 public:
  explicit FlowRefiner(const HyperedgeID num_hyperedges,
                       const Context& context,
                       bool deterministic) :
    _phg(nullptr),
    _context(context),
    _deterministic(deterministic),
    _num_hyperedges(num_hyperedges),
    _block_0(kInvalidPartition),
    _block_1(kInvalidPartition),
    _flow_hg(),
    _sequential_hfc(_flow_hg, context.partition.seed, deterministic),
    _parallel_hfc(_flow_hg, context.partition.seed, deterministic),
    _whfc_to_node(),
    _sequential_construction(nullptr),
    _parallel_construction(nullptr) {
      _sequential_hfc.find_most_balanced = _context.refinement.flows.find_most_balanced_cut;
      _sequential_hfc.timer.active = false;
      _sequential_hfc.forceSequential(true);
      _sequential_hfc.setBulkPiercing(context.refinement.flows.pierce_in_bulk);

      _parallel_hfc.find_most_balanced = _context.refinement.flows.find_most_balanced_cut;
      _parallel_hfc.timer.active = false;
      _parallel_hfc.forceSequential(false);
      _sequential_hfc.setBulkPiercing(context.refinement.flows.pierce_in_bulk);
  }

  FlowRefiner(const FlowRefiner&) = delete;
  FlowRefiner(FlowRefiner&&) = delete;
  FlowRefiner & operator= (const FlowRefiner &) = delete;
  FlowRefiner & operator= (FlowRefiner &&) = delete;

  virtual ~FlowRefiner() = default;

 protected:

 private:
  void initializeImpl(mt_kahypar_partitioned_hypergraph_const_t& hypergraph) override {
    const PartitionedHypergraph& phg = utils::cast_const<PartitionedHypergraph>(hypergraph);
    _phg = &phg;
    _time_limit = std::numeric_limits<double>::max();
    _block_0 = kInvalidPartition;
    _block_1 = kInvalidPartition;
    _flow_hg.clear();
    _whfc_to_node.clear();
  }

  MoveSequence refineImpl(mt_kahypar_partitioned_hypergraph_const_t& hypergraph,
                          const Subhypergraph& sub_hg,
                          const HighResClockTimepoint& start) override;

  bool runFlowCutter(const FlowProblem& flow_problem,
                     const HighResClockTimepoint& start,
                     bool& time_limit_reached);

  FlowProblem constructFlowHypergraph(const PartitionedHypergraph& phg,
                                      const Subhypergraph& sub_hg);

  bool useSequentialAlgorithm();

  const PartitionedHypergraph* _phg;
  const Context& _context;
  bool _deterministic;
  using IFlowRefiner::_time_limit;

  HyperedgeID _num_hyperedges;
  PartitionID _block_0;
  PartitionID _block_1;
  FlowHypergraphBuilder _flow_hg;
  whfc::HyperFlowCutter<whfc::SequentialPushRelabel> _sequential_hfc;
  whfc::HyperFlowCutter<whfc::ParallelPushRelabel> _parallel_hfc;

  vec<HypernodeID> _whfc_to_node;
  std::unique_ptr<SequentialConstruction<GraphAndGainTypes>> _sequential_construction;
  std::unique_ptr<ParallelConstruction<GraphAndGainTypes>> _parallel_construction;
};
}  // namespace mt_kahypar
