/*******************************************************************************
 * MIT License
 *
 * This file is part of Mt-KaHyPar.
 *
 * Copyright (C) 2023 Robert Krause <robert.krause@student.kit.edu>
 * Copyright (C) 2025 Nikolai Maas <nikolai.maas@kit.edu>
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

#include "mt-kahypar/datastructures/streaming_vector.h"
#include "mt-kahypar/partition/context.h"
#include "mt-kahypar/partition/refinement/i_refiner.h"
#include "mt-kahypar/parallel/atomic_wrapper.h"
#include "mt-kahypar/partition/refinement/flows/deterministic/participation_scheduler.h"
#include "mt-kahypar/partition/refinement/flows/i_flow_refiner.h"
#include "mt-kahypar/partition/refinement/flows/flow_refiner.h"
#include "mt-kahypar/partition/refinement/flows/flow_common.h"
#include "mt-kahypar/partition/refinement/flows/problem_construction.h"
#include "mt-kahypar/partition/refinement/flows/quotient_graph.h"
#include "mt-kahypar/partition/refinement/gains/gain_cache_ptr.h"
#include "mt-kahypar/utils/utilities.h"

namespace mt_kahypar {

template<typename GraphAndGainTypes>
class DeterministicFlowRefinementScheduler final : public IRefiner {

  static constexpr bool debug = false;
  static constexpr bool enable_heavy_assert = false;

  using TypeTraits = typename GraphAndGainTypes::TypeTraits;
  using PartitionedHypergraph = typename GraphAndGainTypes::PartitionedHypergraph;
  using GainCache = typename GraphAndGainTypes::GainCache;
  using AttributedGains = typename GraphAndGainTypes::AttributedGains;
  using FlowNetworkConstruction = typename GraphAndGainTypes::FlowNetworkConstruction;

  // needed since we can't use std::pair in StreamingVector
  struct NewCutHyperedge {
    HyperedgeID he;
    PartitionID block;
  };

 public:
  DeterministicFlowRefinementScheduler(const HypernodeID num_hypernodes,
                                       const HyperedgeID num_hyperedges,
                                       const Context& context,
                                       GainCache& gain_cache);

  DeterministicFlowRefinementScheduler(const HypernodeID num_hypernodes,
                                      const HyperedgeID num_hyperedges,
                                      const Context& context,
                                      gain_cache_t gain_cache);

  DeterministicFlowRefinementScheduler(const DeterministicFlowRefinementScheduler&) = delete;
  DeterministicFlowRefinementScheduler(DeterministicFlowRefinementScheduler&&) = delete;
  DeterministicFlowRefinementScheduler& operator= (const DeterministicFlowRefinementScheduler&) = delete;
  DeterministicFlowRefinementScheduler& operator= (DeterministicFlowRefinementScheduler&&) = delete;

private:
  bool refineImpl(mt_kahypar_partitioned_hypergraph_t& phg,
                  const vec<HypernodeID>& refinement_nodes,
                  Metrics& metrics,
                  double time_limit) final;

  std::unique_ptr<IFlowRefiner> constructFlowRefiner();

  HyperedgeWeight applyMoves(const BlockPair& blocks, const MoveSequence& sequence, PartitionedHypergraph& phg);

  void initializeImpl(mt_kahypar_partitioned_hypergraph_t& hypergraph);

  void resizeDataStructuresForCurrentK();

  const Context& _context;
  GainCache& _gain_cache;
  PartitionID _current_k;
  HyperedgeID _num_hyperedges;

  // ! Contains information of all cut hyperedges between the
  // ! blocks of the partition
  QuotientGraph _quotient_graph;

  // ! Block scheduling logic
  ParticipationScheduler _schedule;

  // ! Available flow refiners
  vec<std::unique_ptr<IFlowRefiner>> _refiner;

  // ! Responsible for construction of an flow problems
  ProblemConstruction<TypeTraits> _constructor;

  // ! Stores for each vertex whether it was moved or not
  vec<uint8_t> _was_moved;

  // ! Stores hyperedges that need to be added to the cut
  ds::StreamingVector<NewCutHyperedge> _new_cut_hes;
};

}  // namespace kahypar
