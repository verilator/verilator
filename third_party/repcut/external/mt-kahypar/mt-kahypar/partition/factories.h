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

#include "mt-kahypar/partition/coarsening/i_coarsener.h"
#include "mt-kahypar/partition/context.h"
#include "mt-kahypar/partition/initial_partitioning/i_initial_partitioner.h"
#include "mt-kahypar/partition/refinement/i_refiner.h"
#include "mt-kahypar/partition/refinement/i_rebalancer.h"
#include "mt-kahypar/partition/refinement/fm/strategies/i_fm_strategy.h"
#include "mt-kahypar/partition/refinement/gains/gain_cache_ptr.h"
#include "mt-kahypar/partition/thread_safe_abstract_factory.h"

namespace mt_kahypar {

typedef struct ip_data_container_s ip_data_container_t;

using CoarsenerFactory = mt_kahypar::ThreadSafeFactory<CoarseningAlgorithm,
                                           ICoarsener* (*)(mt_kahypar_hypergraph_t, const Context&, uncoarsening_data_t*)>;

using InitialPartitionerFactory = mt_kahypar::ThreadSafeFactory<InitialPartitioningAlgorithm,
  IInitialPartitioner* (*)(const InitialPartitioningAlgorithm, ip_data_container_t*, const Context&, const int, const int)>;

using LabelPropagationFactory = mt_kahypar::ThreadSafeFactory<LabelPropagationAlgorithm,
                                  IRefiner* (*)(HypernodeID, HyperedgeID, const Context&, gain_cache_t, IRebalancer&)>;

using JetFactory = mt_kahypar::ThreadSafeFactory<JetAlgorithm,
                     IRefiner* (*)(HypernodeID, HyperedgeID, const Context&, gain_cache_t, IRebalancer&)>;

using FMFactory = mt_kahypar::ThreadSafeFactory<FMAlgorithm,
                    IRefiner* (*)(HypernodeID, HyperedgeID, const Context&, gain_cache_t, IRebalancer&)>;

using FMStrategyFactory = mt_kahypar::ThreadSafeFactory<FMAlgorithm, IFMStrategy* (*)(const Context&, FMSharedData&)>;

using FlowSchedulerFactory = mt_kahypar::ThreadSafeFactory<FlowAlgorithm,
                              IRefiner* (*)(const HypernodeID, const HyperedgeID, const Context&, gain_cache_t)>;

using RebalancerFactory = mt_kahypar::ThreadSafeFactory<RebalancingAlgorithm, IRebalancer* (*)(HypernodeID, const Context&, gain_cache_t)>;

}  // namespace mt_kahypar
