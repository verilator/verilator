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

#include "register_initial_partitioning_algorithms.h"

#include "kahypar-resources/meta/static_multi_dispatch_factory.h"
#include "kahypar-resources/meta/typelist.h"
#include "kahypar-resources/meta/registrar.h"

#include "mt-kahypar/partition/context.h"
#include "mt-kahypar/partition/factories.h"
#include "mt-kahypar/definitions.h"
#include "mt-kahypar/partition/initial_partitioning/i_initial_partitioner.h"
#include "mt-kahypar/partition/initial_partitioning/random_initial_partitioner.h"
#include "mt-kahypar/partition/initial_partitioning/bfs_initial_partitioner.h"
#include "mt-kahypar/partition/initial_partitioning/greedy_initial_partitioner.h"
#include "mt-kahypar/partition/initial_partitioning/label_propagation_initial_partitioner.h"
#include "mt-kahypar/partition/initial_partitioning/policies/gain_computation_policy.h"
#include "mt-kahypar/partition/initial_partitioning/policies/pq_selection_policy.h"
#include "mt-kahypar/partition/thread_safe_policy_registry.h"


#define REGISTER_DISPATCHED_INITIAL_PARTITIONER(id, dispatcher, ...)                                  \
  kahypar::meta::Registrar<InitialPartitionerFactory> register_ ## dispatcher(                        \
    id,                                                                                               \
    [](const InitialPartitioningAlgorithm algorithm, ip_data_container_t* ip_data,                    \
       const Context& context, const int seed, const int tag) {                                       \
    return dispatcher::create(                                                                        \
      std::forward_as_tuple(algorithm, ip_data, context, seed, tag),                                  \
      __VA_ARGS__                                                                                     \
      );                                                                                              \
  })

namespace mt_kahypar {

template<typename TypeTraits>
using GreedyRoundRobinFMInitialPartitioner = GreedyInitialPartitioner<TypeTraits, CutGainPolicy, RoundRobinPQSelectionPolicy>;
template<typename TypeTraits>
using GreedyGlobalFMInitialPartitioner = GreedyInitialPartitioner<TypeTraits, CutGainPolicy, GlobalPQSelectionPolicy>;
template<typename TypeTraits>
using GreedySequentialFMInitialPartitioner = GreedyInitialPartitioner<TypeTraits, CutGainPolicy, SequentialPQSelectionPolicy>;
template<typename TypeTraits>
using GreedyRoundRobinMaxNetInitialPartitioner = GreedyInitialPartitioner<TypeTraits, MaxNetGainPolicy, RoundRobinPQSelectionPolicy>;
template<typename TypeTraits>
using GreedyGlobalMaxNetInitialPartitioner = GreedyInitialPartitioner<TypeTraits, MaxNetGainPolicy, GlobalPQSelectionPolicy>;
template<typename TypeTraits>
using GreedySequentialMaxNetInitialPartitioner = GreedyInitialPartitioner<TypeTraits, MaxNetGainPolicy, SequentialPQSelectionPolicy>;

using RandomPartitionerDispatcher = kahypar::meta::StaticMultiDispatchFactory<
                                      RandomInitialPartitioner,
                                      IInitialPartitioner,
                                      kahypar::meta::Typelist<TypeTraitsList>>;
using BFSPartitionerDispatcher = kahypar::meta::StaticMultiDispatchFactory<
                                      BFSInitialPartitioner,
                                      IInitialPartitioner,
                                      kahypar::meta::Typelist<TypeTraitsList>>;
using LPPartitionerDispatcher = kahypar::meta::StaticMultiDispatchFactory<
                                      LabelPropagationInitialPartitioner,
                                      IInitialPartitioner,
                                      kahypar::meta::Typelist<TypeTraitsList>>;
using GreedyRoundRobinFMDispatcher = kahypar::meta::StaticMultiDispatchFactory<
                                      GreedyRoundRobinFMInitialPartitioner,
                                      IInitialPartitioner,
                                      kahypar::meta::Typelist<TypeTraitsList>>;
using GreedyGlobalFMDispatcher = kahypar::meta::StaticMultiDispatchFactory<
                                      GreedyGlobalFMInitialPartitioner,
                                      IInitialPartitioner,
                                      kahypar::meta::Typelist<TypeTraitsList>>;
using GreedySequentialFMDispatcher = kahypar::meta::StaticMultiDispatchFactory<
                                      GreedySequentialFMInitialPartitioner,
                                      IInitialPartitioner,
                                      kahypar::meta::Typelist<TypeTraitsList>>;
using GreedyRoundRobinMaxNetDispatcher = kahypar::meta::StaticMultiDispatchFactory<
                                          GreedyRoundRobinMaxNetInitialPartitioner,
                                          IInitialPartitioner,
                                          kahypar::meta::Typelist<TypeTraitsList>>;
using GreedyGlobalMaxNetDispatcher = kahypar::meta::StaticMultiDispatchFactory<
                                      GreedyGlobalMaxNetInitialPartitioner,
                                      IInitialPartitioner,
                                      kahypar::meta::Typelist<TypeTraitsList>>;
using GreedySequentialMaxNetDispatcher = kahypar::meta::StaticMultiDispatchFactory<
                                          GreedySequentialMaxNetInitialPartitioner,
                                          IInitialPartitioner,
                                          kahypar::meta::Typelist<TypeTraitsList>>;


void register_initial_partitioning_algorithms() {
  REGISTER_DISPATCHED_INITIAL_PARTITIONER(InitialPartitioningAlgorithm::random,
                                          RandomPartitionerDispatcher,
                                          ThreadSafePolicyRegistry<mt_kahypar_partition_type_t>::getInstance().getPolicy(
                                          context.partition.partition_type));
  REGISTER_DISPATCHED_INITIAL_PARTITIONER(InitialPartitioningAlgorithm::bfs,
                                          BFSPartitionerDispatcher,
                                          ThreadSafePolicyRegistry<mt_kahypar_partition_type_t>::getInstance().getPolicy(
                                          context.partition.partition_type));
  REGISTER_DISPATCHED_INITIAL_PARTITIONER(InitialPartitioningAlgorithm::label_propagation,
                                          LPPartitionerDispatcher,
                                          ThreadSafePolicyRegistry<mt_kahypar_partition_type_t>::getInstance().getPolicy(
                                          context.partition.partition_type));
  REGISTER_DISPATCHED_INITIAL_PARTITIONER(InitialPartitioningAlgorithm::greedy_round_robin_fm,
                                          GreedyRoundRobinFMDispatcher,
                                          ThreadSafePolicyRegistry<mt_kahypar_partition_type_t>::getInstance().getPolicy(
                                          context.partition.partition_type));
  REGISTER_DISPATCHED_INITIAL_PARTITIONER(InitialPartitioningAlgorithm::greedy_global_fm,
                                          GreedyGlobalFMDispatcher,
                                          ThreadSafePolicyRegistry<mt_kahypar_partition_type_t>::getInstance().getPolicy(
                                          context.partition.partition_type));
  REGISTER_DISPATCHED_INITIAL_PARTITIONER(InitialPartitioningAlgorithm::greedy_sequential_fm,
                                          GreedySequentialFMDispatcher,
                                          ThreadSafePolicyRegistry<mt_kahypar_partition_type_t>::getInstance().getPolicy(
                                          context.partition.partition_type));
  REGISTER_DISPATCHED_INITIAL_PARTITIONER(InitialPartitioningAlgorithm::greedy_round_robin_max_net,
                                          GreedyRoundRobinMaxNetDispatcher,
                                          ThreadSafePolicyRegistry<mt_kahypar_partition_type_t>::getInstance().getPolicy(
                                          context.partition.partition_type));
  REGISTER_DISPATCHED_INITIAL_PARTITIONER(InitialPartitioningAlgorithm::greedy_global_max_net,
                                          GreedyGlobalMaxNetDispatcher,
                                          ThreadSafePolicyRegistry<mt_kahypar_partition_type_t>::getInstance().getPolicy(
                                          context.partition.partition_type));
  REGISTER_DISPATCHED_INITIAL_PARTITIONER(InitialPartitioningAlgorithm::greedy_sequential_max_net,
                                          GreedySequentialMaxNetDispatcher,
                                          ThreadSafePolicyRegistry<mt_kahypar_partition_type_t>::getInstance().getPolicy(
                                          context.partition.partition_type));
}

}  // namespace mt_kahypar
