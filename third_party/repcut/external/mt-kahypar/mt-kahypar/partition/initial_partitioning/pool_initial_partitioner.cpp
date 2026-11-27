/*******************************************************************************
 * MIT License
 *
 * This file is part of Mt-KaHyPar.
 *
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

#include "pool_initial_partitioner.h"

#include "mt-kahypar/definitions.h"
#include "mt-kahypar/partition/factories.h"
#include "mt-kahypar/partition/initial_partitioning/i_initial_partitioner.h"
#include "mt-kahypar/partition/initial_partitioning/initial_partitioning_data_container.h"
#include "mt-kahypar/utils/cast.h"
#include "mt-kahypar/utils/exception.h"

namespace mt_kahypar {

namespace {
// IP algorithm and random seed
using IPTask = std::tuple<InitialPartitioningAlgorithm, int, int>;
}

template<typename TypeTraits>
void Pool<TypeTraits>::bipartition(PartitionedHypergraph& hypergraph,
                                   const Context& context,
                                   const bool /*run_parallel*/) {
  ASSERT(context.shared_memory.num_threads > 0);
  if ( context.initial_partitioning.enabled_ip_algos.size() <
        static_cast<size_t>(InitialPartitioningAlgorithm::UNDEFINED) ) {
    throw InvalidParameterException(
      "Size of enabled IP algorithms vector is smaller than number of IP algorithms!");
  }

  int tag = 0;
  std::mt19937 rng(context.partition.seed);
  vec<IPTask> _ip_task_lists;
  // Push the runs of the different initial partitioning algorithms into a task list
  for ( uint8_t i = 0; i < static_cast<uint8_t>(InitialPartitioningAlgorithm::UNDEFINED); ++i ) {
    if ( context.initial_partitioning.enabled_ip_algos[i] ) {
      auto algorithm = static_cast<InitialPartitioningAlgorithm>(i);
      for ( size_t j = 0; j < context.initial_partitioning.runs; ++j ) {
        // Each initial partitioning algorithm is assigned a seed and a tag
        // for deterministic behavior when partitioning in deterministic mode.
        _ip_task_lists.emplace_back(algorithm, rng(), tag++);
      }
    }
  }
  // Random shuffle task list to evenly schedule the initial
  // partitioning algorithms to the threads
  std::shuffle(_ip_task_lists.begin(), _ip_task_lists.end(), rng);

  InitialPartitioningDataContainer<TypeTraits> ip_data(hypergraph, context);
  ip_data_container_t* ip_data_ptr = ip::to_pointer(ip_data);
  for ( const auto& ip_task : _ip_task_lists ) {
    const InitialPartitioningAlgorithm algorithm = std::get<0>(ip_task);
    const int seed = std::get<1>(ip_task);
    const int tag = std::get<2>(ip_task);
    std::unique_ptr<IInitialPartitioner> initial_partitioner =
      InitialPartitionerFactory::getInstance().createObject(
        algorithm, algorithm, ip_data_ptr, context, seed, tag);
    initial_partitioner->partition();
  }
  ip_data.apply();
}

INSTANTIATE_CLASS_WITH_TYPE_TRAITS(Pool)

} // namespace mt_kahypar