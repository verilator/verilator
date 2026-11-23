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

#pragma once

#include "kahypar-resources/meta/policy_registry.h"
#include "kahypar-resources/meta/typelist.h"

#include "include/mtkahypartypes.h"
#include "mt-kahypar/macros.h"

#include "mt-kahypar/datastructures/dynamic_graph.h"
#include "mt-kahypar/datastructures/dynamic_graph_factory.h"
#include "mt-kahypar/datastructures/static_graph.h"
#include "mt-kahypar/datastructures/static_graph_factory.h"
#include "mt-kahypar/datastructures/partitioned_graph.h"
#include "mt-kahypar/datastructures/delta_partitioned_graph.h"
#include "mt-kahypar/datastructures/dynamic_hypergraph.h"
#include "mt-kahypar/datastructures/dynamic_hypergraph_factory.h"
#include "mt-kahypar/datastructures/static_hypergraph.h"
#include "mt-kahypar/datastructures/static_hypergraph_factory.h"
#include "mt-kahypar/datastructures/partitioned_hypergraph.h"
#include "mt-kahypar/datastructures/delta_partitioned_hypergraph.h"

namespace mt_kahypar {

using StaticPartitionedGraph = ds::PartitionedGraph<ds::StaticGraph>;
using DynamicPartitionedGraph = ds::PartitionedGraph<ds::DynamicGraph>;
using StaticPartitionedHypergraph = ds::PartitionedHypergraph<ds::StaticHypergraph, ds::ConnectivityInfo>;
using DynamicPartitionedHypergraph = ds::PartitionedHypergraph<ds::DynamicHypergraph, ds::ConnectivityInfo>;
using StaticSparsePartitionedHypergraph = ds::PartitionedHypergraph<ds::StaticHypergraph, ds::SparseConnectivityInfo>;

struct StaticGraphTypeTraits : public kahypar::meta::PolicyBase {
  using Hypergraph = ds::StaticGraph;
  using PartitionedHypergraph = StaticPartitionedGraph;
};

struct DynamicGraphTypeTraits : public kahypar::meta::PolicyBase {
  using Hypergraph = ds::DynamicGraph;
  using PartitionedHypergraph = DynamicPartitionedGraph;
};

struct StaticHypergraphTypeTraits : public kahypar::meta::PolicyBase {
  using Hypergraph = ds::StaticHypergraph;
  using PartitionedHypergraph = StaticPartitionedHypergraph;
};

struct DynamicHypergraphTypeTraits : public kahypar::meta::PolicyBase {
  using Hypergraph = ds::DynamicHypergraph;
  using PartitionedHypergraph = DynamicPartitionedHypergraph;
};

struct LargeKHypergraphTypeTraits : public kahypar::meta::PolicyBase {
  using Hypergraph = ds::StaticHypergraph;
  using PartitionedHypergraph = StaticSparsePartitionedHypergraph;
};

using TypeTraitsList = kahypar::meta::Typelist<StaticHypergraphTypeTraits
                                               ENABLE_GRAPHS(COMMA StaticGraphTypeTraits)
                                               ENABLE_HIGHEST_QUALITY(COMMA DynamicHypergraphTypeTraits)
                                               ENABLE_HIGHEST_QUALITY_FOR_GRAPHS(COMMA DynamicGraphTypeTraits)
                                               ENABLE_LARGE_K(COMMA LargeKHypergraphTypeTraits)>;

#define INSTANTIATE_FUNC_WITH_HYPERGRAPHS(FUNC)                      \
  template FUNC(ds::StaticHypergraph);                               \
  ENABLE_GRAPHS(template FUNC(ds::StaticGraph);)                     \
  ENABLE_HIGHEST_QUALITY(template FUNC(ds::DynamicHypergraph);)       \
  ENABLE_HIGHEST_QUALITY_FOR_GRAPHS(template FUNC(ds::DynamicGraph);)

#define INSTANTIATE_CLASS_WITH_HYPERGRAPHS(C)                           \
  template class C<ds::StaticHypergraph>;                               \
  ENABLE_GRAPHS(template class C<ds::StaticGraph>;)                     \
  ENABLE_HIGHEST_QUALITY(template class C<ds::DynamicHypergraph>;)       \
  ENABLE_HIGHEST_QUALITY_FOR_GRAPHS(template class C<ds::DynamicGraph>;)

#define INSTANTIATE_FUNC_WITH_PARTITIONED_HG(FUNC)                           \
  template FUNC(StaticPartitionedHypergraph);                                \
  ENABLE_GRAPHS(template FUNC(StaticPartitionedGraph);)                      \
  ENABLE_LARGE_K(template FUNC(StaticSparsePartitionedHypergraph);)          \
  ENABLE_HIGHEST_QUALITY(template FUNC(DynamicPartitionedHypergraph);)        \
  ENABLE_HIGHEST_QUALITY_FOR_GRAPHS(template FUNC(DynamicPartitionedGraph);)

#define INSTANTIATE_CLASS_WITH_PARTITIONED_HG(C)                                \
  template class C<StaticPartitionedHypergraph>;                                \
  ENABLE_GRAPHS(template class C<StaticPartitionedGraph>;)                      \
  ENABLE_LARGE_K(template class C<StaticSparsePartitionedHypergraph>;)          \
  ENABLE_HIGHEST_QUALITY(template class C<DynamicPartitionedHypergraph>;)        \
  ENABLE_HIGHEST_QUALITY_FOR_GRAPHS(template class C<DynamicPartitionedGraph>;)

#define INSTANTIATE_CLASS_WITH_TYPE_TRAITS(C)                                   \
  template class C<StaticHypergraphTypeTraits>;                                 \
  ENABLE_GRAPHS(template class C<StaticGraphTypeTraits>;)                       \
  ENABLE_HIGHEST_QUALITY(template class C<DynamicHypergraphTypeTraits>;)         \
  ENABLE_HIGHEST_QUALITY_FOR_GRAPHS(template class C<DynamicGraphTypeTraits>;)   \
  ENABLE_LARGE_K(template class C<LargeKHypergraphTypeTraits>;)


using HighResClockTimepoint = std::chrono::time_point<std::chrono::high_resolution_clock>;

}  // namespace mt_kahypar
