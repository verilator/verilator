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

#include <cstdint>
#include <limits>

#include "include/mtkahypartypes.h"

#include "mt-kahypar/parallel/stl/scalable_vector.h"
#include "mt-kahypar/datastructures/array.h"

namespace mt_kahypar {

#define UI64(X) static_cast<uint64_t>(X)

struct parallel_tag_t { };
using RatingType = double;
#if KAHYPAR_USE_64_BIT_IDS
#define ID(X) static_cast<uint64_t>(X)
using HypernodeID = uint64_t;
using HyperedgeID = uint64_t;
// louvain graph
using NodeID = uint64_t;
#else
#define ID(X) static_cast<uint32_t>(X)
using HypernodeID = uint32_t;
using HyperedgeID = uint32_t;
// louvain graph
using NodeID = uint32_t;
#endif
using HypernodeWeight = int32_t;
using HyperedgeWeight = int32_t;
using PartitionID = int32_t;
using Gain = HyperedgeWeight;

using ArcWeight = double;

struct Arc {
  NodeID head;
  ArcWeight weight;

  Arc() :
    head(0),
    weight(0) { }

  Arc(NodeID head, ArcWeight weight) :
    head(head),
    weight(weight) { }
};

// Constant Declarations
static constexpr PartitionID kInvalidPartition = -1;
static constexpr HypernodeID kInvalidHypernode = std::numeric_limits<HypernodeID>::max();
static constexpr HypernodeID kInvalidHyperedge = std::numeric_limits<HyperedgeID>::max();
static constexpr Gain kInvalidGain = std::numeric_limits<HyperedgeID>::min();
static constexpr size_t kEdgeHashSeed = 42;

static constexpr HypernodeID invalidNode = std::numeric_limits<HypernodeID>::max();
static constexpr Gain invalidGain = std::numeric_limits<Gain>::min();

namespace ds {
  using Clustering = vec<PartitionID>;
}

struct Move {
  PartitionID from = kInvalidPartition;
  PartitionID to = kInvalidPartition;
  HypernodeID node = invalidNode;
  Gain gain = invalidGain;

  bool isValid() const {
    return from != kInvalidPartition;
  }

  void invalidate() {
    from = kInvalidPartition;
  }
};

struct Memento {
  HypernodeID u; // representative
  HypernodeID v; // contraction partner
};

template<typename Hypergraph>
struct ExtractedHypergraph {
  Hypergraph hg;
  vec<HypernodeID> hn_mapping;
  vec<uint8_t> already_cut;
};

using Batch = parallel::scalable_vector<Memento>;
using BatchVector = parallel::scalable_vector<Batch>;
using VersionedBatchVector = parallel::scalable_vector<BatchVector>;

using MoveID = uint32_t;
using SearchID = uint32_t;

// Forward Declaration
class TargetGraph;
namespace ds {
class StaticGraph;
class StaticHypergraph;
class DynamicGraph;
class DynamicHypergraph;
class ConnectivityInfo;
class SparseConnectivityInfo;
}

template<typename Hypergraph, typename ConInfo>
struct PartitionedHypergraphType {
  static constexpr mt_kahypar_partition_type_t TYPE = NULLPTR_PARTITION;
};

template<>
struct PartitionedHypergraphType<ds::StaticHypergraph, ds::ConnectivityInfo> {
  static constexpr mt_kahypar_partition_type_t TYPE = MULTILEVEL_HYPERGRAPH_PARTITIONING;
};

template<>
struct PartitionedHypergraphType<ds::StaticHypergraph, ds::SparseConnectivityInfo> {
  static constexpr mt_kahypar_partition_type_t TYPE = LARGE_K_PARTITIONING;
};

template<>
struct PartitionedHypergraphType<ds::DynamicHypergraph, ds::ConnectivityInfo> {
  static constexpr mt_kahypar_partition_type_t TYPE = N_LEVEL_HYPERGRAPH_PARTITIONING;
};

template<typename Graph>
struct PartitionedGraphType {
  static constexpr mt_kahypar_partition_type_t TYPE = NULLPTR_PARTITION;
};

template<>
struct PartitionedGraphType<ds::StaticGraph> {
  static constexpr mt_kahypar_partition_type_t TYPE = MULTILEVEL_GRAPH_PARTITIONING;
};

template<>
struct PartitionedGraphType<ds::DynamicGraph> {
  static constexpr mt_kahypar_partition_type_t TYPE = N_LEVEL_GRAPH_PARTITIONING;
};


} // namespace mt_kahypar
