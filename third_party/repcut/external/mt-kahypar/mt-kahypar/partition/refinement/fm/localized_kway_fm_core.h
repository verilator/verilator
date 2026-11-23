/*******************************************************************************
 * MIT License
 *
 * This file is part of Mt-KaHyPar.
 *
 * Copyright (C) 2020 Lars Gottesbüren <lars.gottesbueren@kit.edu>
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

#include "mt-kahypar/partition/context.h"
#include "mt-kahypar/partition/metrics.h"

#include "mt-kahypar/datastructures/sparse_map.h"
#include "mt-kahypar/partition/refinement/fm/fm_commons.h"
#include "mt-kahypar/partition/refinement/fm/stop_rule.h"

namespace mt_kahypar {


template<typename GraphAndGainTypes>
class LocalizedKWayFM {
public:
  using PartitionedHypergraph = typename GraphAndGainTypes::PartitionedHypergraph;

 private:
  static constexpr size_t MAP_SIZE_LARGE = 16384;
  static constexpr size_t MAP_SIZE_MOVE_DELTA = 8192;

  using GainCache = typename GraphAndGainTypes::GainCache;
  using DeltaGainCache = typename GraphAndGainTypes::DeltaGainCache;
  using DeltaPartitionedHypergraph = typename PartitionedHypergraph::template DeltaPartition<DeltaGainCache::requires_connectivity_set>;
  using BlockPriorityQueue = ds::ExclusiveHandleHeap< ds::MaxHeap<Gain, PartitionID> >;
  using VertexPriorityQueue = ds::MaxHeap<Gain, HypernodeID>;    // these need external handles

public:
  explicit LocalizedKWayFM(const Context& context,
                           const HypernodeID numNodes,
                           FMSharedData& sharedData,
                           GainCache& gainCache) :
    context(context),
    thisSearch(0),
    deltaPhg(context),
    neighborDeduplicator(PartitionedHypergraph::is_graph ? 0 : numNodes, 0),
    gain_cache(gainCache),
    delta_gain_cache(gainCache),
    sharedData(sharedData),
    blockPQ(static_cast<size_t>(context.partition.k)),
    vertexPQs(static_cast<size_t>(context.partition.k),
      VertexPriorityQueue(sharedData.vertexPQHandles.data(), sharedData.numberOfNodes)) {
    const bool top_level = context.type == ContextType::main;
    delta_gain_cache.initialize(top_level ? MAP_SIZE_LARGE : MAP_SIZE_MOVE_DELTA);
  }

  template<typename DispatchedFMStrategy>
  MT_KAHYPAR_ATTRIBUTE_ALWAYS_INLINE DispatchedFMStrategy initializeDispatchedStrategy() {
    return DispatchedFMStrategy(context, sharedData, blockPQ, vertexPQs);
  }

  template<typename DispatchedFMStrategy>
  bool findMoves(DispatchedFMStrategy& fm_strategy, PartitionedHypergraph& phg, size_t taskID, size_t numSeeds);

  void memoryConsumption(utils::MemoryTreeNode* parent) const;

  void changeNumberOfBlocks(const PartitionID new_k);

private:
  template<typename DispatchedFMStrategy>
  void internalFindMoves(PartitionedHypergraph& phg, DispatchedFMStrategy& fm_strategy);

  template<bool has_fixed_vertices, typename PHG, typename CACHE, typename DispatchedFMStrategy>
  MT_KAHYPAR_ATTRIBUTE_ALWAYS_INLINE
  void acquireOrUpdateNeighbors(PHG& phg, CACHE& gain_cache, const Move& move, DispatchedFMStrategy& fm_strategy);


 private:

  const Context& context;

  // ! Unique search id associated with the current local search
  SearchID thisSearch;

  // ! Local data members required for one localized search run
  //FMLocalData localData;
  vec< std::pair<Move, MoveID> > localMoves;

  // ! Wrapper around the global partitioned hypergraph, that allows
  // ! to perform moves non-visible for other local searches
  DeltaPartitionedHypergraph deltaPhg;

  // ! Used after a move. Stores whether a neighbor of the just moved vertex has already been updated.
  vec<HypernodeID> neighborDeduplicator;
  HypernodeID deduplicationTime = 1;

  // ! Stores hyperedges whose pins's gains may have changed after vertex move
  vec<HyperedgeID> edgesWithGainChanges;

  GainCache& gain_cache;

  DeltaGainCache delta_gain_cache;

  FMSharedData& sharedData;

  // ! Priority Queue that contains for each block of the partition
  // ! the vertex with the best gain value
  BlockPriorityQueue blockPQ;

  // ! From PQs -> For each block it contains the vertices (contained
  // ! in that block) touched by the current local search associated
  // ! with their gain values
  vec<VertexPriorityQueue> vertexPQs;
};

}
