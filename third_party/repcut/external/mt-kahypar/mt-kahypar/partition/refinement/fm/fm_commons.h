/*******************************************************************************
 * MIT License
 *
 * This file is part of Mt-KaHyPar.
 *
 * Copyright (C) 2020 Lars Gottesbüren <lars.gottesbueren@kit.edu>
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

#include <limits>

#include <tbb/enumerable_thread_specific.h>
#include <tbb/parallel_for.h>
#include <tbb/task_group.h>

#include "kahypar-resources/datastructure/fast_reset_flag_array.h"

#include "mt-kahypar/datastructures/concurrent_bucket_map.h"
#include "mt-kahypar/datastructures/priority_queue.h"
#include "mt-kahypar/partition/context.h"
#include "mt-kahypar/partition/refinement/fm/strategies/i_fm_strategy.h"
#include "mt-kahypar/parallel/thread_management.h"
#include "mt-kahypar/parallel/work_stack.h"
#include "mt-kahypar/utils/cast.h"

namespace mt_kahypar {


struct GlobalMoveTracker {
  vec<Move> moveOrder;
  vec<MoveID> moveOfNode;
  CAtomic<MoveID> runningMoveID;
  MoveID firstMoveID = 1;

  explicit GlobalMoveTracker(size_t numNodes = 0) :
          moveOrder(numNodes),
          moveOfNode(numNodes, 0),
          runningMoveID(1) { }

  // Returns true if stored move IDs should be reset
  bool reset() {
    if (runningMoveID.load() >= std::numeric_limits<MoveID>::max() - moveOrder.size() - 20) {
      tbb::parallel_for(UL(0), moveOfNode.size(), [&](size_t i) { moveOfNode[i] = 0; }, tbb::static_partitioner());
      firstMoveID = 1;
      runningMoveID.store(1);
      return true;
    } else {
      firstMoveID = ++runningMoveID;
      return false;
    }
  }

  MoveID insertMove(const Move &m) {
    const MoveID move_id = runningMoveID.fetch_add(1, std::memory_order_relaxed);
    assert(move_id - firstMoveID < moveOrder.size());
    moveOrder[move_id - firstMoveID] = m;
    moveOfNode[m.node] = move_id;
    return move_id;
  }

  Move& getMove(MoveID move_id) {
    assert(move_id - firstMoveID < moveOrder.size());
    return moveOrder[move_id - firstMoveID];
  }

  bool wasNodeMovedInThisRound(HypernodeID u) const {
    const MoveID m_id = moveOfNode[u];
    if (m_id >= firstMoveID && m_id < runningMoveID.load(std::memory_order_relaxed)) {   // active move ID
      ASSERT(moveOrder[m_id - firstMoveID].node == u);
      return moveOrder[m_id - firstMoveID].isValid();  // not reverted already
    }
    return false;
  }

  MoveID numPerformedMoves() const {
    return runningMoveID.load(std::memory_order_relaxed) - firstMoveID;
  }

  bool isMoveStale(const MoveID move_id) const {
    return move_id < firstMoveID;
  }
};

struct NodeTracker {
  vec<CAtomic<SearchID>> searchOfNode;

  SearchID releasedMarker = 1;
  SearchID deactivatedNodeMarker = 2;
  CAtomic<SearchID> highestActiveSearchID { 2 };

  explicit NodeTracker(size_t numNodes = 0) : searchOfNode(numNodes, CAtomic<SearchID>(0)) { }

  // only the search that owns u is allowed to call this
  void deactivateNode(HypernodeID u, SearchID search_id) {
    assert(searchOfNode[u].load() == search_id);
    unused(search_id);
    searchOfNode[u].store(deactivatedNodeMarker, std::memory_order_release);
  }

  bool isLocked(HypernodeID u) {
    return searchOfNode[u].load(std::memory_order_relaxed) == deactivatedNodeMarker;
  }

  void releaseNode(HypernodeID u) {
    searchOfNode[u].store(releasedMarker, std::memory_order_release);
  }

  bool isSearchInactive(SearchID search_id) const {
    return search_id < deactivatedNodeMarker;
  }

  bool canNodeStartNewSearch(HypernodeID u) const {
    return isSearchInactive( searchOfNode[u].load(std::memory_order_relaxed) );
  }

  bool tryAcquireNode(HypernodeID u, SearchID new_search) {
    SearchID current_search = searchOfNode[u].load(std::memory_order_relaxed);
    return isSearchInactive(current_search)
            && searchOfNode[u].compare_exchange_strong(current_search, new_search, std::memory_order_acq_rel);
  }

  void requestNewSearches(SearchID max_num_searches) {
    if (highestActiveSearchID.load(std::memory_order_relaxed) >= std::numeric_limits<SearchID>::max() - max_num_searches - 20) {
      tbb::parallel_for(UL(0), searchOfNode.size(), [&](const size_t i) {
        searchOfNode[i].store(0, std::memory_order_relaxed);
      });
      highestActiveSearchID.store(1, std::memory_order_relaxed);
    }
    deactivatedNodeMarker = ++highestActiveSearchID;
    releasedMarker = deactivatedNodeMarker - 1;
  }
};


// Contains data required for unconstrained FM: We group non-border nodes in buckets based on their
// incident weight to node weight ratio. This allows to give a (pessimistic) estimate of the effective
// gain for moves that violate the balance constraint
class UnconstrainedFMData {
  using AtomicWeight = parallel::IntegralAtomicWrapper<HypernodeWeight>;
  using BucketID = uint32_t;
  using AtomicBucketID = parallel::IntegralAtomicWrapper<BucketID>;

  template<typename GraphAndGainTypes>
  class InitializationHelper {
   public:
    static void initialize(UnconstrainedFMData& data, const Context& context,
                           const typename GraphAndGainTypes::PartitionedHypergraph& phg,
                           const typename GraphAndGainTypes::GainCache& gain_cache);
  };

  static constexpr BucketID NUM_BUCKETS = 16;
  static constexpr double BUCKET_FACTOR = 1.5;
  static constexpr double FALLBACK_TRESHOLD = 0.75;

 public:
  explicit UnconstrainedFMData(HypernodeID num_nodes):
    initialized(false),
    current_k(0),
    bucket_weights(),
    virtual_weight_delta(),
    local_bucket_weights(),
    rebalancing_nodes(num_nodes) { }

  template<typename GraphAndGainTypes>
  void initialize(const Context& context,
                  const typename GraphAndGainTypes::PartitionedHypergraph& phg,
                  const typename GraphAndGainTypes::GainCache& gain_cache) {
    changeNumberOfBlocks(context.partition.k);
    reset();

    InitializationHelper<GraphAndGainTypes>::initialize(*this, context, phg, gain_cache);
  }

  Gain estimatePenaltyForImbalancedMove(PartitionID to, HypernodeWeight initial_imbalance, HypernodeWeight moved_weight) const;

  AtomicWeight& virtualWeightDelta(PartitionID block) {
    ASSERT(block >= 0 && static_cast<size_t>(block) < virtual_weight_delta.size());
    return virtual_weight_delta[block];
  }

  bool isRebalancingNode(HypernodeID hn) const {
    return initialized && rebalancing_nodes[hn];
  }

  void reset();

  void changeNumberOfBlocks(PartitionID new_k) {
    if (new_k != current_k) {
      current_k = new_k;
      local_bucket_weights = tbb::enumerable_thread_specific<vec<HypernodeWeight>>(new_k * NUM_BUCKETS);
      initialized = false;
    }
  }

 private:
  template<typename GraphAndGainTypes>
  friend class InitializationHelper;

  MT_KAHYPAR_ATTRIBUTE_ALWAYS_INLINE size_t indexForBucket(PartitionID block, BucketID bucketId) const {
    ASSERT(bucketId < NUM_BUCKETS && block * NUM_BUCKETS + bucketId < bucket_weights.size());
    return block * NUM_BUCKETS + bucketId;
  }

  // upper bound of gain values in bucket
  static double gainPerWeightForBucket(BucketID bucketId) {
    if (bucketId > 1) {
      return std::pow(BUCKET_FACTOR, bucketId - 2);
    } else if (bucketId == 1) {
      return 0.5;
    } else {
      return 0;
    }
  }

  static BucketID bucketForGainPerWeight(double gainPerWeight) {
    if (gainPerWeight >= 1) {
      return 2 + std::ceil(std::log(gainPerWeight) / std::log(BUCKET_FACTOR));
    } else if (gainPerWeight > 0.5) {
      return 2;
    } else if (gainPerWeight > 0) {
      return 1;
    } else {
      return 0;
    }
  }

  bool initialized = false;
  PartitionID current_k;
  parallel::scalable_vector<HypernodeWeight> bucket_weights;
  parallel::scalable_vector<AtomicWeight> virtual_weight_delta;
  tbb::enumerable_thread_specific<parallel::scalable_vector<HypernodeWeight>> local_bucket_weights;
  parallel::scalable_vector<parallel::scalable_vector<HypernodeWeight>> fallback_bucket_weights;
  kahypar::ds::FastResetFlagArray<> rebalancing_nodes;
};


struct FMSharedData {
  // ! Number of Nodes
  size_t numberOfNodes;

  // ! Nodes to initialize the localized FM searches with
  WorkContainer<HypernodeID> refinementNodes;

  // ! PQ handles shared by all threads (each vertex is only held by one thread)
  vec<PosT> vertexPQHandles;

  // ! Stores the sequence of performed moves and assigns IDs to moves that can be used in the global rollback code
  GlobalMoveTracker moveTracker;

  // ! Tracks the current search of a node, and if a node can still be added to an active search
  NodeTracker nodeTracker;

  // ! Stores the designated target part of a vertex, i.e. the part with the highest gain to which moving is feasible
  vec<PartitionID> targetPart;

  // ! Additional data for unconstrained FM algorithm
  UnconstrainedFMData unconstrained;

  // ! Stop parallel refinement if finishedTasks > finishedTasksLimit to avoid long-running single searches
  CAtomic<size_t> finishedTasks;
  size_t finishedTasksLimit = std::numeric_limits<size_t>::max();

  bool release_nodes = true;

  FMSharedData(size_t numNodes, size_t numThreads) :
    numberOfNodes(numNodes),
    refinementNodes(), //numNodes, numThreads),
    vertexPQHandles(), //numPQHandles, invalid_position),
    moveTracker(), //numNodes),
    nodeTracker(), //numNodes),
    targetPart(),
    unconstrained(numNodes) {
    finishedTasks.store(0, std::memory_order_relaxed);

    tbb::parallel_invoke([&] {
      moveTracker.moveOrder.resize(numNodes);
    }, [&] {
      moveTracker.moveOfNode.resize(numNodes);
    }, [&] {
      nodeTracker.searchOfNode.resize(numNodes, CAtomic<SearchID>(0));
    }, [&] {
      vertexPQHandles.resize(numNodes, invalid_position);
    }, [&] {
      refinementNodes.tls_queues.resize(numThreads);
    }, [&] {
      targetPart.resize(numNodes, kInvalidPartition);
    });
  }

  FMSharedData(size_t numNodes) :
    FMSharedData(
      numNodes,
      parallel::total_number_of_threads())  { }

  FMSharedData() :
    FMSharedData(0, 0) { }

  void memoryConsumption(utils::MemoryTreeNode* parent) const {
    ASSERT(parent);

    utils::MemoryTreeNode* shared_fm_data_node = parent->addChild("Shared FM Data");

    utils::MemoryTreeNode* pq_handles_node = shared_fm_data_node->addChild("PQ Handles");
    pq_handles_node->updateSize(vertexPQHandles.capacity() * sizeof(PosT));
    utils::MemoryTreeNode* move_tracker_node = shared_fm_data_node->addChild("Move Tracker");
    move_tracker_node->updateSize(moveTracker.moveOrder.capacity() * sizeof(Move) +
                                  moveTracker.moveOfNode.capacity() * sizeof(MoveID));
    utils::MemoryTreeNode* node_tracker_node = shared_fm_data_node->addChild("Node Tracker");
    node_tracker_node->updateSize(nodeTracker.searchOfNode.capacity() * sizeof(SearchID));
    refinementNodes.memoryConsumption(shared_fm_data_node);
  }
};


namespace utils {
// compare cast.h
template<typename LocalFM>
localized_k_way_fm_t localized_fm_cast(tbb::enumerable_thread_specific<LocalFM>& local_fm) {
  return localized_k_way_fm_t {
    reinterpret_cast<localized_k_way_fm_s*>(&local_fm), LocalFM::PartitionedHypergraph::TYPE };
}

template<typename LocalFM>
tbb::enumerable_thread_specific<LocalFM>& cast(localized_k_way_fm_t fm) {
  if ( LocalFM::PartitionedHypergraph::TYPE != fm.type ) {
    ERR("Cannot cast local FM [" << typeToString(fm.type) << " to "
        << typeToString(LocalFM::PartitionedHypergraph::TYPE) << "]");
  }
  return *reinterpret_cast<tbb::enumerable_thread_specific<LocalFM>*>(fm.local_fm);
}

} // namespace utils

template<typename FMStrategy>
MT_KAHYPAR_ATTRIBUTE_ALWAYS_INLINE
void findMovesWithConcreteStrategy(FMStrategy& strategy, FMSharedData& sharedData, localized_k_way_fm_t local_fm,
                                   mt_kahypar_partitioned_hypergraph_t& hypergraph, size_t num_tasks, size_t num_seeds, size_t round) {
  using LocalFM = typename FMStrategy::LocalFM;
  using PartitionedHypergraph = typename FMStrategy::PartitionedHypergraph;

  tbb::enumerable_thread_specific<LocalFM>& ets_fm = utils::cast<LocalFM>(local_fm);
  PartitionedHypergraph& phg = utils::cast<PartitionedHypergraph>(hypergraph);
  tbb::task_group tg;

  auto task = [&](const size_t task_id) {
    LocalFM& fm = ets_fm.local();
    while(sharedData.finishedTasks.load(std::memory_order_relaxed) < sharedData.finishedTasksLimit
          && strategy.dispatchedFindMoves(fm, phg, task_id, num_seeds, round)) { /* keep running*/ }
    sharedData.finishedTasks.fetch_add(1, std::memory_order_relaxed);
  };
  for (size_t i = 0; i < num_tasks; ++i) {
    tg.run(std::bind(task, i));
  }
  tg.wait();
}

}
