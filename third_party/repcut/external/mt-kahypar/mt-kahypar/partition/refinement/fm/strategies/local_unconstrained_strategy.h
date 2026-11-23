/*******************************************************************************
 * MIT License
 *
 * This file is part of Mt-KaHyPar.
 *
 * Copyright (C) 2023 Nikolai Maas <nikolai.maas@kit.edu>
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

#include <array>

#include "mt-kahypar/datastructures/sparse_map.h"
#include "mt-kahypar/partition/refinement/fm/fm_commons.h"


namespace mt_kahypar {

  /*
   * LocalFMStrategy interface
   * static constexpr bool uses_gain_cache
   * static constexpr bool maintain_gain_cache_between_rounds
   * static constexpr bool is_unconstrained
   *
   * Constructor(context, sharedData, blockPQ, vertexPQs, runStats)
   * insertIntoPQ(phg, gain_cache, node)
   * updateGain(phg, gain_cache, node, move)
   * findNextMove(phg, gain_cache, move)
   * applyMove(phg, gain_cache, move)
   * reset()
   * deltaGainUpdates(phg, gain_cache, sync_update)
   *
   */

class LocalUnconstrainedStrategy {
  using VirtualWeightMap = ds::SparseMap<PartitionID, HypernodeWeight>;

 public:
  using BlockPriorityQueue = ds::ExclusiveHandleHeap< ds::MaxHeap<Gain, PartitionID> >;
  using VertexPriorityQueue = ds::MaxHeap<Gain, HypernodeID>;    // these need external handles

  static constexpr bool uses_gain_cache = true;
  static constexpr bool maintain_gain_cache_between_rounds = true;
  static constexpr bool is_unconstrained = true;

  LocalUnconstrainedStrategy(const Context& context,
                             FMSharedData& sharedData,
                             BlockPriorityQueue& blockPQ,
                             vec<VertexPriorityQueue>& vertexPQs) :
      context(context),
      sharedData(sharedData),
      blockPQ(blockPQ),
      vertexPQs(vertexPQs),
      localVirtualWeightDelta(context.partition.k),
      penaltyFactor(context.refinement.fm.imbalance_penalty_max),
      upperBound(context.refinement.fm.unconstrained_upper_bound) { }

  template<typename PartitionedHypergraph, typename GainCache>
  MT_KAHYPAR_ATTRIBUTE_ALWAYS_INLINE
  void insertIntoPQ(const PartitionedHypergraph& phg,
                    const GainCache& gain_cache,
                    const HypernodeID v) {
    const PartitionID pv = phg.partID(v);
    ASSERT(pv < context.partition.k);
    auto [target, gain] = computeBestTargetBlock(phg, gain_cache, v, pv);
    ASSERT(target < context.partition.k);
    sharedData.targetPart[v] = target;
    vertexPQs[pv].insert(v, gain);  // blockPQ updates are done later, collectively.
  }

  template<typename PartitionedHypergraph, typename GainCache>
  MT_KAHYPAR_ATTRIBUTE_ALWAYS_INLINE
  void updateGain(const PartitionedHypergraph& phg,
                  const GainCache& gain_cache,
                  const HypernodeID v,
                  const Move& move) {
    const PartitionID pv = phg.partID(v);
    ASSERT(vertexPQs[pv].contains(v));
    const PartitionID designatedTargetV = sharedData.targetPart[v];
    Gain gain = 0;
    PartitionID newTarget = kInvalidPartition;

    if (context.partition.k < 4 || designatedTargetV == move.from || designatedTargetV == move.to) {
      // penalty term of designatedTargetV is affected.
      // and may now be greater than that of other blocks --> recompute full
      std::tie(newTarget, gain) = computeBestTargetBlock(phg, gain_cache, v, pv);
    } else {
      // penalty term of designatedTargetV is not affected.
      // only move.from and move.to may be better
      std::tie(newTarget, gain) = bestOfThree(phg, gain_cache,
        v, pv, { designatedTargetV, move.from, move.to });
    }

    sharedData.targetPart[v] = newTarget;
    vertexPQs[pv].adjustKey(v, gain);
  }

  template<typename PartitionedHypergraph, typename GainCache>
  MT_KAHYPAR_ATTRIBUTE_ALWAYS_INLINE
  bool findNextMove(const PartitionedHypergraph& phg,
                    const GainCache& gain_cache,
                    Move& m) {
    updatePQs();

    if (blockPQ.empty()) {
      return false;
    }

    while (true) {
      const PartitionID from = blockPQ.top();
      const HypernodeID u = vertexPQs[from].top();
      const Gain estimated_gain = vertexPQs[from].topKey();
      ASSERT(estimated_gain == blockPQ.topKey());
      auto [to, gain] = computeBestTargetBlock(phg, gain_cache, u, phg.partID(u));

      bool apply_move = (gain >= estimated_gain); // accept any gain that is at least as good
      if (apply_move && to != kInvalidPartition && penaltyFactor > 0) {
        const HypernodeWeight wu = phg.nodeWeight(u);
        const HypernodeWeight to_weight = phg.partWeight(to);
        if (upperBound >= 1 && to_weight + wu > upperBound * context.partition.max_part_weights[to]) {
          apply_move = false;
        } else if (to_weight + wu > context.partition.max_part_weights[to]) {
          const Gain imbalance_penalty = estimatePenalty(to, to_weight, wu);
          if (imbalance_penalty != std::numeric_limits<Gain>::max()) {
            Gain new_gain = gain_cache.gain(u, from, to) - std::ceil(penaltyFactor * imbalance_penalty);
            gain = new_gain;
          } else {
            apply_move = false;
          }
        }
      }

      if (apply_move) {
        m.node = u; m.to = to; m.from = from;
        m.gain = gain;
        vertexPQs[from].deleteTop();  // blockPQ updates are done later, collectively.
        return true;
      } else {
        vertexPQs[from].adjustKey(u, gain);
        sharedData.targetPart[u] = to;
        if (vertexPQs[from].topKey() != blockPQ.keyOf(from)) {
          blockPQ.adjustKey(from, vertexPQs[from].topKey());
        }
      }
    }
  }

  template<typename PartitionedHypergraph, typename GainCache>
  MT_KAHYPAR_ATTRIBUTE_ALWAYS_INLINE
  void applyMove(const PartitionedHypergraph& phg, const GainCache&, Move m) {
    if (sharedData.unconstrained.isRebalancingNode(m.node)) {
      // If a node is moved which is already in use for penalty estimation, we need to make
      // an adjustment so future estimations are not overly optimistic (since in reality, the
      // node is not available anymore). This is achieved by increasing the "virtual" weight of
      // the origin block, thus pessimizing future estimations
      localVirtualWeightDelta[m.from] += phg.nodeWeight(m.node);
    }
  }

  MT_KAHYPAR_ATTRIBUTE_ALWAYS_INLINE
  void flushLocalChanges() {
    for (auto [block, delta]: localVirtualWeightDelta) {
      ASSERT(delta >= 0);
      sharedData.unconstrained.virtualWeightDelta(block).fetch_add(delta, std::memory_order_relaxed);
    }
    localVirtualWeightDelta.clear();
  }

  void reset() {
    // release all nodes that were not moved
    if (sharedData.release_nodes) {
      // Release all nodes contained in PQ
      for (PartitionID i = 0; i < context.partition.k; ++i) {
        for (PosT j = 0; j < vertexPQs[i].size(); ++j) {
          const HypernodeID v = vertexPQs[i].at(j);
          sharedData.nodeTracker.releaseNode(v);
        }
      }
    }

    for (PartitionID i = 0; i < context.partition.k; ++i) {
      vertexPQs[i].clear();
    }
    blockPQ.clear();
    localVirtualWeightDelta.clear();
  }


  // We're letting the FM details implementation decide what happens here, since some may not want to do gain cache updates,
  // but rather update gains in their PQs or something
  template<typename PartitionedHypergraph, typename GainCache>
  MT_KAHYPAR_ATTRIBUTE_ALWAYS_INLINE
  void deltaGainUpdates(PartitionedHypergraph& phg,
                        GainCache& gain_cache,
                        const SynchronizedEdgeUpdate& sync_update) {
    gain_cache.deltaGainUpdate(phg, sync_update);
  }

  void setPenaltyFactor(double penalty) {
    ASSERT(penalty >= 0 && penalty <= 1);
    penaltyFactor = penalty;
  }

  void setUpperBound(double upper_bound) {
    upperBound = upper_bound;
  }

private:
  MT_KAHYPAR_ATTRIBUTE_ALWAYS_INLINE
  void updatePQs() {
    for (PartitionID i = 0; i < context.partition.k; ++i) {
      if (!vertexPQs[i].empty()) {
        blockPQ.insertOrAdjustKey(i, vertexPQs[i].topKey());
      } else if (blockPQ.contains(i)) {
        blockPQ.remove(i);
      }
    }
  }

  template<typename PartitionedHypergraph, typename GainCache>
  MT_KAHYPAR_ATTRIBUTE_ALWAYS_INLINE
  std::pair<PartitionID, HyperedgeWeight> computeBestTargetBlock(const PartitionedHypergraph& phg,
                                                                 const GainCache& gain_cache,
                                                                 const HypernodeID u,
                                                                 const PartitionID from) const {
    const HypernodeWeight wu = phg.nodeWeight(u);
    const HypernodeWeight from_weight = phg.partWeight(from);
    PartitionID to = kInvalidPartition;
    HyperedgeWeight to_benefit = std::numeric_limits<HyperedgeWeight>::min();
    HypernodeWeight best_to_weight = from_weight - wu;
    for ( const PartitionID& i : gain_cache.adjacentBlocks(u) ) {
      if (i != from) {
        const HypernodeWeight to_weight = phg.partWeight(i);
        const HypernodeWeight max_weight = context.partition.max_part_weights[i];
        HyperedgeWeight benefit = gain_cache.benefitTerm(u, i);
        if (upperBound >= 1 && to_weight + wu > upperBound * max_weight) {
          continue;
        } else if (to_weight + wu > max_weight && benefit <= to_benefit) {
          // don't take imbalanced move without improved gain
          continue;
        } else if (to_weight + wu > max_weight && penaltyFactor > 0) {
          const Gain imbalance_penalty = estimatePenalty(i, to_weight, wu);
          if (imbalance_penalty == std::numeric_limits<Gain>::max()) {
            continue;
          }
          benefit -= std::ceil(penaltyFactor * imbalance_penalty);
        }
        if ( benefit > to_benefit || ( benefit == to_benefit && to_weight < best_to_weight ) ) {
          to_benefit = benefit;
          to = i;
          best_to_weight = to_weight;
        }
      }
    }
    ASSERT(from == phg.partID(u));
    const Gain gain = to != kInvalidPartition ? to_benefit - gain_cache.penaltyTerm(u, from)
                                              : std::numeric_limits<HyperedgeWeight>::min();
    return std::make_pair(to, gain);
  }

  template<typename PartitionedHypergraph, typename GainCache>
  MT_KAHYPAR_ATTRIBUTE_ALWAYS_INLINE
  std::pair<PartitionID, HyperedgeWeight> bestOfThree(const PartitionedHypergraph& phg,
                                                      const GainCache& gain_cache,
                                                      HypernodeID u,
                                                      PartitionID from,
                                                      std::array<PartitionID, 3> parts) const {
    const PartitionID designatedTargetU = sharedData.targetPart[u];
    const HypernodeWeight wu = phg.nodeWeight(u);
    const HypernodeWeight from_weight = phg.partWeight(from);
    PartitionID to = kInvalidPartition;
    HyperedgeWeight to_benefit = std::numeric_limits<HyperedgeWeight>::min();
    HypernodeWeight best_to_weight = from_weight - wu;
    for (PartitionID i : parts) {
      if (i != from && i != kInvalidPartition) {
        const HypernodeWeight to_weight = phg.partWeight(i);
        HyperedgeWeight benefit = gain_cache.benefitTerm(u, i);
        if (upperBound >= 1 && to_weight + wu > upperBound * context.partition.max_part_weights[i]) {
          continue;
        } else if (to_weight + wu > context.partition.max_part_weights[i] && penaltyFactor > 0) {
          const Gain imbalance_penalty = estimatePenalty(i, to_weight, wu);
          if (imbalance_penalty == std::numeric_limits<Gain>::max()) {
            if (i == designatedTargetU) {
              // Edge case: the cached target block for u is overloaded (infinite penalty) and no longer valid.
              // We need to check all blocks, since otherwise the updated node might get a very low priority.
              // Note: Since the penalties increase monotonically during a round, this can happen at most once
              // for each target part of a node
              return computeBestTargetBlock(phg, gain_cache, u, from);
            }
            continue;
          }
          benefit -= std::ceil(penaltyFactor * imbalance_penalty);
        }
        if ( benefit > to_benefit || ( benefit == to_benefit && to_weight < best_to_weight ) ) {
          to_benefit = benefit;
          to = i;
          best_to_weight = to_weight;
        }
      }
    }
    ASSERT(from == phg.partID(u));
    const Gain gain = to != kInvalidPartition ? to_benefit - gain_cache.penaltyTerm(u, from)
                                              : std::numeric_limits<HyperedgeWeight>::min();
    return std::make_pair(to, gain);
  }

  MT_KAHYPAR_ATTRIBUTE_ALWAYS_INLINE
  Gain estimatePenalty(PartitionID to, HypernodeWeight to_weight, HypernodeWeight wu) const {
    HypernodeWeight virtual_delta = sharedData.unconstrained.virtualWeightDelta(to).load(std::memory_order_relaxed)
                                    + localVirtualWeightDelta.getOrDefault(to);
    HypernodeWeight initial_imbalance = to_weight + virtual_delta - context.partition.max_part_weights[to];
    return sharedData.unconstrained.estimatePenaltyForImbalancedMove(to, initial_imbalance, wu);
  }

  const Context& context;

  FMSharedData& sharedData;

  // ! Priority Queue that contains for each block of the partition
  // ! the vertex with the best gain value
  BlockPriorityQueue& blockPQ;

  // ! From PQs -> For each block it contains the vertices (contained
  // ! in that block) touched by the current local search associated
  // ! with their gain values
  vec<VertexPriorityQueue>& vertexPQs;

  // ! Virtual block weights are saved as delta to the actual block weight. They
  // ! are necessary to ensure a reasonable penalty estimation in some edge cases.
  VirtualWeightMap localVirtualWeightDelta;

  double penaltyFactor;
  double upperBound;
};

}
