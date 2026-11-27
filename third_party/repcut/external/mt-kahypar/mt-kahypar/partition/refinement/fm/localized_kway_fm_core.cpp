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

#include "mt-kahypar/partition/refinement/fm/localized_kway_fm_core.h"

#include "mt-kahypar/definitions.h"
#include "mt-kahypar/partition/refinement/gains/gain_definitions.h"
#include "mt-kahypar/partition/refinement/fm/strategies/gain_cache_strategy.h"
#include "mt-kahypar/partition/refinement/fm/strategies/unconstrained_strategy.h"

namespace mt_kahypar {

  template<typename GraphAndGainTypes>
  template<typename DispatchedFMStrategy>
  bool LocalizedKWayFM<GraphAndGainTypes>::findMoves(DispatchedFMStrategy& fm_strategy, PartitionedHypergraph& phg,
                                                  size_t taskID, size_t numSeeds) {
    localMoves.clear();
    thisSearch = ++sharedData.nodeTracker.highestActiveSearchID;

    HypernodeID seedNode;
    HypernodeID pushes = 0;
    while (pushes < numSeeds && sharedData.refinementNodes.try_pop(seedNode, taskID)) {
      if (sharedData.nodeTracker.tryAcquireNode(seedNode, thisSearch)) {
        fm_strategy.insertIntoPQ(phg, gain_cache, seedNode);
        pushes++;
      }
    }

    if (pushes > 0) {
      deltaPhg.clear();
      deltaPhg.setPartitionedHypergraph(&phg);
      delta_gain_cache.clear();
      internalFindMoves(phg, fm_strategy);
      return true;
    } else {
      return false;
    }
  }

  template<typename Partition>
  MT_KAHYPAR_ATTRIBUTE_ALWAYS_INLINE std::pair<PartitionID, HypernodeWeight>
  heaviestPartAndWeight(const Partition& partition, const PartitionID k) {
    PartitionID p = kInvalidPartition;
    HypernodeWeight w = std::numeric_limits<HypernodeWeight>::min();
    for (PartitionID i = 0; i < k; ++i) {
      if (partition.partWeight(i) > w) {
        w = partition.partWeight(i);
        p = i;
      }
    }
    return std::make_pair(p, w);
  }

  template<typename GraphAndGainTypes>
  template<bool has_fixed_vertices, typename PHG, typename CACHE, typename DispatchedFMStrategy>
  MT_KAHYPAR_ATTRIBUTE_ALWAYS_INLINE
  void LocalizedKWayFM<GraphAndGainTypes>::acquireOrUpdateNeighbors(PHG& phg, CACHE& gain_cache, const Move& move,
                                                                 DispatchedFMStrategy& fm_strategy) {
    auto updateOrAcquire = [&](const HypernodeID v) {
      SearchID searchOfV = sharedData.nodeTracker.searchOfNode[v].load(std::memory_order_acquire);
      if (searchOfV == thisSearch) {
        fm_strategy.updateGain(phg, gain_cache, v, move);
      } else if (sharedData.nodeTracker.tryAcquireNode(v, thisSearch)) {
        fm_strategy.insertIntoPQ(phg, gain_cache, v);
      }
    };

    if constexpr (PartitionedHypergraph::is_graph) {
      // simplified case for graphs: neighbors can't be duplicated
      for (HyperedgeID e : phg.incidentEdges(move.node)) {
        HypernodeID v = phg.edgeTarget(e);
        if ( has_fixed_vertices && phg.isFixed(v) ) continue;

        updateOrAcquire(v);
      }
    } else {
      // Note: only vertices incident to edges with gain changes can become new boundary vertices.
      // Vertices that already were boundary vertices, can still be considered later since they are in the task queue
      for (HyperedgeID e : edgesWithGainChanges) {
        if (phg.edgeSize(e) < context.partition.ignore_hyperedge_size_threshold) {
          for (HypernodeID v : phg.pins(e)) {
            if ( has_fixed_vertices && phg.isFixed(v) ) continue;

            if (neighborDeduplicator[v] != deduplicationTime) {
              updateOrAcquire(v);
              neighborDeduplicator[v] = deduplicationTime;
            }
          }
        }
      }

      if (++deduplicationTime == 0) {
        neighborDeduplicator.assign(neighborDeduplicator.size(), 0);
        deduplicationTime = 1;
      }
    }
  }


  template<typename GraphAndGainTypes>
  template<typename DispatchedFMStrategy>
  void LocalizedKWayFM<GraphAndGainTypes>::internalFindMoves(PartitionedHypergraph& phg,
                                                          DispatchedFMStrategy& fm_strategy) {
    StopRule stopRule(phg.initialNumNodes());
    Move move;

    Gain estimatedImprovement = 0;
    Gain bestImprovement = 0;

    HypernodeWeight heaviestPartWeight = 0;
    HypernodeWeight fromWeight = 0, toWeight = 0;

    while (!stopRule.searchShouldStop()
           && sharedData.finishedTasks.load(std::memory_order_relaxed) < sharedData.finishedTasksLimit) {

      if (!fm_strategy.findNextMove(deltaPhg, delta_gain_cache, move)) break;
      sharedData.nodeTracker.deactivateNode(move.node, thisSearch);

      // skip if no target block available
      if (move.to == kInvalidPartition) {
        continue;
      }

      bool expect_improvement = estimatedImprovement + move.gain > bestImprovement;
      bool high_deg = phg.nodeDegree(move.node) >= PartitionedHypergraph::HIGH_DEGREE_THRESHOLD;

      // skip if high degree (unless it nets actual improvement; but don't apply on deltaPhg then)
      if (!expect_improvement && high_deg) {
        continue;
      }

      edgesWithGainChanges.clear(); // clear before move. delta_func feeds nets of moved vertex.
      MoveID move_id = std::numeric_limits<MoveID>::max();
      bool moved = false;
      const HypernodeWeight allowed_weight = DispatchedFMStrategy::is_unconstrained ? std::numeric_limits<HypernodeWeight>::max()
                                             : context.partition.max_part_weights[move.to];

      heaviestPartWeight = heaviestPartAndWeight(deltaPhg, context.partition.k).second;
      fromWeight = deltaPhg.partWeight(move.from);
      toWeight = deltaPhg.partWeight(move.to);
      if (expect_improvement) {
        // since we will flush the move sequence, don't bother running it through the deltaPhg
        // this is intended to allow moving high deg nodes (blow up hash tables) if they give an improvement.
        // The nets affected by a gain cache update are collected when we apply this improvement on the
        // global partition (used to expand the localized search and update the gain values).
        moved = toWeight + phg.nodeWeight(move.node) <= allowed_weight;
      } else {
        moved = deltaPhg.changeNodePart(move.node, move.from, move.to, allowed_weight,
                                        [&](const SynchronizedEdgeUpdate& sync_update) {
          if (!PartitionedHypergraph::is_graph && GainCache::triggersDeltaGainUpdate(sync_update)) {
            edgesWithGainChanges.push_back(sync_update.he);
          }
          delta_gain_cache.deltaGainUpdate(deltaPhg, sync_update);
        });
        fm_strategy.applyMove(deltaPhg, delta_gain_cache, move);
      }

      if (moved) {
        estimatedImprovement += move.gain;
        localMoves.emplace_back(move, move_id);
        stopRule.update(move.gain);
        bool improved_km1 = estimatedImprovement > bestImprovement;
        bool improved_balance_less_equal_km1 = estimatedImprovement >= bestImprovement
                                                     && fromWeight == heaviestPartWeight
                                                     && toWeight + phg.nodeWeight(move.node) < heaviestPartWeight;
        if (improved_km1 || improved_balance_less_equal_km1) {
          // Apply move sequence to global partition
          for (size_t i = 0; i < localMoves.size(); ++i) {
            const Move& local_move = localMoves[i].first;
            phg.changeNodePart(
                    gain_cache, local_move.node, local_move.from, local_move.to,
                    std::numeric_limits<HypernodeWeight>::max(),
                    [&] { sharedData.moveTracker.insertMove(local_move); },
                    [&](const SynchronizedEdgeUpdate& ) {});
          }
          localMoves.clear();
          fm_strategy.flushLocalChanges();
          stopRule.reset();
          deltaPhg.clear();   // clear hashtables, save memory :)
          delta_gain_cache.clear();
          bestImprovement = estimatedImprovement;
        }

        // no need to update our PQs if we stop anyways
        if (stopRule.searchShouldStop()
              || sharedData.finishedTasks.load(std::memory_order_relaxed) >= sharedData.finishedTasksLimit) {
          break;
        }

        if (phg.hasFixedVertices()) {
          acquireOrUpdateNeighbors<true>(deltaPhg, delta_gain_cache, move, fm_strategy);
        } else {
          acquireOrUpdateNeighbors<false>(deltaPhg, delta_gain_cache, move, fm_strategy);
        }

      }
    }

    fm_strategy.reset();
  }


  template<typename GraphAndGainTypes>
  void LocalizedKWayFM<GraphAndGainTypes>::changeNumberOfBlocks(const PartitionID new_k) {
    deltaPhg.changeNumberOfBlocks(new_k);
    blockPQ.resize(new_k);
    for ( VertexPriorityQueue& pq : vertexPQs ) {
      pq.setHandle(sharedData.vertexPQHandles.data(), sharedData.numberOfNodes);
    }
    while ( static_cast<size_t>(new_k) > vertexPQs.size() ) {
      vertexPQs.emplace_back(sharedData.vertexPQHandles.data(), sharedData.numberOfNodes);
    }
  }

  template<typename GraphAndGainTypes>
  void LocalizedKWayFM<GraphAndGainTypes>::memoryConsumption(utils::MemoryTreeNode *parent) const {
    ASSERT(parent);

    utils::MemoryTreeNode *localized_fm_node = parent->addChild("Localized k-Way FM");

    utils::MemoryTreeNode *deduplicator_node = localized_fm_node->addChild("Deduplicator");
    deduplicator_node->updateSize(neighborDeduplicator.capacity() * sizeof(HypernodeID));
    utils::MemoryTreeNode *edges_to_activate_node = localized_fm_node->addChild("edgesWithGainChanges");
    edges_to_activate_node->updateSize(edgesWithGainChanges.capacity() * sizeof(HyperedgeID));

    size_t vertex_pq_sizes = std::accumulate(
            vertexPQs.begin(), vertexPQs.end(), 0,
            [](size_t init, const VertexPriorityQueue& pq) { return init + pq.size_in_bytes(); }
    );
    localized_fm_node->addChild("PQs", blockPQ.size_in_bytes() + vertex_pq_sizes);

    utils::MemoryTreeNode *local_moves_node = parent->addChild("Local FM Moves");
    local_moves_node->updateSize(localMoves.capacity() * sizeof(std::pair<Move, MoveID>));

    deltaPhg.memoryConsumption(localized_fm_node);
    delta_gain_cache.memoryConsumption(localized_fm_node);
  }

  namespace {
  #define LOCALIZED_KWAY_FM(X) LocalizedKWayFM<X>;                                                      \
    template bool LocalizedKWayFM<X>::findMoves(LocalUnconstrainedStrategy&,                            \
                    typename LocalizedKWayFM<X>::PartitionedHypergraph&, size_t, size_t);               \
    template bool LocalizedKWayFM<X>::findMoves(LocalGainCacheStrategy&,                                \
                    typename LocalizedKWayFM<X>::PartitionedHypergraph&, size_t, size_t)
  }

  INSTANTIATE_CLASS_WITH_VALID_TRAITS(LOCALIZED_KWAY_FM)

}   // namespace mt_kahypar
