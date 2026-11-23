/*******************************************************************************
 * MIT License
 *
 * This file is part of Mt-KaHyPar.
 *
 * Copyright (C) 2023 Lars Gottesbüren <lars.gottesbueren@kit.edu>
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

#include "repcut_serial.h"

#include <atomic>

#include "mt-kahypar/datastructures/priority_queue.h"
#include "mt-kahypar/partition/context.h"
#include "mt-kahypar/partition/metrics.h"
#include "mt-kahypar/partition/refinement/i_refiner.h"
#include "mt-kahypar/partition/refinement/i_rebalancer.h"
#include "mt-kahypar/partition/refinement/gains/gain_cache_ptr.h"
#include "mt-kahypar/partition/refinement/rebalancing/repair_empty_blocks.h"

namespace mt_kahypar {

namespace rebalancer {
  struct GuardedPQ {
    GuardedPQ(PosT *handles, size_t num_nodes) : pq(handles, num_nodes) { }
    SpinLock lock;
    ds::MaxHeap<float, HypernodeID> pq;
    float top_key = std::numeric_limits<float>::lowest();
    void reset() {
      pq.clear();
      top_key = std::numeric_limits<float>::lowest();
    }
  };

  struct NodeState {
    uint8_t state = 0;

    bool canMove() const { return state == 1; }

    bool isLocked() const { return state == 2; }

    bool wasMoved() const { return state == 3; }

    // Returns true if the node is marked as movable, is not locked and taking the lock now succeeds
    bool tryLock() {
      uint8_t expected = 1;
      return state == 1 && repcut_serial::Ref(state)
          .compare_exchange_strong(expected, 2, std::memory_order_acquire, std::memory_order_relaxed);
    }

    void unlock() { repcut_serial::Ref(state).store(1, std::memory_order_release); }

    void markAsMovedAndUnlock() { repcut_serial::Ref(state).store(3, std::memory_order_release); }

    void markAsMovable() { state = 1; }

    void reset() { state = 0; }
  };

} // namespace rebalancer


template <typename GraphAndGainTypes>
class AdvancedRebalancer final : public IRebalancer {
private:
  using PartitionedHypergraph = typename GraphAndGainTypes::PartitionedHypergraph;
  using GainCache = typename GraphAndGainTypes::GainCache;
  using GainCalculator = typename GraphAndGainTypes::GainComputation;
  using AttributedGains = typename GraphAndGainTypes::AttributedGains;

  static constexpr bool debug = false;
  static constexpr bool enable_heavy_assert = false;

public:

  explicit AdvancedRebalancer(HypernodeID num_nodes,
                        const Context& context,
                        GainCache& gain_cache);

  explicit AdvancedRebalancer(HypernodeID num_nodes,
                        const Context& context,
                        gain_cache_t gain_cache);

private:
  bool refineImpl(mt_kahypar_partitioned_hypergraph_t& hypergraph,
                  const vec<HypernodeID>& refinement_nodes,
                  Metrics& best_metrics,
                  double);

  void initializeImpl(mt_kahypar_partitioned_hypergraph_t& hypergraph) final;

  bool refineAndOutputMovesImpl(mt_kahypar_partitioned_hypergraph_t& hypergraph,
                                const vec<HypernodeID>& refinement_nodes,
                                vec<vec<Move>>& moves_by_part,
                                Metrics& best_metrics,
                                const double);

  bool refineAndOutputMovesLinearImpl(mt_kahypar_partitioned_hypergraph_t& hypergraph,
                                      const vec<HypernodeID>& refinement_nodes,
                                      vec<Move>& moves,
                                      Metrics& best_metrics,
                                      const double);

  bool refineInternalParallel(mt_kahypar_partitioned_hypergraph_t& hypergraph,
                              vec<vec<Move>>* moves_by_part,
                              vec<Move>* moves_linear,
                              Metrics& best_metric);


  void insertNodesInOverloadedBlocks(mt_kahypar_partitioned_hypergraph_t& hypergraph);

  void findMoves(mt_kahypar_partitioned_hypergraph_t& hypergraph, int64_t& attributed_gain, size_t& global_move_id);

  const Context& _context;
  GainCache& _gain_cache;
  PartitionID _current_k;
  GainCalculator _gain;

  ds::Array<Move> _moves;
  vec<rebalancer::GuardedPQ> _pqs;
  vec<PartitionID> _overloaded_blocks;
  vec<uint8_t> _is_overloaded;
  ds::Array<PartitionID> _target_part;
  ds::Array<PosT> _pq_handles;
  ds::Array<int> _pq_id;
  ds::Array<rebalancer::NodeState> _node_state;
  RepairEmptyBlocks<GraphAndGainTypes> _repair_empty_blocks;
};

}  // namespace mt_kahypar
