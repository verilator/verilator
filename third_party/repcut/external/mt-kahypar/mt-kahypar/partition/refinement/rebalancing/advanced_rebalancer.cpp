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

#include "repcut_serial.h"

#include "mt-kahypar/partition/refinement/rebalancing/advanced_rebalancer.h"

#include <atomic>
#include <array>
#include <optional>
#include <random>

#include "mt-kahypar/partition/refinement/gains/gain_definitions.h"
#include "mt-kahypar/utils/cast.h"
#include "mt-kahypar/partition/context.h"

namespace mt_kahypar {

namespace impl {

  float transformGain(Gain gain_, HypernodeWeight wu) {
    float gain = gain_;
    if (gain > 0) {
      gain *= wu;
    } else if (gain < 0) {
      gain /= wu;
    }
    return gain;
  }

  template<typename PartitionedHypergraph, typename GainCache>
  std::pair<PartitionID, float> computeBestTargetBlock(
          const PartitionedHypergraph& phg, const Context& context, const GainCache& gain_cache,
          HypernodeID u, PartitionID from) {
    const HypernodeWeight wu = phg.nodeWeight(u);
    const HypernodeWeight from_weight = phg.partWeight(from);
    PartitionID to = kInvalidPartition;
    HyperedgeWeight to_benefit = std::numeric_limits<HyperedgeWeight>::min();
    HypernodeWeight best_to_weight = from_weight - wu;
    for (PartitionID i = 0; i < context.partition.k; ++i) {
      if (i != from) {
        const HypernodeWeight to_weight = phg.partWeight(i);
        HyperedgeWeight benefit;
        if (gain_cache.blockIsAdjacent(u, i)) {
          benefit = gain_cache.benefitTerm(u, i);
        } else if (to != kInvalidPartition || to_weight + wu > context.partition.max_part_weights[i]) {
          // skip expensive gain recomputation
          continue;
        } else {
          benefit = gain_cache.recomputeBenefitTerm(phg, u, i);
        }
        if ((benefit > to_benefit || (benefit == to_benefit && to_weight < best_to_weight)) &&
            to_weight + wu <= context.partition.max_part_weights[i]) {
          to_benefit = benefit;
          to = i;
          best_to_weight = to_weight;
        }
      }
    }

    Gain gain = std::numeric_limits<Gain>::min();
    if (to != kInvalidPartition) {
      gain = to_benefit - gain_cache.penaltyTerm(u, phg.partID(u));
    }
    return std::make_pair(to, transformGain(gain, wu));
  }

  template<typename PartitionedHypergraph, typename GainCache>
  std::pair<PartitionID, float> bestOfThree(
          const PartitionedHypergraph& phg, const Context& context, const GainCache& gain_cache,
          HypernodeID u, PartitionID from, std::array<PartitionID, 3> parts) {
    const HypernodeWeight wu = phg.nodeWeight(u);
    const HypernodeWeight from_weight = phg.partWeight(from);
    PartitionID to = kInvalidPartition;
    HyperedgeWeight to_benefit = std::numeric_limits<HyperedgeWeight>::min();
    HypernodeWeight best_to_weight = from_weight - wu;
    for (PartitionID i : parts) {
      if (i != from && i != kInvalidPartition) {
        const HypernodeWeight to_weight = phg.partWeight(i);
        const HyperedgeWeight benefit = gain_cache.blockIsAdjacent(u, i) ? gain_cache.benefitTerm(u, i) : gain_cache.recomputeBenefitTerm(phg, u, i);
        if ((benefit > to_benefit || (benefit == to_benefit && to_weight < best_to_weight)) &&
            to_weight + wu <= context.partition.max_part_weights[i]) {
          to_benefit = benefit;
          to = i;
          best_to_weight = to_weight;
        }
      }
    }

    if (to != kInvalidPartition) {
      Gain gain = to_benefit - gain_cache.penaltyTerm(u, phg.partID(u));
      return std::make_pair(to, transformGain(gain, wu));
    } else {
      // edge case: if u does not fit in any of the three considered blocks we need to check all blocks
      return computeBestTargetBlock(phg, context, gain_cache, u, from);
    }
  }

  struct AccessToken {
    AccessToken(int seed, size_t num_pqs) : dist(0, num_pqs - 1) { rng.seed(seed); }
    size_t getRandomPQ() { return dist(rng); }

    std::array<size_t, 2> getTwoRandomPQs() {
      std::array<size_t, 2> result({getRandomPQ(), getRandomPQ()});
      while (result[0] == result[1]) { result[1] = getRandomPQ(); }
      return result;
    }

    std::mt19937 rng;
    std::uniform_int_distribution<size_t> dist;
  };


  template<typename PartitionedHypergraph, typename GainCache>
  struct NextMoveFinder {
    Move next_move;

    PartitionedHypergraph& _phg;
    GainCache& _gain_cache;
    const Context& _context;

    vec<rebalancer::GuardedPQ>& _pqs;
    ds::Array<PartitionID>& _target_part;
    ds::Array<rebalancer::NodeState>& _node_state;
    AccessToken _token;

    NextMoveFinder(int seed, const Context& context, PartitionedHypergraph& phg, GainCache& gain_cache,
                   vec<rebalancer::GuardedPQ>& pqs,
                   ds::Array<PartitionID>& target_part, ds::Array<rebalancer::NodeState>& node_state) :
                   _phg(phg), _gain_cache(gain_cache), _context(context),
                   _pqs(pqs), _target_part(target_part), _node_state(node_state), _token(seed, pqs.size()) { }


    void recomputeTopGainMove(HypernodeID v, const Move& move /* of the neighbor */) {
      float gain = 0;
      PartitionID newTarget = kInvalidPartition;
      const PartitionID designatedTargetV = _target_part[v];
      if (_context.partition.k < 4 || designatedTargetV == move.from || designatedTargetV == move.to) {
        std::tie(newTarget, gain) = computeBestTargetBlock(_phg, _context, _gain_cache, v, _phg.partID(v));
      } else {
        std::tie(newTarget, gain) = bestOfThree(_phg, _context, _gain_cache,
                                                v, _phg.partID(v), {designatedTargetV, move.from, move.to});
      }
      _target_part[v] = newTarget;
    }

    bool checkCandidate(HypernodeID u, float& gain_in_pq) {
      if (!_node_state[u].tryLock()) return false;
      auto [to, true_gain] = computeBestTargetBlock(_phg, _context, _gain_cache, u, _phg.partID(u));
      if (to != kInvalidPartition && true_gain >= gain_in_pq) {
        next_move.node = u;
        next_move.to = to;
        next_move.from = _phg.partID(u);
        next_move.gain = true_gain;
        return true;
      } else {
        _target_part[u] = to;
        gain_in_pq = true_gain;
        _node_state[u].unlock();
        return false;
      }
    }

    bool lockedModifyPQ(size_t best_id) {
      auto& gpq = _pqs[best_id];
      auto& pq = gpq.pq;

      HypernodeID node = pq.top();
      float gain_in_pq = pq.topKey();
      const bool success = checkCandidate(node, gain_in_pq);

      if (success) {
        pq.deleteTop();
        gpq.top_key = pq.empty() ? std::numeric_limits<float>::lowest() : pq.topKey();
      } else {
        // gain was updated by success_func in this case
        if (_target_part[node] != kInvalidPartition) {
          pq.adjustKey(node, gain_in_pq);
          gpq.top_key = pq.topKey();
        } else {
          pq.deleteTop();
          gpq.top_key = pq.empty() ? std::numeric_limits<float>::lowest() : pq.topKey();
        }
      }
      gpq.lock.unlock();
      return success;
    }

    bool tryPop() {
      static constexpr size_t NUM_TRIES = 32;
      for (size_t i = 0; i < NUM_TRIES; ++i) {
        auto two = _token.getTwoRandomPQs();
        auto& first = _pqs[two[0]];
        auto& second = _pqs[two[1]];
        if (first.pq.empty() && second.pq.empty()) continue;
        size_t best_id = two[0];
        if (first.pq.empty() || first.top_key < second.top_key) best_id = two[1];
        if (!_pqs[best_id].lock.tryLock()) continue;
        // could also check for top key. would want to distinguish tries that failed due to high contention
        // vs approaching the end
        if (_pqs[best_id].pq.empty()) {
          _pqs[best_id].lock.unlock();
          continue;
        }
        if (lockedModifyPQ(best_id)) return true;
        // if you got a PQ but it fails because the node's gain was wrong or the node couldn't be locked
        // (success_func failed) then we still want to use the standard method
        i = 0;
      }

      while (true) {
        float best_key = std::numeric_limits<float>::lowest();
        int best_id = -1;
        for (size_t i = 0; i < _pqs.size(); ++i) {
          if (!_pqs[i].pq.empty() && _pqs[i].top_key > best_key) {
            best_key = _pqs[i].top_key;
            best_id = i;
          }
        }
        if (best_id == -1) return false;
        if (!_pqs[best_id].lock.tryLock()) continue;
        if (_pqs[best_id].pq.empty()) {
          _pqs[best_id].lock.unlock();
          continue;
        }
        if (lockedModifyPQ(best_id)) return true;
      }
    }

    bool findNextMove() {
      return tryPop();
    }
  };

  void deactivateOverloadedBlock(uint8_t* is_overloaded, size_t* num_overloaded_blocks) {
    if (*is_overloaded) {
      uint8_t expected = 1;
      if (repcut_serial::Ref(*is_overloaded)
          .compare_exchange_strong(expected, 0, std::memory_order_acquire, std::memory_order_relaxed)) {
        repcut_serial::Ref(*num_overloaded_blocks).fetch_sub(1, std::memory_order_relaxed);
      }
    }
  }

} // namespace impl


  template <typename GraphAndGainTypes>
  void AdvancedRebalancer<GraphAndGainTypes>::insertNodesInOverloadedBlocks(mt_kahypar_partitioned_hypergraph_t& hypergraph) {
    auto& phg = utils::cast<PartitionedHypergraph>(hypergraph);

    // init PQs if not done before
    const size_t num_pqs = 2 * _context.shared_memory.num_threads;
    if (_pqs.size() != num_pqs) {
      _pqs.assign(num_pqs, rebalancer::GuardedPQ(_pq_handles.data(), _node_state.size()));
    }
    for (auto& gpq : _pqs) {
      gpq.reset();
    }

    // data structures to draw random PQs
    std::atomic<int> seed { 555 };
    tbb::enumerable_thread_specific<impl::AccessToken> ets_tokens([&]() {
      return impl::AccessToken(seed.fetch_add(1, std::memory_order_relaxed), num_pqs);
    });

    // insert nodes into PQs
    phg.doParallelForAllNodes([&](HypernodeID u) {
      const PartitionID b = phg.partID(u);
      if (!_is_overloaded[b] || phg.isFixed(u)) return;

      auto [target, gain] = impl::computeBestTargetBlock(phg, _context, _gain_cache, u, phg.partID(u));
      ASSERT(target == kInvalidPartition ||
             gain == impl::transformGain(_gain_cache.recomputeBenefitTerm(phg, u, target) - _gain_cache.recomputePenaltyTerm(phg, u), phg.nodeWeight(u)),
             "Gain cache is in invalid state!");
      if (target == kInvalidPartition) return;

      _node_state[u].markAsMovable();
      _target_part[u] = target;

      auto& token = ets_tokens.local();
      int my_pq_id = -1;
      while (true) {
        my_pq_id = token.getRandomPQ();
        if (_pqs[my_pq_id].lock.tryLock()) {
          break;
        }
      }
      _pqs[my_pq_id].pq.insert(u, gain);
      _pqs[my_pq_id].lock.unlock();
      _pq_id[u] = my_pq_id;
    });


    for (rebalancer::GuardedPQ& gpq : _pqs) {
      if (!gpq.pq.empty()) {
        gpq.top_key = gpq.pq.topKey();
      }
    }
  }

  template <typename GraphAndGainTypes>
  void AdvancedRebalancer<GraphAndGainTypes>::findMoves(mt_kahypar_partitioned_hypergraph_t& hypergraph,
                                                        int64_t& attributed_gain,
                                                        size_t& global_move_id) {
    auto& phg = utils::cast<PartitionedHypergraph>(hypergraph);
    size_t num_overloaded_blocks = _overloaded_blocks.size();

    auto task = [&](size_t task_id) {
      vec<HyperedgeID> edges_with_gain_changes;
      Gain local_attributed_gain = 0;
      vec<vec<HypernodeID>> nodes_to_update(_pqs.size());
      vec<int> pqs_to_update;

      const int seed = phg.initialNumNodes() + task_id;

      impl::NextMoveFinder<PartitionedHypergraph, GainCache> next_move_finder(
        seed, _context, phg, _gain_cache, _pqs, _target_part, _node_state);

      while (num_overloaded_blocks > 0 && next_move_finder.findNextMove()) {
        const Move& m = next_move_finder.next_move;
        ASSERT(m.to != kInvalidPartition);
        const PartitionID from = phg.partID(m.node);
        _node_state[m.node].markAsMovedAndUnlock();

        if (phg.partWeight(from) <= _context.partition.max_part_weights[from]) {
          impl::deactivateOverloadedBlock(&_is_overloaded[from], &num_overloaded_blocks);
          continue;
        }

        edges_with_gain_changes.clear();
        size_t move_id = 0;
        bool moved = phg.changeNodePart(
                      _gain_cache, m.node, m.from, m.to,
                      _context.partition.max_part_weights[m.to],
                      [&] {
                          move_id = repcut_serial::Ref(global_move_id).fetch_add(1, std::memory_order_relaxed);
                      },
                      [&](const SynchronizedEdgeUpdate& sync_update) {
                        local_attributed_gain += AttributedGains::gain(sync_update);
                        if (!PartitionedHypergraph::is_graph && GainCache::triggersDeltaGainUpdate(sync_update)) {
                          edges_with_gain_changes.push_back(sync_update.he);
                        }
                      }
                    );



        if (!moved) continue;

        auto update_neighbor = [&](HypernodeID v) {
          if (v != m.node && _node_state[v].tryLock()) {
            int my_pq_id = _pq_id[v];
            ASSERT(my_pq_id != -1);
            if (nodes_to_update[my_pq_id].empty()) {
              pqs_to_update.push_back(my_pq_id);
            }
            nodes_to_update[my_pq_id].push_back(v);
            next_move_finder.recomputeTopGainMove(v, m);
          }
        };

        // update neighbors
        if constexpr (PartitionedHypergraph::is_graph) {
          for (const auto e : phg.incidentEdges(m.node)) {
            HypernodeID v = phg.edgeTarget(e);
            update_neighbor(v);
          }
        } else {
          for (HyperedgeID e : edges_with_gain_changes) {
            if (phg.edgeSize(e) < _context.partition.ignore_hyperedge_size_threshold) {
              for (HypernodeID v : phg.pins(e)) {
                update_neighbor(v);
              }
            }
          }
        }

        while (!pqs_to_update.empty()) {
          for (size_t i = 0; i < pqs_to_update.size(); ++i) {
            int my_pq_id = pqs_to_update[i];
            auto& gpq = _pqs[my_pq_id];
            auto& pq = gpq.pq;
            if (gpq.lock.tryLock()) {
              for (HypernodeID v : nodes_to_update[my_pq_id]) {
                if (pq.contains(v)) {
                  if (_target_part[v] != kInvalidPartition) {
                    Gain new_gain_int;
                    if (_gain_cache.blockIsAdjacent(v, _target_part[v])) {
                      new_gain_int = _gain_cache.gain(v, phg.partID(v), _target_part[v]);
                    } else {
                      new_gain_int = _gain_cache.recomputeBenefitTerm(phg, v, _target_part[v]) - _gain_cache.penaltyTerm(v, phg.partID(v));
                    }
                    float new_gain = impl::transformGain(new_gain_int, phg.nodeWeight(v));
                    pq.adjustKey(v, new_gain);
                  } else {
                    pq.remove(v);
                  }
                }
                _node_state[v].unlock();
              }

              gpq.lock.unlock();
              pqs_to_update[i] = pqs_to_update.back();
              pqs_to_update.pop_back();
              nodes_to_update[my_pq_id].clear();
            }
          }
        }

        _moves[move_id] = m;
      }
      repcut_serial::Ref(attributed_gain)
          .fetch_add(local_attributed_gain, std::memory_order_relaxed);
    };

    tbb::task_group tg;
    for (size_t i = 0; i < _context.shared_memory.num_threads; ++i) { tg.run(std::bind(task, i)); }
    tg.wait();
  }

  template <typename GraphAndGainTypes>
  bool AdvancedRebalancer<GraphAndGainTypes>::refineInternalParallel(mt_kahypar_partitioned_hypergraph_t& hypergraph,
                                                                  vec<vec<Move>>* moves_by_part,
                                                                  vec<Move>* moves_linear,
                                                                  Metrics& best_metric) {
    auto& phg = utils::cast<PartitionedHypergraph>(hypergraph);
    HEAVY_REFINEMENT_ASSERT(phg.checkTrackedPartitionInformation(_gain_cache));

    int64_t attributed_gain = 0;
    size_t global_move_id = 0;
    _repair_empty_blocks.repairEmptyBlocks(hypergraph, _gain, [&](const Move& m) {
      bool success = phg.changeNodePart(
        _gain_cache, m.node, m.from, m.to,
        _context.partition.max_part_weights[m.to],
        // Note: we don't explicitly exclude these nodes from being moved again. However, since the previously empty
        // target blocks are not overloaded after the moves, these nodes won't be selected for the main rebalancing
        // round and thus can not be moved a second time.
        [&] { _moves[global_move_id++] = m; },
        [&](const SynchronizedEdgeUpdate& sync_update) {
          attributed_gain += AttributedGains::gain(sync_update);
        }
      );
      ASSERT(success); unused(success);
    });
    ASSERT(!metrics::imbalance(phg, _context).violates_non_empty_blocks || phg.initialNumNodes() < ID(_context.partition.k));

    _overloaded_blocks.clear();
    _is_overloaded.assign(_context.partition.k, false);
    for (PartitionID k = 0; k < _context.partition.k; ++k) {
      if (phg.partWeight(k) > _context.partition.max_part_weights[k]) {
        _overloaded_blocks.push_back(k);
        _is_overloaded[k] = 1;
      }
    }

    insertNodesInOverloadedBlocks(hypergraph);

    findMoves(hypergraph, attributed_gain, global_move_id);

    if constexpr (GainCache::invalidates_entries) {
      tbb::parallel_for(UL(0), global_move_id, [&](const size_t i) {
        _gain_cache.recomputeInvalidTerms(phg, _moves[i].node);
      });
    }

    HEAVY_REFINEMENT_ASSERT(phg.checkTrackedPartitionInformation(_gain_cache));

    if (moves_by_part != nullptr) {
      moves_by_part->resize(_context.partition.k);
      for (auto& direction : *moves_by_part) direction.clear();
      for (size_t i = 0; i < global_move_id; ++i) {
        (*moves_by_part)[_moves[i].from].push_back(_moves[i]);
      }
    } else if (moves_linear != nullptr) {
      moves_linear->clear();
      moves_linear->reserve(global_move_id);
      for (size_t i = 0; i < global_move_id; ++i) {
        moves_linear->push_back(_moves[i]);
      }
    }

    best_metric.quality += attributed_gain;
    best_metric.imbalance = metrics::imbalance(phg, _context);

    size_t num_overloaded_blocks = 0;
    for (PartitionID b = 0; b < _context.partition.k; ++b) {
      if (phg.partWeight(b) > _context.partition.max_part_weights[b]) {
        num_overloaded_blocks++;
      }
    }

    phg.doParallelForAllNodes([&](HypernodeID u) {
      _node_state[u].reset();
    });

    for (auto& gpq : _pqs) {
      gpq.pq.clear();
    }

    return num_overloaded_blocks == 0;
  }


template <typename GraphAndGainTypes>
AdvancedRebalancer<GraphAndGainTypes>::AdvancedRebalancer(
        HypernodeID num_nodes, const Context& context, GainCache& gain_cache) :
        _context(context),
        _gain_cache(gain_cache),
        _current_k(_context.partition.k),
        _gain(context),
        _moves(num_nodes),
        _target_part(num_nodes, kInvalidPartition),
        _pq_handles(num_nodes, invalid_position),
        _pq_id(num_nodes, -1),
        _node_state(num_nodes),
        _repair_empty_blocks(context, gain_cache) { }

template <typename GraphAndGainTypes>
AdvancedRebalancer<GraphAndGainTypes>::AdvancedRebalancer(
        HypernodeID num_nodes, const Context& context, gain_cache_t gain_cache) :
        AdvancedRebalancer(num_nodes, context, GainCachePtr::cast<GainCache>(gain_cache)) { }


template <typename GraphAndGainTypes>
bool AdvancedRebalancer<GraphAndGainTypes>::refineImpl(mt_kahypar_partitioned_hypergraph_t& hypergraph,
                const vec<HypernodeID>& , Metrics& best_metrics, double) {
  return refineInternalParallel(hypergraph, nullptr, nullptr, best_metrics);
}

template <typename GraphAndGainTypes>
void AdvancedRebalancer<GraphAndGainTypes>::initializeImpl(mt_kahypar_partitioned_hypergraph_t& hypergraph) {
  auto& phg = utils::cast<PartitionedHypergraph>(hypergraph);

  if (!_gain_cache.isInitialized()) {
    _gain_cache.initializeGainCache(phg);
  }
}

template <typename GraphAndGainTypes>
bool AdvancedRebalancer<GraphAndGainTypes>::refineAndOutputMovesImpl(mt_kahypar_partitioned_hypergraph_t& hypergraph,
                                                                  const vec<HypernodeID>& ,
                                                                  vec<vec<Move>>& moves_by_part,
                                                                  Metrics& best_metrics,
                                                                  const double) {
  return refineInternalParallel(hypergraph, &moves_by_part, nullptr, best_metrics);
}

template <typename GraphAndGainTypes>
bool AdvancedRebalancer<GraphAndGainTypes>::refineAndOutputMovesLinearImpl(mt_kahypar_partitioned_hypergraph_t& hypergraph,
                                                                        const vec<HypernodeID>& ,
                                                                        vec<Move>& moves,
                                                                        Metrics& best_metrics,
                                                                        const double) {
  return refineInternalParallel(hypergraph, nullptr, &moves, best_metrics);
}

// explicitly instantiate so the compiler can generate them when compiling this cpp file
namespace {
  #define ADVANCED_REBALANCER(X) AdvancedRebalancer<X>
}

// explicitly instantiate so the compiler can generate them when compiling this cpp file
INSTANTIATE_CLASS_WITH_VALID_TRAITS(ADVANCED_REBALANCER)

}   // namespace mt_kahypar
