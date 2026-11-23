/*******************************************************************************
 * MIT License
 *
 * This file is part of Mt-KaHyPar.
 *
 * Copyright (C) 2023 Robert Krause <robert.krause@student.kit.edu>
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

#include "mt-kahypar/partition/refinement/deterministic/deterministic_jet_refiner.h"

#include <tbb/parallel_for.h>
#include <tbb/parallel_reduce.h>

#include "mt-kahypar/definitions.h"
#include "mt-kahypar/partition/metrics.h"
#include "mt-kahypar/partition/refinement/gains/gain_definitions.h"
#include "mt-kahypar/utils/randomize.h"
#include "mt-kahypar/utils/utilities.h"
#include "mt-kahypar/utils/timer.h"
#include "mt-kahypar/utils/cast.h"
#include "mt-kahypar/datastructures/streaming_vector.h"


namespace mt_kahypar {

template<typename GraphAndGainTypes>
bool DeterministicJetRefiner<GraphAndGainTypes>::refineImpl(mt_kahypar_partitioned_hypergraph_t& hypergraph,
                                                            const vec<HypernodeID>& refinement_nodes,
                                                            Metrics& best_metrics,
                                                            const double time_limit) {
    if (!refinement_nodes.empty()) {
        throw UnsupportedOperationException("Deterministic Jet does not support local refinement");
    }

    Metrics current_metrics = best_metrics;
    PartitionedHypergraph& phg = utils::cast<PartitionedHypergraph>(hypergraph);
    const HyperedgeWeight input_quality = best_metrics.quality;
    const auto& jet_context = _context.refinement.jet;
    resizeDataStructuresForCurrentK();

    _current_partition_is_best = true;
    for (size_t dynamic_round = 0; dynamic_round < jet_context.dynamic_rounds; ++dynamic_round) {
        if (jet_context.dynamic_rounds > 1) {
            _negative_gain_factor =
                jet_context.initial_negative_gain_factor +
                (static_cast<double>(dynamic_round) / (jet_context.dynamic_rounds - 1.0)) *
                (jet_context.final_negative_gain_factor - jet_context.initial_negative_gain_factor);
        } else {
            _negative_gain_factor =
                (jet_context.final_negative_gain_factor + jet_context.initial_negative_gain_factor) / 2.0;
        }
        DBG << V(_negative_gain_factor) << ", " << V(jet_context.dynamic_rounds) << ", " << V(metrics::quality(phg, _context, false));

        runJetRounds(phg, best_metrics, time_limit);

        if (!_current_partition_is_best) {
            DBG << "[JET] Rollback to best partition with value " << best_metrics.quality;
            rollbackToBestPartition(phg);
            current_metrics = best_metrics;
        }
        phg.resetEdgeSynchronization();
    }
    HEAVY_REFINEMENT_ASSERT(phg.checkTrackedPartitionInformation(_gain_cache));
    ASSERT(best_metrics.quality == metrics::quality(phg, _context, false),
        V(best_metrics.quality) << V(metrics::quality(phg, _context, false)));
    return best_metrics.quality < input_quality;
}

template <typename GraphAndGainTypes>
void DeterministicJetRefiner<GraphAndGainTypes>::runJetRounds(PartitionedHypergraph& phg, Metrics& best_metrics, const double time_limit) {
    utils::Timer& timer = utils::Utilities::instance().getTimer(_context.utility_id);
    Metrics current_metrics = best_metrics;
    _locks.reset();

    size_t rounds_without_improvement = 0;
    for (size_t i = 0; rounds_without_improvement < _context.refinement.jet.num_iterations; ++i) {
        if (_current_partition_is_best) {
            phg.doParallelForAllNodes([&](const HypernodeID hn) {
                _best_partition[hn] = phg.partID(hn);
            });
        }

        HEAVY_REFINEMENT_ASSERT(noInvalidPartitions(phg, _best_partition));
        timer.start_timer("active_nodes", "Active Nodes");
        computeActiveNodesFromGraph(phg);
        timer.stop_timer("active_nodes");
        HEAVY_REFINEMENT_ASSERT(arePotentialMovesToOtherParts(phg, _active_nodes), "active nodes");

        // label prop round
        timer.start_timer("afterburner", "Afterburner");
        _locks.reset();
        _tmp_active_nodes.clear_sequential();
        if constexpr (PartitionedHypergraph::is_graph) {
            graphAfterburner(phg);
        } else {
            hypergraphAfterburner(phg);
        }
        HEAVY_REFINEMENT_ASSERT(arePotentialMovesToOtherParts(phg, _active_nodes), "moves");
        timer.stop_timer("afterburner");

        // Apply all moves
        timer.start_timer("apply_moves", "Apply Moves");
        auto range = tbb::blocked_range<size_t>(UL(0), _active_nodes.size());
        auto accum = [&](const tbb::blocked_range<size_t>& r, const Gain& init) -> Gain {
            Gain my_gain = init;
            for (size_t j = r.begin(); j < r.end(); ++j) {
                const HypernodeID hn = _active_nodes[j];
                if (PartitionedHypergraph::is_graph || _afterburner_gain[hn] <= 0) {
                    my_gain += performMoveWithAttributedGain(phg, hn);
                    _locks.set(hn);
                }
            }
            return my_gain;
        };
        Gain gain = tbb::parallel_reduce(range, 0, accum, std::plus<>());
        current_metrics.quality -= gain;
        current_metrics.imbalance = metrics::imbalance(phg, _context);

        if (GainCache::invalidates_entries && _gain_cache.isInitialized()) {
            tbb::parallel_for(UL(0), _active_nodes.size(), [&](size_t j) {
                const HypernodeID hn = _active_nodes[j];
                if (_part_before_round[hn] != phg.partID(hn)) {
                    _gain_cache.recomputeInvalidTerms(phg, hn);
                }
            });
        }
        timer.stop_timer("apply_moves");

        // rebalance
        if (!metrics::isValidPartition(phg, _context)) {
            DBG << "[JET] starting rebalancing with quality " << current_metrics.quality << " and imbalance " << current_metrics.imbalance;
            timer.start_timer("rebalance", "Rebalance");
            mt_kahypar_partitioned_hypergraph_t part_hg = utils::partitioned_hg_cast(phg);
            if constexpr (PartitionedHypergraph::is_graph) {
                // if it is a graph, the gain update happens later via calculateGainDelta => use copy of metrics
                Metrics tmp_metrics{current_metrics};
                _rebalancer.refine(part_hg, {}, tmp_metrics, time_limit);
            } else {
                _rebalancer.refine(part_hg, {}, current_metrics, time_limit);
            }
            current_metrics.imbalance = metrics::imbalance(phg, _context);
            timer.stop_timer("rebalance");
            DBG << "[JET] finished rebalancing with quality " << current_metrics.quality << " and imbalance " << current_metrics.imbalance;
        }

        if (PartitionedHypergraph::is_graph && !_gain_cache.isInitialized()) {
            timer.start_timer("reb_quality", "Quality after Rebalancing");
            current_metrics.quality += calculateGainDelta(phg);
            timer.stop_timer("reb_quality");
        }

        HEAVY_REFINEMENT_ASSERT(current_metrics.quality == metrics::quality(phg, _context, false),
            V(current_metrics.quality) << V(metrics::quality(phg, _context, false)));
        ++rounds_without_improvement;

        // if the parition was ever balanced => look for balanced partition with better quality
        // if the partition was never balanced => look for less imbalanced partition regardless of quality
        if (current_metrics.isBetter(best_metrics)) {
            if (best_metrics.quality - current_metrics.quality > _context.refinement.jet.relative_improvement_threshold * best_metrics.quality) {
                rounds_without_improvement = 0;
            }
            best_metrics = current_metrics;
            _current_partition_is_best = true;
        } else {
            _current_partition_is_best = false;
        }
        DBG << "[JET] Finished iteration " << i << " with quality " << current_metrics.quality << " and imbalance " << current_metrics.imbalance;
    }
}


template<typename GraphAndGainTypes>
void DeterministicJetRefiner<GraphAndGainTypes>::computeActiveNodesFromGraph(const PartitionedHypergraph& phg) {
    _active_nodes.clear();
    _tmp_active_nodes.clear_sequential();

    // compute gain for every node 
    phg.doParallelForAllNodes([&](const HypernodeID& hn) {
        _part_before_round[hn] = phg.partID(hn);
        const bool is_locked = _locks[hn];
        if (!phg.isBorderNode(hn) || is_locked || phg.isFixed(hn)) {
            _gains_and_target[hn] = { 0, phg.partID(hn) };
        } else {
            RatingMap& tmp_scores = _gain_computation.localScores();
            Gain isolated_block_gain = 0;
            _gain_computation.precomputeGains(phg, hn, tmp_scores, isolated_block_gain, true);
            // Note: rebalance=true is important here to allow negative gain moves
            Move best_move = _gain_computation.computeMaxGainMoveForScores(phg, tmp_scores, isolated_block_gain, hn,
                /*rebalance=*/true,
                /*consider_non_adjacent_blocks=*/false,
                /*allow_imbalance=*/true);
            tmp_scores.clear();
            bool accept_node = (best_move.gain <= 0 || best_move.gain < std::floor(_negative_gain_factor * isolated_block_gain))
                && best_move.to != phg.partID(hn);
            if (accept_node) {
                _gains_and_target[hn] = { best_move.gain, best_move.to };
                _tmp_active_nodes.stream(hn);
            } else {
                _gains_and_target[hn] = { 0, phg.partID(hn) };
            }
        }
    });
    _active_nodes = _tmp_active_nodes.copy_parallel();
}

template <typename GraphAndGainTypes>
void DeterministicJetRefiner<GraphAndGainTypes>::initializeImpl(mt_kahypar_partitioned_hypergraph_t& phg) {
    _rebalancer.initialize(phg);
}


template<typename GraphAndGainTypes>
Gain DeterministicJetRefiner<GraphAndGainTypes>::performMoveWithAttributedGain(PartitionedHypergraph& phg, const HypernodeID hn) {
    const auto from = phg.partID(hn);
    const auto [gain, to] = _gains_and_target[hn];
    Gain attributed_gain = 0;
    auto objective_delta = [&](const SynchronizedEdgeUpdate& sync_update) {
        attributed_gain -= AttributedGains::gain(sync_update);
    };
    ASSERT(to >= 0 && to < _current_k);
    changeNodePart(phg, hn, from, to, objective_delta);
    // note: returns 0 in "NoSync" case
    return attributed_gain;
}

template <typename GraphAndGainTypes>
void DeterministicJetRefiner<GraphAndGainTypes>::rollbackToBestPartition(PartitionedHypergraph& phg) {
    // This function is passed as lambda to the changeNodePart function and used
    // to calculate the "real" delta of a move (in terms of the used objective function).
    auto objective_delta = [&](const SynchronizedEdgeUpdate& sync_update) {
        _gain_computation.computeDeltaForHyperedge(sync_update);
    };
    const bool update_gain_cache = GainCache::invalidates_entries && _gain_cache.isInitialized();

    phg.doParallelForAllNodes([&](const HypernodeID hn) {
        const PartitionID part_id = phg.partID(hn);
        if (update_gain_cache) {
            _part_before_round[hn] = part_id;
        }
        if (part_id != _best_partition[hn]) {
            ASSERT(_best_partition[hn] != kInvalidPartition);
            ASSERT(_best_partition[hn] >= 0 && _best_partition[hn] < _current_k);
            changeNodePart(phg, hn, part_id, _best_partition[hn], objective_delta);
        }
    });
    if (update_gain_cache) {
         phg.doParallelForAllNodes([&](const HypernodeID hn) {
            if (_part_before_round[hn] != phg.partID(hn)) {
                _gain_cache.recomputeInvalidTerms(phg, hn);
            }
        });
    }
    _current_partition_is_best = true;
}

template <typename GraphAndGainTypes>
void DeterministicJetRefiner<GraphAndGainTypes>::graphAfterburner(PartitionedHypergraph& phg) {
    tbb::parallel_for(UL(0), _active_nodes.size(), [&](size_t j) {
        const HypernodeID hn = _active_nodes[j];
        const PartitionID from = phg.partID(hn);
        const auto [gain, to] = _gains_and_target[hn];
        ASSERT(from != to && to != kInvalidPartition);

        Gain total_gain = 0;
        for (const HyperedgeID& he : phg.incidentEdges(hn)) {
            SynchronizedEdgeUpdate sync_update = phg.createEdgeUpdate(he);
            sync_update.from = from;
            sync_update.to = to;
            sync_update.pin_count_in_from_part_after = 0;
            sync_update.pin_count_in_to_part_after = 1;

            // Jet uses an order based on the precomputed gain values:
            // If the precomputed gain of another node is better than for the current node
            // (or the gain is equal and the id is smaller), we assume the node is already
            // moved to its target part.
            const HypernodeID other_node = phg.edgeTarget(he);
            auto [gain_p, to_p] = _gains_and_target[other_node];
            sync_update.block_of_other_node = (gain_p < gain || (gain_p == gain && other_node < hn)) ? to_p : phg.partID(other_node);
            if (sync_update.block_of_other_node == from) {
                sync_update.pin_count_in_from_part_after++;
            } else if (sync_update.block_of_other_node == to) {
                sync_update.pin_count_in_to_part_after++;
            }
            total_gain += AttributedGains::gain(sync_update);
        }

        if (total_gain <= 0) {
            _tmp_active_nodes.stream(hn);
        }
    });
    _active_nodes = _tmp_active_nodes.copy_parallel();
}

template <typename GraphAndGainTypes>
void DeterministicJetRefiner<GraphAndGainTypes>::hypergraphAfterburner(PartitionedHypergraph& phg) {
    tbb::parallel_for(UL(0), _afterburner_gain.size(), [&](const size_t i) {
        _afterburner_gain[i].store(0);
    });

    auto afterburn_two_pins = [&](const HyperedgeID& he) {
        HypernodeID a = kInvalidHypernode;
        HypernodeID b = kInvalidHypernode;
        Gain minGain = std::numeric_limits<Gain>::max();
        for (const auto pin : phg.pins(he)) {
            const Gain& gain = _gains_and_target[pin].first;
            if (a == kInvalidHypernode || gain < minGain || (minGain == gain && pin < a)) {
                b = a;
                a = pin;
                minGain = gain;
            } else {
                b = pin;
            }
        }
        const auto& [gain_a, to_a] = _gains_and_target[a];
        const auto& [gain_b, to_b] = _gains_and_target[b];
        const PartitionID from_a = phg.partID(a);
        const PartitionID from_b = phg.partID(b);
        const HyperedgeWeight weight = phg.edgeWeight(he);
        // moving a
        if (from_a != to_a) {
            if (from_a == from_b) {
                _afterburner_gain[a] += weight;
            } else if (to_a == from_b) {
                _afterburner_gain[a] -= weight;
            }
        }
        // moving b after a
        if (from_b != to_b) {
            if (from_b == to_a) {
                _afterburner_gain[b] += weight;
            } else if (to_b == to_a) {
                _afterburner_gain[b] -= weight;
            }
        }
    };

    auto afterburn_edge = [&](const HyperedgeID& he) {
        const HypernodeID edgeSize = phg.edgeSize(he);
        if (edgeSize == 2) {
            return afterburn_two_pins(he);
        }

        auto& edgeBuffer = _afterburner_edge_buffer.local();
        if (edgeSize > edgeBuffer.size()) {
            edgeBuffer.resize(edgeSize);
        }

        // materialize the hyperedge and initialize pin counts
        size_t index = 0;
        for (const auto pin : phg.pins(he)) {
            const auto part = phg.partID(pin);
            if (part != _gains_and_target[pin].second) {
                edgeBuffer[index] = pin;
                ++index;
            }
        }

        // sort the pins by afterburner order, with special cases for small pin counts
        if (index == 0) {
            return;
        } else if (index == 1) {
        } else if (index == 2) {
            auto& a = edgeBuffer[0];
            auto& b = edgeBuffer[1];
            auto& [gain_a, to_a] = _gains_and_target[a];
            auto& [gain_b, to_b] = _gains_and_target[b];
            if (!(gain_a < gain_b || (gain_a == gain_b && a < b))) std::swap(a, b);
        } else if (index == 3) {
            auto& a = edgeBuffer[0];
            auto& b = edgeBuffer[1];
            auto& c = edgeBuffer[2];
            if (!(_gains_and_target[a].first < _gains_and_target[c].first || (_gains_and_target[a].first == _gains_and_target[c].first && a < c)))
                std::swap(a, c);
            if (!(_gains_and_target[a].first < _gains_and_target[b].first || (_gains_and_target[a].first == _gains_and_target[b].first && a < b)))
                std::swap(a, b);
            if (!(_gains_and_target[b].first < _gains_and_target[c].first || (_gains_and_target[b].first == _gains_and_target[c].first && b < c)))
                std::swap(b, c);
        } else {
            std::sort(edgeBuffer.begin(), edgeBuffer.begin() + index, [&](const HypernodeID& a, const HypernodeID& b) {
                auto& [gain_a, to_a] = _gains_and_target[a];
                auto& [gain_b, to_b] = _gains_and_target[b];
                return (gain_a < gain_b || (gain_a == gain_b && a < b));
            });
        }

        // scan through the sorted pins and compute gains, updating the pin counts at each step
        SynchronizedEdgeUpdate sync_update = phg.createEdgeUpdate(he);
        for (size_t i = 0; i < index; ++i) {
            const HypernodeID pin = edgeBuffer[i];
            const auto [gain, to] = _gains_and_target[pin];
            sync_update.from = phg.partID(pin);
            sync_update.to = to;
            sync_update.pin_count_in_from_part_after = sync_update.decrementPinCountInPart(sync_update.from);
            sync_update.pin_count_in_to_part_after = sync_update.incrementPinCountInPart(sync_update.to);
            const Gain attributedGain = AttributedGains::gain(sync_update);
            if (attributedGain != 0) {
                _afterburner_gain[pin].fetch_add(attributedGain, std::memory_order_relaxed);
            }
        }
    };

    tbb::parallel_for(UL(0), _active_nodes.size(), [&](const size_t& i) {
        const HypernodeID hn = _active_nodes[i];
        for (const HyperedgeID& he : phg.incidentEdges(hn)) {
            if (_afterburner_visited_hes.compare_and_set_to_true(he)) {
                afterburn_edge(he);
            }
        }
    });
    _afterburner_visited_hes.reset();
}

template <typename GraphAndGainTypes>
HyperedgeWeight DeterministicJetRefiner<GraphAndGainTypes>::calculateGainDelta(PartitionedHypergraph& phg) const {
    tbb::enumerable_thread_specific<HyperedgeWeight> gain_delta(0);
    phg.doParallelForAllNodes([&](const HypernodeID hn) {
        const PartitionID from = _part_before_round[hn];
        const PartitionID to = phg.partID(hn);

        if (from != to) {
            for (const HyperedgeID& he : phg.incidentEdges(hn)) {
                SynchronizedEdgeUpdate sync_update = phg.createEdgeUpdate(he);
                sync_update.from = from;
                sync_update.to = to;
                sync_update.pin_count_in_from_part_after = 0;
                sync_update.pin_count_in_to_part_after = 1;

                const HypernodeID other_node = phg.edgeTarget(he);
                sync_update.block_of_other_node = other_node < hn ? phg.partID(other_node) : _part_before_round[other_node];
                if (sync_update.block_of_other_node == from) {
                    sync_update.pin_count_in_from_part_after++;
                } else if (sync_update.block_of_other_node == to) {
                    sync_update.pin_count_in_to_part_after++;
                }
                gain_delta.local() += AttributedGains::gain(sync_update);
            }
        }
    });
    return gain_delta.combine(std::plus<>());
}

template <typename GraphAndGainTypes>
template<typename F>
void DeterministicJetRefiner<GraphAndGainTypes>::changeNodePart(PartitionedHypergraph& phg,
                                                                const HypernodeID hn,
                                                                const PartitionID from,
                                                                const PartitionID to,
                                                                const F& objective_delta) {
    constexpr HypernodeWeight inf_weight = std::numeric_limits<HypernodeWeight>::max();
    bool success;
    if (_gain_cache.isInitialized()) {
        success = phg.changeNodePart(_gain_cache, hn, from, to, inf_weight, [] {}, objective_delta);
    } else if constexpr (PartitionedHypergraph::is_graph) {
        success = phg.changeNodePartNoSync(hn, from, to);
    } else {
        success = phg.changeNodePart(hn, from, to, inf_weight, [] {}, objective_delta);
    }
    ASSERT(success);
    unused(success);
}

template <typename GraphAndGainTypes>
bool DeterministicJetRefiner<GraphAndGainTypes>::arePotentialMovesToOtherParts(const PartitionedHypergraph& phg, const parallel::scalable_vector<HypernodeID>& moves) {
    for (auto hn : moves) {
        const auto [gain, to] = _gains_and_target[hn];
        if (to == phg.partID(hn)) {
            DBG << "Trying to move node " << hn << " to own part expecting gain " << gain;
            return false;
        }
    }
    return true;
}

template <typename GraphAndGainTypes>
bool DeterministicJetRefiner<GraphAndGainTypes>::noInvalidPartitions(const PartitionedHypergraph& phg, const parallel::scalable_vector<PartitionID>& parts) {
    phg.doParallelForAllNodes([&](const HypernodeID hn) {
        ASSERT(parts[hn] != kInvalidPartition);
        ASSERT(parts[hn] < _current_k);
        unused(hn);
    });
    unused(parts);
    return true;
}

template <typename GraphAndGainTypes>
void DeterministicJetRefiner<GraphAndGainTypes>::resizeDataStructuresForCurrentK() {
    // If the number of blocks changes, we resize data structures
    // (can happen during deep multilevel partitioning)
    if (_current_k != _context.partition.k) {
        _current_k = _context.partition.k;
        _gain_computation.changeNumberOfBlocks(_current_k);
    }
}

namespace {
#define DETERMINISTIC_JET_REFINER(X) DeterministicJetRefiner<X>
}


INSTANTIATE_CLASS_WITH_VALID_TRAITS(DETERMINISTIC_JET_REFINER)
}; // namespace
