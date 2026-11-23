/*******************************************************************************
 * MIT License
 *
 * This file is part of Mt-KaHyPar.
 *
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

#include "mt-kahypar/partition/refinement/fm/sequential_twoway_fm_refiner.h"

#include "mt-kahypar/definitions.h"
#include "mt-kahypar/partition/metrics.h"
#include "mt-kahypar/partition/refinement/fm/stop_rule.h"

namespace mt_kahypar {

template<typename TypeTraits>
bool SequentialTwoWayFmRefiner<TypeTraits>::refine(Metrics& best_metrics, std::mt19937& prng) {

  // Activate all border nodes
  _pq.clear();
  _border_vertices.initialize(_phg);
  _nodes.clear();
  for (HypernodeID hn : _phg.nodes()) {
    if ( !_phg.isFixed(hn) ) {
      _nodes.push_back(hn);
    } else {
      _vertex_state[hn] = VertexState::MOVED;
    }
  }
  std::shuffle(_nodes.begin(), _nodes.end(), prng);
  for ( const HypernodeID& hn : _nodes ) {
    _vertex_state[hn] = VertexState::INACTIVE;
    activate(hn);
  }
  for ( const HyperedgeID& he : _phg.edges() ) {
    _he_state[he] = HEState::FREE;
  }

  auto border_vertex_update = [&](const SynchronizedEdgeUpdate& sync_update) {
                            if ( sync_update.edge_size > 1 ) {
                              if ( sync_update.pin_count_in_from_part_after == 0 ) {
                                _border_vertices.becameNonCutHyperedge(_phg, sync_update.he, _vertex_state);
                              } else if ( sync_update.pin_count_in_to_part_after == 1 ) {
                                _border_vertices.becameCutHyperedge(_phg, sync_update.he, _vertex_state);
                              }
                            }
                          };

  parallel::scalable_vector<HypernodeID> performed_moves;
  HyperedgeWeight current_cut = best_metrics.quality;
  size_t min_cut_idx = 0;
  StopRule stopping_rule(_phg.initialNumNodes());
  while ( !_pq.empty() && !stopping_rule.searchShouldStop() ) {
    ASSERT(_pq.isEnabled(0) || _pq.isEnabled(1));
    HEAVY_REFINEMENT_ASSERT(verifyPQState(), "PQ corrupted!");

    // Retrieve max gain move from PQ
    Gain gain = invalidGain;
    HypernodeID hn = kInvalidHypernode;
    PartitionID to = kInvalidPartition;
    _pq.deleteMax(hn, gain, to);

    ASSERT(hn != kInvalidHypernode);
    ASSERT(_border_vertices.isBorderNode(hn));
    ASSERT(_phg.partID(hn) == 1 - to);
    HEAVY_REFINEMENT_ASSERT(gain == computeGain(hn, _phg.partID(hn), to));

    // Perform vertex move
    PartitionID from = _phg.partID(hn);
    _vertex_state[hn] = VertexState::MOVED;
    if ( _phg.changeNodePart(hn, from, to,
          _context.partition.max_part_weights[to], []{}, border_vertex_update) ) {

      // Perform delta gain updates
      updateNeighbors(hn, from, to);
      updatePQState(from, to);

      // Remove all vertices that became internal from the PQ
      _border_vertices.doForAllVerticesThatBecameInternalVertices(
        [&](const HypernodeID hn) {
          ASSERT(!_border_vertices.isBorderNode(hn));
          ASSERT(_vertex_state[hn] == VertexState::ACTIVE);
          ASSERT(_pq.contains(hn));
          _pq.remove(hn, 1 - _phg.partID(hn));
          _vertex_state[hn] = VertexState::INACTIVE;
        }
      );

      // Insert all new border vertices into PQ
      _border_vertices.doForAllVerticesThatBecameBorderVertices(
        [&](const HypernodeID hn) {
        ASSERT(_border_vertices.isBorderNode(hn));
        ASSERT(_vertex_state[hn] == VertexState::INACTIVE);
        activate(hn);
      });

      performed_moves.push_back(hn);
      DBG << "Moved hypernode" << hn << "from block" << from << "to block" << to << "with gain" << gain;
      current_cut -= gain;
      stopping_rule.update(gain);

      Metrics current_metrics{current_cut, metrics::onlyImbalance(_phg, _context)};
      if ( current_metrics.isBetter(best_metrics) ) {
        DBG << GREEN << "2Way FM improved cut from" << best_metrics.quality << "to" << current_cut
            << "(Imbalance:" << current_metrics.imbalance << ")" << END;
        stopping_rule.reset();
        best_metrics = current_metrics;
        min_cut_idx = performed_moves.size();
      } else {
        DBG << RED << "2Way FM decreased cut to" << current_cut
            << "(Imbalance:" << current_metrics.imbalance << ")" << END;
      }
    }
  }

  // Perform rollback to best partition found during local search
  rollback(performed_moves, min_cut_idx);

  HEAVY_REFINEMENT_ASSERT(best_metrics.quality == metrics::quality(_phg, Objective::cut, false),
    V(best_metrics.quality) << V(metrics::quality(_phg, Objective::cut, false)));
  HEAVY_REFINEMENT_ASSERT(best_metrics.imbalance == metrics::imbalance(_phg, _context),
          V(best_metrics.imbalance) << V(metrics::imbalance(_phg, _context)));
  return min_cut_idx > 0;
}

template<typename TypeTraits>
void SequentialTwoWayFmRefiner<TypeTraits>::activate(const HypernodeID hn) {
  if ( _border_vertices.isBorderNode(hn) ) {
    ASSERT(_vertex_state[hn] == VertexState::INACTIVE);
    const PartitionID from = _phg.partID(hn);
    const PartitionID to = 1 - from;

    ASSERT(!_pq.contains(hn, to), V(hn));
    _vertex_state[hn] = VertexState::ACTIVE;
    _pq.insert(hn, to, computeGain(hn, from, to));
    if ( _phg.partWeight(to) < _context.partition.max_part_weights[to] ) {
      _pq.enablePart(to);
    }
  }
}

/**
 * Performs delta gain update on all non locked hyperedges and
 * state transition of hyperedges.
 */
template<typename TypeTraits>
void SequentialTwoWayFmRefiner<TypeTraits>::updateNeighbors(const HypernodeID hn,
                                                            const PartitionID from,
                                                            const PartitionID to) {
  ASSERT(_phg.partID(hn) == to);

  for ( const HyperedgeID& he : _phg.incidentEdges(hn) ) {
    const PartitionID he_state = _he_state[he];
    if ( _phg.edgeSize(he) > 1 && he_state != HEState::LOCKED ) {
      deltaGainUpdate(he, from, to);
      // State Transition of hyperedge
      if ( he_state == HEState::FREE ) {
        // Vertex hn is the first vertex changed its block
        // in hyperedge he => free -> loose
        _he_state[he] = to;
      } else if ( he_state == from ) {
        // An other vertex already changed its block in opposite direction
        // => hyperedge he can not be removed from cut any more and therefore
        // it can not affect the gains of its pins => loose -> locked
        _he_state[he] = HEState::LOCKED;
      }
    }
  }
}

// ! Delta-Gain Update as decribed in [ParMar06].
template<typename TypeTraits>
void SequentialTwoWayFmRefiner<TypeTraits>::deltaGainUpdate(const HyperedgeID he,
                                                            const PartitionID from,
                                                            const PartitionID to) {
  const HypernodeID pin_count_from_part_after_move = _phg.pinCountInPart(he, from);
  const HypernodeID pin_count_to_part_after_move = _phg.pinCountInPart(he, to);

  const bool he_became_cut_he = pin_count_to_part_after_move == 1;
  const bool he_became_internal_he = pin_count_from_part_after_move == 0;
  const bool increase_necessary = pin_count_from_part_after_move == 1;
  const bool decrease_necessary = pin_count_to_part_after_move == 2;

  if ( he_became_cut_he || he_became_internal_he ||
        increase_necessary || decrease_necessary ) {
    ASSERT(_phg.edgeSize(he) != 1, V(he));
    const HyperedgeWeight he_weight = _phg.edgeWeight(he);

    if (_phg.edgeSize(he) == 2) {
      for (const HypernodeID& pin : _phg.pins(he)) {
        if ( _vertex_state[pin] == VertexState::ACTIVE ) {
          const int factor = (_phg.partID(pin) == from ? 2 : -2);
          updatePin(pin, factor * he_weight);
        }
      }
    } else if (he_became_cut_he) {
      for (const HypernodeID& pin : _phg.pins(he)) {
        if ( _vertex_state[pin] == VertexState::ACTIVE ) {
          updatePin(pin, he_weight);
        }
      }
    } else if (he_became_internal_he) {
      for (const HypernodeID& pin : _phg.pins(he)) {
        if ( _vertex_state[pin] == VertexState::ACTIVE ) {
          updatePin(pin, -he_weight);
        }
      }
    } else {
      if ( increase_necessary || decrease_necessary ) {
        for (const HypernodeID& pin : _phg.pins(he)) {
          if ( _phg.partID(pin) == from ) {
            if ( increase_necessary && _vertex_state[pin] == VertexState::ACTIVE ) {
              updatePin(pin, he_weight);
            }
          } else if ( decrease_necessary && _vertex_state[pin] == VertexState::ACTIVE  ) {
            updatePin(pin, -he_weight);
          }
        }
      }
    }
  }
}

template<typename TypeTraits>
void SequentialTwoWayFmRefiner<TypeTraits>::updatePin(const HypernodeID pin, const Gain delta) {
  const PartitionID to = 1 - _phg.partID(pin);
  ASSERT(_vertex_state[pin] == VertexState::ACTIVE, V(pin));
  ASSERT(_pq.contains(pin, to), V(pin) << V(to));
  _pq.updateKeyBy(pin, to, delta);
}

template<typename TypeTraits>
void SequentialTwoWayFmRefiner<TypeTraits>::updatePQState(const PartitionID from,
                                                          const PartitionID to) {
  if (_phg.partWeight(to) >= _context.partition.max_part_weights[to] ) {
    _pq.disablePart(to);
  }
  if (_phg.partWeight(from) < _context.partition.max_part_weights[from] ) {
    _pq.enablePart(from);
  }
}

template<typename TypeTraits>
Gain SequentialTwoWayFmRefiner<TypeTraits>::computeGain(const HypernodeID hn, const PartitionID from, const PartitionID to) {
  ASSERT(_phg.partID(hn) == from);
  ASSERT(1 - from == to);
  Gain gain = 0;
  for ( const HyperedgeID& he : _phg.incidentEdges(hn) ) {
    if ( _phg.edgeSize(he) > 1 ) {
      if ( _phg.pinCountInPart(he, to) == 0 ) {
        gain -= _phg.edgeWeight(he);
      }
      if ( _phg.pinCountInPart(he, from) == 1 ) {
        gain += _phg.edgeWeight(he);
      }
    }
  }
  return gain;
}

template<typename TypeTraits>
void SequentialTwoWayFmRefiner<TypeTraits>::rollback(const parallel::scalable_vector<HypernodeID>& performed_moves,
                                                     const size_t min_cut_idx) {
  for ( size_t i = min_cut_idx; i < performed_moves.size(); ++i ) {
    const HypernodeID hn = performed_moves[i];
    const PartitionID from = _phg.partID(hn);
    const PartitionID to = 1 - from;
    _phg.changeNodePartNoSync(hn, from, to);
  }
  _phg.resetEdgeSynchronization();
}

template<typename TypeTraits>
bool SequentialTwoWayFmRefiner<TypeTraits>::verifyPQState() const {
  for ( const HypernodeID& hn : _phg.nodes() ) {
    const PartitionID to = 1 - _phg.partID(hn);
    if ( _border_vertices.isBorderNode(hn) && _vertex_state[hn] != VertexState::MOVED ) {
      if ( !_pq.contains(hn, to) ) {
        LOG << "Hypernode" << hn << "is a border node and should be contained in the PQ";
        return false;
      }
      if ( _vertex_state[hn] != VertexState::ACTIVE ) {
        LOG << "Hypernode" << hn << "is a border node and its not moved and its state should be ACTIVE";
        return false;
      }
    } else if ( !_border_vertices.isBorderNode(hn) && _vertex_state[hn] != VertexState::MOVED ) {
      if ( _pq.contains(hn, to) ) {
        LOG << "Hypernode" << hn << "is not a border node and should be not contained in PQ";
        return false;
      }
      if ( _vertex_state[hn] != VertexState::INACTIVE ) {
        LOG << "Hypernode" << hn << "is not a border node and its not moved and its state should be INACTIVE";
        return false;
      }
    }
  }
  return true;
}

INSTANTIATE_CLASS_WITH_TYPE_TRAITS(SequentialTwoWayFmRefiner)

} // namespace mt_kahypar
