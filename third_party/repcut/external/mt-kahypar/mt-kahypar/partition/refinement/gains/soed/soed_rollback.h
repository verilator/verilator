/*******************************************************************************
 * MIT License
 *
 * This file is part of Mt-KaHyPar.
 *
 * Copyright (C) 2023 Tobias Heuer <tobias.heuer@kit.edu>
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

#include <algorithm>

#include "mt-kahypar/datastructures/hypergraph_common.h"
#include "mt-kahypar/macros.h"
#include "mt-kahypar/partition/refinement/gains/cut/cut_rollback.h"
#include "mt-kahypar/partition/refinement/gains/km1/km1_rollback.h"

namespace mt_kahypar {

/**
 * In our FM algorithm, we recompute the gain values of all node moves in the global move sequence
 * M := <m_1, ..., m_l> in parallel (see global_rollback.h).
 * Each node move m_i is of the form (u, V_i, V_j), which means that
 * node u is moved from block V_i to block V_j. Each node in this sequence is moved at most once.
 * Moreover, we assume that all node moves with an index < i are performed before m_i.
 *
 * The parallel gain recomputation algorithm iterates over all hyperedges e \in E in parallel.
 * We then iterate over the pins of e and compute some auxilliary data based on
 * which we then decide if we attribute an increase or reduction by w(e) to a moved pin.
 * This class implements the functions required by the rollback algorithm to recompute all gain values
 * for the connectivity metric.
*/
class SoedRollback {

  using CutRecalculationData = typename CutRollback::RecalculationData;
  using Km1RecalculationData = typename Km1Rollback::RecalculationData;

 public:
  static constexpr bool supports_parallel_rollback = true;

  /**
   * This class stores for a hyperedge and block the correponding data required to
   * recompute the gain values. Since the soed metric can be expressed as connectivity
   * plus cut metric, we use the rollback data of the km1 and cut rollback class.
   */
  struct RecalculationData {
    CutRecalculationData cut_data;
    Km1RecalculationData km1_data;

    RecalculationData() :
      cut_data(),
      km1_data() { }

    void reset() {
      cut_data.reset();
      km1_data.reset();
    }
  };

  // Updates the auxilliary data for a node move m with index m_id.
  static void updateMove(const MoveID m_id,
                         const Move& m,
                         vec<RecalculationData>& r) {
    r[m.to].km1_data.first_in = std::min(r[m.to].km1_data.first_in, m_id);
    r[m.from].km1_data.last_out = std::max(r[m.from].km1_data.last_out, m_id);
    r[m.from].cut_data.first_out = std::min(r[m.from].cut_data.first_out, m_id);
    r[m.to].cut_data.last_in = std::max(r[m.to].cut_data.last_in, m_id);
    ++r[m.from].cut_data.moved_out;
  }

  // Updates the number of non-moved in a block.
  static void updateNonMovedPinInBlock(const PartitionID block,
                                       vec<RecalculationData>& r) {
    r[block].km1_data.remaining_pins++;
  }

  template<typename PartitionedHypergraph>
  static HyperedgeWeight benefit(const PartitionedHypergraph& phg,
                                 const HyperedgeID e,
                                 const MoveID m_id,
                                 const Move& m,
                                 vec<RecalculationData>& r) {
    const HyperedgeWeight edge_weight = phg.edgeWeight(e);
    const HypernodeID edge_size = phg.edgeSize(e);
    // KM1 PART OF SOED METRIC
    // The node move reduces the connectivity of the currently considered hyperedge if m is the last
    // node that moves out of its corresponding block, while the first node that moves into the correponding
    // block is performed strictly after m. Furthermore, the move sequence has to move all nodes out
    // of the correspodning block (r[m.from].remaining_pins == 0).
    const bool has_km1_benefit = r[m.from].km1_data.last_out == m_id &&
      r[m.from].km1_data.first_in > m_id && r[m.from].km1_data.remaining_pins == 0;
    // CUT PART OF SOED METRIC
    // If the hyperedge was potentially a non-cut edge at some point and m is the last node
    // that moves into the corresponding block, while the first node that moves out of the corresponding
    // block is performed strictly after m, then m removes e from the cut.
    const bool was_potentially_non_cut_edge_at_some_point =
      phg.pinCountInPart(e, m.to) + r[m.to].cut_data.moved_out == edge_size;
    const bool has_cut_benefit = was_potentially_non_cut_edge_at_some_point &&
      r[m.to].cut_data.last_in == m_id && m_id < r[m.to].cut_data.first_out;
    return has_km1_benefit * edge_weight + has_cut_benefit * edge_weight;
  }

  template<typename PartitionedHypergraph>
  static HyperedgeWeight penalty(const PartitionedHypergraph& phg,
                                 const HyperedgeID e,
                                 const MoveID m_id,
                                 const Move& m,
                                 vec<RecalculationData>& r) {
    const HyperedgeWeight edge_weight = phg.edgeWeight(e);
    const HypernodeID edge_size = phg.edgeSize(e);
    // KM1 PART OF SOED METRIC
    // The node move increases the connectivity of the currently considered hyperedge if m is the
    // first node that moves into the corresponding block, while the last node that moves out of the
    // corresponding block is performed strictly before m. Furthermore, the move sequence has to move
    // all nodes out of the correspodning block (r[m.to].remaining_pins == 0).
    const bool has_km1_penalty = r[m.to].km1_data.first_in == m_id &&
      r[m.to].km1_data.last_out < m_id && r[m.to].km1_data.remaining_pins == 0;
    // CUT PART OF SOED METRIC
    // If the hyperedge was potentially a non-cut edge at some point and m is the first node
    // that moves out of the corresponding block, while the last node that moves into the corresponding
    // block is performed strictly before m, then m makes e a cut edge.
    const bool was_potentially_non_cut_edge_at_some_point =
      phg.pinCountInPart(e, m.from) + r[m.from].cut_data.moved_out == edge_size;
    const bool has_cut_penalty = was_potentially_non_cut_edge_at_some_point &&
      r[m.from].cut_data.first_out == m_id && m_id > r[m.from].cut_data.last_in;
    return has_km1_penalty * edge_weight + has_cut_penalty * edge_weight;
  }
};

}  // namespace mt_kahypar
