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

#include "mt-kahypar/datastructures/hypergraph_common.h"
#include "mt-kahypar/macros.h"

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
 * for the cut metric.
*/
class CutRollback {

 /**
  * This class stores for a hyperedge and block the correponding data required to
  * recompute the gain values. It stores the move index of the pin that first moved out
  * (first_in) resp. last moved into the corresponding block (last_out) and the number
  * of moved pins that moved out of the block (moved_out).
  */
 public:
  static constexpr bool supports_parallel_rollback = true;

  struct RecalculationData {
    MoveID first_out, last_in;
    HypernodeID moved_out;
    RecalculationData() :
      first_out(std::numeric_limits<MoveID>::max()),
      last_in(std::numeric_limits<MoveID>::min()),
      moved_out(0)
      { }

    void reset() {
      first_out = std::numeric_limits<MoveID>::max();
      last_in = std::numeric_limits<MoveID>::min();
      moved_out = 0;
    }
  };

  // Updates the auxilliary data for a node move m with index m_id.
  static void updateMove(const MoveID m_id,
                         const Move& m,
                         vec<RecalculationData>& r) {
    r[m.from].first_out = std::min(r[m.from].first_out, m_id);
    r[m.to].last_in = std::max(r[m.to].last_in, m_id);
    ++r[m.from].moved_out;
  }

  static void updateNonMovedPinInBlock(const PartitionID,
                                       vec<RecalculationData>&) {
    // Do nothing here
  }

  template<typename PartitionedHypergraph>
  static HyperedgeWeight benefit(const PartitionedHypergraph& phg,
                                 const HyperedgeID e,
                                 const MoveID m_id,
                                 const Move& m,
                                 vec<RecalculationData>& r) {
    const HypernodeID edge_size = phg.edgeSize(e);
    // If the hyperedge was potentially a non-cut edge at some point and m is the last node
    // that moves into the corresponding block, while the first node that moves out of the corresponding
    // block is performed strictly after m, then m removes e from the cut.
    const bool was_potentially_non_cut_edge_at_some_point =
      phg.pinCountInPart(e, m.to) + r[m.to].moved_out == edge_size;
    const bool has_benefit = was_potentially_non_cut_edge_at_some_point &&
      r[m.to].last_in == m_id && m_id < r[m.to].first_out;
    return has_benefit * phg.edgeWeight(e);
  }

  template<typename PartitionedHypergraph>
  static HyperedgeWeight penalty(const PartitionedHypergraph& phg,
                                 const HyperedgeID e,
                                 const MoveID m_id,
                                 const Move& m,
                                 vec<RecalculationData>& r) {
    const HypernodeID edge_size = phg.edgeSize(e);
    // If the hyperedge was potentially a non-cut edge at some point and m is the first node
    // that moves out of the corresponding block, while the last node that moves into the corresponding
    // block is performed strictly before m, then m makes e a cut edge.
    const bool was_potentially_non_cut_edge_at_some_point =
      phg.pinCountInPart(e, m.from) + r[m.from].moved_out == edge_size;
    const bool has_penalty = was_potentially_non_cut_edge_at_some_point &&
      r[m.from].first_out == m_id && m_id > r[m.from].last_in;
    return has_penalty * phg.edgeWeight(e);
  }
};

}  // namespace mt_kahypar
