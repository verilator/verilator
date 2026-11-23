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
#include "mt-kahypar/utils/exception.h"

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
class SteinerTreeRollback {

 public:
  static constexpr bool supports_parallel_rollback = false;

  struct RecalculationData {
    void reset() { /** Do nothing */ }
  };

  // Updates the auxilliary data for a node move m with index m_id.
  static void updateMove(const MoveID, const Move&, vec<RecalculationData>&) {
    throw UnsupportedOperationException(
      "Parallel rollback is not supported for steiner tree metric");
  }

  // Updates the number of non-moved in a block.
  static void updateNonMovedPinInBlock(const PartitionID, vec<RecalculationData>&) {
    throw UnsupportedOperationException(
      "Parallel rollback is not supported for steiner tree metric");
  }

  template<typename PartitionedHypergraph>
  static HyperedgeWeight benefit(const PartitionedHypergraph&,
                                 const HyperedgeID,
                                 const MoveID,
                                 const Move&,
                                 vec<RecalculationData>&) {
    throw UnsupportedOperationException(
      "Parallel rollback is not supported for steiner tree metric");
    return 0;
  }

  template<typename PartitionedHypergraph>
  static HyperedgeWeight penalty(const PartitionedHypergraph&,
                                 const HyperedgeID,
                                 const MoveID,
                                 const Move&,
                                 vec<RecalculationData>&) {
    throw UnsupportedOperationException(
      "Parallel rollback is not supported for steiner tree metric");
    return 0;
  }
};

}  // namespace mt_kahypar
