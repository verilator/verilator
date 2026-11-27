/*******************************************************************************
 * MIT License
 *
 * This file is part of Mt-KaHyPar.
 *
 * Copyright (C) 2021 Tobias Heuer <tobias.heuer@kit.edu>
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

#include "WHFC/datastructure/flow_hypergraph.h"
#include "mt-kahypar/datastructures/hypergraph_common.h"
#include "mt-kahypar/parallel/stl/scalable_vector.h"

namespace mt_kahypar {

enum class MoveSequenceState : uint8_t {
  IN_PROGRESS = 0,
  SUCCESS = 1,
  VIOLATES_BALANCE_CONSTRAINT = 2,
  WORSEN_SOLUTION_QUALITY = 3,
  WORSEN_SOLUTION_QUALITY_WITHOUT_ROLLBACK = 4,
  TIME_LIMIT = 5
};

// Represents a sequence of vertex moves with an
// expected improvement of the solution quality if we
// apply the moves
struct MoveSequence {
  vec<Move> moves;
  Gain expected_improvement = 0; // >= 0
  MoveSequenceState state = MoveSequenceState::IN_PROGRESS;
};

struct FlowProblem {
  whfc::Node source;
  whfc::Node sink;
  HyperedgeWeight total_cut;
  HyperedgeWeight non_removable_cut;
  HypernodeWeight weight_of_block_0;
  HypernodeWeight weight_of_block_1;
};

struct Subhypergraph {
  PartitionID block_0;
  PartitionID block_1;
  vec<HypernodeID> nodes_of_block_0;
  vec<HypernodeID> nodes_of_block_1;
  HypernodeWeight weight_of_block_0;
  HypernodeWeight weight_of_block_1;
  vec<HyperedgeID> hes;
  size_t num_pins;

  size_t numNodes() const {
    return nodes_of_block_0.size() + nodes_of_block_1.size();
  }
};

inline std::ostream& operator<<(std::ostream& out, const Subhypergraph& sub_hg) {
  out << "[Nodes=" << sub_hg.numNodes()
      << ", Edges=" << sub_hg.hes.size()
      << ", Pins=" << sub_hg.num_pins
      << ", Blocks=(" << sub_hg.block_0 << "," << sub_hg.block_1 << ")"
      << ", Weights=(" << sub_hg.weight_of_block_0 << "," << sub_hg.weight_of_block_1 << ")]";
  return out;
}

} // namespace mt_kahypar