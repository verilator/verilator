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

#include "mt-kahypar/datastructures/flow_network_edge_parameters.h"
#include "mt-kahypar/datastructures/hypergraph_common.h"
#include "mt-kahypar/partition/context.h"

namespace mt_kahypar {

/**
 * This struct is used by the flow network construction algorithm
 * to determine the capacity of a hyperedge and whether or not the hyperedge
 * is relevant for optimizing the objective function.
 */
struct SoedFlowNetworkConstruction {
  static constexpr bool is_exact_model = true;

  template<typename PartitionedHypergraph>
  static FlowNetworkEdgeParameters getParameters(const PartitionedHypergraph& phg,
                                                 const Context&,
                                                 const HyperedgeID he,
                                                 const PartitionID block_0,
                                                 const PartitionID block_1) {
    const PartitionID connectivity = phg.connectivity(he);
    const HypernodeID pin_count_block_0 = phg.pinCountInPart(he, block_0);
    const HypernodeID pin_count_block_1 = phg.pinCountInPart(he, block_1);
    bool might_become_uncut = connectivity == 1 ||
      ( connectivity == 2 && pin_count_block_0 > 0 && pin_count_block_1 > 0 );
    return FlowNetworkEdgeParameters( (might_become_uncut ? 2 : 1) * phg.edgeWeight(he));
  }
};

}  // namespace mt_kahypar
