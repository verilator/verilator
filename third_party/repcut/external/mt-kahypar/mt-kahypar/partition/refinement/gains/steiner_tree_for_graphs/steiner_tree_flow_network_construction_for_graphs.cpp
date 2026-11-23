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

#include "mt-kahypar/partition/refinement/gains/steiner_tree_for_graphs/steiner_tree_flow_network_construction_for_graphs.h"

#include "mt-kahypar/definitions.h"
#include "mt-kahypar/partition/mapping/target_graph.h"

namespace mt_kahypar {

template<typename PartitionedHypergraph>
FlowNetworkEdgeParameters GraphSteinerTreeFlowNetworkConstruction::getParameters(const PartitionedHypergraph& phg,
                                                                                 const Context&,
                                                                                 const HyperedgeID he,
                                                                                 const PartitionID block_0,
                                                                                 const PartitionID block_1) {
  ASSERT(phg.hasTargetGraph());
  FlowNetworkEdgeParameters parameters;

  const TargetGraph& target_graph = *phg.targetGraph();
  const HyperedgeWeight edge_weight = phg.edgeWeight(he);
  const HypernodeID u = phg.edgeSource(he);
  const HypernodeID v = phg.edgeTarget(he);
  const PartitionID block_of_u = phg.partID(u);
  const PartitionID block_of_v = phg.partID(v);

  if ( ( block_of_u == block_0 || block_of_u == block_1 ) &&
       ( block_of_v == block_0 || block_of_v == block_1 )  ) {
    // Both endpoints of the edge are either contained in block 0 or 1.
    // Removing the edge from the cut or making it a cut edge has the
    // following gain:
    parameters.capacity = target_graph.distance(block_0, block_1) * edge_weight;
  } else {
    // In this case, only one node is contained in the flow problem and the other
    // node is part of another block different from block_0 and block_1.
    // Here, we set the capacity to difference in the steiner tree metric
    // if we would replace block_0 with block_1.
    PartitionID other_block;
    if ( block_of_u == block_0 || block_of_v == block_0 ) {
      other_block = block_of_u == block_0 ? block_of_v : block_of_u;
    } else if ( block_of_u == block_1 || block_of_v == block_1 ) {
      other_block = block_of_u == block_1 ? block_of_v : block_of_u;
    } else {
      // Can happen due to concurrent node moves applied by other flow problems
      return parameters;
    }

    ASSERT(other_block != kInvalidPartition);
    const HyperedgeWeight distance_with_block_0 = target_graph.distance(block_0, other_block);
    const HyperedgeWeight distance_with_block_1 = target_graph.distance(block_1, other_block);
    parameters.capacity = std::abs(distance_with_block_0 - distance_with_block_1) * edge_weight;

    if ( distance_with_block_0 < distance_with_block_1 ) {
      // Moving the node from block_0 to block_1 would worsen the steiner tree metric,
      // even though the edge is still cut afterwards. To model this percurlarity in the flow network,
      // we add the corresponding edge to the source.
      parameters.connect_to_source = true;
      parameters.is_cut = (block_of_u == block_1 || block_of_v == block_1);
    } else if ( distance_with_block_0 > distance_with_block_1 ) {
      // Moving the node from block_1 to block_0 would worsen the steiner tree metric,
      // even though the edge is still cut afterwards. To model this percurlarity in the flow network,
      // we add the corresponding edge to the sink.
      parameters.connect_to_sink = true;
      parameters.is_cut = (block_of_u == block_0 || block_of_v == block_0);
    }
  }
  return parameters;
}

namespace {
#define GET_PARAMETERS(X) FlowNetworkEdgeParameters GraphSteinerTreeFlowNetworkConstruction::getParameters(  \
  const X&, const Context&, const HyperedgeID, const PartitionID, const PartitionID)
}

INSTANTIATE_FUNC_WITH_PARTITIONED_HG(GET_PARAMETERS)

}  // namespace mt_kahypar
