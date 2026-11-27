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

#include "kahypar-resources/meta/policy_registry.h"
#include "kahypar-resources/meta/typelist.h"

#include "mt-kahypar/partition/context.h"
#include "mt-kahypar/datastructures/fixed_vertex_support.h"
#include "mt-kahypar/datastructures/hypergraph_common.h"
#include "mt-kahypar/macros.h"

namespace mt_kahypar {

class FixedVertexAcceptancePolicy final : public kahypar::meta::PolicyBase {
 public:
  // This function decides if contracting v onto u is allowed if the hypergraph contains fixed vertices.
  template<typename Hypergraph>
  MT_KAHYPAR_ATTRIBUTE_ALWAYS_INLINE static bool acceptContraction(const Hypergraph& hypergraph,
                                                                   const ds::FixedVertexSupport<Hypergraph>& fixed_vertices,
                                                                   const Context& context,
                                                                   const HypernodeID u,
                                                                   const HypernodeID v) {
    // We allow the following contractions:
    // 1.) u = Free Vertex  -> Fixed Vertex = v
    // 1.) u = Free Vertex  -> Free Vertex  = v
    // 3.) u = Fixed Vertex -> Fixed Vertex = v, but u and v must be assigned to the same fixed vertex block
    // Note that we do not allow contractions that contract fixed vertex onto a free vertex.
    // This policy is the same as used in KaHyPar.
    const bool accept_contraction = !fixed_vertices.isFixed(u) || fixed_vertices.isFixed(v);
    // If both are fixed, both vertices must be in the same block
    const bool accept_fixed_vertex_contraction =
      !( fixed_vertices.isFixed(u) && fixed_vertices.isFixed(v) ) ||
      ( fixed_vertices.fixedVertexBlock(v) == fixed_vertices.fixedVertexBlock(u) );
    return accept_contraction && accept_fixed_vertex_contraction &&
      acceptImbalance(hypergraph, fixed_vertices, context, u, v);
  }

 private:
  // During coarsening, we try to keep the partition induced by the fixed vertices balanced.
  // This gives our optimization algorithm that we run after initial partitioning more leeway to
  // improve the solution.
  template<typename Hypergraph>
  MT_KAHYPAR_ATTRIBUTE_ALWAYS_INLINE static bool acceptImbalance(const Hypergraph& hypergraph,
                                                                 const ds::FixedVertexSupport<Hypergraph>& fixed_vertices,
                                                                 const Context& context,
                                                                 const HypernodeID u,
                                                                 const HypernodeID v) {
    const bool is_fixed_u = fixed_vertices.isFixed(u);
    const bool is_fixed_v = fixed_vertices.isFixed(v);
    if ( ( is_fixed_u && is_fixed_v ) || (!is_fixed_u && !is_fixed_v) ) {
      // Contracting a fixed onto a fixed vertex, or an free onto a free vertex does
      // not increase the fixed vertex block weight.
      return true;
    }

    const HypernodeWeight max_allowed_fixed_vertex_block_weight =
      (1.0 + context.partition.epsilon) * std::ceil(
        static_cast<double>(fixed_vertices.totalFixedVertexWeight()) / context.partition.k );
    const PartitionID block_of_u = fixed_vertices.fixedVertexBlock(u);
    const PartitionID block_of_v = fixed_vertices.fixedVertexBlock(v);
    const PartitionID fixed_block = block_of_u == kInvalidPartition ? block_of_v : block_of_u;
    ASSERT(fixed_block != kInvalidPartition);
    const HypernodeWeight fixed_vertex_block_weight_after =
      fixed_vertices.fixedVertexBlockWeight(fixed_block) +
        (block_of_u == kInvalidPartition ? hypergraph.nodeWeight(u) : hypergraph.nodeWeight(v));
    return fixed_vertex_block_weight_after <=
      std::min(max_allowed_fixed_vertex_block_weight,
        context.partition.max_part_weights[fixed_block]);
  }
};

}  // namespace mt_kahypar
