/*******************************************************************************
 * MIT License
 *
 * This file is part of Mt-KaHyPar.
 *
 * Copyright (C) 2023 Tobias Heuer <tobias.heuer@kit.edu>
 * Copyright (C) 2025 Nikolai Maas <nikolai.maas@kit.edu>
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

#include "mt-kahypar/utils/delete.h"

#include "mt-kahypar/definitions.h"
#include "mt-kahypar/macros.h"

namespace mt_kahypar::utils {

void delete_hypergraph(mt_kahypar_hypergraph_t hg) {
  if ( hg.hypergraph ) {
    switch ( hg.type ) {
      case STATIC_HYPERGRAPH: delete reinterpret_cast<ds::StaticHypergraph*>(hg.hypergraph); break;
      ENABLE_GRAPHS(case STATIC_GRAPH: delete reinterpret_cast<ds::StaticGraph*>(hg.hypergraph); break;)
      ENABLE_HIGHEST_QUALITY(case DYNAMIC_HYPERGRAPH: delete reinterpret_cast<ds::DynamicHypergraph*>(hg.hypergraph); break;)
      ENABLE_HIGHEST_QUALITY_FOR_GRAPHS(case DYNAMIC_GRAPH: delete reinterpret_cast<ds::DynamicGraph*>(hg.hypergraph); break;)
      case NULLPTR_HYPERGRAPH:
      default: break;
    }
  }
}

void delete_partitioned_hypergraph(mt_kahypar_partitioned_hypergraph_t phg) {
  if ( phg.partitioned_hg ) {
    switch ( phg.type ) {
      case MULTILEVEL_HYPERGRAPH_PARTITIONING: delete reinterpret_cast<StaticPartitionedHypergraph*>(phg.partitioned_hg); break;
      ENABLE_GRAPHS(case MULTILEVEL_GRAPH_PARTITIONING: delete reinterpret_cast<StaticPartitionedGraph*>(phg.partitioned_hg); break;)
      ENABLE_LARGE_K(case LARGE_K_PARTITIONING: delete reinterpret_cast<StaticSparsePartitionedHypergraph*>(phg.partitioned_hg); break;)
      ENABLE_HIGHEST_QUALITY(case N_LEVEL_HYPERGRAPH_PARTITIONING: delete reinterpret_cast<DynamicPartitionedHypergraph*>(phg.partitioned_hg); break;)
      ENABLE_HIGHEST_QUALITY_FOR_GRAPHS(case N_LEVEL_GRAPH_PARTITIONING: delete reinterpret_cast<DynamicPartitionedGraph*>(phg.partitioned_hg); break;)
      case NULLPTR_PARTITION: break;
      default: break;
    }
  }
}


}  // namespace mt_kahypar