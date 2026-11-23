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

#include "mt-kahypar/partition/mapping/all_pair_shortest_path.h"

namespace mt_kahypar {

namespace {
MT_KAHYPAR_ATTRIBUTE_ALWAYS_INLINE size_t index(
  const HypernodeID u, const HypernodeID v, const HypernodeID n) {
  ASSERT(u < n && v < n);
  return u + v * n;
}
} // namespace

void AllPairShortestPath::compute(const ds::StaticGraph& graph,
                                  vec<HyperedgeWeight>& distances) {
  const HypernodeID n = graph.initialNumNodes();
  ASSERT(static_cast<size_t>(n * n) <= distances.size());

  // Initialize Distance Matrix
  for ( const HypernodeID& u : graph.nodes() ) {
    distances[index(u, u, n)] = 0;
  }
  for ( const HyperedgeID& e : graph.edges() ) {
    const HypernodeID u = graph.edgeSource(e);
    const HypernodeID v = graph.edgeTarget(e);
    distances[index(u, v, n)] = graph.edgeWeight(e);
  }

  // Floyd Algorithm to compute all shortest paths (O(n^3))
  for ( HypernodeID k = 0;  k < n; ++k) {
    for ( HypernodeID u = 0; u < n; ++u ) {
      for ( HypernodeID v = 0; v < n; ++v ) {
        distances[index(u, v, n)] = std::min(distances[index(u, v, n)],
          distances[index(u, k, n)] + distances[index(k, v, n)]);
      }
    }
  }
}

}  // namespace kahypar
