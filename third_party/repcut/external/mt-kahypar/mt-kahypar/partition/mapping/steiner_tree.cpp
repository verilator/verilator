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

#include <cstdint>

#include "mt-kahypar/datastructures/static_bitset.h"
#include "mt-kahypar/partition/mapping/steiner_tree.h"
#include "mt-kahypar/partition/mapping/all_pair_shortest_path.h"
#include "mt-kahypar/partition/mapping/set_enumerator.h"

namespace mt_kahypar {

namespace {
MT_KAHYPAR_ATTRIBUTE_ALWAYS_INLINE size_t index(const ds::StaticBitset& set, const PartitionID k) {
  ASSERT(set.popcount() > 0);
  size_t index = 0;
  PartitionID multiplier = 1;
  PartitionID last_block = kInvalidPartition;
  for ( const PartitionID block : set ) {
    index += multiplier * block;
    multiplier *= k;
    last_block = block;
  }
  return index + (multiplier == k ? last_block * k : 0);
}

MT_KAHYPAR_ATTRIBUTE_ALWAYS_INLINE size_t index(
  const HypernodeID u, const HypernodeID v, const HypernodeID n) {
  ASSERT(u < n && v < n);
  return u + v * n;
}
} // namespace

/**
 * The following algorithm implements the Dreyfus-Wagner algorithm:
 * Dreyfus, Stuart E., and Robert A. Wagner.
 * "The Steiner problem in graphs." Networks 1.3 (1971): 195-207.
 *
 * The algorithm is based on the following property of steiner trees:
 *
 *  q o                       o s
 *     \                     /
 *      o         o         o
 *       \       / \       /
 *      p o --- o   o --- o
 *       /                 \
 *      o                   o
 *     /                     \
 *  r o                       o t
 *
 * The example above shows a steiner tree for the terminal set T = {q, r, s, t}.
 * p is non-terminal node and a junction of the steiner tree. The path from q to p
 * must be a shortest path. Otherwise, the steiner tree has not minimal weight.
 * Morover, paths connecting {p, s, t} and {p, r} in the steiner tree must be also
 * optimal steiner trees for the terminal set T' = {p, s, t} and T'' = {p, t}. Otherwise,
 * the given steiner tree would be not optimal. Thus, we can construct optimal solution for steiner
 * trees out of optimal solution of smaller steiner trees.
 *
 * The following algorithm uses dynamic programming to compute all steiner trees up to a given
 * size of the terminal set. It first computes the shortest path between all nodes and then
 * iterates over all subsets of the node set of certain size. For each subset D, we then enumerate
 * all subsets E c D and compute S_u(E) := OPT(E u { u }) + OPT(D \ E u {u}) for all nodes u \in V, where
 * OPT(E) is the optimal solution of the steiner tree problem for the terminal set E (precomputed in previous
 * step). The optimal solution for a terminal set D u { v } for an abritrary node v \in V is then
 * OPT(D u { v }) := min_{u \in V} min_{E c D} S_u(E) + shortest_path(u, v).
 *
 * The complexity of the algorithm is
 * O( n^3 + \sum_{k = 2 to m - 1} binomial(n, k) * n * ( 2^k * k + n * k ) )
 * where m is the maximum size of the precomputed terminal set
 */
void SteinerTree::compute(const ds::StaticGraph& graph,
                          const size_t max_set_size,
                          vec<HyperedgeWeight>& distances) {
  const PartitionID n = graph.initialNumNodes();
  // Floyds All-Pair Shortest Path Algorithm -> O(n^3)
  AllPairShortestPath::compute(graph, distances);

  /**
   * The following pseudocode is a more readable description of the algorithm below:
   *
   * S = distances
   * for m = 2 to max_set_size - 1 do
   *   for all subsets D of V with |D| = m do
   *     for each u in V do
   *       min_dist = inf
   *       for each proper subset E c D do
   *         F = D \ E
   *         // This computes the min_{E c D} S_u(E) term from the description above
   *         min_dist = min( min_dist, S[ E u { u } ] + S[ F u { u } ] )
   *       for each v in V do
   *         S[ D u { v } ] = min( S[ D u { v } ], S[ {u, v} ] + min_dist )
   */
  for ( size_t m = 2; m < max_set_size; ++m ) { // k - 2 steps -> k := max_set_size
    SetEnumerator subsets_of_size_m(n, m);
    // We compute for each subset D c V of size m the optimal steiner tree here
    for ( const ds::StaticBitset& d_tmp : subsets_of_size_m ) { // O(binom(n,k)) = O(n! / (k!*(n - k)!)) steps
      ds::Bitset d_set = d_tmp.copy();
      ds::StaticBitset d(d_set.numBlocks(), d_set.data());
      ASSERT(static_cast<size_t>(d.popcount()) == m);
      for ( const HypernodeID& u : graph.nodes() ) { // O(n) steps
        HyperedgeWeight min_dist = std::numeric_limits<HyperedgeWeight>::max();
        SubsetEnumerator proper_subsets_of_d(n, d);
        for ( const ds::StaticBitset& e_tmp : proper_subsets_of_d ) { // O(2^k) steps
          // Here, we iterate over all subsets E c D and compute the optimal steiner tree
          // for D with the assumption that u is the junction node of the steiner tree.
          ds::Bitset e_set = e_tmp.copy();
          ds::StaticBitset e(e_set.numBlocks(), e_set.data());
          ds::Bitset f_set = d ^ e; // F = D \ E -> compliment
          ds::StaticBitset f(f_set.numBlocks(), f_set.data());
          e_set.set(u); // Add u to E -> E u { u }
          f_set.set(u); // Add u to F -> F u { u }
          min_dist = std::min(min_dist, distances[index(e, n)] + distances[index(f, n)]);
        }
        for ( const HypernodeID& v : graph.nodes() ) { // O(n) steps
          // Compute optimal steiner tree for D u { v } with the assumption that
          // u is the junction node of the optimal steiner tree. Since the outer
          // loop iterates over all u \in V, this will compute the optimal steiner
          // tree for D u { v } at the end.
          const bool was_set = d_set.isSet(v);
          d_set.set(v); // Add v to set D -> D u { v }
          const size_t idx_d = index(d, n);
          distances[idx_d] = std::min(distances[idx_d],
            distances[index(u, v, n)] + min_dist);
          if ( !was_set ) {
            d_set.unset(v);
          }
        }
      }
    }
  }

}

}  // namespace kahypar
