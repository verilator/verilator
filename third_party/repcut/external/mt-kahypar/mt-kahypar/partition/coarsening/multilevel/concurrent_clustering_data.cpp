/*******************************************************************************
 * MIT License
 *
 * This file is part of Mt-KaHyPar.
 *
 * Copyright (C) 2019 Lars Gottesbüren <lars.gottesbueren@kit.edu>
 * Copyright (C) 2019 Tobias Heuer <tobias.heuer@kit.edu>
 * Copyright (C) 2023 Nikolai Maas <nikolai.maas@kit.edu>
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

#include "mt-kahypar/partition/coarsening/multilevel/concurrent_clustering_data.h"

#include <tbb/parallel_for.h>
#include <tbb/parallel_invoke.h>
#include <tbb/parallel_reduce.h>

#include "mt-kahypar/parallel/stl/scalable_vector.h"


#define STATE(X) static_cast<uint8_t>(X)

namespace mt_kahypar {

ConcurrentClusteringData::ConcurrentClusteringData(HypernodeID initial_num_nodes, const Context& context) :
  _context(context),
  _matching_state(),
  _cluster_weight(),
  _matching_partner() {
  // Initialize internal data structures parallel
  tbb::parallel_invoke([&] {
    _matching_state.resize(initial_num_nodes);
  }, [&] {
    _cluster_weight.resize(initial_num_nodes);
  }, [&] {
    _matching_partner.resize(initial_num_nodes);
  });
}

ConcurrentClusteringData::~ConcurrentClusteringData() {
  parallel::parallel_free(_matching_state, _cluster_weight, _matching_partner);
}

template<typename Hypergraph>
void ConcurrentClusteringData::initializeCoarseningPass(Hypergraph& current_hg,
                                                        parallel::scalable_vector<HypernodeID>& cluster_ids) {
  cluster_ids.resize(current_hg.initialNumNodes());
  tbb::parallel_for(ID(0), current_hg.initialNumNodes(), [&](const HypernodeID hn) {
    // Reset clustering
    _matching_state[hn] = STATE(MatchingState::UNMATCHED);
    _matching_partner[hn] = hn;
    cluster_ids[hn] = hn;
    if ( current_hg.nodeIsEnabled(hn) ) {
      _cluster_weight[hn] = current_hg.nodeWeight(hn);
    }
  });
}


/*!
   * We maintain the invariant during clustering that each cluster has a unique
   * representative and all vertices in the cluster point to that representative.
   * Let v be the representative of a cluster C_v, then for all nodes u \in C_v
   * follows that cluster_ids[u] = v.
   * If we perform sequential clustering, we can simply set
   * cluster_ids[u] = cluster_ids[v] to maintain our invariant. However,
   * things become more complicated if we perform parallel clustering.
   * Especially, if two neighbors u and v are concurrently matched, we have
   * to guarantee that our clustering fullfils our invariant. There are mainly
   * two different cases, which needs special attention:
   *   1.) u is matched with v and v is matched with u concurrently
   *   2.) u is matched with v and v is matched with another vertex w concurrently
   */
template<bool has_fixed_vertices, typename Hypergraph>
bool ConcurrentClusteringData::matchVertices(const Hypergraph& hypergraph,
                                             const HypernodeID u,
                                             const HypernodeID v,
                                             parallel::scalable_vector<HypernodeID>& cluster_ids,
                                             MultilevelVertexPairRater& rater,
                                             ds::FixedVertexSupport<Hypergraph>& fixed_vertices) {
  // MEMORY ORDERING AND SYNCHRONIZATION
  // During the clustering, there are concurrent memory accesses to the following 4 locations:
  // _matching_state, cluster_ids, _matching_partner and _cluster_weight.
  // We use _matching_state to synchronize accesses to cluster_ids with acquire/release semantics, while
  // _matching_partner and _cluster_weight don't require synchronization. In more detail (see also PR #193):
  //   1. We read cluster_ids[v] to determine the representative for joinCluster if v is already matched.
  //      This is synchronized by using release ordering when writing the MATCHED state to _matching_state
  //      and always checking _matching_state[v] with acquire ordering before accessing cluster_ids[v]
  //   2. _matching_partner is used for conflict resolution. Since the conflict resolution loops until
  //      a stable state is detected, no explicit synchronization is necessary and relaxed ordering suffices
  //   3. Updating _cluster_weight might cause a race condition in joinCluster. However, this just causes the
  //      cluster to exceed the allowed weight. This is acceptable since it rarely happens in practice

  ASSERT(u < hypergraph.initialNumNodes());
  ASSERT(v < hypergraph.initialNumNodes());
  const uint8_t matched = STATE(MatchingState::MATCHED);
  const uint8_t match_in_progress = STATE(MatchingState::MATCHING_IN_PROGRESS);

  // Indicates that u wants to join the cluster of v.
  // Will be important later for conflict resolution.
  bool success = false;
  const HypernodeWeight weight_u = hypergraph.nodeWeight(u);
  HypernodeWeight weight_v = _cluster_weight[v].load(std::memory_order_relaxed);
  if ( weight_u + weight_v <= _context.coarsening.max_allowed_node_weight ) {
    uint8_t expect_unmatched_u = STATE(MatchingState::UNMATCHED);
    if ( _matching_state[u].compare_exchange_strong(expect_unmatched_u, match_in_progress, std::memory_order_relaxed) ) {
      _matching_partner[u].store(v, std::memory_order_relaxed);
      // Current thread gets "ownership" for vertex u. Only threads with "ownership"
      // can change the cluster id of a vertex.

      uint8_t expect_unmatched_v = STATE(MatchingState::UNMATCHED);
      uint8_t matching_state_v = _matching_state[v].load(std::memory_order_acquire);
      if ( matching_state_v == matched ) {
        // Vertex v is already matched and will not change it cluster id any more.
        // In that case, it is safe to set the cluster id of u to the cluster id of v.
        const HypernodeID rep = cluster_ids[v];
        ASSERT(_matching_state[rep] == matched);
        success = joinCluster<has_fixed_vertices>(hypergraph, u, rep, cluster_ids, fixed_vertices);
      } else if ( matching_state_v == expect_unmatched_v &&
                  _matching_state[v].compare_exchange_strong(expect_unmatched_v, match_in_progress, std::memory_order_relaxed) ) {
        // Current thread has the "ownership" for u and v and can change the cluster id
        // of both vertices thread-safe.
        success = joinCluster<has_fixed_vertices>(hypergraph, u, v, cluster_ids, fixed_vertices);
        _matching_state[v].store(matched, std::memory_order_release);
      } else {
        // State of v must be either MATCHING_IN_PROGRESS or an other thread changed the state
        // in the meantime to MATCHED. We have to wait until the state of v changed to
        // MATCHED or resolve the conflict if u is matched within a cyclic matching dependency

        // Conflict Resolution
        do {
          // Check if current vertex is in a cyclic matching dependency
          HypernodeID cur_u = u;
          HypernodeID smallest_node_id_in_cycle = cur_u;
          while (true) {
            HypernodeID next_u = _matching_partner[cur_u].load(std::memory_order_relaxed);
            if (next_u != u && next_u != cur_u) {
              cur_u = next_u;
              smallest_node_id_in_cycle = std::min(smallest_node_id_in_cycle, cur_u);
            } else {
              break;
            }
          }

          // Resolve cyclic matching dependency
          // Vertex with smallest id starts to resolve conflict
          const bool is_in_cyclic_dependency = _matching_partner[cur_u].load(std::memory_order_relaxed) == u;
          if ( is_in_cyclic_dependency && u == smallest_node_id_in_cycle) {
            success = joinCluster<has_fixed_vertices>(hypergraph, u, v, cluster_ids, fixed_vertices);
            _matching_state[v].store(matched, std::memory_order_release);
          }
        } while ( _matching_state[v].load(std::memory_order_acquire) == match_in_progress );
        // note: the loop provides acquire semantics for the block below

        // If u is still in state MATCHING_IN_PROGRESS its matching partner v
        // must be matched in the meantime with an other vertex. Therefore,
        // we try to match u with the representative v's cluster.
        if ( _matching_state[u].load(std::memory_order_relaxed) == match_in_progress ) {
          ASSERT( _matching_state[v] == matched );
          const HypernodeID rep = cluster_ids[v];
          success = joinCluster<has_fixed_vertices>(hypergraph, u, rep, cluster_ids, fixed_vertices);
        }
      }
      rater.markAsMatched(u);
      rater.markAsMatched(v);
      _matching_partner[u].store(u, std::memory_order_relaxed);
      _matching_state[u].store(matched, std::memory_order_release);
    }
  }
  return success;
}

// ! Only for testing
template<typename Hypergraph>
bool ConcurrentClusteringData::verifyClustering(const Hypergraph& current_hg,
                                                const parallel::scalable_vector<HypernodeID>& cluster_ids) const {
  parallel::scalable_vector<HypernodeWeight> expected_weights(current_hg.initialNumNodes());
  // Verify that clustering is correct
  for ( const HypernodeID& hn : current_hg.nodes() ) {
    const HypernodeID u = hn;
    const HypernodeID root_u = cluster_ids[u];
    if ( root_u != cluster_ids[root_u] ) {
      LOG << "Hypernode" << u << "is part of cluster" << root_u << ", but cluster"
          << root_u << "is also part of cluster" << cluster_ids[root_u];
      return false;
    }
    expected_weights[root_u] += current_hg.nodeWeight(hn);
  }

  // Verify that cluster weights are aggregated correct
  for ( const HypernodeID& hn : current_hg.nodes() ) {
    const HypernodeID u = hn;
    const HypernodeID root_u = cluster_ids[u];
    if ( root_u == u && expected_weights[u] != _cluster_weight[u] ) {
      LOG << "The expected weight of cluster" << u << "is" << expected_weights[u]
          << ", but currently it is" << _cluster_weight[u];
      return false;
    }
  }
  return true;
}

template<bool has_fixed_vertices, typename Hypergraph>
bool ConcurrentClusteringData::joinCluster(const Hypergraph& hypergraph,
                                           const HypernodeID u,
                                           const HypernodeID rep,
                                           vec<HypernodeID>& cluster_ids,
                                           ds::FixedVertexSupport<Hypergraph>& fixed_vertices) {
  ASSERT(rep == cluster_ids[rep]);
  bool success = false;
  const HypernodeWeight weight_of_u = hypergraph.nodeWeight(u);
  const HypernodeWeight weight_of_rep = _cluster_weight[rep].load(std::memory_order_relaxed);
  bool cluster_join_operation_allowed =
    weight_of_u + weight_of_rep <= _context.coarsening.max_allowed_node_weight;
  if constexpr ( has_fixed_vertices ) {
    if ( cluster_join_operation_allowed ) {
      cluster_join_operation_allowed = fixed_vertices.contract(rep, u);
    }
  }
  if ( cluster_join_operation_allowed ) {
    cluster_ids[u] = rep;
    _cluster_weight[rep].fetch_add(weight_of_u, std::memory_order_relaxed);
    success = true;
  }
  return success;
}

namespace {
  #define INITIALIZE_PASS(X) void ConcurrentClusteringData::initializeCoarseningPass(                         \
                                      X& current_hg, parallel::scalable_vector<HypernodeID>& cluster_ids)

  #define MATCH_VERTICES(X) bool ConcurrentClusteringData::matchVertices<false>(const X& hypergraph, const HypernodeID u, \
                                   const HypernodeID v, parallel::scalable_vector<HypernodeID>& cluster_ids,              \
                                   MultilevelVertexPairRater& rater, ds::FixedVertexSupport<X>& fixed_vertices)
  #define MATCH_VERTICES_FIXED(X) bool ConcurrentClusteringData::matchVertices<true>(const X& hypergraph,              \
                                         const HypernodeID u, const HypernodeID v,                                     \
                                         parallel::scalable_vector<HypernodeID>& cluster_ids,                          \
                                         MultilevelVertexPairRater& rater, ds::FixedVertexSupport<X>& fixed_vertices)

  #define VERIFY_CLUSTERING(X) bool ConcurrentClusteringData::verifyClustering(const X& current_hg,           \
                                        const parallel::scalable_vector<HypernodeID>& cluster_ids) const
}

INSTANTIATE_FUNC_WITH_HYPERGRAPHS(INITIALIZE_PASS)
INSTANTIATE_FUNC_WITH_HYPERGRAPHS(MATCH_VERTICES)
INSTANTIATE_FUNC_WITH_HYPERGRAPHS(MATCH_VERTICES_FIXED)
INSTANTIATE_FUNC_WITH_HYPERGRAPHS(VERIFY_CLUSTERING)

}  // namespace mt_kahypar
