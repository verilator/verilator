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

#pragma once

#include "mt-kahypar/definitions.h"
#include "mt-kahypar/parallel/atomic_wrapper.h"
#include "mt-kahypar/partition/coarsening/multilevel/multilevel_vertex_pair_rater.h"

namespace mt_kahypar {

class ConcurrentClusteringData {
 private:
  enum class MatchingState : uint8_t {
    UNMATCHED = 0,
    MATCHING_IN_PROGRESS = 1,
    MATCHED = 2
  };

  using AtomicMatchingState = parallel::IntegralAtomicWrapper<uint8_t>;
  using AtomicWeight = parallel::IntegralAtomicWrapper<HypernodeWeight>;
  using AtomicID = parallel::IntegralAtomicWrapper<HypernodeID>;

 public:
  ConcurrentClusteringData(HypernodeID initial_num_nodes, const Context& context);

  ConcurrentClusteringData(const ConcurrentClusteringData&) = delete;
  ConcurrentClusteringData(ConcurrentClusteringData&&) = delete;
  ConcurrentClusteringData & operator= (const ConcurrentClusteringData &) = delete;
  ConcurrentClusteringData & operator= (ConcurrentClusteringData &&) = delete;

  ~ConcurrentClusteringData();

  MT_KAHYPAR_ATTRIBUTE_ALWAYS_INLINE bool vertexIsUnmatched(const HypernodeID u) const {
    ASSERT(u < _matching_state.size());
    return _matching_state[u] == static_cast<uint8_t>(MatchingState::UNMATCHED);
  }

  MT_KAHYPAR_ATTRIBUTE_ALWAYS_INLINE const parallel::scalable_vector<AtomicWeight>& clusterWeight() const {
    return _cluster_weight;
  }

  template<typename Hypergraph>
  void initializeCoarseningPass(Hypergraph& current_hg, parallel::scalable_vector<HypernodeID>& cluster_ids);

  /*!
   * We maintain the invariant during clustering that each cluster has a unique
   * representative and all vertices also part of that cluster point to that
   * representative. Let v be the representative of a cluster C_v, then for
   * all nodes u \in C_v follows that cluster_ids[u] = v.
   * If we perform sequential clustering, we can simply set
   * cluster_ids[u] = cluster_ids[v] to maintain our invariant. However,
   * things become more complicated if we perform parallel clustering.
   * Especially, if two neighbors u and v are concurrently matched, we have
   * to guarantee that our clustering fullfils our invariant. There are mainly
   * two different cases, which needs special attention:
   *   1.) u is matched with v and v is matched with u concurrently
   *   2.) u is matched with v and v is matched an other vertex w concurrently
   * The following functions guarantees that our invariant is fullfilled, if
   * vertices are matched concurrently.
   */
  template<bool has_fixed_vertices, typename Hypergraph>
  bool matchVertices(const Hypergraph& hypergraph,
                     const HypernodeID u,
                     const HypernodeID v,
                     parallel::scalable_vector<HypernodeID>& cluster_ids,
                     MultilevelVertexPairRater& rater,
                     ds::FixedVertexSupport<Hypergraph>& fixed_vertices);

  // ! Only for testing
  template<typename Hypergraph>
  bool verifyClustering(const Hypergraph& current_hg, const parallel::scalable_vector<HypernodeID>& cluster_ids) const;

 private:
  template<bool has_fixed_vertices, typename Hypergraph>
  bool joinCluster(const Hypergraph& hypergraph,
                   const HypernodeID u,
                   const HypernodeID rep,
                   vec<HypernodeID>& cluster_ids,
                   ds::FixedVertexSupport<Hypergraph>& fixed_vertices);

  const Context& _context;
  parallel::scalable_vector<AtomicMatchingState> _matching_state;
  parallel::scalable_vector<AtomicWeight> _cluster_weight;
  parallel::scalable_vector<AtomicID> _matching_partner;
};

}  // namespace mt_kahypar
