/*******************************************************************************
 * MIT License
 *
 * This file is part of Mt-KaHyPar.
 *
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

#include <tbb/enumerable_thread_specific.h>

#include "mt-kahypar/datastructures/concurrent_bucket_map.h"
#include "mt-kahypar/datastructures/sparse_map.h"
#include "mt-kahypar/parallel/stl/scalable_vector.h"
#include "mt-kahypar/partition/coarsening/multilevel/clustering_context.h"
#include "mt-kahypar/partition/context.h"


namespace mt_kahypar {

class TwoHopClustering {
  using CacheEfficienIncidenceMap = ds::FixedSizeSparseMap<HypernodeID, RatingType>;
  using LocalCountingMap = ds::DynamicSparseMap<HypernodeID, HypernodeID>;
  using AtomicID = parallel::IntegralAtomicWrapper<HypernodeID>;

  static constexpr HypernodeID LARGE_CLUSTER_DEGREE_THRESHOLD = 1000;

  static constexpr bool debug = false;

  struct MatchingEntry {
    HypernodeID target;
    HypernodeID hn;
  };

 public:
  TwoHopClustering(const HypernodeID num_nodes, const Context& context);

  TwoHopClustering(const TwoHopClustering&) = delete;
  TwoHopClustering(TwoHopClustering&&) = delete;

  TwoHopClustering & operator= (const TwoHopClustering &) = delete;
  TwoHopClustering & operator= (TwoHopClustering &&) = delete;

  template<typename Hypergraph>
  void performClustering(const Hypergraph& hg,
                         const vec<HypernodeID>& node_mapping,
                         ClusteringContext<Hypergraph>& cc);

 private:
  template<typename Hypergraph>
  void matchVerticesInBucket(const Hypergraph& hg,
                             ClusteringContext<Hypergraph>& cc,
                             vec<MatchingEntry>& bucket);

  const Context& _context;
  vec<AtomicID> _cluster_count;
  vec<LocalCountingMap> _local_cluster_count;
  ds::ConcurrentBucketMap<MatchingEntry> _favorite_clusters;
  tbb::enumerable_thread_specific<CacheEfficienIncidenceMap> _local_incidence_map;
  vec<vec<MatchingEntry>> _local_collected_nodes;
};

}  // namespace mt_kahypar
