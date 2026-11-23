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

#include "mt-kahypar/partition/coarsening/multilevel/two_hop_clustering.h"

#include <thread>

#include <tbb/parallel_for.h>

#include "mt-kahypar/definitions.h"
#include "mt-kahypar/utils/exception.h"

namespace mt_kahypar {

TwoHopClustering::TwoHopClustering(const HypernodeID num_nodes, const Context& context):
  _context(context),
  _cluster_count(num_nodes, AtomicID(0)),
  _local_cluster_count(std::thread::hardware_concurrency()),
  _favorite_clusters(),
  _local_incidence_map([this, num_nodes] {
    return CacheEfficienIncidenceMap(3UL * std::min(UL(num_nodes), this->_context.coarsening.two_hop_degree_threshold), 0.0);
  }),
  _local_collected_nodes(std::thread::hardware_concurrency()) {
    if (_context.coarsening.two_hop_cluster_size < 2) {
      throw InvalidParameterException("Value for c-two-hop-cluster-size too small, must be at least 2");
    }
  }

template<typename Hypergraph>
void TwoHopClustering::performClustering(const Hypergraph& hg,
                                         const vec<HypernodeID>& node_mapping,
                                         ClusteringContext<Hypergraph>& cc) {
  // reset
  tbb::parallel_invoke([&] {
    tbb::parallel_for(ID(0), hg.initialNumNodes(), [&](HypernodeID hn) {
      ASSERT(hn < _cluster_count.size());
      _cluster_count[hn] = 0;
    });
  }, [&] {
    for (auto& map: _local_cluster_count) {
      map.clear();
    }
    for (auto& bucket: _local_collected_nodes) {
      bucket.clear();
    }
  }, [&] {
    _favorite_clusters.clearParallel();
    _favorite_clusters.reserve_for_estimated_number_of_insertions(cc.currentNumNodes() / 3);
  });

  auto fill_incidence_map_for_node = [&](auto& incidence_map, const HypernodeID hn, bool& too_many_accesses) {
    if constexpr (Hypergraph::is_graph) {
      for (const HyperedgeID& he : hg.incidentEdges(hn)) {
        HypernodeID target_cluster = cc.clusterID(hg.edgeTarget(he));
        ASSERT(target_cluster != cc.clusterID(hn));  // we only consider unmatched nodes
        incidence_map[target_cluster] += hg.edgeWeight(he);
      }
    } else {
      size_t num_accesses = 0;
      for (const HyperedgeID& he : hg.incidentEdges(hn)) {
        const HypernodeID considered_pins = hg.edgeSize(he) - 1;
        if (num_accesses + considered_pins > _context.coarsening.two_hop_degree_threshold) {
          too_many_accesses = true;
          break;
        }

        for (const HypernodeID& pin: hg.pins(he)) {
          if (pin != hn) {
            HypernodeID target_cluster = cc.clusterID(pin);
            ASSERT(target_cluster != cc.clusterID(hn));  // we only consider unmatched nodes
            incidence_map[target_cluster] += static_cast<double>(hg.edgeWeight(he)) / considered_pins;
          }
        }
        num_accesses += considered_pins;
      }
    }
  };

  // collect unmatched (low degree) nodes and compute their favorite cluster
  tbb::parallel_for(ID(0), hg.initialNumNodes(), [&](const HypernodeID id) {
    ASSERT(id < node_mapping.size());
    const HypernodeID hn = node_mapping[id];
    if (hg.nodeIsEnabled(hn) && cc.vertexIsUnmatched(hn)
        && hg.nodeWeight(hn) <= _context.coarsening.max_allowed_node_weight / 2
        && hg.nodeDegree(hn) <= _context.coarsening.two_hop_degree_threshold) {
      CacheEfficienIncidenceMap& incidence_map = _local_incidence_map.local();
      incidence_map.clear();

      bool too_many_accesses = false;
      fill_incidence_map_for_node(incidence_map, hn, too_many_accesses);

      if (!too_many_accesses) {
        double best_connectivity = 0;
        HypernodeID best_target = kInvalidHypernode;
        for (const auto& [target_cluster, connectivity]: incidence_map) {
          if (connectivity > best_connectivity) {
            best_connectivity = connectivity;
            best_target = target_cluster;
          }
        }
        if (best_target != kInvalidHypernode) {
          const size_t thread_id = THREAD_ID;
          _local_collected_nodes[thread_id].push_back(MatchingEntry{best_target, hn});
          _local_cluster_count[thread_id][best_target]++;
        }
      }
    }
  });

  // compute the total count of incident nodes for each cluster
  tbb::parallel_for(UL(0), _local_cluster_count.size(), [&](size_t thread_id) {
    const LocalCountingMap& local_count = _local_cluster_count[thread_id];
    for (const auto& entry: local_count) {
      _cluster_count[entry.key].fetch_add(entry.value, std::memory_order_relaxed);
    }
  });

  tbb::parallel_for(UL(0), _local_collected_nodes.size(), [&](size_t thread_id) {
    vec<MatchingEntry>& local_nodes = _local_collected_nodes[thread_id];

    // insert nodes incident to "low-degree" clusters into global bucket map, so that
    // all possible contraction partners can be found
    local_nodes.erase(
      std::remove_if(local_nodes.begin(), local_nodes.end(), [&](const MatchingEntry& entry) {
        if (_cluster_count[entry.target].load(std::memory_order_relaxed) < LARGE_CLUSTER_DEGREE_THRESHOLD) {
          _favorite_clusters.insert(entry.target, MatchingEntry(entry));
          return true;
        }
        return false;
      }),
      local_nodes.end());

    // cluster nodes incident to "high-degree" clusters locally, to avoid scalability bottlenecks
    matchVerticesInBucket(hg, cc, local_nodes);
  });

  tbb::parallel_for(UL(0), _favorite_clusters.numBuckets(), [&](const size_t bucket_id) {
    auto& bucket = _favorite_clusters.getBucket(bucket_id);
    matchVerticesInBucket(hg, cc, bucket);
  });
}

template<typename Hypergraph>
void TwoHopClustering::matchVerticesInBucket(const Hypergraph& hg,
                                             ClusteringContext<Hypergraph>& cc,
                                             vec<MatchingEntry>& bucket) {
  auto bucket_comparator = [&](const MatchingEntry& lhs, const MatchingEntry& rhs) {
    if (lhs.target == rhs.target) {
      return hg.communityID(lhs.hn) < hg.communityID(rhs.hn);
    } else {
      return lhs.target < rhs.target;
    }
  };
  std::sort(bucket.begin(), bucket.end(), bucket_comparator);

  // match nodes that have the same favorite cluster
  const HypernodeID max_size = _context.coarsening.two_hop_cluster_size;
  const bool has_fixed_vertices = hg.hasFixedVertices();
  for (size_t i = 0; i + 1 < bucket.size() && cc.shouldContinue(); ++i) {
    HypernodeID offset = 0;
    for (size_t j = i + 1; j < i + max_size && j < bucket.size() && cc.shouldContinue()
          && bucket[i].target == bucket[j].target && hg.communityID(bucket[i].hn) == hg.communityID(bucket[j].hn); ++j) {
      ASSERT((j > i + 1 || cc.vertexIsUnmatched(bucket[i].hn)) && cc.vertexIsUnmatched(bucket[j].hn));

      // Note: cluster weight is checked by `matchVertices` (might not succeed)
      // contraction direction is j -> i, since only the right side is allowed to already be matched
      bool success = false;
      if (!has_fixed_vertices || cc.acceptFixedVertexContraction(hg, _context, bucket[j].hn, bucket[i].hn)) {
        success = cc.matchVertices(hg, bucket[j].hn, bucket[i].hn);
      }
      if (!success) {
        break;
      }
      offset++;
    }
    i += offset;
  }
}

namespace {
  #define PERFORM_CLUSTERING(X) void TwoHopClustering::performClustering(const X& hg,                          \
                                                                         const vec<HypernodeID>& node_mapping, \
                                                                         ClusteringContext<X>& cc)
}

INSTANTIATE_FUNC_WITH_HYPERGRAPHS(PERFORM_CLUSTERING)

}  // namespace mt_kahypar
