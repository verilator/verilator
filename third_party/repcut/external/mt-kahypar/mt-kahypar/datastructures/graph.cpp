/*******************************************************************************
 * MIT License
 *
 * This file is part of Mt-KaHyPar.
 *
 * Copyright (C) 2019 Lars Gottesbüren <lars.gottesbueren@kit.edu>
 * Copyright (C) 2019 Tobias Heuer <tobias.heuer@kit.edu>
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

#include "graph.h"


#include <tbb/parallel_for.h>
#include <tbb/parallel_reduce.h>
#include <tbb/parallel_invoke.h>
#include <tbb/enumerable_thread_specific.h>

#include "mt-kahypar/definitions.h"
#include "mt-kahypar/parallel/parallel_prefix_sum.h"
#include "mt-kahypar/parallel/atomic_wrapper.h"
#include "mt-kahypar/parallel/parallel_counting_sort.h"
#include "mt-kahypar/parallel/thread_management.h"
#include "mt-kahypar/utils/exception.h"
#include "mt-kahypar/utils/timer.h"

namespace mt_kahypar::ds {

  template<typename Hypergraph>
  Graph::Graph(Hypergraph& hypergraph, const LouvainEdgeWeight edge_weight_type, bool is_graph) :
    _num_nodes(0),
    _num_arcs(0),
    _total_volume(0),
    _max_degree(0),
    _indices(),
    _arcs(),
    _node_volumes(),
    _tmp_graph_buffer(nullptr) {

    switch( edge_weight_type ) {
      case LouvainEdgeWeight::uniform:
        construct(hypergraph, is_graph,
                  [&](const HyperedgeWeight edge_weight,
                      const HypernodeID,
                      const HyperedgeID) {
                    return static_cast<ArcWeight>(edge_weight);
                  });
        break;
      case LouvainEdgeWeight::non_uniform:
        construct(hypergraph, is_graph,
                  [&](const HyperedgeWeight edge_weight,
                      const HypernodeID edge_size,
                      const HyperedgeID) {
                    return static_cast<ArcWeight>(edge_weight) /
                           static_cast<ArcWeight>(edge_size);
                  });
        break;
      case LouvainEdgeWeight::degree:
        construct(hypergraph, is_graph,
                  [&](const HyperedgeWeight edge_weight,
                      const HypernodeID edge_size,
                      const HyperedgeID node_degree) {
                    return static_cast<ArcWeight>(edge_weight) *
                           (static_cast<ArcWeight>(node_degree) /
                            static_cast<ArcWeight>(edge_size));
                  });
        break;
      case LouvainEdgeWeight::hybrid:
      case LouvainEdgeWeight::UNDEFINED:
      throw InvalidInputException("No valid louvain edge weight");
    }
  }

  Graph::Graph(Graph&& other) :
    _num_nodes(other._num_nodes),
    _num_arcs(other._num_arcs),
    _total_volume(other._total_volume),
    _max_degree(other._max_degree),
    _indices(std::move(other._indices)),
    _arcs(std::move(other._arcs)),
    _node_volumes(std::move(other._node_volumes)),
    _tmp_graph_buffer(other._tmp_graph_buffer) {
    other._num_nodes = 0;
    other._num_arcs = 0;
    other._total_volume = 0;
    other._max_degree = 0;
    other._tmp_graph_buffer = nullptr;
  }

  Graph& Graph::operator= (Graph&& other) {
    _num_nodes = other._num_nodes;
    _num_arcs = other._num_arcs;
    _total_volume = other._total_volume;
    _max_degree = other._max_degree;
    _indices = std::move(other._indices);
    _arcs = std::move(other._arcs);
    _node_volumes = std::move(other._node_volumes);
    _tmp_graph_buffer = std::move(other._tmp_graph_buffer);
    other._num_nodes = 0;
    other._num_arcs = 0;
    other._total_volume = 0;
    other._max_degree = 0;
    other._tmp_graph_buffer = nullptr;
    return *this;
  }

  Graph::~Graph() {
    if ( _tmp_graph_buffer ) {
      delete(_tmp_graph_buffer);
    }
  }

  Graph Graph::contract_low_memory(Clustering& communities) {
    // map cluster IDs to consecutive range
    vec<NodeID> mapping(numNodes(), 0);   // TODO use memory pool?
    tbb::parallel_for(UL(0), numNodes(), [&](NodeID u) { mapping[communities[u]] = 1; });
    parallel_prefix_sum(mapping.begin(), mapping.begin() + numNodes(), mapping.begin(), std::plus<>(), 0);
    NodeID num_coarse_nodes = mapping[numNodes() - 1];
    // apply mapping to cluster IDs. subtract one because prefix sum is inclusive
    tbb::parallel_for(UL(0), numNodes(), [&](NodeID u) { communities[u] = mapping[communities[u]] - 1; });

    // sort nodes by cluster
    auto get_cluster = [&](NodeID u) { assert(u < communities.size()); return communities[u]; };
    vec<NodeID> nodes_sorted_by_cluster(std::move(mapping));    // reuse memory from mapping since it's no longer needed
    auto cluster_bounds = parallel::counting_sort(nodes(), nodes_sorted_by_cluster, num_coarse_nodes,
                                                  get_cluster, parallel::total_number_of_threads());

    Graph coarse_graph;
    coarse_graph._num_nodes = num_coarse_nodes;
    coarse_graph._indices.resize(num_coarse_nodes + 1);
    coarse_graph._node_volumes.resize(num_coarse_nodes);
    coarse_graph._total_volume = totalVolume();

    struct ClearList {
      vec<NodeID> used;
      vec<ArcWeight> values;

      ClearList(size_t n) : values(n, 0.0) { }
    };
    tbb::enumerable_thread_specific<ClearList> clear_lists(num_coarse_nodes);
    tbb::enumerable_thread_specific<size_t> local_max_degree(0);

    // first pass generating unique coarse arcs to determine coarse node degrees
    tbb::parallel_for(ID(0), num_coarse_nodes, [&](NodeID cu) {
      auto& clear_list = clear_lists.local();
      ArcWeight volume_cu = 0.0;
      for (auto i = cluster_bounds[cu]; i < cluster_bounds[cu + 1]; ++i) {
        NodeID fu = nodes_sorted_by_cluster[i];
        volume_cu += nodeVolume(fu);
        for (const Arc& arc : arcsOf(fu)) {
          NodeID cv = get_cluster(arc.head);
          if (cv != cu && clear_list.values[cv] == 0.0) {
            clear_list.used.push_back(cv);
            clear_list.values[cv] = 1.0;
          }
        }
      }
      coarse_graph._indices[cu + 1] = clear_list.used.size();
      local_max_degree.local() = std::max(local_max_degree.local(), clear_list.used.size());
      for (const NodeID cv : clear_list.used) {
        clear_list.values[cv] = 0.0;
      }
      clear_list.used.clear();
      coarse_graph._node_volumes[cu] = volume_cu;
    });

    // prefix sum coarse node degrees for offsets to write the coarse arcs in second pass
    parallel_prefix_sum(coarse_graph._indices.begin(), coarse_graph._indices.end(), coarse_graph._indices.begin(), std::plus<>(), UL(0));
    size_t num_coarse_arcs = coarse_graph._indices.back();
    coarse_graph._arcs.resize(num_coarse_arcs);
    coarse_graph._num_arcs = num_coarse_arcs;
    coarse_graph._max_degree = local_max_degree.combine([](size_t lhs, size_t rhs) { return std::max(lhs, rhs); });

    // second pass generating unique coarse arcs
    tbb::parallel_for(ID(0), num_coarse_nodes, [&](NodeID cu) {
      auto& clear_list = clear_lists.local();
      for (auto i = cluster_bounds[cu]; i < cluster_bounds[cu+1]; ++i) {
        for (const Arc& arc : arcsOf(nodes_sorted_by_cluster[i])) {
          NodeID cv = get_cluster(arc.head);
          if (cv != cu) {
            if (clear_list.values[cv] == 0.0) {
              clear_list.used.push_back(cv);
            }
            clear_list.values[cv] += arc.weight;
          }
        }
      }
      size_t pos = coarse_graph._indices[cu];
      for (const NodeID cv : clear_list.used) {
        coarse_graph._arcs[pos++] = Arc(cv, clear_list.values[cv]);
        clear_list.values[cv] = 0.0;
      }
      clear_list.used.clear();
    });

    return coarse_graph;
  }


  /*!
 * Contracts the graph based on the community structure passed as argument.
 * In the first step the community ids are compactified (via parallel prefix sum)
 * which also determines the node ids in the coarse graph. Afterwards, we create
 * a temporary graph which contains all arcs that will not form a selfloop in the
 * coarse graph. Finally, the weights of each multiedge in that temporary graph
 * are aggregated and the result is written to the final contracted graph.
 */
  Graph Graph::contract(Clustering& communities, bool low_memory) {
    if (low_memory) {
      return contract_low_memory(communities);
    }
    ASSERT(canBeUsed());
    ASSERT(_num_nodes == communities.size());
    if ( !_tmp_graph_buffer ) {
      allocateContractionBuffers();
    }
    Graph coarse_graph;
    coarse_graph._total_volume = _total_volume;

    // #################### STAGE 1 ####################
    // Compute node ids of coarse graph with a parallel prefix sum
    parallel::scalable_vector<size_t> mapping(_num_nodes, UL(0));
    ds::Array<parallel::IntegralAtomicWrapper<size_t>>& tmp_pos = _tmp_graph_buffer->tmp_pos;
    ds::Array<parallel::IntegralAtomicWrapper<size_t>>& tmp_indices = _tmp_graph_buffer->tmp_indices;
    ds::Array<parallel::AtomicWrapper<ArcWeight>>& coarse_node_volumes = _tmp_graph_buffer->tmp_node_volumes;
    tbb::parallel_for(ID(0), static_cast<NodeID>(_num_nodes), [&](const NodeID u) {
      ASSERT(static_cast<size_t>(communities[u]) < _num_nodes);
      mapping[communities[u]] = UL(1);
      tmp_pos[u] = 0;
      tmp_indices[u] = 0;
      coarse_node_volumes[u].store(0.0);
    });

    // Prefix sum determines node ids in coarse graph
    parallel::TBBPrefixSum<size_t> mapping_prefix_sum(mapping);
    tbb::parallel_scan(tbb::blocked_range<size_t>(UL(0), _num_nodes), mapping_prefix_sum);

    // Remap community ids
    coarse_graph._num_nodes = mapping_prefix_sum.total_sum();
    tbb::parallel_for(ID(0), static_cast<NodeID>(_num_nodes), [&](const NodeID u) {
      communities[u] = mapping_prefix_sum[communities[u]];
    });

    // #################### STAGE 2 ####################
    // Write all arcs, that will not form a selfloop in the coarse graph, into a tmp
    // adjacence array. For that, we compute a prefix sum over the sum of all arcs
    // in each community (which are no selfloop) and write them in parallel to
    // the tmp adjacence array.
    // Compute number of arcs in tmp adjacence array with parallel prefix sum
    ASSERT(coarse_graph._num_nodes <= coarse_node_volumes.size());
    tbb::parallel_for(ID(0), static_cast<NodeID>(_num_nodes), [&](const NodeID u) {
      const NodeID coarse_u = communities[u];
      ASSERT(static_cast<size_t>(coarse_u) < coarse_graph._num_nodes);
      coarse_node_volumes[coarse_u] += nodeVolume(u);     // not deterministic!
      for ( const Arc& arc : arcsOf(u) ) {
        const NodeID coarse_v = communities[arc.head];
        if ( coarse_u != coarse_v ) {
          ++tmp_indices[coarse_u];
        }
      }
    });

    parallel::TBBPrefixSum<parallel::IntegralAtomicWrapper<size_t>, ds::Array> tmp_indices_prefix_sum(tmp_indices);
    tbb::parallel_scan(tbb::blocked_range<size_t>(UL(0), _num_nodes), tmp_indices_prefix_sum);

    // Write all arcs into corresponding tmp adjacence array blocks
    ds::Array<Arc>& tmp_arcs = _tmp_graph_buffer->tmp_arcs;
    ds::Array<size_t>& valid_arcs = _tmp_graph_buffer->valid_arcs;
    tbb::parallel_for(ID(0), static_cast<NodeID>(_num_nodes), [&](const NodeID u) {
      const NodeID coarse_u = communities[u];
      ASSERT(static_cast<size_t>(coarse_u) < coarse_graph._num_nodes);
      for ( const Arc& arc : arcsOf(u) ) {
        const NodeID coarse_v = communities[arc.head];
        if ( coarse_u != coarse_v ) {
          const size_t tmp_arcs_pos = tmp_indices_prefix_sum[coarse_u] + tmp_pos[coarse_u]++;
          ASSERT(tmp_arcs_pos < tmp_indices_prefix_sum[coarse_u + 1]);
          tmp_arcs[tmp_arcs_pos] = Arc { coarse_v, arc.weight };
          valid_arcs[tmp_arcs_pos] = UL(1);
        }
      }
    });

    // #################### STAGE 3 ####################
    // Aggregate weights of arcs that are equal in each community.
    // Therefore, we sort the arcs according to their endpoints
    // and aggregate weight of arcs with equal endpoints.
    tbb::enumerable_thread_specific<size_t> local_max_degree(0);
    tbb::parallel_for(ID(0), static_cast<NodeID>(coarse_graph._num_nodes), [&](const NodeID u) {
      const size_t tmp_arc_start = tmp_indices_prefix_sum[u];
      const size_t tmp_arc_end = tmp_indices_prefix_sum[u + 1];
      // commented out comparison is needed for deterministic arc weights
      // auto comp = [](const Arc& lhs, const Arc& rhs) { return std::tie(lhs.head, lhs.weight) < std::tie(rhs.head, rhs.weight); };
      auto comp = [](const Arc& lhs, const Arc& rhs) { return lhs.head < rhs.head; };
      std::sort(tmp_arcs.begin() + tmp_arc_start, tmp_arcs.begin() + tmp_arc_end, comp);

      size_t arc_rep = tmp_arc_start;
      size_t degree = tmp_arc_start < tmp_arc_end ? 1 : 0;
      for ( size_t pos = tmp_arc_start + 1; pos < tmp_arc_end; ++pos ) {
        if ( tmp_arcs[arc_rep].head == tmp_arcs[pos].head ) {
          tmp_arcs[arc_rep].weight += tmp_arcs[pos].weight;
          valid_arcs[pos] = UL(0);
        } else {
          arc_rep = pos;
          ++degree;
        }
      }
      local_max_degree.local() = std::max(local_max_degree.local(), degree);
    });
    coarse_graph._max_degree = local_max_degree.combine(
            [&](const size_t& lhs, const size_t& rhs) {
              return std::max(lhs, rhs);
            });

    // Write all arcs to coarse graph
    parallel::TBBPrefixSum<size_t, ds::Array> valid_arcs_prefix_sum(valid_arcs);
    tbb::parallel_scan(tbb::blocked_range<size_t>(UL(0),
                                                  tmp_indices_prefix_sum.total_sum()), valid_arcs_prefix_sum);
    coarse_graph._num_arcs = valid_arcs_prefix_sum.total_sum();

    // Move memory down to coarse graph
    coarse_graph._indices = std::move(_indices);
    coarse_graph._arcs = std::move(_arcs);
    coarse_graph._node_volumes = std::move(_node_volumes);

    tbb::parallel_invoke([&] {
      const size_t tmp_num_arcs = tmp_indices_prefix_sum.total_sum();
      tbb::parallel_for(UL(0), tmp_num_arcs, [&](const size_t i) {
        if ( valid_arcs_prefix_sum.value(i) ) {
          const size_t pos = valid_arcs_prefix_sum[i];
          ASSERT(pos < coarse_graph._num_arcs);
          coarse_graph._arcs[pos] = tmp_arcs[i];
        }
      });
    }, [&] {
      tbb::parallel_for(ID(0), static_cast<NodeID>(coarse_graph._num_nodes), [&](const NodeID u) {
        const size_t start_index_pos = valid_arcs_prefix_sum[tmp_indices_prefix_sum[u]];
        ASSERT(start_index_pos <= coarse_graph._num_arcs);
        coarse_graph._indices[u] = start_index_pos;
        coarse_graph._node_volumes[u] = coarse_node_volumes[u];
      });
      coarse_graph._indices[coarse_graph._num_nodes] = coarse_graph._num_arcs;
    });
    coarse_graph._tmp_graph_buffer = _tmp_graph_buffer;
    _tmp_graph_buffer = nullptr;

    return coarse_graph;
  }

  Graph::Graph() :
    _num_nodes(0),
    _num_arcs(0),
    _total_volume(0),
    _max_degree(0),
    _indices(),
    _arcs(),
    _node_volumes(),
    _tmp_graph_buffer(nullptr) { }

  /*!
   * Constructs a graph from a given hypergraph.
   */
  template<typename Hypergraph, typename F>
  void Graph::construct(const Hypergraph& hypergraph,
                        const bool is_graph,
                        const F& edge_weight_func) {
    if ( is_graph ) {
      ASSERT(hypergraph.maxEdgeSize() == 2);
      _num_nodes = hypergraph.initialNumNodes();
      _num_arcs = hypergraph.initialNumPins();
      constructGraph(hypergraph, edge_weight_func);
    } else {
      _num_nodes = hypergraph.initialNumNodes() + hypergraph.initialNumEdges();
      _num_arcs = 2 * hypergraph.initialNumPins();
      constructBipartiteGraph(hypergraph, edge_weight_func);
    }

    // deterministic reduce of node volumes since double addition is not commutative or associative
    // node volumes are computed in for loop because deterministic reduce does not have dynamic load balancing
    // whereas for loop does. this important since each node incurs O(degree) time
    tbb::parallel_for(ID(0), static_cast<NodeID>(numNodes()), [&](NodeID u) { computeNodeVolume(u); });

    auto aggregate_volume = [&](const tbb::blocked_range<NodeID>& r, ArcWeight partial_volume) -> ArcWeight {
      for (NodeID u = r.begin(); u < r.end(); ++u) {
        partial_volume += nodeVolume(u);
      }
      return partial_volume;
    };
    auto r = tbb::blocked_range<NodeID>(ID(0), numNodes(), 1000);
    _total_volume = tbb::parallel_deterministic_reduce(r, 0.0, aggregate_volume, std::plus<>());
  }

  template<typename Hypergraph, typename F>
  void Graph::constructBipartiteGraph(const Hypergraph& hypergraph, F& edge_weight_func) {
    _indices.resize("Preprocessing", "indices", _num_nodes + 1);
    _arcs.resize("Preprocessing", "arcs", _num_arcs);
    _node_volumes.resize("Preprocessing", "node_volumes", _num_nodes);

    // Initialize data structure
    const HypernodeID num_hypernodes = hypergraph.initialNumNodes();
    const HypernodeID num_hyperedges = hypergraph.initialNumEdges();
    tbb::parallel_invoke([&] {
      tbb::parallel_for(ID(0), num_hypernodes, [&](const HypernodeID u) {
        ASSERT(u + 1 < _indices.size());
        _indices[u + 1] = hypergraph.nodeDegree(u);
      });
    }, [&] {
      tbb::parallel_for(num_hypernodes, num_hypernodes + num_hyperedges, [&](const HyperedgeID u) {
        ASSERT(u + 1 < _indices.size());
        const HyperedgeID he = u - num_hypernodes;
        _indices[u + 1] = hypergraph.edgeSize(he);
      });
    });

    parallel::TBBPrefixSum<size_t, ds::Array> indices_prefix_sum(_indices);
    tbb::parallel_scan(tbb::blocked_range<size_t>(UL(0), _indices.size()), indices_prefix_sum);

    tbb::enumerable_thread_specific<size_t> local_max_degree(0);
    tbb::parallel_invoke([&] {
      tbb::parallel_for(ID(0), num_hypernodes, [&](const HypernodeID u) {
        ASSERT(u + 1 < _indices.size());
        size_t pos = _indices[u];
        const HypernodeID hn = u;
        const HyperedgeID node_degree = hypergraph.nodeDegree(hn);
        local_max_degree.local() = std::max(
                local_max_degree.local(), static_cast<size_t>(node_degree));
        for ( const HyperedgeID& he : hypergraph.incidentEdges(hn) ) {
          const NodeID v = he + num_hypernodes;
          const HyperedgeWeight edge_weight = hypergraph.edgeWeight(he);
          const HypernodeID edge_size = hypergraph.edgeSize(he);
          ASSERT(pos < _indices[u + 1]);
          _arcs[pos++] = Arc(v, edge_weight_func(edge_weight, edge_size, node_degree));
        }
      });
    }, [&] {
      tbb::parallel_for(num_hypernodes, num_hypernodes + num_hyperedges, [&](const HyperedgeID u) {
        ASSERT(u + 1 < _indices.size());
        size_t pos = _indices[u];
        const HyperedgeID he = u - num_hypernodes;
        const HyperedgeWeight edge_weight = hypergraph.edgeWeight(he);
        const HypernodeID edge_size = hypergraph.edgeSize(he);
        local_max_degree.local() = std::max(
                local_max_degree.local(), static_cast<size_t>(edge_size));
        for ( const HypernodeID& pin : hypergraph.pins(he) ) {
          const NodeID v = pin;
          const HyperedgeID node_degree = hypergraph.nodeDegree(pin);
          ASSERT(pos < _indices[u + 1]);
          _arcs[pos++] = Arc(v, edge_weight_func(edge_weight, edge_size, node_degree));
        }
      });
    });
    _max_degree = local_max_degree.combine([&](const size_t& lhs, const size_t& rhs) {
      return std::max(lhs, rhs);
    });
  }

  template<typename Hypergraph, typename F>
  void Graph::constructGraph(const Hypergraph& hypergraph, const F& edge_weight_func) {
    _indices.resize("Preprocessing", "indices", _num_nodes + 1);
    _arcs.resize("Preprocessing", "arcs", _num_arcs);
    _node_volumes.resize("Preprocessing", "node_volumes", _num_nodes);

    // Initialize data structure
    const HypernodeID num_hypernodes = hypergraph.initialNumNodes();
    tbb::parallel_for(ID(0), num_hypernodes, [&](const HypernodeID u) {
      ASSERT(u + 1 < _indices.size());
      _indices[u + 1] = hypergraph.nodeDegree(u);
    });

    parallel::TBBPrefixSum<size_t, ds::Array> indices_prefix_sum(_indices);
    tbb::parallel_scan(tbb::blocked_range<size_t>(UL(0), num_hypernodes + 1), indices_prefix_sum);

    tbb::enumerable_thread_specific<size_t> local_max_degree(0);
    tbb::parallel_for(ID(0), num_hypernodes, [&](const HypernodeID u) {
      ASSERT(u + 1 < _indices.size());
      size_t pos = _indices[u];
      const HypernodeID hn = u;
      const HyperedgeID node_degree = hypergraph.nodeDegree(hn);
      local_max_degree.local() = std::max(
              local_max_degree.local(), static_cast<size_t>(node_degree));
      for ( const HyperedgeID& he : hypergraph.incidentEdges(hn) ) {
        const HyperedgeWeight edge_weight = hypergraph.edgeWeight(he);
        NodeID v = std::numeric_limits<NodeID>::max();
        for ( const HypernodeID& pin : hypergraph.pins(he) ) {
          if ( pin != hn ) {
            v = pin;
            break;
          }
        }
        ASSERT(v != std::numeric_limits<NodeID>::max());
        ASSERT(pos < _indices[u + 1]);
        _arcs[pos++] = Arc(v, edge_weight_func(edge_weight, ID(2), node_degree));
      }
    });
    _max_degree = local_max_degree.combine([&](const size_t& lhs, const size_t& rhs) {
      return std::max(lhs, rhs);
    });
  }

  ArcWeight Graph::computeNodeVolume(const NodeID u) {
    ASSERT(u < _num_nodes);
    ArcWeight x = 0.0;
    for (const Arc& arc : arcsOf(u)) {
      x += arc.weight;
    }
    _node_volumes[u] = x;
    return x;
  }

  bool Graph::canBeUsed(const bool verbose) const {
    const bool result = _indices.size() >= numNodes() + 1 && _arcs.size() >= numArcs() && _node_volumes.size() >= numNodes();
    if (verbose && !result) {
      LOG << "Some of the graph's members were stolen. For example the contract function does this. "
             "Make sure you're calling functions with a fresh graph or catch this condition and reinitialize."
             "If you do reinitialize, feel free to silence this warning by passing false to the canBeUsed function";
    }
    return result;
  }

  namespace {
    #define GRAPH(X) Graph::Graph(X& hypergraph, const LouvainEdgeWeight edge_weight_type, bool is_graph)
  }

  INSTANTIATE_FUNC_WITH_HYPERGRAPHS(GRAPH)

} // namespace mt_kahypar::ds
