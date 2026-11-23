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

#pragma once

#include <cmath>

#include "mt-kahypar/datastructures/array.h"
#include "mt-kahypar/datastructures/hypergraph_common.h"
#include "mt-kahypar/parallel/atomic_wrapper.h"
#include "mt-kahypar/partition/context_enum_classes.h"
#include "mt-kahypar/utils/range.h"


namespace mt_kahypar {
namespace ds {

/*!
 * CSR Graph Data Structure
 */
class Graph {

  static constexpr bool debug = false;
  static constexpr bool enable_heavy_assert = false;

  struct TmpGraphBuffer {
    explicit TmpGraphBuffer(const size_t num_nodes,
                            const size_t num_arcs) :
      tmp_indices("Preprocessing", "tmp_indices", num_nodes + 1),
      tmp_pos("Preprocessing", "tmp_pos", num_nodes),
      tmp_node_volumes("Preprocessing", "tmp_node_volumes", num_nodes),
      tmp_arcs("Preprocessing", "tmp_arcs", num_arcs),
      valid_arcs("Preprocessing", "valid_arcs", num_arcs) { }

    ds::Array<parallel::IntegralAtomicWrapper<size_t>> tmp_indices;
    ds::Array<parallel::IntegralAtomicWrapper<size_t>> tmp_pos;
    ds::Array<parallel::AtomicWrapper<ArcWeight>> tmp_node_volumes;
    ds::Array<Arc> tmp_arcs;
    ds::Array<size_t> valid_arcs;
  };

 public:
  using AdjacenceIterator = typename ds::Array<Arc>::const_iterator;

 public:
  template<typename Hypergraph>
  Graph(Hypergraph& hypergraph, const LouvainEdgeWeight edge_weight_type, bool is_graph = false);

  Graph(Graph&& other);
  Graph& operator= (Graph&& other);
  ~Graph();

  // ! Number of nodes in the graph
  size_t numNodes() const {
    return _num_nodes;
  }

  // ! Number of arcs in the graph
  size_t numArcs() const {
    return _num_arcs;
  }

  // ! Iterator over all nodes of the graph
  IntegerRange<NodeID> nodes() const {
    return integer_range<NodeID>(numNodes());
  }

  // ! Iterator over all adjacent vertices of u
  // ! If 'n' is set, then only an iterator over the first n elements is returned
  IteratorRange<AdjacenceIterator> arcsOf(const NodeID u,
                                          const size_t n = std::numeric_limits<size_t>::max()) const {
    ASSERT(u < _num_nodes);
    const size_t start = _indices[u];
    size_t end = _indices[u + 1];
    if ( n < ( end - start ) ) {
      end = start + n;
    }
    return IteratorRange<AdjacenceIterator>(
      _arcs.cbegin() + start, _arcs.cbegin() + end);
  }

  // ! Degree of vertex u
  size_t degree(const NodeID u) const {
    ASSERT(u < _num_nodes);
    return _indices[u + 1] - _indices[u];
  }

  // ! Maximum degree of a vertex
  size_t max_degree() const {
    return _max_degree;
  }

  // ! Total Volume of the graph
  ArcWeight totalVolume() const {
    return _total_volume;
  }

  // ! Node volume of vertex u
  ArcWeight nodeVolume(const NodeID u) const {
    ASSERT(u < _num_nodes);
    return _node_volumes[u];
  }

  // ! Projects the clustering of the (likely bipartite star-expansion) graph to the hypergraph
  template<typename Hypergraph>
  void restrictClusteringToHypernodes(const Hypergraph& hg, ds::Clustering& C) const {
    C.resize(hg.initialNumNodes());
  }

  bool canBeUsed(const bool verbose = true) const;

  /*!
   * Contracts the graph based on the community structure passed as argument.
   * In the first step the community ids are compactified (via parallel prefix sum)
   * which also determines the node ids in the coarse graph. Afterwards, we create
   * a temporary graph which contains all arcs that will not form a selfloop in the
   * coarse graph. Finally, the weights of each multiedge in that temporary graph
   * are aggregated and the result is written to the final contracted graph.
   */
  Graph contract(Clustering& communities, bool low_memory);

  Graph contract_low_memory(Clustering& communities);

  void allocateContractionBuffers() {
    _tmp_graph_buffer = new TmpGraphBuffer(_num_nodes, _num_arcs);
  }

 private:
  Graph();

  /*!
   * Constructs a graph from a given hypergraph.
   */
  template<typename Hypergraph, typename F>
  void construct(const Hypergraph& hypergraph, const bool is_graph, const F& edge_weight_func);

  template<typename Hypergraph, typename F>
  void constructBipartiteGraph(const Hypergraph& hypergraph, F& edge_weight_func);

  template<typename Hypergraph, typename F>
  void constructGraph(const Hypergraph& hypergraph,
                      const F& edge_weight_func);

  ArcWeight computeNodeVolume(const NodeID u);

  // ! Number of nodes
  size_t _num_nodes;
  // ! Number of arcs
  size_t _num_arcs;
  // ! Total volume of the graph (= sum of arc weights)
  ArcWeight _total_volume;
  // ! Maximum degree of a node
  size_t _max_degree;

  // ! Index Vector
  ds::Array<size_t> _indices;
  // ! Arcs
  ds::Array<Arc> _arcs;
  // ! Node Volumes (= sum of arc weights for each node)
  ds::Array<ArcWeight> _node_volumes;
  // ! Data that is reused throughout the louvain method
  // ! to construct and contract a graph and to prevent expensive allocations
  TmpGraphBuffer* _tmp_graph_buffer;
};

}  // namespace ds

// expose
using Graph = ds::Graph;

}  // namespace mt_kahypar
