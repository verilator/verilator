/*******************************************************************************
 * MIT License
 *
 * This file is part of Mt-KaHyPar.
 *
 * Copyright (C) 2019 Lars Gottesbüren <lars.gottesbueren@kit.edu>
 * Copyright (C) 2019 Tobias Heuer <tobias.heuer@kit.edu>
 * Copyright (C) 2021 Nikolai Maas <nikolai.maas@student.kit.edu>
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

#include "static_graph.h"

#include "mt-kahypar/parallel/chunking.h"
#include "mt-kahypar/parallel/parallel_prefix_sum.h"
#include "mt-kahypar/datastructures/concurrent_bucket_map.h"
#include "mt-kahypar/datastructures/hypergraph_utils.h"
#include "mt-kahypar/utils/timer.h"
#include "mt-kahypar/utils/memory_tree.h"

#include <algorithm>

#include <tbb/parallel_reduce.h>
#include <tbb/parallel_sort.h>


namespace mt_kahypar::ds {
  /*!
   * Contracts a given community structure. All vertices with the same label
   * are collapsed into the same vertex. The resulting single-pin and parallel
   * hyperedges are removed from the contracted graph. The function returns
   * the contracted hypergraph and a mapping which specifies a mapping from
   * community label (given in 'communities') to a vertex in the coarse hypergraph.
   *
   * \param communities Community structure that should be contracted
   */
  StaticGraph StaticGraph::contract(parallel::scalable_vector<HypernodeID>& communities, bool /*deterministic*/) {
    ASSERT(communities.size() == _num_nodes);

    if ( !_tmp_contraction_buffer ) {
      allocateTmpContractionBuffer();
    }

    // AUXILIARY BUFFERS - Reused during multilevel hierarchy to prevent expensive allocations
    Array<HypernodeID>& mapping = _tmp_contraction_buffer->mapping;
    Array<Node>& tmp_nodes = _tmp_contraction_buffer->tmp_nodes;
    Array<HyperedgeID>& node_sizes = _tmp_contraction_buffer->node_sizes;
    Array<parallel::IntegralAtomicWrapper<HyperedgeID>>& tmp_num_incident_edges =
            _tmp_contraction_buffer->tmp_num_incident_edges;
    Array<parallel::IntegralAtomicWrapper<HypernodeWeight>>& node_weights =
            _tmp_contraction_buffer->node_weights;
    Array<TmpEdgeInformation>& tmp_edges = _tmp_contraction_buffer->tmp_edges;
    Array<HyperedgeID>& edge_id_mapping = _tmp_contraction_buffer->edge_id_mapping;

    ASSERT(static_cast<size_t>(_num_nodes) <= mapping.size());
    ASSERT(static_cast<size_t>(_num_nodes) <= tmp_nodes.size());
    ASSERT(static_cast<size_t>(_num_nodes) <= node_sizes.size());
    ASSERT(static_cast<size_t>(_num_nodes) <= tmp_num_incident_edges.size());
    ASSERT(static_cast<size_t>(_num_nodes) <= node_weights.size());
    ASSERT(static_cast<size_t>(_num_edges) <= tmp_edges.size());
    ASSERT(static_cast<size_t>(_num_edges / 2) <= edge_id_mapping.size());


    // #################### STAGE 1 ####################
    // Compute vertex ids of coarse graph with a parallel prefix sum
    mapping.assign(_num_nodes, 0);

    doParallelForAllNodes([&](const HypernodeID& node) {
      ASSERT(static_cast<size_t>(communities[node]) < mapping.size());
      mapping[communities[node]] = UL(1);
    });

    // Prefix sum determines vertex ids in coarse graph
    parallel::TBBPrefixSum<HyperedgeID, Array> mapping_prefix_sum(mapping);
    tbb::parallel_scan(tbb::blocked_range<size_t>(ID(0), _num_nodes), mapping_prefix_sum);
    HypernodeID coarsened_num_nodes = mapping_prefix_sum.total_sum();

    // Remap community ids
    tbb::parallel_for(ID(0), _num_nodes, [&](const HypernodeID& node) {
      if ( nodeIsEnabled(node) ) {
        communities[node] = mapping_prefix_sum[communities[node]];
      } else {
        communities[node] = kInvalidHypernode;
      }

      // Reset tmp contraction buffer
      if ( node < coarsened_num_nodes ) {
        node_weights[node] = 0;
        tmp_nodes[node] = Node(true);
        node_sizes[node] = 0;
        tmp_num_incident_edges[node] = 0;
      }
    });

    // Mapping from a vertex id of the current hypergraph to its
    // id in the coarse hypergraph
    auto map_to_coarse_graph = [&](const HypernodeID node) {
      ASSERT(node < communities.size());
      return communities[node];
    };


    doParallelForAllNodes([&](const HypernodeID& node) {
      const HypernodeID coarse_node = map_to_coarse_graph(node);
      ASSERT(coarse_node < coarsened_num_nodes, V(coarse_node) << V(coarsened_num_nodes));
      // Weight vector is atomic => thread-safe
      node_weights[coarse_node] += nodeWeight(node);
      // Aggregate upper bound for number of incident nets of the contracted vertex
      tmp_num_incident_edges[coarse_node] += nodeDegree(node);
    });

    // #################### STAGE 2 ####################
    // In this step the incident edges of vertices are processed and stored inside the temporary
    // buffer. The vertex ids of the targets are remapped and edges that are contained inside
    // one community after contraction are marked as invalid. Note that parallel edges are not
    // invalidated yet.

    // Compute start position the incident nets of a coarse vertex in the
    // temporary incident nets array with a parallel prefix sum
    parallel::scalable_vector<parallel::IntegralAtomicWrapper<HyperedgeID>> tmp_incident_edges_pos;
    parallel::TBBPrefixSum<parallel::IntegralAtomicWrapper<HyperedgeID>, Array>
            tmp_incident_edges_prefix_sum(tmp_num_incident_edges);
    tbb::parallel_invoke([&] {
      tbb::parallel_scan(tbb::blocked_range<size_t>(
              ID(0), static_cast<size_t>(coarsened_num_nodes)), tmp_incident_edges_prefix_sum);
    }, [&] {
      tmp_incident_edges_pos.assign(coarsened_num_nodes, parallel::IntegralAtomicWrapper<HyperedgeID>(0));
    });

    // Write the incident edges of each contracted vertex to the temporary edge array
    doParallelForAllNodes([&](const HypernodeID& node) {
      const HypernodeID coarse_node = map_to_coarse_graph(node);
      const HyperedgeID node_degree = nodeDegree(node);
      const size_t coarse_edges_pos = tmp_incident_edges_prefix_sum[coarse_node] +
                                      tmp_incident_edges_pos[coarse_node].fetch_add(node_degree);
      const size_t edges_pos = _nodes[node].firstEntry();
      ASSERT(coarse_edges_pos + node_degree <= tmp_incident_edges_prefix_sum[coarse_node + 1]);
      ASSERT(edges_pos + node_degree <= _edges.size());
      for (size_t i = 0; i < static_cast<size_t>(node_degree); ++i) {
        const Edge& edge = _edges[edges_pos + i];
        const HyperedgeID unique_id = _unique_edge_ids[edges_pos + i];
        const HypernodeID target = map_to_coarse_graph(edge.target());
        const bool is_valid = target != coarse_node;
        if (is_valid) {
          tmp_edges[coarse_edges_pos + i] = TmpEdgeInformation(target, edge.weight(), unique_id);
        } else {
          tmp_edges[coarse_edges_pos + i] = TmpEdgeInformation();
        }
      }
    });


    // #################### STAGE 3 ####################
    // In this step, we deduplicate parallel edges. To this end, the incident edges
    // of each vertex are sorted and aggregated. However, there is a special treatment
    // for vertices with extremely high degree, as they might become a bottleneck
    // otherwise. Afterwards, for all parallel edges all but one are invalidated and
    // the weight of the remaining edge is set to the sum of the weights.

    // A list of high degree vertices that are processed afterwards
    parallel::scalable_vector<HypernodeID> high_degree_vertices;
    tbb::parallel_for(ID(0), coarsened_num_nodes, [&](const HypernodeID& coarse_node) {
      const size_t incident_edges_start = tmp_incident_edges_prefix_sum[coarse_node];
      const size_t incident_edges_end = tmp_incident_edges_prefix_sum[coarse_node + 1];
      const size_t tmp_degree = incident_edges_end - incident_edges_start;
      if (tmp_degree <= HIGH_DEGREE_CONTRACTION_THRESHOLD) {
        // if the degree is small enough, we directly deduplicate the edges
        node_sizes[coarse_node] = deduplicateTmpEdges(tmp_edges.data() + incident_edges_start,
                                                      tmp_edges.data() + incident_edges_end);
      } else {
        high_degree_vertices.push_back(coarse_node);
      }
      tmp_nodes[coarse_node].setWeight(node_weights[coarse_node]);
      tmp_nodes[coarse_node].setFirstEntry(incident_edges_start);
    });

    if ( !high_degree_vertices.empty() ) {
      // High degree vertices are treated special, because sorting and afterwards
      // removing duplicates can become a major sequential bottleneck
      ConcurrentBucketMap<TmpEdgeInformation> incident_edges_map;
      size_t max_degree = 0;
      for ( const HypernodeID& coarse_node : high_degree_vertices ) {
        const size_t incident_edges_start = tmp_incident_edges_prefix_sum[coarse_node];
        const size_t incident_edges_end = tmp_incident_edges_prefix_sum[coarse_node + 1];
        max_degree = std::max(max_degree, incident_edges_end - incident_edges_start);
      }
      incident_edges_map.reserve_for_estimated_number_of_insertions(max_degree);

      parallel::scalable_vector<std::pair<size_t, size_t>> resulting_ranges;
      for ( const HypernodeID& coarse_node : high_degree_vertices ) {
        const size_t incident_edges_start = tmp_incident_edges_prefix_sum[coarse_node];
        const size_t incident_edges_end = tmp_incident_edges_prefix_sum[coarse_node + 1];
        const size_t size_of_range = incident_edges_end - incident_edges_start;

        // Insert incident edges into concurrent bucket map
        const size_t num_chunks = tbb::this_task_arena::max_concurrency();
        const size_t chunk_size = parallel::chunking::idiv_ceil(size_of_range, num_chunks);
        tbb::parallel_for(UL(0), num_chunks, [&](const size_t chunk_id) {
          auto [start_offset, end_offset] = parallel::chunking::bounds(chunk_id, size_of_range, chunk_size);
          const size_t start = incident_edges_start + start_offset;
          const size_t end = incident_edges_start + end_offset;
          // First, we apply a deduplication step to the thread-local range. The reason is that on large irregular
          // graphs, extremely large clusters (thousands of nodes) can be created during coarsening. In this case,
          // there can be thousands of edges with the same target, which creates a massive imbalance and thus high
          // contention in the bucket map if we insert them directly. The local deduplication avoids this problem
          // by ensuring that each edge appears at most t times.
          const HyperedgeID local_degree = deduplicateTmpEdges(tmp_edges.data() + start, tmp_edges.data() + end);
          for (size_t pos = start; pos < start + local_degree; ++pos) {
            const TmpEdgeInformation& edge = tmp_edges[pos];
            ASSERT(edge.isValid());
            incident_edges_map.insert(edge.getTarget(), TmpEdgeInformation(edge));
          }
        }, tbb::static_partitioner());

        // Process each bucket in parallel and deduplicate the edges
        std::atomic<size_t> incident_edges_pos(incident_edges_start);
        tbb::parallel_for(UL(0), incident_edges_map.numBuckets(), [&](const size_t bucket) {
          auto& incident_edges_bucket = incident_edges_map.getBucket(bucket);
          const HyperedgeID bucket_degree = deduplicateTmpEdges(incident_edges_bucket.data(),
                                              incident_edges_bucket.data() + incident_edges_bucket.size());
          const size_t tmp_incident_edges_pos = incident_edges_pos.fetch_add(bucket_degree);
          memcpy(tmp_edges.data() + tmp_incident_edges_pos,
                 incident_edges_bucket.data(), sizeof(TmpEdgeInformation) * bucket_degree);
          incident_edges_map.clear(bucket);
        });

        const size_t contracted_size = incident_edges_pos.load() - incident_edges_start;
        node_sizes[coarse_node] = contracted_size;
        resulting_ranges.emplace_back(incident_edges_start, incident_edges_pos.load());
      }

      // We still sort the adjacent edges since this results in better cache locality when accessing the neighbors.
      // Also, sorting is necessary for deterministic partitioning.
      tbb::parallel_for(UL(0), resulting_ranges.size(), [&](const size_t i) {
        auto [start, end] = resulting_ranges[i];
        auto comparator = [](const TmpEdgeInformation& e1, const TmpEdgeInformation& e2) {
          return e1._target < e2._target;
        };
        if (end - start > HIGH_DEGREE_CONTRACTION_THRESHOLD
            || resulting_ranges.size() < 2 * static_cast<size_t>(tbb::this_task_arena::max_concurrency())) {
          tbb::parallel_sort(tmp_edges.begin() + start, tmp_edges.begin() + end, comparator);
        } else {
          std::sort(tmp_edges.begin() + start, tmp_edges.begin() + end, comparator);
        }
      });
    }

    // #################### STAGE 4 ####################
    // Coarsened graph is constructed here by writting data from temporary
    // buffers to corresponding members in coarsened graph. We compute
    // a prefix sum over the vertex sizes to determine the start index
    // of the edges in the edge array, removing all invalid edges.
    // Additionally, we need to calculate new unique edge ids.

    StaticGraph hypergraph;

    // Compute number of edges in coarse graph (those flagged as valid)
    parallel::TBBPrefixSum<HyperedgeID, Array> degree_mapping(node_sizes);
    tbb::parallel_scan(tbb::blocked_range<size_t>(
            ID(0), static_cast<size_t>(coarsened_num_nodes)), degree_mapping);
    const HyperedgeID coarsened_num_edges = degree_mapping.total_sum();
    hypergraph._num_nodes = coarsened_num_nodes;
    hypergraph._num_edges = coarsened_num_edges;

    HEAVY_COARSENING_ASSERT(
      [&]{
        HyperedgeID last_end = 0;
        for (size_t i = 0; i < coarsened_num_nodes; ++i) {
          const HyperedgeID tmp_edges_start = tmp_nodes[i].firstEntry();
          if (last_end > tmp_edges_start) {
            return false;
          }
          last_end = tmp_edges_start + degree_mapping.value(i);
        }
        return true;
      }()
    );

    tbb::parallel_invoke([&] {
      // Copy edges
      edge_id_mapping.assign(_num_edges / 2, 0);
      hypergraph._edges.resizeNoAssign(coarsened_num_edges);
      hypergraph._unique_edge_ids.resizeNoAssign(coarsened_num_edges);
      tbb::parallel_for(ID(0), coarsened_num_nodes, [&](const HyperedgeID& coarse_node) {
        const HyperedgeID tmp_edges_start = tmp_nodes[coarse_node].firstEntry();
        const HyperedgeID edges_start = degree_mapping[coarse_node];
        auto handle_edge = [&](const HyperedgeID& index) {
          ASSERT(tmp_edges_start + index < tmp_edges.size() && edges_start + index < hypergraph._edges.size());
          const TmpEdgeInformation& tmp_edge = tmp_edges[tmp_edges_start + index];
          Edge& edge = hypergraph.edge(edges_start + index);
          edge.setTarget(tmp_edge.getTarget());
          edge.setSource(coarse_node);
          edge.setWeight(tmp_edge.getWeight());
          hypergraph._unique_edge_ids[edges_start + index] = tmp_edge.getID();
          ASSERT(static_cast<size_t>(tmp_edge.getID()) < edge_id_mapping.size());
          edge_id_mapping[tmp_edge.getID()] = UL(1);
        };

        if (degree_mapping.value(coarse_node) > HIGH_DEGREE_CONTRACTION_THRESHOLD / 8) {
          tbb::parallel_for(ID(0), degree_mapping.value(coarse_node), handle_edge);
        } else {
          for (size_t index = 0; index < degree_mapping.value(coarse_node); ++index) {
            handle_edge(index);
          }
        }
      });
    }, [&] {
      hypergraph._nodes.resize(coarsened_num_nodes + 1);
      tbb::parallel_for(ID(0), coarsened_num_nodes, [&](const HyperedgeID& coarse_node) {
        Node& node = hypergraph.node(coarse_node);
        node.enable();
        node.setFirstEntry(degree_mapping[coarse_node]);
        node.setWeight(tmp_nodes[coarse_node].weight());
      });
      hypergraph._nodes.back() = Node(static_cast<size_t>(coarsened_num_edges));
    }, [&] {
      hypergraph._community_ids.resize(coarsened_num_nodes);
      doParallelForAllNodes([&](HypernodeID fine_node) {
        hypergraph.setCommunityID(map_to_coarse_graph(fine_node), communityID(fine_node));
      });
    });

    // Remap unique edge ids via prefix sum
    parallel::TBBPrefixSum<HyperedgeID, Array> edge_id_prefix_sum(edge_id_mapping);
    tbb::parallel_scan(tbb::blocked_range<size_t>(ID(0), _num_edges / 2), edge_id_prefix_sum);
    ASSERT(edge_id_prefix_sum.total_sum() == coarsened_num_edges / 2);

    tbb::parallel_for(ID(0), coarsened_num_edges, [&](const HyperedgeID& e) {
      HyperedgeID& unique_id = hypergraph._unique_edge_ids[e];
      unique_id = edge_id_prefix_sum[unique_id];
    });

    if ( hasFixedVertices() ) {
      // Map fixed vertices to coarse graph
      FixedVertexSupport<StaticGraph> coarse_fixed_vertices(
        hypergraph.initialNumNodes(), _fixed_vertices.numBlocks());
      coarse_fixed_vertices.setHypergraph(&hypergraph);
      doParallelForAllNodes([&](const HypernodeID hn) {
        if ( isFixed(hn) ) {
          coarse_fixed_vertices.fixToBlock(communities[hn], fixedVertexBlock(hn));
        }
      });
      hypergraph.addFixedVertexSupport(std::move(coarse_fixed_vertices));
    }

    HEAVY_COARSENING_ASSERT(
      [&](){
        parallel::scalable_vector<bool> covered_ids(hypergraph.initialNumEdges() / 2, false);
        for (HyperedgeID e : hypergraph.edges()) {
          HyperedgeID id = hypergraph.uniqueEdgeID(e);
          covered_ids.at(id) = true;
          bool success = false;
          for (HyperedgeID b_edge : hypergraph.incidentEdges(hypergraph.edgeTarget(e))) {
            if (hypergraph.edgeTarget(b_edge) == hypergraph.edgeSource(e)) {
              if (hypergraph.uniqueEdgeID(b_edge) != id) {
                return false;
              }
              success = true;
              break;
            }
          }
          if (!success) {
            return false;
          }
        }
        for (bool val : covered_ids) {
          if (!val) {
            return false;
          }
        }
        return true;
      }(),
      "Unique edge IDs are not initialized correctly."
    );

    hypergraph._total_weight = _total_weight;
    hypergraph._tmp_contraction_buffer = _tmp_contraction_buffer;
    _tmp_contraction_buffer = nullptr;
    return hypergraph;
  }


  size_t StaticGraph::deduplicateTmpEdges(TmpEdgeInformation* edge_start, TmpEdgeInformation* edge_end) {
    ASSERT(std::distance(edge_start, edge_end) >= 0);
    std::sort(edge_start, edge_end,
              [](const TmpEdgeInformation& e1, const TmpEdgeInformation& e2) {
                return e1._target < e2._target;
              });

    // Deduplicate, aggregate weights and calculate minimum unique id
    //
    // <-- deduplicated --> <-- already processed --> <-- to be processed --> <-- invalid edges -->
    //                    ^                         ^
    // valid_edge_index ---        tmp_edge_index ---
    size_t valid_edge_index = 0;
    size_t tmp_edge_index = 1;
    while (tmp_edge_index < static_cast<size_t>(std::distance(edge_start, edge_end)) && edge_start[tmp_edge_index].isValid()) {
      HEAVY_COARSENING_ASSERT(
        [&](){
          size_t i = 0;
          for (; i <= valid_edge_index; ++i) {
            if (!edge_start[i].isValid()) {
              return false;
            } else if ((i + 1 <= valid_edge_index) &&
              edge_start[i].getTarget() >= edge_start[i + 1].getTarget()) {
              return false;
            }
          }
          return true;
        }(),
        "Invariant violated while deduplicating incident edges!"
      );

      TmpEdgeInformation& valid_edge = edge_start[valid_edge_index];
      TmpEdgeInformation& next_edge = edge_start[tmp_edge_index];
      if (valid_edge.getTarget() == next_edge.getTarget()) {
        valid_edge.addWeight(next_edge.getWeight());
        valid_edge.updateID(next_edge.getID());
        next_edge.invalidate();
      } else {
        edge_start[++valid_edge_index] = next_edge;
      }
      ++tmp_edge_index;
    }
    const bool is_non_empty = (std::distance(edge_start, edge_end) > 0) && edge_start[0].isValid();
    return is_non_empty ? (valid_edge_index + 1) : 0;
  }

  // ! Copy static hypergraph in parallel
  StaticGraph StaticGraph::copy(parallel_tag_t) const {
    StaticGraph hypergraph;

    hypergraph._num_nodes = _num_nodes;
    hypergraph._num_removed_nodes = _num_removed_nodes;
    hypergraph._max_removed_degree_zero_hn_weight = _max_removed_degree_zero_hn_weight;
    hypergraph._num_edges = _num_edges;
    hypergraph._total_weight = _total_weight;

    tbb::parallel_invoke([&] {
      hypergraph._nodes.resize(_nodes.size());
      memcpy(hypergraph._nodes.data(), _nodes.data(),
             sizeof(Node) * _nodes.size());
    }, [&] {
      hypergraph._edges.resize(_edges.size());
      memcpy(hypergraph._edges.data(), _edges.data(),
             sizeof(Edge) * _edges.size());
    }, [&] {
      hypergraph._unique_edge_ids.resize(_unique_edge_ids.size());
      memcpy(hypergraph._unique_edge_ids.data(), _unique_edge_ids.data(),
             sizeof(HyperedgeID) * _unique_edge_ids.size());
    }, [&] {
      hypergraph._community_ids = _community_ids;
    }, [&] {
      hypergraph.addFixedVertexSupport(_fixed_vertices.copy());
    });
    return hypergraph;
  }

  // ! Copy static hypergraph sequential
  StaticGraph StaticGraph::copy() const {
    StaticGraph hypergraph;

    hypergraph._num_nodes = _num_nodes;
    hypergraph._num_removed_nodes = _num_removed_nodes;
    hypergraph._max_removed_degree_zero_hn_weight = _max_removed_degree_zero_hn_weight;
    hypergraph._num_edges = _num_edges;
    hypergraph._total_weight = _total_weight;

    hypergraph._nodes.resize(_nodes.size());
    memcpy(hypergraph._nodes.data(), _nodes.data(),
           sizeof(Node) * _nodes.size());

    hypergraph._edges.resize(_edges.size());
    memcpy(hypergraph._edges.data(), _edges.data(),
           sizeof(Edge) * _edges.size());

    hypergraph._unique_edge_ids.resize(_unique_edge_ids.size());
    memcpy(hypergraph._unique_edge_ids.data(), _unique_edge_ids.data(),
           sizeof(HyperedgeID) * _unique_edge_ids.size());

    hypergraph._community_ids = _community_ids;
    hypergraph.addFixedVertexSupport(_fixed_vertices.copy());

    return hypergraph;
  }

  void StaticGraph::memoryConsumption(utils::MemoryTreeNode* parent) const {
    ASSERT(parent);
    parent->addChild("Hypernodes", sizeof(Node) * _nodes.size());
    parent->addChild("Hyperedges", 2 * sizeof(Edge) * _edges.size());
    parent->addChild("Communities", sizeof(PartitionID) * _community_ids.capacity());
    if ( hasFixedVertices() ) {
      parent->addChild("Fixed Vertex Support", _fixed_vertices.size_in_bytes());
    }
  }

  // ! Computes the total node weight of the hypergraph
  void StaticGraph::computeAndSetTotalNodeWeight(parallel_tag_t) {
    _total_weight = computeTotalNodeWeightParallel(*this, _num_nodes);
  }

} // namespace
