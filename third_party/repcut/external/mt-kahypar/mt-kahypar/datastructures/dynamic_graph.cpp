/*******************************************************************************
 * MIT License
 *
 * This file is part of Mt-KaHyPar.
 *
 * Copyright (C) 2020 Lars Gottesbüren <lars.gottesbueren@kit.edu>
 * Copyright (C) 2020 Tobias Heuer <tobias.heuer@kit.edu>
 * Copyright (C) 2022 Nikolai Maas <nikolai.maas@student.kit.edu>
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

#include "mt-kahypar/datastructures/dynamic_graph.h"

#include <tbb/blocked_range.h>
#include <tbb/parallel_scan.h>
#include <tbb/parallel_sort.h>
#include <tbb/parallel_reduce.h>
#include <tbb/concurrent_queue.h>

#include "mt-kahypar/parallel/stl/scalable_queue.h"
#include "mt-kahypar/datastructures/concurrent_bucket_map.h"
#include "mt-kahypar/datastructures/hypergraph_utils.h"
#include "mt-kahypar/datastructures/streaming_vector.h"
#include "mt-kahypar/utils/timer.h"

namespace mt_kahypar {
namespace ds {

/**!
 * Registers a contraction in the hypergraph whereas vertex u is the representative
 * of the contraction and v its contraction partner. Several threads can call this function
 * in parallel. The function adds the contraction of u and v to a contraction tree that determines
 * a parallel execution order and synchronization points for all running contractions.
 * The contraction can be executed by calling function contract(v, max_node_weight).
 */
bool DynamicGraph::registerContraction(const HypernodeID u, const HypernodeID v) {
  return _contraction_tree.registerContraction(u, v, _version,
                                               [&](HypernodeID u) { acquireHypernode(u); },
                                               [&](HypernodeID u) { releaseHypernode(u); });
}

/**!
 * Contracts a previously registered contraction. Representative u of vertex v is looked up
 * in the contraction tree and performed if there are no pending contractions in the subtree
 * of v and the contractions respects the maximum allowed node weight. If (u,v) is the last
 * pending contraction in the subtree of u then the function recursively contracts also
 * u (if any contraction is registered). Therefore, function can return several contractions
 * or also return an empty contraction vector.
 */
size_t DynamicGraph::contract(const HypernodeID v,
                              const HypernodeWeight max_node_weight) {
  ASSERT(_contraction_tree.parent(v) != v, "No contraction registered for node " << v);

  HypernodeID x = _contraction_tree.parent(v);
  HypernodeID y = v;
  ContractionResult res = ContractionResult::CONTRACTED;
  size_t num_contractions = 0;
  // We perform all contractions registered in the contraction tree
  // as long as there are no pending contractions
  while ( x != y && res != ContractionResult::PENDING_CONTRACTIONS) {
    // Perform Contraction
    res = contract(x, y, max_node_weight);
    if ( res == ContractionResult::CONTRACTED ) {
      ++num_contractions;
    }
    y = x;
    x = _contraction_tree.parent(y);
  }
  return num_contractions;
}

/**!
 * Contracts a previously registered contraction. The contraction of u and v is
 * performed if there are no pending contractions in the subtree of v and the
 * contractions respects the maximum allowed node weight. In case the contraction
 * was performed successfully, enum type CONTRACTED is returned. If contraction
 * was not performed either WEIGHT_LIMIT_REACHED (in case sum of both vertices is
 * greater than the maximum allowed node weight) or PENDING_CONTRACTIONS (in case
 * there are some unfinished contractions in the subtree of v) is returned.
 */
DynamicGraph::ContractionResult DynamicGraph::contract(const HypernodeID u,
                                                       const HypernodeID v,
                                                       const HypernodeWeight max_node_weight) {

  // Acquire ownership in correct order to prevent deadlocks
  if ( u < v ) {
    acquireHypernode(u);
    acquireHypernode(v);
  } else {
    acquireHypernode(v);
    acquireHypernode(u);
  }

  // Contraction is valid if
  //  1.) Contraction partner v is enabled
  //  2.) There are no pending contractions on v
  //  3.) Resulting node weight is less or equal than a predefined upper bound
  //  4.) Fixed Vertex Contraction is valid
  const bool contraction_partner_valid =
    nodeIsEnabled(v) && _contraction_tree.pendingContractions(v) == 0;
  const bool less_or_equal_than_max_node_weight =
    hypernode(u).weight() + hypernode(v).weight() <= max_node_weight;
  const bool valid_contraction =
    contraction_partner_valid && less_or_equal_than_max_node_weight &&
    ( !hasFixedVertices() ||
      /** only run this if all previous checks were successful */ _fixed_vertices.contract(u, v) );
  if ( valid_contraction ) {
    ASSERT(nodeIsEnabled(u), "Hypernode" << u << "is disabled!");
    hypernode(u).setWeight(nodeWeight(u) + nodeWeight(v));
    hypernode(v).disable();
    releaseHypernode(u);
    releaseHypernode(v);

    HypernodeID contraction_start = _contraction_index.load();

    // Contract incident net lists of u and v
    _adjacency_array.contract(u, v, [&](const HypernodeID u) {
      acquireHypernode(u);
    }, [&](const HypernodeID u) {
      releaseHypernode(u);
    });

    HypernodeID contraction_end = ++_contraction_index;
    acquireHypernode(u);
    _contraction_tree.unregisterContraction(u, v, contraction_start, contraction_end);
    releaseHypernode(u);
    return ContractionResult::CONTRACTED;
  } else {
    ContractionResult res = ContractionResult::PENDING_CONTRACTIONS;
    const bool fixed_vertex_contraction_failed =
      contraction_partner_valid && less_or_equal_than_max_node_weight;
    if ( ( !less_or_equal_than_max_node_weight || fixed_vertex_contraction_failed ) &&
         nodeIsEnabled(v) && _contraction_tree.parent(v) == u ) {
      _contraction_tree.unregisterContraction(u, v,
        kInvalidHypernode, kInvalidHypernode, true /* failed */);
      res = fixed_vertex_contraction_failed ?
        ContractionResult::INVALID_FIXED_VERTEX_CONTRACTION :
        ContractionResult::WEIGHT_LIMIT_REACHED;
    }
    releaseHypernode(u);
    releaseHypernode(v);
    return res;
  }
}

 /**
   * Uncontracts a batch of contractions in parallel. The batches must be uncontracted exactly
   * in the order computed by the function createBatchUncontractionHierarchy(...).
   * The two uncontraction functions are required by the partitioned graph to update
   * gain cache values.
   */
void DynamicGraph::uncontract(const Batch& batch,
                              const MarkEdgeFunc& mark_edge,
                              const UncontractionFunction& case_one_func,
                              const UncontractionFunction& case_two_func) {
  ASSERT(batch.size() > UL(0));
  ASSERT([&] {
    const HypernodeID expected_batch_index = hypernode(batch[0].v).batchIndex();
    for ( const Memento& memento : batch ) {
      if ( hypernode(memento.v).batchIndex() != expected_batch_index ) {
        LOG << "Batch contains uncontraction from different batches."
            << "Hypernode" << memento.v << "with version" << hypernode(memento.v).batchIndex()
            << "but expected is" << expected_batch_index;
        return false;
      }
      if ( _contraction_tree.version(memento.v) != _version ) {
        LOG << "Batch contains uncontraction from a different version."
            << "Hypernode" << memento.v << "with version" << _contraction_tree.version(memento.v)
            << "but expected is" << _version;
        return false;
      }
    }
    return true;
  }(), "Batch contains uncontractions from different batches or from a different hypergraph version");

  tbb::parallel_for(UL(0), batch.size(), [&](const size_t i) {
    const Memento& memento = batch[i];
    ASSERT(!hypernode(memento.u).isDisabled(), "Hypernode" << memento.u << "is disabled");
    ASSERT(hypernode(memento.v).isDisabled(), "Hypernode" << memento.v << "is not invalid");

    // Restore incident net list of u and v
    _adjacency_array.uncontract(memento.u, memento.v, mark_edge,
      [&](const HyperedgeID e) {
        case_one_func(memento.u, memento.v, e);
      }, [&](const HyperedgeID e) {
        case_two_func(memento.u, memento.v, e);
      }, [&](const HypernodeID u) {
        acquireHypernode(u);
      }, [&](const HypernodeID u) {
        releaseHypernode(u);
      });

    acquireHypernode(memento.u);
    // Restore hypernode v which includes enabling it and subtract its weight
    // from its representative
    hypernode(memento.v).enable();
    hypernode(memento.u).setWeight(hypernode(memento.u).weight() - hypernode(memento.v).weight());
    releaseHypernode(memento.u);

    // Revert contraction in fixed vertex support
    if ( hasFixedVertices() ) {
      _fixed_vertices.uncontract(memento.u, memento.v);
    }
  });
}

/**
 * Computes a batch uncontraction hierarchy. A batch is a vector of mementos
 * (uncontractions) that are uncontracted in parallel. The function returns a vector
 * of versioned batch vectors. A new version of the hypergraph is induced if we perform
 * single-pin and parallel net detection. Once we process all batches of a versioned
 * batch vector, we have to restore all previously removed single-pin and parallel nets
 * in order to uncontract the next batch vector. We create for each version of the
 * hypergraph a seperate batch uncontraction hierarchy (see createBatchUncontractionHierarchyOfVersion(...))
 */
VersionedBatchVector DynamicGraph::createBatchUncontractionHierarchy(const size_t batch_size) {
  const size_t num_versions = _version + 1;
  // Finalizes the contraction tree such that it is traversable in a top-down fashion
  // and contains subtree size for each  tree node
  _contraction_tree.finalize(num_versions);

  VersionedBatchVector versioned_batches(num_versions);
  parallel::scalable_vector<size_t> batch_sizes_prefix_sum(num_versions, 0);
  BatchIndexAssigner batch_index_assigner(numNodes(), batch_size);
  for ( size_t version = 0; version < num_versions; ++version ) {
    versioned_batches[version] =
      _contraction_tree.createBatchUncontractionHierarchyForVersion(batch_index_assigner, version);
    if ( version > 0 ) {
      batch_sizes_prefix_sum[version] =
        batch_sizes_prefix_sum[version - 1] + versioned_batches[version - 1].size();
    }
    batch_index_assigner.reset(versioned_batches[version].size());
  }

  return versioned_batches;
}

/**
 * Removes single-pin and parallel nets from the hypergraph. The weight
 * of a set of identical nets is aggregated in one representative hyperedge
 * and single-pin hyperedges are removed. Returns a vector of removed hyperedges.
 */
parallel::scalable_vector<DynamicGraph::ParallelHyperedge> DynamicGraph::removeSinglePinAndParallelHyperedges() {
  ++_version;
  return _adjacency_array.removeSinglePinAndParallelEdges();
}

/**
 * Restores a previously removed set of singple-pin and parallel hyperedges. Note, that hes_to_restore
 * must be exactly the same and given in the reverse order as returned by removeSinglePinAndParallelNets(...).
 */
void DynamicGraph::restoreSinglePinAndParallelNets(const parallel::scalable_vector<ParallelHyperedge>& hes_to_restore) {
  _adjacency_array.restoreSinglePinAndParallelEdges(hes_to_restore);
  --_version;
}

// ! Copy dynamic hypergraph in parallel
DynamicGraph DynamicGraph::copy(parallel_tag_t) const {
  DynamicGraph hypergraph;

  hypergraph._num_removed_nodes = _num_removed_nodes;
  hypergraph._max_removed_degree_zero_hn_weight = _max_removed_degree_zero_hn_weight;
  hypergraph._num_edges = _num_edges;
  hypergraph._total_weight = _total_weight;
  hypergraph._version = _version;
  hypergraph._contraction_index.store(_contraction_index.load());

  tbb::parallel_invoke([&] {
    hypergraph._nodes.resize(_nodes.size());
    memcpy(hypergraph._nodes.data(), _nodes.data(),
      sizeof(Node) * _nodes.size());
  }, [&] {
    hypergraph._adjacency_array = _adjacency_array.copy(parallel_tag_t());
  }, [&] {
    hypergraph._acquired_nodes.resize(_acquired_nodes.size());
    tbb::parallel_for(ID(0), numNodes(), [&](const HypernodeID& hn) {
      hypergraph._acquired_nodes[hn] = _acquired_nodes[hn];
    });
  }, [&] {
    hypergraph._contraction_tree = _contraction_tree.copy(parallel_tag_t());
  }, [&] {
    hypergraph._fixed_vertices = _fixed_vertices.copy();
    hypergraph._fixed_vertices.setHypergraph(&hypergraph);
  });
  return hypergraph;
}

// ! Copy dynamic hypergraph sequential
DynamicGraph DynamicGraph::copy() const {
  DynamicGraph hypergraph;

  hypergraph._num_removed_nodes = _num_removed_nodes;
  hypergraph._max_removed_degree_zero_hn_weight = _max_removed_degree_zero_hn_weight;
  hypergraph._num_edges = _num_edges;
  hypergraph._total_weight = _total_weight;
  hypergraph._version = _version;
  hypergraph._contraction_index.store(_contraction_index.load());

  hypergraph._nodes.resize(_nodes.size());
  memcpy(hypergraph._nodes.data(), _nodes.data(),
    sizeof(Node) * _nodes.size());
    hypergraph._adjacency_array = _adjacency_array.copy();
  hypergraph._acquired_nodes.resize(numNodes());
  for ( HypernodeID hn = 0; hn < numNodes(); ++hn ) {
    hypergraph._acquired_nodes[hn] = _acquired_nodes[hn];
  }
  hypergraph._contraction_tree = _contraction_tree.copy();
  hypergraph._fixed_vertices = _fixed_vertices.copy();
  hypergraph._fixed_vertices.setHypergraph(&hypergraph);

  return hypergraph;
}

void DynamicGraph::memoryConsumption(utils::MemoryTreeNode* parent) const {
  ASSERT(parent);

  parent->addChild("Hypernodes", sizeof(Node) * _nodes.size());
  parent->addChild("Incident Nets", _adjacency_array.size_in_bytes());
  parent->addChild("Hypernode Ownership Vector", sizeof(bool) * _acquired_nodes.size());

  utils::MemoryTreeNode* contraction_tree_node = parent->addChild("Contraction Tree");
  _contraction_tree.memoryConsumption(contraction_tree_node);

  if ( hasFixedVertices() ) {
    parent->addChild("Fixed Vertex Support", _fixed_vertices.size_in_bytes());
  }
}

// ! Only for testing
bool DynamicGraph::verifyIncidenceArrayAndIncidentNets() {
  bool success = true;
  tbb::parallel_invoke([&] {
    doParallelForAllNodes([&](const HypernodeID& hn) {
      for ( const HyperedgeID& he : incidentEdges(hn) ) {
        if (edgeSource(he) != hn) {
          LOG << "Edge" << he << "has source" << edgeSource(he) << "but should be" << hn;
          success = false;
        }
        const HypernodeID back_target = edge(edge(he).back_edge).target;
        if (back_target != hn) {
          LOG << "Backedge" << edge(he).back_edge << "(of edge" << he
              << ") has target" << back_target << "but should be" << hn;
          success = false;
        }
      }
    });
  }, [&] {
    doParallelForAllEdges([&](const HyperedgeID& he) {
      bool found = false;
      for ( const HyperedgeID& e : incidentEdges(edgeSource(he)) ) {
        if ( e == he ) {
          found = true;
          break;
        }
      }
      if ( !found ) {
        LOG << "Edge" << he << "not found in incident nets of vertex" << edgeSource(he);
        success = false;
      }
    });
  });
  return success;
}

// ! Computes the total weight of the hypergraph (parallel)
void DynamicGraph::computeAndSetTotalNodeWeight(parallel_tag_t) {
  _total_weight = computeTotalNodeWeightParallel(*this, numNodes());
}

} // namespace ds
} // namespace mt_kahypar