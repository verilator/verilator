/*******************************************************************************
 * MIT License
 *
 * This file is part of Mt-KaHyPar.
 *
 * Copyright (C) 2020 Lars Gottesbüren <lars.gottesbueren@kit.edu>
 * Copyright (C) 2020 Tobias Heuer <tobias.heuer@kit.edu>
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

#include "mt-kahypar/datastructures/dynamic_hypergraph_factory.h"

#include <tbb/parallel_for.h>
#include <tbb/parallel_invoke.h>
#include <tbb/parallel_scan.h>

#include "kahypar-resources/utils/math.h"

#include "mt-kahypar/parallel/parallel_prefix_sum.h"
#include "mt-kahypar/utils/timer.h"

namespace mt_kahypar {
namespace ds {

DynamicHypergraph DynamicHypergraphFactory::construct(
        const HypernodeID num_hypernodes,
        const HyperedgeID num_hyperedges,
        const HyperedgeVector& edge_vector,
        const HyperedgeWeight* hyperedge_weight,
        const HypernodeWeight* hypernode_weight,
        const bool) {
  if (edge_vector.size() != num_hyperedges) {
    throw InvalidInputException("Number of hyperedges does not match length of input data!");
  }

  DynamicHypergraph hypergraph;
  hypergraph._num_hypernodes = num_hypernodes;
  hypergraph._num_hyperedges = num_hyperedges;
  tbb::parallel_invoke([&] {
    hypergraph._hypernodes.resize(num_hypernodes);
  }, [&] {
    hypergraph._hyperedges.resize(num_hyperedges + 1);
  }, [&] {
    hypergraph._removable_single_pin_and_parallel_nets =
      kahypar::ds::FastResetFlagArray<>(num_hyperedges);
  }, [&] {
    hypergraph._hes_to_resize_flag_array =
      ThreadSafeFastResetFlagArray<>(num_hyperedges);
  });
  hypergraph._he_bitset = ThreadLocalBitset(num_hyperedges);

  // Compute number of pins per hyperedge
  Counter num_pins_per_hyperedge(num_hyperedges, 0);
  tbb::enumerable_thread_specific<size_t> local_max_edge_size(UL(0));
  tbb::parallel_for(ID(0), num_hyperedges, [&](const size_t pos) {
    if (edge_vector[pos].size() == 0) {
      throw InvalidInputException("Hyperedge " + STR(pos) + " is empty (hyperedges must contain at least 1 pin)");
    }

    num_pins_per_hyperedge[pos] = edge_vector[pos].size();
    local_max_edge_size.local() = std::max(
      local_max_edge_size.local(), edge_vector[pos].size());
  });
  hypergraph._max_edge_size = local_max_edge_size.combine(
    [&](const size_t lhs, const size_t rhs) {
      return std::max(lhs, rhs);
    });

  // Compute prefix sum over the number of pins per hyperedge and the.
  // The prefix sum is used than as
  // start position for each hyperedge in the incidence array.
  parallel::TBBPrefixSum<size_t> pin_prefix_sum(num_pins_per_hyperedge);
  tbb::parallel_scan(tbb::blocked_range<size_t>(
    UL(0), UI64(num_hyperedges)), pin_prefix_sum);

  hypergraph._num_pins = pin_prefix_sum.total_sum();
  hypergraph._total_degree = pin_prefix_sum.total_sum();
  hypergraph._incidence_array.resize(hypergraph._num_pins);

  tbb::parallel_invoke([&] {
    hypergraph._acquired_hes.assign(
      num_hyperedges, parallel::IntegralAtomicWrapper<bool>(false));
    tbb::parallel_for(ID(0), num_hyperedges, [&](const size_t pos) {
      // Setup hyperedges
      DynamicHypergraph::Hyperedge& hyperedge = hypergraph._hyperedges[pos];
      hyperedge.enable();
      hyperedge.setFirstEntry(pin_prefix_sum[pos]);
      hyperedge.setSize(pin_prefix_sum.value(pos));
      if ( hyperedge_weight ) {
        hyperedge.setWeight(hyperedge_weight[pos]);
      }

      size_t incidence_array_pos = hyperedge.firstEntry();
      size_t hash = kEdgeHashSeed;
      for ( const HypernodeID& pin : edge_vector[pos] ) {
        ASSERT(incidence_array_pos < hyperedge.firstInvalidEntry());
        if (pin >= num_hypernodes) {
          throw InvalidInputException("Hyperedge " + STR(pos) + " contains invalid pin: " + STR(pin));
        }
        // Compute hash of hyperedge
        hash += kahypar::math::hash(pin);
        // Add pin to incidence array
        hypergraph._incidence_array[incidence_array_pos++] = pin;
      }
      hyperedge.hash() = hash;
    });
    // Sentinel
    hypergraph._hyperedges[num_hyperedges].enable();
    hypergraph._hyperedges[num_hyperedges].setFirstEntry(hypergraph._num_pins);
  }, [&] {
    tbb::parallel_invoke([&] {
      hypergraph._acquired_hns.assign(
        num_hypernodes, parallel::IntegralAtomicWrapper<bool>(false));
    }, [&] {
      hypergraph._contraction_tree.initialize(num_hypernodes);
    });
    tbb::parallel_for(ID(0), num_hypernodes, [&](const HypernodeID hn) {
      // Setup hypernodes
      DynamicHypergraph::Hypernode& hypernode = hypergraph._hypernodes[hn];
      hypernode.enable();
      if ( hypernode_weight ) {
        hypernode.setWeight(hypernode_weight[hn]);
      }
    });
    // Compute total weight of hypergraph
    hypergraph.computeAndSetTotalNodeWeight(parallel_tag_t());
  }, [&] {
    // Construct incident net array
    hypergraph._incident_nets = IncidentNetArray(num_hypernodes, edge_vector);
  });
  return hypergraph;
}

/**
 * Compactifies a given hypergraph such that it only contains enabled vertices and hyperedges within
 * a consecutive range of IDs.
 */
std::pair<DynamicHypergraph, parallel::scalable_vector<HypernodeID> >
DynamicHypergraphFactory::compactify(const DynamicHypergraph& hypergraph) {
  HypernodeID num_hypernodes = 0;
  HyperedgeID num_hyperedges = 0;
  parallel::scalable_vector<HypernodeID> hn_mapping;
  parallel::scalable_vector<HyperedgeID> he_mapping;
  // Computes a mapping for vertices and hyperedges to a consecutive range of IDs
  // in the compactified hypergraph via a parallel prefix sum
  tbb::parallel_invoke([&] {
    hn_mapping.assign(hypergraph._num_hypernodes + 1, 0);
    hypergraph.doParallelForAllNodes([&](const HypernodeID hn) {
      hn_mapping[hn + 1] = ID(1);
    });

    parallel::TBBPrefixSum<HypernodeID, parallel::scalable_vector> hn_mapping_prefix_sum(hn_mapping);
    tbb::parallel_scan(tbb::blocked_range<size_t>(
      UL(0), hypergraph._num_hypernodes + 1), hn_mapping_prefix_sum);
    num_hypernodes = hn_mapping_prefix_sum.total_sum();
    hn_mapping.resize(hypergraph._num_hypernodes);
  }, [&] {
    he_mapping.assign(hypergraph._num_hyperedges + 1, 0);
    hypergraph.doParallelForAllEdges([&](const HyperedgeID& he) {
      he_mapping[he + 1] = ID(1);
    });

    parallel::TBBPrefixSum<HyperedgeID, parallel::scalable_vector> he_mapping_prefix_sum(he_mapping);
    tbb::parallel_scan(tbb::blocked_range<size_t>(
      UL(0), hypergraph._num_hyperedges + 1), he_mapping_prefix_sum);
    num_hyperedges = he_mapping_prefix_sum.total_sum();
    he_mapping.resize(hypergraph._num_hyperedges);
  });

  // Remap pins of each hyperedge
  using HyperedgeVector = parallel::scalable_vector<parallel::scalable_vector<HypernodeID>>;
  HyperedgeVector edge_vector;
  parallel::scalable_vector<HyperedgeWeight> hyperedge_weights;
  parallel::scalable_vector<HypernodeWeight> hypernode_weights;
  tbb::parallel_invoke([&] {
    hypernode_weights.resize(num_hypernodes);
    hypergraph.doParallelForAllNodes([&](const HypernodeID hn) {
      const HypernodeID mapped_hn = hn_mapping[hn];
      ASSERT(mapped_hn < num_hypernodes);
      hypernode_weights[mapped_hn] = hypergraph.nodeWeight(hn);
    });
  }, [&] {
    edge_vector.resize(num_hyperedges);
    hyperedge_weights.resize(num_hyperedges);
    hypergraph.doParallelForAllEdges([&](const HyperedgeID he) {
      const HyperedgeID mapped_he = he_mapping[he];
      ASSERT(mapped_he < num_hyperedges);
      hyperedge_weights[mapped_he] = hypergraph.edgeWeight(he);
      for ( const HypernodeID pin : hypergraph.pins(he) ) {
        edge_vector[mapped_he].push_back(hn_mapping[pin]);
      }
    });
  });

  // Construct compactified hypergraph
  DynamicHypergraph compactified_hypergraph = DynamicHypergraphFactory::construct(
    num_hypernodes, num_hyperedges, edge_vector, hyperedge_weights.data(), hypernode_weights.data());
  compactified_hypergraph._total_weight = hypergraph._total_weight;

  tbb::parallel_invoke([&] {
    // Set community ids
    hypergraph.doParallelForAllNodes([&](const HypernodeID& hn) {
      const HypernodeID mapped_hn = hn_mapping[hn];
      compactified_hypergraph.setCommunityID(mapped_hn, hypergraph.communityID(hn));
    });
  }, [&] {
    if ( hypergraph.hasFixedVertices() ) {
      // Set fixed vertices
      ds::FixedVertexSupport<DynamicHypergraph> fixed_vertices(
        compactified_hypergraph.initialNumNodes(), hypergraph._fixed_vertices.numBlocks());
      fixed_vertices.setHypergraph(&compactified_hypergraph);
      hypergraph.doParallelForAllNodes([&](const HypernodeID& hn) {
        if ( hypergraph.isFixed(hn) ) {
          const HypernodeID mapped_hn = hn_mapping[hn];
          fixed_vertices.fixToBlock(mapped_hn, hypergraph.fixedVertexBlock(hn));
        }
      });
      compactified_hypergraph.addFixedVertexSupport(std::move(fixed_vertices));
    }
  });

  tbb::parallel_invoke([&] {
    parallel::parallel_free(he_mapping,
      hyperedge_weights, hypernode_weights);
  }, [&] {
    parallel::parallel_free(edge_vector);
  });

  return std::make_pair(std::move(compactified_hypergraph), std::move(hn_mapping));
}

} // namespace ds
} // namespace mt_kahypar