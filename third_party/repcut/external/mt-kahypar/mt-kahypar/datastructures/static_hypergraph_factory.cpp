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

#include "static_hypergraph_factory.h"

#include <tbb/parallel_for.h>
#include <tbb/parallel_invoke.h>

#include "mt-kahypar/parallel/parallel_prefix_sum.h"
#include "mt-kahypar/utils/timer.h"

namespace mt_kahypar::ds {

  StaticHypergraph StaticHypergraphFactory::construct(
          const HypernodeID num_hypernodes,
          const HyperedgeID num_hyperedges,
          const HyperedgeVector& edge_vector,
          const HyperedgeWeight* hyperedge_weight,
          const HypernodeWeight* hypernode_weight,
          const bool stable_construction_of_incident_edges) {
    if (edge_vector.size() != num_hyperedges) {
      throw InvalidInputException("Number of hyperedges does not match length of input data!");
    }

    StaticHypergraph hypergraph;
    hypergraph._num_hypernodes = num_hypernodes;
    hypergraph._num_hyperedges = num_hyperedges;
    hypergraph._hypernodes.resize(num_hypernodes + 1);
    hypergraph._hyperedges.resize(num_hyperedges + 1);

    // Compute number of pins per hyperedge and number
    // of incident nets per vertex
    Counter num_pins_per_hyperedge(num_hyperedges, 0);
    ThreadLocalCounter local_incident_nets_per_vertex(num_hypernodes, 0);
    tbb::enumerable_thread_specific<size_t> local_max_edge_size(UL(0));
    tbb::parallel_for(ID(0), num_hyperedges, [&](const size_t pos) {
      Counter& num_incident_nets_per_vertex = local_incident_nets_per_vertex.local();
      num_pins_per_hyperedge[pos] = edge_vector[pos].size();
      if (num_pins_per_hyperedge[pos] == 0) {
        throw InvalidInputException("Hyperedge " + STR(pos) + " is empty (hyperedges must contain at least 1 pin)");
      }

      local_max_edge_size.local() = std::max(
              local_max_edge_size.local(), edge_vector[pos].size());
      for ( const HypernodeID& pin : edge_vector[pos] ) {
        if (pin >= num_hypernodes) {
          throw InvalidInputException("Hyperedge " + STR(pos) + " contains invalid pin: " + STR(pin));
        }
        ++num_incident_nets_per_vertex[pin];
      }
    });
    hypergraph._max_edge_size = local_max_edge_size.combine(
            [&](const size_t lhs, const size_t rhs) {
              return std::max(lhs, rhs);
            });

    // We sum up the number of incident nets per vertex only thread local.
    // To obtain the global number of incident nets per vertex, we iterate
    // over each thread local counter and sum it up.
    Counter num_incident_nets_per_vertex(num_hypernodes, 0);
    for ( Counter& c : local_incident_nets_per_vertex ) {
      tbb::parallel_for(ID(0), num_hypernodes, [&](const size_t pos) {
        num_incident_nets_per_vertex[pos] += c[pos];
      });
    }

    // Compute prefix sum over the number of pins per hyperedge and the
    // number of incident nets per vertex. The prefix sum is used than as
    // start position for each hyperedge resp. hypernode in the incidence
    // resp. incident nets array.
    parallel::TBBPrefixSum<size_t> pin_prefix_sum(num_pins_per_hyperedge);
    parallel::TBBPrefixSum<size_t> incident_net_prefix_sum(num_incident_nets_per_vertex);
    tbb::parallel_invoke([&] {
      tbb::parallel_scan(tbb::blocked_range<size_t>(
              UL(0), UI64(num_hyperedges)), pin_prefix_sum);
    }, [&] {
      tbb::parallel_scan(tbb::blocked_range<size_t>(
              UL(0), UI64(num_hypernodes)), incident_net_prefix_sum);
    });

    ASSERT(pin_prefix_sum.total_sum() == incident_net_prefix_sum.total_sum());
    hypergraph._num_pins = pin_prefix_sum.total_sum();
    hypergraph._total_degree = incident_net_prefix_sum.total_sum();
    hypergraph._incident_nets.resize(hypergraph._num_pins);
    hypergraph._incidence_array.resize(hypergraph._num_pins);

    AtomicCounter incident_nets_position(num_hypernodes,
                                         parallel::IntegralAtomicWrapper<size_t>(0));

    auto setup_hyperedges = [&] {
      tbb::parallel_for(ID(0), num_hyperedges, [&](const size_t pos) {
        StaticHypergraph::Hyperedge& hyperedge = hypergraph._hyperedges[pos];
        hyperedge.enable();
        hyperedge.setFirstEntry(pin_prefix_sum[pos]);
        hyperedge.setSize(pin_prefix_sum.value(pos));
        if ( hyperedge_weight ) {
          hyperedge.setWeight(hyperedge_weight[pos]);
        }

        const HyperedgeID he = pos;
        size_t incidence_array_pos = hyperedge.firstEntry();
        for ( const HypernodeID& pin : edge_vector[pos] ) {
          ASSERT(incidence_array_pos < hyperedge.firstInvalidEntry());
          ASSERT(pin < num_hypernodes);
          // Add pin to incidence array
          hypergraph._incidence_array[incidence_array_pos++] = pin;
          // Add hyperedge he as a incident net to pin
          const size_t incident_nets_pos = incident_net_prefix_sum[pin] +
                  incident_nets_position[pin].fetch_add(1, std::memory_order_relaxed);
          ASSERT(incident_nets_pos < incident_net_prefix_sum[pin + 1]);
          hypergraph._incident_nets[incident_nets_pos] = he;
        }
      });
    };

    auto setup_hypernodes = [&] {
      tbb::parallel_for(ID(0), num_hypernodes, [&](const size_t pos) {
        StaticHypergraph::Hypernode& hypernode = hypergraph._hypernodes[pos];
        hypernode.enable();
        hypernode.setFirstEntry(incident_net_prefix_sum[pos]);
        hypernode.setSize(incident_net_prefix_sum.value(pos));
        if ( hypernode_weight ) {
          hypernode.setWeight(hypernode_weight[pos]);
        }
      });
    };

    auto init_communities = [&] {
      hypergraph._community_ids.resize(num_hypernodes, 0);
    };

    tbb::parallel_invoke(setup_hyperedges, setup_hypernodes, init_communities);

    if (stable_construction_of_incident_edges) {
      // sort incident hyperedges of each node, so their ordering is independent of scheduling (and the same as a typical sequential implementation)
      tbb::parallel_for(ID(0), num_hypernodes, [&](HypernodeID u) {
        auto b = hypergraph._incident_nets.begin() + hypergraph.hypernode(u).firstEntry();
        auto e = hypergraph._incident_nets.begin() + hypergraph.hypernode(u).firstInvalidEntry();
        std::sort(b, e);
      });
    }

    // Add Sentinels
    hypergraph._hypernodes.back() = StaticHypergraph::Hypernode(hypergraph._incident_nets.size());
    hypergraph._hyperedges.back() = StaticHypergraph::Hyperedge(hypergraph._incidence_array.size());

    hypergraph.computeAndSetTotalNodeWeight(parallel_tag_t());
    return hypergraph;
  }

}