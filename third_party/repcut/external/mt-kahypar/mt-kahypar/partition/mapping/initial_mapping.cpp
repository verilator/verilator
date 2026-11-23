/*******************************************************************************
 * MIT License
 *
 * This file is part of Mt-KaHyPar.
 *
 * Copyright (C) 2023 Tobias Heuer <tobias.heuer@kit.edu>
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

#include "mt-kahypar/partition/mapping/initial_mapping.h"

#include <tbb/parallel_invoke.h>

#include "mt-kahypar/definitions.h"
#include "mt-kahypar/partition/mapping/target_graph.h"
#include "mt-kahypar/partition/mapping/greedy_mapping.h"
#include "mt-kahypar/partition/metrics.h"
#include "mt-kahypar/parallel/stl/scalable_vector.h"
#include "mt-kahypar/utils/utilities.h"
#include "mt-kahypar/parallel/memory_pool.h"

namespace mt_kahypar {

namespace {

using HyperedgeVector = vec<vec<HypernodeID>>;

template<typename PartitionedHypergraph>
std::pair<ds::StaticHypergraph, StaticPartitionedHypergraph> convert_to_static_hypergraph(const PartitionedHypergraph& phg) {
  using Hypergraph = ds::StaticHypergraph;
  using TargetPartitionedHypergraph = StaticPartitionedHypergraph;
  using Factory = typename Hypergraph::Factory;

  const HypernodeID num_hypernodes = phg.initialNumNodes();
  const HyperedgeID num_hyperedges = phg.initialNumEdges() / (PartitionedHypergraph::is_graph ? 2 : 1);
  HyperedgeVector edge_vector;
  vec<HyperedgeWeight> hyperedge_weight;
  vec<HypernodeWeight> hypernode_weight;

  // Allocate data structure
  tbb::parallel_invoke([&] {
    edge_vector.assign(num_hyperedges, vec<HypernodeID>());
  }, [&] {
    hyperedge_weight.assign(num_hyperedges, 0);
  }, [&] {
    hypernode_weight.assign(num_hypernodes, 0);
  });

  // Write hypergraph into temporary data structure
  tbb::parallel_invoke([&] {
    if constexpr ( PartitionedHypergraph::is_graph ) {
      CAtomic<size_t> cnt(0);
      phg.doParallelForAllEdges([&](const HyperedgeID& he) {
        const HypernodeID u = phg.edgeSource(he);
        const HypernodeID v = phg.edgeTarget(he);
        if ( u < v ) {
          // insert each edge only once
          const size_t id = cnt.fetch_add(1, std::memory_order_relaxed);
          hyperedge_weight[id] = phg.edgeWeight(he);
          edge_vector[id].push_back(u);
          edge_vector[id].push_back(v);
        }
      });
    } else {
      phg.doParallelForAllEdges([&](const HyperedgeID& he) {
        hyperedge_weight[he] = phg.edgeWeight(he);
        for ( const HypernodeID& pin : phg.pins(he) ) {
          edge_vector[he].push_back(pin);
        }
      });
    }
  }, [&] {
    phg.doParallelForAllNodes([&](const HypernodeID& hn) {
      hypernode_weight[hn] = phg.nodeWeight(hn);
    });
  });

  // Construct new hypergraph and apply partition
  Hypergraph converted_hg = Factory::construct(num_hypernodes, num_hyperedges,
    edge_vector, hyperedge_weight.data(), hypernode_weight.data());
  converted_hg.doParallelForAllNodes([&](const HypernodeID& hn) {
    if ( !phg.nodeIsEnabled(hn) ) {
      ASSERT(converted_hg.nodeDegree(hn) == 0);
      converted_hg.disableHypernode(hn);
    }
  });

  TargetPartitionedHypergraph converted_phg(phg.k(), converted_hg, parallel_tag_t { });
  phg.doParallelForAllNodes([&](const HypernodeID& hn) {
    converted_phg.setOnlyNodePart(hn, phg.partID(hn));
  });
  converted_phg.initializePartition();

  // Map fixed vertices to new hypergraph
  if ( phg.hasFixedVertices() ) {
    ds::FixedVertexSupport<ds::StaticHypergraph> fixed_vertices_copy(phg.initialNumNodes(), phg.k());
    fixed_vertices_copy.setHypergraph(&converted_hg);
    phg.doParallelForAllNodes([&](const HypernodeID& hn) {
      if ( phg.isFixed(hn) ) {
        fixed_vertices_copy.fixToBlock(hn, phg.fixedVertexBlock(hn));
      }
    });
    converted_hg.addFixedVertexSupport(std::move(fixed_vertices_copy));
  }

  ASSERT(metrics::quality(phg, Objective::cut) == metrics::quality(converted_phg, Objective::cut));
  return std::make_pair<Hypergraph, TargetPartitionedHypergraph>(
    std::move(converted_hg), std::move(converted_phg));
}

template<typename PartitionedHypergraph, typename TargetPartitionedHypergraph>
void applyPartition(PartitionedHypergraph& phg,
                    TargetPartitionedHypergraph& target_phg) {
  target_phg.doParallelForAllNodes([&](const HypernodeID& hn) {
    const PartitionID from = target_phg.partID(hn);
    const PartitionID to = phg.partID(hn);
    if ( from != to ) {
      target_phg.changeNodePart(hn, from, to);
    }
  });
}

template<typename Hypergraph, typename PartitionedHypergraph>
Hypergraph repairEmptyBlocks(const Hypergraph& contracted_hg,
                             const PartitionedHypergraph& communication_hg,
                             vec<HypernodeID>& mapping,
                             bool deterministic) {
  using Factory = typename Hypergraph::Factory;
  const PartitionID k = communication_hg.k();
  vec<HypernodeID> block_mapping(contracted_hg.initialNumNodes(), kInvalidHypernode);
  HypernodeID cur_id = 0;
  vec<HypernodeWeight> hypernode_weight(k, 0);
  for ( PartitionID block = 0; block < k; ++block ) {
    if ( communication_hg.partWeight(block) > 0 ) {
      ASSERT(UL(cur_id) < block_mapping.size());
      block_mapping[cur_id++] = block;
    }
    hypernode_weight[block] = communication_hg.partWeight(block);
  }

  const HypernodeID num_hypernodes = k;
  const HyperedgeID num_hyperedges = contracted_hg.initialNumEdges();
  HyperedgeVector edge_vector(num_hyperedges, vec<HypernodeID>());
  vec<HyperedgeWeight> hyperedge_weight(num_hyperedges, 0);
  contracted_hg.doParallelForAllEdges([&](const HyperedgeID& he) {
    for ( const HypernodeID& pin : contracted_hg.pins(he) ) {
      edge_vector[he].push_back(block_mapping[pin]);
    }
    hyperedge_weight[he] = contracted_hg.edgeWeight(he);
  });

  // Adapt mapping
  communication_hg.doParallelForAllNodes([&](const HypernodeID& hn) {
    mapping[hn] = block_mapping[mapping[hn]];
  });

  return Factory::construct(num_hypernodes, num_hyperedges,
    edge_vector, hyperedge_weight.data(), hypernode_weight.data(), deterministic);
}

template<typename PartitionedHypergraph>
void map_to_target_graph(PartitionedHypergraph& communication_hg,
                         const TargetGraph& target_graph,
                         const Context& context) {
  using Hypergraph = typename PartitionedHypergraph::UnderlyingHypergraph;
  utils::Timer& timer = utils::Utilities::instance().getTimer(context.utility_id);
  const bool was_unused_memory_allocations_enabled =
    parallel::MemoryPoolT::instance().is_unused_memory_allocations_activated();
  parallel::MemoryPoolT::instance().deactivate_unused_memory_allocations();
  // We contract all blocks of the partition to create an one-to-one mapping problem
  timer.start_timer("contract_partition", "Contract Partition");
  vec<HypernodeID> mapping(communication_hg.initialNumNodes(), kInvalidHypernode);
  communication_hg.setTargetGraph(&target_graph);
  if (static_cast<HypernodeID>(context.partition.k) <= communication_hg.initialNumNodes()) {
    communication_hg.doParallelForAllNodes([&](const HypernodeID hn) {
      mapping[hn] = communication_hg.partID(hn);
    });
  } else {
    std::iota(mapping.begin(), mapping.end(), 0);
  }
  // Here, we collapse each block of the communication hypergraph partition into
  // a single node. The contracted hypergraph has exactly k nodes. In the
  // contracted hypergraph node i corresponds to block i of the input
  // communication hypergraph.
  Hypergraph contracted_hg = communication_hg.hypergraph().contract(mapping, context.partition.deterministic);
  if ( contracted_hg.initialNumNodes() < static_cast<HypernodeID>(communication_hg.k()) ) {
    // If the contracted hypergraph has less than k nodes then there must be some empty
    // blocks which we have to fix in the following
    contracted_hg = repairEmptyBlocks(contracted_hg, communication_hg, mapping, context.partition.deterministic);
  }
  PartitionedHypergraph contracted_phg(communication_hg.k(), contracted_hg);
  for ( const HypernodeID& hn : contracted_phg.nodes() ) {
    contracted_phg.setOnlyNodePart(hn, hn);
  }
  contracted_phg.initializePartition();
  contracted_phg.setTargetGraph(&target_graph);
  timer.stop_timer("contract_partition");

  const HyperedgeWeight objective_before = metrics::quality(contracted_phg, Objective::steiner_tree);
  ASSERT(metrics::quality(communication_hg, Objective::steiner_tree) == objective_before);

  // Solve one-to-one mapping problem
  if ( context.mapping.strategy == OneToOneMappingStrategy::greedy_mapping ) {
    GreedyMapping<PartitionedHypergraph>::mapToTargetGraph(contracted_phg, target_graph, context);
  }

  const HyperedgeWeight objective_after = metrics::quality(contracted_phg, Objective::steiner_tree);
  if ( objective_after < objective_before ) {
    if ( context.partition.enable_logging && context.partition.verbose_logging ) {
      LOG << GREEN << "Initial one-to-one mapping algorithm has improved objective by"
          << (objective_before - objective_after)
          << "( Before =" << objective_before << ", After =" << objective_after << ")" << END;
    }
    // Initial mapping algorithm has improved solution quality
    // => apply improved mapping to input communication hypergraph
    communication_hg.doParallelForAllNodes([&](const HypernodeID& hn) {
      const PartitionID from = communication_hg.partID(hn);
      const PartitionID to = contracted_phg.partID(mapping[hn]);
      if ( from != to ) {
        communication_hg.changeNodePart(hn, from, to);
      }
    });
  } else if ( context.partition.enable_logging
              && context.partition.verbose_logging
              && objective_before < objective_after ) {
    // Initial mapping algorithm has worsen solution quality
    // => use input partition of communication hypergraph
    LOG << RED << "Initial one-to-one mapping algorithm has worsen objective by"
      << (objective_after - objective_before)
      << "( Before =" << objective_before << ", After =" << objective_after << ")."
      << "Use mapping from initial partitiong!"<< END;
  }

  if ( was_unused_memory_allocations_enabled ) {
    parallel::MemoryPoolT::instance().activate_unused_memory_allocations();
  }
}

}

template<typename TypeTraits>
void InitialMapping<TypeTraits>::mapToTargetGraph(PartitionedHypergraph& communication_hg,
                                                   const TargetGraph& target_graph,
                                                   const Context& context) {
  if constexpr ( !PartitionedHypergraph::is_static_hypergraph ) {
    // The mapping algorithm collapses each block of the communication hypergraph partition into
    // a single node. Thereby, it uses the contract(...) function of the hypergraph data structure
    // which is only implemented for static graphs and hypergraphs (implemented for multilevel partitioing,
    // but not for n-level). In case the communication hypergraph uses an dynamic graph or hypergraph
    // data structure, we convert it to static data structure and then compute the initial mapping.
    auto static_hypergraph = convert_to_static_hypergraph(communication_hg);
    StaticPartitionedHypergraph& tmp_communication_hg = static_hypergraph.second;
    tmp_communication_hg.setHypergraph(static_hypergraph.first);
    map_to_target_graph(tmp_communication_hg, target_graph, context);
    applyPartition(tmp_communication_hg, communication_hg);
  } else {
    map_to_target_graph(communication_hg, target_graph, context);
  }
}

INSTANTIATE_CLASS_WITH_TYPE_TRAITS(InitialMapping)

}  // namespace kahypar
