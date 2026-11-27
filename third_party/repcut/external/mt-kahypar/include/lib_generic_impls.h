/*******************************************************************************
 * MIT License
 *
 * This file is part of Mt-KaHyPar.
 *
 * Copyright (C) 2024 Nikolai Maas <nikolai.maas@kit.edu>
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

#include <string>
#include <sstream>
#include <type_traits>

#include "mtkahypartypes.h"

#include "mt-kahypar/definitions.h"
#include "mt-kahypar/partition/context.h"
#include "mt-kahypar/partition/conversion.h"
#include "mt-kahypar/partition/metrics.h"
#include "mt-kahypar/io/hypergraph_io.h"
#include "mt-kahypar/utils/cast.h"
#include "mt-kahypar/utils/exception.h"


using namespace mt_kahypar;

namespace lib {
  using StaticGraph = typename StaticGraphTypeTraits::Hypergraph;
  using DynamicGraph = typename DynamicGraphTypeTraits::Hypergraph;
  using StaticHypergraph = typename StaticHypergraphTypeTraits::Hypergraph;
  using DynamicHypergraph = typename DynamicHypergraphTypeTraits::Hypergraph;

  using StaticPartitionedGraph = typename StaticGraphTypeTraits::PartitionedHypergraph;
  using DynamicPartitionedGraph = typename DynamicGraphTypeTraits::PartitionedHypergraph;
  using StaticPartitionedHypergraph = typename StaticHypergraphTypeTraits::PartitionedHypergraph;
  using DynamicPartitionedHypergraph = typename DynamicHypergraphTypeTraits::PartitionedHypergraph;
  using SparsePartitionedHypergraph = typename LargeKHypergraphTypeTraits::PartitionedHypergraph;


// ####################### Generic Handling of Different Graph Types #######################

template<typename ReturnT, bool Throwing, typename Func>
ReturnT switch_hg(mt_kahypar_hypergraph_t hg, Func f) {
  switch ( hg.type ) {
    case STATIC_GRAPH:
      return f(utils::cast<StaticGraph>(hg));
    case DYNAMIC_GRAPH:
      return f(utils::cast<DynamicGraph>(hg));
    case STATIC_HYPERGRAPH:
      return f(utils::cast<StaticHypergraph>(hg));
    case DYNAMIC_HYPERGRAPH:
      return f(utils::cast<DynamicHypergraph>(hg));
    case NULLPTR_HYPERGRAPH: break;
  }
  if constexpr (Throwing) {
    throw UnsupportedOperationException("Input is not a valid hypergraph.");
  }
  return ReturnT{};
}

template<typename ReturnT, bool Throwing, typename Func>
ReturnT switch_graph(mt_kahypar_hypergraph_t hg, Func f) {
  switch ( hg.type ) {
    case STATIC_GRAPH:
      return f(utils::cast<StaticGraph>(hg));
    case DYNAMIC_GRAPH:
      return f(utils::cast<DynamicGraph>(hg));
    case STATIC_HYPERGRAPH:
    case DYNAMIC_HYPERGRAPH:
    case NULLPTR_HYPERGRAPH:
      break;
  }
  if constexpr (Throwing) {
    throw UnsupportedOperationException("Input is not a graph.");
  }
  return ReturnT{};
}

template<typename ReturnT, bool Throwing, typename Func>
ReturnT switch_phg(mt_kahypar_partitioned_hypergraph_t phg, Func f) {
  switch ( phg.type ) {
    case MULTILEVEL_GRAPH_PARTITIONING:
      return f(utils::cast<StaticPartitionedGraph>(phg));
    case N_LEVEL_GRAPH_PARTITIONING:
      return f(utils::cast<DynamicPartitionedGraph>(phg));
    case MULTILEVEL_HYPERGRAPH_PARTITIONING:
      return f(utils::cast<StaticPartitionedHypergraph>(phg));
    case N_LEVEL_HYPERGRAPH_PARTITIONING:
      return f(utils::cast<DynamicPartitionedHypergraph>(phg));
    case LARGE_K_PARTITIONING:
      return f(utils::cast<SparsePartitionedHypergraph>(phg));
    case NULLPTR_PARTITION:
      break;
  }
  if constexpr (Throwing) {
    throw UnsupportedOperationException("Input is not a valid partitioned hypergraph.");
  }
  return ReturnT{};
}

template<typename HypergraphT>
void check_hypernode_is_valid(const HypergraphT& hg, HypernodeID hn) {
  if (hn >= hg.initialNumNodes()) {
    std::stringstream ss;
    ss << "Invalid hypernode: ID is \"" << hn << "\", but there are only "
       << hg.initialNumNodes() << " nodes";
    throw InvalidInputException(ss.str());
  }
}

template<typename HypergraphT>
void check_hyperedge_is_valid(const HypergraphT& hg, HyperedgeID he) {
  if (he >= hg.initialNumEdges()) {
    std::stringstream ss;
    ss << "Invalid hyperedge: ID is \"" << he << "\", but there are only "
       << hg.initialNumEdges() << " edges";
    throw InvalidInputException(ss.str());
  }
}

template<typename PartitionedHypergraphT>
void check_block_is_valid(const PartitionedHypergraphT& phg, PartitionID block) {
  if (block >= phg.k()) {
    std::stringstream ss;
    ss << "Invalid block: ID is \"" << block << "\", but the partition has only "
       << phg.k() << " blocks";
    throw InvalidInputException(ss.str());
  }
}


// ####################### Hypergraph Generic Implementations #######################

template<bool Throwing>
HypernodeID num_nodes(mt_kahypar_hypergraph_t hypergraph) {
  return switch_hg<PartitionID, Throwing>(hypergraph, [](const auto& hg) {
    return hg.initialNumNodes();
  });
}

template<bool Throwing>
HyperedgeID num_edges(mt_kahypar_hypergraph_t hypergraph) {
  return switch_hg<HyperedgeID, Throwing>(hypergraph, [](const auto& hg) {
    return hg.initialNumEdges();
  });
}

template<bool Throwing>
HypernodeID num_pins(mt_kahypar_hypergraph_t hypergraph) {
  return switch_hg<HypernodeID, Throwing>(hypergraph, [](const auto& hg) {
    return hg.initialNumPins();
  });
}

template<bool Throwing>
HypernodeWeight total_weight(mt_kahypar_hypergraph_t hypergraph) {
  return switch_hg<HypernodeWeight, Throwing>(hypergraph, [](const auto& hg) {
    return hg.totalWeight();
  });
}

template<bool Throwing>
HyperedgeID node_degree(mt_kahypar_hypergraph_t hypergraph, HypernodeID hn) {
  return switch_hg<HyperedgeID, Throwing>(hypergraph, [=](const auto& hg) {
    if constexpr (Throwing) {
      check_hypernode_is_valid(hg, hn);
    }
    return hg.nodeDegree(hn);
  });
}

template<bool Throwing>
HypernodeWeight node_weight(mt_kahypar_hypergraph_t hypergraph, HypernodeID hn) {
  return switch_hg<HypernodeWeight, Throwing>(hypergraph, [=](const auto& hg) {
    if constexpr (Throwing) {
      check_hypernode_is_valid(hg, hn);
    }
    return hg.nodeWeight(hn);
  });
}

template<bool Throwing>
bool is_fixed(mt_kahypar_hypergraph_t hypergraph, HypernodeID hn) {
  return switch_hg<bool, Throwing>(hypergraph, [=](const auto& hg) {
    if constexpr (Throwing) {
      check_hypernode_is_valid(hg, hn);
    }
    return hg.isFixed(hn);
  });
}

template<bool Throwing>
PartitionID fixed_vertex_block(mt_kahypar_hypergraph_t hypergraph, HypernodeID hn) {
  return switch_hg<PartitionID, Throwing>(hypergraph, [=](const auto& hg) {
    if constexpr (Throwing) {
      check_hypernode_is_valid(hg, hn);
    }
    return hg.isFixed(hn) ? hg.fixedVertexBlock(hn) : kInvalidPartition;
  });
}

template<bool Throwing>
HypernodeID edge_size(mt_kahypar_hypergraph_t hypergraph, HyperedgeID he) {
  return switch_hg<HypernodeID, Throwing>(hypergraph, [=](const auto& hg) {
    if constexpr (Throwing) {
      check_hyperedge_is_valid(hg, he);
    }
    return hg.edgeSize(he);
  });
}

template<bool Throwing>
HyperedgeWeight edge_weight(mt_kahypar_hypergraph_t hypergraph, HyperedgeID he) {
  return switch_hg<HyperedgeWeight, Throwing>(hypergraph, [=](const auto& hg) {
    if constexpr (Throwing) {
      check_hyperedge_is_valid(hg, he);
    }
    return hg.edgeWeight(he);
  });
}


// ####################### Partitioned Hypergraph Generic Implementations #######################

template<bool Throwing>
void write_partition_to_file(mt_kahypar_partitioned_hypergraph_t p, const std::string& partition_file) {
  switch_phg<int, Throwing>(p, [&](auto& phg) {
    io::writePartitionFile(phg, partition_file);
    return 0;
  });
}

template<bool Throwing>
void get_partition(mt_kahypar_partitioned_hypergraph_t p, mt_kahypar_partition_id_t* partition) {
  ASSERT(partition != nullptr);
  switch_phg<int, Throwing>(p, [&](const auto& phg) {
    phg.doParallelForAllNodes([&](const HypernodeID& hn) {
      partition[hn] = phg.partID(hn);
    });
    return 0;
  });
}

template<bool Throwing>
void get_block_weights(mt_kahypar_partitioned_hypergraph_t p, mt_kahypar_hypernode_weight_t* block_weights) {
  ASSERT(block_weights != nullptr);
  switch_phg<int, Throwing>(p, [&](const auto& phg) {
    for ( PartitionID i = 0; i < phg.k(); ++i ) {
      block_weights[i] = phg.partWeight(i);
    }
    return 0;
  });
}

template<bool Throwing>
PartitionID num_blocks(mt_kahypar_partitioned_hypergraph_t p) {
  return switch_phg<PartitionID, Throwing>(p, [](const auto& phg) {
    return phg.k();
  });
}

template<bool Throwing>
HypernodeWeight block_weight(mt_kahypar_partitioned_hypergraph_t p, PartitionID block) {
  return switch_phg<HypernodeWeight, Throwing>(p, [=](const auto& phg) {
    if constexpr (Throwing) {
      check_block_is_valid(phg, block);
    }
    return phg.partWeight(block);
  });
}

template<bool Throwing>
PartitionID block_id(mt_kahypar_partitioned_hypergraph_t p, HypernodeID hn) {
  return switch_phg<PartitionID, Throwing>(p, [=](const auto& phg) {
    if constexpr (Throwing) {
      check_hypernode_is_valid(phg, hn);
    }
    return phg.partID(hn);
  });
}

template<bool Throwing>
bool is_incident_to_cut_edge(mt_kahypar_partitioned_hypergraph_t p, HypernodeID hn) {
  return switch_phg<bool, Throwing>(p, [=](const auto& phg) {
    if constexpr (Throwing) {
      check_hypernode_is_valid(phg, hn);
    }
    return phg.isBorderNode(hn);
  });
}

template<bool Throwing>
HyperedgeID num_incident_cut_edges(mt_kahypar_partitioned_hypergraph_t p, HypernodeID hn) {
  return switch_phg<HyperedgeID, Throwing>(p, [=](const auto& phg) {
    if constexpr (Throwing) {
      check_hypernode_is_valid(phg, hn);
    }
    return phg.numIncidentCutHyperedges(hn);
  });
}

template<bool Throwing>
PartitionID connectivity(mt_kahypar_partitioned_hypergraph_t p, HyperedgeID he) {
  return switch_phg<PartitionID, Throwing>(p, [=](const auto& phg) {
    if constexpr (Throwing) {
      check_hyperedge_is_valid(phg, he);
    }
    return phg.connectivity(he);
  });
}

template<bool Throwing>
HypernodeID num_pins_in_block(mt_kahypar_partitioned_hypergraph_t p, HyperedgeID he, PartitionID block) {
  return switch_phg<HypernodeID, Throwing>(p, [=](const auto& phg) {
    if constexpr (Throwing) {
      check_hyperedge_is_valid(phg, he);
      check_block_is_valid(phg, block);
    }
    return phg.pinCountInPart(he, block);
  });
}

template<bool Throwing>
double imbalance(mt_kahypar_partitioned_hypergraph_t p, const Context& context) {
  return switch_phg<double, Throwing>(p, [&](const auto& phg) {
    if (Throwing && context.partition.k != phg.k()) {
      std::stringstream ss;
      ss << "Mismatched number of blocks: the context specifies " << context.partition.k
         << " blocks, but the partition has " << phg.k() << " blocks";
      throw InvalidInputException(ss.str());
    }
    Context c(context);
    c.setupPartWeights(phg.totalWeight());
    return metrics::imbalance(phg, c).imbalance_value;
  });
}

template<bool Throwing>
HyperedgeWeight cut(mt_kahypar_partitioned_hypergraph_t p) {
  return switch_phg<HyperedgeWeight, Throwing>(p, [&](const auto& phg) {
    return metrics::quality(phg, Objective::cut);
  });
}

template<bool Throwing>
HyperedgeWeight km1(mt_kahypar_partitioned_hypergraph_t p) {
  return switch_phg<HyperedgeWeight, Throwing>(p, [&](const auto& phg) {
    return metrics::quality(phg, Objective::km1);
  });
}

template<bool Throwing>
HyperedgeWeight soed(mt_kahypar_partitioned_hypergraph_t p) {
  return switch_phg<HyperedgeWeight, Throwing>(p, [&](const auto& phg) {
    return metrics::quality(phg, Objective::soed);
  });
}

} // namespace lib
