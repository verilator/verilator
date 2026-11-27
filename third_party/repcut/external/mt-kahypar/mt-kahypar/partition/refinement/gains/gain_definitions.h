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

#pragma once

#include "kahypar-resources/meta/typelist.h"
#include "kahypar-resources/meta/policy_registry.h"

#include "mt-kahypar/definitions.h"
#include "mt-kahypar/partition/context_enum_classes.h"
#include "mt-kahypar/datastructures/hypergraph_common.h"
#include "mt-kahypar/partition/refinement/gains/km1/km1_gain_cache.h"
#include "mt-kahypar/partition/refinement/gains/km1/km1_rollback.h"
#include "mt-kahypar/partition/refinement/gains/km1/km1_gain_computation.h"
#include "mt-kahypar/partition/refinement/gains/km1/km1_attributed_gains.h"
#include "mt-kahypar/partition/refinement/gains/km1/km1_flow_network_construction.h"
#include "mt-kahypar/partition/refinement/gains/cut/cut_gain_cache.h"
#include "mt-kahypar/partition/refinement/gains/cut/cut_rollback.h"
#include "mt-kahypar/partition/refinement/gains/cut/cut_gain_computation.h"
#include "mt-kahypar/partition/refinement/gains/cut/cut_attributed_gains.h"
#include "mt-kahypar/partition/refinement/gains/cut/cut_flow_network_construction.h"
#ifdef KAHYPAR_ENABLE_SOED_METRIC
#include "mt-kahypar/partition/refinement/gains/soed/soed_attributed_gains.h"
#include "mt-kahypar/partition/refinement/gains/soed/soed_gain_computation.h"
#include "mt-kahypar/partition/refinement/gains/soed/soed_gain_cache.h"
#include "mt-kahypar/partition/refinement/gains/soed/soed_rollback.h"
#include "mt-kahypar/partition/refinement/gains/soed/soed_flow_network_construction.h"
#endif
#ifdef KAHYPAR_ENABLE_STEINER_TREE_METRIC
#include "mt-kahypar/partition/refinement/gains/steiner_tree/steiner_tree_attributed_gains.h"
#include "mt-kahypar/partition/refinement/gains/steiner_tree/steiner_tree_gain_computation.h"
#include "mt-kahypar/partition/refinement/gains/steiner_tree/steiner_tree_gain_cache.h"
#include "mt-kahypar/partition/refinement/gains/steiner_tree/steiner_tree_rollback.h"
#include "mt-kahypar/partition/refinement/gains/steiner_tree/steiner_tree_flow_network_construction.h"
#endif
#ifdef KAHYPAR_ENABLE_GRAPH_PARTITIONING_FEATURES
#ifdef KAHYPAR_ENABLE_STEINER_TREE_METRIC
#include "mt-kahypar/partition/refinement/gains/steiner_tree_for_graphs/steiner_tree_attributed_gains_for_graphs.h"
#include "mt-kahypar/partition/refinement/gains/steiner_tree_for_graphs/steiner_tree_gain_computation_for_graphs.h"
#include "mt-kahypar/partition/refinement/gains/steiner_tree_for_graphs/steiner_tree_gain_cache_for_graphs.h"
#include "mt-kahypar/partition/refinement/gains/steiner_tree_for_graphs/steiner_tree_flow_network_construction_for_graphs.h"
#endif
#include "mt-kahypar/partition/refinement/gains/cut_for_graphs/cut_gain_cache_for_graphs.h"
#include "mt-kahypar/partition/refinement/gains/cut_for_graphs/cut_attributed_gains_for_graphs.h"
#endif
#include "mt-kahypar/macros.h"
#include "mt-kahypar/utils/exception.h"

namespace mt_kahypar {

struct Km1GainTypes : public kahypar::meta::PolicyBase {
  using GainComputation = Km1GainComputation;
  using AttributedGains = Km1AttributedGains;
  using GainCache = Km1GainCache;
  using DeltaGainCache = DeltaKm1GainCache;
  using Rollback = Km1Rollback;
  using FlowNetworkConstruction = Km1FlowNetworkConstruction;
};

struct CutGainTypes : public kahypar::meta::PolicyBase {
  using GainComputation = CutGainComputation;
  using AttributedGains = CutAttributedGains;
  using GainCache = CutGainCache;
  using DeltaGainCache = DeltaCutGainCache;
  using Rollback = CutRollback;
  using FlowNetworkConstruction = CutFlowNetworkConstruction;
};

#ifdef KAHYPAR_ENABLE_SOED_METRIC
struct SoedGainTypes : public kahypar::meta::PolicyBase {
  using GainComputation = SoedGainComputation;
  using AttributedGains = SoedAttributedGains;
  using GainCache = SoedGainCache;
  using DeltaGainCache = DeltaSoedGainCache;
  using Rollback = SoedRollback;
  using FlowNetworkConstruction = SoedFlowNetworkConstruction;
};
#endif

#ifdef KAHYPAR_ENABLE_STEINER_TREE_METRIC
struct SteinerTreeGainTypes : public kahypar::meta::PolicyBase {
  using GainComputation = SteinerTreeGainComputation;
  using AttributedGains = SteinerTreeAttributedGains;
  using GainCache = SteinerTreeGainCache;
  using DeltaGainCache = DeltaSteinerTreeGainCache;
  using Rollback = SteinerTreeRollback;
  using FlowNetworkConstruction = SteinerTreeFlowNetworkConstruction;
};
#endif

#ifdef KAHYPAR_ENABLE_GRAPH_PARTITIONING_FEATURES
struct CutGainForGraphsTypes : public kahypar::meta::PolicyBase {
  using GainComputation = CutGainComputation;
  using AttributedGains = GraphCutAttributedGains;
  using GainCache = GraphCutGainCache;
  using DeltaGainCache = DeltaGraphCutGainCache;
  using Rollback = Km1Rollback;
  using FlowNetworkConstruction = CutFlowNetworkConstruction;
};

#ifdef KAHYPAR_ENABLE_STEINER_TREE_METRIC
struct SteinerTreeForGraphsTypes : public kahypar::meta::PolicyBase {
  using GainComputation = GraphSteinerTreeGainComputation;
  using AttributedGains = GraphSteinerTreeAttributedGains;
  using GainCache = GraphSteinerTreeGainCache;
  using DeltaGainCache = GraphDeltaSteinerTreeGainCache;
  using Rollback = SteinerTreeRollback;
  using FlowNetworkConstruction = GraphSteinerTreeFlowNetworkConstruction;
};
#endif
#endif

template<typename TypeTraitsT, typename GainTypesT>
struct GraphAndGainTypes : public kahypar::meta::PolicyBase {
  using TypeTraits = TypeTraitsT;
  using GainTypes = GainTypesT;

  using Hypergraph = typename TypeTraits::Hypergraph;
  using PartitionedHypergraph = typename TypeTraits::PartitionedHypergraph;

  using GainComputation = typename GainTypes::GainComputation;
  using AttributedGains = typename GainTypes::AttributedGains;
  using GainCache = typename GainTypes::GainCache;
  using DeltaGainCache = typename GainTypes::DeltaGainCache;
  using Rollback = typename GainTypes::Rollback;
  using FlowNetworkConstruction = typename GainTypes::FlowNetworkConstruction;
};


using GainTypes = kahypar::meta::Typelist<Km1GainTypes,
                                          CutGainTypes
                                          ENABLE_SOED(COMMA SoedGainTypes)
                                          ENABLE_STEINER_TREE(COMMA SteinerTreeGainTypes)
                                          ENABLE_GRAPHS(COMMA CutGainForGraphsTypes)
                                          ENABLE_GRAPHS(ENABLE_STEINER_TREE(COMMA SteinerTreeForGraphsTypes))>;

#define _LIST_HYPERGRAPH_COMBINATIONS(TYPE_TRAITS)                                     \
  GraphAndGainTypes<TYPE_TRAITS, Km1GainTypes>,                                           \
  GraphAndGainTypes<TYPE_TRAITS, CutGainTypes>                                            \
  ENABLE_SOED(COMMA GraphAndGainTypes<TYPE_TRAITS COMMA SoedGainTypes>)                   \
  ENABLE_STEINER_TREE(COMMA GraphAndGainTypes<TYPE_TRAITS COMMA SteinerTreeGainTypes>)

#define _LIST_GRAPH_COMBINATIONS(TYPE_TRAITS)                                             \
  GraphAndGainTypes<TYPE_TRAITS, CutGainForGraphsTypes>                                      \
  ENABLE_STEINER_TREE(COMMA GraphAndGainTypes<TYPE_TRAITS COMMA SteinerTreeForGraphsTypes>)

using GraphAndGainTypesList = kahypar::meta::Typelist<_LIST_HYPERGRAPH_COMBINATIONS(StaticHypergraphTypeTraits)
                                                      ENABLE_GRAPHS(COMMA _LIST_GRAPH_COMBINATIONS(StaticGraphTypeTraits))
                                                      ENABLE_HIGHEST_QUALITY(COMMA _LIST_HYPERGRAPH_COMBINATIONS(DynamicHypergraphTypeTraits))
                                                      ENABLE_HIGHEST_QUALITY_FOR_GRAPHS(COMMA _LIST_GRAPH_COMBINATIONS(DynamicGraphTypeTraits))
                                                      ENABLE_LARGE_K(COMMA _LIST_HYPERGRAPH_COMBINATIONS(LargeKHypergraphTypeTraits))>;


#define _INSTANTIATE_CLASS_MACRO_FOR_HYPERGRAPH_COMBINATIONS(C, TYPE_TRAITS)                  \
  template class C(GraphAndGainTypes<TYPE_TRAITS COMMA Km1GainTypes>);                                \
  template class C(GraphAndGainTypes<TYPE_TRAITS COMMA CutGainTypes>);                                \
  ENABLE_SOED(template class C(GraphAndGainTypes<TYPE_TRAITS COMMA SoedGainTypes>);)                  \
  ENABLE_STEINER_TREE(template class C(GraphAndGainTypes<TYPE_TRAITS COMMA SteinerTreeGainTypes>);)

#define _INSTANTIATE_CLASS_MACRO_FOR_GRAPH_COMBINATIONS(C, TYPE_TRAITS)                           \
  template class C(GraphAndGainTypes<TYPE_TRAITS COMMA CutGainForGraphsTypes>);                           \
  ENABLE_STEINER_TREE(template class C(GraphAndGainTypes<TYPE_TRAITS COMMA SteinerTreeForGraphsTypes>);)


#define INSTANTIATE_CLASS_WITH_VALID_TRAITS(C)                                                                    \
  _INSTANTIATE_CLASS_MACRO_FOR_HYPERGRAPH_COMBINATIONS(C, StaticHypergraphTypeTraits)                             \
  ENABLE_GRAPHS(_INSTANTIATE_CLASS_MACRO_FOR_GRAPH_COMBINATIONS(C, StaticGraphTypeTraits))                        \
  ENABLE_HIGHEST_QUALITY(_INSTANTIATE_CLASS_MACRO_FOR_HYPERGRAPH_COMBINATIONS(C, DynamicHypergraphTypeTraits))    \
  ENABLE_HIGHEST_QUALITY_FOR_GRAPHS(_INSTANTIATE_CLASS_MACRO_FOR_GRAPH_COMBINATIONS(C, DynamicGraphTypeTraits))   \
  ENABLE_LARGE_K(_INSTANTIATE_CLASS_MACRO_FOR_HYPERGRAPH_COMBINATIONS(C, LargeKHypergraphTypeTraits))


// functionality for retrieving combined policy of partition type and gain
#define _RETURN_COMBINED_POLICY(TYPE_TRAITS, GAIN_TYPES) {      \
  static GraphAndGainTypes<TYPE_TRAITS, GAIN_TYPES> traits;        \
  return traits;                                                \
}

#define SWITCH_HYPERGRAPH_GAIN_TYPES(TYPE_TRAITS, gain_policy) {                              \
  switch ( gain_policy ) {                                                                    \
    case GainPolicy::km1: _RETURN_COMBINED_POLICY(TYPE_TRAITS, Km1GainTypes)                  \
    case GainPolicy::cut: _RETURN_COMBINED_POLICY(TYPE_TRAITS, CutGainTypes)                  \
    case GainPolicy::soed: ENABLE_SOED(_RETURN_COMBINED_POLICY(TYPE_TRAITS, SoedGainTypes))   \
    case GainPolicy::steiner_tree:                                                            \
      ENABLE_STEINER_TREE(_RETURN_COMBINED_POLICY(TYPE_TRAITS, SteinerTreeGainTypes))         \
    default: {                                                                                \
      throw InvalidParameterException("Invalid gain policy type");                            \
    }                                                                                         \
  }                                                                                           \
}

#define SWITCH_GRAPH_GAIN_TYPES(TYPE_TRAITS, gain_policy) {                                                   \
  switch ( gain_policy ) {                                                                                    \
    case GainPolicy::cut_for_graphs:                                                                          \
      ENABLE_GRAPHS(_RETURN_COMBINED_POLICY(TYPE_TRAITS, CutGainForGraphsTypes))                              \
    case GainPolicy::steiner_tree_for_graphs:                                                                 \
      ENABLE_STEINER_TREE(ENABLE_GRAPHS(_RETURN_COMBINED_POLICY(TYPE_TRAITS, SteinerTreeForGraphsTypes)))     \
    default: {                                                                                                \
      throw InvalidParameterException("Invalid gain policy type");                                            \
    }                                                                                                         \
  }                                                                                                           \
}

}  // namespace mt_kahypar
