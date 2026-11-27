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

#include "register_policies.h"

#include "kahypar-resources/meta/registrar.h"

#include "mt-kahypar/definitions.h"
#include "mt-kahypar/partition/coarsening/policies/rating_acceptance_policy.h"
#include "mt-kahypar/partition/coarsening/policies/rating_heavy_node_penalty_policy.h"
#include "mt-kahypar/partition/coarsening/policies/rating_score_policy.h"
#include "mt-kahypar/partition/refinement/gains/gain_definitions.h"
#include "mt-kahypar/partition/context_enum_classes.h"
#include "mt-kahypar/partition/thread_safe_policy_registry.h"

#define REGISTER_POLICY(policy, id, policy_class)                                                    \
  static kahypar::meta::Registrar<ThreadSafePolicyRegistry<policy> > register_ ## policy_class( \
    id, new policy_class())

namespace mt_kahypar {

void register_policies() {
  // //////////////////////////////////////////////////////////////////////////////
  //                            Hypergraph Type Traits
  // //////////////////////////////////////////////////////////////////////////////
  #ifdef KAHYPAR_ENABLE_GRAPH_PARTITIONING_FEATURES
  REGISTER_POLICY(mt_kahypar_partition_type_t, MULTILEVEL_GRAPH_PARTITIONING,
                  StaticGraphTypeTraits);
  #endif
  REGISTER_POLICY(mt_kahypar_partition_type_t, MULTILEVEL_HYPERGRAPH_PARTITIONING,
                  StaticHypergraphTypeTraits);
  #ifdef KAHYPAR_ENABLE_LARGE_K_PARTITIONING_FEATURES
  REGISTER_POLICY(mt_kahypar_partition_type_t, LARGE_K_PARTITIONING,
                  LargeKHypergraphTypeTraits);
  #endif
  #ifdef KAHYPAR_ENABLE_HIGHEST_QUALITY_FEATURES
  #ifdef KAHYPAR_ENABLE_GRAPH_PARTITIONING_FEATURES
  REGISTER_POLICY(mt_kahypar_partition_type_t, N_LEVEL_GRAPH_PARTITIONING,
                  DynamicGraphTypeTraits);
  #endif
  REGISTER_POLICY(mt_kahypar_partition_type_t, N_LEVEL_HYPERGRAPH_PARTITIONING,
                  DynamicHypergraphTypeTraits);
  #endif

  // //////////////////////////////////////////////////////////////////////////////
  //                       Coarsening / Rating Policies
  // //////////////////////////////////////////////////////////////////////////////
  REGISTER_POLICY(RatingFunction, RatingFunction::heavy_edge,
                  HeavyEdgeScore);
  #ifdef KAHYPAR_ENABLE_EXPERIMENTAL_FEATURES
  REGISTER_POLICY(RatingFunction, RatingFunction::sameness,
                  SamenessScore);
  #endif

  REGISTER_POLICY(HeavyNodePenaltyPolicy, HeavyNodePenaltyPolicy::no_penalty,
                  NoWeightPenalty);
  #ifdef KAHYPAR_ENABLE_EXPERIMENTAL_FEATURES
  REGISTER_POLICY(HeavyNodePenaltyPolicy, HeavyNodePenaltyPolicy::multiplicative_penalty,
                  MultiplicativePenalty);
  REGISTER_POLICY(HeavyNodePenaltyPolicy, HeavyNodePenaltyPolicy::additive,
                  AdditivePenalty);
  #endif

  REGISTER_POLICY(AcceptancePolicy, AcceptancePolicy::best_prefer_unmatched,
                  BestRatingPreferringUnmatched);
  #ifdef KAHYPAR_ENABLE_EXPERIMENTAL_FEATURES
  REGISTER_POLICY(AcceptancePolicy, AcceptancePolicy::best,
                  BestRatingWithTieBreaking);
  #endif

  // //////////////////////////////////////////////////////////////////////////////
  //                            Gain Type Policies
  // //////////////////////////////////////////////////////////////////////////////
  REGISTER_POLICY(GainPolicy, GainPolicy::km1, Km1GainTypes);
  REGISTER_POLICY(GainPolicy, GainPolicy::cut, CutGainTypes);
  #ifdef KAHYPAR_ENABLE_SOED_METRIC
  REGISTER_POLICY(GainPolicy, GainPolicy::soed, SoedGainTypes);
  #endif
  #ifdef KAHYPAR_ENABLE_STEINER_TREE_METRIC
  REGISTER_POLICY(GainPolicy, GainPolicy::steiner_tree, SteinerTreeGainTypes);
  #endif
  #ifdef KAHYPAR_ENABLE_GRAPH_PARTITIONING_FEATURES
  REGISTER_POLICY(GainPolicy, GainPolicy::cut_for_graphs, CutGainForGraphsTypes);
  #ifdef KAHYPAR_ENABLE_STEINER_TREE_METRIC
  REGISTER_POLICY(GainPolicy, GainPolicy::steiner_tree_for_graphs, SteinerTreeForGraphsTypes);
  #endif
  #endif
}

}  // namespace mt_kahypar
