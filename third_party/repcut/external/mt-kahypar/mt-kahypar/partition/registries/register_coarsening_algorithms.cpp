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

#include "register_coarsening_algorithms.h"

#include "kahypar-resources/meta/registrar.h"
#include "kahypar-resources/meta/static_multi_dispatch_factory.h"
#include "kahypar-resources/meta/typelist.h"

#include "mt-kahypar/definitions.h"
#ifdef KAHYPAR_ENABLE_HIGHEST_QUALITY_FEATURES
#include "mt-kahypar/partition/coarsening/nlevel/nlevel_coarsener.h"
#endif
#include "mt-kahypar/partition/coarsening/multilevel/multilevel_coarsener.h"
#include "mt-kahypar/partition/coarsening/multilevel/deterministic_multilevel_coarsener.h"
#include "mt-kahypar/partition/coarsening/do_nothing_coarsener.h"
#include "mt-kahypar/partition/coarsening/policies/rating_acceptance_policy.h"
#include "mt-kahypar/partition/coarsening/policies/rating_heavy_node_penalty_policy.h"
#include "mt-kahypar/partition/context.h"
#include "mt-kahypar/partition/factories.h"
#include "mt-kahypar/partition/thread_safe_policy_registry.h"


namespace mt_kahypar {
using MultilevelCoarsenerDispatcher = kahypar::meta::StaticMultiDispatchFactory<MultilevelCoarsener,
                                                                                ICoarsener,
                                                                                kahypar::meta::Typelist<TypeTraitsList,
                                                                                                        RatingScorePolicies,
                                                                                                        HeavyNodePenaltyPolicies,
                                                                                                        AcceptancePolicies> >;

using DeterministicCoarsenerDispatcher = kahypar::meta::StaticMultiDispatchFactory<DeterministicMultilevelCoarsener,
                                                                                   ICoarsener,
                                                                                   kahypar::meta::Typelist<TypeTraitsList>>;

#ifdef KAHYPAR_ENABLE_HIGHEST_QUALITY_FEATURES
using NLevelCoarsenerDispatcher = kahypar::meta::StaticMultiDispatchFactory<NLevelCoarsener,
                                                                            ICoarsener,
                                                                            kahypar::meta::Typelist<TypeTraitsList,
                                                                                                    RatingScorePolicies,
                                                                                                    HeavyNodePenaltyPolicies,
                                                                                                    AcceptancePolicies> >;
#endif

using DoNothingCoarsenerDispatcher = kahypar::meta::StaticMultiDispatchFactory<DoNothingCoarsener,
                                                                               ICoarsener,
                                                                               kahypar::meta::Typelist<TypeTraitsList>>;

#define REGISTER_DISPATCHED_COARSENER(id, dispatcher, ...)                                                    \
  kahypar::meta::Registrar<CoarsenerFactory> register_ ## dispatcher(                                         \
    id,                                                                                                       \
    [](mt_kahypar_hypergraph_t hypergraph, const Context& context, uncoarsening_data_t* uncoarseningData) {   \
    return dispatcher::create(                                                                                \
      std::forward_as_tuple(hypergraph, context, uncoarseningData),                                           \
      __VA_ARGS__                                                                                             \
      );                                                                                                      \
  })


void register_coarsening_algorithms() {
  REGISTER_DISPATCHED_COARSENER(CoarseningAlgorithm::multilevel_coarsener,
                                MultilevelCoarsenerDispatcher,
                                ThreadSafePolicyRegistry<mt_kahypar_partition_type_t>::getInstance().getPolicy(
                                  context.partition.partition_type),
                                ThreadSafePolicyRegistry<RatingFunction>::getInstance().getPolicy(
                                  context.coarsening.rating.rating_function),
                                ThreadSafePolicyRegistry<HeavyNodePenaltyPolicy>::getInstance().getPolicy(
                                  context.coarsening.rating.heavy_node_penalty_policy),
                                ThreadSafePolicyRegistry<AcceptancePolicy>::getInstance().getPolicy(
                                  context.coarsening.rating.acceptance_policy));

  #ifdef KAHYPAR_ENABLE_HIGHEST_QUALITY_FEATURES
  REGISTER_DISPATCHED_COARSENER(CoarseningAlgorithm::nlevel_coarsener,
                                NLevelCoarsenerDispatcher,
                                ThreadSafePolicyRegistry<mt_kahypar_partition_type_t>::getInstance().getPolicy(
                                  context.partition.partition_type),
                                ThreadSafePolicyRegistry<RatingFunction>::getInstance().getPolicy(
                                  context.coarsening.rating.rating_function),
                                ThreadSafePolicyRegistry<HeavyNodePenaltyPolicy>::getInstance().getPolicy(
                                  context.coarsening.rating.heavy_node_penalty_policy),
                                ThreadSafePolicyRegistry<AcceptancePolicy>::getInstance().getPolicy(
                                  context.coarsening.rating.acceptance_policy));
  #endif

  REGISTER_DISPATCHED_COARSENER(CoarseningAlgorithm::deterministic_multilevel_coarsener,
                                DeterministicCoarsenerDispatcher,
                                ThreadSafePolicyRegistry<mt_kahypar_partition_type_t>::getInstance().getPolicy(
                                  context.partition.partition_type));

  REGISTER_DISPATCHED_COARSENER(CoarseningAlgorithm::do_nothing_coarsener,
                                DoNothingCoarsenerDispatcher,
                                ThreadSafePolicyRegistry<mt_kahypar_partition_type_t>::getInstance().getPolicy(
                                  context.partition.partition_type));

}

}  // namespace mt_kahypar
