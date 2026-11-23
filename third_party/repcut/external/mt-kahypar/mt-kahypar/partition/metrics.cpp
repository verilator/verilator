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

#include "mt-kahypar/partition/metrics.h"

#include <cmath>
#include <algorithm>

#include "mt-kahypar/definitions.h"
#include "mt-kahypar/partition/mapping/target_graph.h"
#include "mt-kahypar/utils/exception.h"

namespace mt_kahypar {

int numViolations(const BalanceMetrics& imbalance) {
  return (imbalance.violates_balance ? 1 : 0) + (imbalance.violates_non_empty_blocks ? 1 : 0);
}

bool BalanceMetrics::isValidPartition() const {
  return numViolations(*this) == 0;
}

bool BalanceMetrics::isBetter(const BalanceMetrics& other) const {
  return numViolations(*this) < numViolations(other) ||
    (numViolations(*this) == numViolations(other) && imbalance_value < other.imbalance_value);
}

bool BalanceMetrics::isEqual(const BalanceMetrics& other) const {
  return numViolations(*this) == numViolations(other) && imbalance_value == other.imbalance_value;
}

bool BalanceMetrics::operator==(const BalanceMetrics& other) const {
  return imbalance_value == other.imbalance_value &&
    violates_balance == other.violates_balance &&
    violates_non_empty_blocks == other.violates_non_empty_blocks;
}

bool Metrics::isBetter(const Metrics& other) const {
  if (numViolations(imbalance) < numViolations(other.imbalance)) {
    return true;
  } else if (numViolations(imbalance) == numViolations(other.imbalance)) {
    bool improvesBalanceViolation = other.imbalance.violates_balance && imbalance.isBetter(other.imbalance);
    bool worsensBalanceViolation = imbalance.violates_balance && other.imbalance.isBetter(imbalance);
    return improvesBalanceViolation
           || (!worsensBalanceViolation && quality < other.quality)
           || (!worsensBalanceViolation && quality == other.quality
                && imbalance.imbalance_value < other.imbalance.imbalance_value);
  } else {
    return false;
  }
}

bool Metrics::isEqual(const Metrics& other) const {
  return quality == other.quality && imbalance.isEqual(other.imbalance);
}

std::ostream& operator<< (std::ostream& os, const BalanceMetrics& imbalance) {
  return os << "[imb: " << imbalance.imbalance_value  << "; " << (imbalance.isValidPartition() ? "valid" : "invalid") << "]";
}


namespace metrics {

namespace {

template<typename PartitionedHypergraph, Objective objective>
struct ObjectiveFunction { };

template<typename PartitionedHypergraph>
struct ObjectiveFunction<PartitionedHypergraph, Objective::cut> {
  HyperedgeWeight operator()(const PartitionedHypergraph& phg, const HyperedgeID& he) const {
    return phg.connectivity(he) > 1 ? phg.edgeWeight(he) : 0;
  }
};

template<typename PartitionedHypergraph>
struct ObjectiveFunction<PartitionedHypergraph, Objective::km1> {
  HyperedgeWeight operator()(const PartitionedHypergraph& phg, const HyperedgeID& he) const {
    return std::max(phg.connectivity(he) - 1, 0) * phg.edgeWeight(he);
  }
};

template<typename PartitionedHypergraph>
struct ObjectiveFunction<PartitionedHypergraph, Objective::soed> {
  HyperedgeWeight operator()(const PartitionedHypergraph& phg, const HyperedgeID& he) const {
    const PartitionID connectivity = phg.connectivity(he);
    return connectivity > 1 ? connectivity * phg.edgeWeight(he) : 0;
  }
};

template<typename PartitionedHypergraph>
struct ObjectiveFunction<PartitionedHypergraph, Objective::steiner_tree> {
  HyperedgeWeight operator()(const PartitionedHypergraph& phg, const HyperedgeID& he) const {
    ASSERT(phg.hasTargetGraph());
    const TargetGraph* target_graph = phg.targetGraph();
    const HyperedgeWeight distance = target_graph->distance(phg.shallowCopyOfConnectivitySet(he));
    return distance * phg.edgeWeight(he);
  }
};

template<Objective objective, typename PartitionedHypergraph>
HyperedgeWeight compute_objective_parallel(const PartitionedHypergraph& phg) {
  ObjectiveFunction<PartitionedHypergraph, objective> func;
  tbb::enumerable_thread_specific<HyperedgeWeight> obj(0);
  phg.doParallelForAllEdges([&](const HyperedgeID he) {
    obj.local() += func(phg, he);
  });
  return obj.combine(std::plus<>()) / (PartitionedHypergraph::is_graph ? 2 : 1);
}

template<Objective objective, typename PartitionedHypergraph>
HyperedgeWeight compute_objective_sequentially(const PartitionedHypergraph& phg) {
  ObjectiveFunction<PartitionedHypergraph, objective> func;
  HyperedgeWeight obj = 0;
  for (const HyperedgeID& he : phg.edges()) {
    obj += func(phg, he);
  }
  return obj / (PartitionedHypergraph::is_graph ? 2 : 1);
}

template<Objective objective, typename PartitionedHypergraph>
HyperedgeWeight contribution(const PartitionedHypergraph& phg, const HyperedgeID he) {
  ObjectiveFunction<PartitionedHypergraph, objective> func;
  return func(phg, he);
}

}

template<typename PartitionedHypergraph>
HyperedgeWeight quality(const PartitionedHypergraph& hg,
                        const Context& context,
                        const bool parallel) {
  return quality(hg, context.partition.objective, parallel);
}

template<typename PartitionedHypergraph>
HyperedgeWeight quality(const PartitionedHypergraph& hg,
                        const Objective objective,
                        const bool parallel) {
  switch (objective) {
    case Objective::cut:
      return parallel ? compute_objective_parallel<Objective::cut>(hg) :
        compute_objective_sequentially<Objective::cut>(hg);
    case Objective::km1:
      return parallel ? compute_objective_parallel<Objective::km1>(hg) :
        compute_objective_sequentially<Objective::km1>(hg);
    case Objective::soed:
      return parallel ? compute_objective_parallel<Objective::soed>(hg) :
        compute_objective_sequentially<Objective::soed>(hg);
    case Objective::steiner_tree:
      return parallel ? compute_objective_parallel<Objective::steiner_tree>(hg) :
        compute_objective_sequentially<Objective::steiner_tree>(hg);
    default: throw InvalidParameterException("Unknown Objective");
  }
  return 0;
}

template<typename PartitionedHypergraph>
HyperedgeWeight contribution(const PartitionedHypergraph& hg,
                             const HyperedgeID he,
                             const Objective objective) {
  switch (objective) {
    case Objective::cut: return contribution<Objective::soed>(hg, he);
    case Objective::km1: return contribution<Objective::km1>(hg, he);
    case Objective::soed: return contribution<Objective::soed>(hg, he);
    case Objective::steiner_tree: return contribution<Objective::steiner_tree>(hg, he);
    default: throw InvalidParameterException("Unknown Objective");
  }
  return 0;
}

template<typename PartitionedHypergraph>
bool isValidPartition(const PartitionedHypergraph& phg, const Context& context) {
  BalanceMetrics imbalance_metrics = imbalance(phg, context);
  return imbalance_metrics.isValidPartition();
}

template<typename PartitionedHypergraph, typename Func>
BalanceMetrics imbalance_impl(const PartitionedHypergraph& hypergraph,
                              const Context& context,
                              Func&& part_weight_fn,
                              const std::vector<HypernodeWeight>& max_part_weights) {
  ASSERT(context.partition.perfect_balance_part_weights.size() == (size_t)context.partition.k);

  size_t num_empty_parts = 0;
  HypernodeWeight min_empty_part_weight = std::numeric_limits<HypernodeWeight>::max();
  double max_balance = 0.0;
  bool violates_balance = false;
  for (PartitionID i = 0; i < context.partition.k; ++i) {
    const HypernodeWeight part_weight = part_weight_fn(i);
    const double balance_i = (part_weight
            / static_cast<double>(context.partition.perfect_balance_part_weights[i]));
    max_balance = std::max(max_balance, balance_i);
    if (part_weight > max_part_weights[i]) {
      violates_balance = true;
    }
    if (part_weight == 0) {
      num_empty_parts++;
      min_empty_part_weight = std::min(min_empty_part_weight, max_part_weights[i]);
    }
  }

  bool too_many_empty_parts = num_empty_parts > hypergraph.numRemovedHypernodes();
  // use conservative estimate
  bool too_small_empty_parts = num_empty_parts > 0
    && min_empty_part_weight < hypergraph.maxWeightOfRemovedDegreeZeroNode();
  return BalanceMetrics{max_balance - 1.0, violates_balance,
    !context.partition.allow_empty_blocks && (too_many_empty_parts || too_small_empty_parts)};
}

template<typename PartitionedHypergraph>
BalanceMetrics imbalance(const PartitionedHypergraph& hypergraph, const Context& context) {
  return imbalance_impl(
    hypergraph,
    context,
    [&](PartitionID i) { return hypergraph.partWeight(i); },
    context.partition.max_part_weights);
}

template<typename PartitionedHypergraph>
BalanceMetrics imbalance(const PartitionedHypergraph& hypergraph,
                         const Context& context,
                         const std::vector<HypernodeWeight>& max_part_weights) {
  return imbalance_impl(
    hypergraph,
    context,
    [&](PartitionID i) { return hypergraph.partWeight(i); },
    max_part_weights);
}

template<typename PartitionedHypergraph>
BalanceMetrics imbalance(const PartitionedHypergraph& hypergraph,
                         const Context& context,
                         const vec<HypernodeWeight>& part_weights,
                         const std::vector<HypernodeWeight>& max_part_weights) {
  ASSERT(part_weights.size() == (size_t)context.partition.k);
  return imbalance_impl(
    hypergraph,
    context,
    [&](PartitionID i) { return part_weights[i]; },
    max_part_weights);
}

template<typename PartitionedHypergraph>
double approximationFactorForProcessMapping(const PartitionedHypergraph& hypergraph, const Context& context) {
  if ( !PartitionedHypergraph::is_graph ) {
    tbb::enumerable_thread_specific<HyperedgeWeight> approx_factor(0);
    hypergraph.doParallelForAllEdges([&](const HyperedgeID& he) {
      const size_t connectivity = hypergraph.connectivity(he);
      approx_factor.local() += connectivity <= context.mapping.max_steiner_tree_size ? 1 : 2;
    });
    return static_cast<double>(approx_factor.combine(std::plus<>())) / hypergraph.initialNumEdges();
  } else {
    return 1.0;
  }
}

namespace {
#define OBJECTIVE_1(X) HyperedgeWeight quality(const X& hg, const Context& context, const bool parallel)
#define OBJECTIVE_2(X) HyperedgeWeight quality(const X& hg, const Objective objective, const bool parallel)
#define CONTRIBUTION(X) HyperedgeWeight contribution(const X& hg, const HyperedgeID he, const Objective objective)
#define IS_VALID_PARTITION(X) bool isValidPartition(const X& phg, const Context& context)
#define IMBALANCE_1(X) BalanceMetrics imbalance(const X& hypergraph, const Context& context)
#define IMBALANCE_2(X) BalanceMetrics imbalance(const X& hypergraph, \
                                                const Context& context, \
                                                const std::vector<HypernodeWeight>& max_part_weights)
#define IMBALANCE_3(X) BalanceMetrics imbalance(const X& hypergraph, \
                                                const Context& context, \
                                                const vec<HypernodeWeight>& part_weights, \
                                                const std::vector<HypernodeWeight>& max_part_weights)
#define APPROX_FACTOR(X) double approximationFactorForProcessMapping(const X& hypergraph, const Context& context)
}

INSTANTIATE_FUNC_WITH_PARTITIONED_HG(OBJECTIVE_1)
INSTANTIATE_FUNC_WITH_PARTITIONED_HG(OBJECTIVE_2)
INSTANTIATE_FUNC_WITH_PARTITIONED_HG(CONTRIBUTION)
INSTANTIATE_FUNC_WITH_PARTITIONED_HG(IS_VALID_PARTITION)
INSTANTIATE_FUNC_WITH_PARTITIONED_HG(IMBALANCE_1)
INSTANTIATE_FUNC_WITH_PARTITIONED_HG(IMBALANCE_2)
INSTANTIATE_FUNC_WITH_PARTITIONED_HG(IMBALANCE_3)
INSTANTIATE_FUNC_WITH_PARTITIONED_HG(APPROX_FACTOR)

} // namespace metrics

} // namespace mt_kahypar