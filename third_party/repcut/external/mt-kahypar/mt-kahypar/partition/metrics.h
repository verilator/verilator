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

#pragma once

#include <iostream>
#include <limits>

#include "mt-kahypar/partition/context.h"

namespace mt_kahypar {

struct BalanceMetrics {
  double imbalance_value = std::numeric_limits<double>::max();
  bool violates_balance = true;
  bool violates_non_empty_blocks = true;

  bool isValidPartition() const;

  bool isBetter(const BalanceMetrics& other) const;

  bool isEqual(const BalanceMetrics& other) const;

  bool operator==(const BalanceMetrics& other) const;
};

std::ostream& operator<< (std::ostream& os, const BalanceMetrics& imbalance);

struct Metrics {
  HyperedgeWeight quality;
  BalanceMetrics imbalance;

  bool isBetter(const Metrics& other) const;

  bool isEqual(const Metrics& other) const;
};

namespace metrics {

// ! Computes for the given partitioned hypergraph the corresponding objective function
template<typename PartitionedHypergraph>
HyperedgeWeight quality(const PartitionedHypergraph& hg,
                        const Context& context,
                        const bool parallel = true);
template<typename PartitionedHypergraph>
HyperedgeWeight quality(const PartitionedHypergraph& hg,
                        const Objective objective,
                        const bool parallel = true);

// ! Computes for a hyperedge the contribution to the corresponding objective function
template<typename PartitionedHypergraph>
HyperedgeWeight contribution(const PartitionedHypergraph& hg,
                             const HyperedgeID he,
                             const Objective objective);

template<typename PartitionedHypergraph>
bool isValidPartition(const PartitionedHypergraph& phg, const Context& context);

template<typename PartitionedHypergraph>
BalanceMetrics imbalance(const PartitionedHypergraph& hypergraph, const Context& context);

template<typename PartitionedHypergraph>
BalanceMetrics imbalance(const PartitionedHypergraph& hypergraph,
                         const Context& context,
                         const std::vector<HypernodeWeight>& max_part_weights);

template<typename PartitionedHypergraph>
BalanceMetrics imbalance(const PartitionedHypergraph& hypergraph,
                         const Context& context,
                         const vec<HypernodeWeight>& part_weights,
                         const std::vector<HypernodeWeight>& max_part_weights);

template<typename PartitionedHypergraph>
BalanceMetrics onlyImbalance(const PartitionedHypergraph& hypergraph, const Context& context) {
  // cheaper variant that does not consider any constraints other than balance
  double max_balance = 0.0;
  bool violates_balance = false;
  for (PartitionID i = 0; i < context.partition.k; ++i) {
    const HypernodeWeight part_weight = hypergraph.partWeight(i);
    const double balance_i = (part_weight
            / static_cast<double>(context.partition.perfect_balance_part_weights[i]));
    max_balance = std::max(max_balance, balance_i);
    if (part_weight > context.partition.max_part_weights[i]) {
      violates_balance = true;
    }
  }
  return BalanceMetrics{max_balance - 1.0, violates_balance, false};
}

template<typename PartitionedHypergraph>
double approximationFactorForProcessMapping(const PartitionedHypergraph& hypergraph, const Context& context);

}  // namespace metrics
}  // namespace mt_kahypar
