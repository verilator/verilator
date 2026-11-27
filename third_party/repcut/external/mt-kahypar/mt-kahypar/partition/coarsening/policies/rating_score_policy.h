/*******************************************************************************
 * MIT License
 *
 * This file is part of KaHyPar.
 *
 * Copyright (C) 2017 Sebastian Schlag <sebastian.schlag@kit.edu>
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

#include "kahypar-resources/meta/policy_registry.h"
#include "kahypar-resources/meta/typelist.h"

#include "mt-kahypar/datastructures/hypergraph_common.h"
#include "mt-kahypar/macros.h"

namespace mt_kahypar {
class HeavyEdgeScore final : public kahypar::meta::PolicyBase {
 public:
  MT_KAHYPAR_ATTRIBUTE_ALWAYS_INLINE static RatingType score(const HyperedgeWeight edge_weight,
                                                             const HypernodeID edge_size) {
    return static_cast<RatingType>(edge_weight) / (edge_size - 1);
  }
};

#ifdef KAHYPAR_ENABLE_EXPERIMENTAL_FEATURES
class SamenessScore final : public kahypar::meta::PolicyBase {
 public:
  MT_KAHYPAR_ATTRIBUTE_ALWAYS_INLINE static RatingType score(const HyperedgeWeight edge_weight,
                                                             const HypernodeID) {
    return static_cast<RatingType>(edge_weight);
  }
};

using RatingScorePolicies = kahypar::meta::Typelist<HeavyEdgeScore, SamenessScore>;
#else
using RatingScorePolicies = kahypar::meta::Typelist<HeavyEdgeScore>;
#endif

}  // namespace mt_kahypar
