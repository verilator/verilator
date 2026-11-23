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

#include "mt-kahypar/definitions.h"
#include "mt-kahypar/partition/context_enum_classes.h"
#include "mt-kahypar/datastructures/hypergraph_common.h"
#include "mt-kahypar/macros.h"
#include "mt-kahypar/utils/exception.h"

namespace mt_kahypar {


struct BipartitioningPolicy {
  static bool useCutNetSplitting(const GainPolicy policy) {
    switch(policy) {
      case GainPolicy::cut: return false;
      case GainPolicy::km1: return true;
      case GainPolicy::soed: return true;
      case GainPolicy::steiner_tree: return true;
      case GainPolicy::cut_for_graphs: return false;
      case GainPolicy::steiner_tree_for_graphs: return false;
      case GainPolicy::none: throw InvalidParameterException("Gain policy is unknown");
    }
    throw InvalidParameterException("Gain policy is unknown");
    return false;
  }

  static HyperedgeWeight nonCutEdgeMultiplier(const GainPolicy policy) {
    switch(policy) {
      case GainPolicy::cut: return 1;
      case GainPolicy::km1: return 1;
      case GainPolicy::soed: return 2;
      case GainPolicy::steiner_tree: return 1;
      case GainPolicy::cut_for_graphs: return 1;
      case GainPolicy::steiner_tree_for_graphs: return 1;
      case GainPolicy::none: throw InvalidParameterException("Gain policy is unknown");
    }
    throw InvalidParameterException("Gain policy is unknown");
    return 0;
  }
};


}  // namespace mt_kahypar
