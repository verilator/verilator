/*******************************************************************************
 * MIT License
 *
 * This file is part of Mt-KaHyPar.
 *
 * Copyright (C) 2020 Lars Gottesbüren <lars.gottesbueren@kit.edu>
 * Copyright (C) 2020 Tobias Heuer <tobias.heuer@kit.edu>
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

#include "mt-kahypar/datastructures/hypergraph_common.h"

namespace mt_kahypar {

// adaptive random walk stopping rule from KaHyPar
class StopRule {
public:
  StopRule(HypernodeID numNodes) : beta(std::log(numNodes)) { }

  bool searchShouldStop() {
    return (numSteps > beta) && (Mk == 0 || numSteps >= ( variance / (Mk*Mk) ) * stopFactor );
  }

  void update(Gain gain) {
    ++numSteps;
    if (numSteps == 1) {
      Mk = gain;
      MkPrevious = gain;
      SkPrevious = 0.0;
      variance = 0.0;
    } else {
      Mk = MkPrevious + (gain - MkPrevious) / numSteps;
      Sk = SkPrevious + (gain - MkPrevious) * (gain - Mk);
      variance = Sk / (numSteps - 1.0);

      MkPrevious = Mk;
      SkPrevious = Sk;
    }
  }

  void reset() {
    numSteps = 0;
    variance = 0.0;
  }

private:
  size_t numSteps = 0;
  double variance = 0.0, Mk = 0.0, MkPrevious = 0.0, Sk = 0.0, SkPrevious = 0.0;
  const double alpha = 1.0;   // make parameter if it doesn't work well
  const double stopFactor = (alpha / 2.0) - 0.25;
  double beta;
};
}