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

#include "mt-kahypar/macros.h"
#include "mt-kahypar/partition/context.h"

namespace mt_kahypar {

// Forward Declaration
class TargetGraph;

template<typename CommunicationHypergraph>
class KerninghanLin {

  static constexpr bool debug = false;

  // Number of rounds without improvements after which we
  // terminate the search (prevents oscillation).
  static constexpr size_t MAX_NUMBER_OF_FRUITLESS_ROUNDS = 2;

 public:
  // ! This function implements the Kerninghan-Lin algorithm to
  // ! improve a given mapping onto a target graph. The algorithm
  // ! performs in each step a swap operation of two nodes that results
  // ! in largest reduction of the objective function. After each node
  // ! node is swapped at most once, the algorithm rolls back to the
  // ! best seen solution. This is repeated several times until no
  // ! further improvements are possible.
  static void improve(CommunicationHypergraph& communication_hg,
                      const TargetGraph& target_graph,
                      const Context& context);

 private:
  KerninghanLin() { }
};

}  // namespace kahypar
