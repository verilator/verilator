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

#include "mt-kahypar/partition/context.h"

namespace mt_kahypar {

// Forward Declaration
class TargetGraph;

template<typename TypeTraits>
class Multilevel {

  using Hypergraph = typename TypeTraits::Hypergraph;
  using PartitionedHypergraph = typename TypeTraits::PartitionedHypergraph;

 public:
  // ! Partitions a hypergraph using the multilevel paradigm.
  static PartitionedHypergraph partition(Hypergraph& hypergraph,
                                         const Context& context,
                                         const TargetGraph* target_graph = nullptr);

  // ! Partitions a hypergraph using the multilevel paradigm.
  static void partition(PartitionedHypergraph& partitioned_hg,
                        const Context& context,
                        const TargetGraph* target_graph = nullptr);

  // ! Improves an existing partition using the iterated multilevel cycle technique
  // ! (also called V-cycle).
  static void partitionVCycle(Hypergraph& hypergraph,
                              PartitionedHypergraph& partitioned_hg,
                              const Context& context,
                              const TargetGraph* target_graph = nullptr);
};

}  // namespace mt_kahypar
