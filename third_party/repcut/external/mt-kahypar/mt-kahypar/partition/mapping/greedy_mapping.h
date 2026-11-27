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
#include "mt-kahypar/datastructures/partitioned_graph.h"
#include "mt-kahypar/partition/mapping/target_graph.h"
#include "mt-kahypar/partition/context.h"

namespace mt_kahypar {

template<typename CommunicationHypergraph>
class GreedyMapping {

  using PartitionedGraph = ds::PartitionedGraph<ds::StaticGraph>;

 public:
  /** This function implements the greedy mapping algorithm of Glantz et. al.:
    * Glantz, Roland, Hening Meyerhenke, and Alexander Noe.
    * "Algorithms for mapping parallel processes onto grid and torus architectures."
    * 2015 23rd Euromicro International Conference on Parallel, Distributed, and Network-Based Processing. IEEE, 2015.
    *
    * The algorithm chooses a seed node and assigns it to processor with the lowest communication
    * volume. In each step, the algorithm assigns the node of the communication hypergraph with
    * the strongest connection to the partial assignment to the processor that results in the
    * least increasing of the steiner tree metric.
    */
  static void mapToTargetGraph(CommunicationHypergraph& communication_hg,
                                const TargetGraph& target_graph,
                                const Context& context);

 private:
  GreedyMapping() { }
};

}  // namespace kahypar
