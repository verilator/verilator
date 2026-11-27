/*******************************************************************************
 * MIT License
 *
 * This file is part of Mt-KaHyPar.
 *
 * Copyright (C) 2019 Lars Gottesbüren <lars.gottesbueren@kit.edu>
 * Copyright (C) 2019 Tobias Heuer <tobias.heuer@kit.edu>
 * Copyright (C) 2022 Nikolai Maas <nikolai.maas@student.kit.edu>
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

#include <tbb/enumerable_thread_specific.h>

#include "mt-kahypar/datastructures/dynamic_graph.h"
#include "mt-kahypar/parallel/atomic_wrapper.h"


namespace mt_kahypar {
namespace ds {

class DynamicGraphFactory {
  using EdgeVector = parallel::scalable_vector<std::pair<HypernodeID, HypernodeID>>;
  using HyperedgeVector = parallel::scalable_vector<parallel::scalable_vector<HypernodeID>>;
  using Counter = parallel::scalable_vector<size_t>;
  using AtomicCounter = parallel::scalable_vector<parallel::IntegralAtomicWrapper<size_t>>;
  using ThreadLocalCounter = tbb::enumerable_thread_specific<Counter>;

 public:
  static DynamicGraph construct(const HypernodeID num_nodes,
                               const HyperedgeID num_edges,
                               const HyperedgeVector& edge_vector,
                               const HyperedgeWeight* edge_weight = nullptr,
                               const HypernodeWeight* node_weight = nullptr,
                               const bool stable_construction_of_incident_edges = false);

  // ! Provides a more performant construction method by using continuous space for the edges
  // ! (instead of a separate vec per edge).
  // ! No backwards edges allowed, i.e. each edge is unique
  static DynamicGraph construct_from_graph_edges(const HypernodeID num_nodes,
                                                const HyperedgeID num_edges,
                                                const EdgeVector& edge_vector,
                                                const HyperedgeWeight* edge_weight = nullptr,
                                                const HypernodeWeight* node_weight = nullptr,
                                                const bool stable_construction_of_incident_edges = false);

  static std::pair<DynamicGraph, parallel::scalable_vector<HypernodeID> > compactify(const DynamicGraph&);

 private:
  DynamicGraphFactory() { }
};

} // namespace ds
} // namespace mt_kahypar
