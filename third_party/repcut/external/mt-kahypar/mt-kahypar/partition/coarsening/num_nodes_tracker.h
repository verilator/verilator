/*******************************************************************************
 * MIT License
 *
 * This file is part of Mt-KaHyPar.
 *
 * Copyright (C) 2019 Lars Gottesbüren <lars.gottesbueren@kit.edu>
 * Copyright (C) 2019 Tobias Heuer <tobias.heuer@kit.edu>
 * Copyright (C) 2023 Nikolai Maas <nikolai.maas@kit.edu>
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

#include "repcut_serial.h"

#include <atomic>
#include <tbb/enumerable_thread_specific.h>

#include "mt-kahypar/definitions.h"
#include "mt-kahypar/parallel/atomic_wrapper.h"


namespace mt_kahypar {

class NumNodesTracker {
 public:
  explicit NumNodesTracker(): NumNodesTracker(0) { }

  explicit NumNodesTracker(HypernodeID initial_num_nodes):
    _initial_num_nodes(initial_num_nodes),
    _current_num_nodes(initial_num_nodes),
    _contracted_nodes(0),
    _num_nodes_update_threshold(0) { }

  HypernodeID currentNumNodes() const {
    return parallel::atomic_load(_current_num_nodes,
                                 std::memory_order_relaxed);
  }

  void updateCurrentNumNodes() {
    _current_num_nodes = _initial_num_nodes - _contracted_nodes.combine(std::plus<HypernodeID>());
    _num_nodes_update_threshold = tbb::enumerable_thread_specific<HypernodeID>(0);
  }

  HypernodeID finalNumNodes() {
    // update state / reset
    updateCurrentNumNodes();
    return _current_num_nodes;
  }

  void initialize(HypernodeID initial_num_nodes) {
    _initial_num_nodes = initial_num_nodes;
    _current_num_nodes = initial_num_nodes;
    _contracted_nodes = 0;
    _num_nodes_update_threshold = 0;
  }

  void subtractMultiple(HypernodeID num_contractions, size_t num_threads, HypernodeID hierarchy_contraction_limit) {
    HypernodeID local_contracted_nodes = repcut_serial::Ref(_contracted_nodes.local())
        .fetch_add(num_contractions, std::memory_order_relaxed);

    // To maintain the current number of nodes of the hypergraph each PE sums up
    // its number of contracted nodes locally. To compute the current number of
    // nodes, we have to sum up the number of contracted nodes of each PE. This
    // operation becomes more expensive the more PEs are participating in coarsening.
    // In order to prevent expensive updates of the current number of nodes, we
    // define a threshold which the local number of contracted nodes have to exceed
    // before the current PE updates the current number of nodes. This threshold is defined
    // by the distance to the current contraction limit divided by the number of PEs.
    // Once one PE exceeds this bound the first time it is not possible that the
    // contraction limit is reached, because otherwise an other PE would update
    // the global current number of nodes before. After update the threshold is
    // increased by the new difference (in number of nodes) to the contraction limit
    // divided by the number of PEs.
    if (local_contracted_nodes >= _num_nodes_update_threshold.local()) {
      HypernodeID updated_num_nodes = _initial_num_nodes;
      _contracted_nodes.combine_each([&](HypernodeID& val) {
        updated_num_nodes -= repcut_serial::Ref(val).load(std::memory_order_relaxed);
      });
      repcut_serial::Ref(_current_num_nodes).store(updated_num_nodes, std::memory_order_relaxed);

      const HypernodeID dist_to_contraction_limit =
        updated_num_nodes > hierarchy_contraction_limit ?
        updated_num_nodes - hierarchy_contraction_limit : 0;
      _num_nodes_update_threshold.local() += dist_to_contraction_limit / num_threads;
    }
  }

  void subtractNode(size_t num_threads, HypernodeID hierarchy_contraction_limit) {
    subtractMultiple(1, num_threads, hierarchy_contraction_limit);
  }

 private:
  HypernodeID _initial_num_nodes;
  HypernodeID _current_num_nodes;
  tbb::enumerable_thread_specific<HypernodeID> _contracted_nodes;
  tbb::enumerable_thread_specific<HypernodeID> _num_nodes_update_threshold;
};

}  // namespace mt_kahypar
