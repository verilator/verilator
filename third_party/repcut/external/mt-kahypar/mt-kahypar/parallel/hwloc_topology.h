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

#include <vector>

#include <hwloc.h>

#include "kahypar-resources/macros.h"

namespace mt_kahypar {
namespace parallel {
/**
 * Static class responsible for initializing, destroying and
 * calling hwloc library. Calls to hwloc library are outsourced
 * to this class such that hardware topology can be mocked.
 */
class HwlocTopology {
 public:
  static void initialize(hwloc_topology_t& topology) {
    hwloc_topology_init(&topology);
    hwloc_topology_load(topology);
  }

  static hwloc_obj_t get_first_numa_node(hwloc_topology_t topology) {
    int numa_depth = hwloc_get_type_or_below_depth(topology, HWLOC_OBJ_NUMANODE);
    hwloc_obj_t node = hwloc_get_obj_by_depth(topology, numa_depth, 0);

    // Special Case:
    // On some architecture the numa node is represented with a special node
    // (with a so called "special depth" < 0) without childs. The core nodes of the numa
    // node are then stored under another node (e.g. L3 Cache Node) on the same level
    // in the topology. Since, we rely on the assumption that we find all core nodes under
    // a numa node, we have to fix this here.
    if ( numa_depth < 0 ) {
      ASSERT(node->parent);
      for ( size_t i = 0; i < node->parent->arity; ++i ) {
        if ( node->parent->children[i]->type != HWLOC_OBJ_NUMANODE ) {
          node = node->parent->children[i];
          break;
        }
      }

      int current_index = 0;
      hwloc_obj_t current_node = node;
      while(current_node) {
        current_node->os_index = current_index++;
        current_node = current_node->next_cousin;
      }
    }

    return node;
  }

  static std::vector<int> get_cpus_of_numa_node_without_hyperthreads(hwloc_obj_t node) {
    std::vector<int> cpus;

    auto add_cpu_of_core = [&](hwloc_obj_t node) {
                             ASSERT(node->type == HWLOC_OBJ_CORE);
                             std::vector<int> core_cpus;
                             int cpu_id;
                             hwloc_bitmap_foreach_begin(cpu_id, node->cpuset) {
                               core_cpus.emplace_back(cpu_id);
                             }
                             hwloc_bitmap_foreach_end();
                             // Assume that core consists of two processing units (hyperthreads)
                             ASSERT(!core_cpus.empty());
                             cpus.push_back(core_cpus[0]);
                           };
    enumerate_all_core_units(node, add_cpu_of_core);

    return cpus;
  }

  static std::vector<int> get_cpus_of_numa_node_only_hyperthreads(hwloc_obj_t node) {
    std::vector<int> cpus;

    auto add_cpu_of_core = [&](hwloc_obj_t node) {
                             ASSERT(node->type == HWLOC_OBJ_CORE);
                             std::vector<int> core_cpus;
                             int cpu_id;
                             hwloc_bitmap_foreach_begin(cpu_id, node->cpuset) {
                               core_cpus.emplace_back(cpu_id);
                             }
                             hwloc_bitmap_foreach_end();
                             // Assume that core consists of two processing units (hyperthreads)
                             if ( core_cpus.size() >= 2 ) {
                              cpus.push_back(core_cpus[1]);
                             }
                           };
    enumerate_all_core_units(node, add_cpu_of_core);

    return cpus;
  }

  static void destroy_topology(hwloc_topology_t topology) {
    hwloc_topology_destroy(topology);
  }

 private:
  template <class F>
  static void enumerate_all_core_units(hwloc_obj_t node, F& func) {
    if (node->type == HWLOC_OBJ_CORE) {
      func(node);
      return;
    }

    for (size_t i = 0; i < node->arity; ++i) {
      enumerate_all_core_units(node->children[i], func);
    }
  }

  HwlocTopology() { }
};
}  // namespace parallel
}  // namespace mt_kahypar
