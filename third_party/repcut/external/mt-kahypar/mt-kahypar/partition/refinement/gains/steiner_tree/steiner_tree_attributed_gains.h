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

#include "mt-kahypar/datastructures/hypergraph_common.h"
#include "mt-kahypar/datastructures/static_bitset.h"
#include "mt-kahypar/datastructures/synchronized_edge_update.h"
#include "mt-kahypar/partition/mapping/target_graph.h"

namespace mt_kahypar {

/**
 * After moving a node, we perform a synchronized update of the pin count values
 * for each incident hyperedge of the node based on which we then compute an
 * attributed gain value.
 */
struct SteinerTreeAttributedGains {
  static HyperedgeWeight gain(const SynchronizedEdgeUpdate& sync_update) {
    ASSERT(sync_update.target_graph);
    ds::Bitset& connectivity_set = *sync_update.connectivity_set_after;
    // Distance between blocks of the hyperedge after the syncronized edge update
    const HyperedgeWeight distance_after = sync_update.target_graph->distance(connectivity_set);
    if ( sync_update.pin_count_in_from_part_after == 0 ) {
      ASSERT(!connectivity_set.isSet(sync_update.from));
      connectivity_set.set(sync_update.from);
    }
    if ( sync_update.pin_count_in_to_part_after == 1 ) {
      ASSERT(connectivity_set.isSet(sync_update.to));
      connectivity_set.unset(sync_update.to);
    }
    // Distance between blocks of the hyperedge before the syncronized edge update
    const HyperedgeWeight distance_before = sync_update.target_graph->distance(connectivity_set);
    // Reset connectivity set
    if ( sync_update.pin_count_in_from_part_after == 0 ) {
      ASSERT(connectivity_set.isSet(sync_update.from));
      connectivity_set.unset(sync_update.from);
    }
    if ( sync_update.pin_count_in_to_part_after == 1 ) {
      ASSERT(!connectivity_set.isSet(sync_update.to));
      connectivity_set.set(sync_update.to);
    }
    return ( distance_after - distance_before ) * sync_update.edge_weight;
  }
};

}  // namespace mt_kahypar
