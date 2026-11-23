/*******************************************************************************
 * MIT License
 *
 * This file is part of Mt-KaHyPar.
 *
 * Copyright (C) 2024 Nikolai Maas <nikolai.maas@kit.edu>
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

#include "include/mtkahypartypes.h"

#include "mt-kahypar/datastructures/hypergraph_common.h"
#include "mt-kahypar/parallel/atomic_wrapper.h"
#include "mt-kahypar/datastructures/pin_count_snapshot.h"
#include "mt-kahypar/datastructures/bitset.h"


namespace mt_kahypar {

struct SynchronizedEdgeUpdate {
  HyperedgeID he = kInvalidHyperedge;
  PartitionID from = kInvalidPartition;
  PartitionID to = kInvalidPartition;
  HyperedgeID edge_weight = 0;
  HypernodeID edge_size = 0;
  HypernodeID pin_count_in_from_part_after = kInvalidHypernode;
  HypernodeID pin_count_in_to_part_after = kInvalidHypernode;
  PartitionID block_of_other_node = kInvalidPartition;
  ds::Bitset* connectivity_set_after = nullptr;
  ds::PinCountSnapshot* pin_counts_after = nullptr;
  const TargetGraph* target_graph = nullptr;
  ds::Array<SpinLock>* edge_locks = nullptr;

  MT_KAHYPAR_ATTRIBUTE_ALWAYS_INLINE
  HypernodeID decrementPinCountInPart(PartitionID part) {
    ASSERT(pin_counts_after != nullptr);
    HypernodeID decremented = pin_counts_after->decrementPinCountInPart(part);
    if (connectivity_set_after != nullptr && decremented == 0) {
      ASSERT(connectivity_set_after->isSet(part));
      connectivity_set_after->unset(part);
    }
    return decremented;
  }

  MT_KAHYPAR_ATTRIBUTE_ALWAYS_INLINE
  HypernodeID incrementPinCountInPart(PartitionID part) {
    ASSERT(pin_counts_after != nullptr);
    HypernodeID incremented = pin_counts_after->incrementPinCountInPart(part);
    if (connectivity_set_after != nullptr && incremented == 1) {
      ASSERT(!connectivity_set_after->isSet(part));
      connectivity_set_after->set(part);
    }
    return incremented;
  }
};

struct NoOpDeltaFunc {
  void operator() (const SynchronizedEdgeUpdate&) { }
};

} // namespace mt_kahypar
