/*******************************************************************************
 * MIT License
 *
 * This file is part of Mt-KaHyPar.
 *
 * Copyright (C) 2025 Nikolai Maas <nikolai.maas@kit.edu>
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


namespace mt_kahypar {

// This struct describes how (and whether) a hyperedge should be included in 
// a two-way flow network for flow refinement. Its computation depends on the
// concrete objective that is used for the partition
struct FlowNetworkEdgeParameters {
  FlowNetworkEdgeParameters() = default;
  FlowNetworkEdgeParameters(HyperedgeWeight capacity):
    capacity(capacity) {}

  // Capacity of this hyperedge in the flow network. For some objectives
  // (Steiner trees), this might only be an approximation of the actual gain.
  // Zero means the hyperedge should be excluded from the flow problem since
  // it can't affect the global objective.
  HyperedgeWeight capacity = 0;
  // Whether a new pin, which is the source node, should be added to the hyperedge.
  // Useful to model that it is better to have all pins in block 0 than all pins in
  // block 1, which can happen for the Steiner tree metric
  bool connect_to_source = false;
  // Whether a new pin, which is the sink node, should be added to the hyperedge.
  // Useful to model that it is better to have all pins in block 1 than all pins in
  // block 0, which can happen for the Steiner tree metric
  bool connect_to_sink = false;
  // Whether the hyperedge is cut in the flow assignment that corresponds to the
  // current partition (required to correctly compute the initial cut value).
  // Only needs to be set if different from what would be inferred by considering
  // the original pins of the hyperedge
  bool is_cut = false;
};

} // namespace mt_kahypar
