/*******************************************************************************
 * MIT License
 *
 * This file is part of Mt-KaHyPar.
 *
 * Copyright (C) 2019 Tobias Heuer <tobias.heuer@kit.edu>
 * Copyright (C) 2026 Nikolai Maas <nikolai.maas@kit.edu>
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

#include <cstdint>
#include <algorithm>
#include <atomic>

#include "mt-kahypar/datastructures/hypergraph_common.h"
#include "mt-kahypar/parallel/stl/scalable_vector.h"

namespace mt_kahypar::utils {

inline void deduplicateHyperedgePins(vec<HypernodeID>& hyperedge,
                                     size_t& num_duplicated_pins,
                                     size_t& num_hes_with_duplicated_pins) {
  std::sort(hyperedge.begin(), hyperedge.end());
  size_t j = 1;
  for ( size_t i = 1; i < hyperedge.size(); ++i ) {
    if ( hyperedge[j - 1] != hyperedge[i] ) {
      std::swap(hyperedge[i], hyperedge[j++]);
    }
  }

  if ( j < hyperedge.size() ) {
    // Remove duplicated pins
    repcut_serial::Ref(num_hes_with_duplicated_pins).fetch_add(1, std::memory_order_relaxed);
    repcut_serial::Ref(num_duplicated_pins).fetch_add(hyperedge.size() - j, std::memory_order_relaxed);
    hyperedge.resize(j);
  }
}

}  // namespace
