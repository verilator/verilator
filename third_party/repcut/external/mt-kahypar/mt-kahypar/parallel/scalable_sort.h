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

#ifndef KAHYPAR_DISABLE_PARLAY
#include <parlay/primitives.h>
#else
#include <tbb/parallel_sort.h>
#endif

namespace mt_kahypar::parallel {

// scalable sort implementation (with fallback to TBB sort if parlay dependency is disabled)
template <typename Range, typename Compare>
void scalable_sort(Range&& input, Compare&& cmp) {
  #ifndef KAHYPAR_DISABLE_PARLAY
    parlay::sort_inplace(std::forward<Range>(input), std::forward<Compare>(cmp));
  #else
    tbb::parallel_sort(std::forward<Range>(input), std::forward<Compare>(cmp));
  #endif
}

}  // namespace mt_kahypar::parallel
