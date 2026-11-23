/*******************************************************************************
 * MIT License
 *
 * This file is part of Mt-KaHyPar.
 *
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

#ifdef __GNUC__
#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wdeprecated-declarations"
#endif
#include "kahypar-resources/datastructure/kway_priority_queue.h"
#ifdef __GNUC__
#pragma GCC diagnostic pop
#endif

#include "kahypar-resources/datastructure/fast_reset_flag_array.h"

#include <tbb/enumerable_thread_specific.h>

#include "mt-kahypar/datastructures/hypergraph_common.h"

namespace mt_kahypar {

using KWayPriorityQueue = kahypar::ds::KWayPriorityQueue<HypernodeID, Gain, std::numeric_limits<Gain>, false>;
using ThreadLocalKWayPriorityQueue = tbb::enumerable_thread_specific<KWayPriorityQueue>;

using ThreadLocalFastResetFlagArray = tbb::enumerable_thread_specific<kahypar::ds::FastResetFlagArray<> >;

}