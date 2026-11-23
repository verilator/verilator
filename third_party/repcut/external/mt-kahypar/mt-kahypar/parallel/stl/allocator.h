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

#include <cstring>

#ifndef NDEBUG
#include <memory>
#include <stdlib.h>
#else
#include <tbb/tbb_allocator.h>
#include <tbb/scalable_allocator.h>
#endif

namespace mt_kahypar {
namespace parallel {

#ifndef NDEBUG
// note: tbb allocators will still be used for TBB data structures such as
// tbb::concurrent_vector, tbb::concurrent_queue or tbb::enumerable_thread_specific

template<typename T>
using scalable_allocator = std::allocator<T>;

inline void* mtk_scalable_malloc(size_t size) {
  return malloc(size);
}

inline void* mtk_scalable_calloc(size_t nobj, size_t size) {
  return calloc(nobj, size);
}

inline void mtk_scalable_free(void* ptr) {
  free(ptr);
}
#else
template <typename T>
using scalable_allocator = tbb::tbb_allocator<T>;

inline void* mtk_scalable_malloc(size_t size) {
  return scalable_malloc(size);
}

inline void* mtk_scalable_calloc(size_t nobj, size_t size) {
  return scalable_calloc(nobj, size);
}

inline void mtk_scalable_free(void* ptr) {
  scalable_free(ptr);
}
#endif

}  // namespace parallel
}  // namespace mt_kahypar
