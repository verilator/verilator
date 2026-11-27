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

#ifndef NDEBUG
#include <memory>
#else
#include <mt-kahypar/parallel/stl/allocator.h>
#endif

namespace mt_kahypar {
namespace parallel {

#ifndef NDEBUG
template<typename T>
using zero_allocator = std::allocator<T>;
#else
template <typename T>
class zero_allocator : public parallel::scalable_allocator<T> {
 public:
  using value_type = T;
  using propagate_on_container_move_assignment = std::true_type;
  using is_always_equal = std::true_type;

  zero_allocator() = default;
  template <typename U>
  explicit zero_allocator(const U&) noexcept {}

  T* allocate(std::size_t n) {
    T* ptr = parallel::scalable_allocator<T>::allocate(n);
    std::memset(static_cast<void*>(ptr), 0, n * sizeof(value_type));
    return ptr;
  }
};
#endif

}  // namespace parallel
}  // namespace mt_kahypar
