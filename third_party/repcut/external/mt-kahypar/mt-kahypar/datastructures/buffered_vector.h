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

#include <algorithm>
#include <atomic>
#include <vector>
#include <cassert>

#include <tbb/enumerable_thread_specific.h>

#include "mt-kahypar/parallel/stl/allocator.h"

namespace mt_kahypar::ds {

template<typename T>
class BufferedVector {
public:
  using vec_t = std::vector<T, parallel::scalable_allocator<T>>;

  BufferedVector() : BufferedVector(0)
  { }

  explicit BufferedVector(size_t max_size) :
    data(max_size, T()),
    buffers([&] { vec_t x; x.reserve(MAX_BUFFER_SIZE); return x; })
  { }

  void clear() {
    back.store(0, std::memory_order_relaxed);
    assert(std::all_of(buffers.begin(), buffers.end(), [&](vec_t& x) { return x.empty(); }));
  }

  size_t size() const {
    return back.load(std::memory_order_relaxed);
  }

  size_t capacity() const {
    return data.size();
  }

  void adapt_capacity(size_t sz) {
    if (sz > data.size()) {
      data.resize(sz, T());
    }
  }

  void push_back_atomic(const T& element) {
    size_t pos = back.fetch_add(1, std::memory_order_relaxed);
    assert(pos < data.size());
    data[pos] = element;
  }

  void push_back_buffered(const T& element) {
    vec_t& buffer = buffers.local();
    buffer.push_back(element);
    if (buffer.size() == MAX_BUFFER_SIZE) {
      flush_buffer(buffer);
    }
  }

  void finalize() {
    for (vec_t& buffer : buffers) {
      flush_buffer(buffer);
    }
  }

  auto begin() { return data.begin(); }
  auto end() { return data.begin() + size(); }
  T& operator[](size_t pos) { return data[pos]; }
  const T& operator[](size_t pos) const { return data[pos]; }


  struct RandomAccessRange {
    size_t actual_size;
    const vec_t& data_ref;
    const T& operator[](size_t i) const { return data_ref[i]; }
    size_t size() const { return actual_size; }
  };
  RandomAccessRange range() const { return { size(), data }; }

  const vec_t& getData() { return data; }

private:

  void flush_buffer(vec_t& buffer) {
    if (!buffer.empty()) {
      size_t pos = back.fetch_add(buffer.size(), std::memory_order_relaxed);
      assert(pos + buffer.size() - 1 < data.size());
      std::copy_n(buffer.begin(), buffer.size(), data.begin() + pos);
      buffer.clear();
    }
  }

  vec_t data;
  std::atomic<size_t> back{0};
  tbb::enumerable_thread_specific<vec_t> buffers;
  static constexpr size_t MAX_BUFFER_SIZE = 1024;
};
}