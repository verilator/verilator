/*******************************************************************************
 * MIT License
 *
 * This file is part of Mt-KaHyPar.
 *
 * Copyright (C) 2020 Tobias Heuer <tobias.heuer@kit.edu>
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

#include <algorithm>
#include <atomic>
#include <cstddef>
#include <cstdint>
#include <cstring>
#include <limits>
#include <vector>

#include "mt-kahypar/macros.h"
#include "mt-kahypar/parallel/atomic_wrapper.h"

// based on http://upcoder.com/9/fast-resettable-flag-vector/

namespace mt_kahypar {
namespace ds {
template <typename Type = std::uint16_t>
class ThreadSafeFastResetFlagArray {

public:
  explicit ThreadSafeFastResetFlagArray(const size_t size) :
    _v(std::make_unique<Type[]>(size)),
    _threshold(1),
    _size(size) {
    initialize();
  }

  ThreadSafeFastResetFlagArray() :
    _v(nullptr),
    _threshold(1),
    _size(0) { }

  ThreadSafeFastResetFlagArray(const ThreadSafeFastResetFlagArray&) = delete;
  ThreadSafeFastResetFlagArray& operator= (const ThreadSafeFastResetFlagArray&) = delete;

  ThreadSafeFastResetFlagArray(ThreadSafeFastResetFlagArray&&) = default;
  ThreadSafeFastResetFlagArray& operator= (ThreadSafeFastResetFlagArray&&) = default;

  ~ThreadSafeFastResetFlagArray() = default;

  void swap(ThreadSafeFastResetFlagArray& other) {
    using std::swap;
    swap(_v, other._v);
    swap(_threshold, other._threshold);
  }

  bool operator[] (const size_t i) const {
    return isSet(i);
  }

  // ! Changes value of entry i from false to true and returns true, if the value
  // ! hold on position i was false and was successfully set to true
  bool compare_and_set_to_true(const size_t i) {
    Type expected = repcut_serial::Ref(_v[i]).load(std::memory_order_relaxed);
    Type desired = _threshold;
    if (expected != _threshold &&
        repcut_serial::Ref(_v[i]).compare_exchange_strong(
            expected, desired, std::memory_order_acq_rel,
            std::memory_order_relaxed)) {
      // Value was successfully set from false to true
      return true;
    } else {
      // Either expected == _threshold or compare_exchange_strong failed, which means that
      // an other thread set _v[i] to true before.
      return false;
    }
  }

  void set(const size_t i, const bool value) {
	repcut_serial::Ref(_v[i]).store(value ? _threshold : 0, std::memory_order_relaxed);
  }

  void setUnsafe(const size_t i, const bool value) {
   _v[i] = value ? _threshold : 0;
  }

  void reset() {
    if (_threshold == std::numeric_limits<Type>::max()) {
      initialize();
      _threshold = 0;
    }
    ++_threshold;
  }

  size_t size() const {
    return _size;
  }

  void setSize(const size_t size, const bool init = false) {
    ASSERT(_v == nullptr, "Error");
    _v = std::make_unique<Type[]>(size);
    _size = size;
    initialize(init);
  }

  void resize(const size_t size, const bool init = false) {
    if ( size > _size ) {
      std::unique_ptr<Type[]> tmp_v =
        std::make_unique<Type[]>(size);
      std::swap(_v, tmp_v);
      _size = size;
      initialize(init);
    } else {
      _size = size;
    }
  }

 private:
  bool isSet(size_t i) const {
	return repcut_serial::Ref(_v[i]).load(std::memory_order_relaxed) == _threshold;
  }

  void initialize(const bool init = false) {
    const Type init_value = init ? _threshold : 0;
    for ( size_t i = 0; i < _size; ++i ) {
      repcut_serial::Ref(_v[i]).store(init_value, std::memory_order_relaxed);
    }
  }

  std::unique_ptr<Type[]> _v;
  Type _threshold;
  size_t _size;
};

template <typename Type>
void swap(ThreadSafeFastResetFlagArray<Type>& a,
          ThreadSafeFastResetFlagArray<Type>& b) {
  a.swap(b);
}
}  // namespace ds
}  // namespace mt_kahypar
