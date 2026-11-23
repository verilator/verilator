/*******************************************************************************
 * MIT License
 *
 * This file is part of KaHyPar.
 *
 * Copyright (C) 2015-2016 Sebastian Schlag <sebastian.schlag@kit.edu>
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
#include <cstddef>
#include <cstdint>
#include <cstring>
#include <limits>
#include <memory>
#include <vector>

#include "kahypar-resources/macros.h"

// based on http://upcoder.com/9/fast-resettable-flag-vector/

namespace kahypar {
namespace ds {
template <typename UnderlyingType = std::uint16_t>
class FastResetFlagArray {
 public:
  explicit FastResetFlagArray(const size_t size) :
    _v(std::make_unique<UnderlyingType[]>(size)),
    _threshold(1),
    _size(size) {
    memset(_v.get(), 0, size * sizeof(UnderlyingType));
  }

  FastResetFlagArray() :
    _v(nullptr),
    _threshold(1),
    _size(0) { }

  FastResetFlagArray(const FastResetFlagArray&) = delete;
  FastResetFlagArray& operator= (const FastResetFlagArray&) = delete;

  FastResetFlagArray(FastResetFlagArray&&) = default;
  FastResetFlagArray& operator= (FastResetFlagArray&&) = default;

  ~FastResetFlagArray() = default;

  void swap(FastResetFlagArray& other) {
    using std::swap;
    swap(_v, other._v);
    swap(_threshold, other._threshold);
  }

  bool operator[] (const size_t i) const {
    return isSet(i);
  }

  void set(const size_t i, const bool value = true) {
    _v[i] = value ? _threshold : 0;
  }

  void reset() {
    if (_threshold == std::numeric_limits<UnderlyingType>::max()) {
      for (size_t i = 0; i != _size; ++i) {
        _v[i] = 0;
      }
      _threshold = 0;
    }
    ++_threshold;
  }

  void setSize(const size_t size, const bool initialiser = false) {
    ASSERT(_v == nullptr, "Error");
    _v = std::make_unique<UnderlyingType[]>(size);
    _size = size;
    memset(_v.get(), (initialiser ? 1 : 0), size * sizeof(UnderlyingType));
  }

 private:
  bool isSet(size_t i) const {
    return _v[i] == _threshold;
  }

  std::unique_ptr<UnderlyingType[]> _v;
  UnderlyingType _threshold;
  size_t _size;
};

template <typename UnderlyingType>
void swap(FastResetFlagArray<UnderlyingType>& a,
          FastResetFlagArray<UnderlyingType>& b) {
  a.swap(b);
}
}  // namespace ds
}  // namespace kahypar
