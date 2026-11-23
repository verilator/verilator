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

#include <iterator>
#include <vector>
#include <numeric>

namespace mt_kahypar {

template<typename IteratorT>
class IteratorRange {
 public:
  IteratorRange(const IteratorT& first, const IteratorT& firstInvalid) : __begin(first), __end(firstInvalid) { }

  using reference = typename std::iterator_traits<IteratorT>::reference;
  using Iterator = IteratorT; // make publicly visible

  IteratorT begin() const {
    return __begin;
  }

  IteratorT end() const {
    return __end;
  }

  bool empty() const {
    return __begin == __end;
  }

  size_t size() const {
    return __end - __begin;
  }

  reference operator[](size_t n) const {
    return __begin[n];
  }

private:
  IteratorT __begin, __end;
};


template<typename RangeT>
class ConcatenatedRange {
private:
  struct begin_tag {};
  struct end_tag {};

public:
  class Iterator {
  public:
    using value_type = typename std::iterator_traits<typename RangeT::Iterator>::value_type;

    Iterator(std::vector<RangeT>& ranges, begin_tag) : ranges(ranges), currentRange(0), currentRangeIterator(ranges.front().begin()) {
      moveToNextRange();
    }

    Iterator(std::vector<RangeT>& ranges, end_tag) : ranges(ranges), currentRange(ranges.size() - 1), currentRangeIterator(ranges.back().end()) { }


    bool operator==(Iterator& o) {
      return currentRange == o.currentRange && currentRangeIterator == o.currentRangeIterator;
    }

    bool operator!=(Iterator& o) {
      return !operator==(o);
    }

    Iterator& operator++() {
      // if we're at the end of the current range, advance to the next
      // restrict currentRange to ranges.size() - 1, since the end() ConcatenatedRange::Iterator has to be initialized somehow
      if (++currentRangeIterator == ranges[currentRange].end()) {
        moveToNextRange();
      }
      return *this;
    }

    value_type operator*() const {
      return *currentRangeIterator;
    }

  private:
    std::vector<RangeT>& ranges;
    size_t currentRange;
    typename RangeT::Iterator currentRangeIterator;

    void moveToNextRange() {
      while (currentRangeIterator == ranges[currentRange].end() && currentRange < ranges.size() - 1) {
        currentRangeIterator = ranges[++currentRange].begin();
      }
    }

  };

  Iterator begin() {
    assert(!ranges.empty());
    return Iterator(ranges, begin_tag());
  }

  Iterator end() {
    assert(!ranges.empty());
    return Iterator(ranges, end_tag());
  }

  void concat(RangeT&& r) {
    ranges.push_back(r);
  }

  void concat(RangeT& r) {
    ranges.push_back(r);
  }

private:
  std::vector<RangeT> ranges;
};


template<typename T>
class IntegerIterator {
  public:
    using iterator_category = std::random_access_iterator_tag;
    using value_type = T;
    using reference = T;
    using pointer = const T*;
    using difference_type = T;

    explicit IntegerIterator(T value) : _value(value) { }

    reference operator*() const {
      return _value;
    }

    pointer operator->() const {
      return &_value;
    }

    IntegerIterator& operator++() {
      ++_value;
      return *this;
    }

    IntegerIterator& operator--() {
      --_value;
      return *this;
    }

    IntegerIterator operator++(int) {
      IntegerIterator tmp_it(_value);
      ++_value;
      return tmp_it;
    }

    IntegerIterator operator--(int) {
      IntegerIterator tmp_it(_value);
      --_value;
      return tmp_it;
    }

    IntegerIterator operator+(const difference_type& n) const {
      return IntegerIterator(_value + n);
    }

    IntegerIterator& operator+=(const difference_type& n) {
      _value += n;
      return *this;
    }

    IntegerIterator operator-(const difference_type& n) const {
      return IntegerIterator(_value - n);
    }

    IntegerIterator& operator-=(const difference_type& n) {
      _value -= n;
      return *this;
    }

    reference operator[](const difference_type& n) const {
      return _value + n;
    }

    bool operator==(const IntegerIterator& other) const {
      return _value == other._value;
    }

    bool operator!=(const IntegerIterator& other) const {
      return _value != other._value;
    }

    bool operator<(const IntegerIterator& other) const {
      return _value < other._value;
    }

    bool operator>(const IntegerIterator& other) const {
      return _value > other._value;
    }

    bool operator<=(const IntegerIterator& other) const {
      return _value <= other._value;
    }

    bool operator>=(const IntegerIterator& other) const {
      return _value >= other._value;
    }

    difference_type operator-(const IntegerIterator& other) const {
      return (_value - other._value);
    }

    friend IntegerIterator operator+(const difference_type& n, const IntegerIterator& it) {
      return it + n;
    }

  private:
    T _value;
};


template<typename T>
using IntegerRange = IteratorRange<IntegerIterator<T>>;

template<typename T>
IntegerRange<T> integer_range(T start, T end) {
  return IntegerRange<T>(IntegerIterator<T>(start), IntegerIterator<T>(end));
}

template<typename T>
IntegerRange<T> integer_range(T end) {
  return integer_range<T>(0, end);
}

} // namespace mt_kahypar
