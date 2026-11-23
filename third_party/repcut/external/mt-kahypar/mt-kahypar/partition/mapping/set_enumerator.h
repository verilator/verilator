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

#include "mt-kahypar/macros.h"
#include "mt-kahypar/datastructures/bitset.h"
#include "mt-kahypar/datastructures/static_bitset.h"

namespace mt_kahypar {

/**
 * This class implements an iterator to enumerate all subsets of
 * the set {0, ..., n-1} of size m.
 */
class SetEnumerator {

  using Block = typename ds::StaticBitset::Block;
  static constexpr size_t BITS_PER_BLOCK = ds::StaticBitset::BITS_PER_BLOCK;

  class SetIterator {
   public:
    using iterator_category = std::forward_iterator_tag;
    using value_type = const ds::StaticBitset;
    using reference = const ds::StaticBitset&;
    using pointer = const ds::StaticBitset*;
    using difference_type = std::ptrdiff_t;

    SetIterator(const size_t n,
                const size_t m,
                ds::Bitset& bitset,
                const bool end) :
      _bitset(bitset),
      _cur_bitset(bitset.numBlocks(), bitset.data()),
      _cur_set(m + 1, 0) {
      _cur_set[0] = n; // Sentinel
      if ( !end ) {
        for ( size_t i = 0; i < m; ++i ) {
          _cur_set[i + 1] = m - 1 - i;
          _bitset.set(i);
        }
      } else {
        for ( size_t i = 1; i <= m; ++i ) {
          _cur_set[i] = n - i;
        }
        ++_cur_set[0];
      }
    }

    const ds::StaticBitset& operator*() const {
      return _cur_bitset;
    }

    SetIterator& operator++() {
      nextSet();
      return *this;
    }

    SetIterator operator++(int ) {
      const SetIterator res = *this;
      nextSet();
      return res;
    }

    bool operator==(const SetIterator& o) const {
      for ( size_t i = 0; i < std::min(_cur_set.size(), o._cur_set.size()); ++i) {
        if ( _cur_set[i] != o._cur_set[i] ) {
          return false;
        }
      }
      return _cur_set.size() == o._cur_set.size();
    }

    bool operator!=(const SetIterator& o) const {
      return !operator==(o);
    }

   private:
    void nextSet() {
      size_t i = 1;
      for ( ; i < _cur_set.size(); ++i ) {
        _bitset.unset(_cur_set[i]);
        ++_cur_set[i];
        if ( _cur_set[i] < _cur_set[i - 1] ) {
          _bitset.set(_cur_set[i]);
          break;
        } else {
          --_cur_set[i];
        }
      }
      if ( i < _cur_set.size() ) {
        for ( size_t j = i - 1 ; j > 0; --j ) {
          _cur_set[j] = _cur_set[j + 1] + 1;
          _bitset.set(_cur_set[j]);
        }
      } else {
        ++_cur_set[0];
      }
    }

    ds::Bitset& _bitset;
    ds::StaticBitset _cur_bitset;
    vec<size_t> _cur_set;
  };

 public:
  using iterator = SetIterator;
  using const_iterator = const SetIterator;

  explicit SetEnumerator(const size_t n, const size_t m) :
    _n(n),
    _m(m),
    _bitset(n) {
    ASSERT(_m <= _n);
  }

  SetEnumerator(const SetEnumerator&) = delete;
  SetEnumerator & operator= (const SetEnumerator &) = delete;
  SetEnumerator(SetEnumerator&&) = delete;
  SetEnumerator & operator= (SetEnumerator &&) = delete;

  iterator begin() {
    return iterator(_n, _m, _bitset, false);
  }

  iterator end() {
    return iterator(_n, _m, _bitset, true);
  }

  const_iterator cbegin() {
    return const_iterator(_n, _m, _bitset, false);
  }

  const_iterator cend() {
    return const_iterator(_n, _m, _bitset, true);
  }

 private:
  const size_t _n;
  const size_t _m;
  ds::Bitset _bitset;
};

/**
 * This class implements an iterator that iterates over all proper subsets
 * of a set. The set is represented as a bitset and position of the one bits
 * marks elements contained in the set. The set contains elements from 0 to n-1.
 */
class SubsetEnumerator {

  using Block = typename ds::StaticBitset::Block;

  class SubsetIterator {
    using iterator_category = std::forward_iterator_tag;
    using value_type = const ds::StaticBitset;
    using reference = const ds::StaticBitset&;
    using pointer = const ds::StaticBitset*;
    using difference_type = std::ptrdiff_t;

   public:
    SubsetIterator(const vec<PartitionID>& set,
                   ds::Bitset& bitset,
                   const bool end) :
      _set(set),
      _bitset(bitset),
      _cur_mask(0),
      _cur_subset(bitset.numBlocks(), bitset.data()) {
      if ( !end ) {
        applyNextMask();
      } else {
        _cur_mask = (static_cast<Block>(1) << _set.size()) - 1; // pow(2, set.size()) - 1
      }
    }

    const ds::StaticBitset& operator*() const {
      return _cur_subset;
    }

    SubsetIterator& operator++() {
      applyNextMask();
      return *this;
    }

    SubsetIterator operator++(int ) {
      const SubsetIterator res = *this;
      applyNextMask();
      return res;
    }

    bool operator==(const SubsetIterator& o) const {
      return _cur_mask == o._cur_mask;
    }

    bool operator!=(const SubsetIterator& o) const {
      return !operator==(o);
    }

   private:
    void applyNextMask() {
      ++_cur_mask;
      for ( size_t i = 0; i < _set.size(); ++i ) {
        if ( _cur_mask & ( 1 << i ) ) {
          _bitset.set(_set[i]);
        } else {
          _bitset.unset(_set[i]);
        }
      }
    }

    const vec<PartitionID>& _set;
    ds::Bitset& _bitset;
    Block _cur_mask;
    ds::StaticBitset _cur_subset;
  };

 public:
  using iterator = SubsetIterator;
  using const_iterator = const SubsetIterator;

  explicit SubsetEnumerator(const size_t n,
                            const ds::StaticBitset& set) :
    _set(set.popcount(), 0),
    _subset(n) {
    size_t i = 0;
    for ( const PartitionID& block : set ) {
      ASSERT(i < _set.size());
      _set[i++] = block;
    }
  }

  SubsetEnumerator(const SubsetEnumerator&) = delete;
  SubsetEnumerator & operator= (const SubsetEnumerator &) = delete;
  SubsetEnumerator(SubsetEnumerator&&) = delete;
  SubsetEnumerator & operator= (SubsetEnumerator &&) = delete;

  iterator begin() {
    return iterator(_set, _subset, false);
  }

  iterator end() {
    return iterator(_set, _subset, true);
  }

  const_iterator cbegin() {
    return const_iterator(_set, _subset, false);
  }

  const_iterator cend() {
    return const_iterator(_set, _subset, true);
  }

 private:
  vec<PartitionID> _set;
  ds::Bitset _subset;
};

}  // namespace kahypar
