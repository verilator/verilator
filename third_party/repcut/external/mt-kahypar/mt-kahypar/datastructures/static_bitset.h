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

#include "repcut_serial.h"

#include <atomic>
#include <bit>
#include <cstdint>
#include <limits>

#include "mt-kahypar/macros.h"
#include "mt-kahypar/parallel/atomic_wrapper.h"
#include "mt-kahypar/utils/bit_ops.h"
#include "mt-kahypar/datastructures/hypergraph_common.h"
#include "mt-kahypar/datastructures/bitset.h"

namespace mt_kahypar {
namespace ds {

class StaticBitset {

 public:
  using Block = uint64_t;
  static constexpr Block BITS_PER_BLOCK = std::numeric_limits<Block>::digits;
  static_assert(repcut_serial::popcount64(BITS_PER_BLOCK) == 1);
  static constexpr Block MOD_MASK = BITS_PER_BLOCK - 1;
  static constexpr Block DIV_SHIFT = utils::log2(BITS_PER_BLOCK);

 private:
  // ! Iterator enumerates the position of all one bits in the bitset
  class OneBitIterator {
   public:
    using iterator_category = std::forward_iterator_tag;
    using value_type = PartitionID;
    using reference = PartitionID&;
    using pointer = PartitionID*;
    using difference_type = std::ptrdiff_t;

    OneBitIterator(const size_t num_blocks,
                   const Block* bitset,
                   const PartitionID start_block) :
      ENABLE_ASSERTIONS(_num_blocks(num_blocks) COMMA)
      _bitset(bitset),
      _max_block_id(num_blocks * BITS_PER_BLOCK),
      _current_block_id(start_block) {
      if ( _current_block_id < _max_block_id ) {
        nextBlockID();
      }
    }

    PartitionID operator*() const {
      return _current_block_id;
    }

    OneBitIterator& operator++() {
      nextBlockID();
      return *this;
    }

    OneBitIterator operator++(int ) {
      const OneBitIterator res = *this;
      nextBlockID();
      return res;
    }

    bool operator==(const OneBitIterator& o) const {
      return _current_block_id == o._current_block_id;
    }

    bool operator!=(const OneBitIterator& o) const {
      return !operator==(o);
    }

   private:
    MT_KAHYPAR_ATTRIBUTE_ALWAYS_INLINE void nextBlockID() {
      ++_current_block_id;
      Block b = 0;

      while ( _current_block_id < _max_block_id ) {
        b = loadCurrentBlock();
        if (b >> ( _current_block_id & MOD_MASK ) != 0) break;

        // no more one bits in current block -> load next block
        _current_block_id += (BITS_PER_BLOCK - (_current_block_id & MOD_MASK));
      }
      const bool reached_max_id = _current_block_id == _max_block_id;
      // Avoid if statement here
      _current_block_id = (1 - reached_max_id) * ( _current_block_id +
         utils::lowest_set_bit_64(
           std::max(b >> ( _current_block_id & MOD_MASK ), static_cast<uint64_t>(1)))) +
         reached_max_id * _max_block_id;
    }

    MT_KAHYPAR_ATTRIBUTE_ALWAYS_INLINE Block loadCurrentBlock() {
      ASSERT(static_cast<size_t>(_current_block_id >> DIV_SHIFT) <= _num_blocks);
      return parallel::atomic_load(_bitset[_current_block_id >> DIV_SHIFT],
                                   std::memory_order_relaxed);
    }

    ENABLE_ASSERTIONS(const size_t _num_blocks;)
    const Block* _bitset;
    const PartitionID _max_block_id;
    PartitionID _current_block_id;
  };

 public:
  using iterator = OneBitIterator;
  using const_iterator = const OneBitIterator;

  StaticBitset() :
    _num_blocks(0),
    _bitset(nullptr) { }

  StaticBitset(const size_t num_blocks,
               const Block* bitset) :
    _num_blocks(num_blocks),
    _bitset(bitset) { }

  void set(const size_t size, const Block* block) {
    _num_blocks = size;
    _bitset = block;
  }

  iterator begin() const {
    return iterator(_num_blocks, _bitset, -1);
  }

  iterator end() const {
    return iterator(_num_blocks, _bitset, _num_blocks * BITS_PER_BLOCK);
  }

  const_iterator cbegin() const {
    return const_iterator(_num_blocks, _bitset, -1);
  }

  const_iterator cend() const {
    return const_iterator(_num_blocks, _bitset, _num_blocks * BITS_PER_BLOCK);
  }

  const Block* data() const {
    return _bitset;
  }

  bool isSet(const size_t pos) const {
    ASSERT(pos < _num_blocks * BITS_PER_BLOCK);
    const size_t block_idx = pos >> DIV_SHIFT;
    const size_t idx = pos & MOD_MASK;
    return ( *(_bitset + block_idx) >> idx ) & UL(1);
  }

  // ! Returns the number of one bits in the bitset
  int popcount() const {
    int cnt = 0;
    for ( size_t i = 0; i < _num_blocks; ++i ) {
      cnt += utils::popcount_64(
          parallel::atomic_load(_bitset[i], std::memory_order_relaxed));
    }
    return cnt;
  }

  Bitset copy() const {
    Bitset res(_num_blocks * BITS_PER_BLOCK);
    for ( size_t i = 0; i < _num_blocks; ++i ) {
      res._bitset[i] = *( _bitset + i );
    }
    return res;
  }

  Bitset operator^(const StaticBitset& other) const {
    ASSERT(_num_blocks == other._num_blocks);
    Bitset res(_num_blocks * BITS_PER_BLOCK);
    for ( size_t i = 0; i < _num_blocks; ++i ) {
      res._bitset[i] = *( _bitset + i ) ^ *( other._bitset + i );
    }
    return res;
  }

 private:
  size_t _num_blocks;
  const Block* _bitset;
};

}  // namespace ds
}  // namespace mt_kahypar
