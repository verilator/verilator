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

#include <bit>
#include <cmath>
#include <limits>

#include "mt-kahypar/macros.h"
#include "mt-kahypar/parallel/stl/scalable_vector.h"
#include "mt-kahypar/utils/bit_ops.h"

namespace mt_kahypar {
namespace ds {

// Forward Declaration
class StaticBitset;

class Bitset {

  using Block = uint64_t;
  static constexpr Block BITS_PER_BLOCK = std::numeric_limits<Block>::digits;
  static_assert(repcut_serial::popcount64(BITS_PER_BLOCK) == 1);
  static constexpr Block MOD_MASK = BITS_PER_BLOCK - 1;
  static constexpr Block DIV_SHIFT = utils::log2(BITS_PER_BLOCK);

 public:
  explicit Bitset() :
    _size(0),
    _bitset() { }

  explicit Bitset(const size_t size) :
    _size(size),
    _bitset() {
    _bitset.assign(( size >> DIV_SHIFT ) + ( ( size & MOD_MASK ) != 0 ), 0);
  }

  Bitset(const Bitset&) = delete;
  Bitset & operator= (const Bitset &) = delete;
  Bitset(Bitset&&) = default;
  Bitset & operator= (Bitset &&) = default;

  size_t numBlocks() const {
    return _bitset.size();
  }

  const Block* data() const {
    return _bitset.data();
  }

  void reset() {
    memset(_bitset.data(), 0, sizeof(Block) * _bitset.size());
  }

  void resize(const size_t size) {
    _size = size;
    _bitset.assign(( size >> DIV_SHIFT ) + ( ( size & MOD_MASK ) != 0 ), 0);
  }

  void copy(const size_t num_blocks, const Block* blocks) {
    _size = num_blocks * BITS_PER_BLOCK;
    _bitset.resize(num_blocks);
    std::memcpy(_bitset.data(), blocks, sizeof(Block) * num_blocks);
  }

  bool isSet(const size_t pos) const {
    ASSERT(pos < _size);
    const size_t block_idx = pos >> DIV_SHIFT; // pos / BITS_PER_BLOCK;
    const size_t idx = pos & MOD_MASK; // pos % BITS_PER_BLOCK;
    return ( _bitset[block_idx] >> idx ) & UL(1);
  }

  void set(const size_t pos) {
    ASSERT(pos < _size);
    const size_t block_idx = pos >> DIV_SHIFT; // pos / BITS_PER_BLOCK;
    const size_t idx = pos & MOD_MASK; // pos % BITS_PER_BLOCK;
    _bitset[block_idx] |= (static_cast<Block>(1) << idx);
  }

  void unset(const size_t pos) {
    ASSERT(pos < _size);
    const size_t block_idx = pos >> DIV_SHIFT; // pos / BITS_PER_BLOCK;
    const size_t idx = pos & MOD_MASK; // pos % BITS_PER_BLOCK;
    _bitset[block_idx] &= ~(static_cast<Block>(1) << idx);
  }

 private:
  friend class StaticBitset;

  size_t _size;
  vec<Block> _bitset;
};

} // namespace ds
} // namespace mt_kahypar
