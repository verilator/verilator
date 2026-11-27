/*******************************************************************************
 * MIT License
 *
 * This file is part of Mt-KaHyPar.
 *
 * Copyright (C) 2020 Lars Gottesbüren <lars.gottesbueren@kit.edu>
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

#include <array>
#include <cassert>
#include <random>
#include <type_traits>

#include "mt-kahypar/macros.h"

namespace mt_kahypar::hashing {

namespace integer {

// from parlay

inline uint32_t hash32(uint32_t a) {
  a = (a + 0x7ed55d16) + (a << 12);
  a = (a ^ 0xc761c23c) ^ (a >> 19);
  a = (a + 0x165667b1) + (a << 5);
  a = (a + 0xd3a2646c) ^ (a << 9);
  a = (a + 0xfd7046c5) + (a << 3);
  a = (a ^ 0xb55a4f09) ^ (a >> 16);
  return a;
}

inline uint32_t hash32_2(uint32_t a) {
  uint32_t z = (a + 0x6D2B79F5UL);
  z = (z ^ (z >> 15)) * (z | UL(1));
  z ^= z + (z ^ (z >> 7)) * (z | UL(61));
  return z ^ (z >> 14);
}

inline uint32_t hash32_3(uint32_t a) {
  uint32_t z = a + 0x9e3779b9;
  z ^= z >> 15;
  z *= 0x85ebca6b;
  z ^= z >> 13;
  z *= 0xc2b2ae3d;  // 0xc2b2ae35 for murmur3
  return z ^= z >> 16;
}

inline uint64_t hash64(uint64_t u) {
  uint64_t v = u * 3935559000370003845ul + UL(2691343689449507681);
  v ^= v >> 21;
  v ^= v << 37;
  v ^= v >> 4;
  v *= 4768777513237032717ul;
  v ^= v << 20;
  v ^= v >> 41;
  v ^= v << 5;
  return v;
}

inline uint64_t hash64_2(uint64_t x) {
  x = (x ^ (x >> 30)) * UINT64_C(0xbf58476d1ce4e5b9);
  x = (x ^ (x >> 27)) * UINT64_C(0x94d049bb133111eb);
  x = x ^ (x >> 31);
  return x;
}

// from boost::hash_combine
inline uint32_t combine32(uint32_t left, uint32_t hashed_right) {
  return left ^ (hashed_right + 0x9e3779b9 + (left << 6) + (left >> 2));
}

inline uint32_t combine32_2(uint32_t left, uint32_t hashed_right) {
  constexpr uint32_t c1 = 0xcc9e2d51;
  constexpr uint32_t c2 = 0x1b873593;
  constexpr auto rotate_left = [](uint32_t x, uint32_t r) -> uint32_t {
    return (x << r) | (x >> (32 - r));
  };

  hashed_right *= c1;
  hashed_right = rotate_left(hashed_right,15);
  hashed_right *= c2;

  left ^= hashed_right;
  left = rotate_left(left,13);
  left = left * 5 + 0xe6546b64;
  return left;
}

inline uint64_t combine64(uint64_t left, uint64_t hashed_right) {
  return left ^ (hashed_right + 0x9e3779b97f4a7c15 + (left << 12) + (left >> 4));
}

template <class T> struct dependent_false : std::false_type {};

template<typename T> T combine(T left, T hashed_right) {
  if constexpr (sizeof(T) == 4) {
    return combine32(left, hashed_right);
  } else if constexpr (sizeof(T) == 8) {
    return combine64(left, hashed_right);
  } else {
    static_assert(dependent_false<T>::value, "hashing::integer::combine not intended for other sizes than 32bit and 64bit int");
    return left + hashed_right;
  }
}

template<typename T> T hash(T x) {
  if constexpr (sizeof(T) == 4) {
    return hash32(x);
  } else if constexpr (sizeof(T) == 8) {
    return hash64(x);
  } else {
    static_assert(dependent_false<T>::value, "hashing::integer::hash combine not intended for other sizes than 32bit and 64bit int");
    return x;
  }
}


} // namespace integer


// from thrill

  /*!
 * Tabulation Hashing, see https://en.wikipedia.org/wiki/Tabulation_hashing
 *
 * Keeps a table with size * 256 entries of type hash_t, filled with random
 * values.  Elements are hashed by treating them as a vector of 'size' bytes,
 * and XOR'ing the values in the data[i]-th position of the i-th table, with i
 * ranging from 0 to size - 1.
 */

template <size_t size, typename hash_t = uint32_t, typename prng_t = std::mt19937>
class TabulationHashing
{
public:
  using hash_type = hash_t;  // make public
  using prng_type = prng_t;
  using Subtable = std::array<hash_type, 256>;
  using Table = std::array<Subtable, size>;

  explicit TabulationHashing(size_t seed = 0) { init(seed); }

  //! (re-)initialize the table by filling it with random values
  void init(const size_t seed) {
    prng_t rng { seed };
    for (size_t i = 0; i < size; ++i) {
      for (size_t j = 0; j < 256; ++j) {
        table_[i][j] = rng();
      }
    }
  }

  //! Hash an element
  template <typename T>
  hash_type operator () (const T& x) const {
    static_assert(sizeof(T) == size, "Size mismatch with operand type");

    hash_t hash = 0;
    const uint8_t* ptr = reinterpret_cast<const uint8_t*>(&x);
    for (size_t i = 0; i < size; ++i) {
      hash ^= table_[i][*(ptr + i)];
    }
    return hash;
  }

protected:
  Table table_;
};

//! Tabulation hashing
template <typename T>
using HashTabulated = TabulationHashing<sizeof(T), T>;

template<typename T>
struct SimpleIntHash {
  using hash_type = T;

  void init(T /* seed */) {
    // intentionally unimplemented
  }

  T operator()(const T& x) const {
    return integer::hash(x);
  }
};


// implements the rng interface required for std::uniform_int_distribution
template<typename HashFunction>
struct HashRNG {
  using result_type = typename HashFunction::hash_type;
  explicit HashRNG(HashFunction& hash, result_type seed) : hash(hash), state(hash(seed)), counter(0) { }
  static constexpr result_type min() { return std::numeric_limits<result_type>::min(); }
  static constexpr result_type max() { return std::numeric_limits<result_type>::max(); }

  // don't do too many calls of this
  result_type operator()() {
    //state = hash(state);
    state = integer::combine(state, integer::hash(counter++));
    return state;
  }

private:
  HashFunction& hash; // Hash function copy is expensive in case of tabulation hashing.
  result_type state;
  result_type counter;
};

} // namespace mt_kahypar::hashing