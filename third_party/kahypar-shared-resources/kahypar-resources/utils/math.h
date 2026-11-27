/*******************************************************************************
 * MIT License
 *
 * This file is part of KaHyPar.
 *
 * Copyright (C) 2016 Sebastian Schlag <sebastian.schlag@kit.edu>
 * Copyright (C) 2016 Yaroslav Akhremtsev <yaroslav.akhremtsev@kit.edu>
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

#if defined(_MSC_VER)
#include <intrin.h>
#endif

#include <algorithm>
#include <cstddef>
#include <random>
#include <type_traits>
#include <utility>
#include <vector>

#include "kahypar-resources/macros.h"

namespace kahypar {
namespace math {
// See: Warren, Henry S. Hacker's Delight (Second Edition), p.61
template <typename T>
static inline T nextPowerOfTwoCeiled(T n) {
  static_assert(std::is_integral<T>::value, "Integer required.");
  static_assert(std::is_unsigned<T>::value, "Incompatible type");
  --n;
  for (size_t k = 1; k != 8 * sizeof(n); k <<= 1) {
    n |= n >> k;
  }
  return n + 1;
}

template <typename T, typename U>
static inline T nearestMultipleOf(T num, U multiple) {
  return (num + multiple - 1) & ~(multiple - 1);
}

template <typename T>
inline double median(const std::vector<T>& vec) {
  double median = 0.0;
  if ((vec.size() % 2) == 0) {
    median = static_cast<double>((vec[vec.size() / 2] + vec[(vec.size() / 2) - 1])) / 2.0;
  } else {
    median = vec[vec.size() / 2];
  }
  return median;
}

// based on: http://mathalope.co.uk/2014/07/18/accelerated-c-solution-to-exercise-3-2/
template <typename T>
inline std::pair<double, double> firstAndThirdQuartile(const std::vector<T>& vec) {
  if (vec.size() > 1) {
    const size_t size_mod_4 = vec.size() % 4;
    const size_t M = vec.size() / 2;
    const size_t ML = M / 2;
    const size_t MU = M + ML;
    double first_quartile = 0.0;
    double third_quartile = 0.0;
    if (size_mod_4 == 0 || size_mod_4 == 1) {
      first_quartile = (vec[ML] + vec[ML - 1]) / 2;
      third_quartile = (vec[MU] + vec[MU - 1]) / 2;
    } else if (size_mod_4 == 2 || size_mod_4 == 3) {
      first_quartile = vec[ML];
      third_quartile = vec[MU];
    }
    return std::make_pair(first_quartile, third_quartile);
  } else {
    return std::make_pair(0.0, 0.0);
  }
}

#if defined(KAHYPAR_HAS_CRC32)
template <typename T>
static inline T crc32(const T& x) {
  return _mm_crc32_u32((size_t)28475421, x);
}
#endif

template <typename T>
static inline T identity(const T& x) {
  return x;
}

template <typename T>
static inline T cs2(const T& x) {
  return x * x;
}

template <typename T>
static inline T hash(const T& x) {
  return cs2(x);
}

template <typename Key>
class MurmurHash {
 public:
  using HashValue = uint64_t;

  explicit MurmurHash(const uint32_t seed = 0) :
    _seed(seed)
  { }

  void reset(const uint32_t seed) {
    _seed = seed;
  }

  inline HashValue operator() (const Key& key) const {
    return hash(reinterpret_cast<const void*>(&key), sizeof(key), _seed);
  }

 private:
  inline uint64_t hash(const void* key, const uint32_t len, const uint32_t seed) const {
    const uint64_t m = 0xc6a4a7935bd1e995;
    const int r = 47;

    uint64_t h = seed ^ (len * m);

    const uint64_t* data = (const uint64_t*)key;
    const uint64_t* end = data + (len / 8);

    while (data != end) {
      uint64_t k = *data++;

      k *= m;
      k ^= k >> r;
      k *= m;

      h ^= k;
      h *= m;
    }

    const unsigned char* data2 = (const unsigned char*)data;

    switch (len & 7) {
      case 7:
        h ^= uint64_t(data2[6]) << 48;
        KAHYPAR_ATTRIBUTE_FALLTHROUGH;
      case 6:
        h ^= uint64_t(data2[5]) << 40;
        KAHYPAR_ATTRIBUTE_FALLTHROUGH;
      case 5:
        h ^= uint64_t(data2[4]) << 32;
        KAHYPAR_ATTRIBUTE_FALLTHROUGH;
      case 4:
        h ^= uint64_t(data2[3]) << 24;
        KAHYPAR_ATTRIBUTE_FALLTHROUGH;
      case 3:
        h ^= uint64_t(data2[2]) << 16;
        KAHYPAR_ATTRIBUTE_FALLTHROUGH;
      case 2:
        h ^= uint64_t(data2[1]) << 8;
        KAHYPAR_ATTRIBUTE_FALLTHROUGH;
      case 1: h ^= uint64_t(data2[0]);
        h *= m;
    }

    h ^= h >> r;
    h *= m;
    h ^= h >> r;

    return h;
  }

  uint32_t _seed;
};

// based on: https://github.com/llvm-mirror/libcxx/blob/9dcbb46826fd4d29b1485f25e8986d36019a6dca/include/support/win32/support.h#L149-L167
#if !defined(__GNUC__) && !defined(__clang__)
static inline int __builtin_clzll(unsigned long long mask) {
  unsigned long where;
  // BitScanReverse scans from MSB to LSB for first set bit.
  // Returns 0 if no set bit is found.

#if defined(KAHYPAR_HAS_BITSCAN64)
  if (_BitScanReverse64(&where, mask)) {
    return static_cast<int>(63 - where);
  }
#else
  // Scan the high 32 bits.
  if (_BitScanReverse(&where, static_cast<unsigned long>(mask >> 32))) {
    return static_cast<int>(63 - (where + 32));  // Create a bit offset from the MSB.
  }
  // Scan the low 32 bits.
  if (_BitScanReverse(&where, static_cast<unsigned long>(mask))) {
    return static_cast<int>(63 - where);
  }
#endif
  return 64;
}
#endif


// see: http://graphics.stanford.edu/~seander/bithacks.html#IntegerLog10
static const uint64_t powers_of_10[] = {
  0,
  10,
  100,
  1000,
  10000,
  100000,
  1000000,
  10000000,
  100000000,
  1000000000,
  10000000000,
  100000000000,
  1000000000000,
  10000000000000,
  100000000000000,
  1000000000000000,
  10000000000000000,
  100000000000000000,
  1000000000000000000,
  10000000000000000000U
};

static inline uint8_t digits(const uint64_t x) {
  uint64_t t = (64 - __builtin_clzll(x | 1)) * 1233 >> 12;
  return static_cast<uint8_t>(t - (x < powers_of_10[t]) + 1);
}

}  // namespace math
}  // namespace kahypar
