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
#include <random>
#include <tbb/tick_count.h>

#include "mt-kahypar/parallel/parallel_counting_sort.h"
#include "hash.h"

namespace mt_kahypar::utils {

/*!
 * Combines a global seed and an iteration of a loop to initialize an RNG for that iteration
 */
inline size_t seed_iteration(size_t seed, size_t iteration) {
  return hashing::integer::combine(seed, hashing::integer::hash(iteration));
}

template< template<typename> typename UnqualifiedHashFunction >
class UniformRandomSelector {
public:
  using int_type = size_t;
  using HashFunction = UnqualifiedHashFunction<int_type>;
  using RNG = hashing::HashRNG<HashFunction>;

  UniformRandomSelector(const HashFunction& hash_function, int_type seed) : rng(hash_function, seed) { }

  /*!
   * Call when you find an element with the same score as the current best.
   * Selects one of the elements with best score uniformly at random.
   */
  bool replace_sample() {
    return (dist(rng, std::uniform_int_distribution<size_t>::param_type(0, ++counter)) == 0);
  }

  /*!
   * Call when you find an element with better score for the first time
   */
  void replace() {
    counter = 0;
  }

  /*!
   * Does not reseed the hash function but reseeds the RNG, so that it can be used for neighbor rating in coarsening
   */
  void reset(size_t seed) {
    replace();
    rng.init(seed);
  }

private:
  RNG rng;
  std::uniform_int_distribution<int_type> dist;
  size_t counter = 0;
};


struct PrecomputeBucket {
  void compute_buckets(size_t n, size_t num_tasks, uint32_t seed) {
    if (n > precomputed_buckets.size()) {
      precomputed_buckets.resize(n);
    }

    const size_t chunk_size = parallel::chunking::idiv_ceil(n, num_tasks);

    tbb::parallel_for(UL(0), num_tasks, [&](size_t i) {
      std::mt19937 rng(seed);
      rng.discard(i);
      rng.seed(rng());

      auto [begin, end] = parallel::chunking::bounds(i, n, chunk_size);
      assert(begin < end);
      for (size_t j = begin; j < end; ++j) {
        precomputed_buckets[j] = static_cast<uint8_t>(rng());
      }
    });
  }

  size_t operator()(size_t i) const {
    return precomputed_buckets[i];
  }

  vec<uint8_t> precomputed_buckets;
};

// optimized version of PrecomputeBucket that uses all 32 bits of the rng call
struct PrecomputeBucketOpt {
  void compute_buckets(size_t n, size_t num_tasks, uint32_t seed) {
    if (n > precomputed_buckets.size()) {
      precomputed_buckets.resize(n);
    }

    size_t chunk_size = parallel::chunking::idiv_ceil(n, num_tasks);
    if (chunk_size % 4 != 0) {
      chunk_size += 4 - (chunk_size % 4); // round up to multiple of 4 --> only last range has to do the overhang bit
    }
    assert(chunk_size % 4 == 0);
    size_t num_tasks_needed = parallel::chunking::idiv_ceil(n, chunk_size);

    tbb::parallel_for(UL(0), num_tasks_needed, [&](size_t i) {
      std::mt19937 rng(seed);
      rng.discard(i);
      size_t local_seed = rng();
      rng.seed(local_seed);

      auto [begin, end] = parallel::chunking::bounds(i, n, chunk_size);
      assert(begin < end);
      size_t overhang = end % 4;
      size_t truncated_end = end - overhang;

      for (size_t j = begin; j < truncated_end; j += 4) {
        uint32_t x = rng();
        *( reinterpret_cast<uint32_t*>(precomputed_buckets.data() + j) ) = x;
      }

      if (overhang > 0 && begin < end) {
        uint32_t x = rng();
        for (size_t j = 0; j < overhang; ++j) {
          assert(end - j - 1 < precomputed_buckets.size());
          precomputed_buckets[end - j - 1] = static_cast<uint8_t>( mask & (x >> (8*j)) );
        }
      }
    });
  }

  size_t operator()(size_t i) const {
    return precomputed_buckets[i];
  }

  static constexpr uint32_t mask = (1 << 8) - 1;
  vec<uint8_t> precomputed_buckets;
};


struct BucketHashing {
  void compute_buckets(size_t n, size_t /*num_tasks*/, uint32_t seed) {
    unused(n);
    state = hashing::integer::hash32(seed);
  }

  size_t operator()(uint32_t i) const {
   return hashing::integer::combine32(state, hashing::integer::hash32(i)) % num_buckets;
  }

  static constexpr size_t num_buckets = 256;
  uint32_t state;
};


template<typename T, typename GetBucketCallable = PrecomputeBucketOpt>
class ParallelShuffle {
public:
  vec<T> permutation;
  GetBucketCallable get_bucket;
  vec<uint32_t> bucket_bounds;
  static constexpr size_t num_buckets = 256;

  // convenience
  typename vec<T>::const_iterator begin() const { return permutation.cbegin(); }
  typename vec<T>::const_iterator end() const { return permutation.cend(); }

  const T& at(size_t pos) const {
    assert(pos < permutation.size());
    return permutation[pos];
  }

  const T& operator[](size_t pos) const {
    return at(pos);
  }


  template<typename RangeT>
  void shuffle(const RangeT& input_elements, size_t num_tasks, std::mt19937& rng) {
    static_assert(std::is_same<typename RangeT::value_type, T>::value);
    const size_t n = input_elements.size();
    if (n < 1 << 15) {
      permutation.resize(n);
      for (size_t i = 0; i < n; ++i) { permutation[i] = input_elements[i]; }
      std::shuffle(permutation.begin(), permutation.end(), rng);
    } else {
      sample_buckets_and_group_by(input_elements, num_tasks, rng());

      // shuffle each bucket
      for (size_t i = 0; i < num_buckets; ++i) {
        seeds[i] = rng();
      }
      tbb::parallel_for(UL(0), num_buckets, [&](size_t i) {
        std::mt19937 local_rng(seeds[i]);    // alternative: seed with hash of seed and range begin
        std::shuffle(permutation.begin() + bucket_bounds[i], permutation.begin() + bucket_bounds[i + 1], local_rng);
      });
    }
  }

  template<typename RangeT>
  void sample_buckets_and_group_by(const RangeT& input_elements, size_t num_tasks, uint32_t seed) {
    // assign random buckets to elements.
    get_bucket.compute_buckets(input_elements.size(), num_tasks, seed);

    // sort elements by random buckets
    permutation.resize(input_elements.size());
    bucket_bounds = parallel::counting_sort(input_elements, permutation, num_buckets, get_bucket, num_tasks);
    assert(bucket_bounds.size() == num_buckets + 1);
  }

protected:
  std::array<std::mt19937::result_type, num_buckets> seeds;
};

template<typename IntegralT, typename GetBucketCallable = PrecomputeBucketOpt>
class ParallelPermutation : public ParallelShuffle<IntegralT, GetBucketCallable> {
public:
  void create_integer_permutation(IntegralT n, size_t num_tasks, std::mt19937& rng) {
    static_assert(std::is_integral<IntegralT>::value);
    IntegerRange iota = {0, n};
    this->shuffle(iota, num_tasks, rng);
  }

  void random_grouping(IntegralT n, size_t num_tasks, uint32_t seed) {
    static_assert(std::is_integral<IntegralT>::value);
    IntegerRange iota = {0, n};
    this->sample_buckets_and_group_by(iota, num_tasks, seed);
  }

  void sequential_fallback(size_t n, uint32_t seed) {
    auto& perm = this->permutation;
    perm.resize(n);
    std::iota(perm.begin(), perm.end(), 0);
    std::mt19937 prng(seed);
    std::shuffle(perm.begin(), perm.end(), prng);
    this->bucket_bounds.resize(this->num_buckets + 1, 0);
    size_t bucket_size = parallel::chunking::idiv_ceil(n, this->num_buckets);
    for (size_t i = 0; i < this->num_buckets; ++i) {
      this->bucket_bounds[i+1] = parallel::chunking::bounds(i, n, bucket_size).second;
    }
    assert(this->bucket_bounds.back() == n);
    assert(std::is_sorted(this->bucket_bounds.begin(), this->bucket_bounds.end()));
  }


protected:
  struct IntegerRange {
    IntegralT a, b;
    using value_type = IntegralT;
    IntegralT operator[](IntegralT i) const { return a + i;  }
    size_t size() const { return b - a; }
  };
};

class FeistelPermutation {
public:

  void create_permutation(size_t num_rounds, size_t num_entries, std::mt19937& rng) {
    // gen keys
    keys.clear();
    for (size_t i = 0; i < num_rounds; ++i) {
      keys.push_back(rng());
    }

    // set bit masks
    uint64_t num_bits = 0, next_power = 1;
    while (next_power < num_entries && next_power != 0) {
      next_power <<= 1;
      num_bits++;
    }
    assert(num_bits <= max_supported_bits);

    num_right_bits = (num_bits / 2) + (num_bits % 2);
    num_left_bits = num_bits / 2;

    right_mask = (1U << num_right_bits) - 1;
    left_mask = (1U << num_left_bits) - 1;
  }

  uint64_t encrypt(uint64_t x) const {
    assert(x < max_num_entries());
    uint32_t lmask = left_mask, rmask = right_mask;
    uint32_t l = x >> num_right_bits;
    uint32_t r = x & rmask;
    uint32_t next_l;

    for (uint32_t key : keys) {
      next_l = r;
      r = (round_function(key, r) & lmask) ^ l;
      l = next_l;
      std::swap(lmask, rmask);     // unroll loop to avoid swaps?
    }

    // applying mask only to last r and l is bad because we cannot recover those for decryption
    return (uint64_t(r) << plant_shift()) | uint64_t(l);
  }

  uint64_t decrypt(uint64_t x) const {
    uint32_t lmask = left_mask, rmask = right_mask;
    if (num_rounds() % 2 == 0) {
      std::swap(lmask, rmask);
    }

    uint32_t l = x >> plant_shift();
    uint32_t r = x & rmask;
    uint32_t next_l;

    for (auto it = keys.rbegin(); it != keys.rend(); ++it) {
      uint32_t key = *it;
      next_l = r;
      r = (round_function(key, r) & lmask) ^ l;
      l = next_l;
      std::swap(lmask, rmask);
    }

    return (uint64_t(r) << num_right_bits) | uint64_t(l);
  }

  size_t max_num_entries() const {
    return UL(1) << (num_right_bits + num_left_bits);
  }

private:

  uint64_t plant_shift() const {
    return num_rounds() % 2 == 0 ? num_left_bits : num_right_bits;
  }

  uint32_t round_function(uint32_t key, uint32_t raw) const {
    return hashing::integer::combine32(key, hashing::integer::hash32(raw));
  }

  size_t num_rounds() const {
    return keys.size();
  }
  static constexpr size_t max_supported_bits = 62;

  uint64_t num_right_bits, num_left_bits;

  uint32_t right_mask, left_mask;
  vec<uint32_t> keys;   // make std::array once tests are done?
};

} // namespace mt_kahypar::utils