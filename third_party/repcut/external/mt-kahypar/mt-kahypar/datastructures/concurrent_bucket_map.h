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
#include <thread>
#include <cmath>

#include <tbb/task_arena.h>
#include <tbb/task_group.h>

#include "kahypar-resources/meta/mandatory.h"

#include "mt-kahypar/macros.h"
#include "mt-kahypar/parallel/stl/scalable_vector.h"
#include "mt-kahypar/parallel/atomic_wrapper.h"

namespace mt_kahypar {
namespace ds {

/*!
 * Concurrent data structures to distribute key-value pairs
 * into buckets such that values with the same key reside in
 * the same bucket. Main use case for that data structure is
 * within the parallel hyperedge detection inside the multilevel
 * contractions. There, hyperedges are inserted with its footprint
 * as key into this data structure and afterwards all hyperedges
 * with the same footprint reside in the same bucket. Finally,
 * parallel hyperedges can be detected by processing each bucket
 * sequential, but several buckets in parallel.
 * If we insert a key-value pair, we compute its corresponding
 * bucket by computing key % num_buckets. To insert the key-value
 * pair, we acquire a lock on the corresponding bucket. Note,
 * key must be of type uint64_t.
 */
template <typename Value>
class ConcurrentBucketMap {

  static constexpr bool debug = false;
  static constexpr size_t BUCKET_FACTOR = 128;

  using Bucket = parallel::scalable_vector<Value>;

 public:

  ConcurrentBucketMap() :
    _num_buckets(align_to_next_power_of_two(BUCKET_FACTOR * std::thread::hardware_concurrency())),
    _mod_mask(_num_buckets - 1),
    _spin_locks(_num_buckets),
    _buckets(_num_buckets) { }

  ConcurrentBucketMap(const ConcurrentBucketMap&) = delete;
  ConcurrentBucketMap & operator= (const ConcurrentBucketMap &) = delete;

  ConcurrentBucketMap(ConcurrentBucketMap&& other) :
    _num_buckets(other._num_buckets),
    _mod_mask(_num_buckets - 1),
    _spin_locks(_num_buckets),
    _buckets(std::move(other._buckets)) { }

  template<typename F>
  void doParallelForAllBuckets(const F& f) {
    tbb::parallel_for(UL(0), _num_buckets, [&](const size_t i) {
      f(i);
    });
  }

  // ! Returns the number of buckets
  size_t numBuckets() const {
    return _num_buckets;
  }

  // ! Returns the corresponding bucket
  Bucket& getBucket(const size_t bucket) {
    ASSERT(bucket < _num_buckets);
    return _buckets[bucket];
  }

  // ! Reserves memory in each bucket such that the estimated number of insertions
  // ! can be handled without the need (with high probability) of expensive bucket resizing.
  void reserve_for_estimated_number_of_insertions(const size_t estimated_num_insertions) {
    // ! Assumption is that keys are evenly distributed among buckets (with a small buffer)
    const size_t estimated_bucket_size = std::max(
      static_cast<size_t>( 1.5 * estimated_num_insertions ) / _num_buckets, UL(1));
    tbb::parallel_for(UL(0), _num_buckets, [&](const size_t i) {
      _buckets[i].reserve(estimated_bucket_size);
    });
  }

  // ! Inserts a key-value pair
  void insert(const size_t& key, Value&& value) {
    size_t bucket = key & _mod_mask;
    ASSERT(bucket < _num_buckets);
    _spin_locks[bucket].lock();
    _buckets[bucket].emplace_back( std::move(value) );
    _spin_locks[bucket].unlock();
  }

  // ! Frees the memory of all buckets
  void free() {
    parallel::parallel_free(_buckets);
  }

  // ! Frees the memory of the corresponding bucket
  void free(const size_t bucket) {
    ASSERT(bucket < _num_buckets);
    parallel::free(_buckets[bucket]);
  }

  // ! Clears the corresponding bucket
  void clear(const size_t bucket) {
    ASSERT(bucket < _num_buckets);
    _buckets[bucket].clear();
  }

  void clearParallel() {
    doParallelForAllBuckets([&](const size_t i) {
      clear(i);
    });
  }

 private:
  size_t align_to_next_power_of_two(const size_t size) const {
    return std::pow(2.0, std::ceil(std::log2(static_cast<double>(size))));
  }

  const size_t _num_buckets;
  const size_t _mod_mask;
  std::vector<SpinLock> _spin_locks;
  parallel::scalable_vector<Bucket> _buckets;
};
}  // namespace ds
}  // namespace mt_kahypar
