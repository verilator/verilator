/*******************************************************************************
 * MIT License
 *
 * This file is part of Mt-KaHyPar.
 *
 * Copyright (C) 2020 Lars Gottesbüren <lars.gottesbueren@kit.edu>
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

#include <limits>
#include <random>
#include <thread>
#include <vector>
#include <type_traits>

#include <tbb/task_group.h>
#include <tbb/parallel_for.h>

#include "mt-kahypar/macros.h"
#include "mt-kahypar/parallel/stl/scalable_vector.h"


namespace mt_kahypar::utils {

class Randomize {
  static constexpr bool debug = false;
  static constexpr size_t PRECOMPUTED_FLIP_COINS = 128;

  template<typename T>
  using enable_overload_t = std::enable_if_t<!std::is_same_v<parallel::scalable_vector<T>, std::vector<T>>>;

  using SwapBlock = std::pair<size_t, size_t>;

  class RandomFunctions {
   public:
    RandomFunctions() :
      _seed(-1),
      _gen(),
      _next_coin_flip(0),
      _precomputed_flip_coins(PRECOMPUTED_FLIP_COINS),
      _int_dist(0, std::numeric_limits<int>::max()),
      _float_dist(0, 1),
      _norm_dist(0, 1) {
      precompute_flip_coins();
    }

    void setSeed(int seed) {
      _seed = seed;
      _gen.seed(_seed);
      precompute_flip_coins();
    }

    bool flipCoin() {
      return _precomputed_flip_coins[++_next_coin_flip % PRECOMPUTED_FLIP_COINS];
    }

    // returns uniformly random int from the interval [low, high]
    int getRandomInt(int low, int high) {
      return _int_dist(_gen, std::uniform_int_distribution<int>::param_type(low, high));
    }

    // returns uniformly random float from the interval [low, high)
    float getRandomFloat(float low, float high) {
      return _float_dist(_gen, std::uniform_real_distribution<float>::param_type(low, high));
    }

    float getNormalDistributedFloat(float mean, float std_dev) {
      return _norm_dist(_gen, std::normal_distribution<float>::param_type(mean, std_dev));
    }

    std::mt19937& getGenerator() {
      return _gen;
    }

   private:
    void precompute_flip_coins() {
      std::uniform_int_distribution<int> bool_dist(0,1);
      for (size_t i = 0; i < PRECOMPUTED_FLIP_COINS; ++i) {
        _precomputed_flip_coins[i] = static_cast<bool>(bool_dist(_gen));
      }
    }

    int _seed;
    std::mt19937 _gen;
    size_t _next_coin_flip;
    std::vector<bool> _precomputed_flip_coins;
    std::uniform_int_distribution<int> _int_dist;
    std::uniform_real_distribution<float> _float_dist;
    std::normal_distribution<float> _norm_dist;
  };

 public:
  static Randomize& instance() {
    static Randomize instance;
    return instance;
  }

  void enableLocalizedParallelShuffle(const size_t localized_random_shuffle_block_size) {
    _perform_localized_random_shuffle = true;
    _localized_random_shuffle_block_size = localized_random_shuffle_block_size;
  }

  void setSeed(int seed) {
    for (uint32_t i = 0; i < std::thread::hardware_concurrency(); ++i) {
      _rand[i].setSeed(seed + i);
    }
  }

  bool flipCoin(int cpu_id) {
    ASSERT(cpu_id < (int)std::thread::hardware_concurrency());
    return _rand[cpu_id].flipCoin();
  }

  template <typename T, typename = enable_overload_t<T> >
  void shuffleVector(std::vector<T>& vector, size_t num_elements, int cpu_id) {
    ASSERT(cpu_id < (int)std::thread::hardware_concurrency());
    std::shuffle(vector.begin(), vector.begin() + num_elements, _rand[cpu_id].getGenerator());
  }

  template <typename T>
  void shuffleVector(parallel::scalable_vector<T>& vector, int cpu_id = -1) {
    if (cpu_id == -1)
      cpu_id = THREAD_ID;
    ASSERT(cpu_id < (int)std::thread::hardware_concurrency());
    std::shuffle(vector.begin(), vector.end(), _rand[cpu_id].getGenerator());
  }

  template <typename T, typename = enable_overload_t<T> >
  void shuffleVector(std::vector<T>& vector, int cpu_id = -1) {
    if (cpu_id == -1)
      cpu_id = THREAD_ID;
    ASSERT(cpu_id < (int)std::thread::hardware_concurrency());
    std::shuffle(vector.begin(), vector.end(), _rand[cpu_id].getGenerator());
  }

  template <typename T>
  void shuffleVector(parallel::scalable_vector<T>& vector, size_t num_elements, int cpu_id) {
    ASSERT(cpu_id < (int)std::thread::hardware_concurrency());
    std::shuffle(vector.begin(), vector.begin() + num_elements, _rand[cpu_id].getGenerator());
  }

  template <typename T, typename = enable_overload_t<T> >
  void shuffleVector(std::vector<T>& vector, size_t i, size_t j, int cpu_id) {
    ASSERT(i <= j && j <= vector.size());
    ASSERT(cpu_id < (int)std::thread::hardware_concurrency());
    std::shuffle(vector.begin() + i, vector.begin() + j, _rand[cpu_id].getGenerator());
  }

  template <typename T>
  void shuffleVector(parallel::scalable_vector<T>& vector, size_t i, size_t j, int cpu_id) {
    ASSERT(i <= j && j <= vector.size());
    ASSERT(cpu_id < (int)std::thread::hardware_concurrency());
    if ( _perform_localized_random_shuffle ) {
      localizedShuffleVector(vector, i, j, cpu_id);
    } else {
      std::shuffle(vector.begin() + i, vector.begin() + j, _rand[cpu_id].getGenerator());
    }
  }

  template <typename T>
  void parallelShuffleVector(parallel::scalable_vector<T>& vector, const size_t i, const size_t j) {
    ASSERT(i <= j && j <= vector.size());
    const size_t P = 2 * std::thread::hardware_concurrency();
    const size_t N = j - i;
    const size_t step = N / P;

    if ( _perform_localized_random_shuffle ) {
      tbb::parallel_for(UL(0), P, [&](const size_t k) {
        const size_t start = i + k * step;
        const size_t end = i + (k == P - 1 ? N : (k + 1) * step);
        localizedShuffleVector(vector, start, end, THREAD_ID);
      });
    } else {
      // Compute blocks that should be swapped before
      // random shuffling
      parallel::scalable_vector<SwapBlock> swap_blocks;
      parallel::scalable_vector<bool> matched_blocks(P, false);
      int cpu_id = THREAD_ID;
      for ( size_t a = 0; a < P; ++a ) {
        if ( !matched_blocks[a] ) {
          matched_blocks[a] = true;
          size_t b = getRandomInt(0, P - 1, cpu_id);
          while ( matched_blocks[b] ) {
            b = ( b + 1 ) % P;
          }
          matched_blocks[b] = true;
          swap_blocks.push_back(std::make_pair(a, b));
        }
      }
      ASSERT(swap_blocks.size() == P / 2, V(swap_blocks.size()) << V(P));

      tbb::parallel_for(UL(0), P / 2, [&](const size_t k) {
        const size_t block_1 = swap_blocks[k].first;
        const size_t block_2 = swap_blocks[k].second;
        const size_t start_1 = i + block_1 * step;
        const size_t end_1 = i + (block_1 == P - 1 ? N : (block_1 + 1) * step);
        const size_t start_2 = i + block_2 * step;
        const size_t end_2 = i + (block_2 == P - 1 ? N : (block_2 + 1) * step);
        const int cpu_id = THREAD_ID;
        swapBlocks(vector, start_1, end_1, start_2, end_2);
        std::shuffle(vector.begin() + start_1, vector.begin() + end_1, _rand[cpu_id].getGenerator());
        std::shuffle(vector.begin() + start_2, vector.begin() + end_2, _rand[cpu_id].getGenerator());
      });
    }
  }

  // returns uniformly random int from the interval [low, high]
  int getRandomInt(int low, int high, int cpu_id) {
    ASSERT(cpu_id < (int)std::thread::hardware_concurrency());
    return _rand[cpu_id].getRandomInt(low, high);
  }

  // returns uniformly random float from the interval [low, high)
  float getRandomFloat(float low, float high, int cpu_id) {
    ASSERT(cpu_id < (int)std::thread::hardware_concurrency());
    return _rand[cpu_id].getRandomFloat(low, high);
  }

  float getNormalDistributedFloat(float mean, float std_dev, int cpu_id) {
    ASSERT(cpu_id < (int)std::thread::hardware_concurrency());
    return _rand[cpu_id].getNormalDistributedFloat(mean, std_dev);
  }

  std::mt19937& getGenerator() {
    int cpu_id = THREAD_ID;
    return _rand[cpu_id].getGenerator();
  }

 private:
  explicit Randomize() :
    _rand(std::thread::hardware_concurrency()),
    _perform_localized_random_shuffle(false),
    _localized_random_shuffle_block_size(1024) { }

  template <typename T>
  void swapBlocks(parallel::scalable_vector<T>& vector,
                  const size_t start_1,
                  const size_t end_1,
                  const size_t start_2,
                  const size_t end_2) {
    ASSERT(start_1 <= end_1);
    ASSERT(start_2 <= end_2);
    ASSERT(end_1 <= vector.size());
    ASSERT(end_2 <= vector.size());
    size_t N = std::min(end_1 - start_1, end_2 - start_2);
    for ( size_t i = 0; i < N; ++i ) {
      std::swap(vector[start_1 + i], vector[start_2 + i]);
    }
  }

  template <typename T>
  void localizedShuffleVector(parallel::scalable_vector<T>& vector, const size_t i, const size_t j, const int cpu_id) {
    ASSERT(i <= j && j <= vector.size());
    for ( size_t start = i; start < j; start += _localized_random_shuffle_block_size ) {
      const size_t end = std::min(start + _localized_random_shuffle_block_size, j);
      std::shuffle(vector.begin() + start, vector.begin() + end, _rand[cpu_id].getGenerator());
    }
  }

  std::vector<RandomFunctions> _rand;
  bool _perform_localized_random_shuffle;
  size_t _localized_random_shuffle_block_size;
};

}  // namespace mt_kahypar::utils
