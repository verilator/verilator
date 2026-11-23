/*******************************************************************************
 * MIT License
 *
 * This file is part of KaHyPar.
 *
 * Copyright (C) 2014-2016 Sebastian Schlag <sebastian.schlag@kit.edu>
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
#include <ctime>
#include <limits>
#include <random>
#include <vector>

namespace kahypar {
class Randomize {
 public:
  Randomize(const Randomize&) = delete;
  Randomize(Randomize&&) = delete;
  Randomize& operator= (const Randomize&) = delete;
  Randomize& operator= (Randomize&&) = delete;

  static Randomize & instance() {
    static Randomize instance;
    return instance;
  }

  bool flipCoin() {
    return static_cast<bool>(_bool_dist(_gen));
  }

  int newRandomSeed() {
    return _int_dist(_gen);
  }

  void setSeed(int seed) {
    _seed = seed;
    _gen.seed(_seed);
  }

  template <typename T>
  void shuffleVector(std::vector<T>& vector, size_t num_elements) {
    std::shuffle(vector.begin(), vector.begin() + num_elements, _gen);
  }

  template <typename T>
  void shuffleVector(std::vector<T>& vector, size_t i, size_t j) {
    std::shuffle(vector.begin() + i, vector.begin() + j, _gen);
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
  Randomize() :
    _seed(-1),
    _gen(),
    _bool_dist(0, 1),
    _int_dist(0, std::numeric_limits<int>::max()),
    _float_dist(0, 1),
    _norm_dist(0, 1) { }

  ~Randomize() = default;

  int _seed = -1;
  std::mt19937 _gen;
  std::uniform_int_distribution<int> _bool_dist;
  std::uniform_int_distribution<int> _int_dist;
  std::uniform_real_distribution<float> _float_dist;
  std::normal_distribution<float> _norm_dist;
};
}  // namespace kahypar
