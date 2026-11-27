/*******************************************************************************
 * MIT License
 *
 * This file is part of KaHyPar.
 *
 * Copyright (C) 2017 Sebastian Schlag <sebastian.schlag@kit.edu>
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

#include "mt-kahypar/utils/randomize.h"

namespace mt_kahypar {
class LastRatingWins {
 public:
  MT_KAHYPAR_ATTRIBUTE_ALWAYS_INLINE static bool acceptEqual(const int) {
    return true;
  }

  LastRatingWins(const LastRatingWins&) = delete;
  LastRatingWins & operator= (const LastRatingWins &) = delete;

  LastRatingWins(LastRatingWins&&) = delete;
  LastRatingWins & operator= (LastRatingWins &&) = delete;

 protected:
  ~LastRatingWins() = default;
};

class FirstRatingWins {
 public:
  MT_KAHYPAR_ATTRIBUTE_ALWAYS_INLINE static bool acceptEqual(const int) {
    return false;
  }

  FirstRatingWins(const FirstRatingWins&) = delete;
  FirstRatingWins & operator= (const FirstRatingWins &) = delete;

  FirstRatingWins(FirstRatingWins&&) = delete;
  FirstRatingWins & operator= (FirstRatingWins &&) = delete;

 protected:
  ~FirstRatingWins() = default;
};

class RandomRatingWins {
 public:
  MT_KAHYPAR_ATTRIBUTE_ALWAYS_INLINE static bool acceptEqual(const int cpu_id) {
    return utils::Randomize::instance().flipCoin(cpu_id);
  }

  RandomRatingWins(const RandomRatingWins&) = delete;
  RandomRatingWins & operator= (const RandomRatingWins &) = delete;

  RandomRatingWins(RandomRatingWins&&) = delete;
  RandomRatingWins & operator= (RandomRatingWins &&) = delete;

 protected:
  ~RandomRatingWins() = default;
};
}  // namespace mt_kahypar
