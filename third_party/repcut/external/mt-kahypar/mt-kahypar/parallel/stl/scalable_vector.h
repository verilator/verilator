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

#include <vector>

#include <tbb/parallel_for.h>
#include <tbb/parallel_invoke.h>

#include "mt-kahypar/parallel/stl/allocator.h"
#include "mt-kahypar/macros.h"

namespace mt_kahypar {

template<typename T>
using vec = std::vector<T, parallel::scalable_allocator<T> >;  // shorter name

namespace parallel {
template <typename T>
using scalable_vector = vec<T>;

template<typename T>
static inline void free(scalable_vector<T>& vec) {
  scalable_vector<T> tmp_vec;
  vec = std::move(tmp_vec);
}

template<typename T>
MT_KAHYPAR_ATTRIBUTE_ALWAYS_INLINE static void parallel_free(scalable_vector<scalable_vector<T>>& vec) {
  tbb::parallel_for(UL(0), vec.size(), [&](const size_t i) {
    free(vec[i]);
  });
}

template<typename T1,
         typename T2>
MT_KAHYPAR_ATTRIBUTE_ALWAYS_INLINE static void parallel_free(scalable_vector<T1>& vec1,
                                                             scalable_vector<T2>& vec2) {
  tbb::parallel_invoke([&] {
    free(vec1);
  }, [&] {
    free(vec2);
  });
}

template<typename T1,
         typename T2,
         typename T3>
MT_KAHYPAR_ATTRIBUTE_ALWAYS_INLINE static void parallel_free(scalable_vector<T1>& vec1,
                                                             scalable_vector<T2>& vec2,
                                                             scalable_vector<T3>& vec3) {
  tbb::parallel_invoke([&] {
    free(vec1);
  }, [&] {
    free(vec2);
  }, [&] {
    free(vec3);
  });
}

template<typename T1,
         typename T2,
         typename T3,
         typename T4>
MT_KAHYPAR_ATTRIBUTE_ALWAYS_INLINE static void parallel_free(scalable_vector<T1>& vec1,
                                                             scalable_vector<T2>& vec2,
                                                             scalable_vector<T3>& vec3,
                                                             scalable_vector<T4>& vec4) {
  tbb::parallel_invoke([&] {
    free(vec1);
  }, [&] {
    free(vec2);
  }, [&] {
    free(vec3);
  }, [&] {
    free(vec4);
  });
}


template<typename T1,
         typename T2,
         typename T3,
         typename T4,
         typename T5>
MT_KAHYPAR_ATTRIBUTE_ALWAYS_INLINE static void parallel_free(scalable_vector<T1>& vec1,
                                                             scalable_vector<T2>& vec2,
                                                             scalable_vector<T3>& vec3,
                                                             scalable_vector<T4>& vec4,
                                                             scalable_vector<T5>& vec5) {
  tbb::parallel_invoke([&] {
    free(vec1);
  }, [&] {
    free(vec2);
  }, [&] {
    free(vec3);
  }, [&] {
    free(vec4);
  }, [&] {
    free(vec5);
  });
}

template<typename T1,
         typename T2,
         typename T3,
         typename T4,
         typename T5,
         typename T6>
MT_KAHYPAR_ATTRIBUTE_ALWAYS_INLINE static void parallel_free(scalable_vector<T1>& vec1,
                                                             scalable_vector<T2>& vec2,
                                                             scalable_vector<T3>& vec3,
                                                             scalable_vector<T4>& vec4,
                                                             scalable_vector<T5>& vec5,
                                                             scalable_vector<T6>& vec6) {
  tbb::parallel_invoke([&] {
    free(vec1);
  }, [&] {
    free(vec2);
  }, [&] {
    free(vec3);
  }, [&] {
    free(vec4);
  }, [&] {
    free(vec5);
  }, [&] {
    free(vec6);
  });
}

}  // namespace parallel


}  // namespace mt_kahypar
