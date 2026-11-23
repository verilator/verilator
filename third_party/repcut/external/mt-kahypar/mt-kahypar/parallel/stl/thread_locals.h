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

#include <tbb/enumerable_thread_specific.h>
#include <tbb/parallel_for.h>

namespace mt_kahypar {

  namespace internals {
    template<typename T>
    using ThreadLocal = tbb::enumerable_thread_specific<T>;

    template<typename T, typename F>
    struct ThreadLocalFree {
      using RangeType = typename ThreadLocal<T>::range_type;
      using Iterator = typename ThreadLocal<T>::iterator;

      explicit ThreadLocalFree(F&& free_func) :
              _free_func(free_func) { }

      void operator()(RangeType& range) const {
        for ( Iterator it = range.begin(); it < range.end(); ++it ) {
          _free_func(*it);
        }
      }

      F _free_func;
    };
  } // namespace

  namespace parallel {
    template<typename T, typename F>
    static void parallel_free_thread_local_internal_data(internals::ThreadLocal<T>& local,
                                                         F&& free_func) {
      internals::ThreadLocalFree<T, F> thread_local_free(std::move(free_func));
      tbb::parallel_for(local.range(), thread_local_free);
    }
  }

  template<typename T>
  using tls_enumerable_thread_specific = tbb::enumerable_thread_specific<T, tbb::cache_aligned_allocator<T>, tbb::ets_key_per_instance>;

}