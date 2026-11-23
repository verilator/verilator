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

#include <thread>
#include <memory>
#include <iterator>

#include <tbb/parallel_for.h>
#include <tbb/parallel_invoke.h>

#include "mt-kahypar/macros.h"
#include "mt-kahypar/parallel/memory_pool.h"
#include "mt-kahypar/parallel/stl/scalable_unique_ptr.h"
#include "mt-kahypar/utils/exception.h"

namespace mt_kahypar {
namespace ds {

template <typename T>
class Array {

  class ArrayIterator {

    public:
      using iterator_category = std::random_access_iterator_tag;
      using value_type = T;
      using reference = T&;
      using pointer = T*;
      using difference_type = std::ptrdiff_t;

      ArrayIterator() : _ptr(nullptr) { }
      explicit ArrayIterator(T* ptr) : _ptr(ptr) { }

      reference operator*() const {
        return *_ptr;
      }

      pointer operator->() const {
        return _ptr;
      }

      ArrayIterator& operator++() {
        ++_ptr;
        return *this;
      }

      ArrayIterator& operator--() {
        --_ptr;
        return *this;
      }

      ArrayIterator operator++(int) {
        ArrayIterator tmp_it(_ptr);
        ++_ptr;
        return tmp_it;
      }

      ArrayIterator operator--(int) {
        ArrayIterator tmp_it(_ptr);
        --_ptr;
        return tmp_it;
      }

      ArrayIterator operator+(const difference_type& n) const {
        return ArrayIterator(_ptr + n);
      }

      ArrayIterator& operator+=(const difference_type& n) {
        _ptr += n;
        return *this;
      }

      ArrayIterator operator-(const difference_type& n) const {
        return ArrayIterator(_ptr - n);
      }

      ArrayIterator& operator-=(const difference_type& n) {
        _ptr -= n;
        return *this;
      }

      reference operator[](const difference_type& n) const {
        return _ptr[n];
      }

      bool operator==(const ArrayIterator& other) const {
        return _ptr == other._ptr;
      }

      bool operator!=(const ArrayIterator& other) const {
        return _ptr != other._ptr;
      }

      bool operator<(const ArrayIterator& other) const {
        return _ptr < other._ptr;
      }

      bool operator>(const ArrayIterator& other) const {
        return _ptr > other._ptr;
      }

      bool operator<=(const ArrayIterator& other) const {
        return _ptr <= other._ptr;
      }

      bool operator>=(const ArrayIterator& other) const {
        return _ptr >= other._ptr;
      }

      difference_type operator-(const ArrayIterator& other) const {
        return (_ptr - other._ptr);
      }

      friend ArrayIterator operator+(const difference_type& n, const ArrayIterator& it) {
        return it + n;
      }
    private:
      T* _ptr;

  };

 public:

  // Type Traits
  using value_type      = T;
  using size_type       = size_t;
  using reference       = T&;
  using const_reference = const T&;
  using iterator        = ArrayIterator;
  using const_iterator  = const ArrayIterator;

  Array() :
    _group(""),
    _key(""),
    _size(0),
    _data(nullptr),
    _underlying_data(nullptr) { }

  Array(const size_type size,
         const value_type init_value = value_type()) :
    _group(""),
    _key(""),
    _size(0),
    _data(nullptr),
    _underlying_data(nullptr) {
    resize(size, init_value);
  }

  Array(const std::string& group,
         const std::string& key,
         const size_type size,
         const bool zero_initialize = false,
         const bool assign_parallel = true) :
    _group(""),
    _key(""),
    _size(size),
    _data(nullptr),
    _underlying_data(nullptr) {
    resize(group, key, size, zero_initialize, assign_parallel);
  }

  Array(const Array&) = delete;
  Array & operator= (const Array &) = delete;

  Array(Array&& other) :
    _group(std::move(other._group)),
    _key(std::move(other._key)),
    _size(other._size),
    _data(std::move(other._data)),
    _underlying_data(std::move(other._underlying_data)) {
    other._size = 0;
    other._data = nullptr;
    other._underlying_data = nullptr;
  }

  Array & operator=(Array&& other) {
    _group = std::move(other._group);
    _key = std::move(other._key);
    _size = other._size;
    _data = std::move(other._data);
    _underlying_data = std::move(other._underlying_data);
    other._size = 0;
    other._data = nullptr;
    other._underlying_data = nullptr;
    return *this;
  }

  ~Array() {
    if ( !_data && _underlying_data && !_group.empty() && !_key.empty() ) {
      // Memory was allocated from memory pool
      // => Release Memory
      parallel::MemoryPool::instance().release_mem_chunk(_group, _key);
    }
  }

  // ####################### Access Operators #######################

  // ! Returns a reference to the element at specified location pos
  reference operator[](const size_type pos) {
    ASSERT(pos < _size);
    return _underlying_data[pos];
  }

  // ! Returns a reference to the element at specified location pos
  const_reference operator[](const size_type pos) const {
    ASSERT(pos < _size);
    return _underlying_data[pos];
  }

  reference back() {
    ASSERT(_underlying_data && _size > 0);
    return _underlying_data[_size - 1];
  }

  const_reference back() const {
    ASSERT(_underlying_data && _size > 0);
    return _underlying_data[_size - 1];
  }

  value_type* data() {
    ASSERT(_underlying_data);
    return _underlying_data;
  }

  const value_type* data() const {
    ASSERT(_underlying_data);
    return _underlying_data;
  }

  // ####################### Iterators #######################

  iterator begin() {
    ASSERT(_underlying_data);
    return iterator(_underlying_data);
  }

  const_iterator begin() const {
    return cbegin();
  }

  const_iterator cbegin() const {
    ASSERT(_underlying_data);
    return const_iterator(_underlying_data);
  }

  iterator end() {
    ASSERT(_underlying_data);
    return iterator(_underlying_data + _size);
  }

  const_iterator end() const {
    return cend();
  }

  const_iterator cend() const {
    ASSERT(_underlying_data);
    return const_iterator(_underlying_data + _size);
  }

  // ####################### Capacity #######################

  bool empty() const {
    return _size == 0;
  }

  size_type size() const {
    return _size;
  }

  // ####################### Initialization #######################

  void resize(const size_type size,
              const value_type init_value = value_type(),
              const bool assign_parallel = true) {
    if ( _data || _underlying_data ) {
      throw SystemException("Memory of vector already allocated");
    }
    allocate_data(size);
    assign(size, init_value, assign_parallel);
  }

  void resizeNoAssign(const size_type size) {
    if ( _data || _underlying_data ) {
      throw SystemException("Memory of vector already allocated");
    }
    allocate_data(size);
  }

  void resize(const std::string& group,
              const std::string& key,
              const size_type size,
              const bool zero_initialize = false,
              const bool assign_parallel = true) {
    _size = size;
    char* data = parallel::MemoryPool::instance().request_mem_chunk(
      group, key, size, sizeof(value_type));
    if ( data ) {
      _group = group;
      _key = key;
      _underlying_data = reinterpret_cast<value_type*>(data);
      if ( zero_initialize ) {
        assign(size, value_type(), assign_parallel);
      }
    } else {
      resize_with_unused_memory(size, zero_initialize, assign_parallel);
    }
  }

  void resize_with_unused_memory(const size_type size,
                                 const bool zero_initialize = false,
                                 const bool assign_parallel = true) {
    _size = size;
    char* data = parallel::MemoryPool::instance().request_unused_mem_chunk(size, sizeof(value_type));
    if ( data ) {
      _underlying_data = reinterpret_cast<value_type*>(data);
      if ( zero_initialize ) {
        assign(size, value_type(), assign_parallel);
      }
    } else {
      resize(size, value_type(), assign_parallel);
    }
  }

  // ! Replaces the contents of the container
  void assign(const size_type count,
              const value_type value,
              const bool assign_parallel = true) {
    if ( _underlying_data ) {
      ASSERT(count <= _size);
      if ( assign_parallel ) {
        const size_t step = std::max(count / std::thread::hardware_concurrency(), UL(1));
        tbb::parallel_for(UL(0), count, step, [&](const size_type i) {
          for ( size_t j = i; j < std::min(i + step, count); ++j ) {
            _underlying_data[j] = value;
          }
        });
      } else {
        for ( size_t i = 0; i < count; ++i ) {
          _underlying_data[i] = value;
        }
      }
    } else {
      resize(count, value, assign_parallel);
    }
  }

 private:
  void allocate_data(const size_type size) {
    _data = parallel::make_unique<value_type>(size);
    _underlying_data = _data.get();
    _size = size;
  }

  std::string _group;
  std::string _key;
  size_type _size;
  parallel::tbb_unique_ptr<value_type> _data;
  value_type* _underlying_data;
};


}  // namespace ds


namespace parallel {

  template<typename T>
  static inline void free(ds::Array<T>& vec) {
    ds::Array<T> tmp_vec;
    vec = std::move(tmp_vec);
  }

  template<typename T1,
          typename T2>
  MT_KAHYPAR_ATTRIBUTE_ALWAYS_INLINE static void parallel_free(ds::Array<T1>& vec1,
                                                               ds::Array<T2>& vec2) {
    tbb::parallel_invoke([&] {
      free(vec1);
    }, [&] {
      free(vec2);
    });
  }

  template<typename T1,
          typename T2,
          typename T3>
  MT_KAHYPAR_ATTRIBUTE_ALWAYS_INLINE static void parallel_free(ds::Array<T1>& vec1,
                                                               ds::Array<T2>& vec2,
                                                               ds::Array<T3>& vec3) {
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
  MT_KAHYPAR_ATTRIBUTE_ALWAYS_INLINE static void parallel_free(ds::Array<T1>& vec1,
                                                               ds::Array<T2>& vec2,
                                                               ds::Array<T3>& vec3,
                                                               ds::Array<T4>& vec4) {
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
  MT_KAHYPAR_ATTRIBUTE_ALWAYS_INLINE static void parallel_free(ds::Array<T1>& vec1,
                                                               ds::Array<T2>& vec2,
                                                               ds::Array<T3>& vec3,
                                                               ds::Array<T4>& vec4,
                                                               ds::Array<T5>& vec5) {
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
  MT_KAHYPAR_ATTRIBUTE_ALWAYS_INLINE static void parallel_free(ds::Array<T1>& vec1,
                                                               ds::Array<T2>& vec2,
                                                               ds::Array<T3>& vec3,
                                                               ds::Array<T4>& vec4,
                                                               ds::Array<T5>& vec5,
                                                               ds::Array<T6>& vec6) {
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


}

}  // namespace mt_kahypar
