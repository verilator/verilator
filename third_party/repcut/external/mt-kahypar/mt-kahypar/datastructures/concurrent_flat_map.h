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

#include "repcut_serial.h"

#include <algorithm>
#include <atomic>
#include <limits>
#include <utility>
#include <vector>
#include <cmath>

#include "kahypar-resources/macros.h"
#include "kahypar-resources/meta/mandatory.h"

#include "mt-kahypar/macros.h"

namespace mt_kahypar {
namespace ds {

template <typename Key = Mandatory,
          typename Value = Mandatory>
class ConcurrentFlatMap {

  struct MapElement {
    Key key;
    Value value;
    int32_t timestamp;
  };

 public:
  static constexpr size_t MAP_SIZE = 32768; // Size of sparse map is approx. 1 MB

  static_assert(MAP_SIZE && ((MAP_SIZE & (MAP_SIZE - 1)) == UL(0)), "Size of map is not a power of two!");

  explicit ConcurrentFlatMap() :
    _map_size(0),
    _data(nullptr),
    _threshold(2),
    _map() {
    allocate(MAP_SIZE);
  }

  explicit ConcurrentFlatMap(const size_t max_size) :
    _map_size(0),
    _data(nullptr),
    _threshold(2),
    _map(nullptr) {
    allocate(max_size);
  }

  ConcurrentFlatMap(const ConcurrentFlatMap&) = delete;
  ConcurrentFlatMap& operator= (const ConcurrentFlatMap& other) = delete;

  ConcurrentFlatMap(ConcurrentFlatMap&& other) :
    _map_size(other._map_size),
    _data(std::move(other._data)),
    _threshold(other._threshold),
    _map(std::move(other._map)) {
    other._data = nullptr;
    other._map = nullptr;
  }

  ~ConcurrentFlatMap() = default;

  size_t capacity() const {
    return _map_size;
  }

  void setMaxSize(const size_t max_size) {
    if ( 4 * max_size > _map_size ) {
      freeInternalData();
      allocate(4 * max_size);
    }
  }

  Value& operator[] (const Key key) {
    size_t hash = key & ( _map_size - 1 );
    MapElement* elem = &_map[hash];
    int32_t expected = elem->timestamp;
    int32_t desired = _threshold - 1;
    while ( ! ( expected == _threshold && elem->key == key ) ) {
      if ( expected < desired &&
           repcut_serial::Ref(elem->timestamp)
               .compare_exchange_strong(expected, desired, std::memory_order_acq_rel, std::memory_order_relaxed) ) {
        elem->key = key;
        elem->value = Value();
        elem->timestamp = _threshold;
        break;
      }
      hash = find(key, hash + 1);
      elem = &_map[hash];
      expected = elem->timestamp;
    }

    return elem->value;
  }

  Value* get_if_contained(const Key key) {
    size_t hash = find(key, key & ( _map_size - 1 ));
    MapElement* elem = &_map[hash];
    return elem->timestamp == _threshold && elem->key == key ? &elem->value : nullptr;
  }

  void clear() {
    if ( _threshold >= std::numeric_limits<int32_t>::max() - 2 ) {
      _threshold = 0;
      for ( size_t i = 0; i < _map_size; ++i ) {
        _map[i].timestamp = 0;
      }
    }
    _threshold += 2;
  }

  void freeInternalData() {
    _map_size = 0;
    _threshold = 0;
    _data = nullptr;
    _map = nullptr;
  }

 private:
  MT_KAHYPAR_ATTRIBUTE_ALWAYS_INLINE size_t find(const Key key,
                                                 const size_t start_hash) const {
    size_t hash = start_hash & ( _map_size - 1 );
    while ( _map[hash].timestamp == _threshold ) {
      if ( _map[hash].key == key ) {
        return hash;
      }
      hash = (hash + 1) & ( _map_size - 1 );
    }
    return hash;
  }

  void allocate(const size_t size) {
    if ( _data == nullptr ) {
      _map_size = align_to_next_power_of_two(size);
      _data = std::make_unique<uint8_t[]>(_map_size * sizeof(MapElement));
      _threshold = 2;
      _map = reinterpret_cast<MapElement*>(_data.get());
      memset(_data.get(), 0, _map_size * sizeof(MapElement));
    }
  }

  size_t align_to_next_power_of_two(const size_t size) const {
    return std::pow(2.0, std::ceil(std::log2(static_cast<double>(size))));
  }

  size_t _map_size;
  std::unique_ptr<uint8_t[]> _data;

  int32_t _threshold;
  MapElement* _map;
};

} // namespace ds
} // namespace mt_kahypar
