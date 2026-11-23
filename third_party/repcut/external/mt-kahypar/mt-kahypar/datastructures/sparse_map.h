/*******************************************************************************
 * MIT License
 *
 * This file is part of KaHyPar.
 *
 * Copyright (C) 2019 Tobias Heuer <tobias.heuer@kit.edu>
 * Copyright (C) 2016 Sebastian Schlag <sebastian.schlag@kit.edu>
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

/*
 * Sparse map based on sparse set representation of
 * Briggs, Preston, and Linda Torczon. "An efficient representation for sparse sets."
 * ACM Letters on Programming Languages and Systems (LOPLAS) 2.1-4 (1993): 59-69.
 */

#pragma once

#include <algorithm>
#include <limits>
#include <utility>
#include <vector>
#include <cmath>

#include "kahypar-resources/macros.h"
#include "kahypar-resources/meta/mandatory.h"

#include "mt-kahypar/macros.h"
#include "mt-kahypar/parallel/memory_pool.h"
#include "mt-kahypar/parallel/stl/scalable_vector.h"
#include "mt-kahypar/parallel/stl/scalable_unique_ptr.h"

namespace mt_kahypar {
namespace ds {

/*
 * Sparse map based on sparse set representation of
 * Briggs, Preston, and Linda Torczon. "An efficient representation for sparse sets."
 * ACM Letters on Programming Languages and Systems (LOPLAS) 2.1-4 (1993): 59-69.
 */

template <typename Key = Mandatory,
          typename Value = Mandatory,
          typename Derived = Mandatory>
class SparseMapBase {
 protected:
  struct MapElement {
    Key key;
    Value value;
  };

 public:
  SparseMapBase(const SparseMapBase&) = delete;
  SparseMapBase& operator= (const SparseMapBase&) = delete;

  SparseMapBase& operator= (SparseMapBase&&) = delete;

  size_t size() const {
    return _size;
  }

  void setMaxSize(const size_t max_size) {
    ASSERT(_sparse);
    _dense = reinterpret_cast<MapElement*>(_sparse + max_size);
  }

  bool contains(const Key key) const {
    return static_cast<const Derived*>(this)->containsImpl(key);
  }

  void add(const Key key, const Value value) {
    static_cast<Derived*>(this)->addImpl(key, value);
  }

  const MapElement* begin() const {
    return _dense;
  }

  const MapElement* end() const {
    return _dense + _size;
  }

  MapElement* begin() {
    return _dense;
  }

  MapElement* end() {
    return _dense + _size;
  }

  void clear() {
    static_cast<Derived*>(this)->clearImpl();
  }

  Value& operator[] (const Key key) {
    const size_t index = _sparse[key];
    if (!contains(key)) {
      _dense[_size] = MapElement { key, Value() };
      _sparse[key] = _size++;
      return _dense[_size - 1].value;
    }
    return _dense[index].value;
  }

  const Value & get(const Key key) const {
    ASSERT(contains(key), V(key));
    return _dense[_sparse[key]].value;
  }

  Value getOrDefault(const Key key) const {
    const size_t index = _sparse[key];
    if (!contains(key)) {
      return Value();
    }
    return _dense[index].value;
  }

  void freeInternalData() {
    _size = 0;
    _data = nullptr;
    _sparse = nullptr;
    _dense = nullptr;
  }

 protected:
  explicit SparseMapBase(const size_t max_size) :
    _size(0),
    _data(nullptr),
    _sparse(nullptr),
    _dense(nullptr) {
    allocate_data(max_size);
  }

  ~SparseMapBase() = default;

  SparseMapBase(SparseMapBase&& other) :
    _size(other._size),
    _data(std::move(other._data)),
    _sparse(std::move(other._sparse)),
    _dense(std::move(other._dense)) {
    other._size = 0;
    other._data = nullptr;
    other._sparse = nullptr;
    other._dense = nullptr;
  }

  void allocate_data(const size_t max_size) {
    ASSERT(!_data && !_sparse);
    const size_t num_elements = (max_size * sizeof(MapElement) + max_size * sizeof(size_t)) / sizeof(size_t);
    char* data = parallel::MemoryPool::instance().request_unused_mem_chunk(num_elements, sizeof(size_t));
    if ( data ) {
      _sparse = reinterpret_cast<size_t*>(data);
    } else {
      _data = parallel::make_unique<size_t>(num_elements);
      _sparse = reinterpret_cast<size_t*>(_data.get());
    }
    _dense = reinterpret_cast<MapElement*>(_sparse + max_size);
  }

  size_t _size;
  parallel::tbb_unique_ptr<size_t> _data;
  size_t* _sparse;
  MapElement* _dense;
};


template <typename Key = Mandatory,
          typename Value = Mandatory>
class SparseMap final : public SparseMapBase<Key, Value, SparseMap<Key, Value> >{
  using Base = SparseMapBase<Key, Value, SparseMap<Key, Value> >;
  friend Base;

 public:
  explicit SparseMap(const Key max_size) :
    Base(max_size) { }

  SparseMap(const SparseMap&) = delete;
  SparseMap& operator= (const SparseMap& other) = delete;

  SparseMap(SparseMap&& other) :
    Base(std::move(other)) { }

  SparseMap& operator= (SparseMap&& other) {
    _data = std::move(other._data);
    _sparse = std::move(other._sparse);
    _size = 0;
    _dense = std::move(other._dense);
    other._size = 0;
    other._data = nullptr;
    other._sparse = nullptr;
    other._dense = nullptr;
    return *this;
  }

  ~SparseMap() = default;

  void remove(const Key key) {
    const size_t index = _sparse[key];
    if (index < _size && _dense[index].key == key) {
      std::swap(_dense[index], _dense[_size - 1]);
      _sparse[_dense[index].key] = index;
      --_size;
    }
  }

 private:
  bool containsImpl(const Key key) const {
    const size_t index = _sparse[key];
    return index < _size && _dense[index].key == key;
  }


  void addImpl(const Key key, const Value value) {
    const size_t index = _sparse[key];
    if (index >= _size || _dense[index].key != key) {
      _dense[_size] = { key, value };
      _sparse[key] = _size++;
    }
  }

  void clearImpl() {
    _size = 0;
  }

  using Base::_data;
  using Base::_sparse;
  using Base::_dense;
  using Base::_size;
};

/*!
 * Sparse map implementation that uses a fixed size.
 * In contrast to the implementation in KaHyPar (see kahypar/datastructure/sparse_map.h),
 * which uses as size the cardinality of the key universe, hash collisions have to be handled
 * explicitly. Hash collisions are resolved with linear probing.
 * Advantage of the implementation is that it uses significantly less space than the
 * version in KaHyPar and should be therefore more cache-efficient.
 * Note, there is no fallback strategy if all slots of the sparse map are occupied by an
 * element. Please make sure that no more than MAP_SIZE elements are inserted into the
 * sparse map. Otherwise, the behavior is undefined.
 */
template <typename Key = Mandatory,
          typename Value = Mandatory>
class FixedSizeSparseMap {

  struct MapElement {
    Key key;
    Value value;
  };

  struct SparseElement {
    MapElement* element;
    size_t timestamp;
  };

 public:

  static constexpr size_t MAP_SIZE = 32768; // Size of sparse map is approx. 1 MB

  static_assert(MAP_SIZE && ((MAP_SIZE & (MAP_SIZE - 1)) == UL(0)), "Size of map is not a power of two!");

  explicit FixedSizeSparseMap(const Value initial_value) :
    _map_size(0),
    _initial_value(initial_value),
    _data(nullptr),
    _size(0),
    _timestamp(1),
    _sparse(nullptr),
    _dense(nullptr) {
    allocate(MAP_SIZE);
  }

  explicit FixedSizeSparseMap(const size_t max_size,
                              const Value initial_value) :
    _map_size(0),
    _initial_value(initial_value),
    _data(nullptr),
    _size(0),
    _timestamp(1),
    _sparse(nullptr),
    _dense(nullptr) {
    allocate(max_size);
  }

  FixedSizeSparseMap(const FixedSizeSparseMap&) = delete;
  FixedSizeSparseMap& operator= (const FixedSizeSparseMap& other) = delete;

  FixedSizeSparseMap(FixedSizeSparseMap&& other) :
    _map_size(other._map_size),
    _initial_value(other._initial_value),
    _data(std::move(other._data)),
    _size(other._size),
    _timestamp(other._timestamp),
    _sparse(std::move(other._sparse)),
    _dense(std::move(other._dense)) {
    other._data = nullptr;
    other._sparse = nullptr;
    other._dense = nullptr;
  }

  ~FixedSizeSparseMap() = default;

  size_t capacity() const {
    return _map_size;
  }

  size_t size() const {
    return _size;
  }

  const MapElement* begin() const {
    return _dense;
  }

  const MapElement* end() const {
    return _dense + _size;
  }

  MapElement* begin() {
    return _dense;
  }

  MapElement* end() {
    return _dense + _size;
  }

  void setMaxSize(const size_t max_size) {
    if ( max_size > _map_size ) {
      freeInternalData();
      allocate(max_size);
    }
  }

  bool contains(const Key key) const {
    SparseElement* s = find(key);
    return containsValidElement(key, s);
  }

  Value& operator[] (const Key key) {
    SparseElement* s = find(key);
    if ( containsValidElement(key, s) ) {
      ASSERT(s->element);
      return s->element->value;
    } else {
      return addElement(key, _initial_value, s)->value;
    }
  }

  const Value & get(const Key key) const {
    ASSERT(contains(key));
    return find(key)->element->value;
  }

  void clear() {
    _size = 0;
    ++_timestamp;
  }

  void freeInternalData() {
    _size = 0;
    _timestamp = 0;
    _data = nullptr;
    _sparse = nullptr;
    _dense = nullptr;
  }

 private:
  inline SparseElement* find(const Key key) const {
    ASSERT(_size < _map_size);
    size_t hash = key & ( _map_size - 1 );
    while ( _sparse[hash].timestamp == _timestamp ) {
      ASSERT(_sparse[hash].element);
      if ( _sparse[hash].element->key == key ) {
        return &_sparse[hash];
      }
      hash = (hash + 1) & ( _map_size - 1 );
    }
    return &_sparse[hash];
  }

  inline bool containsValidElement(const Key key,
                                   const SparseElement* s) const {
    unused(key);
    ASSERT(s);
    const bool is_contained = s->timestamp == _timestamp;
    ASSERT(!is_contained || s->element->key == key);
    return is_contained;
  }

  inline MapElement* addElement(const Key key,
                                const Value value,
                                SparseElement* s) {
    ASSERT(find(key) == s);
    _dense[_size] = MapElement { key, value };
    *s = SparseElement { &_dense[_size++], _timestamp };
    return s->element;
  }

  void allocate(const size_t size) {
    if ( _data == nullptr ) {
      _map_size = align_to_next_power_of_two(size);
      _data = std::make_unique<uint8_t[]>(
        _map_size * sizeof(MapElement) + _map_size * sizeof(SparseElement));
      _size = 0;
      _timestamp = 1;
      _sparse = reinterpret_cast<SparseElement*>(_data.get());
      _dense = reinterpret_cast<MapElement*>(_data.get() +  + sizeof(SparseElement) * _map_size);
      memset(_data.get(), 0, _map_size * (sizeof(MapElement) + sizeof(SparseElement)));
    }

  }

  size_t align_to_next_power_of_two(const size_t size) const {
    return std::pow(2.0, std::ceil(std::log2(static_cast<double>(size))));
  }

  size_t _map_size;
  const Value _initial_value;
  std::unique_ptr<uint8_t[]> _data;

  size_t _size;
  size_t _timestamp;
  SparseElement* _sparse;
  MapElement* _dense;
};


template <typename Key = Mandatory,
          typename Value = Mandatory,
          typename Derived = Mandatory>
class DynamicMapBase {

 public:
  static constexpr size_t INVALID_POS_MASK = ~(std::numeric_limits<size_t>::max() >> 1); // MSB is set
  static constexpr size_t INITIAL_CAPACITY = 16;

  explicit DynamicMapBase() :
    _capacity(32),
    _size(0),
    _timestamp(1),
    _data(nullptr) {
    initialize(INITIAL_CAPACITY);
  }

  DynamicMapBase(const DynamicMapBase&) = delete;
  DynamicMapBase& operator= (const DynamicMapBase& other) = delete;

  DynamicMapBase(DynamicMapBase&& other) = default;
  DynamicMapBase& operator= (DynamicMapBase&& other) = default;

  ~DynamicMapBase() = default;

  size_t capacity() const {
    return _capacity;
  }

  size_t size() const {
    return _size;
  }

  void initialize(const size_t capacity) {
    _size = 0;
    _capacity = align_to_next_power_of_two(capacity);
    _timestamp = 1;
    const size_t alloc_size = static_cast<const Derived*>(this)->size_in_bytes();
    _data = std::make_unique<uint8_t[]>(alloc_size);
    memset(_data.get(), 0, alloc_size);
    static_cast<Derived*>(this)->initializeImpl();
  }

  bool contains(const Key key) const {
    const size_t pos = find(key);
    return pos < INVALID_POS_MASK;
  }

  Value& operator[] (const Key key) {
    size_t pos = find(key);
    if ( pos < INVALID_POS_MASK ) {
      return getValue(pos);
    } else {
      if (_size + 1 > (_capacity * 2) / 5) {
        grow();
        pos = find(key);
      }
      return static_cast<Derived*>(this)->addElementImpl(key, Value(), pos & ~INVALID_POS_MASK);
    }
  }

  const Value& get(const Key key) const {
    ASSERT(contains(key));
    return getValue(find(key));
  }

  const Value* get_if_contained(const Key key) const {
    const size_t pos = find(key);
    if ( pos < INVALID_POS_MASK ) {
      return &getValue(pos);
    } else {
      return nullptr;
    }
  }

  void clear() {
    _size = 0;
    ++_timestamp;
  }

 private:
  inline size_t find(const Key key) const {
    return static_cast<const Derived*>(this)->findImpl(key);
  }

  void grow() {
    const size_t old_size = _size;
    const size_t old_capacity = _capacity;
    const size_t old_timestamp = _timestamp;
    const size_t new_capacity = 2UL * _capacity;
    const std::unique_ptr<uint8_t[]> old_data = std::move(_data);
    const uint8_t* old_data_begin = old_data.get();
    initialize(new_capacity);
    static_cast<Derived*>(this)->rehashImpl(
      old_data_begin, old_size, old_capacity, old_timestamp);
  }

  MT_KAHYPAR_ATTRIBUTE_ALWAYS_INLINE Value& getValue(const size_t pos) const {
    return static_cast<const Derived*>(this)->valueAtPos(pos);
  }

  constexpr size_t align_to_next_power_of_two(const size_t size) const {
    ASSERT(size > 0);
    return std::pow(2.0, std::ceil(std::log2(static_cast<double>(size))));
  }

 protected:
  size_t _capacity;
  size_t _size;
  size_t _timestamp;
  std::unique_ptr<uint8_t[]> _data;
};



template <typename Key = Mandatory,
          typename Value = Mandatory>
class DynamicSparseMap final : public DynamicMapBase<Key, Value, DynamicSparseMap<Key, Value>> {

  struct MapElement {
    Key key;
    Value value;
  };

  struct SparseElement {
    MapElement* element;
    size_t timestamp;
  };

  using Base = DynamicMapBase<Key, Value, DynamicSparseMap<Key, Value>>;
  using Base::INVALID_POS_MASK;

  friend Base;

 public:
  explicit DynamicSparseMap() :
    Base(),
    _sparse(nullptr),
    _dense(nullptr) {
    Base::initialize(_capacity);
  }

  DynamicSparseMap(const DynamicSparseMap&) = delete;
  DynamicSparseMap& operator= (const DynamicSparseMap& other) = delete;

  DynamicSparseMap(DynamicSparseMap&& other) = default;
  DynamicSparseMap& operator= (DynamicSparseMap&& other) = default;

  ~DynamicSparseMap() = default;

  const MapElement* begin() const {
    return _dense;
  }

  const MapElement* end() const {
    return _dense + _size;
  }

  MapElement* begin() {
    return _dense;
  }

  MapElement* end() {
    return _dense + _size;
  }

  void freeInternalData() {
    _size = 0;
    _timestamp = 0;
    _data = nullptr;
    _sparse = nullptr;
    _dense = nullptr;
  }

  size_t size_in_bytes() const {
    return _capacity * (sizeof(SparseElement) + sizeof(MapElement));
  }

 private:
  MT_KAHYPAR_ATTRIBUTE_ALWAYS_INLINE size_t findImpl(const Key key) const {
    size_t hash = key & (_capacity - 1);
    while ( _sparse[hash].timestamp == _timestamp ) {
      if ( _sparse[hash].element->key == key ) {
        return hash;
      }
      hash = (hash + 1) & (_capacity - 1);
    }
    return hash | INVALID_POS_MASK;
  }

  MT_KAHYPAR_ATTRIBUTE_ALWAYS_INLINE Value& valueAtPos(const size_t pos) const {
    ASSERT(pos < _capacity);
    ASSERT(_sparse[pos].timestamp == _timestamp);
    return _sparse[pos].element->value;
  }

  MT_KAHYPAR_ATTRIBUTE_ALWAYS_INLINE Value& addElementImpl(const Key key, const Value value, const size_t pos) {
    ASSERT(pos < _capacity);
    _dense[_size] = MapElement { key, value };
    _sparse[pos] = SparseElement { &_dense[_size++], _timestamp };
    return _sparse[pos].element->value;
  }

  void initializeImpl() {
    _sparse = reinterpret_cast<SparseElement*>(_data.get());
    _dense = reinterpret_cast<MapElement*>(_data.get() + sizeof(SparseElement) * _capacity);
  }

  void rehashImpl(const uint8_t* old_data_begin,
                  const size_t old_size,
                  const size_t old_capacity,
                  const size_t) {
    const MapElement* elements = reinterpret_cast<const MapElement*>(
      old_data_begin + sizeof(SparseElement) * old_capacity);
    for (size_t i = 0; i < old_size; ++i ) {
      const size_t pos = findImpl(elements[i].key) & ~INVALID_POS_MASK;
      addElementImpl(elements[i].key, elements[i].value, pos);
    }
    ASSERT(old_size == _size);
  }


  using Base::_capacity;
  using Base::_size;
  using Base::_timestamp;
  using Base::_data;

  SparseElement* _sparse;
  MapElement* _dense;
};


template <typename Key = Mandatory,
          typename Value = Mandatory>
class DynamicFlatMap final : public DynamicMapBase<Key, Value, DynamicFlatMap<Key, Value>> {

  struct MapElement {
    Key key;
    Value value;
    size_t timestamp;
  };

  using Base = DynamicMapBase<Key, Value, DynamicFlatMap<Key, Value>>;
  using Base::INVALID_POS_MASK;
  friend Base;

 public:
  explicit DynamicFlatMap() :
    Base(),
    _elements(nullptr) {
    initializeImpl();
  }

  DynamicFlatMap(const DynamicFlatMap&) = delete;
  DynamicFlatMap& operator= (const DynamicFlatMap& other) = delete;

  DynamicFlatMap(DynamicFlatMap&& other) = default;
  DynamicFlatMap& operator= (DynamicFlatMap&& other) = default;

  ~DynamicFlatMap() = default;

  void freeInternalData() {
    _size = 0;
    _timestamp = 0;
    _data = nullptr;
    _elements = nullptr;
  }

  size_t size_in_bytes() const {
    return _capacity * sizeof(MapElement);
  }

 private:
  MT_KAHYPAR_ATTRIBUTE_ALWAYS_INLINE size_t findImpl(const Key key) const {
    size_t hash = key & (_capacity - 1);
    while ( _elements[hash].timestamp == _timestamp ) {
      if ( _elements[hash].key == key ) {
        return hash;
      }
      hash = (hash + 1) & (_capacity - 1);
    }
    return hash | INVALID_POS_MASK;
  }

  MT_KAHYPAR_ATTRIBUTE_ALWAYS_INLINE Value& valueAtPos(const size_t pos) const {
    ASSERT(pos < _capacity);
    ASSERT(_elements[pos].timestamp == _timestamp);
    return _elements[pos].value;
  }

  MT_KAHYPAR_ATTRIBUTE_ALWAYS_INLINE Value& addElementImpl(Key key, Value value, const size_t pos) {
    ASSERT(pos < _capacity);
    _elements[pos] = MapElement { key, value, _timestamp };
    _size++;
    return _elements[pos].value;
  }

  void initializeImpl() {
    _elements = reinterpret_cast<MapElement*>(_data.get());
  }

  void rehashImpl(const uint8_t* old_data_begin,
                  const size_t old_size,
                  const size_t old_capacity,
                  const size_t old_timestamp) {
    unused(old_size);
    const MapElement* elements = reinterpret_cast<const MapElement*>(old_data_begin);
    for (size_t i = 0; i < old_capacity; ++i ) {
      if ( elements[i].timestamp == old_timestamp ) {
        const size_t pos = findImpl(elements[i].key) & ~INVALID_POS_MASK;
        addElementImpl(elements[i].key, elements[i].value, pos);
      }
    }
    ASSERT(old_size == _size);
  }

  using Base::_capacity;
  using Base::_size;
  using Base::_timestamp;
  using Base::_data;
  MapElement* _elements;
};


struct EmptyStruct { };
template<typename Key>
using DynamicSparseSet = DynamicSparseMap<Key, EmptyStruct>;

} // namespace ds
} // namespace mt_kahypar