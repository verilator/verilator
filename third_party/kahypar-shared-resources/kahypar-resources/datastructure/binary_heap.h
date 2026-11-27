/*******************************************************************************
 * MIT License
 *
 * This file is part of KaHyPar.
 *
 * Copyright (C) 2015-2016 Sebastian Schlag <sebastian.schlag@kit.edu>
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
#include <functional>
#include <limits>
#include <memory>
#include <vector>

#include "kahypar-resources/macros.h"

namespace kahypar {
namespace ds {
// Base-Traits for binary heap
template <typename Derived>
class BinaryHeapTraits;

template <class Derived>
class BinaryHeapBase {
 private:
  static constexpr bool enable_heavy_assert = false;

  using KeyType = typename BinaryHeapTraits<Derived>::KeyType;
  using IDType = typename BinaryHeapTraits<Derived>::IDType;
  using Comparator = typename BinaryHeapTraits<Derived>::Comparator;

 protected:
  struct HeapElement {
    explicit HeapElement(const KeyType& key_ = BinaryHeapTraits<Derived>::sentinel(),
                         const IDType& id_ = 0) :
      id(id_),
      key(key_) { }

    IDType id;
    KeyType key;
  };

  explicit BinaryHeapBase(const IDType& size) :
    _heap(std::make_unique<HeapElement[]>(static_cast<size_t>(size) + 1)),
    _handles(std::make_unique<size_t[]>(size)),
    _compare(),
    _next_slot(0),
    _max_size(size + 1) {
    for (size_t i = 0; i < static_cast<size_t>(size); ++i) {
      _heap[i] = HeapElement(BinaryHeapTraits<Derived>::sentinel());
      _handles[i] = 0;
    }
    _heap[size] = HeapElement(BinaryHeapTraits<Derived>::sentinel());
    ++_next_slot;  // _heap[0] is sentinel
  }

 public:
  BinaryHeapBase(const BinaryHeapBase&) = delete;
  BinaryHeapBase& operator= (const BinaryHeapBase&) = delete;

  BinaryHeapBase(BinaryHeapBase&&) = default;
  BinaryHeapBase& operator= (BinaryHeapBase&&) = default;

  ~BinaryHeapBase() = default;

  size_t size() const {
    return _next_slot - 1;
  }

  bool empty() const {
    return size() == 0;
  }

  inline const KeyType & getKey(const IDType& id) const {
    ASSERT(isReached(id, _handles[id]), "Accessing invalid element:" << id);
    return _heap[_handles[id]].key;
  }

  inline bool isReached(const IDType& id, const size_t& handle) const {
    return handle < _next_slot && id == _heap[handle].id;
  }

  inline bool contains(const IDType& id) const {
    const size_t handle = _handles[id];
    return isReached(id, handle) && handle != 0;
  }

  inline void clear() {
    _next_slot = 1;  // remove anything but the sentinel
    ASSERT(_heap[0].key == BinaryHeapTraits<Derived>::sentinel(), "Sentinel element missing");
  }

  KAHYPAR_ATTRIBUTE_ALWAYS_INLINE void push(const IDType& id, const KeyType& key) {
    ASSERT(!contains(id), "pushing already contained element" << id);
    ASSERT(_next_slot + 1 <= _max_size, "heap size overflow");

    const size_t handle = _next_slot++;
    _heap[handle].key = key;
    _heap[handle].id = id;
    _handles[id] = handle;
    upHeap(handle);
    ASSERT(_heap[_handles[id]].key == key, "Push failed - wrong key:"
           << _heap[_handles[id]].key << "!=" << key);
    ASSERT(_heap[_handles[id]].id == id, "Push failed - wrong id:"
           << _heap[_handles[id]].id << "!=" << id);
  }

  inline void decreaseKey(const IDType& id, const KeyType& new_key) {
    ASSERT(contains(id), "Calling decreaseKey for element not contained in Queue:" << id);

    const size_t handle = _handles[id];
    _heap[handle].key = new_key;
    static_cast<Derived*>(this)->decreaseKeyImpl(handle);
    ASSERT(_heap[_handles[id]].key == new_key, "decreaseKey failed - wrong key:" <<
           _heap[_handles[id]].key << "!=" << new_key);
    ASSERT(_heap[_handles[id]].id == id, "decreaseKey failed - wrong id" <<
           _heap[_handles[id]].id << "!=" << id);
  }

  inline void increaseKey(const IDType& id, const KeyType& new_key) {
    ASSERT(contains(id), "Calling increaseKey for element not contained in Queue:" << id);

    const size_t handle = _handles[id];
    _heap[handle].key = new_key;
    static_cast<Derived*>(this)->increaseKeyImpl(handle);
    ASSERT(_heap[_handles[id]].key == new_key, "increaseKey failed - wrong key:" <<
           _heap[_handles[id]].key << "!=" << new_key);
    ASSERT(_heap[_handles[id]].id == id, "increaseKey failed - wrong id" <<
           _heap[_handles[id]].id << "!=" << id);
  }

  inline void decreaseKeyBy(const IDType& id, const KeyType& key_delta) {
    ASSERT(contains(id), "Calling decreaseKeyBy for element not contained in Queue:" << id);

#ifdef KAHYPAR_USE_ASSERTIONS
    const KeyType old_key = _heap[_handles[id]].key;
#endif
    const size_t handle = _handles[id];
    _heap[handle].key -= key_delta;
    static_cast<Derived*>(this)->decreaseKeyImpl(handle);
    ASSERT(_heap[_handles[id]].key == old_key - key_delta, "wrong key:" <<
           _heap[_handles[id]].key << "!=" << old_key + key_delta);
    ASSERT(_heap[_handles[id]].id == id, "wrong id" <<
           _heap[_handles[id]].id << "!=" << id);
  }

  inline void increaseKeyBy(const IDType& id, const KeyType& key_delta) {
    ASSERT(contains(id), "Calling increaseKeyBy for element not contained in Queue:" << id);

#ifdef KAHYPAR_USE_ASSERTIONS
    const KeyType old_key = _heap[_handles[id]].key;
#endif
    const size_t handle = _handles[id];
    _heap[handle].key += key_delta;
    static_cast<Derived*>(this)->increaseKeyImpl(handle);
    ASSERT(_heap[_handles[id]].key == old_key + key_delta, "wrong key:" <<
           _heap[_handles[id]].key << "!=" << old_key + key_delta);
    ASSERT(_heap[_handles[id]].id == id, "wrong id" <<
           _heap[_handles[id]].id << "!=" << id);
  }

  inline void remove(const IDType& id) {
    ASSERT(contains(id), "trying to delete element not in heap:" << id);

    const size_t node_handle = _handles[id];
    const size_t swap_handle = _next_slot - 1;
    if (node_handle != swap_handle) {
      const KeyType node_key = _heap[node_handle].key;
      _handles[_heap[swap_handle].id] = node_handle;
      _handles[id] = 0;
      _heap[node_handle] = _heap[swap_handle];
      --_next_slot;
      if (_compare(node_key, _heap[node_handle].key)) {
        upHeap(node_handle);
      } else if (_compare(_heap[node_handle].key, node_key)) {
        downHeap(node_handle);
      }
    } else {
      --_next_slot;
      _handles[id] = 0;
    }
  }

  inline void updateKey(const IDType& id, const KeyType& new_key) {
    ASSERT(contains(id), "Calling updateKey for element not contained in Queue:" << id);

    const size_t handle = _handles[id];
    if (_compare(new_key, _heap[handle].key)) {
      _heap[handle].key = new_key;
      downHeap(handle);
    } else {
      _heap[handle].key = new_key;
      upHeap(handle);
    }
    ASSERT(_heap[_handles[id]].key == new_key, "updateKey failed - wrong key:" <<
           _heap[_handles[id]].key << "!=" << new_key);
    ASSERT(_heap[_handles[id]].id == id, "updateKey failed - wrong id" <<
           _heap[_handles[id]].id << "!=" << id);
  }

  inline void updateKeyBy(const IDType& id, const KeyType& key_delta) {
    ASSERT(contains(id), "Calling updateKeyBy for element not contained in Queue:" << id);

#ifdef KAHYPAR_USE_ASSERTIONS
    const KeyType old_key = _heap[_handles[id]].key;
#endif
    const size_t handle = _handles[id];
    _heap[handle].key += key_delta;
    if (_compare(key_delta, 0)) {
      downHeap(handle);
    } else {
      upHeap(handle);
    }
    ASSERT(_heap[_handles[id]].key == old_key + key_delta, "wrong key:" <<
           _heap[_handles[id]].key << "!=" << old_key + key_delta);
    ASSERT(_heap[_handles[id]].id == id, "wrong id" <<
           _heap[_handles[id]].id << "!=" << id);
  }

  inline void pop() {
    ASSERT(!empty(), "Deleting from empty heap");

    const size_t handle = _handles[_heap[1].id];
    const size_t swap_handle = _next_slot - 1;
    _handles[_heap[swap_handle].id] = 1;
    _handles[_heap[handle].id] = 0;
    _heap[1] = _heap[swap_handle];
    --_next_slot;
    if (!empty()) {
      downHeap(1);
    }
    HEAVY_DATA_STRUCTURE_ASSERT(isHeap(), "Heap invariant violated!");
  }

  inline const IDType & top() const {
    ASSERT(!empty(), "Heap is empty");
    return _heap[1].id;
  }

  inline const KeyType & topKey() const {
    ASSERT(!empty(), "Heap is empty");
    return _heap[1].key;
  }

 protected:
  KAHYPAR_ATTRIBUTE_ALWAYS_INLINE void upHeap(size_t heap_position) {
    ASSERT(heap_position != 0, "calling upHeap for the sentinel");
    ASSERT(_next_slot > heap_position, "position specified larger than heap size");

    const KeyType rising_key = _heap[heap_position].key;
    const IDType rising_id = _heap[heap_position].id;
    size_t next_position = heap_position >> 1;
    while (_compare(_heap[next_position].key, rising_key)) {
      ASSERT(next_position != 0, "Swapping sentinel.");
      _heap[heap_position] = _heap[next_position];
      _handles[_heap[heap_position].id] = heap_position;
      heap_position = next_position;
      next_position >>= 1;
    }

    _heap[heap_position].key = rising_key;
    _heap[heap_position].id = rising_id;
    _handles[rising_id] = heap_position;
    HEAVY_DATA_STRUCTURE_ASSERT(isHeap(), "Heap invariant violated!");
  }

  KAHYPAR_ATTRIBUTE_ALWAYS_INLINE void downHeap(size_t heap_position) {
    ASSERT(0 != heap_position, "calling downHeap for the sentinel");
    ASSERT(_next_slot > heap_position, "position specified larger than heap size");
    const KeyType dropping_key = _heap[heap_position].key;
    const IDType dropping_id = _heap[heap_position].id;
    const size_t heap_size = _next_slot;
    size_t compare_position = heap_position << 1 | 1;  // heap_position * 2 + 1
    while (compare_position < heap_size &&
           _compare(dropping_key,
                    _heap[compare_position = compare_position -
                                             (_compare(_heap[compare_position].key,
                                                       _heap[compare_position - 1].key))].key)) {
      _heap[heap_position] = _heap[compare_position];
      _handles[_heap[heap_position].id] = heap_position;
      heap_position = compare_position;
      compare_position = compare_position << 1 | 1;
    }

    // check for possible last single child
    if ((heap_size == compare_position) && _compare(dropping_key, _heap[compare_position -= 1].key)) {
      _heap[heap_position] = _heap[compare_position];
      _handles[_heap[heap_position].id] = heap_position;
      heap_position = compare_position;
    }

    _heap[heap_position].key = dropping_key;
    _heap[heap_position].id = dropping_id;
    _handles[dropping_id] = heap_position;
    HEAVY_DATA_STRUCTURE_ASSERT(isHeap(), "Heap invariant violated!");
  }

  bool isHeap() const {
    for (size_t i = 1; i < _next_slot; ++i) {
      if (_compare(_heap[i / 2].key, _heap[i].key)) {
        return false;
      }
    }
    return true;
  }

  friend void swap(BinaryHeapBase& a, BinaryHeapBase& b) {
    using std::swap;
    swap(a._heap, b._heap);
    swap(a._handles, b._handles);
    swap(a._compare, b._compare);
    swap(a._next_slot, b._next_slot);
    swap(a._max_size, b._max_size);
  }

  std::unique_ptr<HeapElement[]> _heap;
  std::unique_ptr<size_t[]> _handles;

  Comparator _compare;
  unsigned int _next_slot;
  size_t _max_size;
};

template <typename IDType_, typename KeyType_>
class BinaryMaxHeap final : public BinaryHeapBase<BinaryMaxHeap<IDType_, KeyType_> >{
  using Base = BinaryHeapBase<BinaryMaxHeap<IDType_, KeyType_> >;
  friend Base;

 public:
  using IDType = typename BinaryHeapTraits<BinaryMaxHeap>::IDType;
  using KeyType = typename BinaryHeapTraits<BinaryMaxHeap>::KeyType;

  // Second parameter is used to satisfy EnhancedBucketPQ interface
  explicit BinaryMaxHeap(const IDType& storage_initializer,
                         const KeyType& UNUSED(unused) = 0) :
    Base(storage_initializer) { }

  friend void swap(BinaryMaxHeap& a, BinaryMaxHeap& b) {
    using std::swap;
    swap(static_cast<Base&>(a), static_cast<Base&>(b));
  }

 protected:
  inline void decreaseKeyImpl(const size_t handle) {
    Base::downHeap(handle);
  }

  inline void increaseKeyImpl(const size_t handle) {
    Base::upHeap(handle);
  }
};

template <typename IDType_, typename KeyType_>
class BinaryMinHeap final : public BinaryHeapBase<BinaryMinHeap<IDType_, KeyType_> >{
  using Base = BinaryHeapBase<BinaryMinHeap<IDType_, KeyType_> >;
  friend Base;

 public:
  using IDType = typename BinaryHeapTraits<BinaryMinHeap>::IDType;
  using KeyType = typename BinaryHeapTraits<BinaryMinHeap>::KeyType;

  // Second parameter is used to satisfy EnhancedBucketPQ interface
  explicit BinaryMinHeap(const IDType& storage_initializer,
                         const KeyType& UNUSED(unused) = 0) :
    Base(storage_initializer) { }

  friend void swap(BinaryMinHeap& a, BinaryMinHeap& b) {
    using std::swap;
    swap(static_cast<Base&>(a), static_cast<Base&>(b));
  }

 protected:
  inline void decreaseKeyImpl(const size_t handle) {
    Base::upHeap(handle);
  }

  inline void increaseKeyImpl(const size_t handle) {
    Base::downHeap(handle);
  }
};


// Traits specialization for max heap:
template <typename IDType_, typename KeyType_>
class BinaryHeapTraits<BinaryMaxHeap<IDType_, KeyType_> >{
 public:
  using IDType = IDType_;
  using KeyType = KeyType_;
  using Comparator = std::less<KeyType>;

  static constexpr KeyType sentinel() {
    return std::numeric_limits<KeyType_>::max();
  }
};

// Traits specialization for min heap:
template <typename IDType_, typename KeyType_>
class BinaryHeapTraits<BinaryMinHeap<IDType_, KeyType_> >{
 public:
  using IDType = IDType_;
  using KeyType = KeyType_;
  using Comparator = std::greater<KeyType>;

  static constexpr KeyType sentinel() {
    return std::numeric_limits<KeyType_>::lowest();
  }
};
}  // namespace ds
}  // namespace kahypar
