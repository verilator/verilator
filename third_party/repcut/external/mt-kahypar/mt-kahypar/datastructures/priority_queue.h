/*******************************************************************************
 * MIT License
 *
 * This file is part of Mt-KaHyPar.
 *
 * Copyright (C) 2020 Lars Gottesbüren <lars.gottesbueren@kit.edu>
 * Copyright (C) 2020 Tobias Heuer <tobias.heuer@kit.edu>
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
#include <cstdint>
#include <functional>
#include <algorithm>
#include <cassert>

#include "mt-kahypar/parallel/stl/scalable_vector.h"

namespace mt_kahypar {

using PosT = uint32_t;
static constexpr PosT invalid_position = std::numeric_limits<PosT>::max();

namespace ds {

template<typename KeyT, typename IdT, typename Comparator = std::less<KeyT>, uint32_t arity = 4>
class Heap {
static constexpr bool enable_heavy_assert = false;
public:
  static_assert(arity > 1);

  explicit Heap(PosT* positions, size_t positions_size) :
    comp(),
    heap(),
    positions(positions),
    positions_size(positions_size) { }

  IdT top() const {
    return heap[0].id;
  }

  KeyT topKey() const {
    return heap[0].key;
  }

  void deleteTop() {
    assert(!empty());
    positions[heap[0].id] = invalid_position;
    positions[heap.back().id] = 0;
    heap[0] = heap.back();
    heap.pop_back();
    if (!empty()) {
      siftDown(0);
    }
  }

  void insert(const IdT e, const KeyT k) {
    ASSERT(!contains(e));
    ASSERT(size() < positions_size);
    const PosT pos = size();
    positions[e] = pos;
    heap.push_back({k, e});
    siftUp(pos);
  }

  void remove(const IdT e) {
    assert(!empty() && contains(e));
    PosT pos = positions[e];
    const KeyT removedKey = heap[pos].key, lastKey = heap.back().key;
    heap[pos] = heap.back();
    positions[heap.back().id] = pos;
    positions[e] = invalid_position;
    heap.pop_back();
    if (pos == size()) {
      return;
    }
    if (comp(removedKey, lastKey)) {
      siftUp(pos);
    } else {
      siftDown(pos);
    }
  }

  // assumes semantics of comp = std::less, i.e. we have a MaxHeap and increaseKey moves the element up the tree. if comp = std::greater, increaseKey will still move the element up the tree
  void increaseKey(const IdT e, const KeyT newKey) {
    assert(contains(e));
    const PosT pos = positions[e];
    assert(comp(heap[pos].key, newKey));
    heap[pos].key = newKey;
    siftUp(pos);
  }

  // assumes semantics of comp = std::less, i.e. we have a MaxHeap and decreaseKey moves the element down the tree
  void decreaseKey(const IdT e, const KeyT newKey) {
    assert(contains(e));
    const PosT pos = positions[e];
    assert(comp(newKey, heap[pos].key));
    heap[pos].key = newKey;
    siftDown(pos);
  }

  void adjustKey(const IdT e, const KeyT newKey) {
    assert(contains(e));
    const PosT pos = positions[e];
    if (comp(heap[pos].key, newKey)) {
      increaseKey(e, newKey);
    } else if (comp(newKey, heap[pos].key)) {
      decreaseKey(e, newKey);
    }
  }

  KeyT getKey(const IdT e) const {
    assert(contains(e));
    return heap[positions[e]].key;
  }

  void insertOrAdjustKey(const IdT e, const KeyT newKey) {
    if (contains(e)) {
      adjustKey(e, newKey);
    } else {
      insert(e, newKey);
    }
  }

  void clear() {
    heap.clear();
  }

  bool contains(const IdT e) const {
    assert(fits(e));
    return positions[e] < heap.size() && heap[positions[e]].id == e;
  }

  PosT size() const {
    return static_cast<PosT>(heap.size());
  }

  bool empty() const {
    return size() == 0;
  }

  KeyT keyAtPos(const PosT pos) const {
    return heap[pos].key;
  }

  KeyT keyOf(const IdT id) const {
    return heap[positions[id]].key;
  }

  IdT at(const PosT pos) const {
    return heap[pos].id;
  }

  void setHandle(PosT* pos, size_t pos_size) {
    clear();
    positions = pos;
    positions_size = pos_size;
  }

  void print() {
    for (PosT i = 0; i < size(); ++i) {
      std::cout << "(" << heap[i].id << "," << heap[i].key << ")" << " ";
    }
    std::cout << std::endl;
  }

  size_t size_in_bytes() const {
    return heap.capacity() * sizeof(HeapElement);
  }


protected:

  bool isHeap() const {
    for (PosT i = 1; i < size(); ++i) {
      if (comp(heap[parent(i)].key, heap[i].key)) {
        LOG << "heap property violation" << V(i) << V(parent(i)) << V(arity) << V(heap[i].key) << V(heap[parent(i)].key);
        return false;
      }
    }
    return true;
  }

  bool positionsMatch() const {
    for (PosT i = 0; i < size(); ++i) {
      assert(size_t(heap[i].id) < positions_size);
      if (positions[heap[i].id] != i) {
        LOG << "position mismatch" << V(heap.size()) << V(i) << V(heap[i].id) << V(positions[heap[i].id]) << V(positions_size);
        return false;
      }
    }
    return true;
  }

  bool fits(const IdT id) const {
    return static_cast<size_t>(id) < positions_size;
  }

  PosT parent(const PosT pos) const {
    return (pos - 1) / arity;
  }

  PosT firstChild(const PosT pos) const {
    return pos*arity + 1;
  }

  void siftUp(PosT pos) {
    const KeyT k = heap[pos].key;
    const IdT id = heap[pos].id;

    PosT parent_pos = parent(pos);
    while (pos > 0 && comp(heap[parent_pos].key, k)) {    // eliminate pos > 0 check by a sentinel at position zero?
      positions[ heap[parent_pos].id ] = pos;
      heap[pos] = heap[parent_pos];
      pos = parent_pos;
      parent_pos = parent(pos);
    }
    positions[id] = pos;
    heap[pos].id = id;
    heap[pos].key = k;

    //HEAVY_REFINEMENT_ASSERT(isHeap());
    //HEAVY_REFINEMENT_ASSERT(positionsMatch());
  }

  void siftDown(PosT pos) {
    const KeyT k = heap[pos].key;
    const IdT id = heap[pos].id;
    const PosT initial_pos = pos;

    PosT first = firstChild(pos);
    while (first < size() && first != pos) {
      PosT largestChild;

      if constexpr (arity > 2) {
        largestChild = first;
        KeyT largestChildKey = heap[largestChild].key;

        // find child with largest key for MaxHeap / smallest key for MinHeap
        const PosT firstInvalid = std::min(size(), firstChild(pos + 1));
        for (PosT c = first + 1; c < firstInvalid; ++c) {
          if ( comp(largestChildKey, heap[c].key) ) {
            largestChildKey = heap[c].key;
            largestChild = c;
          }
        }

        if (comp(largestChildKey, k) || largestChildKey == k) {
          break;
        }

      } else {
        assert(arity == 2);

        const PosT second = std::min(first + 1, size() - 1);    // TODO this branch is not cool. maybe make the while loop condition secondChild(pos) < size() ?
        const KeyT k1 = heap[first].key, k2 = heap[second].key;
        const bool c2IsLarger = comp(k1, k2);
        const KeyT largestChildKey = c2IsLarger ? k2 : k1;
        if (comp(largestChildKey, k) || largestChildKey == k) {
          break;
        }
        largestChild = c2IsLarger ? second : first;
      }

      positions[ heap[largestChild].id ] = pos;
      heap[pos] = heap[largestChild];
      pos = largestChild;
      first = firstChild(pos);
    }

    if (pos != initial_pos) {
      positions[id] = pos;
      heap[pos].key = k;
      heap[pos].id = id;
    }

    //HEAVY_REFINEMENT_ASSERT(isHeap());
    //HEAVY_REFINEMENT_ASSERT(positionsMatch());
  }

  struct HeapElement {
    KeyT key;
    IdT id;
  };

  Comparator comp;                // comp(heap[parent(pos)].key, heap[pos].key) returns true if the element at pos should move upward --> comp = std::less for MaxHeaps
                                  // similarly comp(heap[child(pos)].key, heap[pos].key) returns false if the element at pos should move downward
  vec<HeapElement> heap;
  PosT* positions;
  size_t positions_size;
};


// used to initialize handles in ExclusiveHandleHeap before handing a ref to Heap
struct HandlesPBase {
  explicit HandlesPBase(size_t n) :
    handles(n, invalid_position) { }
  vec<PosT> handles;
};

template<typename HeapT>
class ExclusiveHandleHeap : protected HandlesPBase, public HeapT {
public:
  explicit ExclusiveHandleHeap(size_t nHandles) :
    HandlesPBase(nHandles),
    HeapT(this->handles.data(), this->handles.size()) { }

                                                                              //at this point this->handles is already a deep copy of other.handles
  ExclusiveHandleHeap(const ExclusiveHandleHeap& other) :
    HandlesPBase(other),
    HeapT(this->handles.data(), this->handles.size()) { }

  void resize(const size_t new_n) {
    if ( this->handles.size() < new_n ) {
      this->handles.assign(new_n, invalid_position);
      this->setHandle(this->handles.data(), new_n);
    }
  }
};

template<typename KeyT, typename IdT>
using MaxHeap = Heap<KeyT, IdT, std::less<KeyT>, 2>;

}
}
