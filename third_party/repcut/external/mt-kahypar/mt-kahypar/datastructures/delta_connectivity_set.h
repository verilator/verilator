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

#include <atomic>
#include <type_traits>
#include <limits>
#include <cassert>

#include <tbb/enumerable_thread_specific.h>

#include "mt-kahypar/parallel/atomic_wrapper.h"
#include "mt-kahypar/parallel/stl/scalable_vector.h"
#include "mt-kahypar/datastructures/array.h"
#include "mt-kahypar/datastructures/static_bitset.h"
#include "mt-kahypar/datastructures/connectivity_set.h"
#include "mt-kahypar/datastructures/hypergraph_common.h"
#include "mt-kahypar/datastructures/sparse_map.h"
#include "mt-kahypar/utils/range.h"
#include "mt-kahypar/macros.h"

namespace mt_kahypar {
namespace ds {

/**
 * Data structure maintains the connectivity set relative to an shared connectivity set in
 * the global partition. It is used in the thread-local partition data structure to apply moves
 * that are not visible to other threads. The shared and thread-local connectivity set store
 * the connectivity set of a hyperedge as a bitset of size k. If a move adds or removes a block
 * from the connectivity set of hyperedge, we set a bit representing the block to one. We then compute
 * the thread-local connectivity set of hyperedge with a xor operation between the bitset in shared
 * and thread-local partition.
 */
template<typename ConnectivitySet>
class DeltaConnectivitySet {

 public:
  static constexpr bool debug = false;

  static constexpr int BITS_PER_BLOCK = StaticBitset::BITS_PER_BLOCK;
  using UnsafeBlock = StaticBitset::Block;

 private:
  // ! Iterator enumerates the position of all one bits in a bitset
  class OneBitIterator {
   public:
    using iterator_category = std::forward_iterator_tag;
    using value_type = PartitionID;
    using reference = PartitionID&;
    using pointer = PartitionID*;
    using difference_type = std::ptrdiff_t;

    OneBitIterator(const size_t num_blocks,
                   const UnsafeBlock* shared_bitset,
                   const UnsafeBlock* thread_local_bitset,
                   const PartitionID start_block) :
      _num_blocks(num_blocks),
      _shared_bitset(shared_bitset),
      _thread_local_bitset(thread_local_bitset),
      _max_block_id(num_blocks * BITS_PER_BLOCK),
      _current_block_id(start_block) {
      if ( _current_block_id < _max_block_id ) {
        nextBlockID();
      }
    }

    PartitionID operator*() const {
      return _current_block_id;
    }

    OneBitIterator& operator++() {
      nextBlockID();
      return *this;
    }

    OneBitIterator operator++(int ) {
      const OneBitIterator res = *this;
      nextBlockID();
      return res;
    }

    bool operator==(const OneBitIterator& o) const {
      return _current_block_id == o._current_block_id;
    }

    bool operator!=(const OneBitIterator& o) const {
      return !operator==(o);
    }

   private:
    MT_KAHYPAR_ATTRIBUTE_ALWAYS_INLINE void nextBlockID() {
      ++_current_block_id;
      UnsafeBlock b = _current_block_id < _max_block_id ? loadCurrentBlock() : 0;
      while ( b >> ( _current_block_id % BITS_PER_BLOCK ) == 0 && _current_block_id < _max_block_id ) {
        // no more one bits in current block -> load next block
        _current_block_id += (BITS_PER_BLOCK - (_current_block_id % BITS_PER_BLOCK));
        b = _current_block_id < _max_block_id ? loadCurrentBlock() : 0;
      }
      if ( _current_block_id < _max_block_id ) {
        _current_block_id += utils::lowest_set_bit_64(b >> ( _current_block_id % BITS_PER_BLOCK ));
      } else {
        _current_block_id = _max_block_id;
      }
    }

    MT_KAHYPAR_ATTRIBUTE_ALWAYS_INLINE UnsafeBlock loadCurrentBlock() {
      ASSERT(static_cast<size_t>(_current_block_id / BITS_PER_BLOCK) < _num_blocks);
      const size_t block_idx = _current_block_id / BITS_PER_BLOCK;
      return parallel::atomic_load(_shared_bitset[block_idx],
                                   std::memory_order_relaxed) ^
             *(_thread_local_bitset + block_idx);
    }

    const size_t _num_blocks;
    const UnsafeBlock* _shared_bitset;
    const UnsafeBlock* _thread_local_bitset;
    const PartitionID _max_block_id;
    PartitionID _current_block_id;
  };

public:
  using Iterator = OneBitIterator;

  DeltaConnectivitySet() :
    _connectivity_set(nullptr),
    _k(0),
    _num_blocks_per_hyperedge(0),
    _touched_hes(),
    _delta_connectivity_set(),
    _empty_connectivity_set(),
    _deep_copy_bitset() { }

  DeltaConnectivitySet(const PartitionID k) :
    _connectivity_set(nullptr),
    _k(k),
    _num_blocks_per_hyperedge(k / BITS_PER_BLOCK + (k % BITS_PER_BLOCK != 0)),
    _touched_hes(),
    _delta_connectivity_set(),
    _empty_connectivity_set(),
    _deep_copy_bitset() {
    _empty_connectivity_set.assign(_num_blocks_per_hyperedge, 0);
  }

  void setConnectivitySet(const ConnectivitySet* connectivity_set) {
    ASSERT(connectivity_set);
    _connectivity_set = connectivity_set;
  }

  void setNumberOfBlocks(const PartitionID k) {
    _k = k;
    _num_blocks_per_hyperedge = k / BITS_PER_BLOCK + (k % BITS_PER_BLOCK != 0);
    _empty_connectivity_set.clear();
    _empty_connectivity_set.assign(_num_blocks_per_hyperedge, 0);
  }

  // ! Returns an iterator over the connectivity set of the corresponding hyperedge
  IteratorRange<Iterator> connectivitySet(const HyperedgeID he) const {
    ASSERT(_connectivity_set);
    const size_t* entry = _touched_hes.get_if_contained(he);
    const UnsafeBlock* shared_connectivity_set = _connectivity_set->shallowCopy(he).data();
    const UnsafeBlock* thread_local_connectivity_set = entry ?
      &_delta_connectivity_set[*entry] : _empty_connectivity_set.data();
    return IteratorRange<Iterator>(
      Iterator(_num_blocks_per_hyperedge, shared_connectivity_set, thread_local_connectivity_set, -1),
      Iterator(_num_blocks_per_hyperedge, shared_connectivity_set, thread_local_connectivity_set,
        _num_blocks_per_hyperedge * BITS_PER_BLOCK));
  }

  // ! Adds the block to the connectivity set of the hyperedge
  void add(const HyperedgeID he, const PartitionID p) {
    ASSERT(p != kInvalidPartition && p < _k);
    toggle(he, p);
  }

  // ! Removes the block from the connectivity set of the hyperedge
  void remove(const HyperedgeID he, const PartitionID p) {
    ASSERT(p != kInvalidPartition && p < _k);
    toggle(he, p);
  }

  // ! Returns true, if the block is contained in the connectivity set of the hyperedge
  bool contains(const HyperedgeID he, const PartitionID p) const {
    ASSERT(_connectivity_set);
    ASSERT(p != kInvalidPartition && p < _k);
    return _connectivity_set->contains(he, p) ^ isSet(he, p);
  }

  // ! Clears all touched entries of the thread-local connectivity set
  void reset() {
    _touched_hes.clear();
    _delta_connectivity_set.clear();
  }

  // ! Returns the number of blocks contained in the hyperedge
  PartitionID connectivity(const HyperedgeID he) const {
    ASSERT(_connectivity_set);
    ds::StaticBitset& connectivity_set = _connectivity_set->shallowCopy(he);
    const size_t* entry = _touched_hes.get_if_contained(he);
    if ( entry ) {
      PartitionID connectivity = 0;
      const UnsafeBlock* original_data = connectivity_set.data();
      const UnsafeBlock* delta_data = &_delta_connectivity_set[*entry];
      for ( size_t i = 0; i < _num_blocks_per_hyperedge; ++i ) {
        connectivity += utils::popcount_64( *(original_data + i) ^ *(delta_data + i) );
      }
      return connectivity;
    } else {
      return connectivity_set.popcount();
    }
  }

  Bitset& deepCopy(const HyperedgeID he) const {
    ASSERT(_connectivity_set);
    StaticBitset& shared_con_set = _connectivity_set->shallowCopy(he);
    const size_t* entry = _touched_hes.get_if_contained(he);
    const UnsafeBlock* data = entry ?
      &_delta_connectivity_set[*entry] : _empty_connectivity_set.data();
    StaticBitset thread_local_con_set(_num_blocks_per_hyperedge, data);
    _deep_copy_bitset = shared_con_set ^ thread_local_con_set;
    return _deep_copy_bitset;
  }

  size_t size_in_bytes() const {
    return _touched_hes.size_in_bytes() + _delta_connectivity_set.capacity() * sizeof(UnsafeBlock);
  }

  void freeInternalData() {
    _touched_hes.freeInternalData();
    _delta_connectivity_set.clear();
    _delta_connectivity_set.shrink_to_fit();
  }

private:
	void toggle(const HyperedgeID he, const PartitionID p) {
    const size_t* entry = _touched_hes.get_if_contained(he);
    size_t pos = entry ? *entry : _delta_connectivity_set.size();
    if ( !entry ) {
      _touched_hes[he] = pos;
      _delta_connectivity_set.resize(
        _delta_connectivity_set.size() + _num_blocks_per_hyperedge, 0);
    }
    const size_t offset = p / BITS_PER_BLOCK;
    const size_t idx = p % BITS_PER_BLOCK;
    _delta_connectivity_set[pos + offset] ^= (UL(1) << idx);
	}

  bool isSet(const HyperedgeID he, const PartitionID p) const {
    bool is_set = false;
    const size_t* entry = _touched_hes.get_if_contained(he);
    if ( entry ) {
      const size_t offset = p / BITS_PER_BLOCK;
      const size_t idx = p % BITS_PER_BLOCK;
      is_set = _delta_connectivity_set[*entry + offset] & (UnsafeBlock(1) << idx);
    }
    return is_set;
  }

  const ConnectivitySet* _connectivity_set;
	PartitionID _k;
	size_t _num_blocks_per_hyperedge;

  DynamicFlatMap<size_t, size_t> _touched_hes;
  vec<UnsafeBlock> _delta_connectivity_set;
  vec<UnsafeBlock> _empty_connectivity_set;

  // ! Deep copy of connectivity set
  mutable Bitset _deep_copy_bitset;
};



}  // namespace ds
}  // namespace mt_kahypar
