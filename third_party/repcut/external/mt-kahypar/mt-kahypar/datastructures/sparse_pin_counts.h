/*******************************************************************************
 * MIT License
 *
 * This file is part of Mt-KaHyPar.
 *
 * Copyright (C) 2023 Tobias Heuer <tobias.heuer@kit.edu>
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

#include <tbb/concurrent_vector.h>
#include <tbb/parallel_for.h>
#include <tbb/enumerable_thread_specific.h>

#include "mt-kahypar/macros.h"
#include "mt-kahypar/datastructures/hypergraph_common.h"
#include "mt-kahypar/datastructures/array.h"
#include "mt-kahypar/datastructures/static_bitset.h"
#include "mt-kahypar/datastructures/pin_count_snapshot.h"
#include "mt-kahypar/parallel/atomic_wrapper.h"
#include "mt-kahypar/parallel/stl/scalable_vector.h"
#include "mt-kahypar/utils/range.h"


namespace mt_kahypar {
namespace ds {

/**
 * This is a sparse implementation of the pin count data structure.
 * Our original data structure for the pin count values takes O(k*|E|) space which would
 * be not feasible when k is large. The sparse implementation uses the observation
 * that the connectivity for most hyperedges is small in real-world hypergraphs.
 * The data structure stores for each hyperedge at most c <= k tuples of the form (block, pin_count),
 * where pin_count is the number of nodes part of the given block. If the connectivity of a
 * hyperedge is larger then c, then the data structure explicitly stores all pin count values
 * in an external pin count list. However, this external list is only initialized when the connectivity becomes larger then
 * c, which should happen rarely in practice. Thus, the data structures takes O(c * |E|) space when
 * overflows are negligible.
 *
 * The data structure supports concurrent read, but only one thread can modify the pin count values of
 * a hyperedge. Multiple writes to different hyperedges are supported.
 */
class SparsePinCounts {

  static constexpr bool debug = false;

  static constexpr size_t MAX_ENTRIES_PER_HYPEREDGE = 8; // = c

  struct PinCountHeader {
    // Stores the connectivity of a hyperedge
    PartitionID connectivity;
    // Flag that indicates whether or not pin counts are stored
    // in the external pin count list
    bool is_external;
  };

  // Stores the number of pins contained in a block
  struct PinCountEntry {
    PartitionID block;
    HypernodeID pin_count;
  };

 public:
  using Value = char;

  class Iterator {
   public:
    using iterator_category = std::forward_iterator_tag;
    using value_type = PartitionID;
    using reference = PartitionID&;
    using pointer = PartitionID*;
    using difference_type = std::ptrdiff_t;

    Iterator(const size_t start, const size_t end, const PartitionID k, const PinCountEntry* data) :
      _cur_entry( { kInvalidPartition, 0 } ),
      _cur(start),
      _end(end),
      _k(k),
      _pin_count_list(data),
      _ext_pin_count_list(nullptr) {
      // this assert needs to be active in release mode to silence a null pointer related compiler warning
      ALWAYS_ASSERT(data != nullptr);
      next_valid_entry();
    }

    Iterator(const size_t start, const size_t end, const PartitionID k,
             const tbb::concurrent_vector<PinCountEntry>* data) :
      _cur_entry( { kInvalidPartition, 0 } ),
      _cur(start),
      _end(end),
      _k(k),
      _pin_count_list(nullptr),
      _ext_pin_count_list(data) {
      ASSERT(data != nullptr);
      next_valid_entry();
    }

    PartitionID operator*() const {
      return _cur_entry.block;
    }

    Iterator& operator++() {
      ++_cur;
      next_valid_entry();
      return *this;
    }

    Iterator operator++(int ) {
      const Iterator res = *this;
      ++_cur;
      next_valid_entry();
      return res;
    }

    bool operator==(const Iterator& o) const {
      return _cur == o._cur && _end == o._end;
    }

    bool operator!=(const Iterator& o) const {
      return !operator==(o);
    }

   private:
    inline void next_valid_entry() {
      // Note that the pin list can change due to concurrent writes.
      // Therefore, we only return valid pin count entries
      get_current_entry();
      while ( !is_valid() && _cur < _end ) {
        ++_cur;
        get_current_entry();
      }
    }

    inline void get_current_entry() {
      if ( _cur < _end ) {
        if ( _pin_count_list ) {
          _cur_entry = *(_pin_count_list + _cur);
        } else {
          _cur_entry = (*_ext_pin_count_list)[_cur];
        }
      }
    }

    inline bool is_valid() {
      return _cur_entry.block >= 0 && _cur_entry.block < _k && _cur_entry.pin_count > 0;
    }

    PinCountEntry _cur_entry;
    size_t _cur;
    const size_t _end;
    const PartitionID _k;
    const PinCountEntry* _pin_count_list;
    const tbb::concurrent_vector<PinCountEntry>* _ext_pin_count_list;
  };

  SparsePinCounts() :
    _num_hyperedges(0),
    _k(0),
    _max_hyperedge_size(0),
    _entries_per_hyperedge(0),
    _size_of_pin_counts_per_he(0),
    _pin_count_in_part(),
    _pin_count_ptr(nullptr),
    _ext_pin_count_list(),
    _deep_copy_bitset(),
    _shallow_copy_bitset(),
    _pin_count_snapshot([&] { return initPinCountSnapshot(); }) { }

  SparsePinCounts(const HyperedgeID num_hyperedges,
                  const PartitionID k,
                  const HypernodeID max_value,
                  const bool assign_parallel = true) :
    _num_hyperedges(0),
    _k(0),
    _max_hyperedge_size(0),
    _entries_per_hyperedge(0),
    _size_of_pin_counts_per_he(0),
    _pin_count_in_part(),
    _pin_count_ptr(nullptr),
    _ext_pin_count_list(),
    _deep_copy_bitset(),
    _shallow_copy_bitset(),
    _pin_count_snapshot([&] { return initPinCountSnapshot(); }) {
    initialize(num_hyperedges, k, max_value, assign_parallel);
  }

  SparsePinCounts(const SparsePinCounts&) = delete;
  SparsePinCounts & operator= (const SparsePinCounts &) = delete;

  SparsePinCounts(SparsePinCounts&& other) :
    _num_hyperedges(other._num_hyperedges),
    _k(other._k),
    _max_hyperedge_size(other._max_hyperedge_size),
    _entries_per_hyperedge(other._entries_per_hyperedge),
    _size_of_pin_counts_per_he(other._size_of_pin_counts_per_he),
    _pin_count_in_part(std::move(other._pin_count_in_part)),
    _pin_count_ptr(std::move(other._pin_count_ptr)),
    _ext_pin_count_list(std::move(other._ext_pin_count_list)),
    _deep_copy_bitset(std::move(other._deep_copy_bitset)),
    _shallow_copy_bitset(std::move(other._shallow_copy_bitset)),
    _pin_count_snapshot([&] { return initPinCountSnapshot(); }) { }

  SparsePinCounts & operator= (SparsePinCounts&& other) {
    _num_hyperedges = other._num_hyperedges;
    _k = other._k;
    _max_hyperedge_size = other._max_hyperedge_size;
    _entries_per_hyperedge = other._entries_per_hyperedge;
    _size_of_pin_counts_per_he = other._size_of_pin_counts_per_he;
    _pin_count_in_part = std::move(other._pin_count_in_part);
    _pin_count_ptr = std::move(other._pin_count_ptr);
    _ext_pin_count_list = std::move(other._ext_pin_count_list);
    _deep_copy_bitset = std::move(other._deep_copy_bitset);
    _shallow_copy_bitset = std::move(other._shallow_copy_bitset);
    _pin_count_snapshot = tbb::enumerable_thread_specific<PinCountSnapshot>([&] {
        return initPinCountSnapshot();
      });
    return *this;
  }

  // ################## Connectivity Set ##################

  inline bool contains(const HyperedgeID he, const PartitionID p) const {
    ASSERT(he < _num_hyperedges);
    ASSERT(p < _k);
    return find_entry(he, p) != nullptr;
  }

  inline void clear(const HyperedgeID he) {
    ASSERT(he < _num_hyperedges);
    init_pin_count_of_hyperedge(he);
  }

  inline PartitionID connectivity(const HyperedgeID he) const {
    ASSERT(he < _num_hyperedges);
    const PinCountHeader* head = header(he);
    return head->connectivity;
  }

  IteratorRange<Iterator> connectivitySet(const HyperedgeID he) const {
    ASSERT(he < _num_hyperedges);
    const PinCountHeader* head = header(he);
    const size_t con = head->connectivity;
    if ( likely(!head->is_external) ) {
      return IteratorRange<Iterator>(
        Iterator(UL(0), con, _k, entry(he, 0)),
        Iterator(con, con, _k, entry(he, 0)));
    } else {
      return IteratorRange<Iterator>(
        Iterator(UL(0), con, _k, &_ext_pin_count_list[he]),
        Iterator(con, con, _k, &_ext_pin_count_list[he]));
    }
  }

  StaticBitset& shallowCopy(const HyperedgeID he) const {
    // Shallow copy not possible for sparse pin count data structure
    Bitset& deep_copy = deepCopy(he);
    StaticBitset& shallow_copy = _shallow_copy_bitset.local();
    shallow_copy.set(deep_copy.numBlocks(), deep_copy.data());
    return shallow_copy;
  }

  // Creates a deep copy of the connectivity set of hyperedge he
  Bitset& deepCopy(const HyperedgeID he) const {
    Bitset& deep_copy = _deep_copy_bitset.local();
    deep_copy.resize(_k);
    for ( const PartitionID& block : connectivitySet(he) ) {
      deep_copy.set(block);
    }
    return deep_copy;
  }

  // ################## Pin Count In Part ##################

  // ! Returns the pin count of the hyperedge in the corresponding block
  inline HypernodeID pinCountInPart(const HyperedgeID he,
                                    const PartitionID p) const {
    ASSERT(he < _num_hyperedges);
    ASSERT(p < _k);
    const PinCountEntry* val = find_entry(he, p);
    return val ? val->pin_count : 0;
  }

  // ! Sets the pin count of the hyperedge in the corresponding block to value
  inline void setPinCountInPart(const HyperedgeID he,
                                const PartitionID p,
                                const HypernodeID value) {
    ASSERT(he < _num_hyperedges);
    ASSERT(p < _k);
    add_pin_count_entry(he, p, value);
  }

  // ! Increments the pin count of the hyperedge in the corresponding block
  inline HypernodeID incrementPinCountInPart(const HyperedgeID he,
                                             const PartitionID p) {
    ASSERT(he < _num_hyperedges);
    ASSERT(p < _k);
    PinCountEntry* val = find_entry(he, p);
    HypernodeID inc_pin_count = 0;
    if ( val ) {
      inc_pin_count = ++val->pin_count;
    } else {
      inc_pin_count = 1;
      add_pin_count_entry(he, p, inc_pin_count);
    }
    return inc_pin_count;
  }

  // ! Decrements the pin count of the hyperedge in the corresponding block
  inline HypernodeID decrementPinCountInPart(const HyperedgeID he,
                                             const PartitionID p) {
    ASSERT(he < _num_hyperedges);
    ASSERT(p < _k);
    PinCountEntry* val = find_entry(he, p);
    ASSERT(val);
    const HypernodeID dec_pin_count = --val->pin_count;
    if ( dec_pin_count == 0 ) {
      // Remove pin count entry
      // Note that only one thread can modify the pin count list of
      // a hyperedge at the same time. Therefore, this operation is thread-safe.
      PinCountHeader* head = header(he);
      --head->connectivity;
      if ( likely(!head->is_external) ) {
        PinCountEntry* back = entry(he, head->connectivity);
        *val = *back;
        back->block = kInvalidPartition;
        back->pin_count = 0;
      } else {
        // Note that in case the connectivity becomes smaller than c,
        // we do not fallback to the smaller pin count list bounded by c.
        size_t pos = 0;
        for ( ; pos < _ext_pin_count_list[he].size(); ++pos ) {
          if ( _ext_pin_count_list[he][pos].block == p ) {
            break;
          }
        }
        std::swap(_ext_pin_count_list[he][pos], _ext_pin_count_list[he][head->connectivity]);
        _ext_pin_count_list[he][head->connectivity].block = kInvalidPartition;
        _ext_pin_count_list[he][head->connectivity].pin_count = 0;
      }
    }
    return dec_pin_count;
  }

  PinCountSnapshot& snapshot(const HyperedgeID he) {
    PinCountSnapshot& cpy = _pin_count_snapshot.local();
    cpy.reset();
    for ( const PartitionID block : connectivitySet(he) ) {
      cpy.setPinCountInPart(block, pinCountInPart(he, block));
    }
    return cpy;
  }

  // ################## Miscellaneous ##################

  // ! Initializes the data structure
  void initialize(const HyperedgeID num_hyperedges,
                  const PartitionID k,
                  const HypernodeID max_value,
                  const bool assign_parallel = true) {
    _num_hyperedges = num_hyperedges;
    _k = k;
    _max_hyperedge_size = max_value;
    _entries_per_hyperedge = std::min(
      static_cast<size_t>(k), MAX_ENTRIES_PER_HYPEREDGE);
    _size_of_pin_counts_per_he = sizeof(PinCountHeader) +
      sizeof(PinCountEntry) * _entries_per_hyperedge;
    _pin_count_in_part.resize("Refinement", "pin_count_in_part",
      _size_of_pin_counts_per_he * num_hyperedges, false, assign_parallel);
    _pin_count_ptr = _pin_count_in_part.data();
    _ext_pin_count_list.resize(_num_hyperedges);
    reset(assign_parallel);
  }

  void reset(const bool assign_parallel = true) {
    if ( assign_parallel ) {
      tbb::parallel_for(ID(0), _num_hyperedges, [&](const HyperedgeID he) {
        init_pin_count_of_hyperedge(he);
      });
    } else {
      for ( HyperedgeID he = 0; he < _num_hyperedges; ++he ) {
        init_pin_count_of_hyperedge(he);
      }
    }
  }

  // ! Returns the size in bytes of this data structure
  size_t size_in_bytes() const {
    // TODO: size of external list is missing
    return sizeof(char) * _pin_count_in_part.size();
  }

  void freeInternalData() {
    parallel::free(_pin_count_in_part);
  }

  void memoryConsumption(utils::MemoryTreeNode* parent) const {
    ASSERT(parent);
    parent->addChild("Pin Count Values", sizeof(char) * _pin_count_in_part.size());
    tbb::enumerable_thread_specific<size_t> ext_pin_count_entries(0);
    tbb::parallel_for(ID(0), _num_hyperedges, [&](const HyperedgeID he) {
      ext_pin_count_entries.local() += _ext_pin_count_list[he].size();
    });
    parent->addChild("External Pin Count Values", sizeof(PinCountEntry) *
      ext_pin_count_entries.combine(std::plus<size_t>()));
  }

  static size_t num_elements(const HyperedgeID num_hyperedges,
                             const PartitionID k,
                             const HypernodeID) {
    const size_t entries_per_hyperedge = std::min(
      static_cast<size_t>(k), MAX_ENTRIES_PER_HYPEREDGE);
    const size_t size_of_pin_counts_per_he = sizeof(PinCountHeader) +
      sizeof(PinCountEntry) * entries_per_hyperedge;
    return size_of_pin_counts_per_he * num_hyperedges;
  }

 private:
  inline void init_pin_count_of_hyperedge(const HyperedgeID& he) {
    PinCountHeader* head = header(he);
    head->connectivity = 0;
    head->is_external = false;
    for ( size_t i = 0; i < _entries_per_hyperedge; ++i ) {
      PinCountEntry* pin_count = entry(he, i);
      pin_count->block = kInvalidPartition;
      pin_count->pin_count = 0;
    }
    _ext_pin_count_list[he].clear();
  }

  inline void add_pin_count_entry(const HyperedgeID he,
                                  const PartitionID p,
                                  const HypernodeID value) {
    // Assumes that the block with the given ID does not exist
    // and inserts it at the end of the pin count list
    // Note that only one thread can modify the pin count list of
    // a hyperedge at the same time. Therefore, this operation is thread-safe.
    PinCountHeader* head = header(he);
    if ( likely(!head->is_external) ) {
      const size_t connectivity = head->connectivity;
      if ( connectivity < _entries_per_hyperedge ) {
        // Still enough entries to add the pin count entry
        PinCountEntry* pin_count = entry(he, connectivity);
        pin_count->block = p;
        pin_count->pin_count = value;
      } else {
        // Connecitivity is now larger than c
        // => copy entries to external pin count list
        handle_overflow(he);
        add_pin_count_entry_to_external(he, p, value);
      }
    } else {
      add_pin_count_entry_to_external(he, p, value);
    }
    ++head->connectivity;
  }

  inline void handle_overflow(const HyperedgeID& he) {
    PinCountHeader* head = header(he);
    // Copy entries to external pin count list
    for ( size_t i = 0; i < _entries_per_hyperedge; ++i ) {
      _ext_pin_count_list[he].push_back(*entry(he, i));
    }
    head->is_external = true;
  }

  inline void add_pin_count_entry_to_external(const HyperedgeID he,
                                              const PartitionID p,
                                              const HypernodeID value) {
    PinCountHeader* head = header(he);
    ASSERT(head->is_external);
    if ( static_cast<size_t>(head->connectivity) < _ext_pin_count_list[he].size() ) {
      // Reuse existing entry that was removed due to decrementing the pin count
      ASSERT(_ext_pin_count_list[he][head->connectivity].block == kInvalidPartition);
      _ext_pin_count_list[he][head->connectivity].block = p;
      _ext_pin_count_list[he][head->connectivity].pin_count = value;
    } else {
      _ext_pin_count_list[he].push_back(PinCountEntry { p, value });
    }
  }

  MT_KAHYPAR_ATTRIBUTE_ALWAYS_INLINE const PinCountEntry* find_entry(const HyperedgeID he, const PartitionID p) const {
    const PinCountHeader* head = header(he);
    if ( likely(!head->is_external) ) {
      // Due to concurrent writes, the connectivity can become larger than MAX_ENTRIES_PER_HYPEREDGE.
      const size_t connectivity =
        std::min(static_cast<size_t>(head->connectivity), MAX_ENTRIES_PER_HYPEREDGE);
      for ( size_t i = 0; i < connectivity; ++i ) {
        const PinCountEntry* value = entry(he, i);
        if ( value->block == p ) {
          return value;
        }
      }
    } else {
      const size_t num_entries = head->connectivity;
      for ( size_t i = 0; i < num_entries; ++i ) {
        const PinCountEntry& value = _ext_pin_count_list[he][i];
        if ( value.block == p ) {
          return &value;
        }
      }
    }
    return nullptr;
  }

  MT_KAHYPAR_ATTRIBUTE_ALWAYS_INLINE PinCountEntry* find_entry(const HyperedgeID he, const PartitionID p) {
    return const_cast<PinCountEntry*>(static_cast<const SparsePinCounts&>(*this).find_entry(he, p));
  }

  MT_KAHYPAR_ATTRIBUTE_ALWAYS_INLINE const PinCountHeader* header(const HyperedgeID he) const {
    ASSERT(he <= _num_hyperedges, "Hyperedge" << he << "does not exist");
    return reinterpret_cast<const PinCountHeader*>(_pin_count_ptr + he * _size_of_pin_counts_per_he);
  }

  MT_KAHYPAR_ATTRIBUTE_ALWAYS_INLINE PinCountHeader* header(const HyperedgeID he) {
    return const_cast<PinCountHeader*>(static_cast<const SparsePinCounts&>(*this).header(he));
  }

  MT_KAHYPAR_ATTRIBUTE_ALWAYS_INLINE const PinCountEntry* entry(const HyperedgeID he,
                                                                const size_t idx) const {
    ASSERT(he <= _num_hyperedges, "Hyperedge" << he << "does not exist");
    return reinterpret_cast<const PinCountEntry*>(_pin_count_ptr +
      he * _size_of_pin_counts_per_he + sizeof(PinCountHeader) + sizeof(PinCountEntry) * idx);
  }

  MT_KAHYPAR_ATTRIBUTE_ALWAYS_INLINE PinCountEntry* entry(const HyperedgeID he,
                                                          const size_t idx) {
    return const_cast<PinCountEntry*>(static_cast<const SparsePinCounts&>(*this).entry(he, idx));
  }

  PinCountSnapshot initPinCountSnapshot() const {
    return PinCountSnapshot(_k, _max_hyperedge_size);
  }

  // ! Number of hyperedges
  HyperedgeID _num_hyperedges;

  // ! Number of blocks
  PartitionID _k;

  // ! Maximum size of a hyperedge
  HypernodeID _max_hyperedge_size;

  // ! Maximum number of pin count entries per hyperedge (= c)
  size_t _entries_per_hyperedge;

  // ! Size in bytes of the header struct and all pin count entries
  size_t _size_of_pin_counts_per_he;

  // ! Stores the pin count list bounded by c
  Array<char> _pin_count_in_part;
  char* _pin_count_ptr;

  // ! External pin count list that stores the pin count values when
  // ! the connectivity becomes larger than c.
  // ! Note that we have to use concurrent_vector since we allow concurrent
  // ! read while modyfing the entries.
  vec<tbb::concurrent_vector<PinCountEntry>> _ext_pin_count_list;

  // Bitsets to create shallow and deep copies of the connectivity set
  mutable tbb::enumerable_thread_specific<Bitset> _deep_copy_bitset;
  mutable tbb::enumerable_thread_specific<StaticBitset> _shallow_copy_bitset;
  mutable tbb::enumerable_thread_specific<PinCountSnapshot> _pin_count_snapshot;
};
}  // namespace ds
}  // namespace mt_kahypar
