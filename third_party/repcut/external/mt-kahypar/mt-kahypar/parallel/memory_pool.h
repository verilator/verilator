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

#include <cmath>
#include <memory>
#include <unordered_map>
#include <vector>
#include <algorithm>
#if _WIN32
#include <windows.h>
#else
#include <unistd.h>
#endif

#include <tbb/parallel_for.h>

#include "mt-kahypar/macros.h"
#include "mt-kahypar/parallel/stl/allocator.h"
#include "mt-kahypar/utils/exception.h"
#include "mt-kahypar/utils/memory_tree.h"

namespace mt_kahypar {
namespace parallel {

/*!
 * Singleton that handles huge memory allocations.
 * Memory chunks can be registered with a key and all memory
 * chunks can be collectively allocated in parallel.
 */
class MemoryPoolT {

  static constexpr bool debug = false;
  static constexpr size_t kInvalidMemoryChunk = std::numeric_limits<size_t>::max();

  static constexpr size_t MINIMUM_ALLOCATION_SIZE = 10000000; // 10 MB

  // ! Represents a memory group.
  struct MemoryGroup {

    explicit MemoryGroup(const size_t stage) :
      _stage(stage),
      _key_to_memory_id() { }

    void insert(const std::string& key, const size_t memory_id) {
      _key_to_memory_id.insert(std::make_pair(key, memory_id));
    }

    size_t getKey(const std::string& key) const {
      return _key_to_memory_id.at(key);
    }

    bool containsKey(const std::string& key) const {
      return _key_to_memory_id.find(key) != _key_to_memory_id.end();
    }

    const size_t _stage;
    std::unordered_map<std::string, size_t> _key_to_memory_id;
  };

  // ! Represents a memory chunk.
  struct MemoryChunk {

    explicit MemoryChunk(const size_t num_elements,
                         const size_t size) :
      _num_elements(num_elements),
      _size(size),
      _initial_size(size * num_elements),
      _used_size(size * num_elements),
      _total_size(size * num_elements),
      _data(nullptr),
      _next_memory_chunk_id(kInvalidMemoryChunk),
      _defer_allocation(false),
      _is_assigned(false) { }

    MemoryChunk(MemoryChunk&& other) :
      _num_elements(other._num_elements),
      _size(other._size),
      _initial_size(other._initial_size),
      _used_size(other._used_size),
      _total_size(other._total_size),
      _data(std::move(other._data)),
      _next_memory_chunk_id(other._next_memory_chunk_id),
      _defer_allocation(other._defer_allocation),
      _is_assigned(other._is_assigned) {
      other._data = nullptr;
      other._next_memory_chunk_id = kInvalidMemoryChunk;
      other._defer_allocation = true;
      other._is_assigned = false;
    }

    // ! Requests the memory chunk.
    // ! Note, successive calls to this method will return
    // ! nullptr until release_chunk() is called.
    char* request_chunk() {
      if ( _data && !_is_assigned ) {
        _is_assigned = true;
        return _data;
      } else {
        return nullptr;
      }
    }

    char* request_unused_chunk(const size_t size, const size_t page_size) {
      const size_t aligned_used_size = align_with_page_size(_used_size, page_size);
      if ( _data && aligned_used_size < _total_size &&
            size <= _total_size - aligned_used_size ) {
        char* data = _data + aligned_used_size;
        _used_size = aligned_used_size + size;
        return data;
      }
      return nullptr;
    }

    // ! Releases the memory chunks
    void release_chunk() {
      _is_assigned = false;
    }

    // ! Allocates the memory chunk
    // ! Note, the memory chunk is zero initialized.
    bool allocate() {
      if ( !_data && !_defer_allocation ) {
        _data = (char*) mtk_scalable_calloc(_num_elements, _size);
        if ( !_data ) {
          unsigned long mb_value = std::round(size_in_megabyte(_num_elements * _size));
          throw SystemException("Failed to allocate " + std::to_string(mb_value) + " MB of memory: " +
                                "it seems you have not enough RAM to partition this input\n" +
                                "(for large k: maybe try --mode=rb or --preset-type=large_k?)");
        }
        return true;
      } else {
        return false;
      }
    }

    // ! Frees the memory chunk
    void free() {
      if ( _data ) {
        mtk_scalable_free(_data);
        _data = nullptr;
      }
    }

    // ! Returns the size in bytes of the memory chunk
    size_t size_in_bytes() const {
      size_t size = 0;
      if ( _data ) {
        size = _num_elements * _size;
      }
      return size;
    }

    // Align with page size to minimize cache effects
    size_t align_with_page_size(const size_t size, const size_t page_size) {
      if ( page_size > 1 ) {
        return 2 * page_size * ( size / ( 2 * page_size ) +
          ( ( size % ( 2 * page_size ) ) != 0 ) );
      } else {
        return size;
      }
    }

    // ! Number of elements to allocate
    size_t _num_elements;
    // ! Data type size in bytes
    size_t _size;
    // ! Initial size in bytes of the memory chunk
    const size_t _initial_size;
    // ! Used size in bytes of the memory chunk
    size_t _used_size;
    // ! Total size in bytes of the memory chunk
    size_t _total_size;
    // ! Memory chunk
    char* _data;
    // ! Memory chunk id where this memory chunk is transfered
    // ! to if memory is not needed any more
    size_t _next_memory_chunk_id;
    // ! Memory chunk is not initialized if allocate_memory_chunks()
    // ! is called, because memory is transfered from an other stage
    // ! to this memory chunk.
    bool _defer_allocation;
    // ! True, if already assigned to a vector
    bool _is_assigned;
  };


 public:
  MemoryPoolT(const MemoryPoolT&) = delete;
  MemoryPoolT & operator= (const MemoryPoolT &) = delete;

  MemoryPoolT(MemoryPoolT&&) = delete;
  MemoryPoolT & operator= (MemoryPoolT &&) = delete;

  ~MemoryPoolT() {
    free_memory_chunks();
  }

  static MemoryPoolT& instance() {
    static MemoryPoolT instance;
    return instance;
  }

  // ! Returns wheater memory pool is already initialized
  bool isInitialized() const {
    return _is_initialized;
  }

  // ! Registers a memory group in the memory pool. A memory
  // ! group is associated with a stage. Assumption is that, if
  // ! a stage is completed, than memory is not needed any more
  // ! and can be reused in a consecutive stage.
  void register_memory_group(const std::string& group,
                             const size_t stage) {
    if ( _memory_groups.find(group) == _memory_groups.end() ) {
      _memory_groups.emplace(std::piecewise_construct,
        std::forward_as_tuple(group), std::forward_as_tuple(stage));
    }
  }

  // ! Registers a memory chunk in the memory pool. The memory chunk is
  // ! associated with a memory group and a unique key within that group.
  // ! Note, that the memory chunk is not immediatly allocated. One has to call
  // ! allocate_memory_chunks() to collectively allocate all memory chunks.
  void register_memory_chunk(const std::string& group,
                             const std::string& key,
                             const size_t num_elements,
                             const size_t size) {
    if ( _memory_groups.find(group) != _memory_groups.end() ) {
      MemoryGroup& mem_group = _memory_groups.at(group);
      const size_t memory_id = _memory_chunks.size();
      if ( !mem_group.containsKey(key) ) {
        mem_group.insert(key, memory_id);
        _memory_chunks.emplace_back(num_elements, size);
        DBG << "Registers memory chunk (" << group << "," << key << ")"
            << "of" <<  size_in_megabyte(num_elements * size) << "MB"
            << "in memory pool";
      }
    }
  }

  // ! Allocates all registered memory chunks in parallel
  void allocate_memory_chunks(const bool optimize_allocations = true) {
    if ( optimize_allocations ) {
      optimize_memory_allocations();
    }
    const size_t num_memory_segments = _memory_chunks.size();
    tbb::parallel_for(UL(0), num_memory_segments, [&](const size_t i) {
      if (_memory_chunks[i].allocate()) {
        DBG << "Allocate memory chunk of size"
            << size_in_megabyte(_memory_chunks[i].size_in_bytes()) << "MB";
      }
    });
    update_active_memory_chunks();
    _is_initialized = true;
  }

  // ! Returns the memory chunk registered under the corresponding
  // ! group with the specified key. If the memory chunk is already
  // ! requested, the size of the memory chunk is smaller than the
  // ! requested size or the requested memory chunk does not exist,
  // ! than nullptr is returned.
  char* request_mem_chunk(const std::string& group,
                          const std::string& key,
                          const size_t num_elements,
                          const size_t size) {
    const size_t size_in_bytes = num_elements * size;
    DBG << "Requests memory chunk (" << group << "," << key << ")"
        << "of" <<  size_in_megabyte(size_in_bytes) << "MB"
        << "in memory pool";
    if ( !_use_minimum_allocation_size || size_in_bytes > MINIMUM_ALLOCATION_SIZE ) {
      MemoryChunk* chunk = find_memory_chunk(group, key);

      if ( chunk && size_in_bytes <= chunk->size_in_bytes() ) {
        char* data = chunk->request_chunk();
        if ( data ) {
          DBG << "Memory chunk request (" << group << "," << key << ")"
              << "was successful";
          return data;
        }
      }
    }
    DBG << "Memory chunk request (" << group << "," << key << ") failed";
    return nullptr;
  }

  // ! Requests an unused memory chunk. If memory usage optimization are
  // ! activated some memory chunks have unused memory segments due to
  // ! overallocations.
  char* request_unused_mem_chunk(const size_t num_elements,
                                 const size_t size,
                                 const bool align_with_page_size = true) {
    if ( _is_initialized ) {
      DBG << "Request unused memory chunk of"
          << size_in_megabyte(num_elements * size) << "MB";
      const size_t size_in_bytes = num_elements * size;
      if (_use_unused_memory_chunks &&
          (!_use_minimum_allocation_size || size_in_bytes > MINIMUM_ALLOCATION_SIZE)) {
        const size_t n = _active_memory_chunks.size();
        if (n > 0) {
          const size_t end = _next_active_memory_chunk % n;
          const size_t start = (end + 1) % n;
          for (size_t i = start;; i = (i + 1) % n) {
            size_t memory_id = _active_memory_chunks[i];
            ASSERT(memory_id < _memory_chunks.size());
            char *data = _memory_chunks[memory_id].request_unused_chunk(
                    size_in_bytes, align_with_page_size ? _page_size : UL(1));
            if (data) {
              DBG << "Memory chunk request for an unsed memory chunk was successful";
              if (_use_round_robin_assignment) {
                ++_next_active_memory_chunk;
              }
              return data;
            }
            if (i == end) {
              break;
            }
          }
        }
      }
    }
    DBG << "Memory chunk request for an unsed memory chunk failed";
    return nullptr;
  }

  // ! Returns the memory chunk under the corresponding group with
  // ! the specified key. In contrast to assign_mem_chunk, no explicit
  // ! checks are performed, if chunk is already assigned.
  char* mem_chunk(const std::string& group,
                  const std::string& key) {
    MemoryChunk* chunk = find_memory_chunk(group, key);
    if ( chunk )   {
      return chunk->_data;
    } else {
      return nullptr;
    }
  }

  // ! Releases the memory chunk under the corresponding group with
  // ! the specified key. Afterwards, memory chunk is available for
  // ! further requests.
  void release_mem_chunk(const std::string& group,
                         const std::string& key) {
    MemoryChunk* chunk = find_memory_chunk(group, key);
    if ( chunk ) {
      DBG << "Release memory chunk (" << group << "," << key << ")";
      chunk->release_chunk();
    }
  }

  // ! Signals that the memory of the corresponding group is not
  // ! required any more. If an optimized memory allocation strategy
  // ! was calculated before, the memory is passed to next group.
  void release_mem_group(const std::string& group) {

    if ( _memory_groups.find(group) != _memory_groups.end() ) {
      ASSERT([&] {
        for ( const auto& key : _memory_groups.at(group)._key_to_memory_id ) {
          const size_t memory_id = key.second;
          if ( _memory_chunks[memory_id]._is_assigned ) {
            LOG << "(" << group << "," << key.first << ")"
                << "is assigned";
            return false;
          }
        }
        return true;
      }(), "Some memory chunks of group '" << group << "' are still assigned");

      DBG << "Release memory of group '" << group << "'";
      for ( const auto& key : _memory_groups.at(group)._key_to_memory_id ) {
        const size_t memory_id = key.second;
        MemoryChunk& lhs = _memory_chunks[memory_id];
        ASSERT(lhs._data);
        if ( lhs._next_memory_chunk_id != kInvalidMemoryChunk ) {
          ASSERT(lhs._next_memory_chunk_id < _memory_chunks.size());
          MemoryChunk& rhs = _memory_chunks[lhs._next_memory_chunk_id];
          rhs._data = lhs._data;
          lhs._data = nullptr;
        } else {
          // Memory chunk is not required any more
          // => make it available for unused memory requests
          lhs._used_size = 0;
          lhs._is_assigned = true;
        }
      }
      update_active_memory_chunks();
    }
  }

  // Resets the memory pool to the state after all memory chunks are allocated
  void reset() {

    // Find all root memory chunks of an optimization path
    std::vector<size_t> in_degree(_memory_chunks.size(), 0);
    for ( const MemoryChunk& chunk : _memory_chunks ) {
      if ( chunk._next_memory_chunk_id != kInvalidMemoryChunk ) {
        ++in_degree[chunk._next_memory_chunk_id];
      }
    }

    // Move memory chunks back to root memory chunks
    for ( size_t i = 0; i < _memory_chunks.size(); ++i ) {
      if ( in_degree[i] == 0 && !_memory_chunks[i]._data ) {
        size_t current_mem_chunk = i;
        while ( !_memory_chunks[current_mem_chunk]._data ) {
          ASSERT(_memory_chunks[current_mem_chunk]._next_memory_chunk_id != kInvalidMemoryChunk);
          current_mem_chunk = _memory_chunks[current_mem_chunk]._next_memory_chunk_id;
        }
        ASSERT(_memory_chunks[current_mem_chunk]._data);
        ASSERT(i != current_mem_chunk);
        _memory_chunks[i]._data = _memory_chunks[current_mem_chunk]._data;
        _memory_chunks[current_mem_chunk]._data = nullptr;
      }

      // Reset stats
      _memory_chunks[i]._used_size = _memory_chunks[i]._initial_size;
      _memory_chunks[i]._is_assigned = false;
    }

    update_active_memory_chunks();
  }

  // ! Frees all memory chunks in parallel
  void free_memory_chunks() {
    const size_t num_memory_segments = _memory_chunks.size();
    tbb::parallel_for(UL(0), num_memory_segments, [&](const size_t i) {
      _memory_chunks[i].free();
    });
    _memory_chunks.clear();
    _memory_groups.clear();
    _active_memory_chunks.clear();
    _is_initialized = false;
  }

  // ! Only for testing
  void deactivate_round_robin_assignment() {
    _use_round_robin_assignment = false;
  }

  // ! Only for testing
  void deactivate_minimum_allocation_size() {
    _use_minimum_allocation_size = false;
  }

  bool is_unused_memory_allocations_activated() const {
    return _use_unused_memory_chunks;
  }

  void activate_unused_memory_allocations() {
    _use_unused_memory_chunks = true;
  }

  void deactivate_unused_memory_allocations() {
    _use_unused_memory_chunks = false;
  }

  // ! Returns the size in bytes of the memory chunk under the
  // ! corresponding group with the specified key.
  size_t size_in_bytes(const std::string& group,
                       const std::string& key) {
    MemoryChunk* chunk = find_memory_chunk(group, key);
    if ( chunk )   {
      return chunk->size_in_bytes();
    } else {
      return 0;
    }
  }

  // ! Builds a memory tree that reflects the memory
  // ! consumption of the memory pool
  void memory_consumption(utils::MemoryTreeNode* parent) const {
    ASSERT(parent);
    for ( const auto& group_element : _memory_groups ) {
      const std::string& group = group_element.first;
      const auto& key_to_memory_id = group_element.second._key_to_memory_id;
      utils::MemoryTreeNode* group_node = parent->addChild(group);
      for ( const auto& element : key_to_memory_id ) {
        const std::string& key = element.first;
        const size_t memory_id = element.second;
        ASSERT(memory_id < _memory_chunks.size());
        group_node->addChild(key,
          std::max(_memory_chunks[memory_id].size_in_bytes(), UL(1)));
      }
    }
  }

  void explain_optimizations() const {
    using GroupKey = std::pair<std::string, std::string>;
    size_t total_size = 0;
    size_t allocated_size = 0;
    LOG << BOLD << "Explanation of Memory Usage Optimization:" << END;
    LOG << "  An arrow indicates that memory is transfered to the following memory chunk,"
        << "\n  if corresponding memory group is released.\n";

    std::unordered_map<size_t, GroupKey> memory_id_to_group_key;
    for ( const auto& mem_group : _memory_groups ) {
      const std::string& group = mem_group.first;
      for ( const auto& mem_key : mem_group.second._key_to_memory_id ) {
        const std::string& key = mem_key.first;
        const size_t memory_id = mem_key.second;
        memory_id_to_group_key.emplace(std::piecewise_construct,
          std::forward_as_tuple(memory_id), std::forward_as_tuple(group, key));
      }
    }

    for ( size_t memory_id = 0; memory_id < _memory_chunks.size(); ++memory_id ) {
      if ( !_memory_chunks[memory_id]._defer_allocation ) {
        size_t current_memory_id = memory_id;
        std::string memory_path_desc = "  ";
        size_t path_total_size = 0;
        const size_t path_allocation_size = _memory_chunks[memory_id].size_in_bytes();
        while ( current_memory_id != kInvalidMemoryChunk ) {
          const MemoryChunk& mem_chunk = _memory_chunks[current_memory_id];
          path_total_size += mem_chunk._initial_size;
          const std::string& group = memory_id_to_group_key[current_memory_id].first;
          const std::string& key = memory_id_to_group_key[current_memory_id].second;
          memory_path_desc += "(" + group + "," + key + ") = "
                                  + std::to_string(size_in_megabyte(mem_chunk._initial_size))
                                  + " MB";
          current_memory_id = mem_chunk._next_memory_chunk_id;
          if ( current_memory_id != kInvalidMemoryChunk ) {
            memory_path_desc += " -> ";
          }
        }
        total_size += path_total_size;
        allocated_size += path_allocation_size;
        LOG << "  Allocated" << size_in_megabyte(path_allocation_size) << "MB for the following memory path"
            << "and saved" << size_in_megabyte(path_total_size - path_allocation_size) << "MB:";
        LOG << memory_path_desc << "\n";
      }
    }

    LOG << BOLD << "Summary:" << END;
    LOG << "  Size of registered memory chunks         =" << size_in_megabyte(total_size) << "MB";
    LOG << "  Initial allocated size of memory chunks  =" << size_in_megabyte(allocated_size) << "MB";
    LOG << "  Saved memory due to memory optimizations =" << size_in_megabyte(total_size - allocated_size) << "MB";
  }

 private:
  explicit MemoryPoolT() :
    _is_initialized(false),
    _page_size(0),
    _memory_groups(),
    _memory_chunks(),
    _next_active_memory_chunk(0),
    _active_memory_chunks(),
    _use_round_robin_assignment(true),
    _use_minimum_allocation_size(true),
    _use_unused_memory_chunks(true) {
    #if _WIN32
      SYSTEM_INFO sysInfo;
      GetSystemInfo(&sysInfo);
      _page_size = sysInfo.dwPageSize;
    #else
      _page_size = sysconf(_SC_PAGE_SIZE);
    #endif
  }

  // ! Returns a pointer to memory chunk under the corresponding group with
  // ! the specified key.
  MemoryChunk* find_memory_chunk(const std::string& group,
                                 const std::string& key) {

    if ( _memory_groups.find(group) != _memory_groups.end() &&
         _memory_groups.at(group).containsKey(key) ) {
      const size_t memory_id = _memory_groups.at(group).getKey(key);
      ASSERT(memory_id < _memory_chunks.size());
      return &_memory_chunks[memory_id];
    }
    return nullptr;
  }

  void update_active_memory_chunks() {
    _active_memory_chunks.clear();
    for ( size_t memory_id = 0; memory_id < _memory_chunks.size(); ++memory_id ) {
      if ( _memory_chunks[memory_id]._data ) {
        _active_memory_chunks.push_back(memory_id);
      }
    }
    _next_active_memory_chunk = 0;
  }

  static double size_in_megabyte(const size_t size_in_bytes) {
    return static_cast<double>(size_in_bytes) / 1000000.0;
  }

  // ! Tries to match memory chunks between different groups.
  // ! If a memory chunk is matched with an other memory chunk of
  // ! an other group of an earlier stage, than allocation of that
  // ! chunk is deferred. Once the memory pool is signaled that
  // ! the memory chunks of a group are not required any more
  // ! (release_memory_group), than the memory chunks are transfered
  // ! to next group.
  void optimize_memory_allocations() {
    using MemGroup = std::pair<std::string, size_t>; // <Group ID, Stage>
    using MemChunk = std::pair<size_t, size_t>; // <Memory ID, Size in Bytes>

    // Sort memory groups according to stage
    std::vector<MemGroup> mem_groups;
    for ( const auto& mem_group : _memory_groups ) {
      mem_groups.push_back(std::make_pair(mem_group.first, mem_group.second._stage));
    }
    std::sort(mem_groups.begin(), mem_groups.end(),
      [&](const MemGroup& lhs, const MemGroup& rhs) {
      return lhs.second < rhs.second;
    });

    auto fill_mem_chunks = [&](std::vector<MemChunk>& mem_chunks,
                              const std::string group) {
      for ( const auto& key : _memory_groups.at(group)._key_to_memory_id ) {
        const size_t memory_id = key.second;
        const MemoryChunk& memory_chunk = _memory_chunks[memory_id];
        const size_t size_in_bytes = memory_chunk._num_elements * memory_chunk._size;
        mem_chunks.push_back(std::make_pair(memory_id, size_in_bytes));
      }
      std::sort(mem_chunks.begin(), mem_chunks.end(),
        [&](const MemChunk& lhs, const MemChunk& rhs) {
          return lhs.second < rhs.second || (lhs.second == rhs.second && lhs.first < rhs.first );
        });
    };

    if ( !mem_groups.empty() ) {
      std::vector<MemChunk> lhs_mem_chunks;
      fill_mem_chunks(lhs_mem_chunks, mem_groups[0].first);
      for ( size_t i = 1; i < mem_groups.size(); ++i /* i = stage */ ) {
        // lhs_mem_chunks contains all memory chunks corresponding
        // to a stage j with j < i that are not matched (in increasing
        // order of its size in bytes). rhs_mem_chunks contains all memory
        // chunks of stage i (in increasing order of its size in bytes).
        // Memory chunks are matched greedily according to their size
        // in bytes => to biggest memory chunks of both groups are
        // matched.
        std::vector<MemChunk> rhs_mem_chunks;
        fill_mem_chunks(rhs_mem_chunks, mem_groups[i].first);
        while ( !lhs_mem_chunks.empty() && !rhs_mem_chunks.empty() ) {
          const size_t lhs_mem_id = lhs_mem_chunks.back().first;
          const size_t rhs_mem_id = rhs_mem_chunks.back().first;
          ASSERT(lhs_mem_id != rhs_mem_id);
          ASSERT(lhs_mem_id < _memory_chunks.size());
          ASSERT(rhs_mem_id < _memory_chunks.size());
          _memory_chunks[lhs_mem_id]._next_memory_chunk_id = rhs_mem_id;
          _memory_chunks[rhs_mem_id]._defer_allocation = true;
          lhs_mem_chunks.pop_back();
          rhs_mem_chunks.pop_back();
        }
        fill_mem_chunks(lhs_mem_chunks, mem_groups[i].first);
      }
    }

    auto augment_memory = [&](const size_t memory_id) {
      ASSERT(memory_id < _memory_chunks.size());
      MemoryChunk& memory_chunk = _memory_chunks[memory_id];
      if ( !memory_chunk._defer_allocation ) {
        std::vector<MemoryChunk*> s;
        s.push_back(&memory_chunk);
        size_t max_num_elements = memory_chunk._num_elements;
        size_t max_size = memory_chunk._size;
        while ( s.back()->_next_memory_chunk_id != kInvalidMemoryChunk ) {
          const size_t next_memory_id = s.back()->_next_memory_chunk_id;
          ASSERT(next_memory_id < _memory_chunks.size());
          MemoryChunk& next_memory_chunk = _memory_chunks[next_memory_id];
          const size_t num_elements = next_memory_chunk._num_elements;
          const size_t size = next_memory_chunk._size;
          if ( num_elements * size > max_num_elements * max_size ) {
            max_num_elements = num_elements;
            max_size = size;
          }
          s.push_back(&next_memory_chunk);
        }

        while ( !s.empty() ) {
          s.back()->_num_elements = max_num_elements;
          s.back()->_size = max_size;
          s.back()->_total_size = max_size * max_num_elements;
          s.pop_back();
        }
      }
    };

    // Adapts the allocation sizes along path of matched memory chunks.
    // Allocation size must be the maximum size along that path.
    for ( size_t memory_id = 0; memory_id < _memory_chunks.size(); ++memory_id ) {
      augment_memory(memory_id);
    }
  }

  // ! Read-Write Lock for memory pool
  // ! Initialize Flag
  bool _is_initialized;
  // ! Page size of the system
  size_t _page_size;
  // ! Mapping from group-key to a memory chunk id
  // ! The memory chunk id maps points to the memory chunk vector
  std::unordered_map<std::string, MemoryGroup> _memory_groups;
  // ! Memory chunks
  std::vector<MemoryChunk> _memory_chunks;
  // ! Next active memory chunk for unused memory allocation (round-robin fashion)
  size_t _next_active_memory_chunk;
  // ! Active memory chunks (with allocated memory)
  std::vector<size_t> _active_memory_chunks;

  bool _use_round_robin_assignment;
  bool _use_minimum_allocation_size;
  bool _use_unused_memory_chunks;
};

/**
 * Currently, the memory pool only works if we partition one instance at a time.
 * However, when using the library interface, it is possible that several
 * instances are partitioned simultanously. Therefore, we disable the memory
 * pool in case we compile the library interface.
 */
class DoNothingMemoryPool {

 public:
  DoNothingMemoryPool(const DoNothingMemoryPool&) = delete;
  DoNothingMemoryPool & operator= (const DoNothingMemoryPool &) = delete;

  DoNothingMemoryPool(DoNothingMemoryPool&&) = delete;
  DoNothingMemoryPool & operator= (DoNothingMemoryPool &&) = delete;

  static DoNothingMemoryPool& instance() {
    static DoNothingMemoryPool instance;
    return instance;
  }

  bool isInitialized() const {
    return true;
  }

  void register_memory_group(const std::string&,
                             const size_t) { }

  void register_memory_chunk(const std::string&,
                             const std::string&,
                             const size_t,
                             const size_t) { }

  void allocate_memory_chunks() { }
  void allocate_memory_chunks(const bool) { }

  char* request_mem_chunk(const std::string&,
                          const std::string&,
                          const size_t,
                          const size_t) {
    return nullptr;
  }

  char* request_unused_mem_chunk(const size_t,
                                 const size_t) {
    return nullptr;
  }
  char* request_unused_mem_chunk(const size_t,
                                 const size_t,
                                 const bool) {
    return nullptr;
  }

  char* mem_chunk(const std::string&,
                  const std::string&) {
    return nullptr;
  }
  void release_mem_chunk(const std::string&,
                         const std::string&) { }

  void release_mem_group(const std::string&) { }

  void reset() { }

  void free_memory_chunks() {}

  // ! Only for testing
  void deactivate_round_robin_assignment() { }

  // ! Only for testing
  void deactivate_minimum_allocation_size() { }

  void activate_unused_memory_allocations() { }

  void deactivate_unused_memory_allocations() { }

  size_t size_in_bytes(const std::string&,
                       const std::string&) {
    return 0;
  }

  void memory_consumption(utils::MemoryTreeNode*) const { }

  void explain_optimizations() const { }

 private:
  DoNothingMemoryPool() { }
};

#ifdef MT_KAHYPAR_LIBRARY_MODE
using MemoryPool = DoNothingMemoryPool;
#else
using MemoryPool = MemoryPoolT;
#endif

}  // namespace parallel
}  // namespace mt_kahypar
