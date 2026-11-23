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

#include <tbb/parallel_invoke.h>

#include "mt-kahypar/datastructures/pin_count_in_part.h"
#include "mt-kahypar/datastructures/connectivity_set.h"
#include "mt-kahypar/datastructures/sparse_pin_counts.h"

namespace mt_kahypar {
namespace ds {

class ConnectivityInfo {

 public:
  using Iterator = typename ConnectivitySets::Iterator;

  ConnectivityInfo() :
    _pin_counts(),
    _con_set() { }

  ConnectivityInfo(const HyperedgeID num_hyperedges,
                   const PartitionID k,
                   const HypernodeID max_value) :
    _pin_counts(num_hyperedges, k, max_value, false),
    _con_set(num_hyperedges, k, false) { }

  ConnectivityInfo(const HyperedgeID num_hyperedges,
                   const PartitionID k,
                   const HypernodeID max_value,
                   parallel_tag_t) :
    _pin_counts(),
    _con_set() {
    tbb::parallel_invoke([&] {
      _pin_counts.initialize(num_hyperedges, k, max_value, true);
    }, [&] {
      _con_set = ConnectivitySets(num_hyperedges, k, true);
    });
  }

  ConnectivityInfo(const ConnectivityInfo&) = delete;
  ConnectivityInfo & operator= (const ConnectivityInfo &) = delete;

  ConnectivityInfo(ConnectivityInfo&& other) :
    _pin_counts(std::move(other._pin_counts)),
    _con_set(std::move(other._con_set)) { }

  ConnectivityInfo & operator= (ConnectivityInfo&& other) {
    _pin_counts = std::move(other._pin_counts);
    _con_set = std::move(other._con_set);
    return *this;
  }

  // ################## Connectivity Set ##################

  inline void addBlock(const HyperedgeID he, const PartitionID p) {
    _con_set.add(he, p);
  }

  inline void removeBlock(const HyperedgeID he, const PartitionID p) {
    _con_set.remove(he, p);
  }

  inline bool containsBlock(const HyperedgeID he, const PartitionID p) const {
    return _con_set.contains(he, p);
  }

  inline void clear(const HyperedgeID he) {
    _con_set.clear(he);
  }

  inline PartitionID connectivity(const HyperedgeID he) const {
    return _con_set.connectivity(he);
  }

  inline IteratorRange<Iterator> connectivitySet(const HyperedgeID he) const {
    return _con_set.connectivitySet(he);
  }

  inline StaticBitset& shallowCopy(const HyperedgeID he) const {
    return _con_set.shallowCopy(he);
  }

  inline Bitset& deepCopy(const HyperedgeID he) const {
    return _con_set.deepCopy(he);
  }

  // ################## Pin Count In Part ##################

  // ! Returns the pin count of the hyperedge in the corresponding block
  inline HypernodeID pinCountInPart(const HyperedgeID he,
                                    const PartitionID id) const {
    return _pin_counts.pinCountInPart(he, id);
  }

  // ! Sets the pin count of the hyperedge in the corresponding block to value
  inline void setPinCountInPart(const HyperedgeID he,
                                const PartitionID id,
                                const HypernodeID value) {
    _pin_counts.setPinCountInPart(he, id, value);
  }

  // ! Increments the pin count of the hyperedge in the corresponding block
  inline HypernodeID incrementPinCountInPart(const HyperedgeID he,
                                             const PartitionID id) {
    return _pin_counts.incrementPinCountInPart(he, id);
  }

  // ! Decrements the pin count of the hyperedge in the corresponding block
  inline HypernodeID decrementPinCountInPart(const HyperedgeID he,
                                             const PartitionID id) {
    return _pin_counts.decrementPinCountInPart(he, id);
  }

  // ! Returns a snapshot of the pin counts of the hyperedge
  inline PinCountSnapshot& pinCountSnapshot(const HyperedgeID he) {
    return _pin_counts.snapshot(he);
  }

  // ################## Miscellaneous ##################

  // ! Returns the size in bytes of this data structure
  size_t size_in_bytes() const {
    return _pin_counts.size_in_bytes() /* + connectivity set */;
  }

  void reset(const bool reset_parallel = false) {
    if ( reset_parallel ) {
      tbb::parallel_invoke(
        [&] { _pin_counts.reset(true); },
        [&] { _con_set.reset(true); });
    } else {
      _pin_counts.reset(false);
      _con_set.reset(false);
    }
  }

  void freeInternalData() {
    tbb::parallel_invoke(
      [&] { _pin_counts.freeInternalData(); },
      [&] { _con_set.freeInternalData(); });
  }

  void memoryConsumption(utils::MemoryTreeNode* parent) const {
    ASSERT(parent);
    _pin_counts.memoryConsumption(parent);
    _con_set.memoryConsumption(parent);
  }


 private:
  // ! For each hyperedge and each block, _pins_in_part stores the
  // ! number of pins in that block
  PinCountInPart _pin_counts;

  // ! For each hyperedge, _connectivity_set stores the set of blocks that the hyperedge spans
  ConnectivitySets _con_set;
};

class SparseConnectivityInfo {

 public:
  using Iterator = typename SparsePinCounts::Iterator;

  SparseConnectivityInfo() :
    _pin_counts() { }

  SparseConnectivityInfo(const HyperedgeID num_hyperedges,
                         const PartitionID k,
                         const HypernodeID max_value) :
    _pin_counts(num_hyperedges, k, max_value, false) { }

  SparseConnectivityInfo(const HyperedgeID num_hyperedges,
                         const PartitionID k,
                         const HypernodeID max_value,
                         parallel_tag_t) :
    _pin_counts() {
    _pin_counts.initialize(num_hyperedges, k, max_value, true);
  }

  SparseConnectivityInfo(const SparseConnectivityInfo&) = delete;
  SparseConnectivityInfo & operator= (const SparseConnectivityInfo &) = delete;

  SparseConnectivityInfo(SparseConnectivityInfo&& other) :
    _pin_counts(std::move(other._pin_counts)) { }

  SparseConnectivityInfo & operator= (SparseConnectivityInfo&& other) {
    _pin_counts = std::move(other._pin_counts);
    return *this;
  }

  // ################## Connectivity Set ##################

  inline void addBlock(const HyperedgeID, const PartitionID) {
    // Do nothing, handled by incrementPinCountInPart
  }

  inline void removeBlock(const HyperedgeID, const PartitionID) {
    // Do nothing, handled by decrementPinCountInPart
  }

  inline bool containsBlock(const HyperedgeID he, const PartitionID p) const {
    return _pin_counts.contains(he, p);
  }

  inline void clear(const HyperedgeID he) {
    _pin_counts.clear(he);
  }

  inline PartitionID connectivity(const HyperedgeID he) const {
    return _pin_counts.connectivity(he);
  }

  inline IteratorRange<Iterator> connectivitySet(const HyperedgeID he) const {
    return _pin_counts.connectivitySet(he);
  }

  inline StaticBitset& shallowCopy(const HyperedgeID he) const {
    return _pin_counts.shallowCopy(he);
  }

  inline Bitset& deepCopy(const HyperedgeID he) const {
    return _pin_counts.deepCopy(he);
  }

  // ################## Pin Count In Part ##################

  // ! Returns the pin count of the hyperedge in the corresponding block
  inline HypernodeID pinCountInPart(const HyperedgeID he,
                                    const PartitionID id) const {
    return _pin_counts.pinCountInPart(he, id);
  }

  // ! Sets the pin count of the hyperedge in the corresponding block to value
  inline void setPinCountInPart(const HyperedgeID he,
                                const PartitionID id,
                                const HypernodeID value) {
    _pin_counts.setPinCountInPart(he, id, value);
  }

  // ! Increments the pin count of the hyperedge in the corresponding block
  inline HypernodeID incrementPinCountInPart(const HyperedgeID he,
                                             const PartitionID id) {
    return _pin_counts.incrementPinCountInPart(he, id);
  }

  // ! Decrements the pin count of the hyperedge in the corresponding block
  inline HypernodeID decrementPinCountInPart(const HyperedgeID he,
                                             const PartitionID id) {
    return _pin_counts.decrementPinCountInPart(he, id);
  }

  // ! Returns a snapshot of the pin counts of the hyperedge
  inline PinCountSnapshot& pinCountSnapshot(const HyperedgeID he) {
    return _pin_counts.snapshot(he);
  }

  // ################## Miscellaneous ##################

  // ! Returns the size in bytes of this data structure
  size_t size_in_bytes() const {
    return _pin_counts.size_in_bytes();
  }

  void reset(const bool reset_parallel = false) {
    if ( reset_parallel ) {
      _pin_counts.reset(true);
    } else {
      _pin_counts.reset(false);
    }
  }

  void freeInternalData() {
    _pin_counts.freeInternalData();
  }

  void memoryConsumption(utils::MemoryTreeNode* parent) const {
    ASSERT(parent);
    _pin_counts.memoryConsumption(parent);
  }

 private:
  // ! For each hyperedge and each block, _pins_in_part stores the
  // ! number of pins in that block and also the connectivity set
  SparsePinCounts _pin_counts;
};

}  // namespace ds
}  // namespace mt_kahypar
