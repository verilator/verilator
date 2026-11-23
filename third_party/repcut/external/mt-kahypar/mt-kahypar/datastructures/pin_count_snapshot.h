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

#include <cmath>


#include "mt-kahypar/macros.h"
#include "mt-kahypar/datastructures/hypergraph_common.h"
#include "mt-kahypar/datastructures/array.h"


namespace mt_kahypar {
namespace ds {

class PinCountSnapshot {

  static constexpr bool debug = false;

 public:
  using Value = uint64_t;

  PinCountSnapshot(const PartitionID k,
                   const HypernodeID max_value) :
    _k(k),
    _max_value(max_value),
    _bits_per_element(num_bits_per_element(max_value)),
    _entries_per_value(num_entries_per_value(k, max_value)),
    _extraction_mask(0),
    _pin_counts() {
    _extraction_mask = std::pow(2UL, _bits_per_element) - UL(1);
    _pin_counts.assign(num_values_per_hyperedge(k, max_value), 0);
  }

  PinCountSnapshot(const PinCountSnapshot&) = delete;
  PinCountSnapshot & operator= (const PinCountSnapshot &) = delete;

  PinCountSnapshot(PinCountSnapshot&& other) :
    _k(other._k),
    _max_value(other._max_value),
    _bits_per_element(other._bits_per_element),
    _entries_per_value(other._entries_per_value),
    _extraction_mask(other._extraction_mask),
    _pin_counts(std::move(other._pin_counts)) { }

  PinCountSnapshot & operator= (PinCountSnapshot&& other) {
    _k = other._k;
    _max_value = other._max_value;
    _bits_per_element = other._bits_per_element;
    _entries_per_value = other._entries_per_value;
    _extraction_mask = other._extraction_mask;
    _pin_counts = std::move(other._pin_counts);
    return *this;
  }

  void reset() {
    memset(_pin_counts.data(), 0, sizeof(Value) * _pin_counts.size());
  }

  void snapshot(const Value* src)  {
    std::memcpy(_pin_counts.data(), src, sizeof(Value) * _pin_counts.size());
  }

  // ! Returns the pin count of the hyperedge in the corresponding block
  inline HypernodeID pinCountInPart(const PartitionID id) const {
    ASSERT(id != kInvalidPartition && id < _k);
    const size_t value_pos = id / _entries_per_value;
    const size_t bit_pos = (id % _entries_per_value) * _bits_per_element;
    const Value mask = _extraction_mask << bit_pos;
    return (_pin_counts[value_pos] & mask) >> bit_pos;
  }

  // ! Sets the pin count of the hyperedge in the corresponding block to value
  inline void setPinCountInPart(const PartitionID id,
                                const HypernodeID value) {
    ASSERT(id != kInvalidPartition && id < _k);
    const size_t value_pos = id / _entries_per_value;
    const size_t bit_pos = (id % _entries_per_value) * _bits_per_element;
    updateEntry(_pin_counts[value_pos], bit_pos, value);
  }

  // ! Increments the pin count of the hyperedge in the corresponding block
  inline HypernodeID incrementPinCountInPart(const PartitionID id) {
    ASSERT(id != kInvalidPartition && id < _k);
    const size_t value_pos = id / _entries_per_value;
    const size_t bit_pos = (id % _entries_per_value) * _bits_per_element;
    const Value mask = _extraction_mask << bit_pos;
    Value& current_value = _pin_counts[value_pos];
    Value pin_count_in_part = (current_value & mask) >> bit_pos;
    ASSERT(pin_count_in_part + 1 <= _max_value);
    updateEntry(current_value, bit_pos, pin_count_in_part + 1);
    return pin_count_in_part + 1;
  }

  // ! Decrements the pin count of the hyperedge in the corresponding block
  inline HypernodeID decrementPinCountInPart(const PartitionID id) {
    ASSERT(id != kInvalidPartition && id < _k);
    const size_t value_pos = id / _entries_per_value;
    const size_t bit_pos = (id % _entries_per_value) * _bits_per_element;
    const Value mask = _extraction_mask << bit_pos;
    Value& current_value = _pin_counts[value_pos];
    Value pin_count_in_part = (current_value & mask) >> bit_pos;
    ASSERT(pin_count_in_part > UL(0));
    updateEntry(current_value, bit_pos, pin_count_in_part - 1);
    return pin_count_in_part - 1;
  }

 private:
  inline void updateEntry(Value& value,
                          const size_t bit_pos,
                          const Value new_value) {
    ASSERT(new_value <= _max_value);
    const Value zero_mask = ~(_extraction_mask << bit_pos);
    const Value value_mask = new_value << bit_pos;
    value = (value & zero_mask) | value_mask;
  }

  static size_t num_values_per_hyperedge(const PartitionID k,
                                         const HypernodeID max_value) {
    const size_t entries_per_value = num_entries_per_value(k, max_value);
    ASSERT(entries_per_value <= static_cast<size_t>(k));
    return k / entries_per_value + (k % entries_per_value!= 0);
  }

  static size_t num_entries_per_value(const PartitionID k,
                                      const HypernodeID max_value) {
    const size_t bits_per_element = num_bits_per_element(max_value);
    const size_t bits_per_value = sizeof(Value) * size_t(8);
    ASSERT(bits_per_element <= bits_per_value);
    return std::min(bits_per_value / bits_per_element, static_cast<size_t>(k));
  }

  static size_t num_bits_per_element(const HypernodeID max_value) {
    return std::ceil(std::log2(static_cast<double>(max_value + 1)));
  }

  PartitionID _k;
  HypernodeID _max_value;
  size_t _bits_per_element;
  size_t _entries_per_value;
  Value _extraction_mask;
  vec<Value> _pin_counts;
};
}  // namespace ds
}  // namespace mt_kahypar
