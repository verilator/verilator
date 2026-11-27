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

#ifdef __GNUC__
#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Weffc++"
#endif

#include "repcut_serial.h"

#include <atomic>
#include <type_traits>

#include "mt-kahypar/macros.h"

template<typename T>
class CAtomic : public std::atomic<T> {
public:
  // boilerplate to make it 'movable'.
  using Base = std::atomic<T>;

  explicit CAtomic(const T value = T()) : Base(value) { }

  CAtomic(const CAtomic& other) : Base(other.load(std::memory_order_relaxed)) { }

  CAtomic& operator=(const CAtomic& other) {
    Base::store(other.load(std::memory_order_relaxed), std::memory_order_relaxed);
    return *this;
  }

  CAtomic(CAtomic&& other) noexcept : Base(other.load(std::memory_order_relaxed)) { }

  CAtomic& operator=(CAtomic&& other) noexcept {
    Base::store(other.load(std::memory_order_relaxed), std::memory_order_relaxed);
    return *this;
  }

  // unfortunately the internal value M_i is private, so we cannot issue __atomic_add_fetch( &M_i, i, int(m) ) ourselves
  MT_KAHYPAR_ATTRIBUTE_ALWAYS_INLINE T add_fetch(T i, std::memory_order m = std::memory_order_seq_cst) {
    return Base::fetch_add(i, m) + i;
  }

  MT_KAHYPAR_ATTRIBUTE_ALWAYS_INLINE T sub_fetch(T i, std::memory_order m = std::memory_order_seq_cst) {
    return Base::fetch_sub(i, m) - i;
  }
};

class SpinLock {
public:
  SpinLock() = default;
  SpinLock(const SpinLock&) { }
  SpinLock& operator=(const SpinLock&) { _locked = false; return *this; }

  bool tryLock() {
    if (_locked) return false;
    _locked = true;
    return true;
  }

  void lock() {
    ALWAYS_ASSERT(!_locked);
    _locked = true;
  }

  void unlock() { _locked = false; }

private:
  bool _locked = false;
};


namespace mt_kahypar {
namespace parallel {

// For non-integral types, e.g. floating point. used in community detecion

template <class T>
class AtomicWrapper : public std::atomic<T> {
 public:
  explicit AtomicWrapper(const T value = T()) :
    std::atomic<T>(value) { }

  AtomicWrapper(const AtomicWrapper& other) :
    std::atomic<T>(other.load()) { }

  AtomicWrapper & operator= (const AtomicWrapper& other) {
    this->store(other.load());
    return *this;
  }

  AtomicWrapper(AtomicWrapper&& other) {
    this->store(other.load());
  }

  void operator+= (T other) {
    T cur = this->load(std::memory_order_relaxed);
    while (!this->compare_exchange_weak(cur, cur + other, std::memory_order_relaxed)) {
      cur = this->load(std::memory_order_relaxed);
    }
  }

  void operator-= (T other) {
    T cur = this->load(std::memory_order_relaxed);
    while (!this->compare_exchange_weak(cur, cur - other, std::memory_order_relaxed)) {
      cur = this->load(std::memory_order_relaxed);
    }
  }
};

//template<typename T> using IntegralAtomicWrapper = CAtomic<T>;


template <typename T>
class IntegralAtomicWrapper {
  static_assert(std::is_integral<T>::value, "Value must be of integral type");
  // static_assert( std::atomic<T>::is_always_lock_free, "Atomic must be lock free" );

 public:
  explicit IntegralAtomicWrapper(const T value = T()) :
    _value(value) { }

  IntegralAtomicWrapper(const IntegralAtomicWrapper& other) :
    _value(other._value.load()) { }

  IntegralAtomicWrapper & operator= (const IntegralAtomicWrapper& other) {
    _value = other._value.load();
    return *this;
  }

  IntegralAtomicWrapper(IntegralAtomicWrapper&& other) :
    _value(other._value.load()) { }

  IntegralAtomicWrapper & operator= (IntegralAtomicWrapper&& other) {
    _value = other._value.load();
    return *this;
  }

  IntegralAtomicWrapper & operator= (T desired) noexcept {
    _value = desired;
    return *this;
  }

  void store(T desired, std::memory_order order = std::memory_order_seq_cst) noexcept {
    _value.store(desired, order);
  }

  T load(std::memory_order order = std::memory_order_seq_cst) const noexcept {
    return _value.load(order);
  }

  operator T () const noexcept {
    return _value.load();
  }

  T exchange(T desired, std::memory_order order = std::memory_order_seq_cst) noexcept {
    return _value.exchange(desired, order);
  }

  bool compare_exchange_weak(T &expected, T desired, std::memory_order order = std::memory_order_seq_cst) noexcept {
    return _value.compare_exchange_weak(expected, desired, order);
  }

  bool compare_exchange_strong(T &expected, T desired, std::memory_order order = std::memory_order_seq_cst) noexcept {
    return _value.compare_exchange_strong(expected, desired, order);
  }

  T fetch_add(T arg, std::memory_order order = std::memory_order_seq_cst) noexcept {
    return _value.fetch_add(arg, order);
  }

  T fetch_sub(T arg, std::memory_order order = std::memory_order_seq_cst) noexcept {
    return _value.fetch_sub(arg, order);
  }

  T fetch_and(T arg, std::memory_order order = std::memory_order_seq_cst) noexcept {
    return _value.fetch_and(arg, order);
  }

  T fetch_or(T arg, std::memory_order order = std::memory_order_seq_cst) noexcept {
    return _value.fetch_or(arg, order);
  }

  T fetch_xor(T arg, std::memory_order order = std::memory_order_seq_cst) noexcept {
    return _value.fetch_xor(arg, order);
  }

  T operator++ () noexcept {
    return ++_value;
  }

  T operator++ (int) noexcept {
    return _value++;
  }

  T operator-- () noexcept {
    return --_value;
  }

  T operator-- (int) noexcept {
    return _value++;
  }

  T operator+= (T arg) noexcept {
    return _value.operator+=(arg);
  }

  T operator-= (T arg) noexcept {
    return _value.operator-=(arg);
  }

  T operator&= (T arg) noexcept {
    return _value.operator&=(arg);
  }

  T operator|= (T arg) noexcept {
    return _value.operator|=(arg);
  }

  T operator^= (T arg) noexcept {
    return _value.operator^=(arg);
  }

 private:
  std::atomic<T> _value;
};

template <typename T>
T atomic_load(const T &value,
                    std::memory_order order = std::memory_order_seq_cst) {
  return repcut_serial::Ref<T>(const_cast<T &>(value)).load(order);
}

#ifdef __GNUC__
#pragma GCC diagnostic pop
#endif
}  // namespace parallel
}  // namespace mt_kahypar
