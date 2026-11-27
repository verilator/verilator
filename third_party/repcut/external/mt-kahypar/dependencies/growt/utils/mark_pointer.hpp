#pragma once

/*******************************************************************************
 * mark_pointer.hpp
 *
 * Set of functions, that uses the topmost 16 bits of an atomic pointer to
 * store some flags (e.g. for smart pointers / marking in concurrent algorithms)
 *
 * ATTENTION: This works, because the topmost 16 bits of pointers are currently
 * unused (on current hardware with current operating systems).
 * If this should ever change, we can probably use the bottommost bits (but this
 * really depends on the alignment of the stored elements).
 *
 * Part of my utils library utils_tm - https://github.com/TooBiased/utils_tm.git
 *
 * Copyright (C) 2019 Tobias Maier <t.maier@kit.edu>
 *
 * All rights reserved. Published under the BSD-2 license in the LICENSE file.
 ******************************************************************************/

#include <atomic>
#include <cstddef>

#include "concurrency/memory_order.hpp"

namespace utils_tm
{
namespace mark
{

namespace ctm = concurrency_tm;

/* FLAGS & BITMASK DEFINITIONS ************************************************/
template <size_t i>
inline constexpr size_t flag()
{
    return (1ull << (63 - i));
}

template <size_t i>
inline constexpr size_t mask()
{
    return ~flag<i>();
}

template <size_t i>
inline constexpr size_t lower()
{
    return flag<i>() - 1;
}


/* MARK ***********************************************************************/
template <size_t i, class T = void>
inline bool atomic_mark(std::atomic<T*>&  tar,
                        T*&               exp,
                        std::memory_order order = ctm::mo_seq_cst)
{
    auto temp = (T*)(size_t(exp) | flag<i>());
    return tar.compare_exchange_strong(exp, temp, order);
}

template <size_t i, class T = void>
inline constexpr T* mark(T* ptr)
{
    return (T*)(size_t(ptr) | flag<i>());
}


/* UNMARK *********************************************************************/
template <size_t i, class T = void>
inline bool atomic_unmark_cas(std::atomic<T*>&  tar,
                              T*                exp,
                              std::memory_order order = ctm::mo_seq_cst)
{
    return tar.compare_exchange_strong(exp, exp & mask<i>(), order);
}

template <size_t i, class T = void>
inline bool
atomic_unmark(std::atomic<T*>& tar, std::memory_order order = ctm::mo_seq_cst)
{
    return tar.fetch_and(mask<i>(), order) & flag<i>();
}

template <size_t i, class T = void>
inline constexpr T* unmark(T* ptr)
{
    return (T*)(size_t(ptr) & mask<i>());
}


/* CLEAR **********************************************************************/
template <size_t i, class T = void>
inline bool
atomic_clear(std::atomic<T*>& tar, std::memory_order order = ctm::mo_seq_cst)
{
    return tar.fetch_and(lower<15>(), ctm::mo_seq_cst);
}

template <class T = void>
inline constexpr T* clear(T* ptr)
{
    return (T*)(size_t(ptr) & lower<15>());
}


/* ACCESS FLAGS ***************************************************************/
template <size_t i, class T = void>
inline constexpr bool get_mark(T* ptr)
{
    return size_t(ptr) & flag<i>();
}

template <class T = void>
inline constexpr bool is_marked(T* ptr)
{
    return bool(size_t(ptr) & (~lower<15>()));
}

} // namespace mark
} // namespace utils_tm
