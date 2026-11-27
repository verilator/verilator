// C++17 primitives for the serial bundled partitioner.
// SPDX-FileCopyrightText: 2026-2026 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
#pragma once

#ifndef REPCUT_SERIAL_PARTITIONER
#error These reference operations require the serial bundled partitioner
#endif

#include <atomic>
#include <cstdint>
#include <cstring>
#include <type_traits>

namespace repcut_serial {
    // Ref is not atomic: task execution is synchronous and librepcut rejects
    // overlapping calls with a real atomic guard. Never use it for shared workers.
    template <class T> class Ref
    {
        static_assert((std::is_integral_v<T> || std::is_enum_v<T>) && !std::is_same_v<T, bool>);
        using Unsigned = std::make_unsigned_t<T>;
        T& m_value;

        T replaceBits(Unsigned bits) const
        {
            const T previous = m_value;
            // Preserve the two's-complement wrap of integral atomic arithmetic
            // without signed overflow or out-of-range unsigned-to-signed casts.
            std::memcpy(&m_value, &bits, sizeof(T));
            return previous;
        }

    public:
        explicit Ref(T& value) : m_value{value} {}
        T load(std::memory_order = std::memory_order_seq_cst) const { return m_value; }
        void store(T value, std::memory_order = std::memory_order_seq_cst) const { m_value = value; }
        T exchange(T value, std::memory_order = std::memory_order_seq_cst) const
        {
            const T previous = m_value;
            m_value = value;
            return previous;
        }
        T fetch_add(T value, std::memory_order = std::memory_order_seq_cst) const
        {
            return replaceBits(static_cast<Unsigned>(static_cast<std::uintmax_t>(static_cast<Unsigned>(m_value)) +
                                                     static_cast<Unsigned>(value)));
        }
        T fetch_sub(T value, std::memory_order = std::memory_order_seq_cst) const
        {
            return replaceBits(static_cast<Unsigned>(static_cast<std::uintmax_t>(static_cast<Unsigned>(m_value)) -
                                                     static_cast<Unsigned>(value)));
        }
        T fetch_xor(T value, std::memory_order = std::memory_order_seq_cst) const
        {
            return replaceBits(static_cast<Unsigned>(m_value) ^ static_cast<Unsigned>(value));
        }
        bool compare_exchange_strong(T& expected, T desired, std::memory_order = std::memory_order_seq_cst,
                                     std::memory_order = std::memory_order_seq_cst) const
        {
            if (m_value == expected) {
                m_value = desired;
                return true;
            }
            expected = m_value;
            return false;
        }
    };

    constexpr int popcount64(std::uint64_t value) noexcept
    {
        value -= (value >> 1) & UINT64_C(0x5555555555555555);
        value = (value & UINT64_C(0x3333333333333333)) + ((value >> 2) & UINT64_C(0x3333333333333333));
        value = (value + (value >> 4)) & UINT64_C(0x0f0f0f0f0f0f0f0f);
        return static_cast<int>((value * UINT64_C(0x0101010101010101)) >> 56);
    }
    constexpr int countrZero64(std::uint64_t value) noexcept
    {
        // For zero, unsigned wrap produces all ones and the result is 64.
        return popcount64((value & (std::uint64_t{0} - value)) - std::uint64_t{1});
    }
} // namespace repcut_serial
