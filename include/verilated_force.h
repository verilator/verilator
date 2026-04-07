// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
//
// Code available from: https://verilator.org
//
// Copyright 2026-2026 by Wilson Snyder. This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************
///
/// \file
/// \brief Verilator: Runtime support for force/release statements
///
/// This file provides runtime data structures for efficient dynamic
/// resolution of force/release statements. A sorted list of active
/// forces is maintained that can be efficiently queried and modified
/// at runtime.
///
//*************************************************************************

#ifndef VERILATOR_VERILATED_FORCE_H_
#define VERILATOR_VERILATED_FORCE_H_

#include "verilatedos.h"

#include <algorithm>
#include <cassert>
#include <cstddef>
#include <type_traits>
#include <vector>

template <typename T>
using VlForceBaseType = typename std::remove_cv<typename std::remove_reference<T>::type>::type;

// VlForceRead - Helper functions to read a forced value
//
// These functions combine original value with forced values based on
// VlForceVec entries.
// This achieves O(k) complexity where k = number of active forces.

template <typename T>
struct VlForceTypeInfo final {
    using Type = VlForceBaseType<T>;
    static constexpr bool bitwise
        = std::is_integral<Type>::value || std::is_enum<Type>::value || VlIsVlWide<Type>::value;
    static constexpr bool unpackedArray = false;
};

template <typename T>
struct VlForceArrayIndexer final {
    static constexpr std::size_t size = 1;

    static T& elem(T& value, std::size_t) { return value; }
};

template <typename T, std::size_t N>
struct VlForceArrayIndexer<VlUnpacked<T, N>> final {
    static constexpr std::size_t size = N * VlForceArrayIndexer<T>::size;

    static auto& elem(VlUnpacked<T, N>& array, std::size_t index) {
        constexpr std::size_t subSize = VlForceArrayIndexer<T>::size;
        return VlForceArrayIndexer<T>::elem(array[index / subSize], index % subSize);
    }
};

template <typename T, std::size_t N>
struct VlForceTypeInfo<VlUnpacked<T, N>> final {
    using Type = VlUnpacked<T, N>;
    static constexpr bool bitwise = false;
    static constexpr bool unpackedArray = true;
};

template <typename T, bool = std::is_enum<T>::value>
struct VlForceStorageTypeOf final {
    using type = typename std::make_unsigned<T>::type;
};

template <typename T>
struct VlForceStorageTypeOf<T, true> final {
    using type = typename std::make_unsigned<typename std::underlying_type<T>::type>::type;
};

template <typename T>
using VlForceStorageType = typename VlForceStorageTypeOf<VlForceBaseType<T>>::type;

//=============================================================================
// VlForceVec - Vector of active force entries for a signal
//
// This class maintains a sorted vector of non-overlapping force entries.
// When a new force is added, it removes or trims existing entries that
// overlap with the new range.
//
// The generated code will:
// 1. Use addForce/release to update the active forces
// 2. Call a generated read function that iterates entries and evaluates RHS

class VlForceVec final {
private:
    struct Entry final {
        int m_lsb;  // Inclusive lower bit
        int m_msb;  // Inclusive upper bit
        int m_rhsLsb;  // Destination index that maps to RHS index 0
        const void* m_rhsDatap;  // Pointer to RHS storage

        bool operator<(const Entry& other) const { return m_msb < other.m_msb; }
    };

    std::vector<Entry> m_entries;  // Sorted by msb, non-overlapping

    std::vector<Entry>::iterator trimEntries(int lsb, int msb) {
        auto it = std::lower_bound(m_entries.begin(), m_entries.end(), lsb,
                                   [](const Entry& e, int bit) { return e.m_msb < bit; });
        while (it != m_entries.end() && it->m_lsb <= msb) {
            if (it->m_lsb < lsb && it->m_msb > msb) {
                const Entry right{msb + 1, it->m_msb, it->m_rhsLsb, it->m_rhsDatap};
                it->m_msb = lsb - 1;
                return m_entries.insert(++it, right);
            }
            if (it->m_lsb < lsb) {
                it->m_msb = lsb - 1;
                ++it;
                continue;
            }
            if (it->m_msb > msb) {
                it->m_lsb = msb + 1;
                return it;
            }
            it = m_entries.erase(it);
        }
        return it;
    }

    static QData extractRhsChunk(const Entry& entry, int rhsLsb, int width) {
        assert(width > 0 && width <= std::numeric_limits<QData>::digits);
        assert(rhsLsb >= 0);

        const QData mask = width >= std::numeric_limits<QData>::digits
                               ? ~static_cast<QData>(0)
                               : ((static_cast<QData>(1) << width) - 1);
        const int rhsWidth = entry.m_msb - entry.m_rhsLsb + 1;
        if (rhsWidth <= std::numeric_limits<QData>::digits) {
            const QData rhsVal = static_cast<QData>(*static_cast<const QData*>(entry.m_rhsDatap));
            return (rhsVal >> rhsLsb) & mask;
        }

        const EData* const rhswp = static_cast<const EData*>(entry.m_rhsDatap);
        const int startWord = VL_BITWORD_E(rhsLsb);
        const int startBit = VL_BITBIT_E(rhsLsb);
        QData out = static_cast<QData>(rhswp[startWord]) >> startBit;
        int outBits = VL_EDATASIZE - startBit;
        if (outBits < width) {
            out |= static_cast<QData>(rhswp[startWord + 1]) << outBits;
            outBits += VL_EDATASIZE;
            if (outBits < width) { out |= static_cast<QData>(rhswp[startWord + 2]) << outBits; }
        }
        return out & mask;
    }

    template <typename T>
    static T applyBits(T cur, const Entry& entry, int lsb, int width, int rhsLsb) {
        const T lowMask = width >= static_cast<int>(sizeof(T) * 8)
                              ? ~static_cast<T>(0)
                              : static_cast<T>((static_cast<QData>(1) << width) - 1);
        const T mask = static_cast<T>(lowMask << lsb);
        const T rhsBits = static_cast<T>(
            (static_cast<T>(extractRhsChunk(entry, rhsLsb, width)) & lowMask) << lsb);
        return static_cast<T>((cur & ~mask) | (rhsBits & mask));
    }

    template <typename T>
    static T applyEntry(T result, const Entry& entry) {
        if VL_CONSTEXPR_CXX17 (VlIsVlWide<T>::value) {
            EData* const reswp = result.data();
            const int lword = VL_BITWORD_E(entry.m_lsb);
            const int hword = VL_BITWORD_E(entry.m_msb);
            for (int word = lword; word <= hword; ++word) {
                const int wordLsb = word * VL_EDATASIZE;
                const int segLsb = std::max(entry.m_lsb, wordLsb);
                const int segMsb = std::min(entry.m_msb, wordLsb + VL_EDATASIZE - 1);
                const int segWidth = segMsb - segLsb + 1;
                const int bitOffset = segLsb - wordLsb;
                const int rhsLsb = segLsb - entry.m_rhsLsb;
                reswp[word] = applyBits(reswp[word], entry, bitOffset, segWidth, rhsLsb);
            }
            return result;
        } else if VL_CONSTEXPR_CXX17 (VlForceTypeInfo<T>::bitwise) {
            using U = VlForceStorageType<T>;
            const int width = entry.m_msb - entry.m_lsb + 1;
            const int bits = static_cast<int>(sizeof(U) * 8);
            const int rhsLsb = entry.m_lsb - entry.m_rhsLsb;
            const QData rhsChunk = extractRhsChunk(entry, rhsLsb, width);
            if (width >= bits) return static_cast<T>(static_cast<U>(rhsChunk));
            return static_cast<T>(
                applyBits(static_cast<U>(result), entry, entry.m_lsb, width, rhsLsb));
        } else {
            return *static_cast<const VlForceBaseType<T>*>(entry.m_rhsDatap);
        }
    }

public:
    VlForceVec() = default;

    template <typename T>
    T read(T val) const {
        if VL_CONSTEXPR_CXX17 (VlForceTypeInfo<T>::unpackedArray) {
            // Handling the case of a nested flattened array using recursion
            using ElemRef
                = decltype(VlForceArrayIndexer<T>::elem(val, static_cast<std::size_t>(0)));
            using Elem = VlForceBaseType<ElemRef>;
            const int total = static_cast<int>(VlForceArrayIndexer<T>::size);
            for (const auto& entry : m_entries) {
                const Elem* const rhsBasep = static_cast<const Elem*>(entry.m_rhsDatap);
                const int startIdx = entry.m_lsb;
                const int endIdx = entry.m_msb;
                for (int idx = startIdx; idx <= endIdx; idx++) {
                    const int rhsIndex = idx - entry.m_rhsLsb;
                    const std::size_t uidx = static_cast<std::size_t>(idx);
                    VlForceArrayIndexer<T>::elem(val, uidx) = rhsBasep[rhsIndex];
                }
            }
            return val;
        }

        for (const auto& entry : m_entries) { val = applyEntry(val, entry); }
        return val;
    }

    template <typename T>
    T readIndex(T origVal, int index) const {
        if (m_entries.empty()) return origVal;

        const auto it = std::lower_bound(m_entries.begin(), m_entries.end(), index,
                                         [](const Entry& e, int idx) { return e.m_msb < idx; });
        if (it != m_entries.end() && it->m_lsb <= index) {
            const int rhsIndex = index - it->m_rhsLsb;
            const T* const rhsBasep = static_cast<const T*>(it->m_rhsDatap);
            return rhsBasep[rhsIndex];
        }
        return origVal;
    }

    void addForce(int lsb, int msb, const void* rhsDatap, int rhsLsb) {
        assert(lsb <= msb);
        assert(rhsDatap);
        assert(rhsLsb <= lsb);

        auto it = trimEntries(lsb, msb);
        m_entries.insert(it, {lsb, msb, rhsLsb, rhsDatap});
    }

    void release(int lsb, int msb) {
        assert(lsb <= msb);
        trimEntries(lsb, msb);
    }

    void touch() {}
};

#endif  // guard
