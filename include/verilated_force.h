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
        int m_lsb;  // Inclusive lower bit for scalar path or slot index for slot-tracked
        int m_msb;  // Inclusive upper bit for scalar path or slot index for slot-tracked
        int m_rhsLsb;  // Destination index that maps to RHS index 0
        const void* m_rhsDatap;  // Pointer to RHS storage (bitwise variables only)
        int m_bitLsb = 0;
        int m_bitMsb = 0;
        int m_elemWidth = 0;
        int m_id = -1;  // Force statement id for slot-tracked variables, else -1
    };

    std::vector<Entry> m_entries;  // Sorted by msb, non-overlapping

    std::vector<Entry>::iterator trimEntries(int lsb, int msb) {
        auto it = std::lower_bound(m_entries.begin(), m_entries.end(), lsb,
                                   [](const Entry& e, int bit) { return e.m_msb < bit; });
        while (it != m_entries.end() && it->m_lsb <= msb) {
            if (it->m_lsb < lsb && it->m_msb > msb) {
                Entry right = *it;  // Splits keep the owning force's identity on both halves
                right.m_lsb = msb + 1;
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

    // Split any entry spanning more slots than [elem, elem] so that per-bit trimming below
    // never leaves the vector unsorted, and so the split-off slot can carry a bit range
    void isolateSlot(int elem, int elemWidth) {
        auto it = std::lower_bound(m_entries.begin(), m_entries.end(), elem,
                                   [](const Entry& e, int idx) { return e.m_msb < idx; });
        if (it == m_entries.end() || it->m_lsb > elem) return;
        if (it->m_lsb == elem && it->m_msb == elem) {
            if (it->m_elemWidth == 0) {  // Owned whole; make that an explicit full bit range
                it->m_bitLsb = 0;
                it->m_bitMsb = elemWidth - 1;
                it->m_elemWidth = elemWidth;
            }
            return;
        }
        Entry mid = *it;
        mid.m_lsb = mid.m_msb = elem;
        if (mid.m_elemWidth == 0) {  // Owned whole; make that an explicit full bit range
            mid.m_bitLsb = 0;
            mid.m_bitMsb = elemWidth - 1;
            mid.m_elemWidth = elemWidth;
        }
        const Entry orig = *it;
        auto at = m_entries.erase(it);
        if (orig.m_msb > elem) {
            Entry right = orig;
            right.m_lsb = elem + 1;
            at = m_entries.insert(at, right);
        }
        at = m_entries.insert(at, mid);
        if (orig.m_lsb < elem) {
            Entry left = orig;
            left.m_msb = elem - 1;
            m_entries.insert(at, left);
        }
    }

    std::size_t trimElementBitRange(int elem, int bitLsb, int bitMsb, int elemWidth) {
        isolateSlot(elem, elemWidth);
        auto it = std::lower_bound(m_entries.begin(), m_entries.end(), elem,
                                   [](const Entry& e, int idx) { return e.m_msb < idx; });
        while (it != m_entries.end() && it->m_lsb <= elem) {
            if (it->m_bitMsb < bitLsb || it->m_bitLsb > bitMsb) {
                ++it;
                continue;
            }
            if (it->m_bitLsb < bitLsb && it->m_bitMsb > bitMsb) {
                Entry high = *it;
                high.m_bitLsb = bitMsb + 1;
                it->m_bitMsb = bitLsb - 1;
                m_entries.insert(it + 1, high);
                break;
            }
            if (it->m_bitLsb < bitLsb) {
                it->m_bitMsb = bitLsb - 1;
                ++it;
                continue;
            }
            if (it->m_bitMsb > bitMsb) {
                it->m_bitLsb = bitMsb + 1;
                break;
            }
            it = m_entries.erase(it);
        }
        const auto ins = std::lower_bound(m_entries.begin(), m_entries.end(), elem,
                                          [](const Entry& e, int idx) { return e.m_msb < idx; });
        return static_cast<std::size_t>(ins - m_entries.begin());
    }

    static QData extractRhsChunk(const Entry& entry, int rhsLsb, int width) {
        assert(width > 0 && width <= VL_QUADSIZE);
        assert(rhsLsb >= 0);

        const QData mask = static_cast<QData>(VL_MASK_Q(width));
        const int rhsWidth = entry.m_msb - entry.m_rhsLsb + 1;
        if (rhsWidth <= VL_QUADSIZE) {
            const QData rhsVal = static_cast<QData>(*static_cast<const QData*>(entry.m_rhsDatap));
            return (rhsVal >> rhsLsb) & mask;
        }

        WDataInP rhswp = WDataInP::external(static_cast<const EData*>(entry.m_rhsDatap));
        return VL_SEL_QWII(rhsWidth, rhswp, rhsLsb, width) & mask;
    }

    template <typename T>
    static T applyBits(T cur, const Entry& entry, int lsb, int width, int rhsLsb) {
        const T lowMask = static_cast<T>(VL_MASK_Q(width));
        const T mask = static_cast<T>(lowMask << lsb);
        const T rhsBits = static_cast<T>(
            (static_cast<T>(extractRhsChunk(entry, rhsLsb, width)) & lowMask) << lsb);
        return static_cast<T>((cur & ~mask) | (rhsBits & mask));
    }

    static void applyEntry(WDataOutP reswp, const Entry& entry, int entryLsb, int entryMsb,
                           int lsbOffset) {
        const int resLsb = entryLsb - lsbOffset;
        const int resMsb = entryMsb - lsbOffset;
        const int lword = VL_BITWORD_E(resLsb);
        const int hword = VL_BITWORD_E(resMsb);
        for (int word = lword; word <= hword; ++word) {
            const int wordLsb = word * VL_EDATASIZE;
            const int segLsb = std::max(resLsb, wordLsb);
            const int segMsb = std::min(resMsb, wordLsb + VL_EDATASIZE - 1);
            const int segWidth = segMsb - segLsb + 1;
            const int bitOffset = segLsb - wordLsb;
            const int rhsLsb = lsbOffset + segLsb - entry.m_rhsLsb;
            reswp[word] = applyBits(reswp[word], entry, bitOffset, segWidth, rhsLsb);
        }
    }

    template <typename T>
    static typename std::enable_if<!VlIsVlWide<T>::value && VlForceTypeInfo<T>::bitwise, T>::type
    applyEntry(T result, const Entry& entry) {
        using U = VlForceStorageType<T>;
        const int width = entry.m_msb - entry.m_lsb + 1;
        const int bits = static_cast<int>(sizeof(U) * 8);
        const int rhsLsb = entry.m_lsb - entry.m_rhsLsb;
        const QData rhsChunk = extractRhsChunk(entry, rhsLsb, width);
        if (width >= bits) return static_cast<T>(static_cast<U>(rhsChunk));
        return static_cast<T>(
            applyBits(static_cast<U>(result), entry, entry.m_lsb, width, rhsLsb));
    }

    template <typename T>
    static typename std::enable_if<!VlForceTypeInfo<T>::bitwise, T>::type
    applyEntry(T result, const Entry& entry) {
        static_cast<void>(result);
        return *static_cast<const VlForceBaseType<T>*>(entry.m_rhsDatap);
    }

    template <typename T>
    typename std::enable_if<VlIsVlWide<T>::value>::type applyEntries(T& val) const {
        for (const auto& entry : m_entries) {
            applyEntry(val, entry, entry.m_lsb, entry.m_msb, 0);
        }
    }

    template <typename T>
    typename std::enable_if<!VlIsVlWide<T>::value>::type applyEntries(T& val) const {
        for (const auto& entry : m_entries) val = applyEntry(val, entry);
    }

    void readSel(int lbits, WDataInP valp, WDataOutP reswp, int lsb, int width) const {
        VL_SEL_WWII(width, lbits, reswp, valp, lsb, width);
        const int msb = lsb + width - 1;
        auto it = std::lower_bound(m_entries.begin(), m_entries.end(), lsb,
                                   [](const Entry& e, int bit) { return e.m_msb < bit; });
        while (it != m_entries.end() && it->m_lsb <= msb) {
            applyEntry(reswp, *it, std::max(it->m_lsb, lsb), std::min(it->m_msb, msb), lsb);
            ++it;
        }
    }

public:
    VlForceVec() = default;

    template <typename T>
    T read(const T& val) const {
        T result = val;
        applyEntries(result);
        return result;
    }

    IData readSelI(int lbits, WDataInP valp, int lsb, int width) const {
        IData result;
        readSel(lbits, valp, WDataOutP::external(reinterpret_cast<EData*>(&result)), lsb, width);
        result &= VL_MASK_I(width);
        return result;
    }

    QData readSelQ(int lbits, WDataInP valp, int lsb, int width) const {
        QData result;
        readSel(lbits, valp, WDataOutP::external(reinterpret_cast<EData*>(&result)), lsb, width);
        result &= VL_MASK_Q(width);
        return result;
    }

    template <std::size_t N_Words>
    VlWide<N_Words> readSelW(int lbits, WDataInP valp, int lsb, int width) const {
        VlWide<N_Words> result;
        readSel(lbits, valp, result, lsb, width);
        result[N_Words - 1] &= VL_MASK_E(width);
        return result;
    }

    // Preconditions (lsb <= msb, rhsDatap non-null, rhsLsb <= lsb) are checked in V3Force
    // where the call is generated and a source location is available.
    void addForce(int lsb, int msb, const void* rhsDatap, int rhsLsb) {
        auto it = trimEntries(lsb, msb);
        m_entries.insert(it, {lsb, msb, rhsLsb, rhsDatap});
    }

    // Register a force on a slot-tracked variable.  The value lives in the force's own
    // typed shadow variable; entries only record which force owns which slots.
    void addForceAt(int id, int lsb, int msb) {
        auto it = trimEntries(lsb, msb);
        Entry entry{lsb, msb, 0, nullptr};
        entry.m_id = id;
        m_entries.insert(it, entry);
    }

    // Register a force of a bit range within one slot of a slot-tracked variable
    void addForceAt(int id, int slot, int bitLsb, int bitMsb, int elemWidth) {
        const std::size_t at = trimElementBitRange(slot, bitLsb, bitMsb, elemWidth);
        Entry entry{slot, slot, 0, nullptr, bitLsb, bitMsb, elemWidth};
        entry.m_id = id;
        m_entries.insert(m_entries.begin() + at, entry);
    }

    void release(int lsb, int msb) { trimEntries(lsb, msb); }

    void release(int lsb, int msb, int bitLsb, int bitMsb, int elemWidth) {
        trimElementBitRange(lsb, bitLsb, bitMsb, elemWidth);
    }

    // True when force 'id' owns anything in the slot range
    bool ownsAny(int id, int lsb, int msb) const {
        auto it = std::lower_bound(m_entries.begin(), m_entries.end(), lsb,
                                   [](const Entry& e, int bit) { return e.m_msb < bit; });
        for (; it != m_entries.end() && it->m_lsb <= msb; ++it) {
            if (it->m_id == id) return true;
        }
        return false;
    }

    bool ownsSlot(int id, int slot) const { return ownsAny(id, slot, slot); }

    // Blend the bits of 'rhsVal' that force 'id' currently owns at 'slot' into 'cur'.
    // Yields 'cur' unchanged when the force owns nothing there.
    template <typename T>
    typename std::enable_if<!VlIsVlWide<T>::value, T>::type blendOwned(T cur, QData rhsVal, int id,
                                                                       int slot) const {
        using U = VlForceStorageType<T>;
        U result = static_cast<U>(cur);
        auto it = std::lower_bound(m_entries.begin(), m_entries.end(), slot,
                                   [](const Entry& e, int idx) { return e.m_msb < idx; });
        for (; it != m_entries.end() && it->m_lsb <= slot; ++it) {
            if (it->m_id != id) continue;
            if (it->m_elemWidth == 0) return static_cast<T>(rhsVal);  // Owns the whole slot
            const int width = it->m_bitMsb - it->m_bitLsb + 1;
            const U mask = static_cast<U>(static_cast<U>(VL_MASK_Q(width)) << it->m_bitLsb);
            result = static_cast<U>((result & ~mask) | (static_cast<U>(rhsVal) & mask));
        }
        return static_cast<T>(result);
    }

    template <typename T>
    typename std::enable_if<VlIsVlWide<T>::value, T>::type blendOwned(T cur, const T& rhsVal,
                                                                      int id, int slot) const {
        T result = cur;
        auto it = std::lower_bound(m_entries.begin(), m_entries.end(), slot,
                                   [](const Entry& e, int idx) { return e.m_msb < idx; });
        for (; it != m_entries.end() && it->m_lsb <= slot; ++it) {
            if (it->m_id != id) continue;
            if (it->m_elemWidth == 0) return rhsVal;  // Owns the whole slot
            for (int word = VL_BITWORD_E(it->m_bitLsb); word <= VL_BITWORD_E(it->m_bitMsb);
                 ++word) {
                const int wordLsb = word * VL_EDATASIZE;
                const int segLsb = std::max(it->m_bitLsb, wordLsb);
                const int segMsb = std::min(it->m_bitMsb, wordLsb + VL_EDATASIZE - 1);
                const int width = segMsb - segLsb + 1;
                const EData mask = static_cast<EData>(VL_MASK_Q(width)) << (segLsb - wordLsb);
                result[word] = (result[word] & ~mask) | (rhsVal[word] & mask);
            }
        }
        return result;
    }

    void touch() {}
};

#endif  // guard
