// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Generic container types
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2003-2026 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#ifndef VERILATOR_V3CONTAINER_H_
#define VERILATOR_V3CONTAINER_H_

#include "config_build.h"
#include "verilatedos.h"

#include <unordered_map>
#include <unordered_set>
#include <vector>

//============================================================================

// Similar to std::set, but ordered based on call order to emplace.  Used
// when insertion order is desired (e.g. std::vector), but duplicates need removal.
// Keys may not be modified.  (If needed in future, m_set could contain vector positions.)
template <typename T_Key>
class VInsertionSet final {
    std::vector<T_Key> m_keys;  // Elements by insertion order
    std::unordered_set<T_Key> m_keySet;  // Elements by key
public:
    // METHODS
    bool insert(const T_Key& key) {
        // Returns if did insertion (second pair argument of traditional emplace)
        const auto itFoundPair = m_keySet.insert(key);
        if (itFoundPair.second) m_keys.push_back(key);
        return itFoundPair.second;
    }
    void clear() {
        m_keys.clear();
        m_keySet.clear();
    }

    // ACCESSORS
    bool empty() const { return m_keys.empty(); }
    bool exists(const T_Key& key) const { return m_keySet.find(key) != m_keySet.end(); }

    // ITERATORS
    using const_iterator = typename std::vector<T_Key>::const_iterator;
    const_iterator begin() const { return m_keys.begin(); }
    const_iterator end() const { return m_keys.end(); }
};

//============================================================================
// VInsertionMap: Not currently needed; prototype code exists, just ask.
// Similar to std::map, but ordered based on call order to emplace.  Used
// when insertion order is desired (e.g. std::vector), but duplicates need removal.
// Values may be modified.

#endif  // Guard
