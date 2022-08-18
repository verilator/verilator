// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: List class with storage in existing classes
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2022 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#ifndef VERILATOR_V3LIST_H_
#define VERILATOR_V3LIST_H_

#include "config_build.h"
#include "verilatedos.h"

#include <vector>

//============================================================================

template <class T>
class V3List;
template <class T>
class V3ListEnt;

template <class T>
class V3List final {
    // List container for linked list of elements of type *T  (T is a pointer type)
private:
    // MEMBERS
    T m_headp = nullptr;  // First element
    T m_tailp = nullptr;  // Last element
    friend class V3ListEnt<T>;

public:
    V3List() = default;
    ~V3List() = default;
    // METHODS
    T begin() const { return m_headp; }
    T end() const { return nullptr; }
    bool empty() const { return m_headp == nullptr; }
    void reset() {  // clear() without walking the list
        m_headp = nullptr;
        m_tailp = nullptr;
    }
};

//============================================================================

template <class T>
class V3ListEnt final {
    // List entry for linked list of elements of type *T  (T is a pointer type)
private:
    // MEMBERS
    T m_nextp = nullptr;  // Pointer to next element, nullptr=end
    T m_prevp = nullptr;  // Pointer to previous element, nullptr=beginning
    friend class V3List<T>;
    static V3ListEnt* baseToListEnt(void* newbasep, size_t offset) {
        // "this" must be a element inside of *basep
        // Use that to determine a structure offset, then apply to the new base
        // to get our new pointer information
        return (V3ListEnt*)(((uint8_t*)newbasep) + offset);
    }

public:
    V3ListEnt() = default;
    ~V3ListEnt() {
#ifdef VL_DEBUG
        // Load bogus pointers so we can catch deletion bugs
        m_nextp = reinterpret_cast<T>(1);
        m_prevp = reinterpret_cast<T>(1);
#endif
    }
    T nextp() const { return m_nextp; }
    // METHODS
    void pushBack(V3List<T>& listr, T newp) {
        // "this" must be a element inside of *newp
        // cppcheck-suppress thisSubtraction
        const size_t offset = (size_t)(uint8_t*)(this) - (size_t)(uint8_t*)(newp);
        m_nextp = nullptr;
        if (!listr.m_headp) listr.m_headp = newp;
        m_prevp = listr.m_tailp;
        if (m_prevp) baseToListEnt(m_prevp, offset)->m_nextp = newp;
        listr.m_tailp = newp;
    }
    void pushFront(V3List<T>& listr, T newp) {
        // "this" must be a element inside of *newp
        // cppcheck-suppress thisSubtraction
        const size_t offset = (size_t)(uint8_t*)(this) - (size_t)(uint8_t*)(newp);
        m_nextp = listr.m_headp;
        if (m_nextp) baseToListEnt(m_nextp, offset)->m_prevp = newp;
        listr.m_headp = newp;
        m_prevp = nullptr;
        if (!listr.m_tailp) listr.m_tailp = newp;
    }
    // Unlink from side
    void unlink(V3List<T>& listr, T oldp) {
        // "this" must be a element inside of *oldp
        // cppcheck-suppress thisSubtraction
        const size_t offset = (size_t)(uint8_t*)(this) - (size_t)(uint8_t*)(oldp);
        if (m_nextp) {
            baseToListEnt(m_nextp, offset)->m_prevp = m_prevp;
        } else {
            listr.m_tailp = m_prevp;
        }
        if (m_prevp) {
            baseToListEnt(m_prevp, offset)->m_nextp = m_nextp;
        } else {
            listr.m_headp = m_nextp;
        }
        m_prevp = m_nextp = nullptr;
    }
};

//============================================================================

#endif  // Guard
