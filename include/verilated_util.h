// -*- mode: C++; c-file-style: "cc-mode" -*-
//=============================================================================
//
// Code available from: https://verilator.org
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2026-2026 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//=============================================================================
///
/// \file
/// \brief Verilated utility functions
///
//=============================================================================

#ifndef VERILATOR_VERILATED_UTIL_H_
#define VERILATOR_VERILATED_UTIL_H_

//=============================================================================
// Restorer
//
// This is the same definition as in V3Global.h, but made available
// for verilated_* files.
//
//=============================================================================

#define VL_RESTORER(var) \
    const VRestorerTrivial<typename std::decay_t<decltype(var)>> restorer_##var(var);

// Implementation of VL_RESTORER
template <typename T>
class VRestorerTrivial final {
    static_assert(std::is_trivially_copyable<T>::value,
                  "Use VL_RESTORER_{COPY,CLEAR} for non trivially copyable types");
    T& m_ref;  // Reference to object we're saving and restoring
    const T m_saved;  // Value saved, for later restore

public:
    explicit VRestorerTrivial(T& val)
        : m_ref{val}
        , m_saved{val} {}
    ~VRestorerTrivial() { m_ref = m_saved; }
    VL_UNCOPYABLE(VRestorerTrivial);
    // Must be stack allocated
    void* operator new(size_t) = delete;
    void operator delete(void*) = delete;

    const T& saved() const { return m_saved; }
};

#endif
