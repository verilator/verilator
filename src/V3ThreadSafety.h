// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Definitions for thread safety checking
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2003-2024 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#ifndef VERILATOR_V3THREADSAFETY_H_
#define VERILATOR_V3THREADSAFETY_H_

#include <verilatedos.h>

#include <V3Mutex.h>

// A class that works as an indicator of MT_DISABLED context.
// It uses Clang's thread safety analysis (-fthread-safety) to do its work.
// Its use will most likely be optimized out (or at least reduced to a few insignificant symbols
// or instructions) during compilation.
class VL_CAPABILITY("lock") V3MtDisabledLock final {
    friend class V3MtDisabledLockInstanceAccessor;

    static V3MtDisabledLock s_mtDisabledLock;

    constexpr V3MtDisabledLock() = default;
    ~V3MtDisabledLock() = default;
    VL_UNCOPYABLE(V3MtDisabledLock);
    VL_UNMOVABLE(V3MtDisabledLock);

public:
    // lock() will disable multithreading while in MT Disabled regions
    void lock() VL_ACQUIRE() VL_MT_SAFE;
    // unlock() will reenable multithreading while in MT Disabled regions
    void unlock() VL_RELEASE() VL_MT_SAFE;

    static constexpr V3MtDisabledLock& instance()
        VL_RETURN_CAPABILITY(V3MtDisabledLock::s_mtDisabledLock) {
        return s_mtDisabledLock;
    }
};

// A class providing mutable access to V3MtDisabledLock::s_mtDisabledLock.
// This is a class because VL_RETURN_CAPABILITY works only on methods, not free functions.
// This is not a method in V3MtDisabledLock itself as a method declaration inside #ifdef block
// woudl break ODR.
class V3MtDisabledLockInstanceAccessor final {
public:
    constexpr V3MtDisabledLock& operator()() const
        VL_RETURN_CAPABILITY(V3MtDisabledLock::s_mtDisabledLock) {
        return V3MtDisabledLock::s_mtDisabledLock;
    }
};
// Create a global object which can be called like a function.
static constexpr V3MtDisabledLockInstanceAccessor v3MtDisabledLock VL_ATTR_UNUSED;

using V3MtDisabledLockGuard = V3LockGuardImp<V3MtDisabledLock>;

// Annotated function can be called only in MT_DISABLED context, i.e. either in a code unit
// compiled with VL_MT_DISABLED_CODE_UNIT preprocessor definition, or after obtaining a lock on
// v3MtDisabledLock().
#define VL_MT_DISABLED \
    VL_CLANG_ATTR(annotate("MT_DISABLED")) \
    VL_REQUIRES(V3MtDisabledLock::instance())

#endif  // guard
