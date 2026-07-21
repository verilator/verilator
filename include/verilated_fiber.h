// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
//
// Code available from: https://verilator.org
//
// Copyright 2003-2025 by Wilson Snyder. This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-FileCopyrightText: 2026-2026 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************
///
/// \file
/// \brief Lightweight fiber abstraction for DPI stack switching
///
/// This file is included automatically by Verilator in C++ files that need
/// to suspend DPI code independently of the host stack.
///
//*************************************************************************

#ifndef VERILATOR_VERILATED_FIBER_H_
#define VERILATOR_VERILATED_FIBER_H_

#include "verilatedos.h"

#include <algorithm>
#include <coroutine>
#include <cstddef>
#include <cstdint>
#include <functional>
#include <memory>
#include <vector>

#if defined(__linux__)
#define VERILATOR_FIBER_LINUX
#else
#error "This platform is not supported"
#endif

#if defined(VERILATOR_FIBER_LINUX)
#include <cstddef>
#include <ucontext.h>

#include <sys/mman.h>
#endif

class VlFiber;

#if defined(VERILATOR_FIBER_LINUX)

struct VlFiberMemoryChunk final {
    void* m_chunkAddr;
    void* m_top;
    void* m_freeTop;
    size_t m_free;

    VlFiberMemoryChunk();
    ~VlFiberMemoryChunk();
};

class VlFiberMemoryPool final {
    std::vector<VlFiberMemoryChunk*> m_chunks;

public:
    VlFiberMemoryPool();
    VlFiberMemoryPool(const VlFiberMemoryPool& other) = delete;
    VlFiberMemoryPool(VlFiberMemoryPool&& other) = delete;
    void* get();
    void free(void* ptr);
};

class VlFiberContext final {
    ucontext_t callerCtx{};  // Register state of caller context
    ucontext_t fiberCtx{};  // Register state of fiber context
    void* mappingp;  // Base of mmap allocation (includes guards)
    std::size_t mappingSize;  // Total size of allocation (stackSize + 2*pageSize)

public:
    // Set maximum stack size to 16MB
    static constexpr std::size_t stackSize = 16 * (1 << 20);

    VlFiberContext(void (*f)(VlFiber*), VlFiber* arg);
    VlFiberContext() {};
    void teardown();
    void yield();
    void resume();
    void start();
    void end() VL_ATTR_NORETURN;
};

#endif

// Simple userspace fiber used to run DPI code on an alternate stack.
class VlFiber final {
public:
    // Function executed when the fiber starts running
    using Fn = std::function<void()>;

    // Factory helper returning a unique_ptr so callers cannot forget to destroy
    static std::unique_ptr<VlFiber> create(Fn fn);

    // Resume execution of the fiber
    void resume();

    // Suspend execution of the currently running fiber and switch to caller
    static void yield();

    // Returns true once the fiber finished executing its function
    bool isDone() const noexcept { return m_done; }

    // Return fiber currently executing on this thread (nullptr if outside fiber)
    static VlFiber* current() noexcept { return s_currentFiberp; }

    // Register a coroutine to be resumed once the fiber completes
    void setWaiter(std::coroutine_handle<> waiter);

    // Destructor releases mapped memory and resumes waiters if necessary
    ~VlFiber();

    VlFiber(const VlFiber&) = delete;
    VlFiber& operator=(const VlFiber&) = delete;

private:
    VlFiberContext m_ctx;  // Platform-dependent internal fiber context
    Fn m_fn;  // Function executed by the fiber
    bool m_started = false;  // Indicates whether start() already ran
    bool m_done = false;  // Set once m_fn returns
    std::coroutine_handle<void> m_waiter{};  // Coroutine resumed on completion

    static thread_local VlFiber* s_currentFiberp;  // Fiber currently executing on the thread

    VlFiber(Fn fn);

    // Actual function executing the user callable and performing cleanup
    static void entryPoint(VlFiber* fiberp) VL_ATTR_NORETURN;

    // Resume waiter when the fiber completes
    void resumeWaiter();
};

#endif  // Guard
