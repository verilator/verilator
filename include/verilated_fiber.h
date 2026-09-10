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
/// \brief Lightweight fiber abstraction for DPI stack switching
///
/// This file is included automatically by Verilator in some of the C++ files
/// to support DPI exported tasks with timing constructs.
///
/// This file is not part of the Verilated public-facing API.
/// It is only for internal use.
///
/// See the internals documentation docs/internals.rst for details.
///
//*************************************************************************

#ifndef VERILATOR_VERILATED_FIBER_H_
#define VERILATOR_VERILATED_FIBER_H_

#include "verilatedos.h"

#include "verilated_coroutine.h"

#include <cstddef>
#include <functional>
#include <memory>
#include <vector>

#if defined(__unix__) && __has_include(<ucontext.h>)
#define VERILATOR_FIBER_UNIX
#else
#error "This platform does not support suspendable exported tasks"
#endif

#if defined(VERILATOR_FIBER_UNIX)
#include <ucontext.h>

#include <sys/mman.h>

// Forward declaration for VlFiberContext
class VlFiber;

//=============================================================================
// VlFiberMemoryChunk holds a contiguous area of memory from which fiber stacks are allocated.

struct VlFiberMemoryChunk final {
    // MEMBERS
    void* m_chunkAddr;
    void* m_top;
    void* m_freeTop;
    size_t m_free;  // Indicates how many stacks are left
    bool m_retention : 1;  // Flag indicating that the chunk reached some fullness level

    // CONSTRUCTORS
    VlFiberMemoryChunk();
    ~VlFiberMemoryChunk();
};

//=============================================================================
// VlFiberMemoryPool manages reusable fiber stack allocations.

class VlFiberMemoryPool final {
    // MEMBERS
    std::vector<std::unique_ptr<VlFiberMemoryChunk>> m_chunks;

public:
    // CONSTRUCTORS
    VlFiberMemoryPool();
    VlFiberMemoryPool(const VlFiberMemoryPool& other) = delete;
    VlFiberMemoryPool(VlFiberMemoryPool&& other) = delete;
    ~VlFiberMemoryPool();

    // METHODS
    void* get();
    void free(void* ptr);
};

//=============================================================================
// VlFiberContext stores the platform-specific execution context for a fiber.

class VlFiberContext final {
    // MEMBERS
    ucontext_t callerCtx{};  // State of caller context
    ucontext_t fiberCtx{};  // State of fiber context
    void* mappingp{};  // Base address of allocated stack
    std::size_t mappingSize{};  // Total size of allocated stack

public:
    // CONSTRUCTORS
    VlFiberContext(void (*f)(VlFiber*), VlFiber* arg);
    VlFiberContext() = default;
    ~VlFiberContext();

    // METHODS
    void yield();
    void resume();
    void start();
    void end() VL_ATTR_NORETURN;
};

#endif

//=============================================================================
// VlFiber is a lightweight userspace thread used to run DPI code on an alternate stack.

class VlFiber final {
public:
    // TYPES
    // Function executed when the fiber starts running
    using Fn = std::function<void()>;

    // CONSTRUCTORS
    VlFiber(const VlFiber&) = delete;
    VlFiber& operator=(const VlFiber&) = delete;

    // Destructor releases mapped memory and resumes waiters if necessary
    ~VlFiber();

    // METHODS
    // Factory helper returning a unique_ptr so callers cannot forget to destroy
    static std::unique_ptr<VlFiber> create(Fn fn);

    // Resume execution of the fiber
    void resume();

    // Suspend execution of the currently running fiber and switch to caller
    static void yield();

    // Returns true once the fiber finished executing its function
    bool isDone() const noexcept { return m_done; }

    // Return fiber currently executing on this thread (nullptr if outside fiber)
    static VlFiber* current() noexcept { return t_currentFiberp; }

    // Register a coroutine to be resumed once the fiber completes
    void setWaiter(std::coroutine_handle<> waiter);

private:
    // MEMBERS
    VlFiberContext m_ctx;  // Platform-dependent internal fiber context
    Fn m_fn;  // Function executed by the fiber
    bool m_started = false;  // Indicates whether start() already ran
    bool m_done = false;  // Set once m_fn returns
    std::coroutine_handle<void> m_waiter;  // Coroutine resumed on completion

    static thread_local VlFiber* t_currentFiberp;  // Fiber currently executing on the thread

    // CONSTRUCTORS
    VlFiber(Fn fn);

    // METHODS
    // Actual function executing the user callable and performing cleanup
    static void entryPoint(VlFiber* fiberp) VL_ATTR_NORETURN;

    // Resume waiter when the fiber completes
    void resumeWaiter();
};

#endif  // Guard
