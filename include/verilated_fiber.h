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

#include <cstddef>
#include <functional>
#include <memory>
#include <vector>

#if defined(__linux__)
#define VERILATOR_FIBER_LINUX
#else
#error "This platform is not supported"
#endif

// clang-format off
// Some preprocessor magic to support both Clang and GCC coroutines with both libc++ and libstdc++
#ifdef _LIBCPP_VERSION  // libc++
# if defined(__has_include) && !__has_include(<coroutine>) && __has_include(<experimental/coroutine>)
#  if __clang_major__ > 13  // Clang > 13 warns that coroutine types in std::experimental are deprecated
#   pragma clang diagnostic push
#   pragma clang diagnostic ignored "-Wdeprecated-experimental-coroutine"
#  endif
#  include <experimental/coroutine>
   namespace std {
       using namespace experimental;  // Bring std::experimental into the std namespace
   }
# else
#  include <coroutine>
# endif
#else
# if defined __clang__ && defined __GLIBCXX__ && !defined __cpp_impl_coroutine
#  define __cpp_impl_coroutine 1  // Clang doesn't define this, but it's needed for libstdc++
# endif
# include <coroutine>
# if __clang_major__ < 14
   namespace std {  // Bring coroutine library into std::experimental, as Clang < 14 expects it to be there
       namespace experimental {
           using namespace std;
       }
   }
# endif
#endif
// clang-format on

#if defined(VERILATOR_FIBER_LINUX)
#include <ucontext.h>

#include <sys/mman.h>
#endif

#if defined(VERILATOR_FIBER_LINUX)
// Forward declaration for VlFiberContext
class VlFiber;

//=============================================================================
// VlFiberMemoryChunk holds a contiguous area of memory from which fiber stacks are allocated.

struct VlFiberMemoryChunk final {
    // MEMBERS
    void* m_chunkAddr;
    void* m_top;
    void* m_freeTop;
    size_t m_free;

    // CONSTRUCTORS
    VlFiberMemoryChunk();
    ~VlFiberMemoryChunk();
};

//=============================================================================
// VlFiberMemoryPool manages reusable fiber stack allocations.

class VlFiberMemoryPool final {
    // MEMBERS
    std::vector<VlFiberMemoryChunk*> m_chunks;

public:
    // CONSTRUCTORS
    VlFiberMemoryPool();
    VlFiberMemoryPool(const VlFiberMemoryPool& other) = delete;
    VlFiberMemoryPool(VlFiberMemoryPool&& other) = delete;

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
    static VlFiber* current() noexcept { return s_currentFiberp; }

    // Register a coroutine to be resumed once the fiber completes
    void setWaiter(std::coroutine_handle<> waiter);

private:
    // MEMBERS
    VlFiberContext m_ctx;  // Platform-dependent internal fiber context
    Fn m_fn;  // Function executed by the fiber
    bool m_started = false;  // Indicates whether start() already ran
    bool m_done = false;  // Set once m_fn returns
    std::coroutine_handle<void> m_waiter;  // Coroutine resumed on completion

    static thread_local VlFiber* s_currentFiberp;  // Fiber currently executing on the thread

    // CONSTRUCTORS
    VlFiber(Fn fn);

    // METHODS
    // Actual function executing the user callable and performing cleanup
    static void entryPoint(VlFiber* fiberp) VL_ATTR_NORETURN;

    // Resume waiter when the fiber completes
    void resumeWaiter();
};

#endif  // Guard
