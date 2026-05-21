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

#include "internal/fibers.h"

#include <coroutine>
#include <csetjmp>
#include <cstddef>
#include <cstdint>
#include <functional>
#include <memory>
#include <vector>

// Simple userspace fiber used to run DPI code on an alternate stack.
class VlFiber final {
public:
    // Function executed when the fiber starts running
    using Fn = std::function<void()>;

    // Default stack size used when none is provided (in bytes)
    static constexpr std::size_t defaultStackSize() noexcept { return 512 * 1024; }

    // Factory helper returning a unique_ptr so callers cannot forget to destroy
    static std::unique_ptr<VlFiber> create(Fn fn, std::size_t stackSize = defaultStackSize());

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
    std::jmp_buf m_callerCtx{};  // Register state of caller context
    std::jmp_buf m_fiberCtx{};  // Register state of fiber context
    void* m_mappingp = nullptr;  // Base of mmap allocation (includes guards)
    std::size_t m_mappingSize = 0;  // Total size of allocation (stack + 2*guard)
    uint8_t* m_stackBasep = nullptr;  // Start of usable stack (after low guard)
    std::size_t m_stackSize = 0;  // Size of usable stack (excludes guards)
    Fn m_fn;  // Function executed by the fiber
    bool m_started = false;  // Indicates whether start() already ran
    bool m_done = false;  // Set once m_fn returns
    std::coroutine_handle<void> m_waiter;  // Coroutine resumed on completion

    static thread_local VlFiber* s_currentFiberp;  // Fiber currently executing on the thread

    VlFiber(Fn fn, std::size_t stackSize);

    // Bootstrap entry that jumps to entryPoint on the fiber stack
    static void start(VlFiber* fiberp) VL_ATTR_NORETURN;

    // Actual function executing the user callable and performing cleanup
    static void entryPoint(VlFiber* fiberp) VL_ATTR_NORETURN;

    // Resume waiter when the fiber completes
    void resumeWaiter();
};

#endif  // Guard
