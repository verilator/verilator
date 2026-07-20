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
//=========================================================================
///
/// \file
/// \brief Implementation of lightweight fibers used for DPI stack switching
///
//*************************************************************************

#include "verilatedos.h"

#include "verilated_fiber.h"

#include "verilated.h"

#include <cerrno>
#include <cstddef>
#include <cstdint>
#include <cstring>
#include <functional>
#include <memory>
#include <string>
#include <utility>

//======================================================================
// Platform-dependent internal implementation

#if defined(FIBER_LINUX_X64)
#include <ucontext.h>

#include <sys/mman.h>
#endif

#if defined(FIBER_LINUX_X64)

static long pageSize = sysconf(_SC_PAGESIZE);

VlFiberContext::VlFiberContext(void (*f)(VlFiber*), VlFiber* arg) {
    if (VL_UNLIKELY(pageSize <= 0)) {
        VL_FATAL_MT(__FILE__, __LINE__, "", "sysconf(_SC_PAGESIZE) failed");
    }

    // Allocate memory with mmap (anonymous, private mapping)
    mappingSize = stackSize + 2 * pageSize;
    mappingp = ::mmap(nullptr, mappingSize, PROT_READ | PROT_WRITE,
                      MAP_PRIVATE | MAP_ANONYMOUS | MAP_NORESERVE, -1, 0);
    if (VL_UNLIKELY(mappingp == MAP_FAILED)) {
        VL_FATAL_MT(__FILE__, __LINE__, "",
                    (std::string{"mmap failed: "} + std::strerror(errno)).c_str());
    }

    // Initialize memory layout pointers
    if (VL_UNLIKELY(getcontext(&fiberCtx) == -1)) {
        VL_FATAL_MT(__FILE__, __LINE__, "",
                    (std::string{"getcontext failed: "} + std::strerror(errno)).c_str());
    }
    fiberCtx.uc_stack.ss_sp = mappingp;
    fiberCtx.uc_stack.ss_size = mappingSize;
    makecontext(&fiberCtx, reinterpret_cast<void (*)()>(f), 1, arg);
}

void VlFiberContext::teardown() {
    if (mappingp) ::munmap(mappingp, mappingSize);
}

void VlFiberContext::yield() {
    // Save fiber's state and return to caller
    //if (setjmp(this->fiberCtx) == 0) {
    //    longjmp(this->callerCtx, 1);  // Jump back to last resume()
    //}
    if (VL_UNLIKELY(swapcontext(&fiberCtx, &callerCtx) == -1)) {
        VL_FATAL_MT(__FILE__, __LINE__, "",
                    (std::string{"swapcontext failed: "} + std::strerror(errno)).c_str());
    }
    // Returns here when fiber is resumed
}

void VlFiberContext::resume() {
    // Save caller's state and switch to fiber context
    //if (setjmp(this->callerCtx) == 0) {
    //    longjmp(this->fiberCtx, 1);  // Jump back to last yield()
    //}
    if (VL_UNLIKELY(swapcontext(&callerCtx, &fiberCtx) == -1)) {
        VL_FATAL_MT(__FILE__, __LINE__, "",
                    (std::string{"swapcontext failed: "} + std::strerror(errno)).c_str());
    }
    // Returns here when fiber yields or completes
}

void VlFiberContext::start() {
    if (VL_UNLIKELY(swapcontext(&callerCtx, &fiberCtx) == -1)) {
        VL_FATAL_MT(__FILE__, __LINE__, "",
                    (std::string{"swapcontext failed: "} + std::strerror(errno)).c_str());
    }
    // Returns here when fiber yields or completes
}

void VlFiberContext::end() {
    if (VL_UNLIKELY(setcontext(&callerCtx) == -1)) {
        VL_FATAL_MT(__FILE__, __LINE__, "",
                    (std::string{"setcontext failed: "} + std::strerror(errno)).c_str());
    }
    __builtin_unreachable();
}

#endif

//======================================================================
// Statics

thread_local VlFiber* VlFiber::s_currentFiberp = nullptr;

//======================================================================
// Construction helpers

std::unique_ptr<VlFiber> VlFiber::create(Fn fn) {
    return std::unique_ptr<VlFiber>(new VlFiber{std::move(fn)});
}

VlFiber::VlFiber(Fn fn)
    : m_fn{std::move(fn)} {
    m_ctx = VlFiberContext{&VlFiber::entryPoint, this};
}

VlFiber::~VlFiber() {
    resumeWaiter();
    m_ctx.teardown();
}

//======================================================================
// Scheduling helpers

void VlFiber::resume() {
    if (m_done) {
        // Quick exit if fiber already finished
        resumeWaiter();
        return;
    }

    // Save the current fiber context
    VlFiber* const previousFiberp = s_currentFiberp;
    s_currentFiberp = this;  // We are now the current fiber

    if (!m_started) {
        m_started = true;
        m_ctx.start();
    } else {
        m_ctx.resume();
    }

    // Returns here when fiber yields or completes

    // Restore previous context
    s_currentFiberp = previousFiberp;
    if (m_done) resumeWaiter();
}

void VlFiber::yield() {
    VlFiber* const currentFiberp = s_currentFiberp;
    if (!currentFiberp) return;  // Not in fiber, nothing to yield

    // Save fiber's state and return to caller
    s_currentFiberp = nullptr;
    currentFiberp->m_ctx.yield();

    // Returns here when fiber is resumed
    s_currentFiberp = currentFiberp;  // Restore current fiber
}

void VlFiber::resumeWaiter() {
    if (!m_waiter) return;
    auto waiter = std::move(m_waiter);
    m_waiter = {};
    if (waiter) waiter.resume();
}

void VlFiber::setWaiter(std::coroutine_handle<> waiter) {
    if (!waiter) return;
    m_waiter = waiter;
}

//======================================================================
// Bootstrap

void VlFiber::entryPoint(VlFiber* fiberp) {
    s_currentFiberp = fiberp;
    fiberp->m_fn();
    fiberp->m_done = true;
    s_currentFiberp = nullptr;
    fiberp->m_ctx.end();
    __builtin_unreachable();
}
