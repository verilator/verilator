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
#include <csetjmp>

#include <sys/mman.h>
#endif

namespace VlFiberInternal {

std::uintptr_t alignDown(std::uintptr_t ptr, std::uintptr_t align) { return ptr & ~(align - 1); }

#if defined(FIBER_LINUX_X64)

template <typename T>
Context setup(void (*f)(T*), T* arg) {
    // Get system page size for guard page alignment
    Context ctx;
    const long pageSize = ::sysconf(_SC_PAGESIZE);
    if (VL_UNLIKELY(pageSize <= 0)) {
        VL_FATAL_MT(__FILE__, __LINE__, "", "sysconf(_SC_PAGESIZE) failed");
    }

    // Allocate memory with mmap (anonymous, private mapping)
    ctx.mappingSize = stackSize + 2 * pageSize;
    ctx.mappingp = ::mmap(nullptr, ctx.mappingSize, PROT_READ | PROT_WRITE,
                          MAP_PRIVATE | MAP_ANONYMOUS | MAP_NORESERVE, -1, 0);
    if (VL_UNLIKELY(ctx.mappingp == MAP_FAILED)) {
        VL_FATAL_MT(__FILE__, __LINE__, "",
                    (std::string{"mmap failed: "} + std::strerror(errno)).c_str());
    }

    // Initialize memory layout pointers
    ctx.rsp
        = alignDown(reinterpret_cast<std::uintptr_t>(ctx.mappingp) + stackSize + pageSize - 1, 16);
    ctx.rdi = reinterpret_cast<Register>(arg);
    ctx.rip = reinterpret_cast<Register>(f);

    // Protect guard pages (no read/write access) to catch stack overflow/underflow
    void* const lowGuard = ctx.mappingp;
    void* const highGuard = reinterpret_cast<void*>(alignDown(
        reinterpret_cast<std::uintptr_t>(ctx.mappingp) + stackSize + pageSize, pageSize));

    if (VL_UNLIKELY(::mprotect(lowGuard, pageSize, PROT_NONE) != 0)) {
        VL_FATAL_MT(__FILE__, __LINE__, "", "mprotect failed for low guard page");
    }
    if (VL_UNLIKELY(::mprotect(highGuard, pageSize, PROT_NONE) != 0)) {
        VL_FATAL_MT(__FILE__, __LINE__, "", "mprotect failed for high guard page");
    }
    return ctx;
}

void teardown(Context& ctx) { ::munmap(ctx.mappingp, ctx.mappingSize); }

void start(Context& ctx) {
    if (setjmp(ctx.callerCtx) == 0) {
        asm volatile("mov %[stack], %%rsp\n\t"
                     "xor %%rbp, %%rbp\n\t"
                     "call *%[entry]\n\t"
                     :
                     : [stack] "r"(ctx.rsp), [entry] "r"(ctx.rip), "D"(ctx.rdi)
                     : "memory");
    }
    // Returns here when fiber yields or completes
}

void resume(Context& ctx) {
    // Save caller's state and switch to fiber context
    if (setjmp(ctx.callerCtx) == 0) {
        longjmp(ctx.fiberCtx, 1);  // Jump back to last yield()
    }
    // Returns here when fiber yields or completes
}
void yield(Context& ctx) {
    // Save fiber's state and return to caller
    if (setjmp(ctx.fiberCtx) == 0) {
        longjmp(ctx.callerCtx, 1);  // Jump back to last resume()
    }
    // Returns here when fiber is resumed
}

#endif

};  //namespace VlFiberInternal

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
    m_ctx = VlFiberInternal::setup(&VlFiber::entryPoint, this);
}

VlFiber::~VlFiber() {
    resumeWaiter();
    VlFiberInternal::teardown(m_ctx);
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
        VlFiberInternal::start(m_ctx);
    } else {
        VlFiberInternal::resume(m_ctx);
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
    VlFiberInternal::yield(currentFiberp->m_ctx);

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
    // Resume one last time to finish fiber execution
    VlFiberInternal::yield(fiberp->m_ctx);
    __builtin_unreachable();
}
