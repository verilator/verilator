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
#include <cstring>
#include <string>
#include <utility>

//======================================================================
// Statics

thread_local VlFiber* VlFiber::s_currentFiberp = nullptr;

namespace {

// Align pointer down to 16-byte boundary (required by x86_64 ABI)
// The x86_64 calling convention requires stack pointer to be 16-byte aligned
std::uint8_t* alignDown16(std::uint8_t* ptr) {
    return reinterpret_cast<std::uint8_t*>(reinterpret_cast<std::uintptr_t>(ptr)
                                           & ~std::uintptr_t(0xF));
}

}  // namespace

//======================================================================
// Construction helpers

std::unique_ptr<VlFiber> VlFiber::create(Fn fn, std::size_t stackSize) {
    return std::unique_ptr<VlFiber>(new VlFiber{std::move(fn), stackSize});
}

VlFiber::VlFiber(Fn fn, std::size_t stackSize)
    : m_fn{std::move(fn)} {
    // Get system page size for guard page alignment
    const long page = ::sysconf(_SC_PAGESIZE);
    if (VL_UNLIKELY(page <= 0)) {
        VL_FATAL_MT(__FILE__, __LINE__, "", "sysconf(_SC_PAGESIZE) failed");
    }
    const std::size_t guardSize = static_cast<std::size_t>(page);

    // Calculate total allocation size: stack + two guard pages
    m_stackSize = stackSize;
    m_mappingSize = stackSize + 2 * guardSize;

    // Allocate memory with mmap (anonymous, private mapping)
    void* const mappingp = ::mmap(nullptr, m_mappingSize, PROT_READ | PROT_WRITE,
                                  MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
    if (VL_UNLIKELY(mappingp == MAP_FAILED)) {
        VL_FATAL_MT(__FILE__, __LINE__, "",
                    (std::string{"mmap failed: "} + std::strerror(errno)).c_str());
    }

    // Initialize memory layout pointers early
    m_mappingp = mappingp;
    m_stackBasep = static_cast<std::uint8_t*>(mappingp) + guardSize;

    // Protect guard pages (no read/write access) to catch stack overflow/underflow
    uint8_t* const lowGuard = static_cast<uint8_t*>(mappingp);
    uint8_t* const highGuard = m_stackBasep + stackSize;

    if (VL_UNLIKELY(::mprotect(lowGuard, guardSize, PROT_NONE) != 0)) {
        VL_FATAL_MT(__FILE__, __LINE__, "", "mprotect failed for low guard page");
    }
    if (VL_UNLIKELY(::mprotect(highGuard, guardSize, PROT_NONE) != 0)) {
        VL_FATAL_MT(__FILE__, __LINE__, "", "mprotect failed for high guard page");
    }
}

VlFiber::~VlFiber() {
    resumeWaiters();
    if (m_mappingp) { ::munmap(m_mappingp, m_mappingSize); }
}

//======================================================================
// Scheduling helpers

void VlFiber::resume() {
    if (m_done) {
        // Quick exit if fiber already finished
        resumeWaiters();
        return;
    }

    // Save the current fiber context
    VlFiber* const previousFiberp = s_currentFiberp;
    s_currentFiberp = this;  // We are now the current fiber

    // Save caller's state and switch to fiber context
    if (setjmp(m_callerCtx) == 0) {
        if (!m_started) {
            m_started = true;
            start(this);  // First time through: bootstrap the fiber
        } else {
            longjmp(m_fiberCtx, 1);  // Resume: jump to saved fiber state
        }
    }

    // Returns here when fiber yields or completes

    // Restore previous context
    s_currentFiberp = previousFiberp;
    if (m_done) resumeWaiters();
}

void VlFiber::yield() {
    VlFiber* const currentFiberp = s_currentFiberp;
    if (!currentFiberp) return;  // Not in fiber, nothing to yield

    // Save fiber's state and return to caller
    if (setjmp(currentFiberp->m_fiberCtx) == 0) {
        s_currentFiberp = nullptr;  // No longer in fiber
        longjmp(currentFiberp->m_callerCtx, 1);  // Jump back to resume()
    }

    // Returns here when fiber is resumed
    s_currentFiberp = currentFiberp;  // Restore current fiber
}

void VlFiber::resumeWaiters() {
    if (m_waiters.empty()) return;
    auto waiters = std::move(m_waiters);
    m_waiters.clear();
    for (auto handle : waiters) {
        if (handle) handle.resume();
    }
}

void VlFiber::addWaiter(std::coroutine_handle<> waiter) {
    if (!waiter) return;
    m_waiters.push_back(waiter);
}

//======================================================================
// Bootstrap helpers

void VlFiber::start(VlFiber* fiberp) {
    // Calculate stack top: align down to 16-byte boundary (x86_64 ABI requirement)
    // Stack grows downward, so we start from the end of usable stack space
    // Subtract 8 bytes for alignment to be in mapping range
    std::uint8_t* const stackTop = alignDown16(fiberp->m_stackBasep + fiberp->m_stackSize - 8u);

#if defined(__x86_64__)
    // Switch to fiber stack and call entry point
    // - Set %rsp to stack top (new stack pointer)
    // - Clear %rbp (mark as base of call stack for debuggers)
    // - Call entryPoint with fiberp in %rdi (first arg in x86_64 calling convention)
    asm volatile("mov %[stack], %%rsp\n\t"
                 "xor %%rbp, %%rbp\n\t"
                 "call *%[entry]\n\t"
                 :
                 : [stack] "r"(stackTop), [entry] "r"(&VlFiber::entryPoint), "D"(fiberp)
                 : "memory");
#else
#error "VlFiber currently supports only x86_64"
#endif
    __builtin_unreachable();
}

void VlFiber::entryPoint(VlFiber* fiberp) {
    s_currentFiberp = fiberp;
    fiberp->m_fn();
    fiberp->m_done = true;
    s_currentFiberp = nullptr;
    longjmp(fiberp->m_callerCtx, 1);
}
