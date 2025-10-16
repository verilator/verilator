// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
//
// Code available from: https://verilator.org
//
// Copyright 2003-2025 by Wilson Snyder. This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
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

inline std::uint8_t* alignDown16(std::uint8_t* ptr) {
    return reinterpret_cast<std::uint8_t*>(reinterpret_cast<std::uintptr_t>(ptr)
                                           & ~std::uintptr_t(0xF));
}

}  // namespace

//======================================================================
// Construction helpers

std::unique_ptr<VlFiber> VlFiber::create(Fn fn, std::size_t stackSize) {
    return std::unique_ptr<VlFiber>(new VlFiber(std::move(fn), stackSize));
}

VlFiber::VlFiber(Fn fn, std::size_t stackSize)
    : m_fn{std::move(fn)} {
    const long page = ::sysconf(_SC_PAGESIZE);
    if (VL_UNLIKELY(page <= 0)) {
        VL_FATAL_MT(__FILE__, __LINE__, "", "sysconf(_SC_PAGESIZE) failed");
    }

    const std::size_t guard = static_cast<std::size_t>(page);
    m_mappingSize = stackSize + 2 * guard;

    void* const mappingp = ::mmap(nullptr, m_mappingSize, PROT_READ | PROT_WRITE,
                                   MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
    if (VL_UNLIKELY(mappingp == MAP_FAILED)) {
        VL_FATAL_MT(__FILE__, __LINE__, "",
                    (std::string{"mmap failed: "} + std::strerror(errno)).c_str());
    }
    if (VL_UNLIKELY(::mprotect(mappingp, guard, PROT_NONE) != 0)) {
        VL_FATAL_MT(__FILE__, __LINE__, "", "mprotect failed for guard page (low)");
    }
    if (VL_UNLIKELY(::mprotect(static_cast<std::uint8_t*>(mappingp) + guard + stackSize, guard,
                               PROT_NONE)
                    != 0)) {
        VL_FATAL_MT(__FILE__, __LINE__, "", "mprotect failed for guard page (high)");
    }

    m_mappingp = mappingp;
    m_stackBasep = static_cast<std::uint8_t*>(mappingp) + guard;
    m_stackSize = stackSize;
}

VlFiber::~VlFiber() {
    resumeWaiters();
    if (m_mappingp) {
        ::munmap(m_mappingp, m_mappingSize);
    }
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
    s_currentFiberp = this; // We are now the current fiber

    // Save caller's state and switch to fiber context
    if (setjmp(m_callerCtx) == 0) {
        if (!m_started) {
            m_started = true;
            start(this); // First time through: bootstrap the fiber
        } else {
            longjmp(m_fiberCtx, 1); // Resume: jump to saved fiber state
        }
    }
    
    // Returns here when fiber yields or completes

    // Restore previous context
    s_currentFiberp = previousFiberp;
    if (m_done) resumeWaiters();
}

void VlFiber::yield() {
    VlFiber* const currentFiberp = s_currentFiberp;
    if (!currentFiberp) return; // Not in fiber, nothing to yield

    // Save fiber's state and return to caller
    if (setjmp(currentFiberp->m_fiberCtx) == 0) {
        s_currentFiberp = nullptr; // No longer in fiber
        longjmp(currentFiberp->m_callerCtx, 1); // Jump back to resume()
    }

    // Returns here when fiber is resumed
    s_currentFiberp = currentFiberp; // Restore current fiber
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
    std::uint8_t* const top
        = alignDown16(fiberp->m_stackBasep + fiberp->m_stackSize - 8u) + 8u;
#if defined(__x86_64__)
    asm volatile(
        "mov %[stack], %%rsp\n\t"
        "xor %%rbp, %%rbp\n\t"
        "call *%[entry]\n\t"
        :
        : [stack] "r"(top), [entry] "r"(&VlFiber::entryPoint), "D"(fiberp)
        : "memory");
#else
# error "VlFiber currently supports only x86_64"
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
