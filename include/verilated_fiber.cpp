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

#include <algorithm>
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

#if defined(VERILATOR_FIBER_LINUX)
#include <ucontext.h>

#include <sys/mman.h>
#endif

#if defined(VERILATOR_FIBER_LINUX)

static thread_local VlFiberMemoryPool memoryPool{};

//======================================================================
// VlFiberMemoryPool

// One stack allocation is 1 Mb
static VL_CONSTEXPR_CXX17 unsigned long long allocationSize = 1<<20;

// Allocate space for 16 stacks at once
static VL_CONSTEXPR_CXX17 unsigned long long allocationCount = 16;
static VL_CONSTEXPR_CXX17 unsigned long long chunkSize = allocationSize * allocationCount;

VlFiberMemoryChunk::VlFiberMemoryChunk()
    : m_chunkAddr{}
    , m_top{}
    , m_freeTop{}
    , m_free{0} {
    // Use MAP_NORESERVE to prevent eager page allocation
    m_chunkAddr = ::mmap(nullptr, chunkSize, PROT_READ | PROT_WRITE,
                         MAP_PRIVATE | MAP_ANONYMOUS | MAP_NORESERVE, -1, 0);
    if (VL_UNLIKELY(m_chunkAddr == MAP_FAILED)) {
        VL_FATAL_MT(__FILE__, __LINE__, "",
                    (std::string{"mmap failed: "} + std::strerror(errno)).c_str());
    }
    m_top = m_chunkAddr;
    m_free = allocationCount;
}

VlFiberMemoryChunk::~VlFiberMemoryChunk() {
    if (m_chunkAddr) ::munmap(m_chunkAddr, chunkSize);
}

VlFiberMemoryPool::VlFiberMemoryPool()
    : m_chunks{} {}

void* VlFiberMemoryPool::get() {
    void* returnp{};
    auto chunkIt = std::find_if(m_chunks.begin(), m_chunks.end(),
                                [](const VlFiberMemoryChunk* chunk) { return chunk->m_free > 0; });
    if (VL_UNLIKELY(chunkIt == m_chunks.end())) {
        m_chunks.push_back(new VlFiberMemoryChunk{});
        size_t lastIdx = m_chunks.size() - 1;
        returnp = m_chunks[lastIdx]->m_top;
        m_chunks[lastIdx]->m_top = reinterpret_cast<void*>(
            reinterpret_cast<uintptr_t>(m_chunks[lastIdx]->m_top) + allocationSize);
        m_chunks[lastIdx]->m_free--;
        return returnp;
    }
    VlFiberMemoryChunk* chunkp = *chunkIt;
    if (!chunkp->m_freeTop) {
        returnp = chunkp->m_top;
        chunkp->m_top
            = reinterpret_cast<void*>(reinterpret_cast<uintptr_t>(chunkp->m_top) + allocationSize);
        chunkp->m_free--;
        return returnp;
    }
    returnp = chunkp->m_freeTop;
    chunkp->m_freeTop = reinterpret_cast<void*>(*reinterpret_cast<uintptr_t*>(chunkp->m_freeTop));
    return returnp;
}

void VlFiberMemoryPool::free(void* ptr) {
    auto chunkIt
        = std::find_if(m_chunks.begin(), m_chunks.end(), [&ptr](const VlFiberMemoryChunk* chunk) {
              return chunk->m_chunkAddr <= ptr
                     and ptr <= reinterpret_cast<void*>(
                             reinterpret_cast<uintptr_t>(chunk->m_chunkAddr)
                             + (allocationSize - chunkSize));
          });
    if (chunkIt == m_chunks.end()) return;
    VlFiberMemoryChunk* chunkp = *chunkIt;
    *reinterpret_cast<uintptr_t*>(ptr) = reinterpret_cast<uintptr_t>(chunkp->m_freeTop);
    chunkp->m_freeTop = ptr;
    chunkp->m_free++;
}

//======================================================================
// VlFiberContext

VlFiberContext::VlFiberContext(void (*f)(VlFiber*), VlFiber* arg) {
    mappingSize = allocationSize;
    mappingp = memoryPool.get();

    if (VL_UNLIKELY(getcontext(&fiberCtx) == -1)) {
        VL_FATAL_MT(__FILE__, __LINE__, "",
                    (std::string{"getcontext failed: "} + std::strerror(errno)).c_str());
    }
    fiberCtx.uc_stack.ss_sp = mappingp;
    fiberCtx.uc_stack.ss_size = mappingSize;
    makecontext(&fiberCtx, reinterpret_cast<void (*)()>(f), 1, arg);
}

void VlFiberContext::teardown() {
    if (mappingp) memoryPool.free(mappingp);
}

void VlFiberContext::yield() {
    // Save fiber's state and return to caller
    if (VL_UNLIKELY(swapcontext(&fiberCtx, &callerCtx) == -1)) {
        VL_FATAL_MT(__FILE__, __LINE__, "",
                    (std::string{"swapcontext failed: "} + std::strerror(errno)).c_str());
    }
    // Returns here when fiber is resumed
}

void VlFiberContext::resume() {
    // Save caller's state and switch to fiber context
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
