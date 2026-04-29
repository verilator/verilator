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
/// \brief Verilated DPI fiber integration header
///
//*************************************************************************

#ifndef VERILATOR_VERILATED_DPI_FIBER_H_
#define VERILATOR_VERILATED_DPI_FIBER_H_

#include "verilated.h"
#include "verilated_fiber.h"
#include "verilated_timing.h"

#include <coroutine>
#include <utility>

//======================================================================

namespace {
class FiberAwaitable final {
    VlFiber& m_fiber;

public:
    explicit FiberAwaitable(VlFiber& fiber)
        : m_fiber{fiber} {}

    bool await_ready() const noexcept { return m_fiber.isDone(); }
    void await_suspend(std::coroutine_handle<> waiter) const { m_fiber.addWaiter(waiter); }
    void await_resume() const noexcept {}
};
};  //namespace

namespace VerilatedDpi {
// Run user C code in a fiber, wrapping it in a coroutine for scheduler integration
// This allows the C code to call DPI exports with timing controls
// Callable has void return type because it is a task.
template <typename Callable, typename... Args>
VlCoroutine callImportFiber(Callable&& call, Args&&... args) {
    static_assert(std::is_same<decltype(call(std::forward<Args>(args)...)), int>::value,
                  "Functions called inside a fiber should have 'int' return type");
    auto fiberp{VlFiber::create(
        [&call, &args...]() mutable { std::ignore = call(std::forward<Args>(args)...); })};
    while (!fiberp->isDone()) {
        fiberp->resume();
        co_await FiberAwaitable{*fiberp};
    }
    co_return;
}

// Suspend the current fiber until the DPI export coroutine completes
// Must be called from within a fiber context (i.e., from C code called via DPI import)
template <typename Callable, typename... Args>
decltype(auto) awaitExportFiber(Callable&& call, Args&&... args) {
    static_assert(std::is_same<decltype(call(std::forward<Args>(args)...)), VlCoroutine>::value,
                  "Expected the exported function to be a VlCoroutine");
    VlFiber* const fiberp = VlFiber::current();
    if (VL_UNLIKELY(!fiberp)) {
        VL_FATAL_MT(__FILE__, __LINE__, "",
                    "DPI export with timing invoked outside of a fiber context");
    }
    // Call will return on first delay/event encountered
    VlCoroutine local{call(std::forward<Args>(args)...)};
    local.setFiberContinuation(fiberp);
    while (!local.await_ready()) { VlFiber::yield(); }
}
};  //namespace VerilatedDpi

//======================================================================

#endif  // Guard
