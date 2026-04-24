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

static thread_local struct {
    char* m_filename;
    int m_lineno;
    bool m_inFuncContext;
} s_fileline;

};  //namespace

namespace VerilatedDpi {
// Run user C code in a fiber, wrapping it in a coroutine for scheduler integration
// This allows the C code to call DPI exports with timing controls
template <typename Callable>
VlCoroutine callImportInFiber(Callable&& fn) {
    auto fiberp{
        VlFiber::create([captured = std::forward<Callable>(fn)]() mutable { captured(); })};
    while (!fiberp->isDone()) {
        fiberp->resume();
        co_await FiberAwaitable{*fiberp};
    }
    co_return;
}

template <bool isTask, typename Callable>
constexpr void callImport(Callable&& fn, char* const filename, int lineno) {
    if VL_CONSTEXPR_CXX17 (!isTask) {
        s_fileline.m_filename = filename;
        s_fileline.m_lineno = lineno;
        s_fileline.m_inFuncContext = true;
    }
    fn();
    if VL_CONSTEXPR_CXX17 (!isTask) { s_fileline.m_inFuncContext = false; }
}

// Suspend the current fiber until the DPI export coroutine completes
// Must be called from within a fiber context (i.e., from C code called via DPI import)
template <bool isTask, typename Callable, typename... Args>
void awaitExport(Callable&& call, Args&&... args) {
    if VL_CONSTEXPR_CXX17 (isTask) {
        if (s_fileline.m_inFuncContext) {
            VL_FATAL_MT(s_fileline.m_filename, s_fileline.m_lineno, "",
                        "DPI exported task called from function context");
        }
    }
    if VL_CONSTEXPR_CXX17 (std::is_same<decltype(call(std::forward<Args>(args)...)),
                                        VlCoroutine>::value) {
        VlFiber* const fiberp = VlFiber::current();
        if (VL_UNLIKELY(!fiberp)) {
            VL_FATAL_MT(__FILE__, __LINE__, "",
                        "DPI export with timing invoked outside of a fiber context");
        }
        // Call will return on first delay/event encountered
        VlCoroutine local{call(std::forward<Args>(args)...)};
        local.setFiberContinuation(fiberp);
        while (!local.await_ready()) { VlFiber::yield(); }
    } else {
        // Might be a task without timings or a function
        call(std::forward<Args>(args)...);
    }
}
};  //namespace VerilatedDpi

//======================================================================

#endif  // Guard
