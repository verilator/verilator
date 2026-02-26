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

class VerilatedDpi final {
private:
    class FiberAwaitable final {
        VlFiber& m_fiber;

    public:
        explicit FiberAwaitable(VlFiber& fiber)
            : m_fiber{fiber} {}

        bool await_ready() const noexcept { return m_fiber.isDone(); }
        void await_suspend(std::coroutine_handle<> waiter) const { m_fiber.addWaiter(waiter); }
        void await_resume() const noexcept {}
    };

public:
    // Run user C code in a fiber, wrapping it in a coroutine for scheduler integration
    // This allows the C code to call DPI exports with timing controls
    template <typename Callable>
    static VlCoroutine callImport(Callable&& fn) {
        auto fiberp
            = VlFiber::create([captured = std::forward<Callable>(fn)]() mutable { captured(); });
        while (!fiberp->isDone()) {
            fiberp->resume();
            if (!fiberp->isDone()) co_await FiberAwaitable{*fiberp};
        }
        co_return;
    }

    // Suspend the current fiber until the DPI export coroutine completes
    // Must be called from within a fiber context (i.e., from C code called via DPI import)
    template <typename Callable>
    static void awaitExport(Callable&& coro) {
        VlFiber* const fiberp = VlFiber::current();
        if (VL_UNLIKELY(!fiberp)) {
            VL_FATAL_MT(__FILE__, __LINE__, "",
                        "DPI export with timing invoked outside of a fiber context");
        }
        if VL_CONSTEXPR_CXX17 (std::is_same<std::result_of_t<Callable && ()>,
                                            VlCoroutine>::value) {
            VlCoroutine local{coro()};
            if (local.await_ready()) return;
            do {
                local.setFiberContinuation(fiberp);
                VlFiber::yield();
            } while (!local.await_ready());
        } else {
            coro();
        }
    }
};

//======================================================================

#endif  // Guard
