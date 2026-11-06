// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
//
// Code available from: https://verilator.org
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************
///
/// \file
/// \brief Suspendable DPI imported task calls with --timing enabled
///
/// A VlDpiCall runs a DPI import call on a separate thread taken from
/// a thread pool. At any time either the resuming thread or the DPI thread
/// runs, never both. Verilated thread-local state is copied at each
/// handoff.
///
/// This file is not part of the Verilated public-facing API.
/// It is only for internal use.
///
/// See the internals documentation docs/internals.rst for details.
///
//*************************************************************************

#ifndef VERILATOR_VERILATED_DPI_CALL_H_
#define VERILATOR_VERILATED_DPI_CALL_H_

#include "verilatedos.h"

#include "verilated_threads.h"
#include "verilated_timing.h"

#include <functional>

namespace VerilatedDpiCall {
void resumeAborted();
}

//=============================================================================
// VlDpiCall runs a function on a pool thread. co_await on a VlDpiCall
// suspends until the function returns.

class VlDpiCall final {
    // MEMBERS
    const VlProcessRef m_process;  // SV process executing the imported task
    const std::function<void()> m_fn;  // Function executed on the pool thread
    VerilatedContext* const m_contextp;  // Owning context, whose pool can be recreated on clone
    VlWorkerThread* const m_threadp;  // Worker retained until m_fn returns
    VerilatedMutex m_mutex;  // Protects m_workerTurn and orders thread-local state transfers
    std::condition_variable_any m_cv;  // Signals handoff between the worker and its caller
    bool m_workerTurn VL_GUARDED_BY(m_mutex) = false;  // True while the worker runs
    Verilated::ThreadLocal m_verilatedTls;  // State passed to the side that runs
    VlProcess* m_currentProcessp = nullptr;  // Current process passed at handoff
    VlRNG m_rng{0};  // Explicit seed: the default constructor draws from the current RNG
    bool m_done = false;  // Set once m_fn returns
    bool m_exportAborted = false;  // Set if the process was killed during the DPI call
    std::coroutine_handle<> m_waiter;  // Coroutine resumed when m_fn returns

    static thread_local VlDpiCall* t_currentp;  // VlDpiCall executing on this thread

public:
    // CONSTRUCTORS
    VlDpiCall(VlProcessRef process, std::function<void()> fn);
    VL_UNCOPYABLE(VlDpiCall);

    // METHODS
    // Run m_fn until it yields or returns; the calling thread blocks meanwhile
    void handoffWorker();
    // Called on the DPI thread: hand control back to the last handoffWorker() caller
    static void stopWorker();
    // VlDpiCall running on this thread (nullptr if not a DPI thread)
    static VlDpiCall* current() noexcept { return t_currentp; }
    const VlProcessRef& process() const noexcept { return m_process; }
    // Mark this VlDpiCall as aborted due to process::kill()
    void markAborted();
    bool exportAborted() const noexcept {
        return m_exportAborted || (m_process && m_process->state() == VlProcess::KILLED);
    }

    bool await_ready() const noexcept { return m_done; }
    void await_suspend(std::coroutine_handle<> waiter) noexcept { m_waiter = waiter; }
    void await_resume() const noexcept {}

private:
    void saveThreadLocals();
    void restoreThreadLocals();
    void handoff(bool workerTurn);
    void run();
};

#endif  // Guard
