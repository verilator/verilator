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
//=========================================================================
///
/// \file
/// \brief Implementation of suspendable DPI imported task calls
///
//*************************************************************************

// clang-format off
#include "verilatedos.h"

#include "verilated.h"

#include "verilated_dpi_call.h"
// clang-format on

//======================================================================
// VlDpiCall:: Methods

thread_local VlDpiCall* VlDpiCall::t_currentp = nullptr;

VlDpiCall::VlDpiCall(VlProcessRef process, std::function<void()> fn)
    : m_process{std::move(process)}
    , m_fn{std::move(fn)}
    , m_contextp{Verilated::threadContextp()}
    , m_threadp{static_cast<VlThreadPool*>(m_contextp->threadPoolp())->acquireWorker()} {
    m_threadp->addTask([](void* selfp) { static_cast<VlDpiCall*>(selfp)->run(); }, this);
}

void VlDpiCall::saveThreadLocals() VL_MT_UNSAFE_ONE {
    m_verilatedTls = Verilated::t_s;
    m_currentProcessp = VlProcess::currentp();
    m_rng = VlRNG::vl_thread_rng();
}

void VlDpiCall::restoreThreadLocals() VL_MT_UNSAFE_ONE {
    Verilated::t_s = m_verilatedTls;
    VlProcess::currentp(m_currentProcessp);
    VlRNG::vl_thread_rng() = m_rng;
}

void VlDpiCall::handoff(bool workerTurn) VL_MT_UNSAFE_ONE {
    saveThreadLocals();
    {
        const VerilatedLockGuard lock{m_mutex};
        m_workerTurn = workerTurn;
        m_cv.notify_one();
        m_cv.wait(m_mutex, [&]() VL_REQUIRES(m_mutex) { return m_workerTurn != workerTurn; });
    }
    restoreThreadLocals();
}

void VlDpiCall::run() VL_MT_UNSAFE_ONE {
    {
        const VerilatedLockGuard lock{m_mutex};
        m_cv.wait(m_mutex, [this]() VL_REQUIRES(m_mutex) { return m_workerTurn; });
    }
    restoreThreadLocals();
    t_currentp = this;
    m_fn();
    t_currentp = nullptr;
    saveThreadLocals();
    // The caller can destroy this object once it acquires the mutex. All accesses to the
    // call, including the notification, must finish before releasing the lock.
    const VerilatedLockGuard lock{m_mutex};
    m_done = true;
    m_workerTurn = false;
    m_cv.notify_one();
}

void VlDpiCall::handoffWorker() VL_MT_UNSAFE_ONE {
    handoff(true);
    if (!m_done) return;
    static_cast<VlThreadPool*>(m_contextp->threadPoolp())->releaseWorker(m_threadp);
    if (const std::coroutine_handle<> waiter = m_waiter) {
        if (exportAborted()) {
            waiter.destroy();  // Do not continue if this process was killed.
        } else {
            waiter.resume();  // Resuming the waiter can destroy this object.
        }
    }
}

void VlDpiCall::markAborted() VL_MT_UNSAFE_ONE {
    m_exportAborted = true;
    VerilatedDpiCall::enqueueAborted([this]() { handoffWorker(); });
}

void VlDpiCall::stopWorker() VL_MT_UNSAFE_ONE {
    const VerilatedScope* const scopep = Verilated::dpiScope();
    const char* const filenamep = Verilated::dpiFilenamep();
    const int lineno = Verilated::dpiLineno();
    t_currentp->handoff(false);
    Verilated::dpiContext(scopep, filenamep, lineno);
}
