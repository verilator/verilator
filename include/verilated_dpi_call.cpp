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

#include "verilatedos.h"

#include "verilated_dpi_call.h"

#include <condition_variable>
#include <mutex>
#include <thread>
#include <vector>

//======================================================================
// VlDpiThread is a pool thread that runs one VlDpiCall at a time.
// m_threadTurn selects which side runs: this thread (true) or the
// thread that called VlDpiCall::handoffWorker() (false).

class VlDpiThread final {
    // MEMBERS
    std::mutex m_mutex;  // Protects m_threadTurn, m_exit
    std::condition_variable m_cv;  // Signals m_threadTurn changes
    bool m_threadTurn VL_GUARDED_BY(m_mutex) = false;  // True if this thread runs
    bool m_exit VL_GUARDED_BY(m_mutex) = false;  // Thread should exit at next wake-up
    VlDpiCall* m_callp = nullptr;  // VlDpiCall assigned to this thread
    Verilated::ThreadLocal m_verilatedTls;  // Thread-local state passed from the side that hands
                                            // off to the side that runs
    VlProcess* m_processp = nullptr;  // Current process
    VlRNG m_rng{0};  // Explicit seed: the default constructor draws from the current RNG
    std::thread m_thread;  // Must be last, starts running main()

public:
    // CONSTRUCTORS
    VlDpiThread()
        : m_thread{&VlDpiThread::main, this} {}
    VL_UNCOPYABLE(VlDpiThread);

    // METHODS
    // Give control to the other side, block until it is given back
    void handoff(bool threadTurn) {
        saveThreadLocals();
        {
            std::unique_lock<std::mutex> lock{m_mutex};
            m_threadTurn = threadTurn;
            m_cv.notify_one();
            m_cv.wait(lock, [&] { return m_threadTurn != threadTurn; });
        }
        restoreThreadLocals();
    }
    void assign(VlDpiCall* callp) { m_callp = callp; }
    // Stop and join an idle thread
    void stop() {
        {
            const std::lock_guard<std::mutex> lock{m_mutex};
            m_exit = true;
            m_threadTurn = true;
            m_cv.notify_one();
        }
        m_thread.join();
    }

private:
    void saveThreadLocals() {
        m_verilatedTls = Verilated::t_s;
        m_processp = VlProcess::currentp();
        m_rng = VlRNG::vl_thread_rng();
    }
    void restoreThreadLocals() {
        Verilated::t_s = m_verilatedTls;
        VlProcess::currentp(m_processp);
        VlRNG::vl_thread_rng() = m_rng;
    }
    void main() {
        {
            std::unique_lock<std::mutex> lock{m_mutex};
            m_cv.wait(lock, [this] { return m_threadTurn; });
        }
        restoreThreadLocals();
        while (!m_exit) {
            VlDpiCall::t_currentp = m_callp;
            m_callp->m_fn();
            m_callp->m_done = true;
            VlDpiCall::t_currentp = nullptr;
            handoff(false);  // Returns when the next VlDpiCall is assigned, or on stop()
        }
    }
};

//======================================================================
// VlDpiThreadPool keeps idle VlDpiThreads for reuse

class VlDpiThreadPool final {
    std::mutex m_mutex;  // Protects m_idle and m_aborted
    std::vector<VlDpiThread*> m_idle VL_GUARDED_BY(m_mutex);  // Idle threads
    std::vector<VlDpiCall*> m_aborted VL_GUARDED_BY(m_mutex);  // Aborted DPI calls

public:
    VlDpiThreadPool() = default;
    VL_UNCOPYABLE(VlDpiThreadPool);
    ~VlDpiThreadPool() {
        for (VlDpiThread* const threadp : m_idle) {
            threadp->stop();
            delete threadp;
        }
    }
    VlDpiThread* acquire() {
        {
            const std::lock_guard<std::mutex> lock{m_mutex};
            if (!m_idle.empty()) {
                VlDpiThread* const threadp = m_idle.back();
                m_idle.pop_back();
                return threadp;
            }
        }
        return new VlDpiThread;
    }
    void release(VlDpiThread* threadp) {
        const std::lock_guard<std::mutex> lock{m_mutex};
        m_idle.push_back(threadp);
    }
    void addAborted(VlDpiCall* callp) {
        const std::lock_guard<std::mutex> lock{m_mutex};
        m_aborted.push_back(callp);
    }
    void resumeAborted() {
        while (true) {
            VlDpiCall* callp;
            {
                const std::lock_guard<std::mutex> lock{m_mutex};
                if (m_aborted.empty()) return;
                callp = m_aborted.back();
                m_aborted.pop_back();
            }

            // Thread that is currently executing this VlDpiCall is stuck in stopWorker().
            // Here we resume it.
            callp->handoffWorker();
        }
    }
};

static VlDpiThreadPool& threadPool() {
    static VlDpiThreadPool s_pool;
    return s_pool;
}

namespace VerilatedDpiCall {
void resumeAborted() { threadPool().resumeAborted(); }
};  //namespace VerilatedDpiCall

//======================================================================
// VlDpiCall:: Methods

thread_local VlDpiCall* VlDpiCall::t_currentp = nullptr;

VlDpiCall::VlDpiCall(VlProcessRef process, std::function<void()> fn)
    : m_process{std::move(process)}
    , m_fn{std::move(fn)}
    , m_threadp{threadPool().acquire()} {
    m_threadp->assign(this);
}

void VlDpiCall::handoffWorker() {
    m_threadp->handoff(true);
    if (!m_done) return;
    threadPool().release(m_threadp);
    if (const std::coroutine_handle<> waiter = m_waiter) {
        // Do not continue if this process was killed
        if (exportAborted()) waiter.destroy();
        // Resuming the waiter can destroy this object
        else
            waiter.resume();
    }
}

void VlDpiCall::markAborted() {
    m_exportAborted = true;
    threadPool().addAborted(this);
}

void VlDpiCall::stopWorker() {
    const VerilatedScope* const scopep = Verilated::dpiScope();
    const char* const filenamep = Verilated::dpiFilenamep();
    const int lineno = Verilated::dpiLineno();
    t_currentp->m_threadp->handoff(false);
    Verilated::dpiContext(scopep, filenamep, lineno);
}
