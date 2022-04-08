// -*- mode: C++; c-file-style: "cc-mode" -*-
//=============================================================================
//
// Code available from: https://verilator.org
//
// Copyright 2012-2022 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//=============================================================================
///
/// \file
/// \brief Verilated thread pool and profiling header
///
/// This file is not part of the Verilated public-facing API.
/// It is only for internal use by Verilated library multithreaded
/// routines.
///
//=============================================================================

#ifndef VERILATOR_VERILATED_THREADS_H_
#define VERILATOR_VERILATED_THREADS_H_

#include "verilatedos.h"
#include "verilated.h"  // for VerilatedMutex and clang annotations

#ifndef VL_THREADED
// Hitting this likely means verilated_threads.cpp is being compiled when
// 'verilator --threads' was not used.  'verilator --threads' sets
// VL_THREADED.
// Alternatively it is always safe but may harm performance to always
// define VL_THREADED for all compiles.
#error "verilated_threads.h/cpp expected VL_THREADED (from verilator --threads)"
#endif

#include <atomic>
#include <condition_variable>
#include <set>
#include <thread>
#include <vector>

// clang-format off
#if defined(__linux)
# include <sched.h>  // For sched_getcpu()
#endif
#if defined(__APPLE__) && !defined(__arm64__)
# include <cpuid.h>  // For __cpuid_count()
#endif
// clang-format on

// VlMTaskVertex and VlThreadpool will work with multiple model class types.
// Since the type is opaque to VlMTaskVertex and VlThreadPool, represent it
// as a void* here.
using VlSelfP = void*;

using VlExecFnp = void (*)(VlSelfP, bool);

// Track dependencies for a single MTask.
class VlMTaskVertex final {
    // MEMBERS
    static std::atomic<uint64_t> s_yields;  // Statistics

    // On even cycles, _upstreamDepsDone increases as upstream
    // dependencies complete. When it reaches _upstreamDepCount,
    // this MTaskVertex is ready.
    //
    // On odd cycles, _upstreamDepsDone decreases as upstream
    // dependencies complete, and when it reaches zero this MTaskVertex
    // is ready.
    //
    // An atomic is smaller than a mutex, and lock-free.
    //
    // (Why does the size of this class matter? If an mtask has many
    // downstream mtasks to notify, we hope these will pack into a
    // small number of cache lines to reduce the cost of pointer chasing
    // during done-notification. Nobody's quantified that cost though.
    // If we were really serious about shrinking this class, we could
    // use 16-bit types here...)
    std::atomic<uint32_t> m_upstreamDepsDone;
    const uint32_t m_upstreamDepCount;

public:
    // CONSTRUCTORS

    // 'upstreamDepCount' is the number of upstream MTaskVertex's
    // that must notify this MTaskVertex before it will become ready
    // to run.
    explicit VlMTaskVertex(uint32_t upstreamDepCount);
    ~VlMTaskVertex() = default;

    static uint64_t yields() { return s_yields; }
    static void yieldThread() {
        ++s_yields;  // Statistics
        std::this_thread::yield();
    }

    // Upstream mtasks must call this when they complete.
    // Returns true when the current MTaskVertex becomes ready to execute,
    // false while it's still waiting on more dependencies.
    inline bool signalUpstreamDone(bool evenCycle) {
        if (evenCycle) {
            const uint32_t upstreamDepsDone
                = 1 + m_upstreamDepsDone.fetch_add(1, std::memory_order_release);
            assert(upstreamDepsDone <= m_upstreamDepCount);
            return (upstreamDepsDone == m_upstreamDepCount);
        } else {
            const uint32_t upstreamDepsDone_prev
                = m_upstreamDepsDone.fetch_sub(1, std::memory_order_release);
            assert(upstreamDepsDone_prev > 0);
            return (upstreamDepsDone_prev == 1);
        }
    }
    inline bool areUpstreamDepsDone(bool evenCycle) const {
        const uint32_t target = evenCycle ? m_upstreamDepCount : 0;
        return m_upstreamDepsDone.load(std::memory_order_acquire) == target;
    }
    inline void waitUntilUpstreamDone(bool evenCycle) const {
        unsigned ct = 0;
        while (VL_UNLIKELY(!areUpstreamDepsDone(evenCycle))) {
            VL_CPU_RELAX();
            ++ct;
            if (VL_UNLIKELY(ct > VL_LOCK_SPINS)) {
                ct = 0;
                yieldThread();
            }
        }
    }
};

class VlExecutionProfiler;
class VlThreadPool;

class VlWorkerThread final {
private:
    // TYPES
    struct ExecRec {
        VlExecFnp m_fnp;  // Function to execute
        VlSelfP m_selfp;  // Symbol table to execute
        bool m_evenCycle;  // Even/odd for flag alternation
        ExecRec()
            : m_fnp{nullptr}
            , m_selfp{nullptr}
            , m_evenCycle{false} {}
        ExecRec(VlExecFnp fnp, VlSelfP selfp, bool evenCycle)
            : m_fnp{fnp}
            , m_selfp{selfp}
            , m_evenCycle{evenCycle} {}
    };

    // MEMBERS
    VerilatedMutex m_mutex;
    std::condition_variable_any m_cv;
    // Only notify the condition_variable if the worker is waiting
    bool m_waiting VL_GUARDED_BY(m_mutex) = false;

    // Why a vector? We expect the pending list to be very short, typically
    // 0 or 1 or 2, so popping from the front shouldn't be
    // expensive. Revisit if we ever have longer queues...
    std::vector<ExecRec> m_ready VL_GUARDED_BY(m_mutex);
    // Store the size atomically, so we can spin wait
    std::atomic<size_t> m_ready_size;

    std::atomic<bool> m_exiting;  // Worker thread should exit
    std::thread m_cthread;  // Underlying C++ thread record
    VerilatedContext* const m_contextp;  // Context for spawned thread

    VL_UNCOPYABLE(VlWorkerThread);

public:
    // CONSTRUCTORS
    explicit VlWorkerThread(uint32_t threadId, VerilatedContext* contextp,
                            VlExecutionProfiler* profilerp);
    ~VlWorkerThread();

    // METHODS
    inline void dequeWork(ExecRec* workp) VL_MT_SAFE_EXCLUDES(m_mutex) {
        // Spin for a while, waiting for new data
        for (int i = 0; i < VL_LOCK_SPINS; ++i) {
            if (VL_LIKELY(m_ready_size.load(std::memory_order_relaxed))) {  //
                break;
            }
            VL_CPU_RELAX();
        }
        VerilatedLockGuard lock{m_mutex};
        while (m_ready.empty()) {
            m_waiting = true;
            m_cv.wait(lock);
        }
        m_waiting = false;
        // As noted above this is inefficient if our ready list is ever
        // long (but it shouldn't be)
        *workp = m_ready.front();
        m_ready.erase(m_ready.begin());
        m_ready_size.fetch_sub(1, std::memory_order_relaxed);
    }
    inline void wakeUp() { addTask(nullptr, nullptr, false); }
    inline void addTask(VlExecFnp fnp, VlSelfP selfp, bool evenCycle)
        VL_MT_SAFE_EXCLUDES(m_mutex) {
        bool notify;
        {
            const VerilatedLockGuard lock{m_mutex};
            m_ready.emplace_back(fnp, selfp, evenCycle);
            m_ready_size.fetch_add(1, std::memory_order_relaxed);
            notify = m_waiting;
        }
        if (notify) m_cv.notify_one();
    }
    void workerLoop();
    static void startWorker(VlWorkerThread* workerp, uint32_t threadId,
                            VlExecutionProfiler* profilerp);
};

class VlThreadPool final {
    // MEMBERS
    std::vector<VlWorkerThread*> m_workers;  // our workers

public:
    // CONSTRUCTORS
    // Construct a thread pool with 'nThreads' dedicated threads. The thread
    // pool will create these threads and make them available to execute tasks
    // via this->workerp(index)->addTask(...)
    VlThreadPool(VerilatedContext* contextp, int nThreads, VlExecutionProfiler* profilerp);
    ~VlThreadPool();

    // METHODS
    inline int numThreads() const { return m_workers.size(); }
    inline VlWorkerThread* workerp(int index) {
        assert(index >= 0);
        assert(index < m_workers.size());
        return m_workers[index];
    }

private:
    VL_UNCOPYABLE(VlThreadPool);
};

#endif
