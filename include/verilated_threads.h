// -*- mode: C++; c-file-style: "cc-mode" -*-
//=============================================================================
//
// THIS MODULE IS PUBLICLY LICENSED
//
// Copyright 2012-2020 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//=============================================================================
///
/// \file
/// \brief Thread pool and profiling for Verilated modules
///
//=============================================================================

#ifndef _VERILATED_THREADS_H_
#define _VERILATED_THREADS_H_

#include "verilatedos.h"
#include "verilated.h"  // for VerilatedMutex and clang annotations

#include <condition_variable>
#include <set>
#include <vector>
#if defined(__linux)
#include <sched.h>  // For sched_getcpu()
#endif
#if defined(__APPLE__)
# include <cpuid.h>  // For __cpuid_count()
#endif

// VlMTaskVertex and VlThreadpool will work with multiple symbol table types.
// Since the type is opaque to VlMTaskVertex and VlThreadPool, represent it
// as a void* here.
typedef void* VlThrSymTab;

typedef void (*VlExecFnp)(bool, VlThrSymTab);

/// Track dependencies for a single MTask.
class VlMTaskVertex {
    // MEMBERS
    static std::atomic<vluint64_t> s_yields;  // Statistics

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
    std::atomic<vluint32_t> m_upstreamDepsDone;
    const vluint32_t m_upstreamDepCount;

public:
    // CONSTRUCTORS

    // 'upstreamDepCount' is the number of upstream MTaskVertex's
    // that must notify this MTaskVertex before it will become ready
    // to run.
    explicit VlMTaskVertex(vluint32_t upstreamDepCount);
    ~VlMTaskVertex() {}

    static vluint64_t yields() { return s_yields; }
    static void yieldThread() {
        ++s_yields;  // Statistics
        std::this_thread::yield();
    }

    // Upstream mtasks must call this when they complete.
    // Returns true when the current MTaskVertex becomes ready to execute,
    // false while it's still waiting on more dependencies.
    inline bool signalUpstreamDone(bool evenCycle) {
        if (evenCycle) {
            vluint32_t upstreamDepsDone
                = 1 + m_upstreamDepsDone.fetch_add(1, std::memory_order_release);
            assert(upstreamDepsDone <= m_upstreamDepCount);
            return (upstreamDepsDone == m_upstreamDepCount);
        } else {
            vluint32_t upstreamDepsDone_prev
                = m_upstreamDepsDone.fetch_sub(1, std::memory_order_release);
            assert(upstreamDepsDone_prev > 0);
            return (upstreamDepsDone_prev == 1);
        }
    }
    inline bool areUpstreamDepsDone(bool evenCycle) const {
        vluint32_t target = evenCycle ? m_upstreamDepCount : 0;
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

// Profiling support
class VlProfileRec {
protected:
    friend class VlThreadPool;
    enum VlProfileE {
        TYPE_MTASK_RUN,
        TYPE_BARRIER
    };
    VlProfileE m_type;  // Record type
    vluint32_t m_mtaskId;  // Mtask we're logging
    vluint32_t m_predictTime;  // How long scheduler predicted would take
    vluint64_t m_startTime;  // Tick at start of execution
    vluint64_t m_endTime;  // Tick at end of execution
    unsigned m_cpu;  // Execution CPU number (at start anyways)
public:
    class Barrier {};
    VlProfileRec() {}
    explicit VlProfileRec(Barrier) {
        m_type = TYPE_BARRIER;
        m_mtaskId = 0;
        m_predictTime = 0;
        m_startTime = 0;
        m_endTime = 0;
        m_cpu = getcpu();
    }
    void startRecord(vluint64_t time, uint32_t mtask, uint32_t predict) {
        m_type = VlProfileRec::TYPE_MTASK_RUN;
        m_mtaskId = mtask;
        m_predictTime = predict;
        m_startTime = time;
        m_cpu = getcpu();
    }
    void endRecord(vluint64_t time) { m_endTime = time; }
    static int getcpu() {  // Return current executing CPU
#if defined(__linux)
        return sched_getcpu();
#elif defined(__APPLE__)
        vluint32_t info[4];
        __cpuid_count(1, 0, info[0], info[1], info[2], info[3]);
        // info[1] is EBX, bits 24-31 are APIC ID
        if ((info[3] & (1 << 9)) == 0) {
            return -1;  // no APIC on chip
        } else {
            return (unsigned)info[1] >> 24;
        }
#elif defined(_WIN32)
        return GetCurrentProcessorNumber();
#else
        return 0;
#endif
    }
};

class VlThreadPool;

class VlWorkerThread {
private:
    // TYPES
    struct ExecRec {
        VlExecFnp m_fnp;  // Function to execute
        VlThrSymTab m_sym;  // Symbol table to execute
        bool m_evenCycle;  // Even/odd for flag alternation
        ExecRec() : m_fnp(NULL), m_sym(NULL), m_evenCycle(false) {}
        ExecRec(VlExecFnp fnp, bool evenCycle, VlThrSymTab sym)
            : m_fnp(fnp), m_sym(sym), m_evenCycle(evenCycle) {}
    };

    // MEMBERS
    VerilatedMutex m_mutex;
    std::condition_variable_any m_cv;
    // Only notify the condition_variable if the worker is waiting
    bool m_waiting VL_GUARDED_BY(m_mutex);

    // Why a vector? We expect the pending list to be very short, typically
    // 0 or 1 or 2, so popping from the front shouldn't be
    // expensive. Revisit if we ever have longer queues...
    std::vector<ExecRec> m_ready VL_GUARDED_BY(m_mutex);
    // Store the size atomically, so we can spin wait
    std::atomic<size_t> m_ready_size;

    VlThreadPool* m_poolp;  // Our associated thread pool

    bool m_profiling;  // Is profiling enabled?
    std::atomic<bool> m_exiting;  // Worker thread should exit
    std::thread m_cthread;  // Underlying C++ thread record

    VL_UNCOPYABLE(VlWorkerThread);

public:
    // CONSTRUCTORS
    explicit VlWorkerThread(VlThreadPool* poolp, bool profiling);
    ~VlWorkerThread();

    // METHODS
    inline void dequeWork(ExecRec* workp) {
        // Spin for a while, waiting for new data
        for (int i = 0; i < VL_LOCK_SPINS; ++i) {
            if (VL_LIKELY(m_ready_size.load(std::memory_order_relaxed))) {
                break;
            }
            VL_CPU_RELAX();
        }
        VerilatedLockGuard lk(m_mutex);
        while (m_ready.empty()) {
            m_waiting = true;
            m_cv.wait(lk);
        }
        m_waiting = false;
        // As noted above this is inefficient if our ready list is ever
        // long (but it shouldn't be)
        *workp = m_ready.front();
        m_ready.erase(m_ready.begin());
        m_ready_size.fetch_sub(1, std::memory_order_relaxed);
    }
    inline void wakeUp() { addTask(nullptr, false, nullptr); }
    inline void addTask(VlExecFnp fnp, bool evenCycle, VlThrSymTab sym) {
        bool notify;
        {
            VerilatedLockGuard lk(m_mutex);
            m_ready.emplace_back(fnp, evenCycle, sym);
            m_ready_size.fetch_add(1, std::memory_order_relaxed);
            notify = m_waiting;
        }
        if (notify) m_cv.notify_one();
    }
    void workerLoop();
    static void startWorker(VlWorkerThread* workerp);
};

class VlThreadPool {
    // TYPES
    typedef std::vector<VlProfileRec> ProfileTrace;
    typedef std::set<ProfileTrace*> ProfileSet;

    // MEMBERS
    std::vector<VlWorkerThread*> m_workers;  // our workers
    bool m_profiling;  // is profiling enabled?

    // Support profiling -- we can append records of profiling events
    // to this vector with very low overhead, and then dump them out
    // later. This prevents the overhead of printf/malloc/IO from
    // corrupting the profiling data. It's super cheap to append
    // a VlProfileRec struct on the end of a pre-allocated vector;
    // this is the only cost we pay in real-time during a profiling cycle.
    static VL_THREAD_LOCAL ProfileTrace* t_profilep;
    ProfileSet m_allProfiles VL_GUARDED_BY(m_mutex);
    VerilatedMutex m_mutex;

public:
    // CONSTRUCTORS
    // Construct a thread pool with 'nThreads' dedicated threads. The thread
    // pool will create these threads and make them available to execute tasks
    // via this->workerp(index)->addTask(...)
    VlThreadPool(int nThreads, bool profiling);
    ~VlThreadPool();

    // METHODS
    inline int numThreads() const { return m_workers.size(); }
    inline VlWorkerThread* workerp(int index) {
        assert(index >= 0);
        assert(index < m_workers.size());
        return m_workers[index];
    }
    inline VlProfileRec* profileAppend() {
        t_profilep->emplace_back();
        return &(t_profilep->back());
    }
    void profileAppendAll(const VlProfileRec& rec);
    void profileDump(const char* filenamep, vluint64_t ticksElapsed);
    // In profiling mode, each executing thread must call
    // this once to setup profiling state:
    void setupProfilingClientThread();
    void tearDownProfilingClientThread();
private:
    VL_UNCOPYABLE(VlThreadPool);
};

#endif
