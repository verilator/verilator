// -*- mode: C++; c-file-style: "cc-mode" -*-
//=============================================================================
//
// Code available from: https://verilator.org
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2012-2026 Wilson Snyder
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

#include <atomic>
#include <condition_variable>
#include <memory>
#include <set>
#include <stack>
#include <thread>
#include <vector>

// Use pthreads directly on macOS (could do this on Linux too if needing APIs unavailable via C++)
#if defined(_POSIX_THREADS) && defined(__APPLE__)
#define VL_USE_PTHREADS
#endif

#ifdef VL_USE_PTHREADS
#include <pthread.h>
#endif

class VlExecutionProfiler;
class VlFixedTask;
class VlThreadPool;

// VlThreadpool will work with multiple model class types.
// Since the type is opaque to VlThreadPool, represent it
// as a void* here.
using VlSelfP = void*;

using VlExecFnp = void (*)(VlSelfP);

// Progress of one thread through its part of a static mtask schedule: the position, counted
// from 1, of its last finished mtask. Written only by that thread, with a plain release store;
// other threads wait for it with acquire loads. No read-modify-write, and one cache line per
// thread, so a dependency costs one line transfer from producer to consumer, however many
// consumers there are.
class alignas(VL_CACHE_LINE_BYTES) VlThreadProgress final {
    // MEMBERS
    static std::atomic<uint64_t> s_yields;  // Statistics
    std::atomic<uint32_t> m_pos{0};  // Position of the last finished mtask, or DONE

public:
    static constexpr uint32_t DONE = ~0U;  // Thread finished its part of the schedule

    static uint64_t yields() { return s_yields; }
    static void yieldThread() {
        ++s_yields;  // Statistics
        std::this_thread::yield();
    }

    // Dispatching thread, while no thread runs the schedule
    void reset() { m_pos.store(0, std::memory_order_relaxed); }
    // Thread running its part: everything up to and including 'pos' is done
    void publish(uint32_t pos) { m_pos.store(pos, std::memory_order_release); }
    // Other threads: wait until the thread has published at least 'pos'
    void waitFor(uint32_t pos) const {
        unsigned ct = 0;
        while (VL_UNLIKELY(m_pos.load(std::memory_order_acquire) < pos)) {
            VL_CPU_RELAX();
            ++ct;
            if (VL_UNLIKELY(ct > VL_LOCK_SPINS)) {
                ct = 0;
                yieldThread();
            }
        }
    }
};

// Progress of the threads running the schedule of one exec graph; a graph runs one schedule at
// a time.
template <size_t N_Threads>
class VlScheduleProgress final {
    // MEMBERS
    VlThreadProgress m_threads[N_Threads];  // Progress of each thread of the schedule

public:
    // Dispatching thread, before starting a schedule. Handing the threads' functions to the
    // thread pool orders this before they start.
    void start() {
        for (VlThreadProgress& thread : m_threads) thread.reset();
    }
    void publish(uint32_t thread, uint32_t pos) { m_threads[thread].publish(pos); }
    void waitFor(uint32_t thread, uint32_t pos) const { m_threads[thread].waitFor(pos); }
    void done(uint32_t thread) { m_threads[thread].publish(VlThreadProgress::DONE); }
    // Dispatching thread: wait for a thread run by the pool to be done
    void waitDone(uint32_t thread) const { m_threads[thread].waitFor(VlThreadProgress::DONE); }
};

class VlWorkerThread final {
    friend class VlFixedTask;
    friend class VlThreadPool;

    // TYPES
    struct ExecRec final {
        VlExecFnp m_fnp = nullptr;  // Function to execute
        VlSelfP m_selfp = nullptr;  // Symbol table to execute
        ExecRec() = default;
        ExecRec(VlExecFnp fnp, VlSelfP selfp)
            : m_fnp{fnp}
            , m_selfp{selfp} {}
    };
    // Fixed tasks may outlive the pool after fatal shutdown or prepareClone().
    struct FixedLifetime final {};

    // MEMBERS
    mutable VerilatedMutex m_mutex;  // Protection mutex
    std::condition_variable_any m_cv;  // Wake a parked worker when work arrives
    // Only notify the condition_variable if the worker is waiting
    bool m_waiting VL_GUARDED_BY(m_mutex) = false;

    // Why a vector? We expect the pending list to be very short, typically
    // 0 or 1 or 2, so popping from the front shouldn't be
    // expensive. Revisit if we ever have longer queues...
    std::vector<ExecRec> m_ready VL_GUARDED_BY(m_mutex);
    // Store the size atomically, so we can spin wait
    std::atomic<size_t> m_ready_size;
    // Fixed dispatch has one producer, and at most one outstanding invocation.
    // Keep its frequently written start signal away from queue bookkeeping.
    alignas(VL_CACHE_LINE_BYTES) std::atomic<VlFixedTask*> m_fixedTaskp{nullptr};
    alignas(VL_CACHE_LINE_BYTES) std::atomic<uint32_t> m_fixedUsers{0};
    // Expiration tells surviving tasks that their worker has been destroyed.
    const std::shared_ptr<FixedLifetime> m_fixedLifetime{std::make_shared<FixedLifetime>()};
    // Thread context
    VerilatedContext* const m_contextp;
    // Underlying thread record
#ifdef VL_USE_PTHREADS
    pthread_t m_pthread{};  // Worker thread handle
#else
    std::thread m_cthread;  // Worker thread handle
#endif

    // METHDOS
    static void* start(void*);  // Static entry point, invokes 'main'
    void main();  // 'main' loop of thread
    void retainFixed() VL_MT_SAFE_EXCLUDES(m_mutex);
    void releaseFixed() { m_fixedUsers.fetch_sub(1, std::memory_order_relaxed); }
    bool fixedWork(ExecRec* workp);

    VL_UNCOPYABLE(VlWorkerThread);

public:
    // CONSTRUCTORS
    explicit VlWorkerThread(VerilatedContext* contextp);
    ~VlWorkerThread();

    // METHODS
    template <bool N_SpinWait>
    void dequeWork(ExecRec* workp) VL_MT_SAFE_EXCLUDES(m_mutex) {
        // Fixed models keep their assigned workers polling. Registration wakes a
        // sleeping worker under the same mutex as the condition-variable wait.
        // Queue users still make progress between fixed invocations.
        while (true) {
            unsigned spins = 0;
            while (m_fixedUsers.load(std::memory_order_relaxed)) {
                if (fixedWork(workp)) return;
                if (m_ready_size.load(std::memory_order_relaxed)) break;
                VL_CPU_RELAX();
                if (++spins == VL_LOCK_SPINS) {
                    spins = 0;
                    std::this_thread::yield();
                }
            }
            // Spin for a while, waiting for new data
            if VL_CONSTEXPR_CXX17 (N_SpinWait) {
                for (unsigned i = 0; i < VL_LOCK_SPINS; ++i) {
                    if (VL_LIKELY(m_ready_size.load(std::memory_order_relaxed))
                        || m_fixedUsers.load(std::memory_order_relaxed))
                        break;
                    VL_CPU_RELAX();
                }
            }
            const VerilatedLockGuard lock{m_mutex};
            while (m_ready.empty() && !m_fixedUsers.load(std::memory_order_relaxed)) {
                m_waiting = true;
                m_cv.wait(m_mutex);
            }
            m_waiting = false;
            if (m_ready.empty()) continue;
            // As noted above this is inefficient if our ready list is ever
            // long (but it shouldn't be)
            *workp = m_ready.front();
            m_ready.erase(m_ready.begin());
            m_ready_size.fetch_sub(1, std::memory_order_relaxed);
            return;
        }
    }
    void addTask(VlExecFnp fnp, VlSelfP selfp) VL_MT_SAFE_EXCLUDES(m_mutex) {
        bool notify;
        {
            const VerilatedLockGuard lock{m_mutex};
            m_ready.emplace_back(fnp, selfp);
            m_ready_size.fetch_add(1, std::memory_order_relaxed);
            notify = m_waiting;
        }
        if (notify) m_cv.notify_one();
    }

    void shutdown();  // Finish current tasks, then terminate thread
    void wait();  // Blocks calling thread until all tasks complete in this thread
};

/// Model-owned, statically assigned worker entry point. The caller must join
/// each invocation before restarting or destroying it. Models sharing a pool
/// must evaluate sequentially, just as with the ordinary fixed worker schedule.
///
/// This is a single-producer start mailbox, not a completion object. start()
/// release-publishes the task and prior model writes; the worker acquire-loads
/// it, copies the invocation fields, and clears the mailbox before executing.
/// A cleared mailbox therefore does not mean the task has completed. Generated
/// code joins through the schedule's progress before reusing task fields or
/// destroying the model. The worker must not dereference this object after
/// publishing completion, since the caller can then release it immediately.
///
/// Fixed slots do not participate in the pool's ordinary worker reservations.
/// Generated dispatch uses the reservation/queue path when an enclosing ordinary
/// hierarchical schedule owns workers; concurrently nested models must not
/// configure or start conflicting fixed slots.
class alignas(VL_CACHE_LINE_BYTES) VlFixedTask final {
    friend class VlWorkerThread;
    VlWorkerThread* m_workerp = nullptr;  // Worker assigned to this fixed task
    std::weak_ptr<VlWorkerThread::FixedLifetime> m_workerLifetime;  // Does not keep the pool alive
    VlExecFnp m_fnp = nullptr;  // Function to execute on the assigned worker
    VlSelfP m_selfp = nullptr;  // Model instance passed to the task function

    VL_UNCOPYABLE(VlFixedTask);

public:
    VlFixedTask() = default;
    ~VlFixedTask() {
        // Pool teardown and task destruction are quiescent, never concurrent.
        if (!m_workerLifetime.expired()) m_workerp->releaseFixed();
    }
    /// Register once, before the first invocation. No task is executed here.
    void configure(VlWorkerThread* workerp, VlExecFnp fnp, VlSelfP selfp) {
        assert(!m_workerp && workerp && fnp);
        m_workerp = workerp;
        m_workerLifetime = workerp->m_fixedLifetime;
        m_fnp = fnp;
        m_selfp = selfp;
        m_workerp->retainFixed();
    }
    /// Forget a quiescent registration when its pool is discarded for cloning.
    /// Do not release the old worker: prepareClone() may already have freed it,
    /// or fork() may have left its synchronization objects owned by lost threads.
    /// The next evaluation must configure this task against the replacement pool.
    void resetForClone() {
        m_workerp = nullptr;
        m_workerLifetime.reset();
        m_fnp = nullptr;
        m_selfp = nullptr;
    }
    /// Release-publish a start signal; the worker acquires all caller input writes.
    void start() {
        assert(m_workerp && !m_workerp->m_fixedTaskp.load(std::memory_order_relaxed));
        m_workerp->m_fixedTaskp.store(this, std::memory_order_release);
    }
};

class VlThreadPool final : public VerilatedVirtualBase {
    // MEMBERS
    VerilatedContext* const m_contextp;  // Context for newly acquired workers
    std::vector<VlWorkerThread*> m_workers;  // Statically indexed simulation workers

    mutable VerilatedMutex m_mutex;  // Guards indexes of unassigned workers
    // Indexes of unassigned workers
    std::stack<size_t> m_unassignedWorkers VL_GUARDED_BY(m_mutex);
    // Ordinary hierarchical schedules reserve workers until their join. Fixed
    // kernels nested in those schedules must participate in the same allocation.
    std::atomic<size_t> m_reservedWorkers{0};
    // Workers for blocking calls, separate from the statically indexed simulation workers.
    // An acquired worker belongs to its caller until released back to the pool.
    std::vector<VlWorkerThread*> m_idleWorkers VL_GUARDED_BY(m_mutex);
    // For sequentially generating task IDs to avoid shadowing
    std::atomic<unsigned> m_assignedTasks{0};
    std::string m_numaStatus;  // Status of NUMA assignment

public:
    // CONSTRUCTORS
    // Construct a thread pool with 'nThreads' dedicated threads. The thread
    // pool will create these threads and make them available to execute tasks
    // via this->workerp(index)->addTask(...). Blocking calls acquire additional workers as needed.
    VlThreadPool(VerilatedContext* contextp, unsigned nThreads);
    ~VlThreadPool() override;

    // METHODS
    /// Acquire an exclusive worker for a blocking call, creating one if needed.
    VlWorkerThread* acquireWorker() VL_MT_SAFE_EXCLUDES(m_mutex);
    /// Return a worker after its blocking call has finished accessing the call's state.
    void releaseWorker(VlWorkerThread* workerp) VL_MT_SAFE_EXCLUDES(m_mutex);
    size_t assignWorkerIndex() {
        const VerilatedLockGuard lock{m_mutex};
        assert(!m_unassignedWorkers.empty());
        const size_t index = m_unassignedWorkers.top();
        m_unassignedWorkers.pop();
        m_reservedWorkers.fetch_add(1, std::memory_order_relaxed);
        return index;
    }
    void freeWorkerIndexes(std::vector<size_t>& indexes) {
        const VerilatedLockGuard lock{m_mutex};
        for (const size_t index : indexes) m_unassignedWorkers.push(index);
        m_reservedWorkers.fetch_sub(indexes.size(), std::memory_order_relaxed);
        indexes.clear();
    }
    /// True while an ordinary hierarchical schedule owns worker slots.
    bool hasWorkerReservations() const VL_MT_SAFE {
        return m_reservedWorkers.load(std::memory_order_relaxed) != 0;
    }
    unsigned assignTaskIndex() { return m_assignedTasks++; }
    int numThreads() const { return static_cast<int>(m_workers.size()); }
    std::string numaStatus() const { return m_numaStatus; }
    VlWorkerThread* workerp(int index) {
        assert(index >= 0);
        assert(index < static_cast<int>(m_workers.size()));
        return m_workers[index];
    }

private:
    VL_UNCOPYABLE(VlThreadPool);

    std::string numaAssign(VerilatedContext* contextp);
};

//=============================================================================
// VlExecGraph

#ifndef VL_THREADS_SERIAL_COST
// Evaluations with at most this estimated cost run on the calling thread, without waking others
#define VL_THREADS_SERIAL_COST 80000
#endif

// Static description of a multithreaded exec graph, emitted by Verilator
class VlExecGraph final {
public:
    // TYPES
    using Fnp = void (*)(VlSelfP);  // Function taking the model's root instance
    struct Vertex final {
        Fnp m_fnp;  // MTask body
        uint64_t m_staticCost;  // Static cost estimate
        const QData* m_maskp;  // Trigger bits the MTask tests, one word per trigger word
    };
    struct Edge final {
        uint32_t m_from;  // Index of the MTask that runs first
        uint32_t m_to;  // Index of the MTask that depends on it
    };

private:
    // MEMBERS
    const Vertex* const m_verticesp;  // MTasks, in a topological order
    const uint32_t m_nVertices;  // Number of MTasks
    const Edge* const m_edgesp;  // Dependencies between MTasks
    const uint32_t m_nEdges;  // Number of dependencies
    const size_t m_nTriggerWords;  // Number of trigger words for MTasks
    const IData* const m_triggerCostsp;  // Static cost of the logic each trigger guards
    const Fnp m_dispatchp;  // Runs the graph on the thread pool, as scheduled by Verilator
    const uint64_t m_serialCost;  // Total cost of set triggers' logic run on the caller

    VL_UNCOPYABLE(VlExecGraph);

public:
    // CONSTRUCTORS
    // constexpr, so the global graphs need no dynamic initialization, and can be used from
    // static constructors
    constexpr VlExecGraph(const Vertex* verticesp, uint32_t nVertices, const Edge* edgesp,
                          uint32_t nEdges, size_t nTriggerWords, const IData* triggerCostsp,
                          Fnp dispatchp, uint64_t serialCost)
        : m_verticesp{verticesp}
        , m_nVertices{nVertices}
        , m_edgesp{edgesp}
        , m_nEdges{nEdges}
        , m_nTriggerWords{nTriggerWords}
        , m_triggerCostsp{triggerCostsp}
        , m_dispatchp{dispatchp}
        , m_serialCost{serialCost} {}

    // ACCESSORS
    const Vertex* verticesp() const { return m_verticesp; }
    uint32_t nVertices() const { return m_nVertices; }
    const Edge* edgesp() const { return m_edgesp; }
    uint32_t nEdges() const { return m_nEdges; }
    size_t nTriggerWords() const { return m_nTriggerWords; }
    const IData* triggerCostsp() const { return m_triggerCostsp; }
    Fnp dispatchp() const { return m_dispatchp; }
    uint64_t serialCost() const { return m_serialCost; }
};

// Run 'graph' for the model's root instance 'selfp', when the trigger vector holds the
// words 'triggersp'. Only the thread evaluating the model may call this.
void vl_invokeExecGraph(VlExecGraph& graph, VlSelfP selfp, const QData* triggersp) VL_MT_UNSAFE;

#endif
