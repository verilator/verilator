// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Thread pool for Verilator itself
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2005-2023 by Wilson Snyder.  This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#ifndef _V3THREADPOOL_H_
#define _V3THREADPOOL_H_ 1

#include "V3Mutex.h"

#include <condition_variable>
#include <functional>
#include <future>
#include <list>
#include <mutex>
#include <queue>
#include <thread>

//============================================================================

class V3ThreadPool final {
    // MEMBERS
    static constexpr unsigned int FUTUREWAITFOR_MS = 100;
    using job_t = std::function<void()>;

    mutable V3Mutex m_mutex;  // Mutex for use by m_queue
    std::queue<job_t> m_queue VL_GUARDED_BY(m_mutex);  // Queue of jobs
    // We don't need to guard this condition_variable as
    // both `notify_one` and `notify_all` functions are atomic,
    // `wait` function is not atomic, but we are guarding `m_queue` that is
    // used by this condition_variable, so clang checks that we have mutex locked
    std::condition_variable_any m_cv;  // Conditions to wake up workers
    std::list<std::thread> m_workers;  // Worker threads
    V3Mutex m_stoppedJobsMutex;  // Used to signal stopped jobs
    // Conditions to wake up stopped jobs
    std::condition_variable_any m_stoppedJobsCV VL_GUARDED_BY(m_stoppedJobsMutex);
    std::atomic_uint m_stoppedJobs{0};  // Currently stopped jobs waiting for wake up
    std::atomic_bool m_stopRequested{false};  // Signals to resume stopped jobs
    std::atomic_bool m_exclusiveAccess{false};  // Signals that all other threads are stopped

    std::atomic_bool m_shutdown{false};  // Termination pending

    // CONSTRUCTORS
    V3ThreadPool() = default;
    ~V3ThreadPool() {
        {
            V3LockGuard lock{m_mutex};
            m_queue = {};  // make sure queue is empty
        }
        resize(0);
    }

public:
    // METHODS
    // Singleton
    static V3ThreadPool& s() VL_MT_SAFE {
        static V3ThreadPool s_s;
        return s_s;
    }

    // Resize thread pool to n workers (queue must be empty)
    void resize(unsigned n) VL_MT_UNSAFE VL_EXCLUDES(m_mutex) VL_EXCLUDES(m_stoppedJobsMutex);

    // Enqueue a job for asynchronous execution
    // Due to missing support for lambda annotations in c++11,
    // `clang_check_attributes` script assumes that if
    // function takes `std::function` as argument, it
    // will call it. `VL_MT_START` here indicates that
    // every function call inside this `std::function` requires
    // annotations.
    template <typename T>
    std::future<T> enqueue(std::function<T()>&& f) VL_MT_START;

    // Request exclusive access to processing.
    // It sends request to stop all other threads and waits for them to stop.
    // Other threads needs to manually call 'check_stop_requested' in places where
    // they can be stopped.
    // When all other threads are stopped, this function executes the job
    // and resumes execution of other jobs.
    void requestExclusiveAccess(const job_t&& exclusiveAccessJob) VL_MT_SAFE;

    // Check if other thread requested exclusive access to processing,
    // if so, it waits for it to complete. Afterwards it is resumed.
    // Returns true if request was send and we waited, otherwise false
    bool waitIfStopRequested() VL_MT_SAFE VL_EXCLUDES(m_stoppedJobsMutex);

    // Waits for future.
    // This function can be interupted by exclusive access request.
    // When other thread requested exclusive access to processing,
    // current thread is stopped and waits until it is resumed.
    // Returns future result
    template <typename T>
    static T waitForFuture(std::future<T>& future) VL_MT_SAFE_EXCLUDES(m_mutex);

    // Waits for list of futures
    // This function can be interupted by exclusive access request.
    // When other thread requested exclusive access to processing,
    // current thread is stopped and waits until it is resumed.
    // This function uses function overload instead of template
    // specialization as C++11 requires them to be inside namespace scope
    // Returns list of future result or void
    template <typename T>
    static auto waitForFutures(std::list<std::future<T>>& futures) {
        return waitForFuturesImp(futures);
    }

    static void selfTest();

private:
    template <typename T>
    static std::list<T> waitForFuturesImp(std::list<std::future<T>>& futures) {
        std::list<T> results;
        while (!futures.empty()) {
            results.push_back(V3ThreadPool::waitForFuture(futures.front()));
            futures.pop_front();
        }
        return results;
    }

    static void waitForFuturesImp(std::list<std::future<void>>& futures) {
        while (!futures.empty()) {
            V3ThreadPool::waitForFuture(futures.front());
            futures.pop_front();
        }
    }
    bool willExecuteSynchronously() const VL_MT_SAFE {
        return m_workers.empty() || m_exclusiveAccess;
    }

    // True when any thread requested exclusive access
    bool stopRequested() const VL_MT_SAFE {
        // don't wait if shutdown already requested
        if (m_shutdown) return false;
        return m_stopRequested;
    }

    // Waits until exclusive access job completes its job
    void waitStopRequested() VL_REQUIRES(m_stoppedJobsMutex);

    // Waits until all other jobs are stopped
    void waitOtherThreads() VL_MT_SAFE_EXCLUDES(m_mutex) VL_REQUIRES(m_stoppedJobsMutex);

    template <typename T>
    void pushJob(std::shared_ptr<std::promise<T>>& prom, std::function<T()>&& f) VL_MT_SAFE;

    void workerJobLoop(int id) VL_MT_SAFE;

    static void startWorker(V3ThreadPool* selfThreadp, int id) VL_MT_SAFE;
};

template <typename T>
T V3ThreadPool::waitForFuture(std::future<T>& future) VL_MT_SAFE_EXCLUDES(m_mutex) {
    while (true) {
        V3ThreadPool::s().waitIfStopRequested();
        {
            std::future_status status
                = future.wait_for(std::chrono::milliseconds(V3ThreadPool::FUTUREWAITFOR_MS));
            switch (status) {
            case std::future_status::deferred: continue;
            case std::future_status::timeout: continue;
            case std::future_status::ready: return future.get();
            }
        }
    }
}

template <typename T>
std::future<T> V3ThreadPool::enqueue(std::function<T()>&& f) VL_MT_START {
    std::shared_ptr<std::promise<T>> prom = std::make_shared<std::promise<T>>();
    std::future<T> result = prom->get_future();
    pushJob(prom, std::move(f));
    const V3LockGuard guard{m_mutex};
    m_cv.notify_one();
    return result;
}

template <typename T>
void V3ThreadPool::pushJob(std::shared_ptr<std::promise<T>>& prom,
                           std::function<T()>&& f) VL_MT_SAFE {
    if (willExecuteSynchronously()) {
        prom->set_value(f());
    } else {
        const V3LockGuard guard{m_mutex};
        m_queue.push([prom, f] { prom->set_value(f()); });
    }
}

template <>
void V3ThreadPool::pushJob<void>(std::shared_ptr<std::promise<void>>& prom,
                                 std::function<void()>&& f) VL_MT_SAFE;

#endif  // Guard
