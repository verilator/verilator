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

#include "verilated_threads.h"

#include <condition_variable>
#include <functional>
#include <future>
#include <list>
#include <mutex>
#include <queue>
#include <thread>

//============================================================================

class V3ThreadPool;
// The global thread pool
extern V3ThreadPool v3ThreadPool;

class V3ThreadPool final {
    // MEMBERS
    using job_t = std::function<void()>;

    mutable VerilatedMutex m_mutex;  // Mutex for use by m_queue and m_cv
    std::queue<job_t> m_queue VL_GUARDED_BY(m_mutex);  // Queue of jobs
    std::condition_variable_any m_cv;  // Conditions to wake up workers
    std::list<std::thread> m_workers;  // Worker threads
    VerilatedMutex m_stoppedJobsMutex;  // Used to signal stopped jobs
    std::condition_variable_any
        m_stoppedJobsCV VL_GUARDED_BY(m_stoppedJobsMutex);  // Conditions to wake up stopped jobs
    std::atomic_uint m_stoppedJobs;  // currently stopped jobs waiting for wake up

    bool m_shutdown = false;  // Flag signalling termination

public:
    // CONSTRUCTORS
    V3ThreadPool()
        : m_stoppedJobs{0} {};
    ~V3ThreadPool() {
        VerilatedLockGuard lock{m_mutex};
        // make sure queue is empty
        while (!m_queue.empty()) m_queue.pop();
        lock.unlock();
        resize(0);
    }

    // METHODS
    // Resize thread pool to n workers (queue must be empty)
    void resize(unsigned n) VL_MT_UNSAFE;

    // Enqueue a job for asynchronous execution
    template <typename T>
    std::future<T> enqueue(std::function<T()>&& f) VL_MT_SAFE;

    // This function can be used to request exclusive access to processing.
    // It sends request to stop all other threads and waits for them to stop.
    // Other threads needs to manually call 'check_stop_requested' in places where
    // they can be stopped.
    // When all other threads are stopped, this function executes the job
    // and resumes execution of other jobs.
    void request_exclusive_access(job_t exclusive_access_job) VL_MT_SAFE {
        if (executeSynchronously()) {
            exclusive_access_job();
        } else {
            VerilatedLockGuard stoppedJobLock(m_stoppedJobsMutex);
            m_stoppedJobs++;
            m_cv.notify_all();
            m_stoppedJobsCV.wait(stoppedJobLock, [&]() VL_REQUIRES(m_stoppedJobsMutex) {
                return m_stoppedJobs == m_workers.size();
            });
            exclusive_access_job();
            m_stoppedJobs = 0;
            m_stoppedJobsCV.notify_all();
        }
    }

    // Similar to above function, but when function that requires exclusive access is behind mutex,
    // this function can also unlock it while it is waiting for other jobs and lock afterwards.
    // It can't be merged with above function due to limitations in clang thread-safety analysis.
    void request_exclusive_access(VerilatedMutex* locking, job_t exclusive_access_job) VL_MT_SAFE
        VL_REQUIRES(locking) {
        if (executeSynchronously()) {
            exclusive_access_job();
        } else {
            VerilatedLockGuard stoppedJobLock(m_stoppedJobsMutex);
            locking->unlock();
            m_stoppedJobs++;
            m_cv.notify_all();
            m_stoppedJobsCV.wait(stoppedJobLock, [&]() VL_REQUIRES(m_stoppedJobsMutex) {
                return m_stoppedJobs == m_workers.size();
            });
            locking->lock();
            exclusive_access_job();
            m_stoppedJobs = 0;
            m_stoppedJobsCV.notify_all();
        }
    }

    // This function can be used to check if other thread requested exclusive access to processing,
    // if so, it waits for it to complete. Afterwards it is resumed.
    void check_stop_requested() VL_MT_SAFE {
        VerilatedLockGuard stoppedJobLock(m_stoppedJobsMutex);
        if (m_shutdown || !m_stoppedJobs) return;
        m_stoppedJobs++;
        m_stoppedJobsCV.notify_all();
        m_stoppedJobsCV.wait(stoppedJobLock,
                             [&]() VL_REQUIRES(m_stoppedJobsMutex) { return m_stoppedJobs == 0; });
    }

    // Similar to above function, but when we checking function is behind mutex,
    // this function can also unlock it while it waits to be resumed.
    void check_stop_requested(VerilatedMutex* locking) VL_MT_SAFE VL_REQUIRES(locking) {
        VerilatedLockGuard stoppedJobLock(m_stoppedJobsMutex);
        if (m_shutdown || !m_stoppedJobs) return;
        locking->unlock();
        m_stoppedJobs++;
        m_stoppedJobsCV.notify_all();
        m_stoppedJobsCV.wait(stoppedJobLock,
                             [&]() VL_REQUIRES(m_stoppedJobsMutex) { return m_stoppedJobs == 0; });
        locking->lock();
    }

private:
    bool executeSynchronously() const VL_MT_SAFE { return m_workers.empty(); }

    template <typename T>
    void push_job(std::shared_ptr<std::promise<T>>& prom, std::function<T()>&& f) VL_MT_SAFE;

    void worker(int id) VL_MT_SAFE;

    static void startWorker(V3ThreadPool* selfp, int id) VL_MT_SAFE;
};

template <typename T>
std::future<T> V3ThreadPool::enqueue(std::function<T()>&& f) VL_MT_SAFE {
    std::shared_ptr<std::promise<T>> prom = std::make_shared<std::promise<T>>();
    std::future<T> result = prom->get_future();
    push_job(prom, std::move(f));
    m_cv.notify_one();
    return result;
}

template <typename T>
void V3ThreadPool::push_job(std::shared_ptr<std::promise<T>>& prom,
                            std::function<T()>&& f) VL_MT_SAFE {
    if (executeSynchronously()) {
        prom->set_value(f());
    } else {
        const VerilatedLockGuard guard{m_mutex};
        m_queue.push([prom, f] { prom->set_value(f()); });
    }
}

template <>
void V3ThreadPool::push_job<void>(std::shared_ptr<std::promise<void>>& prom,
                                  std::function<void()>&& f) VL_MT_SAFE;

#endif  // Guard
