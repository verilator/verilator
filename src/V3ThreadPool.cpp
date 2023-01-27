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

#include "config_build.h"

#include "V3ThreadPool.h"

#include "V3Error.h"

// c++11 requires definition of static constexpr as well as declaration
constexpr unsigned int V3ThreadPool::FUTUREWAITFOR_MS;

void V3ThreadPool::resize(unsigned n) VL_MT_UNSAFE {
    // This function is not thread-safe and can result in race between threads
    VerilatedLockGuard lock{m_mutex};
    VerilatedLockGuard stoppedJobsLock{m_stoppedJobsMutex};
    UASSERT(m_queue.empty(), "Resizing busy thread pool");
    // Shut down old threads
    m_shutdown = true;
    m_stoppedJobs = 0;
    m_cv.notify_all();
    m_stoppedJobsCV.notify_all();
    stoppedJobsLock.unlock();
    lock.unlock();
    while (!m_workers.empty()) {
        m_workers.front().join();
        m_workers.pop_front();
    }
    lock.lock();
    // Start new threads
    m_shutdown = false;
    for (unsigned int i = 1; i < n; ++i) {
        m_workers.emplace_back(&V3ThreadPool::startWorker, this, i);
    }
}

void V3ThreadPool::startWorker(V3ThreadPool* selfThreadp, int id) VL_MT_SAFE {
    selfThreadp->workerJobLoop(id);
}

void V3ThreadPool::workerJobLoop(int id) VL_MT_SAFE {
    while (true) {
        // Wait for a notification
        waitIfStopRequested();
        job_t job;
        {
            VerilatedLockGuard lock(m_mutex);
            m_cv.wait(lock, [&]() VL_REQUIRES(m_mutex) {
                return !m_queue.empty() || m_shutdown || m_stopRequested;
            });
            if (m_shutdown) return;  // Terminate if requested
            if (stopRequestedStandalone()) { continue; }
            // Get the job
            UASSERT(!m_queue.empty(), "Job should be available");

            job = m_queue.front();
            m_queue.pop();
        }

        // Execute the job
        job();
    }
}

template <>
void V3ThreadPool::pushJob<void>(std::shared_ptr<std::promise<void>>& prom,
                                 std::function<void()>&& f) VL_MT_SAFE {
    if (willExecuteSynchronously()) {
        f();
        prom->set_value();
    } else {
        const VerilatedLockGuard lock{m_mutex};
        m_queue.push([prom, f] {
            f();
            prom->set_value();
        });
    }
}

void V3ThreadPool::requestExclusiveAccess(const V3ThreadPool::job_t&& exclusiveAccessJob)
    VL_MT_SAFE {
    if (willExecuteSynchronously()) {
        exclusiveAccessJob();
    } else {
        VerilatedLockGuard stoppedJobLock{m_stoppedJobsMutex};
        // if some other job already requested exclusive access
        // wait until it stops
        if (stopRequested()) { waitStopRequested(stoppedJobLock); }
        m_stopRequested = true;
        waitOtherThreads(stoppedJobLock);
        m_exclusiveAccess = true;
        exclusiveAccessJob();
        m_exclusiveAccess = false;
        m_stopRequested = false;
        m_stoppedJobsCV.notify_all();
    }
}

bool V3ThreadPool::waitIfStopRequested() VL_MT_SAFE {
    VerilatedLockGuard stoppedJobLock(m_stoppedJobsMutex);
    if (!stopRequested()) return false;
    waitStopRequested(stoppedJobLock);
    return true;
}

void V3ThreadPool::waitStopRequested(VerilatedLockGuard& stoppedJobLock)
    VL_REQUIRES(m_stoppedJobsMutex) {
    ++m_stoppedJobs;
    m_stoppedJobsCV.notify_all();
    m_stoppedJobsCV.wait(
        stoppedJobLock, [&]() VL_REQUIRES(m_stoppedJobsMutex) { return !m_stopRequested.load(); });
    --m_stoppedJobs;
    m_stoppedJobsCV.notify_all();
}

void V3ThreadPool::waitOtherThreads(VerilatedLockGuard& stoppedJobLock)
    VL_MT_SAFE_EXCLUDES(m_mutex) VL_REQUIRES(m_stoppedJobsMutex) {
    ++m_stoppedJobs;
    m_stoppedJobsCV.notify_all();
    m_cv.notify_all();
    m_stoppedJobsCV.wait(stoppedJobLock, [&]() VL_REQUIRES(m_stoppedJobsMutex) {
        // count also the main thread
        return m_stoppedJobs == (m_workers.size() + 1);
    });
    --m_stoppedJobs;
}

void V3ThreadPool::selfTest() {
    VerilatedMutex commonMutex;
    int commonValue{0};

    auto firstJob = [&](int sleep) -> void {
        std::this_thread::sleep_for(std::chrono::milliseconds{sleep});
        s().requestExclusiveAccess([&]() {
            commonValue = 10;
            std::this_thread::sleep_for(std::chrono::milliseconds{sleep + 10});
            UASSERT(commonValue == 10, "unexpected commonValue = " << commonValue);
        });
    };
    auto secondJob = [&](int sleep) -> void {
        VerilatedLockGuard lock{commonMutex};
        lock.unlock();
        s().waitIfStopRequested();
        lock.lock();
        std::this_thread::sleep_for(std::chrono::milliseconds{sleep});
        commonValue = 1000;
    };
    auto thirdJob = [&](int sleep) -> void {
        VerilatedLockGuard lock{commonMutex};
        std::this_thread::sleep_for(std::chrono::milliseconds{sleep});
        lock.unlock();
        s().requestExclusiveAccess([&]() { firstJob(sleep); });
        lock.lock();
        commonValue = 1000;
    };
    std::list<std::future<void>> futures;

    futures.push_back(s().enqueue<void>(std::bind(firstJob, 100)));
    futures.push_back(s().enqueue<void>(std::bind(secondJob, 100)));
    futures.push_back(s().enqueue<void>(std::bind(firstJob, 100)));
    futures.push_back(s().enqueue<void>(std::bind(secondJob, 100)));
    futures.push_back(s().enqueue<void>(std::bind(secondJob, 200)));
    futures.push_back(s().enqueue<void>(std::bind(firstJob, 200)));
    futures.push_back(s().enqueue<void>(std::bind(firstJob, 300)));
    while (!futures.empty()) {
        s().waitForFuture(futures.front());
        futures.pop_front();
    }
    futures.push_back(s().enqueue<void>(std::bind(thirdJob, 100)));
    futures.push_back(s().enqueue<void>(std::bind(thirdJob, 100)));
    while (!futures.empty()) {
        s().waitForFuture(futures.front());
        futures.pop_front();
    }
    s().waitIfStopRequested();
    s().requestExclusiveAccess(std::bind(firstJob, 100));
    auto forthJob = [&]() -> int { return 1234; };
    std::list<std::future<int>> futuresInt;
    futuresInt.push_back(s().enqueue<int>(forthJob));
    while (!futuresInt.empty()) {
        int result = s().waitForFuture(futuresInt.front());
        UASSERT(result == 1234, "unexpected future result = " << commonValue);
        futuresInt.pop_front();
    }
}
