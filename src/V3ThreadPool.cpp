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

void V3ThreadPool::resize(unsigned n) VL_MT_UNSAFE VL_EXCLUDES(m_mutex)
    VL_EXCLUDES(m_stoppedJobsMutex) {
    // This function is not thread-safe and can result in race between threads
    UASSERT(V3MutexConfig::s().lockConfig(),
            "Mutex config needs to be locked before starting ThreadPool");
    {
        V3LockGuard lock{m_mutex};
        V3LockGuard stoppedJobsLock{m_stoppedJobsMutex};

        UASSERT(m_queue.empty(), "Resizing busy thread pool");
        // Shut down old threads
        m_shutdown = true;
        m_stoppedJobs = 0;
        m_cv.notify_all();
        m_stoppedJobsCV.notify_all();
    }
    while (!m_workers.empty()) {
        m_workers.front().join();
        m_workers.pop_front();
    }
    if (n > 1) {
        V3LockGuard lock{m_mutex};
        // Start new threads
        m_shutdown = false;
        for (unsigned int i = 1; i < n; ++i) {
            m_workers.emplace_back(&V3ThreadPool::startWorker, this, i);
        }
    }
}

void V3ThreadPool::startWorker(V3ThreadPool* selfThreadp, int id) VL_MT_SAFE {
    selfThreadp->workerJobLoop(id);
}

void V3ThreadPool::workerJobLoop(int id) VL_MT_SAFE {
    while (true) {
        // Wait for a notification
        waitIfStopRequested();
        VAnyPackagedTask job;
        {
            V3LockGuard lock(m_mutex);
            m_cv.wait(m_mutex, [&]() VL_REQUIRES(m_mutex) {
                return !m_queue.empty() || m_shutdown || m_stopRequested;
            });
            if (m_shutdown) return;  // Terminate if requested
            if (stopRequested()) { continue; }
            // Get the job
            UASSERT(!m_queue.empty(), "Job should be available");

            job = std::move(m_queue.front());
            m_queue.pop();
        }

        // Execute the job
        job();
    }
}

bool V3ThreadPool::waitIfStopRequested() VL_MT_SAFE VL_EXCLUDES(m_stoppedJobsMutex) {
    if (!stopRequested()) return false;
    V3LockGuard stoppedJobLock(m_stoppedJobsMutex);
    waitForResumeRequest();
    return true;
}

void V3ThreadPool::waitForResumeRequest() VL_REQUIRES(m_stoppedJobsMutex) {
    ++m_stoppedJobs;
    m_stoppedJobsCV.notify_all();
    m_stoppedJobsCV.wait(m_stoppedJobsMutex, [&]() VL_REQUIRES(m_stoppedJobsMutex) {
        return !m_stopRequested.load();
    });
    --m_stoppedJobs;
    m_stoppedJobsCV.notify_all();
}

void V3ThreadPool::stopOtherThreads() VL_MT_SAFE_EXCLUDES(m_mutex)
    VL_REQUIRES(m_stoppedJobsMutex) {
    m_stopRequested = true;
    ++m_stoppedJobs;
    m_stoppedJobsCV.notify_all();
    m_cv.notify_all();
    m_stoppedJobsCV.wait(m_stoppedJobsMutex, [&]() VL_REQUIRES(m_stoppedJobsMutex) {
        // count also the main thread
        return m_stoppedJobs == (m_workers.size() + 1);
    });
    --m_stoppedJobs;
}

void V3ThreadPool::selfTest() {
    V3Mutex commonMutex;
    int commonValue{0};

    auto firstJob = [&](int sleep) -> void {
        std::this_thread::sleep_for(std::chrono::milliseconds{sleep});
        const V3ThreadPool::ScopedExclusiveAccess exclusiveAccess;
        commonValue = 10;
        std::this_thread::sleep_for(std::chrono::milliseconds{sleep + 10});
        UASSERT(commonValue == 10, "unexpected commonValue = " << commonValue);
    };
    auto secondJob = [&](int sleep) -> void {
        commonMutex.lock();
        commonMutex.unlock();
        s().waitIfStopRequested();
        V3LockGuard lock{commonMutex};
        std::this_thread::sleep_for(std::chrono::milliseconds{sleep});
        commonValue = 1000;
    };
    auto thirdJob = [&](int sleep) -> void {
        {
            V3LockGuard lock{commonMutex};
            std::this_thread::sleep_for(std::chrono::milliseconds{sleep});
        }
        s().requestExclusiveAccess([&]() { firstJob(sleep); });
        V3LockGuard lock{commonMutex};
        commonValue = 1000;
    };
    std::list<std::future<void>> futures;

    futures.push_back(s().enqueue(std::bind(firstJob, 100)));
    futures.push_back(s().enqueue(std::bind(secondJob, 100)));
    futures.push_back(s().enqueue(std::bind(firstJob, 100)));
    futures.push_back(s().enqueue(std::bind(secondJob, 100)));
    futures.push_back(s().enqueue(std::bind(secondJob, 200)));
    futures.push_back(s().enqueue(std::bind(firstJob, 200)));
    futures.push_back(s().enqueue(std::bind(firstJob, 300)));
    while (!futures.empty()) {
        s().waitForFuture(futures.front());
        futures.pop_front();
    }
    futures.push_back(s().enqueue(std::bind(thirdJob, 100)));
    futures.push_back(s().enqueue(std::bind(thirdJob, 100)));
    V3ThreadPool::waitForFutures(futures);

    s().waitIfStopRequested();
    s().requestExclusiveAccess(std::bind(firstJob, 100));

    auto forthJob = [&]() -> int { return 1234; };
    std::list<std::future<int>> futuresInt;
    futuresInt.push_back(s().enqueue(forthJob));
    auto result = V3ThreadPool::waitForFutures(futuresInt);
    UASSERT(result.back() == 1234, "unexpected future result = " << result.back());
}

V3MtDisabledLock V3MtDisabledLock::s_mtDisabledLock;
