// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Thread pool for Verilator itself
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// Copyright 2005-2024 by Wilson Snyder.  This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#include "V3ThreadPool.h"

#include "V3Error.h"
#include "V3Global.h"
#include "V3Mutex.h"

V3ThreadPool::V3ThreadPool(int numThreads) {
    numThreads = std::max(numThreads, 1);
    if (numThreads == 1) return;
    for (int i = 0; i < numThreads; ++i) {
        m_workers.emplace_back(&V3ThreadPool::startWorker, this);
    }
}

V3ThreadPool::~V3ThreadPool() {
    {
        const V3LockGuard lock{m_mutex};
        m_shutdown = true;
    }
    m_cv.notify_all();
    wait();
}

void V3ThreadPool::enqueue(std::function<void()>&& f) {
    if (m_workers.empty()) {
        f();
    } else {
        {
            const V3LockGuard lock{m_mutex};
            m_queue.push(std::move(f));
        }
        m_pendingJobs.fetch_add(1, std::memory_order_release);
        m_cv.notify_one();
    }
}

void V3ThreadPool::wait() {
    while (m_pendingJobs.load(std::memory_order_acquire) > 0 && !m_shutdown) {
        std::this_thread::yield();
    }
    if (m_shutdown) {
        for (auto& worker : m_workers) worker.join();
    }
}

void V3ThreadPool::startWorker(V3ThreadPool* selfThreadp) { selfThreadp->workerJobLoop(); }

void V3ThreadPool::workerJobLoop() {
    while (true) {
        std::function<void()> job;
        {
            // Locking before `condition_variable::wait` is required to ensure that the
            // `m_cv` condition will be executed under a lock. Taking a lock
            // before `condition_variable::wait` may lead to missed
            // `condition_variable::notify_all` notification (when a thread waits at the lock
            // before) but, according to C++ standard, the `condition_variable::wait` first checks
            // the condition and then waits for the notification, thus even when notification is
            // missed, the condition still will be checked.
            const V3LockGuard lock{m_mutex};
            m_cv.wait(m_mutex,
                      [&]() VL_REQUIRES(m_mutex) { return !m_queue.empty() || m_shutdown; });
            if (m_shutdown) return;  // Terminate if requested
            UASSERT(!m_queue.empty(), "Job should be available");
            if (m_queue.empty()) continue;
            job = std::move(m_queue.front());
            m_queue.pop();
        }
        job();
        m_pendingJobs.fetch_sub(1, std::memory_order_release);
    }
}

void V3ThreadPool::selfTestMtDisabled() {
    // empty
}

void V3ThreadPool::selfTest() {
    V3Mutex commonMutex;
    int commonValue{0};

    auto firstJob = [&](int sleep) -> void {
        std::this_thread::sleep_for(std::chrono::milliseconds{sleep});
        const V3LockGuard lock{commonMutex};
        commonValue = 10;
        std::this_thread::sleep_for(std::chrono::milliseconds{sleep + 10});
        UASSERT(commonValue == 10, "unexpected commonValue = " << commonValue);
    };
    auto secondJob = [&](int sleep) -> void {
        commonMutex.lock();
        commonMutex.unlock();
        V3LockGuard lock{commonMutex};
        std::this_thread::sleep_for(std::chrono::milliseconds{sleep});
        commonValue = 1000;
    };
    auto thirdJob = [&](int sleep) -> void {
        {
            V3LockGuard lock{commonMutex};
            std::this_thread::sleep_for(std::chrono::milliseconds{sleep});
        }
        firstJob(sleep);
        V3LockGuard lock{commonMutex};
        commonValue = 100;
    };
    {
        V3ThreadScope scope;

        scope.enqueue(std::bind(firstJob, 100));
        scope.enqueue(std::bind(secondJob, 100));
        scope.enqueue(std::bind(firstJob, 100));
        scope.enqueue(std::bind(secondJob, 100));
        scope.enqueue(std::bind(secondJob, 200));
        scope.enqueue(std::bind(firstJob, 200));
        scope.enqueue(std::bind(firstJob, 300));
        scope.wait();

        UASSERT(commonValue == 1000 || commonValue == 10,
                "unexpected common value = " << commonValue);

        scope.enqueue(std::bind(thirdJob, 100));
        scope.enqueue(std::bind(thirdJob, 100));
    }

    UASSERT(commonValue == 100, "unexpected common value = " << commonValue);

    {
        V3ThreadScope scope;
        scope.enqueue(std::bind(firstJob, 100));
    }

    UASSERT(commonValue == 10, "unexpected common value = " << commonValue);

    {
        int result = 0;
        auto forthJob = [&]() -> void { result = 1234; };

        V3ThreadScope scope;
        scope.enqueue(forthJob);
        scope.wait();
        UASSERT(result == 1234, "unexpected job result = " << result);
    }
    selfTestMtDisabled();
}

V3ThreadScope::V3ThreadScope() {
    UASSERT(v3Global.threadPoolp(), "ThreadPool must be initialized before ThreadScope.");
    m_pool = v3Global.threadPoolp();
    wait();
}

void V3ThreadScope::enqueue(std::function<void()>&& f) { m_pool->enqueue(std::move(f)); }

void V3ThreadScope::wait() { m_pool->wait(); }
