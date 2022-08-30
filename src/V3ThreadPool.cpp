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

// The global thread pool
V3ThreadPool v3ThreadPool;

void V3ThreadPool::resize(unsigned n) VL_MT_UNSAFE {
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
    for (unsigned int i = 1; i < n; i++) {
        m_workers.emplace_back(&V3ThreadPool::startWorker, this, i);
    }
}

void V3ThreadPool::startWorker(V3ThreadPool* selfp, int id) VL_MT_SAFE { selfp->worker(id); }

void V3ThreadPool::worker(int id) VL_MT_SAFE {
    while (true) {
        // Wait for a notification
        job_t job;
        {
            VerilatedLockGuard lock(m_mutex);
            m_cv.wait(lock, [&]() VL_REQUIRES(m_mutex) {
                return !m_queue.empty() || m_shutdown || m_stoppedJobs;
            });

            // Terminate if requested
            if (m_shutdown) return;

            if (m_stoppedJobs) {
                check_stop_requested(&m_mutex);
                continue;
            }

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
void V3ThreadPool::push_job<void>(std::shared_ptr<std::promise<void>>& prom,
                                  std::function<void()>&& f) VL_MT_SAFE {
    if (executeSynchronously()) {
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
