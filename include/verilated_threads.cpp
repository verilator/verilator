// -*- mode: C++; c-file-style: "cc-mode" -*-
//=============================================================================
//
// Copyright 2012-2020 by Wilson Snyder. This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//=============================================================================
///
/// \file
/// \brief Thread pool for verilated modules
///
//=============================================================================

#include "verilatedos.h"
#include "verilated_threads.h"

#include <cstdio>

std::atomic<vluint64_t> VlMTaskVertex::s_yields;

VL_THREAD_LOCAL VlThreadPool::ProfileTrace* VlThreadPool::t_profilep = NULL;

//=============================================================================
// VlMTaskVertex

VlMTaskVertex::VlMTaskVertex(vluint32_t upstreamDepCount)
    : m_upstreamDepsDone(0),
      m_upstreamDepCount(upstreamDepCount) {
    assert(atomic_is_lock_free(&m_upstreamDepsDone));
}

//=============================================================================
// VlWorkerThread

VlWorkerThread::VlWorkerThread(VlThreadPool* poolp, bool profiling)
    : m_ready_size(0)
    , m_poolp(poolp)
    , m_profiling(profiling)
    , m_exiting(false)
      // Must init this last -- after setting up fields that it might read:
    , m_cthread(startWorker, this) {}

VlWorkerThread::~VlWorkerThread() {
    m_exiting.store(true, std::memory_order_release);
    wakeUp();
    // The thread should exit; join it.
    m_cthread.join();
}

void VlWorkerThread::workerLoop() {
    if (VL_UNLIKELY(m_profiling)) {
        m_poolp->setupProfilingClientThread();
    }

    ExecRec work;
    work.m_fnp = NULL;

    while (1) {
        if (VL_LIKELY(!work.m_fnp)) {
            dequeWork(&work);
        }

        // Do this here, not above, to avoid a race with the destructor.
        if (VL_UNLIKELY(m_exiting.load(std::memory_order_acquire)))
            break;

        if (VL_LIKELY(work.m_fnp)) {
            work.m_fnp(work.m_evenCycle, work.m_sym);
            work.m_fnp = NULL;
        }
    }

    if (VL_UNLIKELY(m_profiling)) {
        m_poolp->tearDownProfilingClientThread();
    }
}

void VlWorkerThread::startWorker(VlWorkerThread* workerp) {
    workerp->workerLoop();
}

//=============================================================================
// VlThreadPool

VlThreadPool::VlThreadPool(int nThreads, bool profiling)
    : m_profiling(profiling) {
    // --threads N passes nThreads=N-1, as the "main" threads counts as 1
    unsigned cpus = std::thread::hardware_concurrency();
    if (cpus < nThreads+1) {
        static int warnedOnce = 0;
        if (!warnedOnce++) {
            VL_PRINTF_MT("%%Warning: System has %u CPUs but model Verilated with"
                         " --threads %d; may run slow.\n", cpus, nThreads+1);
        }
    }
    // Create'em
    for (int i=0; i<nThreads; ++i) {
        m_workers.push_back(new VlWorkerThread(this, profiling));
    }
    // Set up a profile buffer for the current thread too -- on the
    // assumption that it's the same thread that calls eval and may be
    // donated to run mtasks during the eval.
    if (VL_UNLIKELY(m_profiling)) {
        setupProfilingClientThread();
    }
}

VlThreadPool::~VlThreadPool() {
    for (int i = 0; i < m_workers.size(); ++i) {
        // Each ~WorkerThread will wait for its thread to exit.
        delete m_workers[i];
    }
    if (VL_UNLIKELY(m_profiling)) {
        tearDownProfilingClientThread();
    }
}

void VlThreadPool::tearDownProfilingClientThread() {
    assert(t_profilep);
    delete t_profilep;
    t_profilep = NULL;
}

void VlThreadPool::setupProfilingClientThread() {
    assert(!t_profilep);
    t_profilep = new ProfileTrace;
    // Reserve some space in the thread-local profiling buffer;
    // try not to malloc while collecting profiling.
    t_profilep->reserve(4096);
    {
        VerilatedLockGuard lk(m_mutex);
        m_allProfiles.insert(t_profilep);
    }
}

void VlThreadPool::profileAppendAll(const VlProfileRec& rec) {
    VerilatedLockGuard lk(m_mutex);
    for (ProfileSet::iterator it = m_allProfiles.begin();
         it != m_allProfiles.end(); ++it) {
        // Every thread's profile trace gets a copy of rec.
        (*it)->emplace_back(rec);
    }
}

void VlThreadPool::profileDump(const char* filenamep, vluint64_t ticksElapsed) {
    VerilatedLockGuard lk(m_mutex);
    VL_DEBUG_IF(VL_DBG_MSGF("+prof+threads writing to '%s'\n", filenamep););

    FILE* fp = fopen(filenamep, "w");
    if (VL_UNLIKELY(!fp)) {
        VL_FATAL_MT(filenamep, 0, "", "+prof+threads+file file not writable");
        return;
    }

    // TODO Perhaps merge with verilated_coverage output format, so can
    // have a common merging and reporting tool, etc.
    fprintf(fp, "VLPROFTHREAD 1.0 # Verilator thread profile dump version 1.0\n");
    fprintf(fp, "VLPROF arg --threads %" VL_PRI64 "u\n",
            vluint64_t(m_workers.size()+1));
    fprintf(fp, "VLPROF arg +verilator+prof+threads+start+%" VL_PRI64 "u\n",
            Verilated::profThreadsStart());
    fprintf(fp, "VLPROF arg +verilator+prof+threads+window+%u\n",
            Verilated::profThreadsWindow());
    fprintf(fp, "VLPROF stat yields %" VL_PRI64 "u\n",
            VlMTaskVertex::yields());

    vluint32_t thread_id = 0;
    for (ProfileSet::const_iterator pit = m_allProfiles.begin();
         pit != m_allProfiles.end(); ++pit) {
        ++thread_id;

        bool printing = false;  // False while in warmup phase
        for (ProfileTrace::const_iterator eit = (*pit)->begin();
             eit != (*pit)->end(); ++eit) {
            switch (eit->m_type) {
            case VlProfileRec::TYPE_BARRIER:
                printing = true;
                break;
            case VlProfileRec::TYPE_MTASK_RUN:
                if (!printing) break;
                fprintf(fp, "VLPROF mtask %d"
                        " start %" VL_PRI64"u end %" VL_PRI64"u elapsed %" VL_PRI64 "u"
                        " predict_time %u cpu %u on thread %u\n",
                        eit->m_mtaskId,
                        eit->m_startTime,
                        eit->m_endTime,
                        (eit->m_endTime - eit->m_startTime),
                        eit->m_predictTime,
                        eit->m_cpu,
                        thread_id);
                break;
            default: assert(false); break;  // LCOV_EXCL_LINE
            }
        }
    }
    fprintf(fp, "VLPROF stat ticks %" VL_PRI64 "u\n",
            ticksElapsed);

    fclose(fp);
}
