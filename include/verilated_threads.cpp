// -*- mode: C++; c-file-style: "cc-mode" -*-
//=============================================================================
//
// Code available from: https://verilator.org
//
// Copyright 2012-2021 by Wilson Snyder. This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//=============================================================================
///
/// \file
/// \brief Verilated thread pool implementation code
///
/// This file must be compiled and linked against all Verilated objects
/// that use --threads.
///
/// Use "verilator --threads" to add this to the Makefile for the linker.
///
//=============================================================================

#include "verilatedos.h"
#include "verilated_threads.h"

#include <cstdio>
#include <fstream>

//=============================================================================
// Globals

// Internal note: Globals may multi-construct, see verilated.cpp top.

std::atomic<vluint64_t> VlMTaskVertex::s_yields;

VL_THREAD_LOCAL VlThreadPool::ProfileTrace* VlThreadPool::t_profilep = nullptr;

//=============================================================================
// VlMTaskVertex

VlMTaskVertex::VlMTaskVertex(vluint32_t upstreamDepCount)
    : m_upstreamDepsDone{0}
    , m_upstreamDepCount{upstreamDepCount} {
    assert(atomic_is_lock_free(&m_upstreamDepsDone));
}

//=============================================================================
// VlWorkerThread

VlWorkerThread::VlWorkerThread(VlThreadPool* poolp, VerilatedContext* contextp, bool profiling)
    : m_ready_size{0}
    , m_poolp{poolp}
    , m_profiling{profiling}  // Must init this last -- after setting up fields that it might read:
    , m_exiting{false}
    , m_cthread{startWorker, this}
    , m_contextp{contextp} {}

VlWorkerThread::~VlWorkerThread() {
    m_exiting.store(true, std::memory_order_release);
    wakeUp();
    // The thread should exit; join it.
    m_cthread.join();
}

void VlWorkerThread::workerLoop() {
    if (VL_UNLIKELY(m_profiling)) m_poolp->setupProfilingClientThread();

    ExecRec work;
    work.m_fnp = nullptr;

    while (true) {
        if (VL_LIKELY(!work.m_fnp)) dequeWork(&work);

        // Do this here, not above, to avoid a race with the destructor.
        if (VL_UNLIKELY(m_exiting.load(std::memory_order_acquire))) break;

        if (VL_LIKELY(work.m_fnp)) {
            work.m_fnp(work.m_selfp, work.m_evenCycle);
            work.m_fnp = nullptr;
        }
    }

    if (VL_UNLIKELY(m_profiling)) m_poolp->tearDownProfilingClientThread();
}

void VlWorkerThread::startWorker(VlWorkerThread* workerp) {
    Verilated::threadContextp(workerp->m_contextp);
    workerp->workerLoop();
}

//=============================================================================
// VlThreadPool

VlThreadPool::VlThreadPool(VerilatedContext* contextp, int nThreads, bool profiling)
    : m_profiling{profiling} {
    // --threads N passes nThreads=N-1, as the "main" threads counts as 1
    const unsigned cpus = std::thread::hardware_concurrency();
    if (cpus < nThreads + 1) {
        static int warnedOnce = 0;
        if (!warnedOnce++) {
            VL_PRINTF_MT("%%Warning: System has %u CPUs but model Verilated with"
                         " --threads %d; may run slow.\n",
                         cpus, nThreads + 1);
        }
    }
    // Create'em
    for (int i = 0; i < nThreads; ++i) {
        m_workers.push_back(new VlWorkerThread{this, contextp, profiling});
    }
    // Set up a profile buffer for the current thread too -- on the
    // assumption that it's the same thread that calls eval and may be
    // donated to run mtasks during the eval.
    if (VL_UNLIKELY(m_profiling)) setupProfilingClientThread();
}

VlThreadPool::~VlThreadPool() {
    // Each ~WorkerThread will wait for its thread to exit.
    for (auto& i : m_workers) delete i;
    if (VL_UNLIKELY(m_profiling)) tearDownProfilingClientThread();
}

void VlThreadPool::tearDownProfilingClientThread() {
    assert(t_profilep);
    delete t_profilep;
    t_profilep = nullptr;
}

void VlThreadPool::setupProfilingClientThread() VL_MT_SAFE_EXCLUDES(m_mutex) {
    assert(!t_profilep);
    t_profilep = new ProfileTrace;
    // Reserve some space in the thread-local profiling buffer;
    // try not to malloc while collecting profiling.
    t_profilep->reserve(4096);
    {
        const VerilatedLockGuard lock{m_mutex};
        m_allProfiles.insert(t_profilep);
    }
}

void VlThreadPool::profileAppendAll(const VlProfileRec& rec) VL_MT_SAFE_EXCLUDES(m_mutex) {
    const VerilatedLockGuard lock{m_mutex};
    for (const auto& profilep : m_allProfiles) {
        // Every thread's profile trace gets a copy of rec.
        profilep->emplace_back(rec);
    }
}

void VlThreadPool::profileDump(const char* filenamep, vluint64_t tickStart, vluint64_t tickEnd)
    VL_MT_SAFE_EXCLUDES(m_mutex) {
    const VerilatedLockGuard lock{m_mutex};
    VL_DEBUG_IF(VL_DBG_MSGF("+prof+threads writing to '%s'\n", filenamep););

    FILE* const fp = std::fopen(filenamep, "w");
    if (VL_UNLIKELY(!fp)) {
        VL_FATAL_MT(filenamep, 0, "", "+prof+threads+file file not writable");
        // cppcheck-suppress resourceLeak   // bug, doesn't realize fp is nullptr
        return;  // LCOV_EXCL_LINE
    }

    // TODO Perhaps merge with verilated_coverage output format, so can
    // have a common merging and reporting tool, etc.
    fprintf(fp, "VLPROFTHREAD 1.1 # Verilator thread profile dump version 1.1\n");
    fprintf(fp, "VLPROF arg --threads %" VL_PRI64 "u\n", vluint64_t(m_workers.size() + 1));
    fprintf(fp, "VLPROF arg +verilator+prof+threads+start+%" VL_PRI64 "u\n",
            Verilated::threadContextp()->profThreadsStart());
    fprintf(fp, "VLPROF arg +verilator+prof+threads+window+%u\n",
            Verilated::threadContextp()->profThreadsWindow());
    fprintf(fp, "VLPROF stat yields %" VL_PRI64 "u\n", VlMTaskVertex::yields());

    // Copy /proc/cpuinfo into this output so verilator_gantt can be run on
    // a different machine
    {
        const std::unique_ptr<std::ifstream> ifp{new std::ifstream("/proc/cpuinfo")};
        if (!ifp->fail()) {
            std::string line;
            while (std::getline(*ifp, line)) { fprintf(fp, "VLPROFPROC %s\n", line.c_str()); }
        }
    }

    vluint32_t thread_id = 0;
    for (const auto& pi : m_allProfiles) {
        ++thread_id;

        bool printing = false;  // False while in warmup phase
        for (const auto& ei : *pi) {
            switch (ei.m_type) {
            case VlProfileRec::TYPE_BARRIER:  //
                printing = true;
                break;
            case VlProfileRec::TYPE_EVAL:
                if (!printing) break;
                fprintf(fp,
                        "VLPROF eval start %" VL_PRI64 "u elapsed %" VL_PRI64 "u"
                        " cpu %u on thread %u\n",
                        ei.m_startTime - tickStart, (ei.m_endTime - ei.m_startTime), ei.m_cpu,
                        thread_id);
                break;
            case VlProfileRec::TYPE_EVAL_LOOP:
                if (!printing) break;
                fprintf(fp,
                        "VLPROF eval_loop start %" VL_PRI64 "u elapsed %" VL_PRI64 "u"
                        " cpu %u on thread %u\n",
                        ei.m_startTime - tickStart, (ei.m_endTime - ei.m_startTime), ei.m_cpu,
                        thread_id);
                break;
            case VlProfileRec::TYPE_MTASK_RUN:
                if (!printing) break;
                fprintf(fp,
                        "VLPROF mtask %d"
                        " start %" VL_PRI64 "u elapsed %" VL_PRI64 "u"
                        " predict_start %u predict_cost %u cpu %u on thread %u\n",
                        ei.m_mtaskId, ei.m_startTime - tickStart, (ei.m_endTime - ei.m_startTime),
                        ei.m_predictStart, ei.m_predictCost, ei.m_cpu, thread_id);
                break;
            default: assert(false); break;  // LCOV_EXCL_LINE
            }
        }
    }
    fprintf(fp, "VLPROF stat ticks %" VL_PRI64 "u\n", tickEnd - tickStart);

    std::fclose(fp);
}
