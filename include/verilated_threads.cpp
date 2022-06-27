// -*- mode: C++; c-file-style: "cc-mode" -*-
//=============================================================================
//
// Code available from: https://verilator.org
//
// Copyright 2012-2022 by Wilson Snyder. This program is free software; you can
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
#include <memory>
#include <string>

//=============================================================================
// Globals

// Internal note: Globals may multi-construct, see verilated.cpp top.

std::atomic<uint64_t> VlMTaskVertex::s_yields;

//=============================================================================
// VlMTaskVertex

VlMTaskVertex::VlMTaskVertex(uint32_t upstreamDepCount)
    : m_upstreamDepsDone{0}
    , m_upstreamDepCount{upstreamDepCount} {
    assert(atomic_is_lock_free(&m_upstreamDepsDone));
}

//=============================================================================
// VlWorkerThread

VlWorkerThread::VlWorkerThread(uint32_t threadId, VerilatedContext* contextp,
                               VlExecutionProfiler* profilerp, VlStartWorkerCb startCb)
    : m_ready_size{0}
    , m_cthread{startWorker, this, threadId, profilerp, startCb}
    , m_contextp{contextp} {}

VlWorkerThread::~VlWorkerThread() {
    shutdown();
    // The thread should exit; join it.
    m_cthread.join();
}

void VlWorkerThread::shutdownTask(void*, bool) {
    // Deliberately empty, we use the address of this function as a magic number
}

void VlWorkerThread::workerLoop() {
    ExecRec work;

    while (true) {
        dequeWork(&work);
        if (VL_UNLIKELY(work.m_fnp == shutdownTask)) break;
        work.m_fnp(work.m_selfp, work.m_evenCycle);
    }
}

void VlWorkerThread::startWorker(VlWorkerThread* workerp, uint32_t threadId,
                                 VlExecutionProfiler* profilerp, VlStartWorkerCb startCb) {
    Verilated::threadContextp(workerp->m_contextp);
    if (VL_UNLIKELY(startCb)) startCb(profilerp, threadId);
    workerp->workerLoop();
}

//=============================================================================
// VlThreadPool

VlThreadPool::VlThreadPool(VerilatedContext* contextp, int nThreads,
                           VlExecutionProfiler* profilerp, VlStartWorkerCb startCb) {
    // --threads N passes nThreads=N-1, as the "main" threads counts as 1
    ++nThreads;
    const unsigned cpus = std::thread::hardware_concurrency();
    if (cpus < nThreads) {
        static int warnedOnce = 0;
        if (!warnedOnce++) {
            VL_PRINTF_MT("%%Warning: System has %u CPUs but model Verilated with"
                         " --threads %d; may run slow.\n",
                         cpus, nThreads);
        }
    }
    // Create worker threads
    for (uint32_t threadId = 1; threadId < nThreads; ++threadId) {
        m_workers.push_back(new VlWorkerThread{threadId, contextp, profilerp, startCb});
    }
}

VlThreadPool::~VlThreadPool() {
    // Each ~WorkerThread will wait for its thread to exit.
    for (auto& i : m_workers) delete i;
}
