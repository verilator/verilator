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

VlWorkerThread::VlWorkerThread(VerilatedContext* contextp)
    : m_ready_size{0}
    , m_cthread{startWorker, this, contextp} {}

VlWorkerThread::~VlWorkerThread() {
    shutdown();
    // The thread should exit; join it.
    m_cthread.join();
}

static void shutdownTask(void*, bool) {
    // Deliberately empty, we use the address of this function as a magic number
}

void VlWorkerThread::shutdown() { addTask(shutdownTask, nullptr); }

void VlWorkerThread::wait() {
    // Enqueue a task that sets this flag. Execution is in-order so this ensures completion.
    std::atomic<bool> flag{false};
    addTask([](void* flagp, bool) { static_cast<std::atomic<bool>*>(flagp)->store(true); }, &flag);
    // Spin wait
    for (unsigned i = 0; i < VL_LOCK_SPINS; ++i) {
        if (flag.load()) return;
        VL_CPU_RELAX();
    }
    // Yield wait
    while (!flag.load()) std::this_thread::yield();
}

void VlWorkerThread::workerLoop() {
    ExecRec work;

    // Wait for the first task without spinning, in case the thread is never actually used.
    dequeWork</* SpinWait: */ false>(&work);

    while (true) {
        if (VL_UNLIKELY(work.m_fnp == shutdownTask)) break;
        work.m_fnp(work.m_selfp, work.m_evenCycle);
        // Wait for next task with spinning.
        dequeWork</* SpinWait: */ true>(&work);
    }
}

void VlWorkerThread::startWorker(VlWorkerThread* workerp, VerilatedContext* contextp) {
    Verilated::threadContextp(contextp);
    workerp->workerLoop();
}

//=============================================================================
// VlThreadPool

VlThreadPool::VlThreadPool(VerilatedContext* contextp, unsigned nThreads) {
    for (unsigned i = 0; i < nThreads; ++i) m_workers.push_back(new VlWorkerThread{contextp});
}

VlThreadPool::~VlThreadPool() {
    // Each ~WorkerThread will wait for its thread to exit.
    for (auto& i : m_workers) delete i;
}
