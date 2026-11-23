// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Fixed worker dispatch and object lifetime
//
// Code available to: https://verilator.org
//
//*************************************************************************
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2026-2026 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#include "verilated.h"
#include "verilated_threads.h"

#include <atomic>
#include <chrono>
#include <iostream>

struct FixedState final {
    VlFixedTask task;
    std::atomic<uint32_t> input{0};
    std::atomic<uint32_t> output{0};
    std::atomic<bool> done{false};
};

static void fixedFn(void* selfp) {
    FixedState* const statep = static_cast<FixedState*>(selfp);
    const uint32_t in = statep->input.load(std::memory_order_relaxed);
    statep->output.store(in ^ 0x12345678U, std::memory_order_relaxed);
    statep->done.store(true, std::memory_order_release);
}

// Start one fixed invocation and join it before returning, so the caller only
// reuses the descriptor after the worker has finished with it.
static void runOnce(FixedState* statep, uint32_t in) {
    statep->done.store(false, std::memory_order_relaxed);
    statep->input.store(in, std::memory_order_relaxed);
    statep->task.start();
    while (!statep->done.load(std::memory_order_acquire)) VL_CPU_RELAX();
    if (statep->output.load(std::memory_order_relaxed) != (in ^ 0x12345678U)) {
        VL_FATAL_MT(__FILE__, __LINE__, "", "Fixed dispatch lost input");
    }
}

static void checkFixed(VlWorkerThread* workerp) {
    for (unsigned lifetime = 0; lifetime < 1000; ++lifetime) {
        // Let the ordinary queue worker park before re-registering fixed work.
        if (lifetime % 100 == 0) std::this_thread::sleep_for(std::chrono::milliseconds{2});
        // Two live descriptors on one worker, interleaved.
        // Delete immediately after the final join to exercise descriptor lifetime.
        FixedState* const ap = new FixedState;
        FixedState* const bp = new FixedState;
        ap->task.configure(workerp, fixedFn, ap);
        bp->task.configure(workerp, fixedFn, bp);
        for (unsigned i = 0; i < 32; ++i) {
            FixedState* const statep = (i % 3) == 0 ? bp : ap;
            runOnce(statep, lifetime * 32 + i);
            // Setup, ordinary model work and wait markers must still progress
            // while fixed entries are registered on the same pool.
            if (i % 7 == 0) workerp->wait();
        }
        delete ap;
        delete bp;
        workerp->wait();
    }
}

// A quiescent registration can be forgotten after its pool is discarded for cloning.
static void checkCloneReset() {
    VerilatedContext context;
    context.threads(2);
    VlWorkerThread* workerp = static_cast<VlThreadPool*>(context.threadPoolp())->workerp(0);
    FixedState* const statep = new FixedState;
    statep->task.configure(workerp, fixedFn, statep);
    runOnce(statep, 7);
    context.prepareClone();
    statep->task.resetForClone();
    workerp = static_cast<VlThreadPool*>(context.threadPoolpOnClone())->workerp(0);
    statep->task.configure(workerp, fixedFn, statep);
    runOnce(statep, 9);
    delete statep;
    workerp->wait();
}

// Fatal shutdown can delete the pool before static model-owned tasks are destroyed.
static void checkShutdown() {
    FixedState state;
    VerilatedContext context;
    context.threads(2);
    VlWorkerThread* const workerp = static_cast<VlThreadPool*>(context.threadPoolp())->workerp(0);
    state.task.configure(workerp, fixedFn, &state);
    runOnce(&state, 11);
    context.threadPoolShutdown();
}

int main() {
    VerilatedContext context;
    context.threads(2);
    VlWorkerThread* const workerp = static_cast<VlThreadPool*>(context.threadPoolp())->workerp(0);
    checkFixed(workerp);
    checkCloneReset();
    checkShutdown();
    std::cout << "*-* All Finished *-*\n";
    return 0;
}
