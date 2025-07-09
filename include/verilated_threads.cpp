// -*- mode: C++; c-file-style: "cc-mode" -*-
//=============================================================================
//
// Code available from: https://verilator.org
//
// Copyright 2012-2025 by Wilson Snyder. This program is free software; you can
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
#include <iostream>
#include <memory>
#include <string>

#ifdef __FreeBSD__
#include <pthread_np.h>
#endif

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

static void shutdownTask(void*, bool) {  // LCOV_EXCL_LINE
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
    for (unsigned i = 0; i < nThreads; ++i) {
        m_workers.push_back(new VlWorkerThread{contextp});
        m_unassignedWorkers.push(i);
    }
    m_numaStatus = numaAssign();
}

VlThreadPool::~VlThreadPool() {
    // Each ~WorkerThread will wait for its thread to exit.
    for (auto& i : m_workers) delete i;
}

bool VlThreadPool::isNumactlRunning() {
    // We assume if current thread is CPU-masked, then under numactl, otherwise not.
    // This shows that numactl is visible through the affinity mask
#if defined(__linux) || defined(CPU_ZERO)  // Linux-like; assume we have pthreads etc
    const unsigned num_cpus = std::thread::hardware_concurrency();
    cpu_set_t cpuset;
    CPU_ZERO(&cpuset);
    const int rc = pthread_getaffinity_np(pthread_self(), sizeof(cpu_set_t), &cpuset);
    if (rc != 0) return true;  // Error; assuming returning true is the least-damage option
    for (unsigned c = 0; c < std::min(num_cpus, static_cast<unsigned>(CPU_SETSIZE)); ++c) {
        if (!CPU_ISSET(c, &cpuset)) return true;
    }
#endif
    return false;
}

std::string VlThreadPool::numaAssign() {
#if defined(__linux) || defined(CPU_ZERO) || defined(VL_CPPCHECK)  // Linux-like pthreads
    // If not under numactl, make a reasonable processor affinity selection
    if (isNumactlRunning()) return "running under numactl";  // User presumably set affinity
    const int num_threads = static_cast<int>(m_workers.size());
    const int num_proc = static_cast<int>(std::thread::hardware_concurrency());
    if (num_threads < 2) return "too few threads";
    if (num_threads > num_proc) return "too many threads";

    // Read CPU info.
    // Uncertain if any modern system has gaps in the processor id (Solaris
    // did), but just in case use vectors instead of processor number math.
    //
    // Currently ignoring socket number "physical id".
    // If processor numbers are sequential on sockets, algorithm works out ok.
    // If processor numbers are strided on sockets, algorithm also works out ok.
    std::ifstream is{"/proc/cpuinfo"};
    if (VL_UNLIKELY(!is)) return "%Warning: no /proc/cpuinfo";

    std::vector<int> unassigned_processors;  // Processors to assign in sorted order
    std::map<int, int> processor_core;
    std::multimap<int, int> core_processors;
    std::set<int> cores;
    {
        int processor = -1;
        while (!is.eof()) {
            std::string line;
            std::getline(is, line);
            static std::string::size_type pos = line.find(":");
            int number = -1;
            if (pos != std::string::npos) number = atoi(line.c_str() + pos + 1);
            if (line.compare(0, std::strlen("processor"), "processor") == 0) {
                processor = number;
            } else if (line.compare(0, std::strlen("core id"), "core id") == 0) {
                const int core = number;
                // std::cout << "p" << processor << " socket " << socket << " c" << core <<
                // std::endl;
                cores.emplace(core);
                processor_core[processor] = core;
                core_processors.emplace(core, processor);
                unassigned_processors.push_back(processor);
            }
        }
    }

    // Start scheduling on the current CPU + 1.
    // This will help to land on the same socket as current CPU, and also
    // help make sure that different processes have different masks (when
    // num_threads is not a common-factor of the processor count).
    std::sort(unassigned_processors.begin(), unassigned_processors.end());
    {
        const int on_cpu = sched_getcpu();  // TODO: this is a system call. Not exactly cheap.
        bool hit = false;
        std::vector<int> new_front;
        std::vector<int> new_back;
        for (const int processor : unassigned_processors) {
            if (hit) {
                new_front.push_back(processor);
            } else {
                new_back.push_back(processor);
            }
            if (processor == on_cpu) hit = true;
        }
        unassigned_processors = new_front;
        unassigned_processors.insert(unassigned_processors.end(), new_back.begin(),
                                     new_back.end());
    }

    // If less threads than cores, we can schedule per-core
    const bool core_per_thread = num_threads <= cores.size();

    // Compute core mapping
    std::multimap<int, int> thread_processors;
    {
        std::set<int> assigned_processors;
        int thread = 0;
        for (const int processor : unassigned_processors) {
            // Find free processor, the current thread can use that
            if (assigned_processors.find(processor) != assigned_processors.end()) continue;
            assigned_processors.emplace(processor);
            thread_processors.emplace(thread, processor);
            if (core_per_thread) {
                // Also include all other processors same core,
                // so that another thread doesn't land on different processor in same core
                const int core = processor_core[processor];
                const auto bounds = core_processors.equal_range(core);
                for (auto it{bounds.first}; it != bounds.second; ++it) {
                    if (assigned_processors.find(it->second) != assigned_processors.end())
                        continue;
                    if (it->second == processor) continue;
                    thread_processors.emplace(thread, it->second);
                    assigned_processors.emplace(it->second);
                }
            }
            // Prepare for next loop
            thread = (thread + 1) % num_threads;
        }
    }

    // Set affinity
    std::string status = "assigned ";
    for (int thread = 0; thread < num_threads; ++thread) {
        cpu_set_t cpuset;
        CPU_ZERO(&cpuset);

        const auto bounds = thread_processors.equal_range(thread);
        for (auto it{bounds.first}; it != bounds.second; ++it) {
            if (it != bounds.first) status += ',';
            status += std::to_string(it->second);
            CPU_SET(it->second, &cpuset);
        }
        status += ";";

        const int rc = pthread_setaffinity_np(m_workers[thread]->m_cthread.native_handle(),
                                              sizeof(cpu_set_t), &cpuset);
        if (rc != 0) return "%Warning: pthread_setaffinity_np failed";
    }
    // std::cout << "Status: " << status << std::endl;
    return status;
#else
    return "non-supported host OS";
#endif
}
