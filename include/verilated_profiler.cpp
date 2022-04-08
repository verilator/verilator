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
/// \brief Verilated run-time profiling implementation code
///
//=============================================================================

#include "verilatedos.h"
#include "verilated_profiler.h"

#if VL_THREADED
#include "verilated_threads.h"
#endif

#include <fstream>
#include <string>

//=============================================================================
// Globals

// Internal note: Globals may multi-construct, see verilated.cpp top.

VL_THREAD_LOCAL VlExecutionProfiler::ExecutionTrace VlExecutionProfiler::t_trace;

constexpr const char* const VlExecutionRecord::s_ascii[];

//=============================================================================
// VlPgoProfiler implementation

uint16_t VlExecutionRecord::getcpu() {
#if defined(__linux)
    return sched_getcpu();  // TODO: this is a system call. Not exactly cheap.
#elif defined(__APPLE__) && !defined(__arm64__)
    uint32_t info[4];
    __cpuid_count(1, 0, info[0], info[1], info[2], info[3]);
    // info[1] is EBX, bits 24-31 are APIC ID
    if ((info[3] & (1 << 9)) == 0) {
        return -1;  // no APIC on chip
    } else {
        return (unsigned)info[1] >> 24;
    }
#elif defined(_WIN32)
    return GetCurrentProcessorNumber();
#else
    return 0;
#endif
}

//=============================================================================
// VlExecutionProfiler implementation

template <size_t N> size_t roundUptoMultipleOf(size_t value) {
    static_assert((N & (N - 1)) == 0, "'N' must be a power of 2");
    size_t mask = N - 1;
    return (value + mask) & ~mask;
}

VlExecutionProfiler::VlExecutionProfiler() {
    // Setup profiling on main thread
    setupThread(0);
}

void VlExecutionProfiler::configure(const VerilatedContext& context) {
    if (VL_UNLIKELY(m_enabled)) {
        --m_windowCount;
        if (VL_UNLIKELY(m_windowCount == context.profExecWindow())) {
            VL_DEBUG_IF(VL_DBG_MSGF("+ profile start collection\n"););
            clear();  // Clear the profile after the cache warm-up cycles.
            m_tickBegin = VL_CPU_TICK();
        } else if (VL_UNLIKELY(m_windowCount == 0)) {
            const uint64_t tickEnd = VL_CPU_TICK();
            VL_DEBUG_IF(VL_DBG_MSGF("+ profile end\n"););
            const std::string& fileName = context.profExecFilename();
            dump(fileName.c_str(), tickEnd);
            m_enabled = false;
        }
        return;
    }

    const uint64_t startReq = context.profExecStart() + 1;  // + 1, so we can start at time 0

    if (VL_UNLIKELY(m_lastStartReq < startReq && VL_TIME_Q() >= context.profExecStart())) {
        VL_DEBUG_IF(VL_DBG_MSGF("+ profile start warmup\n"););
        VL_DEBUG_IF(assert(m_windowCount == 0););
        m_enabled = true;
        m_windowCount = context.profExecWindow() * 2;
        m_lastStartReq = startReq;
    }
}

void VlExecutionProfiler::setupThread(uint32_t threadId) {
    // Reserve some space in the thread-local profiling buffer, in order to try to avoid malloc
    // while profiling.
    t_trace.reserve(RESERVED_TRACE_CAPACITY);
    // Register thread-local buffer in list of all buffers
    {
        const VerilatedLockGuard lock{m_mutex};
        bool exists = !m_traceps.emplace(threadId, &t_trace).second;
        assert(!exists);
    }
}

void VlExecutionProfiler::clear() VL_MT_SAFE_EXCLUDES(m_mutex) {
    const VerilatedLockGuard lock{m_mutex};
    for (const auto& pair : m_traceps) {
        ExecutionTrace* const tracep = pair.second;
        const size_t reserve = roundUptoMultipleOf<RESERVED_TRACE_CAPACITY>(tracep->size());
        tracep->clear();
        tracep->reserve(reserve);
    }
}

void VlExecutionProfiler::dump(const char* filenamep, uint64_t tickEnd)
    VL_MT_SAFE_EXCLUDES(m_mutex) {
    const VerilatedLockGuard lock{m_mutex};
    VL_DEBUG_IF(VL_DBG_MSGF("+prof+exec writing to '%s'\n", filenamep););

    FILE* const fp = std::fopen(filenamep, "w");
    if (VL_UNLIKELY(!fp)) { VL_FATAL_MT(filenamep, 0, "", "+prof+exec+file file not writable"); }

    // TODO Perhaps merge with verilated_coverage output format, so can
    // have a common merging and reporting tool, etc.
    fprintf(fp, "VLPROFVERSION 2.0 # Verilator execution profile version 2.0\n");
    fprintf(fp, "VLPROF arg +verilator+prof+exec+start+%" PRIu64 "\n",
            Verilated::threadContextp()->profExecStart());
    fprintf(fp, "VLPROF arg +verilator+prof+exec+window+%u\n",
            Verilated::threadContextp()->profExecWindow());
    const unsigned threads = static_cast<unsigned>(m_traceps.size());
    fprintf(fp, "VLPROF stat threads %u\n", threads);
#ifdef VL_THREADED
    fprintf(fp, "VLPROF stat yields %" PRIu64 "\n", VlMTaskVertex::yields());
#endif

    // Copy /proc/cpuinfo into this output so verilator_gantt can be run on
    // a different machine
    {
        const std::unique_ptr<std::ifstream> ifp{new std::ifstream("/proc/cpuinfo")};
        if (!ifp->fail()) {
            std::string line;
            while (std::getline(*ifp, line)) { fprintf(fp, "VLPROFPROC %s\n", line.c_str()); }
        }
    }

    for (const auto& pair : m_traceps) {
        const uint32_t threadId = pair.first;
        ExecutionTrace* const tracep = pair.second;
        fprintf(fp, "VLPROFTHREAD %" PRIu32 "\n", threadId);

        for (const VlExecutionRecord& er : *tracep) {
            const char* const name = VlExecutionRecord::s_ascii[static_cast<uint8_t>(er.m_type)];
            const uint64_t time = er.m_tick - m_tickBegin;
            fprintf(fp, "VLPROFEXEC %s %" PRIu64, name, time);

            switch (er.m_type) {
            case VlExecutionRecord::Type::EVAL_BEGIN:
            case VlExecutionRecord::Type::EVAL_END:
            case VlExecutionRecord::Type::EVAL_LOOP_BEGIN:
            case VlExecutionRecord::Type::EVAL_LOOP_END:
                // No payload
                fprintf(fp, "\n");
                break;
            case VlExecutionRecord::Type::MTASK_BEGIN: {
                const auto& payload = er.m_payload.mtaskBegin;
                fprintf(fp, " id %u predictStart %u cpu %u\n", payload.m_id,
                        payload.m_predictStart, payload.m_cpu);
                break;
            }
            case VlExecutionRecord::Type::MTASK_END: {
                const auto& payload = er.m_payload.mtaskEnd;
                fprintf(fp, " id %u predictCost %u\n", payload.m_id, payload.m_predictCost);
                break;
            }
            default: abort();  // LCOV_EXCL_LINE
            }
        }
    }
    fprintf(fp, "VLPROF stat ticks %" PRIu64 "\n", tickEnd - m_tickBegin);

    std::fclose(fp);
}
