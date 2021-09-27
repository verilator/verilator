// -*- mode: C++; c-file-style: "cc-mode" -*-
//=============================================================================
//
// Code available from: https://verilator.org
//
// Copyright 2012-2021 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//=============================================================================
///
/// \file
/// \brief Verilated general profiling header
///
/// This file is not part of the Verilated public-facing API.
/// It is only for internal use by Verilated library routines.
///
//=============================================================================

#ifndef VERILATOR_VERILATED_PROFILER_H_
#define VERILATOR_VERILATED_PROFILER_H_

#include "verilatedos.h"
#include "verilated.h"  // for VerilatedMutex and clang annotations

// Profile record, private class used only by this header
class VerilatedProfilerRec final {
    std::string m_name;  // Hashed name of mtask/etc
    size_t m_counterNumber = 0;  // Which counter has data
public:
    // METHODS
    VerilatedProfilerRec(size_t counterNumber, const std::string& name)
        : m_name{name}
        , m_counterNumber{counterNumber} {}
    VerilatedProfilerRec() = default;
    size_t counterNumber() const { return m_counterNumber; }
    std::string name() const { return m_name; }
};

// Create some number of bucketed profilers
template <std::size_t T_Entries> class VerilatedProfiler final {
    // Counters are stored packed, all together, versus in VerilatedProfilerRec to
    // reduce cache effects
    std::array<vluint64_t, T_Entries> m_counters{};  // Time spent on this record
    std::deque<VerilatedProfilerRec> m_records;  // Record information

public:
    // METHODS
    VerilatedProfiler() = default;
    ~VerilatedProfiler() = default;
    void write(const char* modelp, const std::string& filename) VL_MT_SAFE;
    void addCounter(size_t counter, const std::string& name) {
        VL_DEBUG_IF(assert(counter < T_Entries););
        m_records.emplace_back(VerilatedProfilerRec{counter, name});
    }
    void startCounter(size_t counter) {
        vluint64_t val;
        VL_RDTSC(val);
        // -= so when we add end time in stopCounter, we already subtracted
        // out, without needing to hold another temporary
        m_counters[counter] -= val;
    }
    void stopCounter(size_t counter) {
        vluint64_t val;
        VL_RDTSC(val);
        m_counters[counter] += val;
    }
};

template <std::size_t T_Entries>
void VerilatedProfiler<T_Entries>::write(const char* modelp,
                                         const std::string& filename) VL_MT_SAFE {
    static VerilatedMutex s_mutex;
    const VerilatedLockGuard lock{s_mutex};

    // On the first call we create the file.  On later calls we append.
    // So when we have multiple models in an executable, possibly even
    // running on different threads, each will have a different symtab so
    // each will collect is own data correctly.  However when each is
    // destroid we need to get all the data, not keep overwriting and only
    // get the last model's data.
    static bool s_firstCall = true;

    VL_DEBUG_IF(VL_DBG_MSGF("+prof+vlt+file writing to '%s'\n", filename.c_str()););

    FILE* fp = nullptr;
    if (!s_firstCall) fp = std::fopen(filename.c_str(), "a");
    if (VL_UNLIKELY(!fp))
        fp = std::fopen(filename.c_str(), "w");  // firstCall, or doesn't exist yet
    if (VL_UNLIKELY(!fp)) {
        VL_FATAL_MT(filename.c_str(), 0, "", "+prof+vlt+file file not writable");
        // cppcheck-suppress resourceLeak   // bug, doesn't realize fp is nullptr
        return;  // LCOV_EXCL_LINE
    }
    s_firstCall = false;

    // TODO Perhaps merge with verilated_coverage output format, so can
    // have a common merging and reporting tool, etc.
    fprintf(fp, "// Verilated model profile-guided optimization data dump file\n");
    fprintf(fp, "`verilator_config\n");

    for (const auto& it : m_records) {
        const std::string& name = it.name();
        fprintf(fp, "profile_data -model \"%s\" -mtask \"%s\" -cost 64'd%" VL_PRI64 "u\n", modelp,
                name.c_str(), m_counters[it.counterNumber()]);
    }

    std::fclose(fp);
}

#endif
