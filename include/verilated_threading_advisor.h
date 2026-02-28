// -*- mode: C++; c-file-style: "cc-mode" -*-
//=============================================================================
//
// Code available from: https://verilator.org
//
// Copyright 2025 by Wilson Snyder. This program is free software; you
// can redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//=============================================================================
///
/// \file
/// \brief Verilated runtime threading advisor
///
/// This file provides runtime analysis of threading configuration and
/// emits warnings when potential issues are detected. Unlike verilator_gantt
/// which requires explicit profiling and post-hoc analysis, this advisor
/// checks for common configuration issues automatically.
///
/// This file is not part of the Verilated public-facing API.
/// It is only for internal use by Verilated library routines.
///
//=============================================================================

#ifndef VERILATOR_VERILATED_THREADING_ADVISOR_H_
#define VERILATOR_VERILATED_THREADING_ADVISOR_H_

#include "verilatedos.h"

#include <cstdint>
#include <cstdio>
#include <fstream>
#include <set>
#include <sstream>
#include <string>
#include <utility>
#include <vector>

//=============================================================================
// VlThreadingAdvisor - Runtime threading configuration advisor
//
// Analyzes CPU topology and threading configuration to detect potential
// performance issues. This is advisory only - it does not affect simulation.

class VlThreadingAdvisor final {
    // TYPES
    struct CpuInfo final {
        int cpuId = -1;  // Logical CPU ID
        int physicalId = -1;  // Physical socket/package ID
        int coreId = -1;  // Core ID within socket
        bool valid = false;  // True if info was successfully read
    };

    // MEMBERS
    std::vector<CpuInfo> m_cpuInfo;  // CPU topology information
    unsigned m_physicalCores = 0;  // Number of physical cores
    unsigned m_logicalCpus = 0;  // Number of logical CPUs (hw threads)
    unsigned m_sockets = 0;  // Number of CPU sockets
    bool m_hyperthreading = false;  // True if SMT/hyperthreading detected
    bool m_topologyRead = false;  // True if topology was successfully read

public:
    // CONSTRUCTORS
    VlThreadingAdvisor() { readTopology(); }
    ~VlThreadingAdvisor() = default;

    // METHODS

    /// Analyze threading configuration and emit warnings if issues detected
    /// @param nthreads  Number of simulation threads (including main thread)
    /// @param quiet  If true, suppress all output
    void analyze(unsigned nthreads, bool quiet) const {
        if (quiet) return;
        if (nthreads <= 1) return;  // Single-threaded, nothing to check
        if (!m_topologyRead) return;  // Can't analyze without topology

        checkThreadCount(nthreads);
        checkHyperthreading(nthreads);
    }

    // ACCESSORS
    unsigned physicalCores() const { return m_physicalCores; }
    unsigned logicalCpus() const { return m_logicalCpus; }
    unsigned sockets() const { return m_sockets; }
    bool hasHyperthreading() const { return m_hyperthreading; }

private:
    void readTopology() {
#if defined(__linux__)
        readTopologyLinux();
#elif defined(__APPLE__)
        readTopologyMacOS();
#endif
    }

#if defined(__linux__)
    void readTopologyLinux() {
        // Read CPU topology from /sys/devices/system/cpu/
        const unsigned maxCpus = VlOs::getProcessDefaultParallelism();
        m_cpuInfo.resize(maxCpus);

        std::set<int> sockets;
        std::set<std::pair<int, int>> physCores;  // (socket, core) pairs

        for (unsigned cpu = 0; cpu < maxCpus; ++cpu) {
            CpuInfo& info = m_cpuInfo[cpu];
            info.cpuId = static_cast<int>(cpu);

            // Read physical package ID (socket)
            std::ostringstream physPath;
            physPath << "/sys/devices/system/cpu/cpu" << cpu
                     << "/topology/physical_package_id";
            std::ifstream physFile(physPath.str());
            if (physFile.good()) {
                physFile >> info.physicalId;
                sockets.insert(info.physicalId);
            }

            // Read core ID
            std::ostringstream corePath;
            corePath << "/sys/devices/system/cpu/cpu" << cpu << "/topology/core_id";
            std::ifstream coreFile(corePath.str());
            if (coreFile.good()) {
                coreFile >> info.coreId;
                if (info.physicalId >= 0) {
                    physCores.insert({info.physicalId, info.coreId});
                }
            }

            info.valid = (info.physicalId >= 0 && info.coreId >= 0);
        }

        m_logicalCpus = maxCpus;
        m_sockets = static_cast<unsigned>(sockets.size());
        m_physicalCores = static_cast<unsigned>(physCores.size());
        m_hyperthreading = (m_logicalCpus > m_physicalCores);
        m_topologyRead = (m_physicalCores > 0);
    }
#endif

#if defined(__APPLE__)
    void readTopologyMacOS() {
        // On macOS, use sysctl to get CPU info
        // For simplicity, just use basic heuristics
        m_logicalCpus = VlOs::getProcessDefaultParallelism();
        // Apple Silicon doesn't have traditional hyperthreading
        // Intel Macs may have it - assume no HT for simplicity
        m_physicalCores = m_logicalCpus;
        m_sockets = 1;
        m_hyperthreading = false;
        m_topologyRead = true;
    }
#endif

    void checkThreadCount(unsigned nthreads) const {
        // Check if requesting more threads than physical cores
        if (m_hyperthreading && nthreads > m_physicalCores) {
            std::fprintf(stderr,
                         "%%Warning: Simulation uses %u threads but system has only %u physical "
                         "cores (%u logical CPUs with hyperthreading).\n",
                         nthreads, m_physicalCores, m_logicalCpus);
            std::fprintf(stderr,
                         "        : Using more threads than physical cores often reduces "
                         "performance.\n");
            std::fprintf(stderr,
                         "        : Consider --threads %u or use numactl to bind to physical "
                         "cores.\n",
                         m_physicalCores);
        }
    }

    void checkHyperthreading(unsigned /*nthreads*/) const {
        // On systems with hyperthreading, could warn about potential core sharing
        // However, this is too noisy for default behavior. Users who want detailed
        // analysis should use +verilator+prof+exec and verilator_gantt.
    }
};

#endif  // VERILATOR_VERILATED_THREADING_ADVISOR_H_
