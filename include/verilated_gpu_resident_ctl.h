// -*- mode: C++; c-file-style: "cc-mode" -*-
//=============================================================================
//
// Code available from: https://verilator.org
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2026-2026 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//=============================================================================
///
/// \file
/// \brief GPU runtime: resident scheduler control block
///
//=============================================================================

#ifndef VERILATOR_VERILATED_GPU_RESIDENT_CTL_H_
#define VERILATOR_VERILATED_GPU_RESIDENT_CTL_H_

#include <cstdint>

enum VlGpuResidentError : uint32_t {
    VL_GPU_ERR_NONE = 0,
    VL_GPU_ERR_CONVERGE = 1,
    VL_GPU_ERR_FORK_OVERFLOW = 2,
};

struct VlGpuResidentCtl final {
    static constexpr int LOOPS = 6;
    uint64_t m_reduce[3];  // Rotating slots for grid-wide time minimum
    uint32_t m_flags[3];  // Rotating slots for grid-wide flag OR
    uint32_t m_done;  // Set by the kernel when no copy has more work
    uint64_t m_sliceNs;  // Kernel time slice in ns, 0 for none
    uint64_t m_steps;  // Time steps simulated, for statistics
    uint64_t m_profGraphNs;  // Time spent in task graphs
    uint64_t m_profGraphRuns;  // Number of task graph runs
    uint64_t m_profStepNs;  // Time spent in time steps
    uint32_t m_convergeLimit;  // Region iterations before a copy fails to converge
    uint32_t* m_runp;  // Per loop and copy: copy still iterating this loop
    uint32_t* m_iterp;  // Per loop and copy: iterations so far
    uint32_t* m_wantp;  // Per copy: task graph the copy is waiting for, 0 for none
    uint32_t* m_errorp;  // Per copy: error code, 0 for none
    uint32_t* m_steppingp;  // Per copy: copy takes part in the current time step
    uint64_t* m_nextp;  // Per copy: time of its next event
    uint64_t* m_stepTimesp;  // Times of the simulated steps, for debugging
    uint64_t m_levelNs[64];  // Time per graph level, for statistics
    uint32_t m_epoch[32];  // Dataflow epoch per task graph
    uint32_t m_levelMode;  // Run task graphs level by level instead of dataflow
    uint64_t m_stopTime;  // Stop when time passes this, for state dumps
    uint32_t m_flowMax;  // Waiting copies above which graphs run level by level
    uint32_t m_counts[3];  // Rotating slots for grid-wide counts
    uint64_t m_regionNs[8];  // Time per scheduler region, for statistics
    uint64_t m_regionCalls[8];  // Calls per scheduler region, for statistics
    uint64_t m_stepTimesMax;  // Capacity of m_stepTimesp
    uint64_t m_profSeqRuns;  // Number of graph runs on the sequential path
    uint32_t m_noSeq;  // Disable the sequential graph path
    uint32_t m_noSplit;  // Disable the control/worker block split
    uint32_t m_cmd;  // Command for worker blocks: graph and mode, or exit
    uint32_t m_cmdGen;  // Incremented for each new command
    uint32_t m_barGen;  // Generation of the control-block barrier
    uint32_t m_barCount;  // Control blocks arrived at the barrier
};

#endif
