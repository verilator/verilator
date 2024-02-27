// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
//
// Copyright 2024 by Andrew Nolte. This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

// Copyright cocotb contributors
// Licensed under the Revised BSD License, see LICENSE for details.
// SPDX-License-Identifier: BSD-3-Clause

#include "verilated.h"
#include "verilated_vpi.h"

#include VM_PREFIX_INCLUDE

#include <cstdint>
#include <memory>

#ifndef VM_TRACE_FST
// emulate new verilator behavior for legacy versions
#define VM_TRACE_FST 0
#endif

#if VM_TRACE
#if VM_TRACE_FST
#include <verilated_fst_c.h>
#else
#include <verilated_vcd_c.h>
#endif
#endif

extern void (*vlog_startup_routines[])();

static bool settle_value_callbacks() {
    bool cbs_called;
    bool again;

    // Call Value Change callbacks
    // These can modify signal values so we loop
    // until there are no more changes
    cbs_called = again = VerilatedVpi::callValueCbs();
    while (again) { again = VerilatedVpi::callValueCbs(); }

    return cbs_called;
}

int main(int argc, char** argv) {
    const std::unique_ptr<VerilatedContext> contextp{new VerilatedContext};
    bool traceOn = false;

    for (int i = 1; i < argc; ++i) {
        const std::string arg = std::string(argv[i]);
        if (arg == "--trace") {
            traceOn = true;
        } else if (arg == "--help") {
            fprintf(stderr,
                    "usage: %s [--trace]\n"
                    "\n"
                    "Cocotb + Verilator sim\n"
                    "\n"
                    "options:\n"
                    "  --trace      Enables tracing (VCD or FST)\n",
                    basename(argv[0]));
            return 0;
        }
    }

    (void)traceOn;  // Prevent unused if VM_TRACE not defined
    contextp->commandArgs(argc, argv);
#ifdef VERILATOR_SIM_DEBUG
    contextp->debug(99);
#endif
    const std::unique_ptr<VM_PREFIX> top{new VM_PREFIX{contextp.get(),
                                                       // Note null name - we're flattening it out
                                                       ""}};
    contextp->fatalOnVpiError(false);  // otherwise it will fail on systemtf

#ifdef VERILATOR_SIM_DEBUG
    contextp->internalsDump();
#endif
    for (auto it = &vlog_startup_routines[0]; *it != nullptr; it++) {
        auto routine = *it;
        routine();
    }

    VerilatedVpi::callCbs(cbStartOfSimulation);

#if VM_TRACE
#if VM_TRACE_FST
    std::unique_ptr<VerilatedFstC> tfp(new VerilatedFstC);
    const char* traceFile = "dump.fst";
#else
    std::unique_ptr<VerilatedVcdC> tfp(new VerilatedVcdC);
    const char* traceFile = "dump.vcd";
#endif

    if (traceOn) {
        contextp->traceEverOn(true);
        top->trace(tfp.get(), 99);
        tfp->open(traceFile);
    }
#endif

    while (!contextp->gotFinish()) {
        // Call registered timed callbacks (e.g. clock timer)
        // These are called at the beginning of the time step
        // before the iterative regions (IEEE 1800-2012 4.4.1)
        VerilatedVpi::callTimedCbs();

        // Call Value Change callbacks triggered by Timer callbacks
        // These can modify signal values
        settle_value_callbacks();

        // We must evaluate whole design until we process all 'events'
        bool again = true;
        while (again) {
            // Evaluate design
            top->eval_step();

            // Call Value Change callbacks triggered by eval()
            // These can modify signal values
            again = settle_value_callbacks();

            // Call registered ReadWrite callbacks
            again |= VerilatedVpi::callCbs(cbReadWriteSynch);

            // Call Value Change callbacks triggered by ReadWrite callbacks
            // These can modify signal values
            again |= settle_value_callbacks();
        }
        top->eval_end_step();

        // Call ReadOnly callbacks
        VerilatedVpi::callCbs(cbReadOnlySynch);

#if VM_TRACE
        if (traceOn) { tfp->dump(contextp->time()); }
#endif
        // cocotb controls the clock inputs using cbAfterDelay so
        // skip ahead to the next registered callback
        const uint64_t NO_TOP_EVENTS_PENDING = static_cast<uint64_t>(~0ULL);
        const uint64_t next_time_cocotb = VerilatedVpi::cbNextDeadline();
        const uint64_t next_time_timing
            = top->eventsPending() ? top->nextTimeSlot() : NO_TOP_EVENTS_PENDING;
        const uint64_t next_time = std::min(next_time_cocotb, next_time_timing);

        // If there are no more cbAfterDelay callbacks,
        // the next deadline is max value, so end the simulation now
        if (next_time == NO_TOP_EVENTS_PENDING) {
            break;
        } else {
            contextp->time(next_time);
        }

        // Call registered NextSimTime
        // It should be called in simulation cycle before everything else
        // but not on first cycle
        VerilatedVpi::callCbs(cbNextSimTime);

        // Call Value Change callbacks triggered by NextTimeStep callbacks
        // These can modify signal values
        settle_value_callbacks();
    }

    VerilatedVpi::callCbs(cbEndOfSimulation);

    top->final();

#if VM_TRACE
    if (traceOn) { tfp->close(); }
#endif

// VM_COVERAGE is a define which is set if Verilator is
// instructed to collect coverage (when compiling the simulation)
#if VM_COVERAGE
    VerilatedCov::write("coverage.dat");
#endif

    return 0;
};
