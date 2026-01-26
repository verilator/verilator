// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
//
// Copyright 2026 by Wilson Snyder. This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

// Generated header
#include "Vt_gantt_numa_default_threads.h"
// General headers
#include "verilated.h"

#include "TestCheck.h"

int errors = 0;

std::unique_ptr<Vt_gantt_numa_default_threads> topp;

int main(int argc, char** argv) {
    vluint64_t sim_time = 1100;
    const std::unique_ptr<VerilatedContext> contextp{new VerilatedContext};
    contextp->debug(0);
    contextp->commandArgs(argc, argv);
    srand48(5);
    TEST_CHECK_EQ(contextp->useNumaAssign(), false);
    contextp->threads(3);
    TEST_CHECK_EQ(contextp->useNumaAssign(), true);
    contextp->useNumaAssign(false);
    TEST_CHECK_EQ(contextp->useNumaAssign(), false);
    topp.reset(new VM_PREFIX{"top"});

    topp->clk = 0;
    topp->eval();
    { contextp->timeInc(10); }

    while ((contextp->time() < sim_time) && !contextp->gotFinish()) {
        topp->eval();
        topp->clk = !topp->clk;
        topp->eval();
        contextp->timeInc(5);
    }
    if (!contextp->gotFinish()) {
        vl_fatal(__FILE__, __LINE__, "main", "%Error: Timeout; never got a $finish");
    }
    topp->final();

    topp.reset();
    return (errors ? 10 : 0);
}
