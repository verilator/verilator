// -*- mode: C++; c-file-style: "cc-mode" -*-
//
// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2022 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

#include <verilated.h>
#include VL_STRINGIFY(TRACE_HEADER_C)

#include <memory>

#include VM_PREFIX_INCLUDE

unsigned long long main_time = 0;
double sc_time_stamp() { return (double)main_time; }

const unsigned long long dt_2 = 3;

int main(int argc, char** argv) {
    Verilated::debug(0);
    Verilated::traceEverOn(true);
    Verilated::commandArgs(argc, argv);

    std::unique_ptr<VM_PREFIX> top{new VM_PREFIX{"top"}};

    std::unique_ptr<VERILATED_TRACE_C> tfp{new VERILATED_TRACE_C};

#if defined(TEST_VARIANT_0)
    tfp->dumpvars(0, "");
#elif defined(TEST_VARIANT_1)
    tfp->dumpvars(99, "t");  // This should not match "top."
    tfp->dumpvars(1, "top.t.cyc");  // A signal
    tfp->dumpvars(1, "top.t.sub1a");  // Scope
    tfp->dumpvars(2, "top.t.sub1b");  // Scope
#else
#error "Bad test"
#endif

    top->trace(tfp.get(), 99);
    tfp->open(VL_STRINGIFY(TEST_OBJ_DIR) "/simx." VL_STRINGIFY(TRACE_FMT));
    top->clk = 0;

    while (main_time <= 20) {
        top->eval();
        tfp->dump((unsigned int)(main_time));
        ++main_time;
        top->clk = !top->clk;
    }
    tfp->close();
    top->final();
    tfp.reset();
    top.reset();
    printf("*-* All Finished *-*\n");
    return 0;
}
