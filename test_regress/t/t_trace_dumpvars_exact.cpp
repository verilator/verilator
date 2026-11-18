// -*- mode: C++; c-file-style: "cc-mode" -*-
//
// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

#include <verilated.h>
#include VL_STRINGIFY(TRACE_HEADER_C)

#include <memory>
#include <string>
#include <vector>

#include VM_PREFIX_INCLUDE

unsigned long long main_time = 0;
double sc_time_stamp() { return (double)main_time; }

int main(int argc, char** argv) {
    Verilated::debug(0);
    Verilated::traceEverOn(true);
    Verilated::commandArgs(argc, argv);

    std::unique_ptr<VM_PREFIX> top{new VM_PREFIX{"top.inst"}};

    std::unique_ptr<VERILATED_TRACE_C> tfp{new VERILATED_TRACE_C};

    tfp->dumpvarsExact("top.inst t cyc");  // A dot inside the model name
    tfp->dumpvarsExact("top.inst t sub1a value");
    tfp->dumpvarsExact("top.inst t sub1b sub2a");  // A scope, not a signal
    tfp->dumpvarsExact("top.inst.t.cyc");  // Dots are not separators

    top->trace(tfp.get(), 99);
    tfp->open(VL_STRINGIFY(TEST_OBJ_DIR) "/simx." VL_STRINGIFY(TRACE_FMT));
    top->clk = 0;

    const std::vector<std::string> unmatched = tfp->dumpvarsUnmatched();
    const std::vector<std::string> expected{"top.inst t sub1b sub2a", "top.inst.t.cyc"};
    if (unmatched != expected) {
        for (const std::string& name : unmatched) printf("Unmatched: %s\n", name.c_str());
        printf("%%Error: unexpected dumpvarsUnmatched()\n");
        return 1;
    }

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
