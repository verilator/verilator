//
// DESCRIPTION: Verilator: Verilog Multiple Model Test Module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2022 by Geza Lore.
// SPDX-License-Identifier: CC0-1.0
//

#include "verilated.h"

#include VM_PREFIX_INCLUDE

#include <memory>

int main(int argc, char** argv) {
    srand48(5);

    VerilatedContext context;
    // VL_USE_THREADS define is set in t_gantt_two.py
    context.threads(TEST_USE_THREADS);
    context.debug(0);
    context.commandArgs(argc, argv);

    VM_PREFIX topa{&context, "topa"};
    VM_PREFIX topb{&context, "topb"};

    topa.clk = false;
    topa.eval();
    topb.clk = false;
    topb.eval();

    context.timeInc(10);
    while ((context.time() < 1100) && !context.gotFinish()) {
        topa.clk = !topa.clk;
        topa.eval();
        topb.clk = !topb.clk;
        topb.eval();
        context.timeInc(5);
    }
    if (!context.gotFinish()) {
        vl_fatal(__FILE__, __LINE__, "main", "%Error: Timeout; never got a $finish");
    }
    return 0;
}
