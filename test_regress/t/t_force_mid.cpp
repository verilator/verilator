// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Test defines
#define MAIN_TIME_MULTIPLIER 1
#include <memory>
// OS header
#include "verilatedos.h"
// Generated header
#include "Vt_force_mid.h"
// General headers
#include "verilated.h"

int main(int argc, char** argv) {
    uint64_t sim_time = 1100;
    VerilatedContext context;
    Vt_force_mid top{"top"};
    context.commandArgs(argc, argv);
    context.debug(0);
    srand48(5);
    top.topin = 0x9;
    top.eval();
    {
        top.clk = false;
        context.timeInc(10 * MAIN_TIME_MULTIPLIER);
    }
    while ((context.time() < sim_time * MAIN_TIME_MULTIPLIER) && !context.gotFinish()) {
        top.clk = !top.clk;
        top.eval();
        context.timeInc(1 * MAIN_TIME_MULTIPLIER);
        context.timeInc(1 * MAIN_TIME_MULTIPLIER);
        context.timeInc(1 * MAIN_TIME_MULTIPLIER);
        context.timeInc(1 * MAIN_TIME_MULTIPLIER);
        context.timeInc(1 * MAIN_TIME_MULTIPLIER);
    }
    if (!context.gotFinish()) {
        vl_fatal(__FILE__, __LINE__, "main", "%Error: Timeout; never got a $finish");
    }
    top.final();

    return 0;
}
