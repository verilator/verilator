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
std::unique_ptr<Vt_force_mid> topp;
int main(int argc, char** argv) {
    uint64_t sim_time = 1100;
    const std::unique_ptr<VerilatedContext> contextp{new VerilatedContext};
    contextp->commandArgs(argc, argv);
    contextp->debug(0);
    srand48(5);
    topp.reset(new Vt_force_mid{"top"});
    topp->topin = 0x9;
    topp->eval();
    {
        topp->clk = false;
        contextp->timeInc(10 * MAIN_TIME_MULTIPLIER);
    }
    while ((contextp->time() < sim_time * MAIN_TIME_MULTIPLIER) && !contextp->gotFinish()) {
        topp->clk = !topp->clk;
        topp->eval();
        contextp->timeInc(1 * MAIN_TIME_MULTIPLIER);
        contextp->timeInc(1 * MAIN_TIME_MULTIPLIER);
        contextp->timeInc(1 * MAIN_TIME_MULTIPLIER);
        contextp->timeInc(1 * MAIN_TIME_MULTIPLIER);
        contextp->timeInc(1 * MAIN_TIME_MULTIPLIER);
    }
    if (!contextp->gotFinish()) {
        vl_fatal(__FILE__, __LINE__, "main", "%Error: Timeout; never got a $finish");
    }
    topp->final();

    topp.reset();
    return 0;
}
