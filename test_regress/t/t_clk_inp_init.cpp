// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2020 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Test defines
// Generated header
#include "Vt_clk_inp_init.h"
// General headers
#include "verilated.h"

void oneTest(int argc, char** argv, int seed) {
    uint64_t sim_time = 1000;

#ifdef TEST_VERBOSE
    VL_PRINTF("== Seed=%d\n", seed);
#endif

    const std::unique_ptr<VerilatedContext> contextp{new VerilatedContext};
    contextp->commandArgs(argc, argv);

    // Randomise initial state
    srand48(seed);
    srand48(5);
    contextp->randReset(123);

    // Construct the Verilated model, from Vtop.h generated from Verilating
    const std::unique_ptr<Vt_clk_inp_init> topp{new Vt_clk_inp_init{contextp.get()}};

    // Start not in reset
    topp->rst_n = 1;
    topp->clk = 0;
    topp->eval();

    // Tick for a little bit
    while (contextp->time() < sim_time && !contextp->gotFinish()) {
        topp->clk = 0;
        topp->eval();

        contextp->timeInc(5);

        topp->clk = 1;
        topp->eval();

        contextp->timeInc(5);
    }

    if (!contextp->gotFinish()) {
        vl_fatal(__FILE__, __LINE__, "main", "%Error: Timeout; never got a $finish");
    }

    topp->final();
}

int main(int argc, char** argv, char** env) {
#if VL_DEBUG
    // Verilated::debug(1);
#endif

    for (int seed = 123; seed < 133; ++seed) oneTest(argc, argv, seed);

    return 0;
}
