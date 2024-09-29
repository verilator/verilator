// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2020 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

#include VM_PREFIX_INCLUDE

void oneTest(int argc, char** argv, int seed) {
    uint64_t sim_time = 1000;

#ifdef TEST_VERBOSE
    VL_PRINTF("== Seed=%d\n", seed);
#endif

    VerilatedContext context;
    context.commandArgs(argc, argv);

    // Randomise initial state
    srand48(seed);
    srand48(5);
    context.randReset(123);

    // Construct the Verilated model, from Vtop.h generated from Verilating
    VM_PREFIX top{&context};

    // Start not in reset
    top.rst_n = 1;
    top.clk = 0;
    top.eval();

    // Tick for a little bit
    while (context.time() < sim_time && !context.gotFinish()) {
        top.clk = 0;
        top.eval();

        context.timeInc(5);

        top.clk = 1;
        top.eval();

        context.timeInc(5);
    }

    if (!context.gotFinish()) {
        vl_fatal(__FILE__, __LINE__, "main", "%Error: Timeout; never got a $finish");
    }

    top.final();
}

int main(int argc, char** argv) {
#if VL_DEBUG
    // Verilated::debug(1);
#endif

    for (int seed = 123; seed < 133; ++seed) oneTest(argc, argv, seed);

    return 0;
}
