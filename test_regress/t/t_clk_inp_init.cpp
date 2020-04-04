// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2020 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Test defines
// Generated header
#include "Vt_clk_inp_init.h"
// General headers
#include "verilated.h"

Vt_clk_inp_init* topp;

vluint64_t main_time;
double sc_time_stamp() { return main_time; }

void oneTest(int seed) {
    double sim_time = 1000;

#ifdef TEST_VERBOSE
    VL_PRINTF("== Seed=%d\n", seed);
#endif

    // Randomise initial state
    srand48(seed);
    srand48(5);
    Verilated::randReset(123);

    topp = new Vt_clk_inp_init("top");

    // Start not in reset
    topp->rst_n = 1;
    topp->clk = 0;
    topp->eval();

    // Tick for a little bit
    while (sc_time_stamp() < sim_time && !Verilated::gotFinish()) {
        topp->clk = 0;
        topp->eval();

        main_time += 5;

        topp->clk = 1;
        topp->eval();

        main_time += 5;
    }

    if (!Verilated::gotFinish()) {
        vl_fatal(__FILE__, __LINE__, "main", "%Error: Timeout; never got a $finish");
    }

    topp->final();
    VL_DO_DANGLING(delete topp, topp);
}

int main(int argc, char** argv, char** env) {
    Verilated::commandArgs(argc, argv);
#if VL_DEBUG
    // Verilated::debug(1);
#endif

    for (int seed = 123; seed < 133; ++seed) {
        oneTest(seed);
    }

    return 0;
}
