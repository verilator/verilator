// -*- mode: C++; c-file-style: "cc-mode" -*-
//
// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2010 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

#include <verilated.h>
#include VM_PREFIX_INCLUDE

unsigned int main_time = 0;

double sc_time_stamp() { return main_time; }

VM_PREFIX* topp = nullptr;

void clockit(int clk1, int clk0) {
    topp->clks = clk1 << 1 | clk0;
#ifndef T_CLK_2IN_VEC
    topp->c1 = clk1;
    topp->c0 = clk0;
#endif
#ifdef TEST_VERBOSE
    printf("[%u] c1=%d c0=%d\n", main_time, clk1, clk0);
#endif
    topp->eval();
    main_time++;
}

int main(int argc, char* argv[]) {
    topp = new VM_PREFIX;
    topp->check = 0;
    clockit(0, 0);
    main_time += 10;

    Verilated::debug(0);

    for (int i = 0; i < 2; i++) {
        clockit(0, 0);
        clockit(0, 1);
        clockit(1, 1);
        clockit(0, 0);
        clockit(1, 1);
        clockit(1, 0);
        clockit(0, 0);
        clockit(0, 1);
        clockit(1, 0);
        clockit(0, 0);
    }
    topp->check = 1;
    clockit(0, 0);

    topp->final();
    VL_DO_DANGLING(delete topp, topp);
}
