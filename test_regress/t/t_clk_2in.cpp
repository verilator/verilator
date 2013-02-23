// -*- mode: C++; c-file-style: "cc-mode" -*-
//
// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2010 by Wilson Snyder.

#include <verilated.h>
#ifdef T_CLK_2IN_VEC
# include "Vt_clk_2in_vec.h"
#else
# include "Vt_clk_2in.h"
#endif

unsigned int main_time = false;

double sc_time_stamp () {
    return main_time;
}

VM_PREFIX* topp = NULL;

void clockit(int clk1, int clk0) {
    topp->clks = clk1<<1 | clk0;
#ifndef T_CLK_2IN_VEC
    topp->c1 = clk1;
    topp->c0 = clk0;
#endif
#ifdef TEST_VERBOSE
    printf("[%d] c1=%d c0=%d\n", main_time, clk1, clk0);
#endif
    topp->eval();
    main_time++;
}

int main (int argc, char *argv[]) {
    topp = new VM_PREFIX;
    topp->check = 0;
    clockit(0,0);
    main_time+=10;

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
    clockit(0,0);
}
