// -*- mode: C++; c-file-style: "cc-mode" -*-
//
// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2008 by Wilson Snyder.

#include <verilated.h>
#include <verilated_vcd_c.h>

#include "Vt_trace_public_sig.h"
#include "Vt_trace_public_sig_t.h"
#include "Vt_trace_public_sig_glbl.h"

#define STRINGIFY(x) STRINGIFY2(x)
#define STRINGIFY2(x) #x

unsigned long long main_time = 0;
double sc_time_stamp() {
    return (double)main_time;
}

const unsigned long long dt_2 = 3;

int main(int argc, char **argv, char **env) {
    Vt_trace_public_sig *top = new Vt_trace_public_sig("top");

    Verilated::debug(0);
    Verilated::traceEverOn(true);

    VerilatedVcdC* tfp = new VerilatedVcdC;
    top->trace(tfp,99);
    tfp->open(STRINGIFY(TEST_OBJ_DIR) "/simx.vcd");

    while (main_time <= 20) {
        top->CLK   = (main_time/dt_2)%2;
        top->eval();

        top->t->glbl->GSR = (main_time < 7);

        tfp->dump((unsigned int)(main_time));
        ++main_time;
    }
    tfp->close();
    top->final();
    printf("*-* All Finished *-*\n");
    return 0;
}
