// -*- mode: C++; c-file-style: "cc-mode" -*-
//
// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2008 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

#include <verilated.h>
#include <verilated_vcd_c.h>

#include VM_PREFIX_INCLUDE
#ifdef T_TRACE_PUBLIC_SIG_VLT
# include "Vt_trace_public_sig_vlt_t.h"
# include "Vt_trace_public_sig_vlt_glbl.h"
#else
# include "Vt_trace_public_sig_t.h"
# include "Vt_trace_public_sig_glbl.h"
#endif

unsigned long long main_time = 0;
double sc_time_stamp() { return (double)main_time; }

const unsigned long long dt_2 = 3;

int main(int argc, char** argv, char** env) {
    VM_PREFIX* top = new VM_PREFIX("top");

    Verilated::debug(0);
    Verilated::traceEverOn(true);

    VerilatedVcdC* tfp = new VerilatedVcdC;
    top->trace(tfp, 99);
    tfp->open(VL_STRINGIFY(TEST_OBJ_DIR) "/simx.vcd");

    while (main_time <= 20) {
        top->CLK = (main_time / dt_2) % 2;
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
