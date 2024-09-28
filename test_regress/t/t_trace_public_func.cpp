// -*- mode: C++; c-file-style: "cc-mode" -*-
//
// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2008 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

#include <verilated.h>
#include <verilated_vcd_c.h>

#include <memory>

// clang-format off
#include VM_PREFIX_INCLUDE
#ifdef T_TRACE_PUBLIC_FUNC_VLT
# include "Vt_trace_public_func_vlt_t.h"
# include "Vt_trace_public_func_vlt_glbl.h"
#else
# include "Vt_trace_public_func_t.h"
# include "Vt_trace_public_func_glbl.h"
#endif
// clang-format on

unsigned long long main_time = 0;
double sc_time_stamp() { return (double)main_time; }

const unsigned long long dt_2 = 3;

int main(int argc, char** argv) {
    Verilated::debug(0);
    Verilated::traceEverOn(true);
    Verilated::commandArgs(argc, argv);

    {
        VM_PREFIX top{"top"};

        VerilatedVcdC tf;
        top.trace(&tf, 99);
        tf.open(VL_STRINGIFY(TEST_OBJ_DIR) "/simx.vcd");

        while (main_time <= 20) {
            top.CLK = (main_time / dt_2) % 2;
            top.eval();

            top.t->glbl->setGSR(main_time < 7);

            tf.dump((unsigned int)(main_time));
            ++main_time;
        }
        tf.close();
        top.final();
    }

    printf("*-* All Finished *-*\n");
    return 0;
}
