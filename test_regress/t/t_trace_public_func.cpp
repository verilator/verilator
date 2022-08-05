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

int main(int argc, char** argv, char** env) {
    std::unique_ptr<VM_PREFIX> top{new VM_PREFIX("top")};

    Verilated::debug(0);
    Verilated::traceEverOn(true);

    std::unique_ptr<VerilatedVcdC> tfp{new VerilatedVcdC};
    top->trace(tfp.get(), 99);
    tfp->open(VL_STRINGIFY(TEST_OBJ_DIR) "/simx.vcd");

    while (main_time <= 20) {
        top->CLK = (main_time / dt_2) % 2;
        top->eval();

        top->t->glbl->setGSR(main_time < 7);

        tfp->dump((unsigned int)(main_time));
        ++main_time;
    }
    tfp->close();
    top->final();
    tfp.reset();
    top.reset();
    printf("*-* All Finished *-*\n");
    return 0;
}
