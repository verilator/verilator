// -*- mode: C++; c-file-style: "cc-mode" -*-
//
// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2022 by Todd Strader.
// SPDX-License-Identifier: CC0-1.0

// Generated header
#include "Vt_public_clk.h"
#include "Vt_public_clk___024root.h"
// General headers
#include "verilated.h"

int main(int argc, char** argv) {
    vluint64_t sim_time = 1100;
    VerilatedContext context;
    context.debug(0);
    context.commandArgs(argc, argv);
    srand48(5);
    VM_PREFIX top{"top"};

    top.rootp->t__DOT__clk = 0;
    top.eval();
    { context.timeInc(10); }

    while ((context.time() < sim_time) && !context.gotFinish()) {
        top.rootp->t__DOT__clk = !top.rootp->t__DOT__clk;
        top.eval();
        context.timeInc(5);
    }

    if (!context.gotFinish()) {
        vl_fatal(__FILE__, __LINE__, "main", "%Error: Timeout; never got a $finish");
    }
    top.final();

    return 0;
}
