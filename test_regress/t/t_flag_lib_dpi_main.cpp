// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Shupei Fan.
// SPDX-License-Identifier: CC0-1.0
//
//*************************************************************************
//
// DESCRIPTION: main() calling loop, created with Verilator --main

#include "verilated.h"

#include "Vt_flag_lib_dpi.h"

//======================

int main(int argc, char** argv, char**) {
    // Setup context, defaults, and parse command line
    Verilated::debug(0);
    VerilatedContext context;
    context.commandArgs(argc, argv);

    // Construct the Verilated model, from Vtop.h generated from Verilating
    Vt_flag_lib_dpi top{&context};

    // Simulate until $finish
    while (!context.gotFinish()) {
        // Evaluate model
        top.eval();
        // Advance time
        context.timeInc(1);
    }

    if (!context.gotFinish()) {
        VL_DEBUG_IF(VL_PRINTF("+ Exiting without $finish; no events left\n"););
    }

    // Final model cleanup
    top.final();
    return 0;
}
