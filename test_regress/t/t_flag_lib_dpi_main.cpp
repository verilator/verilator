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
    const std::unique_ptr<VerilatedContext> contextp{new VerilatedContext};
    contextp->commandArgs(argc, argv);

    // Construct the Verilated model, from Vtop.h generated from Verilating
    const std::unique_ptr<Vt_flag_lib_dpi> topp{new Vt_flag_lib_dpi{contextp.get()}};

    // Simulate until $finish
    while (!contextp->gotFinish()) {
        // Evaluate model
        topp->eval();
        // Advance time
        contextp->timeInc(1);
    }

    if (!contextp->gotFinish()) {
        VL_DEBUG_IF(VL_PRINTF("+ Exiting without $finish; no events left\n"););
    }

    // Final model cleanup
    topp->final();
    return 0;
}
