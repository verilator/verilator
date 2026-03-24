// -*- mode: C++; c-file-style: "cc-mode" -*-
//
// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

#include <verilated.h>

#include VM_PREFIX_INCLUDE

extern "C" int sim_main(int argc, char* argv[]) {
    const std::unique_ptr<VerilatedContext> contextp{new VerilatedContext};
    const std::unique_ptr<VM_PREFIX> topp{new VM_PREFIX{contextp.get(), "top"}};

    contextp->debug(0);
    contextp->traceEverOn(true);
    contextp->commandArgs(argc, argv);

    while (!contextp->gotFinish()) {
        topp->eval();
        topp->clk = !topp->clk;
        contextp->timeInc(1);
    }

    topp->final();

    return 0;
}

int main(int argc, char* argv[]) { return sim_main(argc, argv); }
