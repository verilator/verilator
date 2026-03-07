// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

#include <verilated.h>

#include "Vt_covergroup_cross_large.h"

int main(int argc, char** argv) {
    const std::unique_ptr<VerilatedContext> contextp{new VerilatedContext};
    contextp->commandArgs(argc, argv);
    const std::unique_ptr<Vt_covergroup_cross_large> topp{
        new Vt_covergroup_cross_large{contextp.get()}};

    topp->clk = 0;

    while (!contextp->gotFinish() && contextp->time() < 100) {
        topp->clk = !topp->clk;
        topp->eval();
        contextp->timeInc(1);
    }

    topp->final();
    contextp->coveragep()->write();

    return 0;
}
