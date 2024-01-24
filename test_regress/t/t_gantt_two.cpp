//
// DESCRIPTION: Verilator: Verilog Multiple Model Test Module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2022 by Geza Lore.
// SPDX-License-Identifier: CC0-1.0
//

#include "verilated.h"

#include VM_PREFIX_INCLUDE

#include <memory>

int main(int argc, char** argv) {
    srand48(5);

    const std::unique_ptr<VerilatedContext> contextp{new VerilatedContext};
    // VL_USE_THREADS define is set in t_gantt_two.pl
    contextp->threads(TEST_USE_THREADS);
    contextp->debug(0);
    contextp->commandArgs(argc, argv);

    std::unique_ptr<VM_PREFIX> topap{new VM_PREFIX{contextp.get(), "topa"}};
    std::unique_ptr<VM_PREFIX> topbp{new VM_PREFIX{contextp.get(), "topb"}};

    topap->clk = false;
    topap->eval();
    topbp->clk = false;
    topbp->eval();

    contextp->timeInc(10);
    while ((contextp->time() < 1100) && !contextp->gotFinish()) {
        topap->clk = !topap->clk;
        topap->eval();
        topbp->clk = !topbp->clk;
        topbp->eval();
        contextp->timeInc(5);
    }
    if (!contextp->gotFinish()) {
        vl_fatal(__FILE__, __LINE__, "main", "%Error: Timeout; never got a $finish");
    }
    return 0;
}
