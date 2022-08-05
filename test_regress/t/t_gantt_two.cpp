//
// DESCRIPTION: Verilator: Verilog Multiple Model Test Module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2022 by Geza Lore.
// SPDX-License-Identifier: CC0-1.0
//

#include "verilated.h"

#include "Vt_gantt_two.h"

#include <memory>

int main(int argc, char** argv, char** env) {
    srand48(5);

    const std::unique_ptr<VerilatedContext> contextp{new VerilatedContext};
#ifdef VL_THREADED
    contextp->threads(2);
#endif
    contextp->commandArgs(argc, argv);
    contextp->debug(0);

    std::unique_ptr<Vt_gantt_two> topap{new Vt_gantt_two{contextp.get(), "topa"}};
    std::unique_ptr<Vt_gantt_two> topbp{new Vt_gantt_two{contextp.get(), "topb"}};

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
