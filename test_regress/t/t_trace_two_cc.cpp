// DESCRIPTION: Verilator: Verilog Test
//
// Copyright 2003-2020 by Wilson Snyder. This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

// clang-format off
#include "verilatedos.h"
#include VM_PREFIX_INCLUDE
#include "Vt_trace_two_b.h"
#include "verilated.h"
#ifdef TEST_HDR_TRACE
# ifdef TEST_FST
#  include "verilated_fst_c.h"
# else
#  include "verilated_vcd_c.h"
# endif
#endif
// clang-format on

// Compile in place
#include "Vt_trace_two_b__ALL.cpp"

VM_PREFIX* ap;
Vt_trace_two_b* bp;

int main(int argc, char** argv, char** env) {
    const std::unique_ptr<VerilatedContext> contextp{new VerilatedContext};

    uint64_t sim_time = 1100;
    contextp->commandArgs(argc, argv);
    contextp->debug(0);
    contextp->traceEverOn(true);
    srand48(5);
    ap = new VM_PREFIX{contextp.get(), "topa"};
    bp = new Vt_trace_two_b{contextp.get(), "topb"};

// clang-format off
#ifdef TEST_HDR_TRACE
    contextp->traceEverOn(true);
# ifdef TEST_FST
    VerilatedFstC* tfp = new VerilatedFstC;
    ap->trace(tfp, 99);
    bp->trace(tfp, 99);
    tfp->open(VL_STRINGIFY(TEST_OBJ_DIR) "/simx.fst");
# else
    VerilatedVcdC* tfp = new VerilatedVcdC;
    ap->trace(tfp, 99);
    bp->trace(tfp, 99);
    tfp->open(VL_STRINGIFY(TEST_OBJ_DIR) "/simx.vcd");
# endif
#endif
    // clang-format on

#ifdef TEST_HDR_TRACE
    ap->eval_step();
    bp->eval_step();
    ap->eval_end_step();
    bp->eval_end_step();
    if (tfp) tfp->dump(contextp->time());
#endif

    {
        ap->clk = false;
        contextp->timeInc(10);
    }
    while (contextp->time() < sim_time && !contextp->gotFinish()) {
        ap->clk = !ap->clk;
        bp->clk = ap->clk;
        ap->eval_step();
        bp->eval_step();
        ap->eval_end_step();
        bp->eval_end_step();
#ifdef TEST_HDR_TRACE
        if (tfp) tfp->dump(contextp->time());
#endif
        contextp->timeInc(5);
    }
    if (!contextp->gotFinish()) {
        vl_fatal(__FILE__, __LINE__, "main", "%Error: Timeout; never got a $finish");
    }
    ap->final();
    bp->final();

#ifdef TEST_HDR_TRACE
    if (tfp) tfp->close();
    VL_DO_DANGLING(delete tfp, tfp);
#endif

    VL_DO_DANGLING(delete ap, ap);
    VL_DO_DANGLING(delete bp, bp);
    return 0;
}
