// DESCRIPTION: Verilator: Verilog Test
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2003-2020 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

// clang-format off
#include "verilatedos.h"
#include VM_PREFIX_INCLUDE
#include "Vt_trace_two_b.h"
#include "verilated.h"
#ifdef TEST_HDR_TRACE
#  include VL_STRINGIFY(TRACE_HEADER_C)
#endif
// clang-format on

// Compile in place
#include "Vt_trace_two_b__ALL.cpp"

VM_PREFIX* ap;
Vt_trace_two_b* bp;

int main(int argc, char** argv) {
    VerilatedContext context{};

    uint64_t sim_time = 1100;
    context.debug(0);
    context.commandArgs(argc, argv);
    context.traceEverOn(true);
    srand48(5);
    ap = new VM_PREFIX{&context, "topa"};
    bp = new Vt_trace_two_b{&context, "topb"};

#ifdef TEST_HDR_TRACE
    VERILATED_TRACE_C* tfp = new VERILATED_TRACE_C;
    ap->trace(tfp, 99);
    bp->trace(tfp, 99);
    tfp->open(VL_STRINGIFY(TEST_OBJ_DIR) "/simx." VL_STRINGIFY(TRACE_FMT));

    ap->eval_step();
    bp->eval_step();
    ap->eval_end_step();
    bp->eval_end_step();
    if (tfp) tfp->dump(context.time());
#endif

    {
        ap->clk = false;
        context.timeInc(10);
    }
    while (context.time() < sim_time && !context.gotFinish()) {
        ap->clk = !ap->clk;
        bp->clk = ap->clk;
        ap->eval_step();
        bp->eval_step();
        ap->eval_end_step();
        bp->eval_end_step();
#ifdef TEST_HDR_TRACE
        if (tfp) tfp->dump(context.time());
#endif
        context.timeInc(5);
    }
    if (!context.gotFinish()) {
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
