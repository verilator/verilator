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

int main(int argc, char** argv) {
    VerilatedContext context;

    uint64_t sim_time = 1100;
    context.debug(0);
    context.commandArgs(argc, argv);
    context.traceEverOn(true);
    srand48(5);
    VM_PREFIX a{&context, "topa"};
    Vt_trace_two_b b{&context, "topb"};

    // clang-format off
#ifdef TEST_HDR_TRACE
    context.traceEverOn(true);
# ifdef TEST_FST
    VerilatedFstC tf;
    a.trace(&tf, 99);
    b.trace(&tf, 99);
    tf.open(VL_STRINGIFY(TEST_OBJ_DIR) "/simx.fst");
# else
    VerilatedVcdC tf;
    a.trace(&tf, 99);
    b.trace(&tf, 99);
    tf.open(VL_STRINGIFY(TEST_OBJ_DIR) "/simx.vcd");
# endif
#endif
    // clang-format on

#ifdef TEST_HDR_TRACE
    a.eval_step();
    b.eval_step();
    a.eval_end_step();
    b.eval_end_step();
    tf.dump(context.time());
#endif

    {
        a.clk = false;
        context.timeInc(10);
    }
    while (context.time() < sim_time && !context.gotFinish()) {
        a.clk = !a.clk;
        b.clk = a.clk;
        a.eval_step();
        b.eval_step();
        a.eval_end_step();
        b.eval_end_step();
#ifdef TEST_HDR_TRACE
        tf.dump(context.time());
#endif
        context.timeInc(5);
    }
    if (!context.gotFinish()) {
        vl_fatal(__FILE__, __LINE__, "main", "%Error: Timeout; never got a $finish");
    }
    a.final();
    b.final();

#ifdef TEST_HDR_TRACE
    tf.close();
#endif

    return 0;
}
