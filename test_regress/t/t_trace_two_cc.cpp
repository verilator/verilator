// DESCRIPTION: Verilator: Verilog Test
//
// Copyright 2003-2020 by Wilson Snyder. This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

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

// Compile in place
#include "Vt_trace_two_b.cpp"
#include "Vt_trace_two_b__Syms.cpp"
#include "Vt_trace_two_b__Trace.cpp"
#include "Vt_trace_two_b__Trace__Slow.cpp"

VM_PREFIX* ap;
Vt_trace_two_b* bp;
vluint64_t main_time = 0;
double sc_time_stamp() { return main_time; }

int main(int argc, char** argv, char** env) {
    double sim_time = 1100;
    Verilated::commandArgs(argc, argv);
    Verilated::debug(0);
    Verilated::traceEverOn(true);
    srand48(5);
    ap = new VM_PREFIX("topa");
    bp = new Vt_trace_two_b("topb");

#ifdef TEST_HDR_TRACE
    Verilated::traceEverOn(true);
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

#ifdef TEST_HDR_TRACE
    ap->eval_step();
    bp->eval_step();
    ap->eval_end_step();
    bp->eval_end_step();
    if (tfp) tfp->dump(main_time);
#endif

    {
        ap->clk = false;
        ap->clk = false;
        main_time += 10;
    }
    while (sc_time_stamp() < sim_time && !Verilated::gotFinish()) {
        ap->clk = !ap->clk;
        bp->clk = ap->clk;
        ap->eval_step();
        bp->eval_step();
        ap->eval_end_step();
        bp->eval_end_step();
#ifdef TEST_HDR_TRACE
        if (tfp) tfp->dump(main_time);
#endif
        main_time += 5;
    }
    if (!Verilated::gotFinish()) {
        vl_fatal(__FILE__, __LINE__, "main", "%Error: Timeout; never got a $finish");
    }
    ap->final();
    bp->final();

#ifdef TEST_HDR_TRACE
    if (tfp) tfp->close();
#endif

    VL_DO_DANGLING(delete ap, ap);
    VL_DO_DANGLING(delete bp, bp);
    exit(0L);
}
