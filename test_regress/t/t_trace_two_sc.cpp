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
# include "verilated_vcd_sc.h"
#endif
// clang-format on

// Compile in place
#include "Vt_trace_two_b__ALL.cpp"

// General headers
#include "verilated.h"
#include "systemc.h"

VM_PREFIX* ap;
Vt_trace_two_b* bp;

int sc_main(int argc, char** argv) {
    sc_signal<bool> clk;
    sc_time sim_time(1100, SC_NS);
    Verilated::commandArgs(argc, argv);
    Verilated::traceEverOn(true);
    Verilated::debug(0);
    srand48(5);
    ap = new VM_PREFIX{"topa"};
    bp = new Vt_trace_two_b{"topb"};
    ap->clk(clk);
    bp->clk(clk);

#ifdef TEST_HDR_TRACE
    VerilatedVcdSc* tfp = new VerilatedVcdSc;
    sc_core::sc_start(sc_core::SC_ZERO_TIME);
    ap->trace(tfp, 99);
    bp->trace(tfp, 99);
    tfp->open(VL_STRINGIFY(TEST_OBJ_DIR) "/simx.vcd");
#endif
    {
        clk = false;
        sc_start(10, SC_NS);
    }
    while (sc_time_stamp() < sim_time && !Verilated::gotFinish()) {
        clk = !clk;
        sc_start(5, SC_NS);
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
    return 0;
}
