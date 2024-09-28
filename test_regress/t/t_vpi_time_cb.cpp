// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
//
// Copyright 2010-2011 by Wilson Snyder. This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#include "verilated.h"
#include "verilated_vcd_c.h"
#include "verilated_vpi.h"

#include "Vt_vpi_time_cb.h"
#include "Vt_vpi_time_cb__Dpi.h"
#include "svdpi.h"

#include <iostream>

// These require the above. Comment prevents clang-format moving them
#include "TestCheck.h"

//======================================================================

int main(int argc, char** argv) {
    VerilatedContext context;

    uint64_t sim_time = 1100;
    context.debug(0);
    context.commandArgs(argc, argv);

    VM_PREFIX top{&context, ""};  // Note null name - we're flattening it out

#ifdef TEST_VERBOSE
    context.scopesDump();
#endif

#if VM_TRACE
    context.traceEverOn(true);
    VL_PRINTF("Enabling waves...\n");
    VerilatedVcdC tf;
    top.trace(&tf, 99);
    tf.open(VL_STRINGIFY(TEST_OBJ_DIR) "/simx.vcd");
#endif

    VerilatedVpi::callCbs(cbStartOfSimulation);

    top.eval();
    top.clk = 0;

    while (vl_time_stamp64() < sim_time && !context.gotFinish()) {
        context.timeInc(1);
        top.eval();
        VerilatedVpi::callValueCbs();
        VerilatedVpi::callTimedCbs();
        if (context.time() > 20) {  // Else haven't registered callbacks
            TEST_CHECK_EQ(VerilatedVpi::cbNextDeadline(), context.time() + 1);
        }
        if ((context.time() % 5) == 0) top.clk = !top.clk;
            // mon_do();
#if VM_TRACE
        tf.dump(context.time());
#endif
    }

    VerilatedVpi::callCbs(cbEndOfSimulation);

    if (!context.gotFinish()) {
        vl_fatal(__FILE__, __LINE__, "main", "%Error: Timeout; never got a $finish");
    }
    top.final();

#if VM_TRACE
    tf.close();
#endif

    return errors ? 10 : 0;
}
