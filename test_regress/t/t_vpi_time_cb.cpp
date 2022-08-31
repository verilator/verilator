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

int main(int argc, char** argv, char** env) {
    const std::unique_ptr<VerilatedContext> contextp{new VerilatedContext};

    uint64_t sim_time = 1100;
    contextp->commandArgs(argc, argv);
    contextp->debug(0);

    const std::unique_ptr<VM_PREFIX> topp{new VM_PREFIX{contextp.get(),
                                                        // Note null name - we're flattening it out
                                                        ""}};

// clang-format off
#ifdef TEST_VERBOSE
    contextp->scopesDump();
#endif
    // clang-format on

#if VM_TRACE
    contextp->traceEverOn(true);
    VL_PRINTF("Enabling waves...\n");
    VerilatedVcdC* tfp = new VerilatedVcdC;
    topp->trace(tfp, 99);
    tfp->open(VL_STRINGIFY(TEST_OBJ_DIR) "/simx.vcd");
#endif

    VerilatedVpi::callCbs(cbStartOfSimulation);

    topp->eval();
    topp->clk = 0;

    while (vl_time_stamp64() < sim_time && !contextp->gotFinish()) {
        contextp->timeInc(1);
        topp->eval();
        VerilatedVpi::callValueCbs();
        VerilatedVpi::callTimedCbs();
        if (contextp->time() > 20) {  // Else haven't registered callbacks
            TEST_CHECK_EQ(VerilatedVpi::cbNextDeadline(), contextp->time() + 1);
        }
        if ((contextp->time() % 5) == 0) topp->clk = !topp->clk;
            // mon_do();
#if VM_TRACE
        if (tfp) tfp->dump(contextp->time());
#endif
    }

    VerilatedVpi::callCbs(cbEndOfSimulation);

    if (!contextp->gotFinish()) {
        vl_fatal(__FILE__, __LINE__, "main", "%Error: Timeout; never got a $finish");
    }
    topp->final();

#if VM_TRACE
    if (tfp) tfp->close();
#endif

    return errors ? 10 : 0;
}
