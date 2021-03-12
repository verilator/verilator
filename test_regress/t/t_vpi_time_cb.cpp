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

#include "Vt_vpi_time_cb.h"
#include "verilated.h"
#include "svdpi.h"

#include "Vt_vpi_time_cb__Dpi.h"

#include "verilated_vpi.h"
#include "verilated_vcd_c.h"

#include "TestCheck.h"

#include <dlfcn.h>
#include <iostream>

bool errors = false;

unsigned int main_time = 0;

//======================================================================

double sc_time_stamp() { return main_time; }

int main(int argc, char** argv, char** env) {
    vluint64_t sim_time = 1100;
    Verilated::commandArgs(argc, argv);
    Verilated::debug(0);

    VM_PREFIX* topp = new VM_PREFIX("");  // Note null name - we're flattening it out

// clang-format off
#ifdef TEST_VERBOSE
    Verilated::scopesDump();
#endif
    // clang-format on

#if VM_TRACE
    Verilated::traceEverOn(true);
    VL_PRINTF("Enabling waves...\n");
    VerilatedVcdC* tfp = new VerilatedVcdC;
    topp->trace(tfp, 99);
    tfp->open(VL_STRINGIFY(TEST_OBJ_DIR) "/simx.vcd");
#endif

    // Load and initialize the PLI application
    {
        const char* filenamep = VL_STRINGIFY(TEST_OBJ_DIR) "/libvpi.so";
        void* lib = dlopen(filenamep, RTLD_LAZY);
        void* bootstrap = dlsym(lib, "vpi_compat_bootstrap");
        if (!bootstrap) {
            std::string msg = std::string("%Error: Could not dlopen ") + filenamep;
            vl_fatal(__FILE__, __LINE__, "main", msg.c_str());
        }
        ((void (*)(void))bootstrap)();
    }

    VerilatedVpi::callCbs(cbStartOfSimulation);

    topp->eval();
    topp->clk = 0;
    main_time += 1;

    while (vl_time_stamp64() < sim_time && !Verilated::gotFinish()) {
        main_time += 1;
        topp->eval();
        VerilatedVpi::callValueCbs();
        VerilatedVpi::callTimedCbs();
        TEST_CHECK(VerilatedVpi::cbNextDeadline(), main_time + 1);
        topp->clk = !topp->clk;
        // mon_do();
#if VM_TRACE
        if (tfp) tfp->dump(main_time);
#endif
    }

    VerilatedVpi::callCbs(cbEndOfSimulation);

    if (!Verilated::gotFinish()) {
        vl_fatal(__FILE__, __LINE__, "main", "%Error: Timeout; never got a $finish");
    }
    topp->final();

#if VM_TRACE
    if (tfp) tfp->close();
#endif

    VL_DO_DANGLING(delete topp, topp);
    return errors ? 10 : 0;
}
