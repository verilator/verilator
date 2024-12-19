// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
//
// Copyright 2010-2023 by Wilson Snyder. This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#ifdef IS_VPI

#include "vpi_user.h"

#include <cstdlib>

#else

#include "verilated.h"
#include "verilated_vcd_c.h"
#include "verilated_vpi.h"

#include VM_PREFIX_INCLUDE
#ifdef T_VPI_PUBLIC_DEPTH
#include "Vt_vpi_public_depth__Dpi.h"
#elif defined(T_VPI_PUBLIC_DEPTH_OFF)
#include "Vt_vpi_public_depth_off__Dpi.h"
#else
#error "Bad test"
#endif
#include "svdpi.h"

#endif

#include <cstdio>
#include <cstring>
#include <iostream>

// These require the above. Comment prevents clang-format moving them
#include "TestSimulator.h"
#include "TestVpi.h"

void modDump(const TestVpiHandle& it, int n) {
    while (TestVpiHandle hndl = vpi_scan(it)) {
        const char* nm = vpi_get_str(vpiName, hndl);
        for (int i = 0; i < n; i++) printf("    ");
        printf("%s\n", nm);
        TestVpiHandle subIt = vpi_iterate(vpiModule, hndl);
        if (subIt) modDump(subIt, n + 1);
    }
}

extern "C" {
int mon_check() {
#ifdef TEST_VERBOSE
    printf("-mon_check()\n");
#endif

    TestVpiHandle it = vpi_iterate(vpiModule, NULL);
    CHECK_RESULT_NZ(it);
    // Uncomment to see what other simulators return
    // modDump(it, 0);
    // return 1;

    TestVpiHandle topmod;
    // both somepackage and t exist at the top level
    while ((topmod = vpi_scan(it))) {
        if (vpi_get(vpiType, topmod) == vpiModule) break;
    }
    CHECK_RESULT_NZ(topmod);

    const char* t_name = vpi_get_str(vpiName, topmod);
    CHECK_RESULT_NZ(t_name);

    // Icarus reports the top most module as "top"
    if (std::strcmp(t_name, "top") == 0) {
        it = vpi_iterate(vpiModule, topmod);
        CHECK_RESULT_NZ(it);
        CHECK_RESULT(vpi_get(vpiType, it), vpiModule);
        topmod = vpi_scan(it);
        t_name = vpi_get_str(vpiName, topmod);
        CHECK_RESULT_NZ(t_name);
    }
    CHECK_RESULT_CSTR(t_name, "t");
    TestVpiHandle topmod_done_should_be_0 = (vpi_scan(it));
    it.freed();  // IEEE 37.2.2 vpi_scan at end does a vpi_release_handle
    CHECK_RESULT_Z(topmod_done_should_be_0);

    TestVpiHandle it2 = vpi_iterate(vpiModule, topmod);
    CHECK_RESULT_NZ(it2);

    TestVpiHandle mod2 = vpi_scan(it2);
    CHECK_RESULT_NZ(mod2);

    const char* mod_a_name = vpi_get_str(vpiName, mod2);
    CHECK_RESULT_CSTR(mod_a_name, "\\mod.a ");

    TestVpiHandle it3 = vpi_iterate(vpiModule, mod2);

#ifdef T_VPI_PUBLIC_DEPTH
    CHECK_RESULT_NZ(it3);
    TestVpiHandle mod3 = vpi_scan(it3);
    CHECK_RESULT_NZ(mod3);

    const char* mod_c_name = vpi_get_str(vpiName, mod3);
    if (std::strcmp(mod_c_name, "\\mod_b$ ") == 0) {
        // Full visibility in other simulators, skip mod_b
        TestVpiHandle mod4 = vpi_scan(it3);
        CHECK_RESULT_NZ(mod4);
        mod_c_name = vpi_get_str(vpiName, mod4);
    }
    CHECK_RESULT_CSTR(mod_c_name, "\\mod\\c$ ");

#elif defined(T_VPI_PUBLIC_DEPTH_OFF)
    CHECK_RESULT_Z(it3);
#endif

    return 0;  // Ok
}
}
//======================================================================

#ifdef IS_VPI

static int mon_check_vpi() {
    TestVpiHandle href = vpi_handle(vpiSysTfCall, 0);
    s_vpi_value vpi_value;

    vpi_value.format = vpiIntVal;
    vpi_value.value.integer = mon_check();
    vpi_put_value(href, &vpi_value, NULL, vpiNoDelay);

    return 0;
}

static s_vpi_systf_data vpi_systf_data[] = {{vpiSysFunc, vpiIntFunc, (PLI_BYTE8*)"$mon_check",
                                             (PLI_INT32(*)(PLI_BYTE8*))mon_check_vpi, 0, 0, 0},
                                            0};

// cver entry
void vpi_compat_bootstrap(void) {
    p_vpi_systf_data systf_data_p;
    systf_data_p = &(vpi_systf_data[0]);
    while (systf_data_p->type != 0) vpi_register_systf(systf_data_p++);
}

// icarus entry
void (*vlog_startup_routines[])() = {vpi_compat_bootstrap, 0};

#else

int main(int argc, char** argv) {
    const std::unique_ptr<VerilatedContext> contextp{new VerilatedContext};

    uint64_t sim_time = 1100;
    contextp->debug(0);
    contextp->commandArgs(argc, argv);
    // We're going to be checking for these errors so don't crash out
    contextp->fatalOnVpiError(0);

    {
        // Construct and destroy
        const std::unique_ptr<VM_PREFIX> topp{
            new VM_PREFIX{contextp.get(),
                          // Note null name - we're flattening it out
                          ""}};
    }

    // Test second construction
    const std::unique_ptr<VM_PREFIX> topp{new VM_PREFIX{contextp.get(),
                                                        // Note null name - we're flattening it out
                                                        ""}};

#ifdef VERILATOR
#ifdef TEST_VERBOSE
    contextp->scopesDump();
#endif
#endif

#if VM_TRACE
    contextp->traceEverOn(true);
    VL_PRINTF("Enabling waves...\n");
    VerilatedVcdC* tfp = new VerilatedVcdC;
    topp->trace(tfp, 99);
    tfp->open(STRINGIFY(TEST_OBJ_DIR) "/simx.vcd");
#endif

    topp->eval();
    topp->clk = 0;
    contextp->timeInc(10);

    while (contextp->time() < sim_time && !contextp->gotFinish()) {
        contextp->timeInc(1);
        topp->eval();
        VerilatedVpi::callValueCbs();
        topp->clk = !topp->clk;
        // mon_do();
#if VM_TRACE
        if (tfp) tfp->dump(contextp->time());
#endif
    }
    if (!contextp->gotFinish()) {
        vl_fatal(FILENM, __LINE__, "main", "%Error: Timeout; never got a $finish");
    }
    topp->final();

#if VM_TRACE
    if (tfp) tfp->close();
#endif

    return 0;
}

#endif
