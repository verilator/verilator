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

#ifdef IS_VPI

#include "vpi_user.h"
#include <cstdlib>

#else

#include "Vt_vpi_module.h"
#include "verilated.h"
#include "svdpi.h"

#include "Vt_vpi_module__Dpi.h"

#include "verilated_vpi.h"
#include "verilated_vcd_c.h"

#endif

#include <cstdio>
#include <cstring>
#include <iostream>

#include "TestSimulator.h"
#include "TestVpi.h"

// __FILE__ is too long
#define FILENM "t_vpi_module.cpp"

#define DEBUG \
    if (0) printf

unsigned int main_time = 0;

#define CHECK_RESULT_NZ(got) \
    if (!(got)) { \
        printf("%%Error: %s:%d: GOT = NULL  EXP = !NULL\n", FILENM, __LINE__); \
        return __LINE__; \
    }

#define CHECK_RESULT_Z(got) \
    if (got) { \
        printf("%%Error: %s:%d: GOT = !NULL  EXP = NULL\n", FILENM, __LINE__); \
        return __LINE__; \
    }

#define CHECK_RESULT_CSTR(got, exp) \
    if (strcmp((got), (exp))) { \
        printf("%%Error: %s:%d: GOT = '%s'   EXP = '%s'\n", FILENM, __LINE__, \
               (got) ? (got) : "<null>", (exp) ? (exp) : "<null>"); \
        return __LINE__; \
    }

void modDump(const TestVpiHandle& it, int n) {
    while (TestVpiHandle hndl = vpi_scan(it)) {
        const char* nm = vpi_get_str(vpiName, hndl);
        for (int i = 0; i < n; i++)
            printf("    ");
        printf("%s\n", nm);
        TestVpiHandle subIt = vpi_iterate(vpiModule, hndl);
        if (subIt)
            modDump(subIt, n+1);
    }
}

extern "C" {
int mon_check() {
    TestVpiHandle root_it = vpi_iterate(vpiModule, NULL);
#ifdef IS_ICARUS
    // Icarus segfaults when some VPI handles are freed
    root_it.nofree();
#endif
    CHECK_RESULT_NZ(root_it);
    // Uncomment to see what other simulators return
    //modDump(root_it, 0);
    //return 1;

    TestVpiHandle topmod = vpi_scan(root_it);
    CHECK_RESULT_NZ(topmod);

    const char* t_name = vpi_get_str(vpiName, topmod);
    CHECK_RESULT_NZ(t_name);

    // Icarus reports the top most module as "top"
    if (strcmp(t_name, "top") == 0) {
        root_it = vpi_iterate(vpiModule, topmod);
        CHECK_RESULT_NZ(root_it);
        topmod = vpi_scan(root_it);
        t_name = vpi_get_str(vpiName, topmod);
        CHECK_RESULT_NZ(t_name);
    }
    CHECK_RESULT_CSTR(t_name, "t");
    TestVpiHandle topmod_done = (vpi_scan(root_it));
    CHECK_RESULT_Z(topmod_done);

    TestVpiHandle topmod_it = vpi_iterate(vpiModule, topmod);
#ifdef IS_ICARUS
    topmod_it.nofree();
#endif
    CHECK_RESULT_NZ(topmod_it);

    TestVpiHandle mod = vpi_scan(topmod_it);
    CHECK_RESULT_NZ(mod);

    const char* mod_a_name = vpi_get_str(vpiName, mod);
    CHECK_RESULT_CSTR(mod_a_name, "mod_a");
    TestVpiHandle t_done = (vpi_scan(topmod_it));
    CHECK_RESULT_Z(t_done);

    TestVpiHandle sub_a_it = vpi_iterate(vpiModule, mod);
    CHECK_RESULT_NZ(sub_a_it);

    TestVpiHandle sub_a_mod = vpi_scan(sub_a_it);
    CHECK_RESULT_NZ(sub_a_mod);

    const char* mod_c_name = vpi_get_str(vpiName, sub_a_mod);
    if (strcmp(mod_c_name, "mod_b") == 0) {
        // Full visibility in other simulators, skip mod_b
        sub_a_mod = vpi_scan(sub_a_it);
        CHECK_RESULT_NZ(sub_a_mod);
        mod_c_name = vpi_get_str(vpiName, sub_a_mod);
    }
    CHECK_RESULT_CSTR(mod_c_name, "mod_c.");

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

double sc_time_stamp() { return main_time; }
int main(int argc, char** argv, char** env) {
    double sim_time = 1100;
    Verilated::commandArgs(argc, argv);
    Verilated::debug(0);
    // we're going to be checking for these errors do don't crash out
    Verilated::fatalOnVpiError(0);

    VM_PREFIX* topp = new VM_PREFIX("");  // Note null name - we're flattening it out

#ifdef VERILATOR
#ifdef TEST_VERBOSE
    Verilated::scopesDump();
#endif
#endif

#if VM_TRACE
    Verilated::traceEverOn(true);
    VL_PRINTF("Enabling waves...\n");
    VerilatedVcdC* tfp = new VerilatedVcdC;
    topp->trace(tfp, 99);
    tfp->open(STRINGIFY(TEST_OBJ_DIR) "/simx.vcd");
#endif

    topp->eval();
    topp->clk = 0;
    main_time += 10;

    while (sc_time_stamp() < sim_time && !Verilated::gotFinish()) {
        main_time += 1;
        topp->eval();
        VerilatedVpi::callValueCbs();
        topp->clk = !topp->clk;
        // mon_do();
#if VM_TRACE
        if (tfp) tfp->dump(main_time);
#endif
    }
    if (!Verilated::gotFinish()) {
        vl_fatal(FILENM, __LINE__, "main", "%Error: Timeout; never got a $finish");
    }
    topp->final();

#if VM_TRACE
    if (tfp) tfp->close();
#endif

    VL_DO_DANGLING(delete topp, topp);
    exit(0L);
}

#endif
