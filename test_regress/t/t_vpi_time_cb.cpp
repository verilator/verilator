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

#else

#include "Vt_vpi_time_cb.h"
#include "verilated.h"
#include "svdpi.h"
#include <dlfcn.h>

#include "Vt_vpi_time_cb__Dpi.h"

#include "verilated_vpi.h"
#include "verilated_vcd_c.h"

#endif

#include <cstdlib>
#include <cstdio>
#include <cstring>
#include <iostream>

#include "TestSimulator.h"
#include "TestVpi.h"

unsigned int main_time = 0;
unsigned int callback_count_time1 = 3;
unsigned int callback_count_time2 = 4;
unsigned int callback_count_start_of_sim = 0;

//======================================================================

// Use cout to avoid issues with %d/%lx etc
#define CHECK_RESULT(got, exp) \
    if ((got) != (exp)) { \
        std::cout << std::dec << "%Error: " << __FILE__ << ":" << __LINE__ << ": GOT = " << (got) \
                  << "   EXP = " << (exp) << std::endl; \
        return __LINE__; \
    }

//======================================================================

#ifdef IS_VPI

static int _never_cb(p_cb_data cb_data) {
    CHECK_RESULT(0, 1);  // Should never get called
}

static int _time_cb1(p_cb_data cb_data) {
    s_vpi_time t;
    t.type = vpiSimTime;
    vpi_get_time(0, &t);
    //  fprintf(stdout, "time_cb1: %d\n", t.low);
    CHECK_RESULT(callback_count_time1, t.low);
    callback_count_time1++;

    t_cb_data cb_data_n;
    bzero(&cb_data_n, sizeof(cb_data_n));
    {
        cb_data_n.reason = cbAfterDelay;
        t.type = vpiSimTime;
        t.high = 0;
        t.low = 1;
        cb_data_n.time = &t;
        cb_data_n.cb_rtn = _time_cb1;
        TestVpiHandle cb_data_n1_h = vpi_register_cb(&cb_data_n);
        CHECK_RESULT(vpi_get(vpiType, cb_data_n1_h), vpiCallback);
    }
    {
        // Test cancelling a callback
        cb_data_n.reason = cbAfterDelay;
        t.type = vpiSimTime;
        t.high = 0;
        t.low = 1;
        cb_data_n.time = &t;
        cb_data_n.cb_rtn = _never_cb;
        TestVpiHandle cb_h = vpi_register_cb(&cb_data_n);
        vpi_remove_cb(cb_h);
        cb_h.freed();
    }
    return 0;
}

static int _time_cb2(p_cb_data cb_data) {
    s_vpi_time t;
    t.type = vpiSimTime;
    vpi_get_time(0, &t);
    //  fprintf(stdout, "time_cb2: %d\n", t.low);
    CHECK_RESULT(callback_count_time2, t.low);
    callback_count_time2++;

    t_cb_data cb_data_n;
    bzero(&cb_data_n, sizeof(cb_data_n));

    cb_data_n.reason = cbAfterDelay;
    t.type = vpiSimTime;
    t.high = 0;
    t.low = 1;
    cb_data_n.time = &t;
    cb_data_n.cb_rtn = _time_cb2;
    TestVpiHandle cb_data_n2_h = vpi_register_cb(&cb_data_n);
    CHECK_RESULT(vpi_get(vpiType, cb_data_n2_h), vpiCallback);
    return 0;
}

static int _start_of_sim_cb(p_cb_data cb_data) {
#ifdef TEST_VERBOSE
    printf("-_start_of_sim_cb\n");
#endif

    t_cb_data cb_data_n1, cb_data_n2;
    bzero(&cb_data_n1, sizeof(cb_data_n1));
    bzero(&cb_data_n2, sizeof(cb_data_n2));
    s_vpi_time t1, t2;

    cb_data_n1.reason = cbAfterDelay;
    t1.type = vpiSimTime;
    t1.high = 0;
    t1.low = 3;
    cb_data_n1.time = &t1;
    cb_data_n1.cb_rtn = _time_cb1;
    TestVpiHandle cb_data_n1_h = vpi_register_cb(&cb_data_n1);
    CHECK_RESULT(vpi_get(vpiType, cb_data_n1_h), vpiCallback);

    cb_data_n2.reason = cbAfterDelay;
    t2.type = vpiSimTime;
    t2.high = 0;
    t2.low = 4;
    cb_data_n2.time = &t2;
    cb_data_n2.cb_rtn = _time_cb2;
    TestVpiHandle cb_data_n2_h = vpi_register_cb(&cb_data_n2);
    callback_count_start_of_sim++;
    return 0;
}

static int _end_of_sim_cb(p_cb_data cb_data) {
    CHECK_RESULT(callback_count_start_of_sim, 1);
    fprintf(stdout, "*-* All Finished *-*\n");
    return 0;
}

// cver entry
#ifdef __cplusplus
extern "C"
#endif

    // clang-format off
void vpi_compat_bootstrap(void) {
    // clang-format on
    t_cb_data cb_data;
    bzero(&cb_data, sizeof(cb_data));
    {
        // VL_PRINTF("register start-of-sim callback\n");
        cb_data.reason = cbStartOfSimulation;
        cb_data.time = 0;
        cb_data.cb_rtn = _start_of_sim_cb;
        TestVpiHandle _start_of_sim_cb_h = vpi_register_cb(&cb_data);
    }
    {
        cb_data.reason = cbEndOfSimulation;
        cb_data.time = 0;
        cb_data.cb_rtn = _end_of_sim_cb;
        TestVpiHandle _end_of_sim_cb_h = vpi_register_cb(&cb_data);
    }
    {
        // Test cancelling a callback
        cb_data.reason = cbStartOfSimulation;
        cb_data.time = 0;
        cb_data.cb_rtn = _never_cb;
        TestVpiHandle cb_h = vpi_register_cb(&cb_data);
        vpi_remove_cb(cb_h);
        cb_h.freed();
    }
}

// icarus entry
void (*vlog_startup_routines[])() = {vpi_compat_bootstrap, 0};

#else

double sc_time_stamp() { return main_time; }

int main(int argc, char** argv, char** env) {
    vluint64_t sim_time = 1100;
    Verilated::commandArgs(argc, argv);
    Verilated::debug(0);

    VM_PREFIX* topp = new VM_PREFIX("");  // Note null name - we're flattening it out

// clang-format off
#ifdef VERILATOR
# ifdef TEST_VERBOSE
    Verilated::scopesDump();
# endif
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
        CHECK_RESULT(VerilatedVpi::cbNextDeadline(), main_time + 1);
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
    return 0;
}

#endif
