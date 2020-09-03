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

#include "Vt_vpi_zero_time_cb.h"
#include "verilated.h"
#include "svdpi.h"
#include <dlfcn.h>

#include "Vt_vpi_zero_time_cb__Dpi.h"

#include "verilated_vpi.h"
#include "verilated_vcd_c.h"

#endif

#include <cstdlib>
#include <cstdio>
#include <cstring>
#include <iostream>

#include "TestSimulator.h"
#include "TestVpi.h"

#define TEST_MSG \
    if (0) printf

unsigned int main_time = 0;
unsigned int callback_count_zero_time = 0;
unsigned int callback_count_start_of_sim = 0;

//======================================================================

#define CHECK_RESULT_VH(got, exp) \
    if ((got) != (exp)) { \
        printf("%%Error: %s:%d: GOT = %p   EXP = %p\n", __FILE__, __LINE__, (got), (exp)); \
        return __LINE__; \
    }

#define CHECK_RESULT_NZ(got) \
    if (!(got)) { \
        printf("%%Error: %s:%d: GOT = NULL  EXP = !NULL\n", __FILE__, __LINE__); \
        return __LINE__; \
    }

// Use cout to avoid issues with %d/%lx etc
#define CHECK_RESULT(got, exp) \
    if ((got) != (exp)) { \
        std::cout << std::dec << "%Error: " << __FILE__ << ":" << __LINE__ << ": GOT = " << (got) \
                  << "   EXP = " << (exp) << std::endl; \
        return __LINE__; \
    }

#define CHECK_RESULT_HEX(got, exp) \
    if ((got) != (exp)) { \
        std::cout << std::dec << "%Error: " << __FILE__ << ":" << __LINE__ << hex \
                  << ": GOT = " << (got) << "   EXP = " << (exp) << std::endl; \
        return __LINE__; \
    }

#define CHECK_RESULT_CSTR(got, exp) \
    if (strcmp((got), (exp))) { \
        printf("%%Error: %s:%d: GOT = '%s'   EXP = '%s'\n", __FILE__, __LINE__, \
               (got) ? (got) : "<null>", (exp) ? (exp) : "<null>"); \
        return __LINE__; \
    }

#define CHECK_RESULT_CSTR_STRIP(got, exp) CHECK_RESULT_CSTR(got + strspn(got, " "), exp)

//======================================================================

#ifdef IS_VPI

static int _zero_time_cb(p_cb_data cb_data) {
    callback_count_zero_time++;
    return 0;
}

static int _start_of_sim_cb(p_cb_data cb_data) {
    t_cb_data cb_data_n;
    bzero(&cb_data_n, sizeof(cb_data_n));
    s_vpi_time t;

    cb_data_n.reason = cbAfterDelay;
    t.type = vpiSimTime;
    t.high = 0;
    t.low = 0;
    cb_data_n.time = &t;
    cb_data_n.cb_rtn = _zero_time_cb;
    vpi_register_cb(&cb_data_n);
    callback_count_start_of_sim++;
    return 0;
}

static int _end_of_sim_cb(p_cb_data cb_data) {
    CHECK_RESULT(callback_count_start_of_sim, 1);
    CHECK_RESULT(callback_count_zero_time, 1);
    fprintf(stdout, "*-* All Finished *-*\n");
    return 0;
}

// cver entry
#ifdef __cplusplus
extern "C"
#endif

void vpi_compat_bootstrap(void) {
    t_cb_data cb_data;
    bzero(&cb_data, sizeof(cb_data));

    // VL_PRINTF("register start-of-sim callback\n");
    cb_data.reason = cbStartOfSimulation;
    cb_data.time = 0;
    cb_data.cb_rtn = _start_of_sim_cb;
    vpi_register_cb(&cb_data);

    cb_data.reason = cbEndOfSimulation;
    cb_data.time = 0;
    cb_data.cb_rtn = _end_of_sim_cb;
    vpi_register_cb(&cb_data);
}

// icarus entry
void (*vlog_startup_routines[])() = {vpi_compat_bootstrap, 0};

#else

double sc_time_stamp() { return main_time; }

int main(int argc, char** argv, char** env) {
    double sim_time = 1100;
    Verilated::commandArgs(argc, argv);
    Verilated::debug(0);

    VM_PREFIX* topp = new VM_PREFIX("");  // Note null name - we're flattening it out

#ifdef VERILATOR
# ifdef TEST_VERBOSE
    Verilated::scopesDump();
# endif
#endif

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

    while (sc_time_stamp() < sim_time && !Verilated::gotFinish()) {
        main_time += 1;
        topp->eval();
        VerilatedVpi::callValueCbs();
        VerilatedVpi::callTimedCbs();
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
    exit(0L);
}

#endif
