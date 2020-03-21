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

#include "Vt_vpi_get.h"
#include "verilated.h"
#include "svdpi.h"

#include "Vt_vpi_get__Dpi.h"

#include "verilated_vpi.h"
#include "verilated_vcd_c.h"

#endif

#include <cstdio>
#include <cstring>
#include <iostream>
using namespace std;

#include "TestSimulator.h"
#include "TestVpi.h"

// __FILE__ is too long
#define FILENM "t_vpi_get.cpp"

#define TEST_MSG \
    if (0) printf

unsigned int main_time = 0;

//======================================================================

#define CHECK_RESULT_VH(got, exp) \
    if ((got) != (exp)) { \
        printf("%%Error: %s:%d: GOT = %p   EXP = %p\n", FILENM, __LINE__, (got), (exp)); \
        return __LINE__; \
    }

#define CHECK_RESULT_NZ(got) \
    if (!(got)) { \
        printf("%%Error: %s:%d: GOT = NULL  EXP = !NULL\n", FILENM, __LINE__); \
        return __LINE__; \
    }

// Use cout to avoid issues with %d/%lx etc
#define CHECK_RESULT(got, exp) \
    if ((got) != (exp)) { \
        cout << dec << "%Error: " << FILENM << ":" << __LINE__ << ": GOT = " << (got) \
             << "   EXP = " << (exp) << endl; \
        return __LINE__; \
    }

#define CHECK_RESULT_HEX(got, exp) \
    if ((got) != (exp)) { \
        cout << dec << "%Error: " << FILENM << ":" << __LINE__ << hex << ": GOT = " << (got) \
             << "   EXP = " << (exp) << endl; \
        return __LINE__; \
    }

#define CHECK_RESULT_CSTR(got, exp) \
    if (strcmp((got), (exp))) { \
        printf("%%Error: %s:%d: GOT = '%s'   EXP = '%s'\n", FILENM, __LINE__, \
               (got) ? (got) : "<null>", (exp) ? (exp) : "<null>"); \
        return __LINE__; \
    }

#define CHECK_RESULT_CSTR_STRIP(got, exp) CHECK_RESULT_CSTR(got + strspn(got, " "), exp)

static int _mon_check_props(TestVpiHandle& handle, int size, int direction, int scalar, int type) {
    s_vpi_value value = {vpiIntVal, .value = {.integer = 0}};
    // check size of object
    int vpisize = vpi_get(vpiSize, handle);
    CHECK_RESULT(vpisize, size);

    // icarus verilog does not support vpiScalar, vpiVector or vpi*Range
    if (TestSimulator::has_get_scalar()) {
        int vpiscalar = vpi_get(vpiScalar, handle);
        CHECK_RESULT((bool)vpiscalar, (bool)scalar);
        int vpivector = vpi_get(vpiVector, handle);
        CHECK_RESULT((bool)vpivector, (bool)!scalar);
    }

    // Icarus only supports ranges on memories
    if (!scalar && !(TestSimulator::is_icarus() && type != vpiMemory)) {
        TestVpiHandle left_h, right_h;

        // check coherency for vectors
        // get left hand side of range
        left_h = vpi_handle(vpiLeftRange, handle);
        CHECK_RESULT_NZ(left_h);
        vpi_get_value(left_h, &value);
        int coherency = value.value.integer;
        // get right hand side of range
        right_h = vpi_handle(vpiRightRange, handle);
        CHECK_RESULT_NZ(right_h);
        vpi_get_value(right_h, &value);
        TEST_MSG("%d:%d\n", coherency, value.value.integer);
        coherency -= value.value.integer;
        // calculate size & check
        coherency = abs(coherency) + 1;
        CHECK_RESULT(coherency, size);
    }

    // Only check direction on ports
    if (type == vpiPort) {
        // check direction of object
        int vpidir = vpi_get(vpiDirection, handle);
        // Don't check port directions in verilator
        // see #681
        if (!TestSimulator::is_verilator()) { CHECK_RESULT(vpidir, direction); }
    }

    // check type of object
    int vpitype = vpi_get(vpiType, handle);
    if (!(TestSimulator::is_verilator() && type == vpiPort)) {
        // Don't check for ports in verilator
        // see #681
        CHECK_RESULT(vpitype, type);
    }

    return 0;  // Ok
}

struct params {
    const char* signal;
    struct {
        unsigned int size;
        unsigned int direction;
        unsigned int scalar;
        int type;
    } attributes, children;
};

int mon_check_props() {
    // This table needs to be function-static.
    // This avoids calling is_verilator() below at global-static init time.
    // When global-static led to a race between the is_verilator call below, and
    // the code that sets up the VerilatedAssertOneThread() check in
    // verilated_vpi.cc, it was causing the check to falsely fail
    // (due to m_threadid within the check not being initted yet.)
    static struct params values[]
        = {{"onebit", {1, vpiNoDirection, 1, vpiReg}, {0, 0, 0, 0}},
           {"twoone", {2, vpiNoDirection, 0, vpiReg}, {0, 0, 0, 0}},
           {"onetwo",
            {2, vpiNoDirection, 0, TestSimulator::is_verilator() ? vpiReg : vpiMemory},
            {0, 0, 0, 0}},
           {"fourthreetwoone",
            {2, vpiNoDirection, 0, vpiMemory},
            {2, vpiNoDirection, 0, vpiMemoryWord}},
           {"clk", {1, vpiInput, 1, vpiPort}, {0, 0, 0, 0}},
           {"testin", {16, vpiInput, 0, vpiPort}, {0, 0, 0, 0}},
           {"testout", {24, vpiOutput, 0, vpiPort}, {0, 0, 0, 0}},
           {"sub.subin", {1, vpiInput, 1, vpiPort}, {0, 0, 0, 0}},
           {"sub.subout", {1, vpiOutput, 1, vpiPort}, {0, 0, 0, 0}},
           {NULL, {0, 0, 0, 0}, {0, 0, 0, 0}}};
    struct params* value = values;
    while (value->signal) {
        TestVpiHandle h = VPI_HANDLE(value->signal);
        CHECK_RESULT_NZ(h);
        TEST_MSG("%s\n", value->signal);
        if (int status = _mon_check_props(h, value->attributes.size, value->attributes.direction,
                                          value->attributes.scalar, value->attributes.type))
            return status;
        if (value->children.size) {
            int size = 0;
            TestVpiHandle iter_h = vpi_iterate(vpiMemoryWord, h);
            while (TestVpiHandle word_h = vpi_scan(iter_h.nofree())) {
                // check size and range
                if (int status
                    = _mon_check_props(word_h, value->children.size, value->children.direction,
                                       value->children.scalar, value->children.type))
                    return status;
                size++;
            }
            CHECK_RESULT(size, value->attributes.size);
        }
        value++;
    }
    return 0;
}

int mon_check() {
    // Callback from initial block in monitor
    if (int status = mon_check_props()) return status;
    return 0;  // Ok
}

//======================================================================

#ifdef IS_VPI

static int mon_check_vpi() {
    vpiHandle href = vpi_handle(vpiSysTfCall, 0);
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
    while (systf_data_p->type != 0)
        vpi_register_systf(systf_data_p++);
}

// icarus entry
void (*vlog_startup_routines[])() = {vpi_compat_bootstrap, 0};

#else
double sc_time_stamp() { return main_time; }
int main(int argc, char** argv, char** env) {
    double sim_time = 1100;
    Verilated::commandArgs(argc, argv);
    Verilated::debug(0);

    Vt_vpi_get* topp = new Vt_vpi_get("");  // Note null name - we're flattening it out

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
    tfp->open(VL_STRINGIFY(TEST_OBJ_DIR) "/simx.vcd");
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
