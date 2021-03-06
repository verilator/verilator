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

#include "Vt_vpi_memory.h"
#include "verilated.h"
#include "svdpi.h"

#include "Vt_vpi_memory__Dpi.h"

#include "verilated_vpi.h"
#include "verilated_vcd_c.h"

#endif

#include <cstdio>
#include <cstring>
#include <iostream>

#include "TestSimulator.h"
#include "TestVpi.h"

// __FILE__ is too long
#define FILENM "t_vpi_memory.cpp"

#define DEBUG \
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
        std::cout << std::dec << "%Error: " << FILENM << ":" << __LINE__ << ": GOT = " << (got) \
                  << "   EXP = " << (exp) << std::endl; \
        return __LINE__; \
    }

#define CHECK_RESULT_HEX(got, exp) \
    if ((got) != (exp)) { \
        std::cout << std::dec << "%Error: " << FILENM << ":" << __LINE__ << std::hex \
                  << ": GOT = " << (got) << "   EXP = " << (exp) << std::endl; \
        return __LINE__; \
    }

#define CHECK_RESULT_CSTR(got, exp) \
    if (strcmp((got), (exp))) { \
        printf("%%Error: %s:%d: GOT = '%s'   EXP = '%s'\n", FILENM, __LINE__, \
               (got) ? (got) : "<null>", (exp) ? (exp) : "<null>"); \
        return __LINE__; \
    }

#define CHECK_RESULT_CSTR_STRIP(got, exp) CHECK_RESULT_CSTR(got + strspn(got, " "), exp)

int _mon_check_range(const TestVpiHandle& handle, int size, int left, int right) {
    s_vpi_value value;
    value.format = vpiIntVal;
    value.value.integer = 0;
    // check size of object
    {
        int vpisize = vpi_get(vpiSize, handle);
        CHECK_RESULT(vpisize, size);
    }
    int coherency;
    {
        // check left hand side of range
        TestVpiHandle left_h = vpi_handle(vpiLeftRange, handle);
        CHECK_RESULT_NZ(left_h);
        vpi_get_value(left_h, &value);
        CHECK_RESULT(value.value.integer, left);
        coherency = value.value.integer;
    }
    {
        // check right hand side of range
        TestVpiHandle right_h = vpi_handle(vpiRightRange, handle);
        CHECK_RESULT_NZ(right_h);
        vpi_get_value(right_h, &value);
        CHECK_RESULT(value.value.integer, right);
        coherency -= value.value.integer;
    }
    // calculate size & check
    coherency = abs(coherency) + 1;
    CHECK_RESULT(coherency, size);
    return 0;  // Ok
}

int _mon_check_memory() {
    s_vpi_value value;
    value.format = vpiIntVal;
    value.value.integer = 0;
    s_vpi_error_info e;

    vpi_printf((PLI_BYTE8*)"Check memory vpi ...\n");
    TestVpiHandle mem_h = vpi_handle_by_name((PLI_BYTE8*)TestSimulator::rooted("mem0"), NULL);
    CHECK_RESULT_NZ(mem_h);
    {
        // check type
        int vpitype = vpi_get(vpiType, mem_h);
        CHECK_RESULT(vpitype, vpiMemory);
    }
    if (int status = _mon_check_range(mem_h, 16, 16, 1)) return status;
    // iterate and store
    {
        TestVpiHandle iter_h = vpi_iterate(vpiMemoryWord, mem_h);
        int cnt = 0;
        while (TestVpiHandle lcl_h = vpi_scan(iter_h)) {
            value.value.integer = ++cnt;
            vpi_put_value(lcl_h, &value, NULL, vpiNoDelay);
            // check size and range
            if (int status = _mon_check_range(lcl_h, 32, 31, 0)) return status;
        }
        iter_h.freed();  // IEEE 37.2.2 vpi_scan at end does a vpi_release_handle
        CHECK_RESULT(cnt, 16);  // should be 16 addresses
    }
    {
        // iterate and accumulate
        TestVpiHandle iter_h = vpi_iterate(vpiMemoryWord, mem_h);
        int cnt = 0;
        while (TestVpiHandle lcl_h = vpi_scan(iter_h)) {
            ++cnt;
            vpi_get_value(lcl_h, &value);
            CHECK_RESULT(value.value.integer, cnt);
        }
        iter_h.freed();  // IEEE 37.2.2 vpi_scan at end does a vpi_release_handle
        CHECK_RESULT(cnt, 16);  // should be 16 addresses
    }

    // don't care for non verilator
    // (crashes on Icarus)
    if (TestSimulator::is_icarus()) {
        vpi_printf((PLI_BYTE8*)"Skipping property checks for simulator %s\n",
                   TestSimulator::get_info().product);
        return 0;  // Ok
    }
    {
        // make sure trying to get properties that don't exist
        // doesn't crash
        TestVpiHandle iter_h = vpi_iterate(vpiMemoryWord, mem_h);
        int should_be_0 = vpi_get(vpiSize, iter_h);
        CHECK_RESULT(should_be_0, 0);
        should_be_0 = vpi_get(vpiIndex, iter_h);
        CHECK_RESULT(should_be_0, 0);
        vpiHandle should_be_NULL = vpi_handle(vpiLeftRange, iter_h);
        CHECK_RESULT(should_be_NULL, 0);
        should_be_NULL = vpi_handle(vpiRightRange, iter_h);
        CHECK_RESULT(should_be_NULL, 0);
        should_be_NULL = vpi_handle(vpiScope, iter_h);
        CHECK_RESULT(should_be_NULL, 0);
    }
    {
        // check vpiRange
        TestVpiHandle iter_h = vpi_iterate(vpiRange, mem_h);
        CHECK_RESULT_NZ(iter_h);
        TestVpiHandle lcl_h = vpi_scan(iter_h);
        CHECK_RESULT_NZ(lcl_h);
        {
            TestVpiHandle side_h = vpi_handle(vpiLeftRange, lcl_h);
            CHECK_RESULT_NZ(side_h);
            vpi_get_value(side_h, &value);
            CHECK_RESULT(value.value.integer, 16);
        }
        {
            TestVpiHandle side_h = vpi_handle(vpiRightRange, lcl_h);
            CHECK_RESULT_NZ(side_h);
            vpi_get_value(side_h, &value);
            CHECK_RESULT(value.value.integer, 1);
            // check writing to vpiConstant
            vpi_put_value(side_h, &value, NULL, vpiNoDelay);
            CHECK_RESULT_NZ(vpi_chk_error(&e));
        }
        {
            // iterator should exhaust after 1 dimension
            TestVpiHandle zero_h = vpi_scan(iter_h);
            iter_h.freed();  // IEEE 37.2.2 vpi_scan at end does a vpi_release_handle
            CHECK_RESULT(zero_h, 0);
        }
    }
    return 0;  // Ok
}

int mon_check() {
    // Callback from initial block in monitor
    if (int status = _mon_check_memory()) return status;
    return 0;  // Ok
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
    vluint64_t sim_time = 1100;
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
    tfp->open(VL_STRINGIFY(TEST_OBJ_DIR) "/simx.vcd");
#endif

    topp->eval();
    topp->clk = 0;
    main_time += 10;

    while (vl_time_stamp64() < sim_time && !Verilated::gotFinish()) {
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
    return 0;
}

#endif
