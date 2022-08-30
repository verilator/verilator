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

#include "verilated.h"
#include "verilated_vcd_c.h"
#include "verilated_vpi.h"

#include "Vt_vpi_memory.h"
#include "Vt_vpi_memory__Dpi.h"
#include "svdpi.h"

#endif

#include <cstdio>
#include <cstring>
#include <iostream>

// These require the above. Comment prevents clang-format moving them
#include "TestCheck.h"
#include "TestSimulator.h"
#include "TestVpi.h"

// __FILE__ is too long
#define FILENM "t_vpi_memory.cpp"

#define DEBUG \
    if (0) printf

int errors = 0;

//======================================================================

void _mon_check_range(const TestVpiHandle& handle, int size, int left, int right) {
    s_vpi_value value;
    value.format = vpiIntVal;
    value.value.integer = 0;
    // check size of object
    {
        int vpisize = vpi_get(vpiSize, handle);
        TEST_CHECK_EQ(vpisize, size);
    }
    int coherency;
    {
        // check left hand side of range
        TestVpiHandle left_h = vpi_handle(vpiLeftRange, handle);
        TEST_CHECK_NZ(left_h);
        vpi_get_value(left_h, &value);
        TEST_CHECK_EQ(value.value.integer, left);
        coherency = value.value.integer;
    }
    {
        // check right hand side of range
        TestVpiHandle right_h = vpi_handle(vpiRightRange, handle);
        TEST_CHECK_NZ(right_h);
        vpi_get_value(right_h, &value);
        TEST_CHECK_EQ(value.value.integer, right);
        coherency -= value.value.integer;
    }
    // calculate size & check
    coherency = abs(coherency) + 1;
    TEST_CHECK_EQ(coherency, size);
}

void _mem_check(const char* name, int size, int left, int right, int words) {
    s_vpi_value value;
    s_vpi_error_info e;

    vpi_printf((PLI_BYTE8*)"Check memory vpi (%s) ...\n", name);
    TestVpiHandle mem_h = vpi_handle_by_name((PLI_BYTE8*)TestSimulator::rooted(name), NULL);
    TEST_CHECK_NZ(mem_h);
    // check type
    int vpitype = vpi_get(vpiType, mem_h);
    if (vpitype != vpiMemory && vpitype != vpiReg) {
        printf("%%Error: %s:%d vpiType neither vpiMemory or vpiReg: %d\n", FILENM, __LINE__,
               vpitype);
        errors++;
    }
    std::string binStr;
    for (int i = words; i >= 1; i--) {
        for (int pos = size - 1; pos >= 0; pos--) {
            int posValue = (i >> pos) & 0x1;
            binStr += posValue ? "1" : "0";
        }
    }
    // iterate and store
    if (vpitype == vpiMemory) {
        _mon_check_range(mem_h, words, words, 1);
        TestVpiHandle iter_h = vpi_iterate(vpiMemoryWord, mem_h);
        int cnt = 0;
        while (TestVpiHandle lcl_h = vpi_scan(iter_h)) {
            value.format = vpiIntVal;
            value.value.integer = ++cnt;
            vpi_put_value(lcl_h, &value, NULL, vpiNoDelay);
            TEST_CHECK_Z(vpi_chk_error(&e));
            // check size and range
            _mon_check_range(lcl_h, size, left, right);
        }
        iter_h.freed();  // IEEE 37.2.2 vpi_scan at end does a vpi_release_handle
        TEST_CHECK_EQ(cnt, words);  // should be words addresses
    } else {
        int expSize = size * words;
        _mon_check_range(mem_h, expSize, expSize - 1, 0);
        value.format = vpiBinStrVal;
        value.value.str = const_cast<char*>(binStr.c_str());
        vpi_put_value(mem_h, &value, NULL, vpiNoDelay);
        TEST_CHECK_Z(vpi_chk_error(&e));
    }
    if (vpitype == vpiMemory) {
        // iterate and accumulate
        TestVpiHandle iter_h = vpi_iterate(vpiMemoryWord, mem_h);
        int cnt = 0;
        while (TestVpiHandle lcl_h = vpi_scan(iter_h)) {
            ++cnt;
            value.format = vpiIntVal;
            vpi_get_value(lcl_h, &value);
            TEST_CHECK_Z(vpi_chk_error(&e));
            TEST_CHECK_EQ(value.value.integer, cnt);
        }
        iter_h.freed();  // IEEE 37.2.2 vpi_scan at end does a vpi_release_handle
        TEST_CHECK_EQ(cnt, words);  // should be words addresses
    } else {
        value.format = vpiBinStrVal;
        vpi_get_value(mem_h, &value);
        TEST_CHECK_Z(vpi_chk_error(&e));
        TEST_CHECK_EQ(std::string{value.value.str}, binStr);
    }

    // don't care for non verilator
    // (crashes on Icarus)
    if (TestSimulator::is_icarus()) {
        vpi_printf((PLI_BYTE8*)"Skipping property checks for simulator %s\n",
                   TestSimulator::get_info().product);
        return;  // Ok
    }
    {
        // make sure trying to get properties that don't exist
        // doesn't crash
        TestVpiHandle iter_h = vpi_iterate(vpiMemoryWord, mem_h);
        int should_be_0 = vpi_get(vpiSize, iter_h);
        TEST_CHECK_EQ(should_be_0, 0);
        should_be_0 = vpi_get(vpiIndex, iter_h);
        TEST_CHECK_EQ(should_be_0, 0);
        vpiHandle should_be_NULL = vpi_handle(vpiLeftRange, iter_h);
        TEST_CHECK_EQ(should_be_NULL, 0);
        should_be_NULL = vpi_handle(vpiRightRange, iter_h);
        TEST_CHECK_EQ(should_be_NULL, 0);
        should_be_NULL = vpi_handle(vpiScope, iter_h);
        TEST_CHECK_EQ(should_be_NULL, 0);
    }
    if (vpitype == vpiMemory) {
        // check vpiRange
        TestVpiHandle iter_h = vpi_iterate(vpiRange, mem_h);
        TEST_CHECK_NZ(iter_h);
        TestVpiHandle lcl_h = vpi_scan(iter_h);
        TEST_CHECK_NZ(lcl_h);
        {
            TestVpiHandle side_h = vpi_handle(vpiLeftRange, lcl_h);
            TEST_CHECK_NZ(side_h);
            vpi_get_value(side_h, &value);
            TEST_CHECK_EQ(value.value.integer, 16);
        }
        {
            TestVpiHandle side_h = vpi_handle(vpiRightRange, lcl_h);
            TEST_CHECK_NZ(side_h);
            vpi_get_value(side_h, &value);
            TEST_CHECK_EQ(value.value.integer, 1);
            // check writing to vpiConstant
            vpi_put_value(side_h, &value, NULL, vpiNoDelay);
            TEST_CHECK_NZ(vpi_chk_error(&e));
        }
        {
            // iterator should exhaust after 1 dimension
            TestVpiHandle zero_h = vpi_scan(iter_h);
            iter_h.freed();  // IEEE 37.2.2 vpi_scan at end does a vpi_release_handle
            TEST_CHECK_EQ(zero_h, 0);
        }
    }
}

struct params {
    const char* name;
    int size;
    int left;
    int right;
    int words;
};

void _mon_check_memory() {
    // See note in t_vpi_get.cpp about static
    static struct params values[]
        = {{"mem0", 32, 31, 0, 16},   {"memp32", 32, 31, 0, 16}, {"memp31", 31, 30, 0, 16},
           {"memp33", 33, 32, 0, 15}, {"memw", 32, 31, 0, 16},   {NULL, 0, 0, 0, 0}};
    struct params* value = values;
    while (value->name) {
        _mem_check(value->name, value->size, value->left, value->right, value->words);
        value++;
    }
}

extern "C" int mon_check() {
    // Callback from initial block in monitor
    _mon_check_memory();
    return errors;
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

int main(int argc, char** argv, char** env) {
    const std::unique_ptr<VerilatedContext> contextp{new VerilatedContext};

    uint64_t sim_time = 1100;
    contextp->commandArgs(argc, argv);
    contextp->debug(0);
    // we're going to be checking for these errors do don't crash out
    contextp->fatalOnVpiError(0);

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
    tfp->open(VL_STRINGIFY(TEST_OBJ_DIR) "/simx.vcd");
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
