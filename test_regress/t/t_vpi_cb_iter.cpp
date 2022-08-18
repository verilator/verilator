// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
//
// Copyright 2020 by Wilson Snyder and Marlon James. This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#include "verilated.h"
#include "verilated_vpi.h"

#include "Vt_vpi_cb_iter.h"
#include "vpi_user.h"

#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <iostream>
#include <vector>

// These require the above. Comment prevents clang-format moving them
#include "TestCheck.h"
#include "TestSimulator.h"
#include "TestVpi.h"

int errors = 0;

TestVpiHandle vh_value_cb;
TestVpiHandle vh_rw_cb;

unsigned int last_value_cb_time = 0;
unsigned int last_rw_cb_time = 0;

unsigned int main_time = 0;

static void reregister_value_cb();
static void reregister_rw_cb();

static int the_value_callback(p_cb_data cb_data) {
    reregister_value_cb();
    return 0;
}

static int the_rw_callback(p_cb_data cb_data) {
    reregister_rw_cb();
    return 0;
}

static void reregister_value_cb() {
    if (vh_value_cb) {
        if (verbose) vpi_printf(const_cast<char*>("- Removing cbValueChange callback\n"));
        int ret = vpi_remove_cb(vh_value_cb);
        vh_value_cb.freed();
        TEST_CHECK_EQ(ret, 1);

        if (verbose) {
            vpi_printf(const_cast<char*>("- last_value_cb_time %d , main_time %d\n"),
                       last_value_cb_time, main_time);
        }
        TEST_CHECK_NE(main_time, last_value_cb_time);
        last_value_cb_time = main_time;
    }
    if (verbose) vpi_printf(const_cast<char*>("- Registering cbValueChange callback\n"));
    t_cb_data cb_data_testcase;
    bzero(&cb_data_testcase, sizeof(cb_data_testcase));
    cb_data_testcase.cb_rtn = the_value_callback;
    cb_data_testcase.reason = cbValueChange;

    TestVpiHandle vh1 = VPI_HANDLE("count");
    TEST_CHECK_NZ(vh1);

    s_vpi_value v;
    v.format = vpiSuppressVal;

    cb_data_testcase.obj = vh1;
    cb_data_testcase.value = &v;

    vh_value_cb = vpi_register_cb(&cb_data_testcase);
    TEST_CHECK_NZ(vh_value_cb);
}

static void reregister_rw_cb() {
    if (vh_rw_cb) {
        if (verbose) vpi_printf(const_cast<char*>("- Removing cbReadWriteSynch callback\n"));
        int ret = vpi_remove_cb(vh_rw_cb);
        vh_rw_cb.freed();
        TEST_CHECK_EQ(ret, 1);

        if (verbose) {
            vpi_printf(const_cast<char*>("- last_rw_cb_time %d , main_time %d\n"), last_rw_cb_time,
                       main_time);
        }
        TEST_CHECK_NE(main_time, last_rw_cb_time);
        last_rw_cb_time = main_time;
    }
    if (verbose) vpi_printf(const_cast<char*>("- Registering cbReadWriteSynch callback\n"));
    t_cb_data cb_data_testcase;
    bzero(&cb_data_testcase, sizeof(cb_data_testcase));
    cb_data_testcase.cb_rtn = the_rw_callback;
    cb_data_testcase.reason = cbReadWriteSynch;

    vh_rw_cb = vpi_register_cb(&cb_data_testcase);
    TEST_CHECK_NZ(vh_rw_cb);
}

static int the_filler_callback(p_cb_data cb_data) { return 0; }

static void register_filler_cb() {
    if (verbose) {
        vpi_printf(const_cast<char*>("- Registering filler cbReadWriteSynch callback\n"));
    }
    t_cb_data cb_data_1;
    bzero(&cb_data_1, sizeof(cb_data_1));
    cb_data_1.cb_rtn = the_filler_callback;
    cb_data_1.reason = cbReadWriteSynch;

    TestVpiHandle cb_data_1_h = vpi_register_cb(&cb_data_1);
    TEST_CHECK_NZ(cb_data_1_h);

    if (verbose) {
        vpi_printf(const_cast<char*>("- Registering filler cbValueChange callback\n"));
    }
    t_cb_data cb_data_2;
    bzero(&cb_data_2, sizeof(cb_data_2));
    cb_data_2.cb_rtn = the_filler_callback;
    cb_data_2.reason = cbValueChange;

    TestVpiHandle vh2 = VPI_HANDLE("count");
    TEST_CHECK_NZ(vh2);

    s_vpi_value v;
    v.format = vpiSuppressVal;

    cb_data_2.obj = vh2;
    cb_data_2.value = &v;

    TestVpiHandle cb_data_2_h = vpi_register_cb(&cb_data_2);
    TEST_CHECK_NZ(cb_data_2_h);
}

double sc_time_stamp() { return main_time; }

int main(int argc, char** argv, char** env) {
    const std::unique_ptr<VerilatedContext> contextp{new VerilatedContext};

    uint64_t sim_time = 100;
    contextp->commandArgs(argc, argv);
    contextp->debug(0);

    const std::unique_ptr<VM_PREFIX> topp{new VM_PREFIX{contextp.get(),
                                                        // Note null name - we're flattening it out
                                                        ""}};

    reregister_value_cb();
    TEST_CHECK_NZ(vh_value_cb);
    reregister_rw_cb();
    TEST_CHECK_NZ(vh_rw_cb);
    register_filler_cb();

    topp->eval();
    topp->clk = 0;

    while (main_time < sim_time && !contextp->gotFinish()) {
        main_time += 1;
        if (verbose) VL_PRINTF("Sim Time %d got_error %d\n", main_time, errors);
        topp->clk = !topp->clk;
        topp->eval();
        VerilatedVpi::callValueCbs();
        VerilatedVpi::callCbs(cbReadWriteSynch);
        if (errors) vl_stop(__FILE__, __LINE__, "TOP-cpp");
    }

    if (!contextp->gotFinish()) {
        vl_fatal(__FILE__, __LINE__, "main", "%Error: Timeout; never got a $finish");
    }
    topp->final();

    return errors ? 10 : 0;
}
