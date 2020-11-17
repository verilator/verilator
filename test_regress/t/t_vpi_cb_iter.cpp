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

#include "Vt_vpi_cb_iter.h"
#include "verilated.h"
#include "verilated_vpi.h"

#include <cstdlib>
#include <cstdio>
#include <cstring>
#include <iostream>
#include <vector>

#include "TestSimulator.h"
#include "TestVpi.h"

#include "vpi_user.h"

bool got_error = false;

vpiHandle vh_value_cb = 0;
vpiHandle vh_rw_cb = 0;

unsigned int last_value_cb_time = 0;
unsigned int last_rw_cb_time = 0;

unsigned int main_time = 0;

#ifdef TEST_VERBOSE
bool verbose = true;
#else
bool verbose = false;
#endif

#define CHECK_RESULT_NZ(got) \
    if (!(got)) { \
        printf("%%Error: %s:%d: GOT = NULL  EXP = !NULL\n", __FILE__, __LINE__); \
        got_error = true; \
    }

// Use cout to avoid issues with %d/%lx etc
#define CHECK_RESULT_NE(got, exp) \
    if ((got) == (exp)) { \
        std::cout << std::dec << "%Error: " << __FILE__ << ":" << __LINE__ << ": GOT = " << (got) \
                  << "   EXP = !" << (exp) << std::endl; \
        got_error = true; \
    }

// Use cout to avoid issues with %d/%lx etc
#define CHECK_RESULT(got, exp) \
    if ((got) != (exp)) { \
        std::cout << std::dec << "%Error: " << __FILE__ << ":" << __LINE__ << ": GOT = " << (got) \
                  << "   EXP = " << (exp) << std::endl; \
        got_error = true; \
    }
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
        if (verbose) { vpi_printf(const_cast<char*>("- Removing cbValueChange callback\n")); }
        int ret = vpi_remove_cb(vh_value_cb);
        CHECK_RESULT(ret, 1);

        if (verbose) {
            vpi_printf(const_cast<char*>("- last_value_cb_time %d , main_time %d\n"),
                       last_value_cb_time, main_time);
        }
        CHECK_RESULT_NE(main_time, last_value_cb_time);
        last_value_cb_time = main_time;
    }
    if (verbose) { vpi_printf(const_cast<char*>("- Registering cbValueChange callback\n")); }
    t_cb_data cb_data_testcase;
    bzero(&cb_data_testcase, sizeof(cb_data_testcase));
    cb_data_testcase.cb_rtn = the_value_callback;
    cb_data_testcase.reason = cbValueChange;

    vpiHandle vh1 = VPI_HANDLE("count");
    CHECK_RESULT_NZ(vh1);

    s_vpi_value v;
    v.format = vpiSuppressVal;

    cb_data_testcase.obj = vh1;
    cb_data_testcase.value = &v;

    vh_value_cb = vpi_register_cb(&cb_data_testcase);
    CHECK_RESULT_NZ(vh_value_cb);
}

static void reregister_rw_cb() {
    if (vh_rw_cb) {
        if (verbose) { vpi_printf(const_cast<char*>("- Removing cbReadWriteSynch callback\n")); }
        int ret = vpi_remove_cb(vh_rw_cb);
        CHECK_RESULT(ret, 1);

        if (verbose) {
            vpi_printf(const_cast<char*>("- last_rw_cb_time %d , main_time %d\n"), last_rw_cb_time,
                       main_time);
        }
        CHECK_RESULT_NE(main_time, last_rw_cb_time);
        last_rw_cb_time = main_time;
    }
    if (verbose) { vpi_printf(const_cast<char*>("- Registering cbReadWriteSynch callback\n")); }
    t_cb_data cb_data_testcase;
    bzero(&cb_data_testcase, sizeof(cb_data_testcase));
    cb_data_testcase.cb_rtn = the_rw_callback;
    cb_data_testcase.reason = cbReadWriteSynch;

    vh_rw_cb = vpi_register_cb(&cb_data_testcase);
    CHECK_RESULT_NZ(vh_rw_cb);
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

    vpiHandle vh1 = vpi_register_cb(&cb_data_1);
    CHECK_RESULT_NZ(vh1);

    if (verbose) {
        vpi_printf(const_cast<char*>("- Registering filler cbValueChange callback\n"));
    }
    t_cb_data cb_data_2;
    bzero(&cb_data_2, sizeof(cb_data_2));
    cb_data_2.cb_rtn = the_filler_callback;
    cb_data_2.reason = cbValueChange;

    vpiHandle vh2 = VPI_HANDLE("count");
    CHECK_RESULT_NZ(vh2);

    s_vpi_value v;
    v.format = vpiSuppressVal;

    cb_data_2.obj = vh2;
    cb_data_2.value = &v;

    vpiHandle vh3 = vpi_register_cb(&cb_data_2);
    CHECK_RESULT_NZ(vh3);
}

double sc_time_stamp() { return main_time; }

int main(int argc, char** argv, char** env) {
    double sim_time = 100;
    Verilated::commandArgs(argc, argv);
    Verilated::debug(0);

    VM_PREFIX* topp = new VM_PREFIX("");  // Note null name - we're flattening it out

    reregister_value_cb();
    CHECK_RESULT_NZ(vh_value_cb);
    reregister_rw_cb();
    CHECK_RESULT_NZ(vh_rw_cb);
    register_filler_cb();

    topp->eval();
    topp->clk = 0;

    while (sc_time_stamp() < sim_time && !Verilated::gotFinish()) {
        main_time += 1;
        if (verbose) { VL_PRINTF("Sim Time %d got_error %d\n", main_time, got_error); }
        topp->clk = !topp->clk;
        topp->eval();
        VerilatedVpi::callValueCbs();
        VerilatedVpi::callCbs(cbReadWriteSynch);
        if (got_error) { vl_stop(__FILE__, __LINE__, "TOP-cpp"); }
    }

    if (!Verilated::gotFinish()) {
        vl_fatal(__FILE__, __LINE__, "main", "%Error: Timeout; never got a $finish");
    }
    topp->final();

    VL_DO_DANGLING(delete topp, topp);
    exit(0L);
}
