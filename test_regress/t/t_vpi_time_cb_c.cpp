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

#include "vpi_user.h"

#include <cstdlib>
#include <cstdio>
#include <cstring>
#include <iostream>

#include "TestCheck.h"
#include "TestSimulator.h"
#include "TestVpi.h"

bool errors = false;

unsigned int callback_count_time1 = 3;
unsigned int callback_count_time2 = 4;
unsigned int callback_count_start_of_sim = 0;

//======================================================================

static int _never_cb(p_cb_data cb_data) {
    TEST_CHECK(0, 1);  // Should never get called
    return 0;
}

static int _time_cb1(p_cb_data cb_data) {
    s_vpi_time t;
    t.type = vpiSimTime;
    vpi_get_time(0, &t);
    TEST_VERBOSE_PRINTF("time_cb1: %d\n", t.low);
    TEST_CHECK(callback_count_time1, t.low);
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
        TEST_CHECK(vpi_get(vpiType, cb_data_n1_h), vpiCallback);
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
    TEST_VERBOSE_PRINTF("time_cb2: %d\n", t.low);
    TEST_CHECK(callback_count_time2, t.low);
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
    TEST_CHECK(vpi_get(vpiType, cb_data_n2_h), vpiCallback);
    return 0;
}

static int _start_of_sim_cb(p_cb_data cb_data) {
    TEST_VERBOSE_PRINTF("-_start_of_sim_cb\n");

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
    TEST_CHECK(vpi_get(vpiType, cb_data_n1_h), vpiCallback);

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
    TEST_CHECK(callback_count_start_of_sim, 1);
    if (!errors) fprintf(stdout, "*-* All Finished *-*\n");
    return 0;
}

extern "C" void vpi_compat_bootstrap(void) {
    t_cb_data cb_data;
    bzero(&cb_data, sizeof(cb_data));
    {
        TEST_VERBOSE_PRINTF("register _start_of_sim_cb_h\n");
        cb_data.reason = cbStartOfSimulation;
        cb_data.time = 0;
        cb_data.cb_rtn = _start_of_sim_cb;
        TestVpiHandle _start_of_sim_cb_h = vpi_register_cb(&cb_data);
    }
    {
        TEST_VERBOSE_PRINTF("register _end_of_sim_cb_h\n");
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

#ifdef IVERILOG
// icarus entry
void (*vlog_startup_routines[])() = {vpi_compat_bootstrap, 0};
#endif
