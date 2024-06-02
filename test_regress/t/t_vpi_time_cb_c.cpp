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

#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <iostream>

// These require the above. Comment prevents clang-format moving them
#include "TestCheck.h"
#include "TestSimulator.h"
#include "TestVpi.h"

int errors = 0;

unsigned int callback_count1 = 0;
unsigned int callback_count2 = 0;
unsigned int callback_time1 = 0;
unsigned int callback_time2 = 0;

//======================================================================

static int _never_cb(p_cb_data cb_data) {
    TEST_CHECK_EQ(0, 1);  // Should never get called
    return 0;
}

static int _time_cb1(p_cb_data cb_data) {
    s_vpi_time t;
    t.type = vpiSimTime;
    vpi_get_time(0, &t);
    TEST_VERBOSE_PRINTF("time_cb1: %d\n", t.low);
    ++callback_count1;
    if (callback_time1) TEST_CHECK_EQ(callback_time1, t.low);
    callback_time1 = t.low + 1;  // Next call

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
        TEST_CHECK_EQ(vpi_get(vpiType, cb_data_n1_h), vpiCallback);
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
    // One-shot
    s_vpi_time t;
    t.type = vpiSimTime;
    vpi_get_time(0, &t);
    TEST_VERBOSE_PRINTF("time_cb2: %d\n", t.low);
    if (callback_time2) TEST_CHECK_EQ(callback_time2, t.low);
    ++callback_count2;

    t_cb_data cb_data_n;
    bzero(&cb_data_n, sizeof(cb_data_n));

    cb_data_n.reason = cbAfterDelay;
    t.type = vpiSimTime;
    t.high = 0;
    t.low = 1;
    cb_data_n.time = &t;
    cb_data_n.cb_rtn = _time_cb2;
    TestVpiHandle cb_data_n2_h = vpi_register_cb(&cb_data_n);
    TEST_CHECK_EQ(vpi_get(vpiType, cb_data_n2_h), vpiCallback);
    return 0;
}

extern "C" void dpii_init() {
    TEST_VERBOSE_PRINTF("-dpii_init()\n");

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
    TEST_CHECK_EQ(vpi_get(vpiType, cb_data_n1_h), vpiCallback);

    cb_data_n2.reason = cbAfterDelay;
    t2.type = vpiSimTime;
    t2.high = 0;
    t2.low = 4;
    cb_data_n2.time = &t2;
    cb_data_n2.cb_rtn = _time_cb2;
    TestVpiHandle cb_data_n2_h = vpi_register_cb(&cb_data_n2);
}

extern "C" void dpii_final() {
    TEST_VERBOSE_PRINTF("-dpii_final()\n");

    // Allow some slop as cb might be before/after this call
    TEST_CHECK(callback_count1, 1010, (callback_count1 >= 1000 && callback_count1 <= 1020));
    TEST_CHECK(callback_count2, 1010, (callback_count2 >= 1000 && callback_count2 <= 1020));

    if (errors) {
        vpi_control(vpiStop);
    } else {
        printf("*-* All Finished *-*\n");
    }
}
