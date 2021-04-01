// -*- mode: C++; c-file-style: "cc-mode" -*-
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2020 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

#include <verilated.h>

#include "TestCheck.h"

#include VM_PREFIX_INCLUDE

unsigned long long main_time = 0;
double sc_time_stamp() { return (double)main_time; }

#include <iostream>

#define FILENM "t_timescale.cpp"

int errors = 0;

int main(int argc, char** argv, char** env) {
    VM_PREFIX* top = new VM_PREFIX("top");

    TEST_CHECK_EQ(VL_TIME_STR_CONVERT("100s"), 2);
    TEST_CHECK_EQ(VL_TIME_STR_CONVERT("10s"), 1);
    TEST_CHECK_EQ(VL_TIME_STR_CONVERT("1s"), 0);
    TEST_CHECK_EQ(VL_TIME_STR_CONVERT("100ms"), -1);
    TEST_CHECK_EQ(VL_TIME_STR_CONVERT("10ms"), -2);
    TEST_CHECK_EQ(VL_TIME_STR_CONVERT("1ms"), -3);
    TEST_CHECK_EQ(VL_TIME_STR_CONVERT("100us"), -4);
    TEST_CHECK_EQ(VL_TIME_STR_CONVERT("10us"), -5);
    TEST_CHECK_EQ(VL_TIME_STR_CONVERT("1us"), -6);
    TEST_CHECK_EQ(VL_TIME_STR_CONVERT("100ns"), -7);
    TEST_CHECK_EQ(VL_TIME_STR_CONVERT("10ns"), -8);
    TEST_CHECK_EQ(VL_TIME_STR_CONVERT("1ns"), -9);
    TEST_CHECK_EQ(VL_TIME_STR_CONVERT("100ps"), -10);
    TEST_CHECK_EQ(VL_TIME_STR_CONVERT("10ps"), -11);
    TEST_CHECK_EQ(VL_TIME_STR_CONVERT("1ps"), -12);
    TEST_CHECK_EQ(VL_TIME_STR_CONVERT("100fs"), -13);
    TEST_CHECK_EQ(VL_TIME_STR_CONVERT("10fs"), -14);
    TEST_CHECK_EQ(VL_TIME_STR_CONVERT("1fs"), -15);

    TEST_CHECK_EQ(VL_TIME_STR_CONVERT("1.5s"), 0);
    TEST_CHECK_EQ(VL_TIME_STR_CONVERT("1s "), 0);
    TEST_CHECK_EQ(VL_TIME_STR_CONVERT("1ss"), 0);
    TEST_CHECK_EQ(VL_TIME_STR_CONVERT("s"), 0);
    TEST_CHECK_EQ(VL_TIME_STR_CONVERT(0), 0);

    top->final();
    VL_DO_DANGLING(delete top, top);
    printf("*-* All Finished *-*\n");

    return errors ? 10 : 0;
}
