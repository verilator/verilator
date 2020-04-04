// -*- mode: C++; c-file-style: "cc-mode" -*-
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2020 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

#include <verilated.h>

#include VM_PREFIX_INCLUDE

unsigned long long main_time = 0;
double sc_time_stamp() { return (double)main_time; }

#include <iostream>
using namespace std;

#define FILENM "t_timescale.cpp"

#define CHECK_RESULT(got, exp) \
    if ((got) != (exp)) { \
        cout << dec << "%Error: " << FILENM << ":" << __LINE__ << ": GOT = " << (got) \
             << "   EXP = " << (exp) << endl; \
        return __LINE__; \
    }

int main(int argc, char** argv, char** env) {
    VM_PREFIX* top = new VM_PREFIX("top");

    CHECK_RESULT(VL_TIME_STR_CONVERT("100s"), 2);
    CHECK_RESULT(VL_TIME_STR_CONVERT("10s"), 1);
    CHECK_RESULT(VL_TIME_STR_CONVERT("1s"), 0);
    CHECK_RESULT(VL_TIME_STR_CONVERT("100ms"), -1);
    CHECK_RESULT(VL_TIME_STR_CONVERT("10ms"), -2);
    CHECK_RESULT(VL_TIME_STR_CONVERT("1ms"), -3);
    CHECK_RESULT(VL_TIME_STR_CONVERT("100us"), -4);
    CHECK_RESULT(VL_TIME_STR_CONVERT("10us"), -5);
    CHECK_RESULT(VL_TIME_STR_CONVERT("1us"), -6);
    CHECK_RESULT(VL_TIME_STR_CONVERT("100ns"), -7);
    CHECK_RESULT(VL_TIME_STR_CONVERT("10ns"), -8);
    CHECK_RESULT(VL_TIME_STR_CONVERT("1ns"), -9);
    CHECK_RESULT(VL_TIME_STR_CONVERT("100ps"), -10);
    CHECK_RESULT(VL_TIME_STR_CONVERT("10ps"), -11);
    CHECK_RESULT(VL_TIME_STR_CONVERT("1ps"), -12);
    CHECK_RESULT(VL_TIME_STR_CONVERT("100fs"), -13);
    CHECK_RESULT(VL_TIME_STR_CONVERT("10fs"), -14);
    CHECK_RESULT(VL_TIME_STR_CONVERT("1fs"), -15);

    CHECK_RESULT(VL_TIME_STR_CONVERT("1.5s"), 0);
    CHECK_RESULT(VL_TIME_STR_CONVERT("1s "), 0);
    CHECK_RESULT(VL_TIME_STR_CONVERT("1ss"), 0);
    CHECK_RESULT(VL_TIME_STR_CONVERT("s"), 0);
    CHECK_RESULT(VL_TIME_STR_CONVERT(0), 0);

    top->final();
    printf("*-* All Finished *-*\n");
    return 0;
}
