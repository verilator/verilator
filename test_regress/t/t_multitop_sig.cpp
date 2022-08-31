// -*- mode: C++; c-file-style: "cc-mode" -*-
//
// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2006 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

#include <verilated.h>

#include "Vt_multitop_sig.h"

#include <iostream>

// These require the above. Comment prevents clang-format moving them
#include "TestCheck.h"

double sc_time_stamp() { return 0; }

int errors = 0;

int main(int argc, char* argv[]) {
    Vt_multitop_sig* topp = new Vt_multitop_sig{""};

    Verilated::debug(0);

    {
        topp->a__02Ein = 0;
        topp->b__02Ein = 0;
        topp->uniq_in = 0;
        topp->eval();
        TEST_CHECK_EQ(topp->a__02Eout, 1);
        TEST_CHECK_EQ(topp->b__02Eout, 0);
        TEST_CHECK_EQ(topp->uniq_out, 1);
        topp->a__02Ein = 1;
        topp->b__02Ein = 1;
        topp->uniq_in = 1;
        topp->eval();
        TEST_CHECK_EQ(topp->a__02Eout, 0);
        TEST_CHECK_EQ(topp->b__02Eout, 1);
        TEST_CHECK_EQ(topp->uniq_out, 0);
    }

    topp->final();
    VL_DO_DANGLING(delete topp, topp);

    printf("*-* All Finished *-*\n");
    return errors ? 10 : 0;
}
