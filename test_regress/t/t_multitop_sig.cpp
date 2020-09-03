// -*- mode: C++; c-file-style: "cc-mode" -*-
//
// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2006 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

#include <iostream>
#include <verilated.h>
#include "Vt_multitop_sig.h"

// Use cout to avoid issues with %d/%lx etc
#define CHECK_RESULT(got, exp) \
    if ((got) != (exp)) { \
        std::cout << std::dec << "%Error: " << __FILE__ << ":" << __LINE__ << ": GOT = " << (got) \
                  << "   EXP = " << (exp) << std::endl; \
        return __LINE__; \
    }

int main(int argc, char* argv[]) {
    Vt_multitop_sig* topp = new Vt_multitop_sig("");

    Verilated::debug(0);

    {
        topp->a__02Ein = 0;
        topp->b__02Ein = 0;
        topp->uniq_in = 0;
        topp->eval();
        CHECK_RESULT(topp->a__02Eout, 1);
        CHECK_RESULT(topp->b__02Eout, 0);
        CHECK_RESULT(topp->uniq_out, 1);
        topp->a__02Ein = 1;
        topp->b__02Ein = 1;
        topp->uniq_in = 1;
        topp->eval();
        CHECK_RESULT(topp->a__02Eout, 0);
        CHECK_RESULT(topp->b__02Eout, 1);
        CHECK_RESULT(topp->uniq_out, 0);
    }
    printf("*-* All Finished *-*\n");
}
