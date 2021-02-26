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

#include VM_PREFIX_INCLUDE

#include <cstdlib>
#include <cstdio>
#include <cstring>
#include <iostream>

bool got_error = false;

// Use cout to avoid issues with %d/%lx etc
#define CHECK_RESULT(got, exp) \
    if ((got) != (exp)) { \
        std::cout << std::dec << "%Error: " << __FILE__ << ":" << __LINE__ << ": GOT = " << (got) \
                  << "   EXP = " << (exp) << std::endl; \
        got_error = true; \
    }
#define CHECK_RESULT_CSTR(got, exp) \
    if (strcmp((got), (exp))) { \
        printf("%%Error: %s:%d: GOT = '%s'   EXP = '%s'\n", __FILE__, __LINE__, \
               (got) ? (got) : "<null>", (exp) ? (exp) : "<null>"); \
        return __LINE__; \
    }

vluint64_t main_time = 0;

#ifdef T_WRAPPER_LEGACY_TIME64
vluint64_t vl_time_stamp64() { return main_time; }
#endif
#ifdef T_WRAPPER_LEGACY
double sc_time_stamp() { return main_time; }
#endif

int main(int argc, char** argv, char** env) {
    // Test that the old non-context Verilated:: calls all work
    // (This test should never get updated to use context)

    // Many used only by git@github.com:djg/verilated-rs.git

    Verilated::commandArgs(argc, argv);  // Commonly used
    CHECK_RESULT_CSTR(Verilated::commandArgsPlusMatch("not-matching"), "");

    Verilated::assertOn(true);
    CHECK_RESULT(Verilated::assertOn(), true);

    Verilated::calcUnusedSigs(true);
    CHECK_RESULT(Verilated::calcUnusedSigs(), true);

    Verilated::debug(9);  // Commonly used
    CHECK_RESULT(Verilated::debug(), 9);
    Verilated::debug(0);

    Verilated::fatalOnVpiError(true);
    CHECK_RESULT(Verilated::fatalOnVpiError(), true);

    Verilated::gotFinish(false);
    CHECK_RESULT(Verilated::gotFinish(), false);  // Commonly used

    Verilated::mkdir(VL_STRINGIFY(TEST_OBJ_DIR) "/mkdired");

    Verilated::randReset(0);
    CHECK_RESULT(Verilated::randReset(), 0);

    Verilated::traceEverOn(true);  // Commonly used

    CHECK_RESULT_CSTR(Verilated::productName(), Verilated::productName());
    CHECK_RESULT_CSTR(Verilated::productVersion(), Verilated::productVersion());

    if (Verilated::timeunit()) {}
    if (Verilated::timeprecision()) {}

    VM_PREFIX* topp = new VM_PREFIX();

    topp->eval();
    topp->clk = 0;

    VL_PRINTF("Starting\n");

    vluint64_t sim_time = 100;
    while (vl_time_stamp64() < sim_time && !Verilated::gotFinish()) {
        CHECK_RESULT(VL_TIME_Q(), main_time);
        CHECK_RESULT(VL_TIME_D(), main_time);
        main_time += 1;
        topp->clk = !topp->clk;
        topp->eval();
    }

    topp->final();
    Verilated::flushCall();
    Verilated::runFlushCallbacks();

    Verilated::internalsDump();
    Verilated::scopesDump();

    VL_DO_DANGLING(delete topp, topp);
    Verilated::runExitCallbacks();
    return got_error ? 10 : 0;
}
