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

#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <iostream>

// These require the above. Comment prevents clang-format moving them
#include "TestCheck.h"

int errors = 0;

vluint64_t main_time = 0;
#ifdef T_WRAPPER_LEGACY
#elif defined(T_WRAPPER_LEGACY_TIME64)
vluint64_t vl_time_stamp64() { return main_time; }
#elif defined(T_WRAPPER_LEGACY_TIMED)
double sc_time_stamp() { return main_time; }
#endif

int main(int argc, char** argv, char** env) {
    // Test that the old non-context Verilated:: calls all work
    // (This test should never get updated to use context)

    // Many used only by git@github.com:djg/verilated-rs.git

    Verilated::commandArgs(argc, argv);  // Commonly used
    TEST_CHECK_CSTR(Verilated::commandArgsPlusMatch("not-matching"), "");

    const char* argadd[] = {"+testingPlusAdd+2", nullptr};
    Verilated::commandArgsAdd(1, argadd);
    TEST_CHECK_CSTR(Verilated::commandArgsPlusMatch("testingPlusAdd"), "+testingPlusAdd+2");

    Verilated::assertOn(true);
    TEST_CHECK_EQ(Verilated::assertOn(), true);

    Verilated::calcUnusedSigs(true);
    TEST_CHECK_EQ(Verilated::calcUnusedSigs(), true);

    Verilated::debug(9);  // Commonly used
    TEST_CHECK_EQ(Verilated::debug(), 9);
    Verilated::debug(0);

    Verilated::errorLimit(2);
    TEST_CHECK_EQ(Verilated::errorLimit(), 2);

    Verilated::fatalOnError(true);
    TEST_CHECK_EQ(Verilated::fatalOnError(), true);

    Verilated::fatalOnVpiError(true);
    TEST_CHECK_EQ(Verilated::fatalOnVpiError(), true);

    Verilated::gotError(false);
    TEST_CHECK_EQ(Verilated::gotError(), false);

    Verilated::gotFinish(false);
    TEST_CHECK_EQ(Verilated::gotFinish(), false);  // Commonly used

    Verilated::mkdir(VL_STRINGIFY(TEST_OBJ_DIR) "/mkdired");

    Verilated::randReset(0);
    TEST_CHECK_EQ(Verilated::randReset(), 0);

    Verilated::randSeed(1234);
    TEST_CHECK_EQ(Verilated::randSeed(), 1234);

    Verilated::traceEverOn(true);  // Commonly used

    TEST_CHECK_CSTR(Verilated::productName(), Verilated::productName());
    TEST_CHECK_CSTR(Verilated::productVersion(), Verilated::productVersion());

    TEST_CHECK_EQ(Verilated::timeunit(), 12);
    TEST_CHECK_EQ(Verilated::timeprecision(), 12);

    TEST_CHECK_EQ(sizeof(vluint8_t), 1);  // Intentional use of old typedef
    TEST_CHECK_EQ(sizeof(vluint16_t), 2);  // Intentional use of old typedef
    TEST_CHECK_EQ(sizeof(vluint32_t), 4);  // Intentional use of old typedef
    TEST_CHECK_EQ(sizeof(vluint64_t), 8);  // Intentional use of old typedef
    TEST_CHECK_EQ(sizeof(vlsint8_t), 1);  // Intentional use of old typedef
    TEST_CHECK_EQ(sizeof(vlsint16_t), 2);  // Intentional use of old typedef
    TEST_CHECK_EQ(sizeof(vlsint32_t), 4);  // Intentional use of old typedef
    TEST_CHECK_EQ(sizeof(vlsint64_t), 8);  // Intentional use of old typedef

    VM_PREFIX* topp = new VM_PREFIX{};

    topp->eval();
    topp->clk = 0;

    VL_PRINTF("Starting\n");

    vluint64_t sim_time = 100;
    while (
#ifdef T_WRAPPER_LEGACY
        Verilated::time()
#else
        vl_time_stamp64()
#endif
            < sim_time
        && !Verilated::gotFinish()) {
        TEST_CHECK_EQ(VL_TIME_Q(), main_time);
        TEST_CHECK_EQ(VL_TIME_D(), main_time);

        main_time += 1;
#ifdef T_WRAPPER_LEGACY
        Verilated::timeInc(1);
        // Check reading and writing of time
        Verilated::time(Verilated::time());
#endif

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
    return errors ? 10 : 0;
}
