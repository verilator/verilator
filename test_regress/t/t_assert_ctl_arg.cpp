// -*- mode: C++; c-file-style: "cc-mode" -*-
//
// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

#include "verilated_cov.h"
#include <verilated.h>
#include VM_PREFIX_INCLUDE

// These require the above. Comment prevents clang-format moving them
#include "TestCheck.h"

unsigned int main_time = 0;

double sc_time_stamp() { return main_time; }
//======================================================================

int errors = 0;

void verilatedTest() {
    VerilatedContext context;
    // Assert enable/disable
    context.assertOn(true);
    TEST_CHECK_NZ(context.assertOn());
    context.assertOn(false);
    TEST_CHECK_Z(context.assertOn());
    TEST_CHECK_Z(context.assertOnGet(1, 1));

    // Setting one type
    context.assertOnSet(1, 1);
    TEST_CHECK_NZ(context.assertOnGet(1, 1));
    TEST_CHECK_NZ(context.assertOn());
    TEST_CHECK_Z(context.assertOnGet(2, 2));

    // Setting types
    context.assertOn(false);
    context.assertOnSet(1, 3);
    TEST_CHECK_NZ(context.assertOnGet(1, 3));
    TEST_CHECK_NZ(context.assertOnGet(1, 2));
    TEST_CHECK_NZ(context.assertOnGet(1, 1));
    TEST_CHECK_Z(context.assertOnGet(1, 0));
    TEST_CHECK_Z(context.assertOnGet(2, 0));
    TEST_CHECK_Z(context.assertOnGet(0, 0));

    // Setting multiple types separately
    context.assertOn(false);
    context.assertOnSet(0, 1);
    context.assertOnSet(1, 2);
    context.assertOnSet(2, 3);
    TEST_CHECK_NZ(context.assertOn());
    TEST_CHECK_Z(context.assertOnGet(0, 1));
    TEST_CHECK_Z(context.assertOnGet(1, 1));
    TEST_CHECK_NZ(context.assertOnGet(1, 2));
    TEST_CHECK_NZ(context.assertOnGet(2, 1));
    TEST_CHECK_NZ(context.assertOnGet(2, 2));
    TEST_CHECK_NZ(context.assertOnGet(2, 3));
    TEST_CHECK_Z(context.assertOnGet(0, 2));
    TEST_CHECK_Z(context.assertOnGet(4, 1));
    TEST_CHECK_Z(context.assertOnGet(8, 7));

    // Clearing selected types
    context.assertOn(true);
    context.assertOnClear(1, 3);
    context.assertOnClear(1, 4);
    TEST_CHECK_Z(context.assertOnGet(1, 1));
    TEST_CHECK_Z(context.assertOnGet(1, 2));
    TEST_CHECK_Z(context.assertOnGet(1, 4));
    context.assertOnClear(4, 4);
    TEST_CHECK_Z(context.assertOnGet(4, 4));
    TEST_CHECK_NZ(context.assertOnGet(4, 1));
    TEST_CHECK_NZ(context.assertOnGet(4, 2));
    TEST_CHECK_NZ(context.assertOn());

    // Clearing all assert types
    context.assertOn(true);
    context.assertOnClear(255, 7);
    // Everything is disabled except internal asserts
    TEST_CHECK_NZ(context.assertOn());
    context.assertOn(false);
    // Now everything is disabled
    TEST_CHECK_Z(context.assertOn());
}
int main(int argc, char** argv) {
    verilatedTest();
    if (errors) return 10;

    VerilatedContext context;
    context.threads(1);
    context.commandArgs(argc, argv);
    context.debug(0);

    srand48(5);

    VM_PREFIX top{"top"};
    constexpr uint64_t sim_time = 100;
    while ((context.time() < sim_time) && !context.gotFinish()) {
        top.clk = !top.clk;
        top.eval();
        context.timeInc(1);
    }
    const std::string filename = std::string{VL_STRINGIFY(TEST_OBJ_DIR) "/coverage.dat"};
    context.coveragep()->write(filename);

    if (!context.gotFinish()) {
        vl_fatal(__FILE__, __LINE__, "main", "%Error: Timeout; never got a $finish");
    }
    top.final();

    return 0;
}
