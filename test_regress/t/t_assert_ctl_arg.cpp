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
    const std::unique_ptr<VerilatedContext> contextp{new VerilatedContext};
    // Assert enable/disable
    contextp->assertOn(true);
    TEST_CHECK_NZ(contextp->assertOn());
    contextp->assertOn(false);
    TEST_CHECK_Z(contextp->assertOn());
    TEST_CHECK_Z(contextp->assertOnGet(1, 1));

    // Setting one type
    contextp->assertOnSet(1, 1);
    TEST_CHECK_NZ(contextp->assertOnGet(1, 1));
    TEST_CHECK_NZ(contextp->assertOn());
    TEST_CHECK_Z(contextp->assertOnGet(2, 2));

    // Setting types
    contextp->assertOn(false);
    contextp->assertOnSet(1, 3);
    TEST_CHECK_NZ(contextp->assertOnGet(1, 3));
    TEST_CHECK_NZ(contextp->assertOnGet(1, 2));
    TEST_CHECK_NZ(contextp->assertOnGet(1, 1));
    TEST_CHECK_Z(contextp->assertOnGet(1, 0));
    TEST_CHECK_Z(contextp->assertOnGet(2, 0));
    TEST_CHECK_Z(contextp->assertOnGet(0, 0));

    // Setting multiple types separately
    contextp->assertOn(false);
    contextp->assertOnSet(0, 1);
    contextp->assertOnSet(1, 2);
    contextp->assertOnSet(2, 3);
    TEST_CHECK_NZ(contextp->assertOn());
    TEST_CHECK_Z(contextp->assertOnGet(0, 1));
    TEST_CHECK_Z(contextp->assertOnGet(1, 1));
    TEST_CHECK_NZ(contextp->assertOnGet(1, 2));
    TEST_CHECK_NZ(contextp->assertOnGet(2, 1));
    TEST_CHECK_NZ(contextp->assertOnGet(2, 2));
    TEST_CHECK_NZ(contextp->assertOnGet(2, 3));
    TEST_CHECK_Z(contextp->assertOnGet(0, 2));
    TEST_CHECK_Z(contextp->assertOnGet(4, 1));
    TEST_CHECK_Z(contextp->assertOnGet(8, 7));

    // Clearing selected types
    contextp->assertOn(true);
    TEST_CHECK_NZ(contextp->assertOnGet(255, 6));
    contextp->assertOnClear(1, 3);
    contextp->assertOnClear(1, 4);
    TEST_CHECK_Z(contextp->assertOnGet(1, 1));
    TEST_CHECK_Z(contextp->assertOnGet(1, 2));
    TEST_CHECK_Z(contextp->assertOnGet(1, 4));
    contextp->assertOnClear(4, 4);
    TEST_CHECK_Z(contextp->assertOnGet(4, 4));
    TEST_CHECK_NZ(contextp->assertOnGet(4, 1));
    TEST_CHECK_NZ(contextp->assertOnGet(4, 2));
    TEST_CHECK_NZ(contextp->assertOn());

    // Clearing all assert types
    contextp->assertOn(true);
    contextp->assertOnClear(255, 7);
    // Everything is disabled except internal asserts
    TEST_CHECK_NZ(contextp->assertOn());
    contextp->assertOn(false);
    // Now everything is disabled
    TEST_CHECK_Z(contextp->assertOn());
}
int main(int argc, char** argv) {
    verilatedTest();
    if (errors) return 10;

    const std::unique_ptr<VerilatedContext> contextp{new VerilatedContext};
    contextp->threads(1);
    contextp->commandArgs(argc, argv);
    contextp->debug(0);

    srand48(5);

    const std::unique_ptr<VM_PREFIX> topp{new VM_PREFIX{"top"}};
    constexpr uint64_t sim_time = 100;
    while ((contextp->time() < sim_time) && !contextp->gotFinish()) {
        topp->clk = !topp->clk;
        topp->eval();
        contextp->timeInc(1);
    }
    const std::string filename = std::string{VL_STRINGIFY(TEST_OBJ_DIR) "/coverage.dat"};
    contextp->coveragep()->write(filename);

    if (!contextp->gotFinish()) {
        vl_fatal(__FILE__, __LINE__, "main", "%Error: Timeout; never got a $finish");
    }
    topp->final();

    return 0;
}
