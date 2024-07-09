// -*- mode: C++; c-file-style: "cc-mode" -*-
//
// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

#include <verilated.h>

// These require the above. Comment prevents clang-format moving them
#include "TestCheck.h"

//======================================================================

unsigned int main_time = 0;
int errors = 0;

double sc_time_stamp() { return main_time; }

void test() {
    const std::unique_ptr<VerilatedContext> contextp{new VerilatedContext};
    // assertOn
    TEST_CHECK_NZ(contextp->assertOn());
    contextp->assertOn(false);
    TEST_CHECK_Z(contextp->assertOn());
    TEST_CHECK_Z(contextp->assertOnGet(1, 1));

    contextp->assertOnSet(1, 1);
    TEST_CHECK_NZ(contextp->assertOnGet(1, 1));
    TEST_CHECK_NZ(contextp->assertOn());
    TEST_CHECK_Z(contextp->assertOnGet(2, 2));

    contextp->assertOn(false);
    contextp->assertOnSet(1, 3);
    TEST_CHECK_NZ(contextp->assertOnGet(1, 3));
    TEST_CHECK_NZ(contextp->assertOnGet(1, 2));
    TEST_CHECK_NZ(contextp->assertOnGet(1, 1));
    TEST_CHECK_Z(contextp->assertOnGet(1, 0));
    TEST_CHECK_Z(contextp->assertOnGet(2, 0));
    TEST_CHECK_Z(contextp->assertOnGet(0, 0));

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

    contextp->assertOn(true);
    contextp->assertOnClear(255, 7);
    TEST_CHECK_Z(contextp->assertOn());
}
int main() {
    Verilated::debug(0);

    test();

    return errors ? 10 : 0;
}
