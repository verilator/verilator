// DESCRIPTION: Verilator: Verilog Test
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// The block is de-parameterized, so its promoted port has to be matched under
// the mangled name. o is i ^ ph[P], with i 1, ph 0x5a and P 2.
//
#include <verilated.h>

#include VM_PREFIX_INCLUDE

#include <iostream>

// These require the above. Comment prevents clang-format moving them
#include "TestCheck.h"

int errors = 0;

int main(int argc, char** argv) {
    Verilated::commandArgs(argc, argv);
    VM_PREFIX* const topp = new VM_PREFIX{"top"};
    for (int i = 0; i < 10; ++i) topp->eval();

    TEST_CHECK_EQ(topp->o_bit, 1);  // 1 ^ 0x5a[2] == 1 ^ 0
    topp->final();
    VL_DO_DANGLING(delete topp, topp);
    if (errors) return 10;
    std::cout << "*-* All Finished *-*" << std::endl;
    return 0;
}
