// DESCRIPTION: Verilator: Verilog Test
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// A dotted path is relative to the module it appears in. leaf_out reaches
// outside the block and must read 0x5a; leaf_in spells the same path at its
// own instance and must keep reading 0x3c.
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

    // 0x5a bit 1, reached out of the block
    TEST_CHECK_EQ(topp->o_bits & 1, 1);
    // 0x3c bit 2, its own instance; 0 would mean the outer source was used
    TEST_CHECK_EQ((topp->o_bits >> 1) & 1, 1);
    topp->final();
    VL_DO_DANGLING(delete topp, topp);
    if (errors) return 10;
    std::cout << "*-* All Finished *-*" << std::endl;
    return 0;
}
