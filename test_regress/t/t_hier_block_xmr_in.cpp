// DESCRIPTION: Verilator: Verilog Test
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// Checks the values arriving through the promoted output ports, which a
// Verilog initial block cannot do here: it would run before the
// combinational network has settled.

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

    TEST_CHECK_HEX_EQ(static_cast<unsigned>(topp->o_blk), 0x5a);
    TEST_CHECK_HEX_EQ(static_cast<unsigned>(topp->o_param), 0x5a);  // de-parameterized block
    TEST_CHECK_HEX_EQ(static_cast<unsigned>(topp->o_sig), 0x5a);  // three levels in
    TEST_CHECK_HEX_EQ(static_cast<unsigned>(topp->o_again), 0x5a);  // same path, one port
    TEST_CHECK_EQ(static_cast<unsigned>(topp->o_bit), 1);  // 0x5a[1]
    TEST_CHECK_HEX_EQ(static_cast<unsigned>(topp->o_part), 0x5);  // 0x5a[7:4]
    TEST_CHECK_EQ(static_cast<unsigned>(topp->o_neg), 1);  // -5 through a signed port
    TEST_CHECK_HEX_EQ(static_cast<unsigned>(topp->o_tdef), 0x3c);  // typedef'd target
    TEST_CHECK_HEX_EQ(static_cast<unsigned>(topp->o_above), 0x5a);  // from above the parent
    // The reference sits in a de-parameterized module, read at two parameters
    TEST_CHECK_EQ(static_cast<unsigned>(topp->o_h0), 1);  // 0x5a[1]
    TEST_CHECK_EQ(static_cast<unsigned>(topp->o_h1), 0);  // 0x5a[2]

    if (!errors) printf("*-* All Finished *-*\n");
    topp->final();
    VL_DO_DANGLING(delete topp, topp);
    return errors ? 10 : 0;
}
