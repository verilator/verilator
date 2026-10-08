// DESCRIPTION: Verilator: Verilog Test
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// Checks the values arriving through the promoted ports, which a Verilog
// initial block cannot do here: it would run before the combinational
// network has settled.

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

    TEST_CHECK_HEX_EQ(static_cast<unsigned>(topp->o_ph), 0x5a);
    TEST_CHECK_EQ(static_cast<unsigned>(topp->o_en), 1);
    TEST_CHECK_HEX_EQ(static_cast<unsigned>(topp->o_pub), 0xa);
    TEST_CHECK_EQ(static_cast<unsigned>(topp->o_neg),
                  1);  // -5 read through a signed promoted port
    TEST_CHECK_HEX_EQ(static_cast<unsigned>(topp->o_part), 0x5);  // 0x5a[7:4], a part select
    TEST_CHECK_HEX_EQ(static_cast<unsigned>(topp->o_ph2),
                      0x5a);  // second module, same path, one port
    // leaf_out reads 0x5a[1]; leaf_in keeps its own 0x3c[2]. A 0 in either bit
    // means that module's reference was rewritten the wrong way.
    TEST_CHECK_HEX_EQ(static_cast<unsigned>(topp->o_scope), 0x3);
    TEST_CHECK_EQ(static_cast<unsigned>(topp->o_param), 1);  // 1 ^ 0x5a[2], SEL parameterized to 2
    // Two instances of one block, each contributing 0x5a bits 0 and 1
    TEST_CHECK_HEX_EQ(static_cast<unsigned>(topp->o_gen), 0xa);

    topp->final();
    VL_DO_DANGLING(delete topp, topp);
    if (errors) return 10;
    std::cout << "*-* All Finished *-*" << std::endl;
    return 0;
}
