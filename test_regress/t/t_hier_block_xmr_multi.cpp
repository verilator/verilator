// DESCRIPTION: Verilator: Verilog Test
//
// Both instances of the block read 0x5a through the shared promoted port, so
// each contributes bits 0 and 1 of it: 0 then 1.
//
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

#include <verilated.h>

#include VM_PREFIX_INCLUDE

#include <cstdio>
#include <cstdlib>

int main(int argc, char** argv) {
    Verilated::commandArgs(argc, argv);
    VM_PREFIX* const topp = new VM_PREFIX{"top"};
    for (int i = 0; i < 10; ++i) topp->eval();

    // 0x5a is 0101_1010, so bit 0 is 0 and bit 1 is 1, for both instances
    const unsigned exp = 0xa;
    bool ok = true;
    if (topp->o_bits != exp) {
        printf("%%Error: o_bits=0x%x exp 0x%x\n", (unsigned)topp->o_bits, exp);
        ok = false;
    }
    topp->final();
    VL_DO_DANGLING(delete topp, topp);
    if (!ok) return 10;
    printf("*-* All Finished *-*\n");
    return 0;
}
