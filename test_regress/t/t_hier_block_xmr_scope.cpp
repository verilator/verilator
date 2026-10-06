// DESCRIPTION: Verilator: Verilog Test
//
// A dotted path is relative to the module it appears in. leaf_out reaches
// outside the block and must read 0x5a; leaf_in spells the same path at its
// own instance and must keep reading 0x3c.
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

    bool ok = true;
    // 0x5a bit 1, reached out of the block
    if (!(topp->o_bits & 1)) {
        printf("%%Error: leaf_out read %d exp 1\n", (int)(topp->o_bits & 1));
        ok = false;
    }
    // 0x3c bit 2, its own instance; 0 would mean the outer source was used
    if (!(topp->o_bits & 2)) {
        printf("%%Error: leaf_in read %d exp 1 (promoted when it should not be)\n",
               (int)((topp->o_bits >> 1) & 1));
        ok = false;
    }
    topp->final();
    VL_DO_DANGLING(delete topp, topp);
    if (!ok) return 10;
    printf("*-* All Finished *-*\n");
    return 0;
}
