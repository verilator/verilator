// DESCRIPTION: Verilator: Verilog Test
//
// The block is de-parameterized, so its promoted port has to be matched under
// the mangled name. o is i ^ ph[P], with i 1, ph 0x5a and P 2.
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
    if (topp->o_bit != 1) {  // 1 ^ 0x5a[2] == 1 ^ 0
        printf("%%Error: o_bit=%d exp 1\n", (int)topp->o_bit);
        ok = false;
    }
    topp->final();
    VL_DO_DANGLING(delete topp, topp);
    if (!ok) return 10;
    printf("*-* All Finished *-*\n");
    return 0;
}
