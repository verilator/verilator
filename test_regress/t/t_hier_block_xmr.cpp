// DESCRIPTION: Verilator: Verilog Test
//
// Checks the values arriving through the promoted ports, which a Verilog
// initial block cannot do here: it would run before the combinational
// network has settled.
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
    if (topp->o_ph != 0x5a) {
        printf("%%Error: o_ph=0x%02x exp 0x5a\n", (unsigned)topp->o_ph);
        ok = false;
    }
    if (topp->o_en != 1) {
        printf("%%Error: o_en=%d exp 1\n", (int)topp->o_en);
        ok = false;
    }
    if (topp->o_pub != 0xa) {
        printf("%%Error: o_pub=0x%x exp 0xa\n", (unsigned)topp->o_pub);
        ok = false;
    }
    if (topp->o_neg != 1) {  // -5 read through a signed promoted port
        printf("%%Error: o_neg=%d exp 1 (signedness lost)\n", (int)topp->o_neg);
        ok = false;
    }
    topp->final();
    VL_DO_DANGLING(delete topp, topp);
    if (!ok) return 10;
    printf("*-* All Finished *-*\n");
    return 0;
}
