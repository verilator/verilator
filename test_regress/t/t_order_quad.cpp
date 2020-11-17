// -*- mode: C++; c-file-style: "cc-mode" -*-
//
// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2010 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

#include <verilated.h>
#include "Vt_order_quad.h"

//======================================================================

unsigned int main_time = 0;

double sc_time_stamp() { return main_time; }

VM_PREFIX* topp = nullptr;
bool fail = false;

void check(QData got, QData exp) {
    if (got != exp) {
        VL_PRINTF("%%Error: got=0x%" VL_PRI64 "x exp=0x%" VL_PRI64 "x\n", got, exp);
        fail = true;
    }
}

int main(int argc, char* argv[]) {
    topp = new VM_PREFIX;

    Verilated::debug(0);

    topp->a0 = 0;
    topp->eval();
    check(topp->y, 0x0ULL);

    topp->a0 = 15;
    topp->eval();
    check(topp->y, 0x3c00000000ULL);

    if (!fail) {
        VL_PRINTF("*-* All Finished *-*\n");
        topp->final();
    } else {
        vl_fatal(__FILE__, __LINE__, "top", "Unexpected results\n");
    }

    VL_DO_DANGLING(delete topp, topp);
    return 0;
}
