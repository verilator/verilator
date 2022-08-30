// -*- mode: C++; c-file-style: "cc-mode" -*-
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2008 by Lane Brooks.
// SPDX-License-Identifier: CC0-1.0

#include "Vt_tri_inout.h"

VM_PREFIX* tb = nullptr;

double sc_time_stamp() { return 0; }

bool check() {
    bool pass;
    int Z;
    if (tb->SEL) {
        Z = tb->A;
    } else {
        Z = tb->B;
    }

    if (tb->Z == tb->Y1 && tb->Z == tb->Y2 && tb->Z == Z) {
        printf("PASS: ");
        pass = true;
    } else {
        printf("FAIL: ");
        pass = false;
    }
#ifdef TEST_VERBOSE
    printf("SEL=%d A=%d B=%d Z=%d Y1=%d Y2=%d\n", tb->SEL, tb->A, tb->B, tb->Z, tb->Y1, tb->Y2);
#endif
    return pass;
}

int main() {
    bool pass = true;

    Verilated::debug(0);
    tb = new Vt_tri_inout{"tb"};

    // loop through every possibility and check the result
    for (tb->SEL = 0; tb->SEL < 2; tb->SEL++) {
        for (tb->A = 0; tb->A < 2; tb->A++) {
            for (tb->B = 0; tb->B < 2; tb->B++) {
                tb->eval();
                if (!check()) pass = false;
            }
        }
    }
    tb->SEL = tb->A = tb->B = 0;

    for (int i = 0; i < 256; ++i) {
        tb->clk = 0;
        tb->eval();
        tb->clk = 1;
        tb->eval();
        if (tb->done) break;
        if (i + 1 == 256) pass = false;
    }

    if (pass) {
        VL_PRINTF("*-* All Finished *-*\n");
        tb->final();
    } else {
        vl_fatal(__FILE__, __LINE__, "top", "Unexpected results from inout test\n");
    }
    VL_DO_DANGLING(delete tb, tb);
    return 0;
}
