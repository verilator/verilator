// -*- mode: C++; c-file-style: "cc-mode" -*-
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2008 by Lane Brooks.
// SPDX-License-Identifier: CC0-1.0

#include VM_PREFIX_INCLUDE

VM_PREFIX* tb = NULL;

double sc_time_stamp() { return 0; }

bool check() {
    bool pass;
    int c = (tb->A >> tb->SEL) & 0x1;
#ifdef TEST_VERBOSE
    bool verbose = true;
#else
    bool verbose = false;
#endif

    if (tb->W == c && tb->X == c && tb->Y == c && tb->Z == c) {
        pass = true;
        if (verbose) printf("-  pass: ");
    } else {
        pass = false;
        verbose = true;
        printf("%%E-FAIL: ");
    }
    if (verbose) {
        printf("SEL=%d A=%d   got: W=%d X=%d Y=%d Z=%d  exp: WXYZ=%d\n", tb->SEL, tb->A, tb->W,
               tb->X, tb->Y, tb->Z, c);
    }
    return pass;
}

int main() {
    bool pass = true;

    Verilated::debug(0);
    tb = new VM_PREFIX("tb");

    // loop through every possibility and check the result
    for (tb->SEL = 0; tb->SEL < 2; tb->SEL++) {
        for (tb->A = 0; tb->A < 4; tb->A++) {
            tb->eval();
            if (!check()) { pass = false; }
        }
    }

    if (pass) {
        VL_PRINTF("*-* All Finished *-*\n");
        tb->final();
    } else {
        vl_fatal(__FILE__, __LINE__, "top", "Unexpected results from tristate test\n");
    }
    return 0;
}
