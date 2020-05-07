// -*- mode: C++; c-file-style: "cc-mode" -*-
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2020 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

#include "Vt_tri_select.h"

Vt_tri_select* tb = NULL;

double sc_time_stamp() { return 0; }

bool check() {
    bool pass = true;
#ifdef TEST_VERBOSE
    bool verbose = true;
#else
    bool verbose = false;
#endif

    int Y = ((tb->OE1) & (!tb->OE2))
                ? tb->A1
                : ((!tb->OE1) & (tb->OE2))
                      ? tb->A2
                      : ((tb->OE1) & (tb->OE2)) ? (tb->A1 | tb->A2) : 3;  // pullup

    int W = (((tb->OE2) ? (tb->A2 & 0x1) : 0) << tb->A1)
            | (((tb->OE1) ? (tb->A2 >> 1) & 0x1 : 0) << tb->A2);

    if (tb->Y1 == Y && tb->Y2 == Y && tb->Y3 == Y && tb->W == W) {
        pass = true;
        if (verbose) printf("-  pass: ");
    } else {
        pass = false;
        verbose = true;
        printf("%%E-Fail: ");
    }

    if (verbose)
        printf("Read: OE1=%d OE2=%d A1=0x%x A2=0x%x Y1=0x%x Y2=0x%x Y3=0x%x W=0x%x  Expected: "
               "Y1=Y2=Y3=%d and W=0x%x\n",
               tb->OE1, tb->OE2, tb->A1, tb->A2, tb->Y1, tb->Y2, tb->Y3, tb->W, Y, W);
    return pass;
}

int main() {
    bool pass = true;

    Verilated::debug(0);
    tb = new Vt_tri_select("tb");

    // loop through every possibility and check the result
    for (tb->OE1 = 0; tb->OE1 < 2; tb->OE1++) {
        for (tb->OE2 = 0; tb->OE2 < 2; tb->OE2++) {
            for (tb->A1 = 0; tb->A1 < 4; tb->A1++) {
                for (tb->A2 = 0; tb->A2 < 4; tb->A2++) {
                    tb->eval();
                    if (!check()) { pass = false; }
                }
            }
        }
    }

    if (pass) {
        VL_PRINTF("*-* All Finished *-*\n");
        tb->final();
    } else {
        vl_fatal(__FILE__, __LINE__, "top", "Unexpected results from t_tri_select\n");
    }
    return 0;
}
