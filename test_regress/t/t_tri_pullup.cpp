// -*- mode: C++; c-file-style: "cc-mode" -*-
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2008 by Lane Brooks.
// SPDX-License-Identifier: CC0-1.0

#include "Vt_tri_pullup.h"

VM_PREFIX* tb = nullptr;

double sc_time_stamp() { return 0; }

bool check() {
    bool pass;
    int Z, Y, X;
    if (tb->OE) {
        Z = tb->A;
        Y = tb->A;
        X = tb->A;
    } else {
        Z = 1;
        Y = 0;
        X = 1;
    }

#ifdef TEST_VERBOSE
    bool verbose = true;
#else
    bool verbose = false;
#endif

    if (tb->Z == Z && tb->Y == Y && tb->X == X) {
        if (verbose) printf("PASS: ");
        pass = true;
    } else {
        printf("%%E-FAIL: ");
        verbose = true;
        pass = false;
    }
    if (verbose)
        printf("OE=%d A=%d  X=%d xexp=%d  Y=%d yexp=%d  Z=%d zexp=%d\n", tb->OE, tb->A, tb->X, X,
               tb->Y, Y, tb->Z, Z);
    return pass;
}

int main() {
    bool pass = true;

    Verilated::debug(0);
    tb = new Vt_tri_pullup{"tb"};

    // loop through every possibility and check the result
    for (tb->OE = 0; tb->OE < 2; tb->OE++) {
        for (tb->A = 0; tb->A < 2; tb->A++) {
            tb->eval();
            if (!check()) pass = false;
        }
    }

    if (pass) {
        VL_PRINTF("*-* All Finished *-*\n");
        tb->final();
    } else {
        vl_fatal(__FILE__, __LINE__, "top", "Unexpected results from pullup test\n");
    }
    VL_DO_DANGLING(delete tb, tb);
    return 0;
}
