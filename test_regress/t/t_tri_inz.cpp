// -*- mode: C++; c-file-style: "cc-mode" -*-
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2020 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

#include "Vt_tri_inz.h"
#include "Vt_tri_inz___024root.h"

VM_PREFIX* tb = nullptr;
bool pass = true;

double sc_time_stamp() { return 0; }

void checkone(const char* name, int got, int exp) {
    if (got != exp) {
        printf("%%Error: For %s got=%d exp=%d\n", name, got, exp);
        pass = false;
    }
}

void check(int d, int en, int exp0, int exp1, int expx, int expz) {
    tb->d = d;
    tb->rootp->d__en0 = en;
    tb->eval();
#ifdef TEST_VERBOSE
    printf("Drive d=%d en=%d got0=%d/1=%d/x=%d/z=%d  exp0=%d/1=%d/x=%d/z=%d\n", d, en, tb->ext0,
           tb->ext1, tb->extx, tb->extz, exp0, exp1, expx, expz);
#endif
    if (!expz) checkone("ext0", tb->ext0, exp0);
    if (!expz) checkone("ext1", tb->ext1, exp1);
    checkone("extx", tb->extx, expx);
    checkone("extz", tb->extz, expz);
}

int main() {
    Verilated::debug(0);
    tb = new Vt_tri_inz{"tb"};
    check(0, 1, 1, 0, 0, 0);
    check(1, 1, 0, 1, 0, 0);
    check(0, 0, 0, 0, 0, 1);

    if (pass) {
        VL_PRINTF("*-* All Finished *-*\n");
        tb->final();
    } else {
        vl_fatal(__FILE__, __LINE__, "top", "Unexpected results from t_tri_inz\n");
    }
    VL_DO_DANGLING(delete tb, tb);
    return 0;
}
