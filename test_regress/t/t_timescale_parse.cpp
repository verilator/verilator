// -*- mode: C++; c-file-style: "cc-mode" -*-
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2019 by Wilson Snyder

#include "Vt_timescale_parse.h"

VM_PREFIX* tb = nullptr;

double sc_time_stamp() {
    return 2 * 1e9;  // e.g. 2 seconds in ns units
}

int main() {
    tb = new VM_PREFIX{"tb"};

    tb->eval();
    tb->eval();
    tb->eval();

    tb->final();
    VL_DO_DANGLING(delete tb, tb);
}
