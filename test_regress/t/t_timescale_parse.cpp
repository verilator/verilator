// -*- mode: C++; c-file-style: "cc-mode" -*-
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2019 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

#include VM_PREFIX_INCLUDE

VM_PREFIX* tb = nullptr;

double s_time = 0.0;

double sc_time_stamp() { return s_time; }

int main() {
    tb = new VM_PREFIX{"tb"};

    s_time = 2 * 1e9;  // e.g. 2 seconds in ns units
    tb->eval();
    tb->eval();
    tb->eval();

    tb->final();
    VL_DO_DANGLING(delete tb, tb);
}
