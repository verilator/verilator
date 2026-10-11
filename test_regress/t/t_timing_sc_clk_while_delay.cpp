// -*- mode: C++; c-file-style: "cc-mode" -*-
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 ViraSemi Inc.
// SPDX-License-Identifier: CC0-1.0

#include VM_PREFIX_INCLUDE

using namespace sc_core;

// A 10ns clock drives the model while it waits on a long delay
int sc_main(int argc, char* argv[]) {
    sc_clock clk{"clk", 10, SC_NS};
    VM_PREFIX* tb = new VM_PREFIX{"tb"};
    tb->clk(clk);

    while (!Verilated::gotFinish() && sc_time_stamp() < sc_time(2, SC_US)) sc_start(1, SC_NS);
    if (!Verilated::gotFinish())
        vl_fatal(__FILE__, __LINE__, "tb", "Timeout; never got a $finish\n");

    tb->final();
    VL_DO_DANGLING(delete tb, tb);
    return 0;
}
