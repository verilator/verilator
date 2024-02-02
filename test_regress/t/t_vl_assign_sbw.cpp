// -*- mode: C++; c-file-style: "cc-mode" -*-
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Antmicro.
// SPDX-License-Identifier: CC0-1.0

#include VM_PREFIX_INCLUDE

#include <systemc.h>

#include <sysc/kernel/sc_simcontext.h>

int sc_main(int argc, char* argv[]) {
    using namespace sc_core;

    VM_PREFIX* tb = new VM_PREFIX{"t"};
    constexpr int val = 1;
    sc_signal<sc_biguint<256>> SC_NAMED(in, val);
    sc_signal<sc_biguint<256>> SC_NAMED(out);

    tb->in(in);
    tb->out(out);

    bool pass = out.read().iszero();

    sc_start(1, SC_NS);

    pass &= !out.read().iszero();
    pass &= out == val;

    tb->final();
    VL_DO_DANGLING(delete tb, tb);

    if (pass) { VL_PRINTF("*-* All Finished *-*\n"); }

    return 0;
}
