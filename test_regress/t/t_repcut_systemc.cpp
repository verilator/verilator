// -*- mode: C++; c-file-style: "cc-mode" -*-
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026-2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

#include VM_PREFIX_INCLUDE

int sc_main(int argc, char** argv) {
    Verilated::commandArgs(argc, argv);
    sc_core::sc_signal<bool> clk, reset;
    sc_core::sc_signal<uint32_t> x7, q7;
    sc_core::sc_signal<sc_dt::sc_biguint<15>> x15, q15;
    sc_core::sc_signal<sc_dt::sc_biguint<33>> x33, q33;
    sc_core::sc_signal<sc_dt::sc_bv<65>> x65, q65;
    VM_PREFIX top{"top"};
    top.clk(clk);
    top.reset(reset);
    top.x7(x7);
    top.x15(x15);
    top.x33(x33);
    top.x65(x65);
    top.q7(q7);
    top.q15(q15);
    top.q33(q33);
    top.q65(q65);

    uint32_t expected7 = 0;
    uint32_t expected15 = 0;
    uint64_t expected33 = 0;
    sc_dt::sc_biguint<65> expected65 = 0;
    uint64_t random = 0xfedcba9876543210ULL;
    for (unsigned cycle = 0; cycle < 1024; ++cycle) {
        random ^= random << 13;
        random ^= random >> 7;
        random ^= random << 17;
        const bool rst = cycle % 127 == 0;
        sc_dt::sc_biguint<65> data65 = random;
        data65[64] = cycle & 1U;
        clk.write(false);
        reset.write(rst);
        x7.write(random & 0x7fU);
        x15.write(random & 0x7fffU);
        x33.write(random & 0x1ffffffffULL);
        x65.write(sc_dt::sc_bv<65>{data65});
        sc_core::sc_start(1, sc_core::SC_NS);
        if (rst) {
            expected7 = expected15 = 0;
            expected33 = 0;
            expected65 = 0;
        } else {
            expected7 = (expected7 + (random & 0x7fU)) & 0x7fU;
            expected15 ^= random & 0x7fffU;
            expected33 = (expected33 + random) & 0x1ffffffffULL;
            expected65 = ((expected65 << 1) | (expected65 >> 64)) ^ data65;
        }
        clk.write(true);
        sc_core::sc_start(1, sc_core::SC_NS);
        if (q7.read() != expected7 || q15.read().to_uint() != expected15
            || q33.read().to_uint64() != expected33
            || q65.read() != sc_dt::sc_bv<65>{expected65}) {
            vl_fatal(__FILE__, __LINE__, "top", "SystemC RepCut state mismatch");
        }
    }
    top.final();
    VL_PRINTF("*-* All Finished *-*\n");
    return 0;
}
