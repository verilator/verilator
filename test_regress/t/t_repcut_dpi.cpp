// -*- mode: C++; c-file-style: "cc-mode" -*-
// DESCRIPTION: Verilator: RepCut DPI calls and scheduling oracle
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2026-2026 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

#include "verilated.h"

#include "Vt_repcut_dpi.h"
#include "Vt_repcut_dpi__Dpi.h"

#include <cstdlib>
#include <cstring>
#include <iostream>
#include <thread>

static unsigned calls = 0;
static unsigned wideCalls = 0;
static std::thread::id caller;
static void check(bool condition) {
    if (!condition) std::abort();
}
extern "C" unsigned int repcut_tick(const char* tag, unsigned int x, unsigned int* y,
                                    unsigned int* z) {
    check(std::this_thread::get_id() == caller);
    check(!std::strcmp(tag, "first") || !std::strcmp(tag, "second"));
    ++calls;
    *y = x * 3U + 7U;
    *z += x ^ 0x5a5aU;
    const unsigned result = *y ^ *z;
    std::cout << "ORDER call " << tag << ' ' << std::hex << result << '\n';
    return result;
}
extern "C" void repcut_wide(const svLogicVecVal* x, svLogicVecVal* y) {
    check(std::this_thread::get_id() == caller);
    ++wideCalls;
    for (unsigned i = 0; i < 3; ++i) {
        check(x[i].bval == 0);
        y[i].aval = x[i].aval ^ (0x12345678U + i);
        y[i].bval = 0;
    }
}
int main(int argc, char** argv) {
    VerilatedContext context;
    context.commandArgs(argc, argv);
    context.threads(2);
    context.randReset(0);
    caller = std::this_thread::get_id();
    Vt_repcut_dpi model{&context};
    unsigned q = 0, old = 0, z = 0, rtl = 0, expectedCalls = 0, expectedWide = 0;
    unsigned wide[3] = {};
    model.clk = 0;
    model.eval();
    check(calls == 0 && wideCalls == 0);
    for (unsigned step = 0; step < 256; ++step) {
        model.reset = step == 0 || step % 47 == 0;
        model.enable = step % 5 != 0;
        model.x = step * 0x193acaU ^ 0xabcdefU;
        model.clk = 0;
        model.eval();
        const unsigned previousQ = q;
        if (model.reset) {
            q = old = 0;
            z = 1;
            wide[0] = wide[1] = wide[2] = 0;
        } else if (model.enable) {
            std::cout << "EXPECT before " << std::hex << q << '\n';
            unsigned y = 0;
            const auto tick = [&](const char* tag, unsigned x) {
                ++expectedCalls;
                y = x * 3U + 7U;
                z += x ^ 0x5a5aU;
                const unsigned r = y ^ z;
                std::cout << "EXPECT call " << tag << ' ' << std::hex << r << '\n';
                return r;
            };
            unsigned r = tick("first", (model.x ^ rtl) + q);
            if (r & 1U) r = tick("second", y ^ r);
            ++expectedWide;
            wide[0] = z ^ 0x12345678U;
            wide[1] = y ^ 0x12345679U;
            wide[2] = (r ^ 0x1234567aU) & 0x7fffffffU;
            old = q;
            q = y + z + r;
            std::cout << "EXPECT after " << std::hex << r << '\n';
        }
        rtl = model.reset ? 0 : model.x + previousQ;
        model.clk = 1;
        model.eval();
        check(model.q == q && model.old_q == old && model.rtl_q == rtl);
        for (unsigned i = 0; i < 3; ++i) check(model.wide_q[i] == wide[i]);
        check(calls == expectedCalls && wideCalls == expectedWide);
        model.x ^= 0x7539U;
        model.eval();
        check(calls == expectedCalls && wideCalls == expectedWide && model.q == q);
    }
    model.final();
    std::cout << "*-* All Finished *-*\n";
}
