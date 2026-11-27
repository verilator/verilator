// -*- mode: C++; c-file-style: "cc-mode" -*-
// DESCRIPTION: Verilator: RepCut DPI calls and scheduling oracle
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2026-2026 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

#include "verilated.h"

#include "Vt_repcut_dpi_arrays.h"
#include "Vt_repcut_dpi_arrays__Dpi.h"

#include <cstdlib>
#include <iostream>
#include <thread>

static unsigned calls = 0;
static unsigned initializations = 0;
static unsigned cookie = 0;
static std::thread::id caller;
static void check(bool condition) {
    if (!condition) std::abort();
}
extern "C" void* repcut_array_init() {
    check(std::this_thread::get_id() == caller);
    ++initializations;
    return &cookie;
}
extern "C" unsigned repcut_array_tick(void* handle, const svOpenArrayHandle descending,
                                      const svOpenArrayHandle ascending,
                                      const svOpenArrayHandle reply) {
    check(std::this_thread::get_id() == caller && handle == &cookie);
    check(svLow(descending, 1) == 3 && svHigh(descending, 1) == 7);
    check(svLow(ascending, 1) == 2 && svHigh(ascending, 1) == 6);
    check(svLow(reply, 1) == 3 && svHigh(reply, 1) == 7);
    ++calls;
    unsigned result = calls * 0x193acaU;
    for (int i = 0; i < 5; ++i) {
        const unsigned char a
            = *static_cast<const unsigned char*>(svGetArrElemPtr1(descending, i + 3));
        const unsigned char b
            = *static_cast<const unsigned char*>(svGetArrElemPtr1(ascending, i + 2));
        *static_cast<unsigned char*>(svGetArrElemPtr1(reply, i + 3)) = a ^ b ^ calls;
        result = (result * 33U) ^ (a + (b << 8));
    }
    return result;
}
static void setBits(unsigned* words, unsigned low, unsigned width, unsigned value) {
    for (unsigned bit = 0; bit < width; ++bit) {
        const unsigned pos = low + bit;
        words[pos / 32]
            = (words[pos / 32] & ~(1U << (pos % 32))) | (((value >> bit) & 1U) << (pos % 32));
    }
}
int main(int argc, char** argv) {
    VerilatedContext context;
    context.commandArgs(argc, argv);
    context.threads(REPCUT_TEST_THREADS);
    context.randReset(0);
    caller = std::this_thread::get_id();
    Vt_repcut_dpi_arrays model{&context};
    unsigned q[3] = {}, previous = 0, observed = 0, expectedCalls = 0;
#ifdef PARTIAL_ARRAY
    unsigned heldLane = 0xc7U;
#endif
    model.clk = 0;
    model.eval();
    for (unsigned step = 0; step < 257; ++step) {
        model.reset = step == 0 || step % 47 == 0;
        model.enable = step % 5 != 0;
        for (unsigned word = 0; word < 3; ++word)
            model.x[word] = (step + word * 7539U) * 0x193acaU ^ 0xabcdefU;
        model.x[2] &= 0x7fffffffU;
        model.clk = 0;
        model.eval();
#ifdef PARTIAL_ARRAY
        if (step != 0) {
            if (model.reset)
                heldLane = 0xc7U;
            else if (model.enable)
                heldLane = (heldLane + 0x13U) & 255U;
        }
#endif
        const uint64_t rtl
            = model.reset ? 0 : ((uint64_t{model.x[1] ^ q[1]} << 32) | (model.x[0] ^ q[0]));
        if (model.reset) {
            q[0] = q[1] = q[2] = previous = observed = 0;
        } else if (model.enable) {
            ++expectedCalls;
            unsigned reply[5];
            observed = expectedCalls * 0x193acaU;
            for (unsigned i = 0; i < 5; ++i) {
                const unsigned lowA = 8 * i, lowB = lowA + 40;
                unsigned a = ((model.x[lowA / 32] >> (lowA % 32)) & 255U) ^ (3 * i + 1);
                const unsigned b
                    = (((model.x[lowB / 32] >> (lowB % 32)) & 255U) + 5 * i + 7) & 255U;
#ifdef PARTIAL_ARRAY
                if (i == 2) a = heldLane;
#endif
                reply[i] = (a ^ b ^ expectedCalls) & 255U;
                observed = (observed * 33U) ^ (a + (b << 8));
            }
            previous = q[0];
            q[0] = model.x[0];
            q[1] = model.x[1];
            q[2] = observed & 0x7fffffffU;
            setBits(q, 17, 17, (reply[0] << 9) | (reply[2] << 1) | (observed & 1));
            setBits(q, 80, 15, ((reply[1] & 127) << 8) | reply[4]);
        }
        model.clk = 1;
        model.eval();
        for (unsigned word = 0; word < 3; ++word) check(model.q[word] == q[word]);
        check(model.previous == previous && model.observed == observed && model.rtl == rtl);
        check(calls == expectedCalls && initializations == unsigned(expectedCalls != 0));
        model.x[0] ^= 0x7539U;
        model.eval();
        check(calls == expectedCalls && model.q[0] == q[0]);
    }
    model.final();
    std::cout << "*-* All Finished *-*\n";
}
