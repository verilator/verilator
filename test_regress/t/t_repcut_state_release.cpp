// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: RepCut guarded state release regression
//
// Code available from: https://verilator.org
//
//*************************************************************************
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2026-2026 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#include "verilated.h"

#include "Vt_repcut_state_release.h"

#if VM_TRACE_VCD
#include "verilated_vcd_c.h"
#endif

#include <array>
#include <cstdlib>
#include <iostream>

extern "C" unsigned int state_release_observe(unsigned int value) { return value; }

static void check(uint32_t actual, uint32_t expected, const char* name, unsigned step) {
    if (actual != expected) {
        std::cerr << name << " mismatch at " << step << ": " << actual << " != " << expected
                  << '\n';
        std::exit(1);
    }
}

int main(int argc, char** argv) {
    VerilatedContext context;
    context.commandArgs(argc, argv);
    context.threads(REPCUT_TEST_THREADS);
    context.randReset(0);
#if VM_TRACE_VCD
    context.traceEverOn(true);
#endif
    Vt_repcut_state_release model{&context};
#if VM_TRACE_VCD
    VerilatedVcdC trace;
    model.trace(&trace, 99);
    trace.open(argv[1]);
#endif
    uint32_t rng = 0x193aca;
    uint32_t a = 0, b = 0, c = 0, swapA = 0, swapB = 0, guarded = 0, narrow = 0;
    uint32_t observed = 0;
    // Model of the USER_TABLE's single-entry cache: an entry is only written
    // when `always @(narrow)` actually fires, i.e. on a change.
    bool table0 = false;
    std::array<uint32_t, 3> wide{};
#ifdef REPCUT_TEST_DECODER
    std::array<uint32_t, 4> decoded{};
#endif
    bool previousClock2 = false;
    for (unsigned step = 0; step < 2048; ++step) {
        rng ^= rng << 13;
        rng ^= rng >> 17;
        rng ^= rng << 5;
        const uint32_t data = rng & 0x7fffU;
        const bool enable = (rng >> 17) & 1U;
        const bool reset = step % 127 < 2;
        const bool clock2 = (step / 3) & 1U;
        if (REPCUT_TEST_OBSERVER == 2 && clock2 && !previousClock2) observed = a;
        previousClock2 = clock2;
        model.data = data;
        model.enable = enable;
        model.reset = reset;
#ifdef REPCUT_TEST_DECODER
        for (unsigned word = 0; word < 4; ++word) {
            model.mask[word] = 0x9e3779b9U * (step + 1 + word * 13);
            const uint32_t oldDecode
                = model.mask[word] ^ (narrow / 32 == word ? (1U << (narrow % 32)) : 0U);
            if (reset)
                decoded[word] = 0;
            else if (enable)
                decoded[word] = oldDecode;
        }
#endif
        model.clk = 0;
        model.clk2 = clock2;
        model.eval();
#if VM_TRACE_VCD
        trace.dump(context.time());
#endif
        context.timeInc(1);
        if (REPCUT_TEST_OBSERVER == 1 && step < 40) observed = a;
        const uint32_t snapshot = a ^ b ^ c;
        const uint32_t later = a ^ guarded;
        const uint32_t nextA = reset ? 1 : enable ? data : a;
        const uint32_t nextB = reset ? 2 : enable ? a : b;
        const uint32_t nextC = reset ? 3 : enable ? b : c;
        const uint32_t nextSwapA = reset ? 7 : swapB;
        const uint32_t nextSwapB = reset ? 11 : swapA;
        guarded = reset ? 13 : (a & 1U) ? data : guarded ^ data;
        const uint32_t nextNarrow = reset ? 0 : enable ? data & 0x7fU : narrow;
        if (REPCUT_TEST_OBSERVER == 5) {
            // `always @(narrow)` only runs when narrow changes, so a held reset
            // leaves the table all-zero and observed at 0.
            if (nextNarrow != narrow) table0 = nextNarrow == 0;
            observed = table0;
        }
        narrow = nextNarrow;
        if (reset) {
            wide = {{1, 0, 0}};
        } else if (enable) {
            wide = {{(wide[0] >> 15) | (wide[1] << 17), (wide[1] >> 15) | (wide[2] << 17),
                     (wide[2] >> 15) | (data << 16)}};
        }
        a = nextA;
        if (REPCUT_TEST_OBSERVER == 3 || REPCUT_TEST_OBSERVER == 4) observed = a;
        b = nextB;
        c = nextC;
        swapA = nextSwapA;
        swapB = nextSwapB;
        model.clk = 1;
        model.eval();
#if VM_TRACE_VCD
        trace.dump(context.time());
#endif
        context.timeInc(1);
        check(model.a, a, "a", step);
        check(model.b, b, "b", step);
        check(model.c, c, "c", step);
        check(model.snapshot, snapshot, "snapshot", step);
        check(model.later, later, "later", step);
        check(model.swap_a, swapA, "swap_a", step);
        check(model.swap_b, swapB, "swap_b", step);
        check(model.guarded, guarded, "guarded", step);
        check(model.narrow, narrow, "narrow", step);
        check(model.observed, observed, "observed", step);
#ifdef REPCUT_TEST_DECODER
        for (unsigned word = 0; word < 4; ++word) {
            const uint32_t newDecode
                = model.mask[word] ^ (narrow / 32 == word ? (1U << (narrow % 32)) : 0U);
            check(model.decoded[word], decoded[word], "old-state decoder", step);
            check(model.decoded_live[word], newDecode, "settled decoder", step);
        }
#endif
        for (unsigned word = 0; word < 3; ++word)
            check(model.wide[word], wide[word], "wide", step);
        model.eval();
        check(model.a, a, "a without edge", step);
        check(model.snapshot, snapshot, "snapshot without edge", step);
    }
    model.final();
#if VM_TRACE_VCD
    trace.close();
#endif
    std::cout << "*-* All Finished *-*\n";
}
