// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: RepCut population count regression
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

#include "Vt_repcut_countones.h"

#include <cstdlib>
#include <iostream>

static unsigned countBits(uint64_t value) {
    unsigned result = 0;
    while (value) {
        result += value & 1;
        value >>= 1;
    }
    return result;
}

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
    Vt_repcut_countones model{&context};
    uint32_t rng = 0x193aca;
    const auto randomWord = [&]() {
        rng ^= rng << 13;
        rng ^= rng >> 17;
        rng ^= rng << 5;
        return rng;
    };
    uint32_t state31 = 0, state64 = 0, state95 = 0, state129 = 0;
    unsigned truncated = 0, singleBit = 0;
    for (unsigned step = 0; step < 4096; ++step) {
        model.data31 = randomWord() & 0x7fffffffU;
        model.data64 = uint64_t{randomWord()} | (uint64_t{randomWord()} << 32);
        for (unsigned n = 0; n < 3; ++n) model.data95[n] = randomWord();
        for (unsigned n = 0; n < 5; ++n) model.data129[n] = randomWord();
        // Cover zero, all ones, and individual bits at every word boundary.
        if (step % 11 < 2) {
            const uint32_t fill = step % 11 ? ~uint32_t{0} : 0;
            model.data31 = fill;
            model.data64 = uint64_t{fill} | (uint64_t{fill} << 32);
            for (unsigned n = 0; n < 3; ++n) model.data95[n] = fill;
            for (unsigned n = 0; n < 5; ++n) model.data129[n] = fill;
        } else if (step % 11 == 2) {
            model.data31 = uint32_t{1} << (step % 31);
            model.data64 = uint64_t{1} << (step % 64);
            for (unsigned n = 0; n < 3; ++n) model.data95[n] = 0;
            for (unsigned n = 0; n < 5; ++n) model.data129[n] = 0;
            model.data95[(step % 95) / 32] = uint32_t{1} << (step % 95 % 32);
            model.data129[(step % 129) / 32] = uint32_t{1} << (step % 129 % 32);
        }
        model.data31 &= 0x7fffffffU;
        model.data95[2] &= 0x7fffffffU;
        model.data129[4] &= 1;
        model.reset = step < 4 || step % 71 == 0;
        model.enable = randomWord() & 1;
        model.select = randomWord() & 1;
        model.clk = 0;
        unsigned wide95 = 0, wide129 = 0;
        for (unsigned n = 0; n < 3; ++n) wide95 += countBits(model.data95[n]);
        for (unsigned n = 0; n < 5; ++n) wide129 += countBits(model.data129[n]);
        const auto observed = [&]() -> uint32_t {
            return model.select ? (countBits(model.data31) + countBits(model.data64)) ^ state95
                                : (wide95 + wide129) ^ state31;
        };
        model.eval();
        check(model.observed, observed(), "pre-edge output", step);
        if (model.reset) {
            state31 = 3;
            state64 = 5;
            state95 = 7;
            state129 = 11;
            truncated = singleBit = 0;
        } else if (model.enable) {
            const uint32_t next31
                = model.select && (model.data31 & 2) ? wide129 + state31 : observed() + state64;
            const uint32_t next64 = countBits(model.data64 ^ state31);
            const uint32_t next95 = wide95 + state129;
            const uint32_t next129 = wide129 ^ state95;
            state31 = next31;
            state64 = next64;
            state95 = next95;
            state129 = next129;
            truncated = wide95 & 15;
            singleBit = model.data31 & 1;
        }
        model.clk = 1;
        for (unsigned repeat = 0; repeat < 3; ++repeat) {
            model.eval();
            check(model.observed, observed(), "post-edge output", step);
            check(model.state31, state31, "31-bit cone", step);
            check(model.state64, state64, "64-bit count", step);
            check(model.state95, state95, "95-bit signed count", step);
            check(model.state129, state129, "129-bit count", step);
            check(model.truncated, truncated, "truncated count", step);
            check(model.single_bit, singleBit, "single-bit count", step);
        }
    }
    model.final();
    std::cout << "*-* All Finished *-*\n";
    return 0;
}
