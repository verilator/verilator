// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Test conditional RepCut evaluation and publication
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

#include "Vt_repcut_control.h"

#include <array>
#include <iostream>

int main() {
    VerilatedContext context;
    context.threads(2);
    context.randReset(0);
    Vt_repcut_control model{&context};
    model.clk = 0;
    model.eval();
    unsigned q = 5;
    std::array<uint32_t, 3> wideq{{0, 0, 0}};
    std::array<unsigned, 3> memory{{11, 22, 33}};
    uint32_t rng = 23;
    const auto randomWord = [&]() {
        rng ^= rng << 13;
        rng ^= rng >> 17;
        rng ^= rng << 5;
        return rng;
    };
    const auto check = [&]() {
        for (unsigned word = 0; word < 3; ++word) {
            if (model.wq[word] != wideq[word]) {
                std::cerr << "Wide signed result mismatch at word " << word << '\n';
                return false;
            }
            const uint32_t expected
                = model.select ? model.wa[word] ^ model.wb[word] : model.wa[word] & model.wb[word];
            if (model.wide_result[word] != expected) {
                std::cerr << "Wide combinational output mismatch at word " << word << '\n';
                return false;
            }
        }
        const unsigned a = model.a;
        const unsigned b = model.b;
        const unsigned sum = (a + b) & 127;
        const unsigned term = ((a ^ b) + 0x13) & 127;
        const unsigned localResult = ((term & a) ^ (term + b)) & 127;
        if (model.local_result != localResult) {
            std::cerr << "Block-local expression mismatch\n";
            return false;
        }
        const unsigned y
            = model.mode ? (model.en ? (sum ^ a) + b : b - a) : (model.select ? a * b : a ^ b);
        const unsigned data
            = model.mode ? (model.en ? (model.rd < 3 ? memory[model.rd] : 0) : b) : a;
        if (model.observed_y != ((y ^ q) & 127)) {
            std::cerr << "Output fanout mismatch\n";
            return false;
        }
        if (model.q == q && model.y == (y & 127) && model.data == data) return true;
        std::cerr << "Mismatch: q=" << unsigned{model.q} << '/' << q << " y=" << unsigned{model.y}
                  << '/' << (y & 127) << " data=" << unsigned{model.data} << '/' << data << '\n';
        return false;
    };
    for (unsigned cycle = 0; cycle < 4096; ++cycle) {
        model.clk = 0;
        model.a = randomWord() & 127;
        model.b = randomWord() & 127;
        model.mode = cycle & 7;
        model.en = randomWord() & 1;
        model.select = randomWord() & 1;
        model.reset = (cycle % 17) == 0;
        model.rd = randomWord() & 3;
        model.wr = randomWord() & 3;
        for (unsigned word = 0; word < 3; ++word) {
            model.wa[word] = randomWord();
            model.wb[word] = randomWord();
        }
        model.wa[2] &= 0x7fffffffU;
        model.wb[2] &= 0x7fffffffU;
        model.eval();
        if (!check()) return 1;
        const unsigned sum = (model.a + model.b) & 127;
        if (model.reset) {
            wideq = {{0, 0, 0}};
        } else if (model.en) {
            uint64_t carry = 0;
            for (unsigned word = 0; word < 3; ++word) {
                const uint32_t shifted = (model.wa[word] >> 3)
                                         | (word < 2 ? model.wa[word + 1] << 29
                                            : (model.wa[2] & 0x40000000U) ? 0x70000000U
                                                                          : 0);
                const uint64_t total = uint64_t{shifted} + model.wb[word] + carry;
                wideq[word] = total;
                carry = total >> 32;
            }
            wideq[2] &= 0x7fffffffU;
        }
        if (model.reset) {
            q = 0;
        } else {
            if (model.mode) q = model.en ? sum ^ q : (q + model.b) & 127;
            if (model.select) q = model.a;
        }
        if (model.mode) {
            if (model.en) {
                if (model.wr < 3) memory[model.wr] = model.select ? model.a ^ model.b : sum;
            } else if (model.rd < 3) {
                memory[model.rd] = model.a;
            }
        }
        model.clk = 1;
        model.eval();
        if (!check()) return 2;
        // Input-only changes must settle without applying another state update.
        model.a = randomWord() & 127;
        model.en ^= 1;
        model.select ^= 1;
        model.wa[1] ^= 0x89abcdefU;
        model.eval();
        if (!check()) return 3;
    }
    model.final();
    std::cout << "*-* All Finished *-*\n";
    return 0;
}
