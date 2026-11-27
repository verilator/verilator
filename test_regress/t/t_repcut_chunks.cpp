// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Guarded RepCut chunk regression
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

#include "Vt_repcut_chunks.h"

#include <iostream>

int main(int argc, char** argv) {
    VerilatedContext context;
    context.commandArgs(argc, argv);
    context.threads(REPCUT_TEST_THREADS);
    context.randReset(0);
    Vt_repcut_chunks model{&context};
    IData random = 17;
    IData q = 0;
    IData count = 0;
    for (unsigned cycle = 0; cycle < 4096; ++cycle) {
        random = random * 1664525U + 1013904223U;
        model.clk = 0;
        model.reset = cycle == 0 || cycle % 257 == 0;
        model.en = cycle % 11 != 0;
        model.reverse = (cycle / 128) & 1;
        model.a = (random >> 7) & 127;
        for (unsigned word = 0; word < 4; ++word) model.mask[word] = 0;
        // Visit every leaf in both directions, plus multiple-hit and no-hit
        // paths. Neither the selection oracle nor its priority uses a chain.
        const unsigned bit = cycle % 128;
        model.mask[bit / 32] = 1U << (bit % 32);
        if (cycle % 3 == 0) model.mask[(127 - bit) / 32] |= 1U << ((127 - bit) % 32);
        if (cycle % 17 == 0) {
            for (unsigned word = 0; word < 4; ++word) model.mask[word] = 0;
        }
        model.eval();
        if (model.q != q || model.count != count) return 1;
        IData next = q;
        if (model.reset) {
            next = 0;
            count = 0;
        } else if (model.en) {
            int chosen = -1;
            for (int bit = 0; bit < 128; ++bit) {
                if (!(model.mask[bit / 32] & (1U << (bit % 32)))) continue;
                if (chosen < 0 || model.reverse) chosen = bit;
            }
            if (chosen >= 0) {
                const IData value = model.reverse ? model.a + chosen : model.a ^ chosen;
                next = (value ^ count) & 127;
            }
            count = (count + q + 1) & 0x7fffffffU;
        }
        q = next;
        model.clk = 1;
        model.eval();
        if (model.q != q || model.count != count) {
            std::cerr << "Priority/old-state mismatch at cycle " << cycle << '\n';
            return 1;
        }
        model.eval();
        if (model.q != q || model.count != count) return 1;
    }
    model.final();
    std::cout << "*-* All Finished *-*\n";
    return 0;
}
