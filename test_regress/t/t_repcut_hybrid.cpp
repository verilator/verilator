// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Source/graph RepCut boundary regression
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2026-2026 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//*************************************************************************

#include "verilated.h"

#include "Vt_repcut_hybrid.h"

#include <array>
#include <iostream>

int main(int argc, char** argv) {
    VerilatedContext context;
    context.commandArgs(argc, argv);
    context.threads(REPCUT_TEST_THREADS);
    context.randReset(0);
    Vt_repcut_hybrid model{&context};
    IData random = 137;
    IData q = 0;
    IData r = 0;
    std::array<IData, 24> wide{};
    std::array<IData, 3> memory{};
    for (unsigned cycle = 0; cycle < 4096; ++cycle) {
        std::cout << "CYCLE " << cycle << '\n';
        random = random * 1664525U + 1013904223U;
        model.clk = 0;
        model.reset = cycle % 257 == 0;
        model.enable = cycle % 7 != 0;
        model.event_enable = cycle % 19 == 0 || cycle % 19 == 1;
        model.data = random;
        model.denom = (random >> 16) & 15;
        model.address = cycle % 4;
        model.eval();
        IData expensive = 0;
        for (unsigned i = 0; i < 24; ++i) expensive ^= model.data / (model.denom | (2 * i + 1));
#ifdef REPCUT_GRAPH_ONLY
        const IData shared = model.data;
#else
        const IData shared = (expensive + model.data) ^ q;
        if (model.q != q || model.r != r || model.observed != (shared ^ r)) return 1;
        if (model.enable && model.address < 3) memory[model.address] = shared ^ wide[0];
#endif
        if (model.reset) {
#ifndef REPCUT_GRAPH_ONLY
            q = 0;
            r = 7;
#endif
            wide.fill(0);
        } else if (model.enable) {
#ifndef REPCUT_GRAPH_ONLY
            const IData oldq = q;
            q = shared + r;
            r = oldq ^ model.data;
#endif
            for (unsigned i = 0; i < 24; ++i) wide[23 - i] = shared / (model.denom | (2 * i + 1));
        }
        model.clk = 1;
        model.eval();
        for (unsigned repeat = 0; repeat < 2; ++repeat) {
            if (model.q != q || model.r != r) return 2;
            for (unsigned i = 0; i < 24; ++i) {
                if (model.wide[i] != wide[i]) return 3;
            }
            if (model.mem_out != (model.address < 3 ? memory[model.address] : 0)) return 4;
#ifdef REPCUT_GRAPH_ONLY
            if (model.observed != 0) return 5;
#else
            if (model.observed != (((expensive + model.data) ^ q) ^ r)) return 5;
#endif
            model.eval();
        }
    }
    model.final();
    std::cout << "*-* All Finished *-*\n";
}
