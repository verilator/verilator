// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
// DESCRIPTION: Verilator: Early state-aware RepCut graph exploration
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

#include "Vt_repcut_runtime.h"

#include <iostream>

struct CheckedModel final {
    Vt_repcut_runtime model;
    uint32_t rng = 17;
    unsigned a = 0x13;
    unsigned b = 0x29;
    unsigned previous;
    unsigned cycle = 0;

    CheckedModel(VerilatedContext* contextp, const char* name, unsigned first)
        : model{contextp, name}
        , previous{first} {
        model.clk = first;
    }
    unsigned randomWord() {
        rng ^= rng << 13;
        rng ^= rng >> 17;
        rng ^= rng << 5;
        return rng;
    }
    void step() {
        model.x = randomWord() & 255;
        model.y = randomWord() & 255;
        model.en = randomWord() & 1;
        model.reset = randomWord() & 1;
        model.force_b = randomWord() & 1;
        if (cycle && cycle % 3 == 0) model.clk = !model.clk;
        if ((!cycle && REPCUT_INITIAL_EDGE)
            || (cycle && previous != model.clk && model.clk == !REPCUT_NEGEDGE)) {
            const unsigned sum = (unsigned(model.x) + model.y) & 255;
            const unsigned nextA = model.reset ? 0 : model.en ? sum ^ b : a;
            b = model.reset ? 0 : model.force_b ? sum : a;
            a = nextA;
        }
        previous = model.clk;
        model.eval();
        if (model.a != a || model.b != b || model.observation != (a ^ b)
            || model.controlled != ((model.x & 1) ? a : b)
            || model.clock_data != (model.clk ? a : b) || model.constant_data != 0x5a
            || model.repeated != (model.x & 3) * 0x55) {
            VL_FATAL_MT(__FILE__, __LINE__, "", "Shared-pool runtime mismatch");
        }
        ++cycle;
    }
};

int main() {
    for (const bool shared : {false, true}) {
        // Cover separate pools and interleaved models sharing one pool.
        VerilatedContext survivorContext;
        survivorContext.threads(2);
        survivorContext.randReset(0);
        CheckedModel survivor{&survivorContext, "survivor", 0};
        for (unsigned first = 0; first < 2; ++first) {
            VerilatedContext modelContext;
            modelContext.threads(2);
            modelContext.randReset(0);
            CheckedModel model{shared ? &survivorContext : &modelContext, "temporary", first};
            for (unsigned cycle = 0; cycle < 4096; ++cycle) {
                model.step();
                if (cycle % 3 == 0) survivor.step();
            }
            model.model.final();
        }
        survivor.step();
        survivor.model.final();
    }
    std::cout << "*-* All Finished *-*\n";
    return 0;
}
