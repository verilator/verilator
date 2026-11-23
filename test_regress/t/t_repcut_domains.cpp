// -*- mode: C++; c-file-style: "cc-mode" -*-
// DESCRIPTION: Verilator: RepCut activation group differential driver
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2026-2026 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

#include "verilated.h"

#include "Vt_repcut_domains.h"

#include <iostream>

static unsigned observeCounts[2] = {};
static unsigned observeValues[2] = {};

extern "C" void repcut_domains_observe(unsigned domainId, unsigned value) {
    ++observeCounts[domainId];
    observeValues[domainId] = value;
}

int main(int argc, char** argv) {
    VerilatedContext context;
    context.commandArgs(argc, argv);
    context.threads(4);
    context.randReset(0);
    Vt_repcut_domains model{&context};
    unsigned rng = 0x7391ba;
    for (unsigned step = 0; step < 2048; ++step) {
        rng ^= rng << 13;
        rng ^= rng >> 17;
        rng ^= rng << 5;
        model.clk = step > 1 && ((rng >> 20) & 1);
        model.other_clk = step > 1 && ((rng >> 21) & 1);
        model.gate = (rng >> 22) & 1;
        model.reset_n = step > 1 && step % 29;
        // Stop the main domain for odd and even stretches, then reactivate it.
        // This exercises caller-only batches between parallel dispatch epochs.
        if (step % 127 < 61 && step > 8) {
            model.clk = 0;
            model.gate = 0;
            model.reset_n = 1;
            model.other_clk = step & 1;
        }
        model.x = rng & 0x7fff;
        context.timeInc(1);
        model.eval();
        // Re-evaluation without an event must not update sequential state.
        for (unsigned repeat = 0; repeat < 2; ++repeat) {
            for (unsigned i = 0; i < 15; ++i) std::cout << model.q[i] << ' ';
            std::cout << observeCounts[0] << ' ' << observeCounts[1] << ' ' << observeValues[0]
                      << ' ' << observeValues[1] << '\n';
            model.eval();
        }
    }
    model.final();
    std::cout << "*-* All Finished *-*\n";
}
