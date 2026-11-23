// -*- mode: C++; c-file-style: "cc-mode" -*-
// DESCRIPTION: Verilator: Trace activity across RepCut publication joins
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2026-2026 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

#include "verilated.h"

#include "Vt_repcut_trace.h"
#if VM_TRACE_FST
#include "verilated_fst_c.h"
#else
#include "verilated_vcd_c.h"
#endif

#include <array>
#include <cstdlib>
#include <iostream>

int main(int argc, char** argv) {
    if (argc != 3) std::abort();
    VerilatedContext context;
    context.commandArgs(argc, argv);
    context.threads(std::atoi(argv[2]));
    context.randReset(0);
    context.traceEverOn(true);
    Vt_repcut_trace model{&context, ""};
    model.clk_a = 0;
    model.clk_b = 0;
    model.reset = 1;
    model.en = 0;
    model.data = 0;
    model.eval();
#if VM_TRACE_FST
    VerilatedFstC trace;
#else
    VerilatedVcdC trace;
#endif
    model.trace(&trace, 99);
    trace.open(argv[1]);
    trace.dump(context.time());
    std::array<std::array<IData, REPCUT_STATE_WORDS>, 64> expected{};
    IData expectedStructured = 0;
    IData rng = 0x719b3;
    for (unsigned step = 1; step <= 1024; ++step) {
        rng ^= rng << 13;
        rng ^= rng >> 17;
        rng ^= rng << 5;
        const bool oldA = model.clk_a;
        const bool oldB = model.clk_b;
        if (step % 2 == 0) model.clk_a = !model.clk_a;
        if (step % 3 == 0) model.clk_b = !model.clk_b;
        model.reset = step < 12 || step % 127 < 8;
        model.en = step % 37 < 12 ? 0 : (rng >> 8) & 15;
        model.data = rng;
        if (!oldA && model.clk_a) {
            if (model.reset) {
                expectedStructured = 0;
            } else if (model.en & 1U) {
                expectedStructured += model.data + 5;
            }
        }
        for (unsigned g = 0; g < expected.size(); ++g) {
            const bool edge = g % 2 ? !oldB && model.clk_b : !oldA && model.clk_a;
            if (edge) {
                if (model.reset) {
                    expected[g].fill(0);
                    expected[g][0] = g;
                } else if (model.en & (1U << (g % 4))) {
                    QData carry = QData{model.data} + g + 1;
                    for (IData& word : expected[g]) {
                        carry += word;
                        word = carry;
                        carry >>= 32;
                    }
                }
            }
        }
        context.timeInc(1);
        model.eval();
        model.eval();  // No edge: neither state nor accumulated activity may be lost.
        if (model.structured != expectedStructured) std::abort();
        for (unsigned g = 0; g < expected.size(); ++g) {
            for (unsigned word = 0; word < expected[g].size(); ++word) {
                if (model.result[g * REPCUT_STATE_WORDS + word] != expected[g][word]) {
                    std::cerr << "State mismatch at step " << step << " bank " << g << '\n';
                    std::abort();
                }
            }
        }
        // Also exercise several evaluations between dumps and inactive domains.
        if (step < 32 || step % 7 == 0) trace.dump(context.time());
    }
    model.final();
    trace.close();
    std::cout << "*-* All Finished *-*\n";
    return 0;
}
