// -*- mode: C++; c-file-style: "cc-mode" -*-
// DESCRIPTION: Verilator: Per-domain automatic RepCut publication
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2026-2026 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

#include "verilated.h"

#include "Vt_repcut_publication_auto.h"
#if VM_TRACE
#include "verilated_vcd_c.h"
#endif
#include <array>
#include <cstdlib>
#include <iostream>

static unsigned parallelPublicationCalls = 0;

// The driver instruments the generated parallel dispatchers for this check.
void repcutParallelPublicationSeen() { ++parallelPublicationCalls; }

int main(int argc, char** argv) {
    if (argc != 5) std::abort();
    const bool conditional = std::atoi(argv[3]);
    const bool expectParallelPublication = std::atoi(argv[4]);
    VerilatedContext context;
    context.threads(std::atoi(argv[2]));
    context.randReset(0);
#if VM_TRACE
    context.traceEverOn(true);
#endif
    Vt_repcut_publication_auto model{&context};
    model.clk_a = model.clk_b = model.clk_c = 0;
    model.reset = 1;
    model.enable = 0;
    model.data = 0;
    model.write_mask = 0;
    model.eval();
#if VM_TRACE
    VerilatedVcdC trace;
    model.trace(&trace, 99);
    trace.open(argv[1]);
    trace.dump(0);
#endif
    std::array<std::array<IData, 32>, 128> a{}, c{};
    std::array<std::array<IData, 3>, 8> memory{};
    QData small = 0, auxiliary = 0;
    IData rng = 0x719b3;
    for (unsigned step = 1; step <= 512; ++step) {
        rng ^= rng << 13;
        rng ^= rng >> 17;
        rng ^= rng << 5;
        const bool oldA = model.clk_a, oldB = model.clk_b, oldC = model.clk_c;
        if (step % 2 == 0) model.clk_a = !model.clk_a;
        if (step % 3 == 0) model.clk_b = !model.clk_b;
        if (step % 5 == 0) model.clk_c = !model.clk_c;
        model.reset = step < 30 || step % 127 < 15;
        // Exercise long idle/active bursts and isolated enables at both ends
        // of the bounded OR tree, with independent simultaneous clock edges.
        const unsigned activity = (step / 64) % 4;
        model.enable = activity == 1 || (activity >= 2 && ((rng >> 9) & 1));
        model.write_mask = activity == 0   ? 0
                           : activity == 1 ? ~QData{0}
                                           : (QData{rng} << 32) | rng;
        if (activity == 3) {
            const unsigned bit = (step & 4) ? 63 : 0;
            model.write_mask = QData{1} << bit;
        }
        model.data = rng;
        if (!oldB && model.clk_b) {
            if (model.reset) {
                for (unsigned j = 0; j < 8; ++j) memory[j] = {{j, 0, 0}};
            } else if (model.enable) {
                for (unsigned w = 0; w < 3; ++w)
                    memory[rng & 7][w] = (rng & 8) ? rng + 1 : memory[rng & 7][w] ^ rng;
                memory[rng & 7][2] &= 0x7fffffff;
            }
            if (model.reset)
                small = auxiliary = 0;
            else if (model.enable)
                small = auxiliary = (small + rng) & 0x7fffffffffffffffULL;
        }
        for (unsigned g = 0; g < 128; ++g) {
            for (unsigned w = 0; w < 32; ++w) {
                if (!oldA && model.clk_a) {
                    if (model.reset)
                        a[g][w] = w ? 0 : g;
                    else if (!conditional || ((model.write_mask >> (g / 2)) & 1))
                        a[g][w] ^= rng + g;
                }
                if (!oldC && model.clk_c) {
                    if (model.reset)
                        c[g][w] = w ? 0 : g;
                    else if (model.enable)
                        c[g][w] ^= rng - g;
                }
            }
            a[g][31] &= 0x7fffffff;
            c[g][31] &= 0x7fffffff;
        }
        context.timeInc(1);
        model.eval();
        model.eval();
        if (model.narrow != small || model.auxiliary != auxiliary) std::abort();
        for (unsigned w = 0; w < 3; ++w)
            if (model.memory_view[w] != (conditional ? memory[rng & 7][w] : 0)) std::abort();
        // Output elements deliberately straddle C++ word boundaries.
        for (unsigned g = 0; g < 128; ++g) {
            for (unsigned bit = 0; bit < 1023; ++bit) {
                const unsigned pos = 1023 * g + bit;
                if (((model.balanced[pos / 32] >> (pos % 32)) & 1)
                    != ((a[g][bit / 32] >> (bit % 32)) & 1))
                    std::abort();
                if (((model.skewed[pos / 32] >> (pos % 32)) & 1)
                    != ((c[g][bit / 32] >> (bit % 32)) & 1))
                    std::abort();
            }
        }
#if VM_TRACE
        if (step < 32 || step % 7 == 0) trace.dump(context.time());
#endif
    }
    model.final();
    if ((parallelPublicationCalls != 0) != expectParallelPublication) {
        std::cerr << "Publication did not use the selected execution policy\n";
        std::abort();
    }
#if VM_TRACE
    trace.close();
#endif
    std::cout << "*-* All Finished *-*\n";
}
