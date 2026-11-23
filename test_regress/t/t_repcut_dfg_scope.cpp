// DESCRIPTION: Verilator: Check independent state in repeated RepCut module instances
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026-2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

#include "verilated.h"

#include "Vt_repcut_dfg_scope.h"

#include <array>
#include <cstdio>
#include <cstdlib>

int main(int argc, char** argv) {
    VerilatedContext context;
    context.commandArgs(argc, argv);
    context.threads(2);
    Vt_repcut_dfg_scope model{&context};
    std::array<uint32_t, 2> state{}, other{};
    uint32_t random = 0x135792abU;
    for (unsigned step = 0; step < 256; ++step) {
        std::array<std::array<uint32_t, 4>, 2> expected;
        model.clk = 0;
        for (unsigned i = 0; i < 2; ++i) {
            random ^= random << 13;
            random ^= random >> 17;
            random ^= random << 5;
            model.a[i] = random;
            model.b[i] = random + step;
            model.c[i] = random ^ (0x87654321U >> i);
            const uint32_t shared = other[i] ^ (state[i] & model.c[i]);
            expected[i] = {model.c[i] ^ model.a[i], (shared ^ state[i]) | (shared + state[i]),
                           model.b[i], model.b[i]};
            other[i] = state[i] + model.a[i];
            state[i] = model.a[i] ^ model.b[i] ^ model.c[i];
        }
        model.eval();
        model.clk = 1;
        model.eval();
        for (unsigned i = 0; i < 2; ++i) {
            for (unsigned word = 0; word < 4; ++word) {
                if (model.q[i][word] != expected[i][word]) {
                    std::fprintf(stderr, "step %u instance %u word %u: got %x expected %x\n", step,
                                 i, word, model.q[i][word], expected[i][word]);
                    std::abort();
                }
            }
        }
    }
    model.final();
    std::puts("*-* All Finished *-*");
}
