// DESCRIPTION: Verilator: Check shared class fields published by different workers
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026-2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

#include "verilated.h"

#include "Vt_repcut_shared_state.h"

#include <array>
#include <cstdio>
#include <cstdlib>

int main(int argc, char** argv) {
    VerilatedContext context;
    context.commandArgs(argc, argv);
    context.threads(2);
    Vt_repcut_shared_state model{&context};
    std::array<std::array<uint32_t, 1025>, 2> state{};
    uint32_t random = 0x135792abU;
    for (unsigned step = 0; step < 128; ++step) {
        model.clk = 0;
        for (unsigned i = 0; i < 2; ++i) {
            random ^= random << 13;
            random ^= random >> 17;
            random ^= random << 5;
            model.a[i] = random;
        }
        model.eval();
        model.clk = 1;
        model.eval();
        for (unsigned i = 0; i < 2; ++i) {
            for (unsigned word = 0; word < state[i].size(); ++word) {
                if (model.q[i][word] != state[i][word]) {
                    std::fprintf(stderr, "step %u instance %u word %u: got %x expected %x\n", step,
                                 i, word, model.q[i][word], state[i][word]);
                    std::abort();
                }
            }
            if (model.auxiliary[i] != model.a[i]) std::abort();
            for (unsigned word = state[i].size() - 1; word; --word)
                state[i][word] = state[i][word - 1];
            state[i].back() &= 1;
            state[i][0] = model.a[i];
        }
    }
    model.final();
    std::puts("*-* All Finished *-*");
}
