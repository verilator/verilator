// DESCRIPTION: Verilator: Independent subgraph clocks and three receivers
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

#include "verilated.h"

#include <cstdio>

#include VM_PREFIX_INCLUDE

int main(int argc, char** argv) {
    VerilatedContext context;
    context.commandArgs(argc, argv);
    Vt_subgraph_shared_limits top{&context};
    top.clk_a = 0;
    top.clk_b = 0;
    top.d = 17;
    top.eval();

    top.clk_a = 1;
    top.eval();
    if (top.q0 != 17 || top.q1 != 17 || top.q2 != 17 || top.q3 != 17 || top.q5 != 17
        || top.q6 != 17 || top.q7 != 17 || top.q8 != 17) {
        std::fprintf(stderr, "First clock updated %u,%u,%u,%u,%u,%u,%u,%u\n",
                     static_cast<unsigned>(top.q0), static_cast<unsigned>(top.q1),
                     static_cast<unsigned>(top.q2), static_cast<unsigned>(top.q3),
                     static_cast<unsigned>(top.q5), static_cast<unsigned>(top.q6),
                     static_cast<unsigned>(top.q7), static_cast<unsigned>(top.q8));
        return 1;
    }

    top.d = 23;
    top.clk_b = 1;
    top.eval();
    if (top.q0 != 17 || top.q1 != 17 || top.q2 != 17 || top.q3 != 17 || top.q4 != 23
        || top.q5 != 17 || top.q6 != 17 || top.q7 != 17 || top.q8 != 17) {
        std::fprintf(stderr, "Second clock updated %u,%u,%u,%u,%u\n",
                     static_cast<unsigned>(top.q0), static_cast<unsigned>(top.q1),
                     static_cast<unsigned>(top.q2), static_cast<unsigned>(top.q3),
                     static_cast<unsigned>(top.q4));
        return 1;
    }

    top.final();
    return 0;
}
