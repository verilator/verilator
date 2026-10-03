// DESCRIPTION: Verilator: Distinct receiver state in shared subgraph evaluation
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

#include "verilated.h"

#include <cstdio>

#include VM_PREFIX_INCLUDE
#include "Vt_subgraph_shared_initial_sg_shared_initial.h"

int main(int argc, char** argv) {
    VerilatedContext context;
    context.commandArgs(argc, argv);
    Vt_subgraph_shared_initial top{&context};
    top.clk = 0;
    top.eval();

    top.__PVT__t__DOT__i_a->q = 7;
    top.__PVT__t__DOT__i_b->q = 9;
    top.eval();
    if (top.__PVT__t__DOT__i_a->q != 7 || top.__PVT__t__DOT__i_b->q != 9) {
        std::fprintf(stderr, "Initial receivers: q=%u,%u\n",
                     static_cast<unsigned>(top.__PVT__t__DOT__i_a->q),
                     static_cast<unsigned>(top.__PVT__t__DOT__i_b->q));
        return 1;
    }

    top.clk = 1;
    top.eval();
    if (top.__PVT__t__DOT__i_a->q != 3 || top.__PVT__t__DOT__i_b->q != 5 || top.b != 5) {
        std::fprintf(stderr, "Clocked receivers: q=%u,%u output=%u\n",
                     static_cast<unsigned>(top.__PVT__t__DOT__i_a->q),
                     static_cast<unsigned>(top.__PVT__t__DOT__i_b->q),
                     static_cast<unsigned>(top.b));
        return 1;
    }

    top.final();
    return 0;
}
