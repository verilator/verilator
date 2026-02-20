// -*- mode: C++; c-file-style: "cc-mode" -*-
// Simple test harness for t_covergroup_empty - provides clock
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2026 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

#include "verilated.h"

#include "Vt_covergroup_empty.h"

int main(int argc, char** argv) {
    Verilated::commandArgs(argc, argv);
    Vt_covergroup_empty* top = new Vt_covergroup_empty;

    // Run for 20 cycles
    for (int i = 0; i < 20; i++) {
        top->clk = 0;
        top->eval();
        top->clk = 1;
        top->eval();

        if (Verilated::gotFinish()) break;
    }

    delete top;
    return 0;
}
