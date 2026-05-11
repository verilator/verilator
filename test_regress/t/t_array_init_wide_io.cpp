// -*- mode: C++; c-file-style: "cc-mode" -*-
// DESCRIPTION: Verilator: Verilog Test driver
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

#include "verilated.h"
#include "Vt_array_init_wide_io.h"

int main(int argc, char** argv) {
    Verilated::debug(0);
    Verilated::commandArgs(argc, argv);

    std::unique_ptr<Vt_array_init_wide_io> top{new Vt_array_init_wide_io{"top"}};

    top->clk = 0;
    while (!Verilated::gotFinish()) {
        top->clk = !top->clk;
        top->eval();
    }

    top->final();
    return 0;
}
