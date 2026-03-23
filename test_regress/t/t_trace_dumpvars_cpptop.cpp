// -*- mode: C++; c-file-style: "cc-mode" -*-
//
// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 by Marco Bartoli.
// SPDX-License-Identifier: CC0-1.0

#include <verilated.h>

#include <memory>

#include VM_PREFIX_INCLUDE

unsigned long long main_time = 0;
double sc_time_stamp() { return (double)main_time; }

int main(int argc, char** argv) {
    Verilated::debug(0);
    Verilated::traceEverOn(true);
    Verilated::commandArgs(argc, argv);

    // Name the top module "cpptop" instead of default "TOP"
    std::unique_ptr<VM_PREFIX> top{new VM_PREFIX{"cpptop"}};
    top->clk = 0;

    while (!Verilated::gotFinish()) {
        top->eval();
        ++main_time;
        top->clk = !top->clk;
    }
    top->final();
    top.reset();
    printf("*-* All Finished *-*\n");
    return 0;
}
