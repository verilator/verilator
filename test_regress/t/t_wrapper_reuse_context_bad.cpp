//
// DESCRIPTION: Verilator: Verilog Multiple Model Test Module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

#include <verilated.h>

#include VM_PREFIX_INCLUDE

int main(int argc, char** argv) {
    // Create contexts
    VerilatedContext* contextp{new VerilatedContext};

    for (int i = 0; i < 2; ++i) {
        std::unique_ptr<VM_PREFIX> topp{new VM_PREFIX{contextp, "TOP"}};
        topp->eval();
        contextp->timeInc(1);
        topp->eval();
    }

    return 0;
}
