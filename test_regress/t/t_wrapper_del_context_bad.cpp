//
// DESCRIPTION: Verilator: Verilog Multiple Model Test Module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2022 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

#include <verilated.h>

#include VM_PREFIX_INCLUDE

int main(int argc, char** argv) {
    // Create contexts
    VerilatedContext context;

    // Ideally we'd do this, but then address sanitizer blows up
    // delete contextp;  // Test mistake - deleting contextp
    context.selfTestClearMagic();

    // instantiate verilated design
    VM_PREFIX top{&context, "TOP"};

    return 0;
}
