//
// DESCRIPTION: Verilator: Verilog Multiple Model Test Module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

#include <verilated.h>

#include VM_PREFIX_INCLUDE

int main() {
    const std::unique_ptr<VerilatedContext> contextp{new VerilatedContext};

    // Two models under the same hierarchical path in one context
    const std::unique_ptr<VM_PREFIX> firstp{new VM_PREFIX{contextp.get(), "TOP"}};
    const std::unique_ptr<VM_PREFIX> secondp{new VM_PREFIX{contextp.get(), "TOP"}};

    return 0;
}
