// -*- mode: C++; c-file-style: "cc-mode" -*-
//
// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

#include <verilated.h>
#include <verilated_vcd_c.h>

#include VM_PREFIX_INCLUDE

int main() {
    const std::unique_ptr<VerilatedContext> contextAp{new VerilatedContext};
    const std::unique_ptr<VerilatedContext> contextBp{new VerilatedContext};
    contextAp->traceEverOn(true);
    contextBp->traceEverOn(true);
    const std::unique_ptr<VM_PREFIX> topAp{new VM_PREFIX{contextAp.get(), "a"}};
    const std::unique_ptr<VM_PREFIX> topBp{new VM_PREFIX{contextBp.get(), "b"}};

    // A trace file traces the models of a single context
    const std::unique_ptr<VerilatedVcdC> tfp{new VerilatedVcdC};
    topAp->trace(tfp.get(), 99);
    topBp->trace(tfp.get(), 99);  // Error!

    return 0;
}
