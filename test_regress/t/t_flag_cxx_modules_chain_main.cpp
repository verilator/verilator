// -*- mode: C++; c-file-style: "cc-mode" -*-
//
// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

#include "verilated.h"

#include VM_PREFIX_INCLUDE

import buildmod;
import m2;

int main(int argc, char** argv) {
    VerilatedContext context;
    context.commandArgs(argc, argv);
    VM_PREFIX top{&context};
    top.eval();
    return g() == 2 && module_value() == 42 ? 0 : 1;
}
