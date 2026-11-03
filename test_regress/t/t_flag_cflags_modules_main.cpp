// -*- mode: C++; c-file-style: "cc-mode" -*-
//
// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0
#include "verilated.h"

#include "Vt_flag_cflags_modules.h"
import std; //this is a C++23 std module, if GNU or LLVM maybe need give compilation product, ok, perfect
int main(int argc, char** argv) {
    VerilatedContext context;
    context.commandArgs(argc, argv);
    Vt_flag_cflags_modules top{&context};
    top.eval();
    std::cout << "C++23 std module OK" << std::endl;
    return 0;
}
