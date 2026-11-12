// -*- mode: C++; c-file-style: "cc-mode" -*-
//
// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

#include "verilated.h"

#include VM_PREFIX_INCLUDE

#ifdef _MSC_VER
import t_flag_cxx_modules_msvc;
#else
import std;
#endif

int main(int argc, char** argv) {
    VerilatedContext context;
    context.commandArgs(argc, argv);
    VM_PREFIX top{&context};
    top.eval();
#ifdef _MSC_VER
    return module_value() == 42 ? 0 : 1;
#else
    std::cout << "C++23 std module OK" << std::endl;
    return 0;
#endif
}
