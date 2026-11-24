// -*- mode: C++; c-file-style: "cc-mode" -*-
//
// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

#include "verilated.h"

#include VM_PREFIX_INCLUDE

#if 0
import "t_flag_cxx_modules_missing.h";
#endif
import "t_flag_cxx_modules_header.h";
import "t_flag_cxx_modules_isystem.h";

int main(int argc, char** argv) {
    VerilatedContext context;
    context.commandArgs(argc, argv);
    VM_PREFIX top{&context};
    top.eval();
    return header_unit_value() + isystem_header_unit_value() == 85 ? 0 : 1;
}
