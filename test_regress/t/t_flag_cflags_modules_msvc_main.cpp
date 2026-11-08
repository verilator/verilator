// -*- mode: C++; c-file-style: "cc-mode" -*-
//
// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0
#include "verilated.h"

#include "Vt_flag_cflags_modules_msvc.h"
import t_flag_cflags_modules_msvc;

int main(int argc, char** argv) {
    VerilatedContext context;
    context.commandArgs(argc, argv);
    Vt_flag_cflags_modules_msvc top{&context};
    top.eval();
    return module_value() == 42 ? 0 : 1;
}
