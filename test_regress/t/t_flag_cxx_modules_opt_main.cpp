// -*- mode: C++; c-file-style: "cc-mode" -*-
//
// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0
#include "verilated.h"

#include "Vt_flag_cxx_modules_opt.h"
import cxx_opt_mod;

int main(int argc, char** argv) {
    VerilatedContext context;
    context.commandArgs(argc, argv);
    Vt_flag_cxx_modules_opt top{&context};
    top.eval();
    return module_value() == 42 ? 0 : 1;
}
