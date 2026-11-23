// -*- mode: C++; c-file-style: "cc-mode" -*-
//
// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

#include <verilated.h>
#include <verilated_rtmd.h>

#include <cstdio>
#include <iostream>
#include <memory>
#include <string>

#include VM_PREFIX_INCLUDE

int main(int argc, char** argv) {
    const std::unique_ptr<VerilatedContext> contextp{new VerilatedContext};
    contextp->commandArgs(argc, argv);
    // The name of the model is given by +topname=<name>
    const std::string topnameArg = contextp->commandArgsPlusMatch("topname=");
    if (topnameArg.empty()) {
        std::printf("%%Error: +topname=<name> is required\n");
        return 1;
    }
    const std::string topname = topnameArg.substr(9);
    const std::unique_ptr<VM_PREFIX> topp{new VM_PREFIX{contextp.get(), topname.c_str()}};

    // With +split, the components of unpacked arrays and structs are walked too
    VlRtmd::hierDump(std::cout, *contextp, *contextp->commandArgsPlusMatch("split"));

    std::printf("*-* All Finished *-*\n");
    return 0;
}
