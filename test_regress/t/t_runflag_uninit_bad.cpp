// -*- mode: C++; c-file-style: "cc-mode" -*-
//
// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2010 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

#include <verilated.h>
#include <verilated_save.h>

#include <iostream>
#include VM_PREFIX_INCLUDE

//======================================================================

unsigned int main_time = 0;

double sc_time_stamp() { return main_time; }

int main(int argc, char* argv[]) {
    auto topp = new VM_PREFIX;

    // We aren't calling Verilated::commandArgs(argc, argv)
    topp->eval();

    return 0;
}
