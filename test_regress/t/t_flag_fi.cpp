// -*- mode: C++; c-file-style: "cc-mode" -*-
//
// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2017 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

#include <verilated.h>
#include "Vt_flag_fi.h"

//======================================================================

unsigned int main_time = 0;

double sc_time_stamp() { return main_time; }

VM_PREFIX* topp = NULL;
bool gotit = false;

void myfunction() { gotit = true; }

int main(int argc, char* argv[]) {
    topp = new VM_PREFIX;

    Verilated::debug(0);

    topp->eval();
    if (!gotit) { vl_fatal(__FILE__, __LINE__, "dut", "Never got call to myfunction"); }

    topp->final();

    return 0;
}
