// -*- mode: C++; c-file-style: "cc-mode" -*-
//
// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2010 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

#include <verilated.h>
#include VM_PREFIX_INCLUDE

//======================================================================

#include "Vt_dpi_export_context2_bad__Dpi.h"

//======================================================================

unsigned int main_time = 0;

double sc_time_stamp() { return main_time; }

VM_PREFIX* topp = nullptr;

int main(int argc, char* argv[]) {
    Verilated::debug(0);
    Verilated::commandArgs(argc, argv);

    topp = new VM_PREFIX;

    topp->eval();
    VL_DO_DANGLING(delete topp, topp);
    return 1;
}
int dpii_task() {

    // Check DPI warnings
    svScope scope = svGetScope();  // Will warn
    (void)scope;  // Unused
    const char* filenamep = "";
    int lineno = 0;
    svGetCallerInfo(&filenamep, &lineno);  // Will warn
    (void)filenamep;  // Unused
    (void)lineno;  // Unused

    dpix_task();
    return 0;
}
