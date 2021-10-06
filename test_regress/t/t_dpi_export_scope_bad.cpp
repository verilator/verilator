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

#include "Vt_dpi_export_scope_bad__Dpi.h"

#ifdef NEED_EXTERNS
extern "C" {
extern void dpix_task();
}
#endif

//======================================================================

unsigned int main_time = 0;

double sc_time_stamp() { return main_time; }

VM_PREFIX* topp = nullptr;

int main(int argc, char* argv[]) {
    topp = new VM_PREFIX;

    Verilated::debug(0);

    topp->eval();

    topp->final();
    VL_DO_DANGLING(delete topp, topp);
    return 1;
}

void dpix_run_tests() {
    dpix_task();  // Wrong scope
}
