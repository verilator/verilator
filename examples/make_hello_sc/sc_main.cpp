// -*- SystemC -*-
// DESCRIPTION: Verilator Example: Top level main for invoking SystemC model
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2017 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0
//======================================================================

// SystemC global header
#include <systemc.h>

// Include common routines
#include <verilated.h>

// Include model header, generated from Verilating "top.v"
#include "Vtop.h"

int sc_main(int argc, char* argv[]) {
    // See a similar example walkthrough in the verilator manpage.

    // This is intended to be a minimal example.  Before copying this to start a
    // real project, it is better to start with a more complete example,
    // e.g. examples/c_tracing.

    // Prevent unused variable warnings
    if (false && argc && argv) {}

    // Construct the Verilated model, from Vtop.h generated from Verilating "top.v"
    Vtop* top = new Vtop{"top"};

    // Initialize SC model
    sc_start(1, SC_NS);

    // Simulate until $finish
    while (!Verilated::gotFinish()) {
        // Simulate 1ns
        sc_start(1, SC_NS);
    }

    // Final model cleanup
    top->final();

    // Return good completion status
    return 0;
}
