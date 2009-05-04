// DESCRIPTION: Verilator Example: Top level main for invoking model
//
// Copyright 2003-2009 by Wilson Snyder. This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.

#include <verilated.h>		// Defines common routines
#include "Vtop.h"		// From Verilating "top.v"
#if VM_TRACE
# include <SpTraceVcdC.h>	// Trace file format header (from SystemPerl)
#endif

Vtop *top;			// Instantiation of module

unsigned int main_time = 0;	// Current simulation time

double sc_time_stamp () {	// Called by $time in Verilog
    return main_time;
}

int main(int argc, char **argv, char **env) {
    if (0 && argc && argv && env) {}	// Prevent unused variable warnings
    top = new Vtop;		// Create instance of module

    Verilated::debug(0);

#if VM_TRACE			// If verilator was invoked with --trace
    Verilated::traceEverOn(true);	// Verilator must compute traced signals
    cout << "Enabling waves...\n";
    SpTraceVcdCFile* tfp = new SpTraceVcdCFile;
    top->trace (tfp, 99);	// Trace 99 levels of hierarchy
    tfp->open ("vl_dump.vcd");	// Open the dump file
#endif

    top->reset_l = 1;		// Set some inputs
    top->fastclk = 0;
    top->clk = 0;
    top->passed = 0;

    while (main_time < 60 && !top->passed) {

	if ((main_time % 10) == 3) {	// Toggle clock
	    top->clk = 1;
	}
	if ((main_time % 10) == 8) {
	    top->clk = 0;
	}
	if (main_time > 10) {
	    top->reset_l = 1;	// Deassert reset
	} else if (main_time > 1) {
	    top->reset_l = 0;	// Assert reset
	}

	top->eval();		// Evaluate model
#if VM_TRACE
	tfp->dump (main_time);	// Create waveform trace for this timestamp
#endif

	// Read outputs
	VL_PRINTF ("[%d] %x %x %x %x %x_%08x_%08x\n",
		   main_time, top->clk, top->reset_l, top->passed,
		   top->out_small, top->out_wide[2], top->out_wide[1], top->out_wide[0]);

	top->fastclk = !top->fastclk;
	main_time++;		// Time passes...
    }

    top->final();

#if VM_TRACE
    tfp->close();
#endif

    if (!top->passed) {
	VL_PRINTF ("A Test failed\n");
	abort();
    } else {
	VL_PRINTF ("All Tests passed\n");
    }

    exit(0L);
}
