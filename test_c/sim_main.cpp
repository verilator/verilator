// DESCRIPTION: Verilator Example: Top level main for invoking model
//
// Copyright 2003-2015 by Wilson Snyder. This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.

#include <verilated.h>		// Defines common routines
#include "Vtop.h"		// From Verilating "top.v"
#if VM_TRACE
# include <verilated_vcd_c.h>	// Trace file format header
#endif

Vtop *top;			// Instantiation of module

vluint64_t main_time = 0;	// Current simulation time (64-bit unsigned)

double sc_time_stamp () {	// Called by $time in Verilog
    return main_time;		// Note does conversion to real, to match SystemC
}

int main(int argc, char **argv, char **env) {
    if (0 && argc && argv && env) {}	// Prevent unused variable warnings
    top = new Vtop;		// Create instance of module

    Verilated::commandArgs(argc, argv);
    Verilated::debug(0);

#if VM_TRACE			// If verilator was invoked with --trace
    Verilated::traceEverOn(true);	// Verilator must compute traced signals
    VL_PRINTF("Enabling waves...\n");
    VerilatedVcdC* tfp = new VerilatedVcdC;
    top->trace (tfp, 99);	// Trace 99 levels of hierarchy
    tfp->open ("vlt_dump.vcd");	// Open the dump file
#endif

    top->reset_l = 1;		// Set some inputs
    top->fastclk = 0;
    top->clk = 0;
    top->passed = 0;

    while (main_time < 60 && !top->passed && !Verilated::gotFinish()) {

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
	if (tfp) tfp->dump (main_time);	// Create waveform trace for this timestamp
#endif

	// Read outputs
	VL_PRINTF ("[%" VL_PRI64 "d] %x %x %x %x %x_%08x_%08x\n",
		   main_time, top->clk, top->reset_l, top->passed,
		   top->out_small, top->out_wide[2], top->out_wide[1], top->out_wide[0]);

	top->fastclk = !top->fastclk;
	main_time++;		// Time passes...
    }

    top->final();

#if VM_TRACE
    if (tfp) tfp->close();
#endif

    if (!top->passed) {
	VL_PRINTF ("A Test failed\n");
	abort();
    } else {
	VL_PRINTF ("All Tests passed\n");
    }

    exit(0L);
}
