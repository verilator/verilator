// $Id$ -*- SystemC -*-
// DESCRIPTION: Verilator Example: Top level main for invoking SystemC model
//
// Copyright 2003-2006 by Wilson Snyder. This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// General Public License or the Perl Artistic License.
//====================================================================

#include <stdio.h>
#include <iostream>
#include <sys/times.h>
#include <sys/stat.h>

#ifdef SYSTEMPERL
# include "systemperl.h"	// SystemC + SystemPerl global header
# include "sp_log.h"		// Logging cout to files
# include "SpTraceVcd.h"
# include "SpCoverage.h"
#else
# include "systemc.h"		// SystemC global header
#endif

#include "Vtop.h"		// Top level header, generated from verilog

Vtop *top;

int sc_main(int argc, char* argv[]) {
    Verilated::randReset(2);
    Verilated::debug(0);	// We compiled with it on for testing, turn it back off

    // General logfile
    ios::sync_with_stdio();
#ifdef SYSTEMPERL
    sp_log_file simlog ("sim.log");
    simlog.redirect_cout();
#endif

    // Defaults
#if (SYSTEMC_VERSION>20011000)
#else
    sc_time dut(1.0, sc_ns);
    sc_set_default_time_unit(dut);
#endif

    //==========
    // Define the Clocks

    cout << ("Defining Clocks\n");
    sc_clock clk     ("clk",10, 0.5, 3, true);
    sc_clock fastclk ("fastclk",2, 0.5, 2, true);
    sc_signal<bool> reset_l;
    sc_signal<bool> passed;
    sc_signal<uint32_t> in_small;
    sc_signal<sc_bv<40> > in_quad;
    sc_signal<sc_bv<70> > in_wide;
    sc_signal<uint32_t> out_small;
    sc_signal<sc_bv<40> > out_quad;
    sc_signal<sc_bv<70> > out_wide;

    //==========
    // Part under test

#ifdef SYSTEMPERL
    SP_CELL (top, Vtop);
    SP_PIN (top, clk,		clk);
    SP_PIN (top, fastclk,	fastclk);
    SP_PIN (top, reset_l,	reset_l);
    SP_PIN (top, passed,	passed);
    SP_PIN (top, in_small,	in_small);
    SP_PIN (top, in_quad,	in_quad);
    SP_PIN (top, in_wide,	in_wide);
    SP_PIN (top, out_small,	out_small);
    SP_PIN (top, out_quad,	out_quad);
    SP_PIN (top, out_wide,	out_wide);
#else
    Vtop* top = new Vtop("top");
    top->clk		(clk);
    top->fastclk	(fastclk);
    top->reset_l	(reset_l);
    top->passed		(passed);
    top->in_small	(in_small);
    top->in_quad	(in_quad);
    top->in_wide	(in_wide);
    top->out_small	(out_small);
    top->out_quad	(out_quad);
    top->out_wide	(out_wide);
#endif

    //==========
    //  Waves

#if WAVES
    // Before any evaluation, need to know to calculate those signals only used for tracing
    Verilated::traceEverOn(true);
#endif

    // You must do one evaluation before enabling waves, in order to allow
    // SystemC to interconnect everything for testing.
    cout <<("Test initialization...\n");
    reset_l = 1;
    sc_start(1);

    //==========
    //  Waves

#if WAVES
    cout << "Enabling waves...\n";
    SpTraceFile* tfp = new SpTraceFile;
    top->trace (tfp, 99);
    tfp->open ("vl_dump.vcd");
#endif

    //==========
    // Start of Test

    cout <<("Test beginning...\n");
	
    reset_l = 1;
    while (VL_TIME_Q() < 60 && !passed) {
#if WAVES
	// Flush the wave files each cycle so we can immediately see the output
	// Don't do this in "real" programs, do it in a abort() handler instead
	tfp->flush();
#endif
	if (VL_TIME_Q() > 10) {
	    reset_l = 1;	// Deassert reset
	} else if (VL_TIME_Q() > 1) {
	    reset_l = 0;	// Assert reset
	}
	sc_start(1);
    }

    top->final();

    //==========
    //  Close Waves
#if WAVES
    tfp->close();
#endif

    if (!passed) {
	UTIL_PRINTF ("A Test failed!!\n");
	abort();
    }

    //==========
    //  Coverage analysis (since test passed)
    mkdir("logs", 0777);
#ifdef SYSTEMPERL
    SpCoverage::write();  // Writes logs/coverage.pl
#endif

    //==========
    //  Close LogFiles

    cout << "*-* All Finished *-*\n";  // Magic if using perl's Log::Detect

    return(0);
}
