// -*- mode: C++; c-file-style: "cc-mode" -*-
//
// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2008 by Wilson Snyder.

#include <verilated.h>
#include <verilated_vcd_c.h>

#if defined(T_TRACE_CAT)
# include "Vt_trace_cat.h"
#elif defined(T_TRACE_CAT_REOPEN)
# include "Vt_trace_cat_reopen.h"
#elif defined(T_TRACE_CAT_RENEW)
# include "Vt_trace_cat_renew.h"
#else
# error "Unknown test"
#endif

unsigned long long main_time = 0;
double sc_time_stamp() {
    return (double)main_time;
}

const char* trace_name() {
    static char name[1000];
#if defined(T_TRACE_CAT)
    VL_SNPRINTF(name,1000,"obj_dir/t_trace_cat/simpart_%04d.vcd", (int)main_time);
#elif defined(T_TRACE_CAT_REOPEN)
    VL_SNPRINTF(name,1000,"obj_dir/t_trace_cat_reopen/simpart_%04d.vcd", (int)main_time);
#elif defined(T_TRACE_CAT_RENEW)
    VL_SNPRINTF(name,1000,"obj_dir/t_trace_cat_renew/simpart_%04d.vcd", (int)main_time);
#else
# error "Unknown test"
#endif
    return name;
}

int main(int argc, char **argv, char **env) {
    VM_PREFIX* top = new VM_PREFIX("top");

    Verilated::debug(0);
    Verilated::traceEverOn(true);

    VerilatedVcdC* tfp = new VerilatedVcdC;
    top->trace(tfp,99);

    tfp->open(trace_name());

    top->clk = 0;

    while (main_time < 190) {  // Creates 2 files
	top->clk   = ~top->clk;
	top->eval();

	if ((main_time % 100) == 0) {
#if defined(T_TRACE_CAT)
	    tfp->openNext(true);
#elif defined(T_TRACE_CAT_REOPEN)
	    tfp->close();
	    tfp->open(trace_name());
#elif defined(T_TRACE_CAT_RENEW)
	    tfp->close();
	    delete tfp;
	    tfp = new VerilatedVcdC;
	    top->trace(tfp,99);
	    tfp->open(trace_name());
#else
# error "Unknown test"
#endif
	}
	tfp->dump((unsigned int)(main_time));
	++main_time;
    }
    tfp->close();
    top->final();
    printf ("*-* All Finished *-*\n");
    return 0;
}
