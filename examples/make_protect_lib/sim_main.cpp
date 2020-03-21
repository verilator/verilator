// DESCRIPTION: Verilator: --protect-lib example module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2019 by Todd Strader.
// SPDX-License-Identifier: CC0-1.0
//======================================================================

// See examples/tracing_c for notes on tracing

// Include common routines
#include <verilated.h>

#include "Vtop.h"

#if VM_TRACE
# include <verilated_vcd_c.h>
#endif

vluint64_t main_time = 0;
double sc_time_stamp() {
    return main_time;
}

int main(int argc, char** argv, char** env) {
    if (0 && argc && argv && env) {}

    Verilated::debug(0);
    Verilated::randReset(2);
    Verilated::commandArgs(argc, argv);

    // Construct the Verilated model, including the secret module
    Vtop* top = new Vtop;

#if VM_TRACE
    // When tracing, the contents of the secret module will not be seen
    VerilatedVcdC* tfp = NULL;
    const char* flag = Verilated::commandArgsPlusMatch("trace");
    if (flag && 0==strcmp(flag, "+trace")) {
        Verilated::traceEverOn(true);
        VL_PRINTF("Enabling waves into logs/vlt_dump.vcd...\n");
        tfp = new VerilatedVcdC;
        top->trace(tfp, 99);
        Verilated::mkdir("logs");
        tfp->open("logs/vlt_dump.vcd");
    }
#endif

    top->clk = 0;

    // Simulate until $finish
    while (!Verilated::gotFinish()) {
        main_time++;
        top->clk = ~top->clk & 0x1;
        top->eval();
#if VM_TRACE
        if (tfp) tfp->dump(main_time);
#endif
    }

    // Final model cleanup
    top->final();

    // Close trace if opened
#if VM_TRACE
    if (tfp) { tfp->close(); tfp = NULL; }
#endif

    // Destroy model
    delete top; top = NULL;

    // Fin
    exit(0);
}
