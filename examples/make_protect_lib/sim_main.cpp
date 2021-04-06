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
#include <verilated_vcd_c.h>
#endif

int main(int argc, char** argv, char** env) {
    if (false && argc && argv && env) {}

    // Construct context to hold simulation time, etc
    VerilatedContext* contextp = new VerilatedContext;
    contextp->debug(0);
    contextp->randReset(2);
    contextp->commandArgs(argc, argv);

    // Construct the Verilated model, including the secret module
    Vtop* top = new Vtop{contextp};

#if VM_TRACE
    // When tracing, the contents of the secret module will not be seen
    VerilatedVcdC* tfp = nullptr;
    const char* flag = contextp->commandArgsPlusMatch("trace");
    if (flag && 0 == strcmp(flag, "+trace")) {
        contextp->traceEverOn(true);
        VL_PRINTF("Enabling waves into logs/vlt_dump.vcd...\n");
        tfp = new VerilatedVcdC;
        top->trace(tfp, 99);
        Verilated::mkdir("logs");
        tfp->open("logs/vlt_dump.vcd");
    }
#endif

    top->clk = 0;

    // Simulate until $finish
    while (!contextp->gotFinish()) {
        contextp->timeInc(1);
        top->clk = ~top->clk & 0x1;
        top->eval();
#if VM_TRACE
        if (tfp) tfp->dump(contextp->time());
#endif
    }

    // Final model cleanup
    top->final();

    // Close trace if opened
#if VM_TRACE
    if (tfp) {
        tfp->close();
        tfp = nullptr;
    }
#endif

    // Destroy model
    delete top;
    top = nullptr;
    delete contextp;
    contextp = nullptr;

    // Return good completion status
    // Don't use exit() or destructor won't get called
    return 0;
}
