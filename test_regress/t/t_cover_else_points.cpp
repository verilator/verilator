/*--------------------------------------------------------------------
File Name :
Purpose :
Creation Date :
Last Modified : Fri 19 Jan 2024 09:41:39 PM EST
Created By :
History :
Copyright (c) ChipIC
--------------------------------------------------------------------*/
#include "verilated.h"
#include "Vt_cover_else_points.h"

//======================

int main(int argc, char** argv, char**) {
    // Setup context, defaults, and parse command line
    Verilated::debug(0);
    const std::unique_ptr<VerilatedContext> contextp{new VerilatedContext};
    contextp->traceEverOn(true);
    contextp->commandArgs(argc, argv);

    // Construct the Verilated model, from Vtop.h generated from Verilating
    const std::unique_ptr<Vt_cover_else_points> topp{new Vt_cover_else_points{contextp.get()}};

    // Simulate until $finish
    while (!contextp->gotFinish()) {
        // Evaluate model
        topp->eval();
        // Advance time
        if (!topp->eventsPending()) break;
        contextp->time(topp->nextTimeSlot());
    }

    if (!contextp->gotFinish()) {
        VL_DEBUG_IF(VL_PRINTF("+ Exiting without $finish; no events left\n"););
    }

    // Final model cleanup
    topp->final();

#if VM_COVERAGE
    contextp->coveragep()->write("obj_vlt/t_cover_else_points/coverage.dat");
#endif

    return 0;
}

