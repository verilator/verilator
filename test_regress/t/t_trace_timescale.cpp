// -*- mode: C++; c-file-style: "cc-mode" -*-
//
// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2008 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

#include <verilated.h>
#include <verilated_vcd_c.h>

#include VM_PREFIX_INCLUDE

unsigned long long main_time = 0;
double sc_time_stamp() { return ((double)main_time) / VL_TIME_MULTIPLIER; }

int main(int argc, char** argv, char** env) {
    VM_PREFIX* top = new VM_PREFIX("top");

    Verilated::debug(0);
    Verilated::traceEverOn(true);

    VerilatedVcdC* tfp = new VerilatedVcdC;
    tfp->set_time_resolution("1ps");
    tfp->set_time_unit("1ns");

    top->trace(tfp, 99);

    tfp->open(VL_STRINGIFY(TEST_OBJ_DIR) "/simx.vcd");

    top->clk = 0;

    while (main_time < 190 * VL_TIME_MULTIPLIER) {
        top->clk = !top->clk;
        top->eval();
        tfp->dump((unsigned int)(main_time));
        // Advance by 0.5 time units, to make sure our fractional
        // time is working correctly
        main_time += VL_TIME_MULTIPLIER / 2;
    }
    tfp->close();
    top->final();
    printf("*-* All Finished *-*\n");
    return 0;
}
