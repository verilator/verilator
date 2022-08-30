// -*- mode: C++; c-file-style: "cc-mode" -*-
//
// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2008 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

#include <verilated.h>
#include <verilated_vcd_c.h>

#include <memory>

#include VM_PREFIX_INCLUDE

unsigned long long main_time = 0;
double sc_time_stamp() { return (double)main_time; }

int main(int argc, char** argv, char** env) {
    std::unique_ptr<VM_PREFIX> top{new VM_PREFIX("top")};

    Verilated::debug(0);
    Verilated::traceEverOn(true);

    std::unique_ptr<VerilatedVcdC> tfp{new VerilatedVcdC};
    top->trace(tfp.get(), 99);

    tfp->rolloverSize(1000);  // But will be increased to 8kb chunk size
    tfp->open(VL_STRINGIFY(TEST_OBJ_DIR) "/simrollover.vcd");

    top->clk = 0;

    while (main_time < 1900) {  // Creates 2 files
        top->clk = !top->clk;
        top->eval();
        tfp->dump((unsigned int)(main_time));
        ++main_time;
    }
    tfp->close();
    top->final();
    tfp.reset();
    top.reset();
    printf("*-* All Finished *-*\n");
    return 0;
}
