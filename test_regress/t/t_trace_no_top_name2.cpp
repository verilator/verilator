// -*- mode: C++; c-file-style: "cc-mode" -*-
//
// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2022 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

#include <verilated.h>
#if VM_TRACE_FST
#include <verilated_fst_c.h>
#define TRACE_FILE_NAME "simx.fst"
#define TRACE_CLASS VerilatedFstC
#elif VM_TRACE_VCD
#include <verilated_vcd_c.h>
#define TRACE_FILE_NAME "simx.vcd"
#define TRACE_CLASS VerilatedVcdC
#endif

#include <memory>

#include VM_PREFIX_INCLUDE

unsigned long long main_time = 0;
double sc_time_stamp() { return (double)main_time; }

int main(int argc, char** argv) {
    Verilated::debug(0);
    Verilated::traceEverOn(true);
    Verilated::commandArgs(argc, argv);

    // This test is to specifically check "" as the below upper model name
    std::unique_ptr<VM_PREFIX> top{new VM_PREFIX{""}};

    std::unique_ptr<TRACE_CLASS> tfp{new TRACE_CLASS};

    top->trace(tfp.get(), 99);
    tfp->open(VL_STRINGIFY(TEST_OBJ_DIR) "/" TRACE_FILE_NAME);
    top->clk = 0;

    while (main_time <= 20) {
        top->eval();
        tfp->dump((unsigned int)(main_time));
        ++main_time;
        top->clk = !top->clk;
    }
    tfp->close();
    top->final();
    tfp.reset();
    top.reset();
    printf("*-* All Finished *-*\n");
    return 0;
}
