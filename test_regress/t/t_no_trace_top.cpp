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

int main(int argc, char** argv) {
    Verilated::debug(0);
    Verilated::traceEverOn(true);
    Verilated::commandArgs(argc, argv);
    {
        VM_PREFIX top{"top"};

        VerilatedVcdC tf;
        top.trace(&tf, 99);
        tf.open(VL_STRINGIFY(TEST_OBJ_DIR) "/simno_trace_top.vcd");

        top.clk = 0;

        while (main_time < 1900) {  // Creates 2 files
            top.clk = !top.clk;
            top.eval();
            tf.dump((unsigned int)(main_time));
            ++main_time;
        }
        tf.close();
        top.final();
    }

    printf("*-* All Finished *-*\n");
    return 0;
}
