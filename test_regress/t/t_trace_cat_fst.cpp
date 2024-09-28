// -*- mode: C++; c-file-style: "cc-mode" -*-
//
// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2008 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

#include <verilated.h>
#include <verilated_fst_c.h>

#include <memory>

#include VM_PREFIX_INCLUDE

unsigned long long main_time = 0;
double sc_time_stamp() { return (double)main_time; }

const char* trace_name() {
    static char name[1000];
    VL_SNPRINTF(name, 1000, VL_STRINGIFY(TEST_OBJ_DIR) "/simpart_%04d.fst", (int)main_time);
    return name;
}

int main(int argc, char** argv) {
    Verilated::debug(0);
    Verilated::traceEverOn(true);
    Verilated::commandArgs(argc, argv);

    {
        VM_PREFIX top{"top"};

        VerilatedFstC tf;
        top.trace(&tf, 99);

        tf.open(trace_name());

        top.clk = 0;

        while (main_time < 190) {  // Creates 2 files
            top.clk = !top.clk;
            top.eval();

            if ((main_time % 100) == 0) {
                tf.close();
                tf.open(trace_name());
            }
            tf.dump((unsigned int)(main_time));
            ++main_time;
        }
        tf.close();
        top.final();
    }

    printf("*-* All Finished *-*\n");
    return 0;
}
