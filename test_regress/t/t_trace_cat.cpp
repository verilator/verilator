// -*- mode: C++; c-file-style: "cc-mode" -*-
//
// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2008 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

#include <verilated.h>
#include VL_STRINGIFY(TRACE_HEADER_C)

#include <memory>

#include VM_PREFIX_INCLUDE

#include "TestCheck.h"

int errors = 0;

unsigned long long main_time = 0;
double sc_time_stamp() { return (double)main_time; }

const char* trace_name() {
    static char name[1000];
    VL_SNPRINTF(name, 1000, VL_STRINGIFY(TEST_OBJ_DIR) "/simx_part_%04d." VL_STRINGIFY(TRACE_FMT),
                (int)main_time);
    return name;
}

int main(int argc, char** argv) {
    Verilated::debug(0);
    Verilated::traceEverOn(true);
    Verilated::commandArgs(argc, argv);

    std::unique_ptr<VM_PREFIX> top{new VM_PREFIX{"top"}};

    std::unique_ptr<VERILATED_TRACE_C> tfp{new VERILATED_TRACE_C};
    top->trace(tfp.get(), 99);

    // Test for traceCapable - randomly-ish selected this test
    TEST_CHECK_EQ(top->traceCapable, true);

    tfp->open(trace_name());

    top->clk = 0;

    while (main_time < 190) {  // Creates 2 files
        top->clk = !top->clk;
        top->eval();

        if ((main_time % 100) == 0) {
#if defined(TRACE_OPENNEXT)
            tfp->openNext(true);
#elif defined(TRACE_REOPEN)
            tfp->close();
            tfp->open(trace_name());
#elif defined(TRACE_RENEW)
            tfp->close();
            tfp.reset(new VERILATED_TRACE_C);
            top->trace(tfp.get(), 99);
            tfp->open(trace_name());
#else
#error "Unknown test"
#endif
        }
        tfp->dump((unsigned int)(main_time));
        ++main_time;
    }
    tfp->close();
    top->final();
    tfp.reset();
    top.reset();
    printf("*-* All Finished *-*\n");
    return errors;
}
