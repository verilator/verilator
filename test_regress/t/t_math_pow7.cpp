// -*- mode: C++; c-file-style: "cc-mode" -*-
//
// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

#include VM_PREFIX_INCLUDE

#include "TestCheck.h"

int errors = 0;

int main(int argc, char** argv) {
    vluint64_t sim_time = 1100;
    {
        VerilatedContext context;
        context.commandArgs(argc, argv);
        VM_PREFIX top{"top"};

        top.eval();
        { context.timeInc(10); }

        int cyc = 0;

        while ((context.time() < sim_time) && !context.gotFinish()) {
            top.eval();
            context.timeInc(5);

            ++cyc;
            if (cyc > 10) break;
        }

        TEST_CHECK_EQ(top.out_data, 1);

        top.final();
    }

    printf("*-* All Finished *-*\n");
    return errors != 0;
}
