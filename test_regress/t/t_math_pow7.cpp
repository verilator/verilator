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

std::unique_ptr<VM_PREFIX> topp;
int main(int argc, char** argv) {
    vluint64_t sim_time = 1100;
    const std::unique_ptr<VerilatedContext> contextp{new VerilatedContext};
    contextp->commandArgs(argc, argv);
    topp.reset(new VM_PREFIX{"top"});

    topp->eval();
    { contextp->timeInc(10); }

    int cyc = 0;

    while ((contextp->time() < sim_time) && !contextp->gotFinish()) {
        topp->eval();
        contextp->timeInc(5);

        ++cyc;
        if (cyc > 10) break;
    }

    TEST_CHECK_EQ(topp->out_data, 1);

    topp->final();
    topp.reset();

    printf("*-* All Finished *-*\n");
    return errors != 0;
}
