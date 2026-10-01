// -*- mode: C++; c-file-style: "cc-mode" -*-
//
// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2024 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

#include "verilated_cov.h"
#include <verilated.h>
#include VM_PREFIX_INCLUDE

// These require the above. Comment prevents clang-format moving them
#include "TestCheck.h"

unsigned int main_time = 0;

double sc_time_stamp() { return main_time; }
//======================================================================

int errors = 0;

void verilatedTest() {
    const std::unique_ptr<VerilatedContext> contextp{new VerilatedContext};
    // Assert enable/disable
    contextp->assertOn(true);
    TEST_CHECK_NZ(contextp->assertOn());
    contextp->assertOn(false);
    TEST_CHECK_Z(contextp->assertOn());
}

void verilatedLockedTest() {
    // With +verilator+assert+lock, every assertion-control update is a no-op
    const std::unique_ptr<VerilatedContext> contextp{new VerilatedContext};
    const char* argsp[] = {"+verilator+assert+lock"};
    contextp->commandArgsAdd(1, argsp);
    contextp->assertOn(false);
    TEST_CHECK_NZ(contextp->assertOn());
}

int main(int argc, char** argv) {
    verilatedTest();
    verilatedLockedTest();
    if (errors) return 10;

    const std::unique_ptr<VerilatedContext> contextp{new VerilatedContext};
    contextp->threads(1);
    contextp->commandArgs(argc, argv);
    contextp->debug(0);

    srand48(5);

    const std::unique_ptr<VM_PREFIX> topp{new VM_PREFIX{"top"}};
    constexpr uint64_t sim_time = 100;
    while ((contextp->time() < sim_time) && !contextp->gotFinish()) {
        topp->clk = !topp->clk;
        topp->eval();
        contextp->timeInc(1);
    }
    const std::string filename = std::string{VL_STRINGIFY(TEST_OBJ_DIR) "/coverage.dat"};
    contextp->coveragep()->write(filename);

    if (!contextp->gotFinish()) {
        vl_fatal(__FILE__, __LINE__, "main", "%Error: Timeout; never got a $finish");
    }
    topp->final();

    return 0;
}
