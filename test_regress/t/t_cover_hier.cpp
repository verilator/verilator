// DESCRIPTION: Verilator: C++ test driver
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

#include <verilated.h>
#include <verilated_cov.h>

#include <memory>

#include VM_PREFIX_INCLUDE

int main(int argc, char** argv) {
    VerilatedContext context;
    context.commandArgs(argc, argv);

    const std::unique_ptr<VM_PREFIX> topp{new VM_PREFIX{&context, "top"}};

    for (int cyc = 0; cyc < 9; ++cyc) {
        topp->clk = 0;
        topp->eval();
        context.timeInc(1);

        topp->clk = 1;
        topp->eval();
        context.timeInc(1);
    }

    // The paired inline/no-inline regressions check that duplicate hierarchy
    // instances keep real counters, so forcePerInstance can split the same
    // source coverage point by hierarchy at write time.
    context.coveragep()->forcePerInstance(true);
    context.coveragep()->write(VL_STRINGIFY(TEST_OBJ_DIR) "/coverage.dat");

    return 0;
}
