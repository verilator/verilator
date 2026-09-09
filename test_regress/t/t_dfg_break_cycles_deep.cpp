//
// DESCRIPTION: Verilator: DFG break cycles deep test
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0
//

#include <verilated.h>

#include <Vopt.h>
#include <iostream>

int main(int, char**) {
    VerilatedContext ctx;
    Vopt opt{&ctx};

    while (!ctx.gotFinish()) {
        opt.eval();
        ctx.timeInc(1);
    }

    std::cout << "*-* All Finished *-*\n";
}
