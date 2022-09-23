//
// DESCRIPTION: Verilator: DFG optimzier equivalence testing
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2022 by Geza Lore.
// SPDX-License-Identifier: CC0-1.0
//

#include <verilated.h>
#include <verilated_cov.h>

#include <Vopt.h>
#include <Vref.h>
#include <iostream>

int main(int, char**) {
    // Create contexts
    VerilatedContext ctx;

    // Create models
    Vref ref{&ctx};
    Vopt opt{&ctx};

    ref.clk = 0;
    opt.clk = 0;

    while (!ctx.gotFinish()) {
        ref.eval();
        opt.eval();
#include "checks.h"
        // increment time
        ctx.timeInc(1);

        ref.clk = !ref.clk;
        opt.clk = !opt.clk;
    }
}
