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

void rngUpdate(uint64_t& x) {
    x ^= x << 13;
    x ^= x >> 7;
    x ^= x << 17;
}

int main(int, char**) {
    // Create contexts
    VerilatedContext ctx;

    // Create models
    Vref ref{&ctx};
    Vopt opt{&ctx};

    uint64_t rand_a = 0x5aef0c8dd70a4497;
    uint64_t rand_b = 0xf0c0a8dd75ae4497;
    uint64_t srand_a = 0x00fa8dcc7ae4957;

    for (size_t n = 0; n < 200000; ++n) {
        // Update rngs
        rngUpdate(rand_a);
        rngUpdate(rand_b);
        rngUpdate(srand_a);

        // Assign inputs
        ref.rand_a = opt.rand_a = rand_a;
        ref.rand_b = opt.rand_b = rand_b;
        ref.srand_a = opt.srand_a = srand_a;

        // Evaluate both models
        ref.eval();
        opt.eval();

        // Check equivalence
#include "checks.h"

        // increment time
        ctx.timeInc(1);
    }

    std::cout << "*-* All Finished *-*\n";
}
