// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
//
// Copyright 2022 by Geza Lore. This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#include "verilated.h"

#include "Vt_comb_input_0.h"
#include "Vt_comb_input_0__Syms.h"

#include <memory>

int main(int argc, char** argv, char** env) {
    const std::unique_ptr<VerilatedContext> contextp{new VerilatedContext};
    contextp->commandArgs(argc, argv);
    contextp->debug(0);
    srand48(5);

    const std::unique_ptr<Vt_comb_input_0> topp{new Vt_comb_input_0};
    topp->inc = 1;
    topp->clk = false;
    topp->eval();

    while (!contextp->gotFinish() && contextp->time() < 100000) {
        contextp->timeInc(5);
        if (topp->clk) topp->inc += 1;
        topp->clk = !topp->clk;
        topp->eval();
    }

    if (!contextp->gotFinish()) {
        vl_fatal(__FILE__, __LINE__, "main", "%Error: Timeout; never got a $finish");
    }
    return 0;
}
