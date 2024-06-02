// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
//
// Copyright 2023 by Geza Lore. This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#include "verilated.h"

#include "Vt_interface_virtual_sched_ico.h"
#include "Vt_interface_virtual_sched_ico__Syms.h"

#include <memory>

int main(int argc, char** argv) {
    const std::unique_ptr<VerilatedContext> contextp{new VerilatedContext};
    contextp->debug(0);
    contextp->commandArgs(argc, argv);
    srand48(5);

    const std::unique_ptr<VM_PREFIX> topp{new VM_PREFIX};
    topp->clk = false;
    topp->inc1 = 1;
    topp->eval();
    topp->inc2 = 1;
    topp->eval();

    bool flop = true;
    while (!contextp->gotFinish() && contextp->time() < 100000) {
        contextp->timeInc(5);
        if (topp->clk) {
            if (flop) {
                topp->inc1 += 1;
            } else {
                topp->inc2 += 1;
            }
            flop = !flop;
        }
        topp->clk = !topp->clk;
        topp->eval();
    }

    if (!contextp->gotFinish()) {
        vl_fatal(__FILE__, __LINE__, "main", "%Error: Timeout; never got a $finish");
    }
    return 0;
}
