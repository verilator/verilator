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
    VerilatedContext context;
    context.debug(0);
    context.commandArgs(argc, argv);
    srand48(5);

    VM_PREFIX top;
    top.clk = false;
    top.inc1 = 1;
    top.eval();
    top.inc2 = 1;
    top.eval();

    bool flop = true;
    while (!context.gotFinish() && context.time() < 100000) {
        context.timeInc(5);
        if (top.clk) {
            if (flop) {
                top.inc1 += 1;
            } else {
                top.inc2 += 1;
            }
            flop = !flop;
        }
        top.clk = !top.clk;
        top.eval();
    }

    if (!context.gotFinish()) {
        vl_fatal(__FILE__, __LINE__, "main", "%Error: Timeout; never got a $finish");
    }
    return 0;
}
