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

int main(int argc, char** argv) {
    VerilatedContext context;
    context.debug(0);
    context.commandArgs(argc, argv);
    srand48(5);

    VM_PREFIX top;
    top.inc = 1;
    top.clk = false;
    top.eval();

    while (!context.gotFinish() && context.time() < 100000) {
        context.timeInc(5);
        if (top.clk) top.inc += 1;
        top.clk = !top.clk;
        top.eval();
    }

    if (!context.gotFinish()) {
        vl_fatal(__FILE__, __LINE__, "main", "%Error: Timeout; never got a $finish");
    }
    return 0;
}
