// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
//
// Copyright 2021 by Geza Lore. This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#include <svdpi.h>

#include <Vt_dpi_clock_gen.h>
#include <Vt_dpi_clock_gen__Dpi.h>

static int current_time = 0;

static Vt_dpi_clock_gen* tb;

static void tick() {
    // Toggle and set clock
    svSetScope(svGetScopeFromName("TOP.testbench"));
    static bool clk = true;
    clk = !clk;
    set_clk(clk);

    // Eval
    tb->eval();

    // Advance time
    current_time += 500;
}

int main(int argc, char* argv[]) {
    tb = new Vt_dpi_clock_gen();

    while (!Verilated::gotFinish()) {
        if (current_time > 100000) break;
        tick();
    }

    delete tb;

    return 0;
}
