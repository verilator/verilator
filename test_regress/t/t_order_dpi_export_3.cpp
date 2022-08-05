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

#include <Vt_order_dpi_export_3.h>
#include <Vt_order_dpi_export_3__Dpi.h>
#include <svdpi.h>

void toggle_other_clk(svBit val) { set_other_clk(val); }

void toggle_third_clk(svBit val) { set_third_clk(val); }

int main(int argc, char* argv[]) {
    Vt_order_dpi_export_3* const tb = new Vt_order_dpi_export_3;
    tb->contextp()->commandArgs(argc, argv);
    bool clk = true;

    while (!tb->contextp()->gotFinish()) {
        // Timeout
        if (tb->contextp()->time() > 100000) break;
        // Toggle and set main clock
        clk = !clk;
        tb->clk = clk;
        // Eval
        tb->eval();
        // Advance time
        tb->contextp()->timeInc(500);
    }

    delete tb;
    return 0;
}
