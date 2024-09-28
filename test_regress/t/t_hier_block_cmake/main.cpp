// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
//
// Copyright 2020 by Yutetsu TAKATSUKASA. This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

#include "Vt_hier_block.h"

#include <memory>

int main(int argc, char* argv[]) {
    VerilatedContext context;
    // TEST_THREADS is set in t_hier_block_cmake.py
    context.threads(TEST_THREADS);
    context.commandArgs(argc, argv);
    Vt_hier_block top{&context, "top"};
    for (int i = 0; i < 100 && !context.gotFinish(); ++i) {
        top.eval();
        top.clk ^= 1;
    }
    if (!context.gotFinish()) {
        vl_fatal(__FILE__, __LINE__, "main", "%Error: Timeout; never got a $finish");
    }
    top.final();
    return 0;
}
