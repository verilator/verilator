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

#include <memory>
#include "Vt_hier_block.h"

int main(int argc, char *argv[]) {
    const std::unique_ptr<VerilatedContext> contextp{new VerilatedContext};
#if VL_THREADED
    contextp->threads(6);
#endif
    contextp->commandArgs(argc, argv);
    std::unique_ptr<Vt_hier_block> top{new Vt_hier_block{contextp.get(), "top"}};
    for (int i = 0; i < 100 && !contextp->gotFinish(); ++i) {
        top->eval();
        top->clk ^= 1;
    }
    if (!contextp->gotFinish()) {
        vl_fatal(__FILE__, __LINE__, "main", "%Error: Timeout; never got a $finish");
    }
    top->final();
    return 0;
}
