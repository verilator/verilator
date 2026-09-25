// -*- mode: C++; c-file-style: "cc-mode" -*-
//*************************************************************************
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
//
//*************************************************************************

// Generated header
#include "Vt_threads_context_default.h"
// General headers
#include "verilated.h"

#include <memory>

int main(int argc, char** argv) {
    // Deliberately no contextp->threads() call, so the context thread count is the default
    const std::unique_ptr<VerilatedContext> contextp{new VerilatedContext};
    contextp->commandArgs(argc, argv);
    const std::unique_ptr<Vt_threads_context_default> topp{
        new Vt_threads_context_default{contextp.get(), "top"}};

    topp->clk = 0;
    while (contextp->time() < 1100 && !contextp->gotFinish()) {
        topp->eval();
        topp->clk = !topp->clk;
        contextp->timeInc(5);
    }
    if (!contextp->gotFinish()) {
        vl_fatal(__FILE__, __LINE__, "main", "%Error: Timeout; never got a $finish");
    }
    topp->final();
    return 0;
}
