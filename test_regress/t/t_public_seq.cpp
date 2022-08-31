// -*- mode: C++; c-file-style: "cc-mode" -*-
//
// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2022 by Todd Strader.
// SPDX-License-Identifier: CC0-1.0

// Generated header
#include "Vt_public_seq.h"
#include "Vt_public_seq___024root.h"
// General headers
#include "verilated.h"

std::unique_ptr<Vt_public_seq> topp;
int main(int argc, char** argv, char** env) {
    vluint64_t sim_time = 1100;
    const std::unique_ptr<VerilatedContext> contextp{new VerilatedContext};
    contextp->commandArgs(argc, argv);
    contextp->debug(0);
    srand48(5);
    topp.reset(new Vt_public_seq("top"));

    topp->clk = 0;
    topp->eval();
    { contextp->timeInc(10); }

    int cyc = 0;

    while ((contextp->time() < sim_time) && !contextp->gotFinish()) {
        if (cyc >= 5) ++topp->rootp->t__DOT__pub_byte;
        topp->eval();
        topp->clk = !topp->clk;
        topp->eval();
        contextp->timeInc(5);
        if (topp->clk) cyc++;
    }
    if (!contextp->gotFinish()) {
        vl_fatal(__FILE__, __LINE__, "main", "%Error: Timeout; never got a $finish");
    }
    topp->final();

    topp.reset();
    return 0;
}
