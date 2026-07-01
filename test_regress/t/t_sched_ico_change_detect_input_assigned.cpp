// -*- mode: C++; c-file-style: "cc-mode" -*-
//
// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

#include <verilated.h>

#include <memory>
#include <string>

#include VM_PREFIX_INCLUDE

int main(int argc, char** argv) {
    const std::unique_ptr<VerilatedContext> contextp{new VerilatedContext};
    contextp->threads(1);
    contextp->commandArgs(argc, argv);

    const std::unique_ptr<VM_PREFIX> topp{new VM_PREFIX{contextp.get(), "top"}};
    topp->clk = 0;
    topp->i = 0;
    topp->eval();

    while ((contextp->time() < 10000) && !contextp->gotFinish()) {
        contextp->timeInc(1);
        topp->clk = !topp->clk;
        // Always set to the same constant value, so change detection will think it's not changing
        topp->i = 500000;
        topp->eval();
        if (topp->o != topp->i + 10) {
            const std::string msg = "%Error: incorrect output, got: " + std::to_string(topp->o)
                                    + " expected: " + std::to_string(topp->i + 10);
            vl_fatal(__FILE__, __LINE__, "main", msg.c_str());
            break;
        }
    }

    if (!contextp->gotFinish()) {
        vl_fatal(__FILE__, __LINE__, "main", "%Error: Timeout; never got a $finish");
    }
    topp->final();
    return 0;
}
