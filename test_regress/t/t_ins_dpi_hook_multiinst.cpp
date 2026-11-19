// -*- mode: C++; c-file-style: "cc-mode" -*-
//
// DESCRIPTION: Verilator: DPI-hook targets in instances of one module and of sibling modules
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2025 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

#include VM_PREFIX_INCLUDE
#include "verilated.h"

#include <string>
#include <vector>

int main(int argc, char** argv) {
    const std::unique_ptr<VerilatedContext> contextp{new VerilatedContext};
    contextp->debug(0);
    contextp->commandArgs(argc, argv);
    const std::unique_ptr<VM_PREFIX> topp{new VM_PREFIX{contextp.get(), "top_module"}};

    const std::vector<std::vector<std::string>> paths
        = {{"s0", "v"}, {"s1", "v"}, {"ia", "va"}, {"ib", "vb"}};
    for (size_t i = 0; i < paths.size(); ++i) {
        topp->__Vdpihook_id[i] = static_cast<int>(i % 2);
        for (size_t j = 0; j < paths[i].size(); ++j) topp->__Vdpihook_path[i][j] = paths[i][j];
    }

    while (!contextp->gotFinish()) {
        topp->__Vdpihook_trigger = !topp->__Vdpihook_trigger;
        topp->eval();
        if (!topp->eventsPending()) break;
        contextp->timeInc(1);
    }
    if (!contextp->gotFinish()) {
        vl_fatal(__FILE__, __LINE__, "main", "%Error: Timeout; never got a $finish");
    }
    topp->final();
    return 0;
}
