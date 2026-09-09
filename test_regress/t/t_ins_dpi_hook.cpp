// -*- mode: C++; c-file-style: "cc-mode" -*-
//
// DESCRIPTION: Verilator: DPI-hook insertion test main
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2025 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

#include VM_PREFIX_INCLUDE
#include "verilated.h"

#include <map>
#include <string>
#include <vector>

int main(int argc, char** argv) {
    const std::unique_ptr<VerilatedContext> contextp{new VerilatedContext};
    contextp->debug(0);
    contextp->commandArgs(argc, argv);

    const std::unique_ptr<VM_PREFIX> topp{new VM_PREFIX{contextp.get(), "top_module"}};

    // Pair each hook path with the id the callback should receive for it.
    const std::multimap<int, std::vector<std::string>> hook_paths = {
        {0, {"a1", "b1", "out"}},
        {1, {"a2", "out"}},
    };
    size_t slot = 0;
    for (const auto& [id, path] : hook_paths) {
        topp->DPIHOOK_CASE_ID[slot] = id;
        for (size_t j = 0; j < path.size(); ++j) topp->DPIHOOK_PATH[slot][j] = path[j];
        ++slot;
    }

    while (!contextp->gotFinish()) {
        topp->eval();
        if (!topp->eventsPending()) break;
        contextp->time(topp->nextTimeSlot());
    }
    if (!contextp->gotFinish()) {
        vl_fatal(__FILE__, __LINE__, "main", "%Error: Timeout; never got a $finish");
    }
    topp->final();
    return 0;
}
