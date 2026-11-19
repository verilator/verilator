// -*- mode: C++; c-file-style: "cc-mode" -*-
//
// DESCRIPTION: Verilator: DPI-hook on signals of interfaces nested in an interface
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

#include VM_PREFIX_INCLUDE
#include "verilated.h"

#include <string>
#include <svdpi.h>
#include <vector>

extern "C" char cb_nested(int insID, svBit trigger, const svLogicVecVal* value) {
    (void)trigger;
    unsigned v = value[0].aval & 0xffU;
    const uint64_t t = VL_TIME_Q();
    if (insID == 1 && t >= 20 && t < 50) v ^= 0x0fU;
    if (insID == 2 && t >= 30 && t < 60) v ^= 0xf0U;
    if (insID == 3 && t >= 40 && t < 70) v = 0x55U;
    return static_cast<char>(v);
}

int main(int argc, char** argv) {
    const std::unique_ptr<VerilatedContext> contextp{new VerilatedContext};
    contextp->debug(0);
    contextp->commandArgs(argc, argv);
    const std::unique_ptr<VM_PREFIX> topp{new VM_PREFIX{contextp.get(), "top_module"}};

    const std::vector<std::vector<std::string>> paths
        = {{"m", "ob", "in", "data"}, {"m", "ob", "arr[1]", "data"}, {"m", "ob", "sum"}};
    for (size_t i = 0; i < paths.size(); ++i) {
        topp->__Vdpihook_id[i] = static_cast<int>(i) + 1;
        for (size_t j = 0; j < paths[i].size(); ++j) topp->__Vdpihook_path[i][j] = paths[i][j];
    }

    while (!contextp->gotFinish()) {
        topp->__Vdpihook_trigger = !topp->__Vdpihook_trigger;
        topp->eval();
        if (!topp->eventsPending()) break;
        contextp->timeInc(1);
    }
    topp->final();
    return 0;
}
